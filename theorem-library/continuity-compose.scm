;;; continuity-compose.scm -- COMPOSITION OF CONTINUOUS MAPS, PROVEN.
;;;
;;;   f continuous at a,  g continuous at f(a)   =>   COMPOSE(g,f) continuous at a
;;;
;;; This was the SIXTH of the seven `support' + `warrant!' facts of
;;; theorem-library/continuity-algebra.scm (only `cont-agree-off-pt' is left
;;; there), and it is the one block the Caratheodory CHAIN RULE needs: the
;;; factor of g o f is (phi_g o f) * phi_f, whose first half is continuous at a
;;; only by this theorem.  The statement is reproduced VERBATIM from
;;; continuity-algebra.scm, so any citation reads exactly as before.
;;;
;;; ROUTE.  eps/delta, directly -- NOT the sequential characterization.  That
;;; was tried first, `continuous-at-iff-sequential' (theorem-library/
;;; sequential-continuity.scm) being the newer machinery, and it wants TWO
;;; lemmas the tree does not have:
;;;
;;;   * associativity of COMPOSE.  The sequential form of the conclusion is
;;;     about COMPOSE(COMPOSE(g,f), sq); what the two sequential hypotheses
;;;     deliver is COMPOSE(g, COMPOSE(f, sq)).  `COMPOSE' is a functoid whose
;;;     unfold is a VNB-LAMBDA over DOM, so the two terms are not syntactically
;;;     equal and nothing in the tree relates them.
;;;   * transfer of CONVERGES-TO across pointwise equality of sequences -- the
;;;     sequence-level analogue of `cont-transfer-ptwise-eq', which would be
;;;     needed to close that gap even with the beta law in hand.
;;;
;;; Both are worth having; neither is on the way to the chain rule.  So the
;;; proof below is the direct one, and it is SHORTER than either of its
;;; neighbours in the continuity algebra: there is no eps/2 split, no `min' of
;;; two deltas, and -- as in continuity-transfer.scm -- no arithmetic at all.
;;; The distance is never opened into `abs': `rr-ms-dist', `ineq' and `crs' are
;;; not cited, and in consequence the proof is not about RR.  It would run
;;; verbatim over any three metric spaces; it is kept at RR-MS because that is
;;; where continuity-algebra states it and where differentiation cites it.
;;;
;;; THE MATHEMATICS is one nesting of deltas.  Given eps > 0, take g's delta at
;;; f(a) for that eps -- call it d1 -- and then f's delta at a for d1.  For b
;;; within d2 of a, f(b) is within d1 of f(a), so g(f(b)) is within eps of
;;; g(f(a)).  The only mechanical point is that the goal's terms are
;;; (COMPOSE(g,f))(a) and (COMPOSE(g,f))(b), which `compose-apply' turns into
;;; g(f(a)) and g(f(b)).
;;;
;;; WHAT IT COSTS: `modulo {compose-type, compose-apply}' -- the two COMPOSE
;;; laws of structure-library/compose.scm, both `warrant: proof' (the top tier),
;;; both one-line derivations that have not been run.  Everything else in the
;;; bill is zero: the two IS-METRIC-SPACE conjuncts of the goal come out of the
;;; hypotheses' OWN unfolds and `rr-is-metric-space' is never cited.
;;;
;;; TWO DRIVER POINTS.
;;;
;;; * The two eps-universals CANNOT be told apart by shape -- both are
;;;   FORALL/POS-RR/DIST -- and they cannot be told apart by "mentions f"
;;;   either, because g's universal is about the point f(a) and so mentions f
;;;   as well.  The discriminator is the OTHER way round: g's universal is the
;;;   one that mentions g, f's is the one that does not.
;;; * NO `slot-h' anywhere.  Its neighbours push PTS(RR-MS) down to RR because
;;;   their estimates are RR arithmetic; here every term stays a point of
;;;   PTS(RR-MS), which is also the spelling `compose-type' and `compose-apply'
;;;   want for A = B = C.  Slotting would have had to be undone twice.
;;;
;;; Loads beside continuity-basics/-sum/-product/-transfer/-sub and BEFORE
;;; continuity-algebra (whose `compose-continuous-at' support it retires) and
;;; differentiation.  Needs metric-continuity (IS-CONTINUOUS-AT), compose
;;; (COMPOSE, compose-type, compose-apply), fun-apply-type-proof
;;; (fun-apply-type-c), rr-metric-space (RR-MS), driver-kit.

;;; ---- file-local driver helpers (the `cmp-' prefix) --------------------

(define (cmp-peel!)
  (let loop ((n 0))
    (let ((g (dk-goal)))
      (if (and (pair? g) (memq (car g) '(FORALL IMPLIES)) (< n 14))
          (begin (di) (loop (+ n 1))) #t))))

(define (cmp-split!)
  (let loop ((l (dk-asms)) (n 0))
    (cond ((or (null? l) (> n 24)) #t)
          ((and (pair? (car l)) (eq? (caar l) 'AND))
           (ai (car l)) (loop (dk-asms) (+ n 1)))
          (else (loop (cdr l) n)))))

;;; Walk a right-nested AND goal down to its leaves, running CLOSER on each.
(define (cmp-goal-and! closer)
  (let ((g (dk-goal)))
    (if (and (pair? g) (eq? (car g) 'AND))
        (for-each (lambda (k) (dk-focus! k) (cmp-goal-and! closer))
                  (dk-opened (lambda () (di))))
        (closer))))

;;; `di' until an ASSUMPTION lands: a guarded universal lands its guard in one
;;; call, an implication with an AND antecedent lands nothing, so counting
;;; `di's is not a way to reach a chosen goal.
(define (cmp-di-landed!)
  (let loop ((n 0))
    (let ((new (dk-landed* (lambda () (di)))))
      (cond ((pair? new) new)
            ((> n 4) (error "cmp-di-landed!: di landed no assumption"))
            (else (loop (+ n 1)))))))

(define (cmp-find what pred)
  (let loop ((l (dk-asms)))
    (cond ((null? l) (error "cmp-find: no context formula" what))
          ((pred (car l)) (car l))
          (else (loop (cdr l))))))

(define (cmp-obtain what lane)
  (let ((v (obtain lane)))
    (if (not v) (error "cmp-obtain: nothing obtained for" what))
    v))

;;; ---- the eigenvariables, set as the proof runs ------------------------

(define cmp-f #f)        ; the inner map, continuous at a
(define cmp-g #f)        ; the outer map, continuous at f(a)
(define cmp-a #f)        ; the point
(define cmp-pts '(PTS RR-MS))

;;; g's unfolded continuity: forall eps. POS-RR(eps) => forsome delta. ...
;;; BOTH unfolds have this shape and BOTH mention f (g's is about the point
;;; f(a)), so the discriminator is g.
(define (cmp-eps-universal-g)
  (cmp-find 'eps-g
    (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                      (dk-contains? fm 'POS-RR) (dk-contains? fm 'DIST)
                      (dk-contains? fm cmp-g)))))

(define (cmp-eps-universal-f)
  (cmp-find 'eps-f
    (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                      (dk-contains? fm 'POS-RR) (dk-contains? fm 'DIST)
                      (not (dk-contains? fm cmp-g))))))

;;; the body the existential delivered, at the delta D: forall b in PTS. ...
;;; POS-RR excluded so it cannot match the universal above.
(define (cmp-delta-universal d subj)
  (cmp-find 'delta
    (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                      (dk-contains? fm 'DIST) (dk-contains? fm d)
                      (dk-contains? fm subj)
                      (not (dk-contains? fm 'POS-RR))))))

;;; ---- the innermost goal ----------------------------------------------
;;; d((g o f)(a), (g o f)(b)) <= eps, for b within d2 of a.

(define (cmp-inner! d1 d2)
  (let* ((landed (cmp-di-landed!))
         (mem (or (find-first (lambda (x) (and (pair? x) (eq? (car x) 'IN))) landed)
                  (error "cmp-inner!: no membership landed")))
         (b (cadr mem)))
    (if (not (find-first (lambda (x) (and (pair? x) (eq? (car x) '<=))) landed))
        (cmp-di-landed!))
    ;; f carries b into the d1-ball around f(a) ...
    (inst+ (cmp-delta-universal d2 cmp-f) b)
    (fact 'fun-apply-type-c cmp-f cmp-pts cmp-pts b)
    ;; ... and g carries f(b) into the eps-ball around g(f(a)).
    (inst+ (cmp-delta-universal d1 cmp-g) (list cmp-f b))
    ;; the goal still speaks of (COMPOSE g f)(-); compose-apply names the values
    (inst+ (cmp-compose-apply) cmp-a)
    (inst+ (cmp-compose-apply) b)
    (subst (list '= (list (list 'COMPOSE cmp-g cmp-f) cmp-a)
                    (list cmp-g (list cmp-f cmp-a))))
    (subst (list '= (list (list 'COMPOSE cmp-g cmp-f) b)
                    (list cmp-g (list cmp-f b))))
    (ass)))

;;; the beta law for THIS composite, landed once at the top and instantiated
;;; at each point: forall x in PTS(RR-MS). (COMPOSE(g,f))(x) = g(f(x)).
(define (cmp-compose-apply)
  (cmp-find 'compose-apply
    (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                      (dk-contains? fm 'COMPOSE)
                      (not (dk-contains? fm 'DIST))))))

;;; ---- the eps branch: nest g's delta inside f's -----------------------

(define (cmp-eps!)
  (let* ((pos (car (cmp-di-landed!)))
         (eps (cadr pos))
         ;; d1: g's delta at f(a) for eps
         (d1 (cmp-obtain 'd1 (lambda () (inst+ (cmp-eps-universal-g) eps))))
         (dummy (cmp-split!))
         ;; d2: f's delta at a for d1 -- POS-RR(d1) is in context by now
         (d2 (cmp-obtain 'd2 (lambda () (inst+ (cmp-eps-universal-f) d1)))))
    (cmp-split!)
    (ew d2)
    (cmp-goal-and!
     (lambda ()
       (if (eq? (car (dk-goal)) 'FORALL) (cmp-inner! d1 d2) (ass))))))

;;; ---- the proof -------------------------------------------------------

;;; Statement reproduced VERBATIM from theorem-library/continuity-algebra.scm,
;;; where it stood as a `well-known' support until 2026-08-23.
(sp (make-wff
     '(FORALL g (FORALL f (FORALL a (IMPLIES
        (IS-CONTINUOUS-AT RR-MS RR-MS f a)
        (IMPLIES (IS-CONTINUOUS-AT RR-MS RR-MS g (f a))
        (IS-CONTINUOUS-AT RR-MS RR-MS (COMPOSE g f) a))))))))
(cmp-peel!)

;;; Read the three eigenvariables off the GOAL, which names all three in their
;;; roles; the context's two continuity hypotheses are the same shape.
(let* ((g0 (dk-goal))                       ; (IS-CONTINUOUS-AT RR-MS RR-MS (COMPOSE g f) a)
       (comp (list-ref g0 3)))
  (set! cmp-g (list-ref comp 1))
  (set! cmp-f (list-ref comp 2))
  (set! cmp-a (list-ref g0 4)))

(mac-h 'is-continuous-at (list 'IS-CONTINUOUS-AT 'RR-MS 'RR-MS cmp-f cmp-a))
(cmp-split!)
(mac-h 'is-continuous-at
       (list 'IS-CONTINUOUS-AT 'RR-MS 'RR-MS cmp-g (list cmp-f cmp-a)))
(cmp-split!)

;;; the composite's typing and its beta law, both off the two FUN memberships
;;; the unfolds landed.  `fact' will not split a conjunctive antecedent, so the
;;; AND is put in context first.
(have! (list 'AND (list 'IN cmp-f (list 'FUN cmp-pts cmp-pts))
                  (list 'IN cmp-g (list 'FUN cmp-pts cmp-pts))))
;; compose-type's (IN A SET) guard: PTS(RR-MS) slots to RR, which is a set.
(have! (list 'IN cmp-pts 'SET)
  (lambda () (slot 'PTS) (fact 'rr-is-set) (ass)))
(fact 'compose-type cmp-pts cmp-pts cmp-pts cmp-g cmp-f)
(fact 'compose-apply cmp-pts cmp-pts cmp-pts cmp-g cmp-f)

(mac 'is-continuous-at)
(cmp-goal-and!
 (lambda ()
   (if (eq? (car (dk-goal)) 'FORALL) (cmp-eps!) (ass))))

(qed 'compose-continuous-at)
(topic! 'compose-continuous-at 'topology)
(alias! 'compose-continuous-at
        "the composite of two continuous maps is continuous")
