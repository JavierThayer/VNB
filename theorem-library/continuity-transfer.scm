;;; continuity-transfer.scm -- continuity reads only the VALUES: a map that
;;; agrees pointwise with a map continuous at a is itself continuous at a.
;;; PROVEN.
;;;
;;;   f in FUN(RR,RR),  g continuous at a,  f(x) = g(x) for every real x
;;;      =>  f continuous at a
;;;
;;; This was the fifth of the seven `support' + `warrant! 'well-known' facts in
;;; theorem-library/continuity-algebra.scm, and the one that stood between
;;; `diff-implies-continuous' (theorem-library/differentiation.scm) and
;;; `modulo 0'.  The statement is reproduced VERBATIM from there, so that file's
;;; citation reads exactly as before.
;;;
;;; WHAT IT IS FOR.  It is the joint between the two halves of every
;;; Caratheodory-style argument.  The continuity algebra proves things about
;;; SYNTAX -- `sum-continuous-at' concludes about the literal term
;;; (VNB-LAMBDA x RR (+ (g x) (h x))), not about "any map that happens to be
;;; the sum".  The function actually in hand is some other term that agrees
;;; with it at every point.  Without a transfer the algebra can only ever
;;; conclude about lambdas it built itself.  `diff-implies-continuous' is the
;;; worked case: f is arbitrary, and what the algebra reaches is
;;; G(x) = f(a) + phi(x)*(x-a); the Caratheodory identity says f = G pointwise,
;;; and this theorem carries the conclusion across.
;;;
;;; THE PROOF, and why it needs no arithmetic at all.  Unfold both continuity
;;; predicates.  Fix eps > 0 and take g's OWN delta, unchanged -- there is no
;;; eps/2 split and no estimate, because the two distances are not merely close,
;;; they are the same number:
;;;
;;;     d(f(a), f(b))  =  d(g(a), g(b))          f(a)=g(a) and f(b)=g(b)
;;;
;;; So the whole of the mathematics is two instances of the pointwise hypothesis
;;; and two `subst'.  Nothing here cites rr-ms-dist, `ineq' or `crs': the
;;; distance is never opened into `abs' at all, and in consequence the proof is
;;; not about RR -- it would run verbatim over any pair of metric spaces.  The
;;; statement is kept at RR-MS because that is where continuity-algebra states
;;; it and where differentiation.scm cites it; generalising it is a separate,
;;; strictly larger job (the general form wants IS-METRIC-SPACE hypotheses,
;;; which the RR form gets for free from g's own unfold).
;;;
;;; THE ONE ORDERING TRAP, and it is `slot-h' being destructive rather than any
;;; of the usual suspects.  `(IN b (PTS RR-MS))' is needed TWICE and in two
;;; different spellings: as itself, to detach g's delta-universal at b, and as
;;; `(IN b RR)', to detach the pointwise hypothesis at b.  `slot-h 'PTS'
;;; REPLACES the assumption, so the order is forced -- instantiate g's
;;; universal FIRST, then slot the membership down to RR.  Done the other way
;;; the `inst+' silently lands nothing and the `ass' at the end fails several
;;; steps away from the cause.  (continuity-sum.scm meets the same trap and
;;; solves it the other way, with a `have!' that puts the PTS form back.)
;;;
;;; Note also that the two `IS-METRIC-SPACE RR-MS' conjuncts of the goal come
;;; out of g's OWN unfold and are never cited.  That is what keeps the bill at
;;; zero: `rr-is-metric-space' is still an asserted support, and citing it here
;;; would have put it into this bill and into differentiation's.
;;;
;;; WHAT IT COSTS.  Nothing: `modulo 0'.
;;;
;;; Loads after metric-continuity (IS-CONTINUOUS-AT) and rr-metric-space
;;; (RR-MS, PTS), beside continuity-basics/-sum/-product, and BEFORE
;;; continuity-algebra, whose `cont-transfer-ptwise-eq' support it retires, and
;;; differentiation.

;;; ---- file-local driver helpers (the `ct-' prefix) --------------------

(define (ct-peel!)
  (let loop ((n 0))
    (let ((g (dk-goal)))
      (if (and (pair? g) (memq (car g) '(FORALL IMPLIES)) (< n 14))
          (begin (di) (loop (+ n 1))) #t))))

(define (ct-split!)
  (let loop ((l (dk-asms)) (n 0))
    (cond ((or (null? l) (> n 18)) #t)
          ((and (pair? (car l)) (eq? (caar l) 'AND))
           (ai (car l)) (loop (dk-asms) (+ n 1)))
          (else (loop (cdr l) n)))))

;;; Walk an AND goal down to its leaves, running CLOSER on each.
(define (ct-goal-and! closer)
  (let ((g (dk-goal)))
    (if (and (pair? g) (eq? (car g) 'AND))
        (for-each (lambda (k) (dk-focus! k) (ct-goal-and! closer))
                  (dk-opened (lambda () (di))))
        (closer))))

;;; `di' until an ASSUMPTION lands.  A GUARDED universal goes whole; an
;;; unguarded one peels the quantifier and lands nothing, so counting `di's is
;;; not a way to reach a chosen goal.
(define (ct-di-landed!)
  (let loop ((n 0))
    (let ((new (dk-landed* (lambda () (di)))))
      (cond ((pair? new) new)
            ((> n 4) (error "ct-di-landed!: di landed no assumption"))
            (else (loop (+ n 1)))))))

(define (ct-find what pred)
  (let loop ((l (dk-asms)))
    (cond ((null? l) (error "ct-find: no context formula" what))
          ((pred (car l)) (car l))
          (else (loop (cdr l))))))

;;; ---- the three eigenvariables, set as the proof runs ------------------

(define ct-f #f)          ; the map whose continuity is concluded
(define ct-g #f)          ; the map already known continuous
(define ct-a #f)          ; the point

;;; The pointwise-equality hypothesis: the FORALL whose body's consequent is an
;;; EQUATION.  Discriminated on the CONSEQUENT and not on a symbol it contains
;;; -- the two other universals in this context (g's eps-universal and, later,
;;; its delta-universal) are the same FORALL/IMPLIES shape.
(define (ct-ptwise)
  (ct-find 'ptwise
    (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                      (pair? (caddr fm)) (eq? (car (caddr fm)) 'IMPLIES)
                      (pair? (caddr (caddr fm)))
                      (eq? (car (caddr (caddr fm))) '=)))))

;;; g's unfolded continuity: forall eps. POS-RR(eps) => forsome delta. ...
(define (ct-eps-universal)
  (ct-find 'eps
    (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                      (dk-contains? fm 'POS-RR) (dk-contains? fm 'DIST)))))

;;; the body of the existential that universal delivered, at the delta D.
;;; POS-RR excluded so it cannot match the universal above.
(define (ct-delta-universal d)
  (ct-find 'delta
    (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                      (dk-contains? fm 'DIST) (dk-contains? fm d)
                      (not (dk-contains? fm 'POS-RR))))))

;;; ---- the innermost goal: d(f(a), f(b)) <= eps for b within delta of a ----
(define (ct-inner! dlt)
  (ct-di-landed!)                                  ; (IN b (PTS RR-MS))
  (let* ((mem (ct-find 'b (lambda (fm) (and (pair? fm) (eq? (car fm) 'IN)
                                            (equal? (caddr fm) '(PTS RR-MS))))))
         (b (cadr mem)))
    (ct-di-landed!)                                ; d(a,b) <= delta
    ;; g's bound at b, BEFORE `slot-h' consumes the PTS membership it needs
    (inst+ (ct-delta-universal dlt) b)
    (slot-h 'PTS mem)                              ; (IN b RR), for the ptwise eq
    (inst+ (ct-ptwise) ct-a)                       ; f(a) = g(a)
    (inst+ (ct-ptwise) b)                          ; f(b) = g(b)
    (subst (list '= (list ct-f ct-a) (list ct-g ct-a)))
    (subst (list '= (list ct-f b) (list ct-g b)))
    (ass)))

;;; ---- the eps branch: take g's delta, unchanged ------------------------
(define (ct-eps!)
  (let* ((pos (car (ct-di-landed!)))
         (eps (cadr pos))
         (dlt (obtain (lambda () (inst+ (ct-eps-universal) eps)))))
    (if (not dlt) (error "ct-eps!: no delta obtained for" eps))
    (ct-split!)
    (ew dlt)
    (ct-goal-and!
     (lambda ()
       (if (eq? (car (dk-goal)) 'FORALL) (ct-inner! dlt) (ass))))))

;;; ---- the proof -------------------------------------------------------

;;; Statement reproduced VERBATIM from theorem-library/continuity-algebra.scm,
;;; where it stood as a `well-known' support until 2026-08-18.
(sp (make-wff
     '(FORALL f (FORALL g (FORALL a (IMPLIES
        (IN f (FUN RR RR))
        (IMPLIES (IS-CONTINUOUS-AT RR-MS RR-MS g a)
        (IMPLIES (FORALL x (IMPLIES (IN x RR) (= (f x) (g x))))
                 (IS-CONTINUOUS-AT RR-MS RR-MS f a)))))))))
(ct-peel!)

;;; f and a off the GOAL, which names both in their roles; g off the ONE
;;; continuity hypothesis whose subject is not f.
(let ((g0 (dk-goal)))
  (set! ct-f (list-ref g0 3))
  (set! ct-a (list-ref g0 4)))
(set! ct-g (list-ref (ct-find 'g-continuity
                       (lambda (fm) (and (pair? fm) (eq? (car fm) 'IS-CONTINUOUS-AT)
                                         (not (eq? (list-ref fm 3) ct-f)))))
                     3))

(mac-h 'is-continuous-at (list 'IS-CONTINUOUS-AT 'RR-MS 'RR-MS ct-g ct-a))
(ct-split!)
;; PTS(RR-MS) down to RR on the two typings the unfold landed
(slot-h 'PTS (list 'IN ct-a '(PTS RR-MS)))
(slot-h 'PTS (list 'IN ct-g '(FUN (PTS RR-MS) (PTS RR-MS))))

(mac 'is-continuous-at)
(ct-goal-and!
 (lambda ()
   (let ((g (dk-goal)))
     (cond ((eq? (car g) 'FORALL) (ct-eps!))
           ((and (eq? (car g) 'IN) (dk-contains? g 'PTS)) (slot 'PTS) (ass))
           (else (ass))))))

(qed 'cont-transfer-ptwise-eq)
(topic! 'cont-transfer-ptwise-eq 'analysis)
(alias! 'cont-transfer-ptwise-eq
        "a map agreeing pointwise with a continuous map is continuous")
