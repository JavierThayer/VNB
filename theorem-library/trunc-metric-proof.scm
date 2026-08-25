;;; trunc-metric-proof.scm -- the truncated metric d'(x,y) = min(1, d(x,y)) is a
;;; metric, is bounded by 1, and is UNIFORMLY equivalent to d.
;;;
;;; The construction is structure-library/trunc-metric.scm, a
;;; `def-constructed-functor' METRIC-SPACE -> METRIC-SPACE which asserts nothing.
;;; This file discharges its typing obligation and proves the equivalence.
;;;
;;;   rr-min-one-mono                     a <= b  =>  min(1,a) <= min(1,b)
;;;   trunc-metric-dist                   d'(u,v) == min(1, d(u,v))
;;;   trunc-metric-is-metric-space        the functor's typing obligation
;;;   trunc-metric-bounded                d'(u,v) <= 1
;;;   trunc-metric-id-uniformly-continuous       id : (X,d)  -> (X,d')
;;;   trunc-metric-id-uniformly-continuous-back  id : (X,d') -> (X,d)
;;;
;;; WHAT THE EQUIVALENCE COSTS, AND WHY IT IS *UNIFORM*.
;;;
;;; Forward is free: d' <= d pointwise (rr-min-le-right), so delta = eps serves,
;;; and the estimate never looks at the point.
;;;
;;; Backward is the half that carries the content, and it is one line of
;;; mathematics: d' < 1 FORCES d' = d.  `rr-min-cases' says min(1,t) is 1 or t;
;;; a delta chosen strictly below 1 rules the first case out arithmetically, and
;;; what survives is d(a,b) = d'(a,b) <= delta.  No inverse function, no
;;; continuity of one, no eps/delta beyond picking the delta -- which is the
;;; whole reason min(1,.) is UNIFORMLY equivalent to d while a general bounded
;;; transform need only be topologically equivalent.
;;;
;;; The delta is built, not found:  h with h + h = 1 (`rr-pos-halvable' at 1),
;;; then w = a positive lower bound of eps and h (`rr-min-pos').  Then w <= h and
;;; h + h = 1 make "1 <= w" linearly absurd -- 2 <= 2h = 1 -- which is why the
;;; excluded case closes by `ineq' with no appeal to strictness at all, and why
;;; `contra' is not needed (it loads far below this file in any case).
;;;
;;; WHERE rr-min-one-mono BELONGS.  Beside `rr-min-one-subadditive' in
;;; theorem-library/rr-min-basics.scm: it is a fact about min, not about metric
;;; spaces, and the triangle inequality here is exactly
;;; mono(metric-triangle) composed with subadditivity.  It is proved here only
;;; because moving it would re-run every file between the two, which is a
;;; separate measurement.
;;;
;;; WHAT IT COSTS.  Every result below is `modulo {metric-dist-real}' except
;;; rr-min-one-mono and trunc-metric-dist, which are `modulo 0'.
;;; `metric-dist-real' (structure-library/metric-space.scm) is the pre-existing
;;; well-known support "the distance is real-valued"; its own comment says it is
;;; derivable "via a cartesian-application of fun-apply-type" and was kept rather
;;; than re-ground in every metric proof.  Nothing in this file adds to the debt:
;;; every bill here is that one leaf, which every metric estimate in the library
;;; already carries.
;;;
;;; Loads after metric-laws (the five projected laws), rr-min-basics
;;; (rr-min-closed / -cases / -le-left / -le-right / rr-le-min /
;;; rr-min-one-subadditive), rr-halving (rr-pos-halvable), rr-order-basics
;;; (rr-min-pos), rr-recip-order (rr-zero-lt-one), metric-continuity
;;; (IS-UNIFORMLY-CONTINUOUS), structure-library/trunc-metric, and `obtain'
;;; (sketch.scm).

;;; ---- file-local driver helpers (the `trm-' prefix) -------------------
(define (trm-goal) (wff-formula (sequent-node-assertion (proof-state-focus *ps*))))
(define (trm-asms) (map wff-formula (sequent-node-assumptions (proof-state-focus *ps*))))
(define (trm-open) (filter (lambda (s) (null? (sequent-node-in-arrows s))) (proof-leaves)))
(define (trm-head g) (and (pair? g) (car g)))
(define (trm-closed?) (null? (sequent-node-in-arrows (proof-state-focus *ps*))))

(define (trm-peel!)
  (let lp ((n 0)) (if (and (memq (trm-head (trm-goal)) '(FORALL IMPLIES)) (< n 12))
                      (begin (di) (lp (+ n 1))) #t)))

;;; `ineq' on NAMED premises only: the context carries DIST applications whose
;;; atoms have no (IN _ RR) certificate until they are cited, and one such
;;; premise poisons the whole call (continuity-product.scm makes the same point).
(define (trm-idx form)
  (let loop ((l (trm-asms)) (i 1))
    (cond ((null? l) (error "trm-idx: not in context" form))
          ((equal? (car l) form) i)
          (else (loop (cdr l) (+ i 1))))))
(define (trm-ineq . forms) (apply ineq (map trm-idx forms)))

(define (trm-has-lam? g)
  (cond ((and (pair? g) (pair? (car g)) (eq? (caar g) 'VNB-LAMBDA)) #t)
        ((pair? g) (or (trm-has-lam? (car g)) (trm-has-lam? (cdr g))))
        (else #f)))

;;; Beta to a fixpoint, guarded on PROGRESS (`lam-b' only warns when there is
;;; nothing to do, so "while there is a redex" would spin).  ALWAYS run before
;;; the `di' that lands the point memberships: the enclosing guarded universal
;;; is what licenses the reduction, and a beta fired after the peel would owe
;;; (IN a (PTS s)) at a node whose context predates a.
(define (trm-beta!)
  (let loop ((fuel 20))
    (if (and (> fuel 0) (trm-has-lam? (trm-goal)))
        (let ((before (trm-goal))) (lam-b)
          (if (equal? (trm-goal) before) #t (loop (- fuel 1))))
        #t)))

;;; Decompose every open leaf whose goal is a FORALL/IMPLIES/AND, beta-reducing
;;; first so that what an IMPLIES lands is already in min/DIST form.
(define (trm-drive!)
  (let loop ((fuel 200))
    (let ((s (find-first (lambda (s) (memq (trm-head (wff-formula (sequent-node-assertion s)))
                                           '(FORALL IMPLIES AND)))
                         (trm-open))))
      (if (and s (> fuel 0))
          (begin (dk-focus! s) (trm-beta!)
                 (if (memq (trm-head (trm-goal)) '(FORALL IMPLIES AND)) (di) #t)
                 (loop (- fuel 1)))
          #t))))

;;; Split an AND goal to its atoms and run CLOSER on each.
(define (trm-and! closer)
  (if (eq? (trm-head (trm-goal)) 'AND)
      (for-each (lambda (k) (dk-focus! k) (trm-and! closer)) (dk-opened (lambda () (di))))
      (closer)))

;;; `ai' every conjunction in the context to exhaustion.
(define (trm-split!)
  (let loop ((l (trm-asms)) (n 0))
    (cond ((or (null? l) (> n 12)) #t)
          ((and (pair? (car l)) (eq? (caar l) 'AND)) (ai (car l)) (loop (trm-asms) (+ n 1)))
          (else (loop (cdr l) n)))))

;;; (IN (PTS s) SET) from IS-METRIC-SPACE(s).  `mac-h' is DESTRUCTIVE -- it
;;; REPLACES the hypothesis -- but this leaf is terminal, so the folded
;;; IS-METRIC-SPACE(s) the sibling leaves need is untouched (each leaf is its
;;; own sequent node).
(define (trm-pts-set!) (mac-h 'IS-METRIC-SPACE '(IS-METRIC-SPACE s)) (trm-split!) (ass))

(define (trm-dd a b) (list (list 'DIST 's) a b))   ; d(a,b)
(define (trm-mn d)   (list 'min 1 d))              ; min(1, d)

;;; 0, 1 and 0 <= 1.  NOT `(have! '(<= 0 1) ...)': the side goal a cut opens is
;;; hash-consed by (assertion, context), so the SECOND leaf to ask for the same
;;; claim under the same context gets a node that is already grounded, `cut'
;;; opens nothing, and have! dies with "no side goal" several laws later.
(define (trm-base!)
  (fact 'rr-zero-in) (fact 'rr-one-in)
  (fact 'rr-zero-lt-one)
  (mac-h '< '(< 0 1))
  (trm-split!))

;;; The standard bag for one pair of points: d(a,b) in RR, min(1,d) in RR, the
;;; two bounds min <= 1 and min <= d, 0 <= d, and 0 <= min.
(define (trm-pair! a b)
  (let ((d (trm-dd a b)))
    (fact 'metric-dist-real 's a b)
    (fact 'rr-min-closed 1 d)
    (fact 'rr-min-le-left 1 d)
    (fact 'rr-min-le-right 1 d)
    (fact 'metric-pos 's a b)
    (fact 'rr-le-min 1 d 0)
    d))

;;; =====================================================================
;;; (1) min(1,.) IS MONOTONE.  Two cases of rr-min-cases on the RIGHT side;
;;; the left is bounded by 1 and by its own argument in both.
;;; =====================================================================
(sp (make-wff-from-string
     "forall([a_ in rr, b_ in rr], a_ <= b_ implies min(1,a_) <= min(1,b_))"))
(trm-peel!)
(fact 'rr-one-in)
(fact 'rr-min-closed 1 'a_)
(fact 'rr-min-closed 1 'b_)
(fact 'rr-min-le-left 1 'a_)
(fact 'rr-min-le-right 1 'a_)
(fact 'rr-min-cases 1 'b_)
(use-cases (list '(= (min 1 b_) 1) '(= (min 1 b_) b_))
  (lambda () (trm-ineq '(<= (min 1 a_) 1) '(= (min 1 b_) 1)))
  (lambda () (trm-ineq '(<= (min 1 a_) a_) '(<= a_ b_) '(= (min 1 b_) b_))))
(qed 'rr-min-one-mono)
(topic! 'rr-min-one-mono 'inequalities)
(alias! 'rr-min-one-mono "truncation at 1 is monotone")

;;; =====================================================================
;;; (2) THE DISTANCE, on the surface.  The functor projection reduces
;;; DIST(TRUNC-METRIC s) to the lambda (which `subst' could not do: the term is
;;; in OPERATOR position); `lam-b' takes the tupled bind-spec applied to two
;;; arguments as it stands; `qrfl' closes t == t.
;;;
;;; Stated with `==' and GUARDED, for the reason rr-ms-dist gives: off PTS(s)
;;; the left side is an application outside its lambda's domain, and nothing in
;;; the theory says min(1, d(u,v)) is undefined there.
;;; =====================================================================
(sp (make-wff
     (list 'FORALL 's
       (forall-guarded '(u_ v_) '((IN u_ (PTS s)) (IN v_ (PTS s)))
         '(== ((DIST (TRUNC-METRIC s)) u_ v_) (min 1 ((DIST s) u_ v_)))))))
(trm-peel!)
(slot 'DIST)
(lam-b)
(qrfl)
(qed 'trunc-metric-dist)
(topic! 'trunc-metric-dist 'constructions)
(alias! 'trunc-metric-dist "the truncated distance is min(1, d)")

;;; =====================================================================
;;; (3) THE FUNCTOR'S TYPING OBLIGATION: TRUNC-METRIC(s) is a metric space.
;;;
;;; The goal is taken from `functor-obligation' rather than restated, so the
;;; statement cannot drift from the one `functor-obligation-audit' reports.
;;;
;;; IS-METRIC-SPACE is unfolded on the GOAL ONLY -- the hypothesis stays folded,
;;; because every citation below (metric-pos, metric-self-zero, metric-zero-eq,
;;; metric-sym, metric-triangle, metric-dist-real) is guarded on it.  The one
;;; conjunct that wants the unfolded form, PTS(s) in SET, gets it leaf-locally.
;;; =====================================================================

;;; The two leaves `lam-t' opens for the distance: the pointwise typing of the
;;; body, and the SETHOOD of the domain -- a lambda over a proper class is not a
;;; function, so the second is not a formality.
(define (trm-dist-fun-leaf!)
  (let ((g (trm-goal)))
    (cond
      ((equal? g '(IN (CARTESIAN (PTS s) (PTS s)) SET))
       (mac 'cartesian-set-iff)
       (for-each (lambda (k) (dk-focus! k) (trm-pts-set!)) (dk-opened (lambda () (di)))))
      ((and (eq? (trm-head g) 'IN) (pair? (cadr g)) (eq? (car (cadr g)) 'min))
       (let* ((d (caddr (cadr g))) (a (cadr d)) (b (caddr d)))
         (fact 'rr-one-in) (fact 'metric-dist-real 's a b)
         (fact 'rr-min-closed 1 d) (ass)))
      (else (error "trm-dist-fun-leaf!: unexpected leaf" g)))))

;;; The five metric laws for min(1,d), dispatched on the shape of the leaf.
(define (trm-law!)
  (let ((g (trm-goal)))
    (cond
      ;; d'(u,u) = 0 :  0 <= min(1,d) <= d = 0.
      ((and (eq? (trm-head g) '=) (pair? (cadr g)) (eq? (car (cadr g)) 'min)
            (equal? (caddr g) 0))
       (let* ((d (caddr (cadr g))) (a (cadr d)))
         (trm-base!) (trm-pair! a a)
         (fact 'metric-self-zero 's a)
         (trm-ineq (list '<= (trm-mn d) d) (list '<= 0 (trm-mn d)) (list '= d 0))))
      ;; 0 <= d'(u,v) : rr-le-min against 0 <= 1 and metric-pos.
      ((and (eq? (trm-head g) '<=) (equal? (cadr g) 0))
       (let* ((d (caddr (caddr g))) (a (cadr d)) (b (caddr d)))
         (trm-base!) (trm-pair! a b) (ass)))
      ;; SEPARATION.  d'(u,v) = 0 is in context and the goal is u = v, which no
      ;; arithmetic oracle can conclude -- so the arithmetic is done inside a
      ;; `have!' that establishes d(u,v) = 0, and metric-zero-eq finishes.  In
      ;; the min = 1 case the two equations give 1 = 0, which `ineq' refutes.
      ((and (eq? (trm-head g) '=) (symbol? (cadr g)))
       (let* ((hyp (or (find-first (lambda (f) (and (pair? f) (eq? (car f) '=)
                                                    (pair? (cadr f)) (eq? (car (cadr f)) 'min)
                                                    (equal? (caddr f) 0)))
                                   (trm-asms))
                       (error "trm-law!: no d'(u,v) = 0 hypothesis")))
              (d (caddr (cadr hyp))) (a (cadr d)) (b (caddr d)))
         (trm-base!) (trm-pair! a b)
         (fact 'rr-min-cases 1 d)
         (have! (list '= d 0)
           (lambda ()
             (use-cases (list (list '= (trm-mn d) 1) (list '= (trm-mn d) d))
               (lambda () (trm-ineq (list '= (trm-mn d) 1) hyp))
               (lambda () (trm-ineq (list '= (trm-mn d) d) hyp)))))
         (fact 'metric-zero-eq 's a b)
         (ass)))
      ;; SYMMETRY.  metric-sym rewrites d(u,v) to d(v,u) on BOTH sides of the
      ;; goal, and `rfl' closes t = t -- `=' being partial, that needs t defined,
      ;; which (IN min(1,d(v,u)) RR) witnesses.
      ((and (eq? (trm-head g) '=) (pair? (cadr g)) (eq? (car (cadr g)) 'min))
       (let* ((d1 (caddr (cadr g))) (a (cadr d1)) (b (caddr d1)) (d2 (trm-dd b a)))
         (trm-base!) (trm-pair! b a)
         (fact 'metric-sym 's a b)
         (subst (list '= d1 d2))
         (rfl)))
      ;; THE TRIANGLE INEQUALITY, and it is the only law with content:
      ;;   min(1, d(u,w)) <= min(1, d(u,v) + d(v,w))         [mono + metric-triangle]
      ;;                  <= min(1, d(u,v)) + min(1, d(v,w)) [rr-min-one-subadditive]
      ((eq? (trm-head g) '<=)
       (let* ((duw (caddr (cadr g)))
              (rhs (caddr g))
              (duv (caddr (cadr rhs)))
              (dvw (caddr (caddr rhs)))
              (a (cadr duw)) (c (caddr duw)) (b (caddr duv))
              (sum (list '+ duv dvw)))
         (trm-base!)
         (trm-pair! a c) (trm-pair! a b) (trm-pair! b c)
         (fact 'metric-triangle 's a b c)
         (have! (list 'AND (list 'IN duv 'RR) (list 'IN dvw 'RR)))
         (fact 'rr-add-closed duv dvw)
         (fact 'rr-min-closed 1 sum)
         (fact 'rr-min-one-mono duw sum)
         (fact 'rr-min-one-subadditive duv dvw)
         (trm-ineq (list '<= (trm-mn duw) (trm-mn sum))
                   (list '<= (trm-mn sum) (list '+ (trm-mn duv) (trm-mn dvw))))))
      (else (error "trm-law!: unexpected leaf" g)))))

(sp (functor-obligation 'trunc-metric-is-metric-space))
(di) (di)                                  ; intro s; IS-METRIC-SPACE(s) to ctx
(mac 'IS-METRIC-SPACE)                     ; the GOAL only
(slot 'PTS)                                ; PTS(TRUNC-METRIC s) -> PTS(s)
(slot 'DIST)                               ; DIST(TRUNC-METRIC s) -> the lambda
(trm-and!
 (lambda ()
   (let ((g (trm-goal)))
     (cond
       ;; length(TRUNC-METRIC s) = 2 -- the tuple unfold, local to this leaf.
       ((and (eq? (trm-head g) '=) (pair? (cadr g)) (eq? (car (cadr g)) 'LENGTH))
        (mac 'TRUNC-METRIC) (len-r) (arith))
       ((equal? g '(IN (PTS s) SET)) (trm-pts-set!))
       ((eq? (trm-head g) 'IN)
        (for-each (lambda (k) (dk-focus! k) (trm-drive!) (trm-dist-fun-leaf!))
                  (dk-opened (lambda () (lam-t)))))
       (else (mac 'is-metric) (trm-drive!)
             (for-each (lambda (k) (dk-focus! k) (trm-law!)) (trm-open)))))))
(qed 'trunc-metric-is-metric-space)
(topic! 'trunc-metric-is-metric-space 'constructions)
(alias! 'trunc-metric-is-metric-space
        "the truncation of a metric is a metric")

;;; =====================================================================
;;; (4) THE TRUNCATION IS BOUNDED BY 1.  This is the whole point of the
;;; construction, and it is rr-min-le-left.
;;; =====================================================================
(sp (make-wff
     (list 'FORALL 's (list 'IMPLIES '(IS-METRIC-SPACE s)
       (forall-guarded '(u_ v_) '((IN u_ (PTS s)) (IN v_ (PTS s)))
         '(<= ((DIST (TRUNC-METRIC s)) u_ v_) 1))))))
(trm-peel!)
(slot 'DIST)
(lam-b)
(fact 'rr-one-in)
(fact 'metric-dist-real 's 'u_ 'v_)
(fact 'rr-min-le-left 1 '((DIST s) u_ v_))
(ass)
(qed 'trunc-metric-bounded)
(topic! 'trunc-metric-bounded 'constructions)
(alias! 'trunc-metric-bounded "the truncated metric has diameter at most 1")

;;; =====================================================================
;;; (5) and (6) UNIFORM EQUIVALENCE.  The map is the SAME term in both
;;; directions -- the identity of PTS(s), which is also PTS(TRUNC-METRIC s), so
;;; `(slot 'PTS)' makes the two FUN typings coincide and the reader sees one map
;;; and its inverse rather than two lambdas that happen to agree.
;;; =====================================================================
(define trm-id '(VNB-LAMBDA a_ (PTS s) a_))

;;; The identity is a function PTS(s) -> PTS(s): `lam-t' opens the pointwise
;;; typing (the guard IS the goal) and the sethood of PTS(s).
(define (trm-id-fun!)
  (for-each (lambda (k) (dk-focus! k)
              (if (eq? (trm-head (trm-goal)) 'FORALL) (begin (di) (ass)) (trm-pts-set!)))
            (dk-opened (lambda () (lam-t)))))

;;; Peel FORALL eps, read eps off the goal, land POS-RR(eps).  The universal is
;;; NOT guarded by a membership, so the first `di' peels the quantifier and
;;; lands nothing; the eps is in the antecedent, not in a landing.
(define (trm-eps!)
  (di)
  (let ((eps (cadr (cadr (trm-goal)))))
    (di)
    eps))

;;; --- (5) id : (X,d) -> (X,d') is uniformly continuous.  delta = eps. ---
(define (trm-fwd-inner! eps)
  (trm-beta!)                       ; the identity applications, under the guards
  (slot 'DIST)
  (trm-beta!)                       ; the truncated-distance lambda
  (trm-peel!)                       ; the two memberships AND d(a,b) <= eps: a
                                    ; guarded universal goes whole under one
                                    ; `di', but the implication that follows it
                                    ; needs another call

  (let* ((g (trm-goal)) (d (caddr (cadr g))) (a (cadr d)) (b (caddr d)))
    (mac-h 'pos-rr (list 'POS-RR eps))
    (trm-split!)
    (fact 'rr-one-in)
    (fact 'metric-dist-real 's a b)
    (fact 'rr-min-closed 1 d)
    (fact 'rr-min-le-right 1 d)
    (trm-ineq (list '<= (trm-mn d) d) (list '<= d eps))))

(sp (make-wff (list 'FORALL 's (list 'IMPLIES '(IS-METRIC-SPACE s)
      (list 'IS-UNIFORMLY-CONTINUOUS 's '(TRUNC-METRIC s) trm-id)))))
(di) (di)
(mac 'IS-UNIFORMLY-CONTINUOUS)
(slot 'PTS)
(trm-and!
 (lambda ()
   (let ((g (trm-goal)))
     (cond
       ((equal? g '(IS-METRIC-SPACE s)) (ass))
       ((eq? (trm-head g) 'IS-METRIC-SPACE) (fact 'trunc-metric-is-metric-space 's) (ass))
       ((eq? (trm-head g) 'IN) (trm-id-fun!))
       (else
        (let ((eps (trm-eps!)))
          (ew eps)
          (trm-and! (lambda ()
            (if (eq? (trm-head (trm-goal)) 'POS-RR) (ass) (trm-fwd-inner! eps))))))))))
(qed 'trunc-metric-id-uniformly-continuous)
(topic! 'trunc-metric-id-uniformly-continuous 'analysis)
(alias! 'trunc-metric-id-uniformly-continuous
        "the identity (X,d) -> (X,min(1,d)) is uniformly continuous")

;;; --- (6) id : (X,d') -> (X,d) is uniformly continuous.  delta = w, a
;;; positive lower bound of eps and of a half of 1.  In the excluded case
;;; min(1,d) = 1 the premises give 1 <= w <= h and h + h = 1, hence 2 <= 1. ---
(define (trm-back-inner! eps h w)
  (trm-beta!)
  (slot 'DIST)
  (trm-beta!)
  (trm-peel!)                       ; memberships and  min(1, d(a,b)) <= w
  (let* ((g (trm-goal)) (d (cadr g)) (a (cadr d)) (b (caddr d)))
    (fact 'rr-one-in)
    (fact 'metric-dist-real 's a b)
    (fact 'rr-min-closed 1 d)
    (fact 'rr-min-cases 1 d)
    (use-cases (list (list '= (trm-mn d) 1) (list '= (trm-mn d) d))
      (lambda () (trm-ineq (list '= (trm-mn d) 1) (list '<= (trm-mn d) w)
                           (list '<= w h) (list '= (list '+ h h) 1)))
      (lambda () (trm-ineq (list '= (trm-mn d) d) (list '<= (trm-mn d) w)
                           (list '<= w eps))))))

;;; POS-RR(t) from an already-unfolded (< 0 t).
(define (trm-pos! t)
  (have! (list 'POS-RR t) (lambda () (mac 'pos-rr) (trm-and! (lambda () (ass))))))

(sp (make-wff (list 'FORALL 's (list 'IMPLIES '(IS-METRIC-SPACE s)
      (list 'IS-UNIFORMLY-CONTINUOUS '(TRUNC-METRIC s) 's trm-id)))))
(di) (di)
(mac 'IS-UNIFORMLY-CONTINUOUS)
(slot 'PTS)
(trm-and!
 (lambda ()
   (let ((g (trm-goal)))
     (cond
       ((equal? g '(IS-METRIC-SPACE s)) (ass))
       ((eq? (trm-head g) 'IS-METRIC-SPACE) (fact 'trunc-metric-is-metric-space 's) (ass))
       ((eq? (trm-head g) 'IN) (trm-id-fun!))
       (else
        (let ((eps (trm-eps!)))
          (mac-h 'pos-rr (list 'POS-RR eps))
          (trm-split!)
          (have! (list '< 0 eps) (lambda () (mac '<) (from-context!)))
          (fact 'rr-zero-in) (fact 'rr-one-in)
          (have! '(POS-RR 1) (lambda () (mac 'pos-rr) (trm-and! (lambda () (arith)))))
          ;; h : a positive half of 1 -- so h < 1, arithmetically
          (let ((h (or (obtain (lambda () (fact 'rr-pos-halvable 1)))
                       (error "trunc-metric: no half of 1 obtained"))))
            (mac-h 'pos-rr (list 'POS-RR h))
            (trm-split!)
            (have! (list '< 0 h) (lambda () (mac '<) (from-context!)))
            ;; w : positive, below eps AND below h
            (let ((w (or (obtain (lambda () (fact 'rr-min-pos eps h)))
                         (error "trunc-metric: no lower bound obtained"))))
              (mac-h '< (list '< 0 w))
              (trm-split!)
              (trm-pos! w)
              (ew w)
              (trm-and! (lambda ()
                (if (eq? (trm-head (trm-goal)) 'POS-RR) (ass)
                    (trm-back-inner! eps h w))))))))))))
(qed 'trunc-metric-id-uniformly-continuous-back)
(topic! 'trunc-metric-id-uniformly-continuous-back 'analysis)
(alias! 'trunc-metric-id-uniformly-continuous-back
        "the identity (X,min(1,d)) -> (X,d) is uniformly continuous"
        "min(1,d) < 1 forces min(1,d) = d, so a delta below 1 transports the estimate back")
