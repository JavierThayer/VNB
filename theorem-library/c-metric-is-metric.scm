;;; c-metric-is-metric.scm -- THE CANONICAL METRIC OF A COUNTABLY-METRISED SPACE
;;; IS A METRIC SPACE, proven.
;;;
;;;   c-metric-w-is-metric-space:
;;;     IS-C-METRIC-SPACE(s), SUMMABLE-WEIGHT(w)  =>  IS-METRIC-SPACE(C-METRIC-W(s,w))
;;;   c-metric-is-metric-space:
;;;     IS-C-METRIC-SPACE(s)  =>  IS-METRIC-SPACE(C-METRIC(s))
;;;
;;;   D_w(x,y) = SUM_k w(k) * min(1, d_k(x,y)),   d_k = DISTS(s)(k).
;;;
;;; THE FILE IS theorem-library/product-is-metric-space.scm ONE CONSTRUCTION
;;; OVER, and deliberately so: the same termwise-statement-plus-one-transfer
;;; plan, the transfer being `series-limit-le' (proven there) for the order laws
;;; and `series-limit-add' (S = S + S) for the zero law.  What differs:
;;;
;;;   * the per-coordinate distance is a PSEUDOmetric d_k, read through the
;;;     four projections of pseudometric-laws.scm at ((DISTS s) k), PTS(s)
;;;     (`c-metric-pseudometric-at' supplies the hypothesis);
;;;   * the truncation is min(1,.), so the zero law ends with `rr-min-cases'
;;;     (min(1,d) = 0 forces d = 0, the case min(1,d) = 1 being absurd) and the
;;;     triangle law goes through `rr-min-one-mono' and `rr-min-one-subadditive';
;;;   * the separation law of IS-C-METRIC-SPACE replaces function
;;;     extensionality: once every d_k(x,y) vanishes, x = y is its instance.
;;;
;;; The weight is a general SUMMABLE-WEIGHT throughout (its positivity is what
;;; the zero law spends); the canonical instance is one citation of
;;; `product-metric-default-summable', exactly as c-metric-canonical-summable is.
;;;
;;;   L1  cmim-dist-in-rr          D(x,y) in RR
;;;   L2  cmim-term-nonneg         0 <= the n-th term
;;;   L3  cmim-dist-nonneg         0 <= D(x,y)
;;;   L4  cmim-term-self-zero      the n-th term of D(x,x) is 0
;;;   L5  cmim-dist-self-zero      D(x,x) = 0
;;;   L6  cmim-term-zero           the n-th term is 0  =>  d_n(x,y) = 0
;;;   L7  cmim-dist-zero-eq        D(x,y) = 0  =>  x = y
;;;   L8  cmim-term-sym            termwise symmetry, as a <=
;;;   L9  cmim-dist-sym            D(x,y) = D(y,x)
;;;   L10 cmim-sum-seq-in-fun      the termwise sum of two term sequences is real
;;;   L11 cmim-sum-seq-split       and it is the termwise sum
;;;   L12 cmim-term-triangle       the weighted truncated triangle inequality
;;;   L13 cmim-dist-triangle       D(x,z) <= D(x,y) + D(y,z)
;;;   THE THEOREMS  c-metric-w-is-metric-space, c-metric-is-metric-space
;;;
;;; WINDOW.  lo: theorem-library/c-metric-summable (c-metric-dist-real,
;;; c-metric-pseudometric-at, c-metric-term-bound, c-metric-term-seq-in-fun,
;;; c-metric-summable, c-metric-carrier, c-metric-distance,
;;; c-metric-dist-converges), the latest citation.  Also, all earlier:
;;; theorem-library/product-is-metric-space (series-limit-le, series-limit-iota),
;;; theorem-library/dyadic-weights (product-metric-default-summable),
;;; theorem-library/limit-arithmetic (series-limit-add, series-converges-to-add),
;;; theorem-library/mono-le-limit (series-term-le-sum),
;;; theorem-library/dominated-convergence (series-limit-in-rr),
;;; theorem-library/pseudometric-laws, theorem-library/rr-min-basics,
;;; theorem-library/trunc-metric-proof (rr-min-one-mono),
;;; theorem-library/rr-order-basics (rr-no-zero-divisors).
;;; hi: theorem-library/c-continuous-category (hom-c-continuous-id).
;;;
;;; Helper prefix: cmim-.

;;; ---- the cmim- kit ---------------------------------------------------

(define cmim-P '(PTS s))

(define (cmim-d x y n) (list (list '(DISTS s) n) x y))
(define (cmim-m x y n) (list 'min 1 (cmim-d x y n)))
(define (cmim-term x y n) (list '* (list 'w n) (cmim-m x y n)))
(define (cmim-lam x y) (list 'VNB-LAMBDA 'k 'NN (cmim-term x y 'k)))
(define (cmim-sumlam x y z)
  (list 'VNB-LAMBDA 'k 'NN (list '+ (cmim-term x y 'k) (cmim-term y z 'k))))
(define (cmim-dd x y) (list '(DIST (C-METRIC-W s w)) x y))

(define (cmim-stmt vars body)
  (let loop ((vs vars))
    (if (null? vs) body
        (list 'FORALL (car vs)
              (list 'IMPLIES (list 'IN (car vs) cmim-P) (loop (cdr vs)))))))
(define (cmim-full vars body)
  (list 'FORALL 's (list 'IMPLIES '(IS-C-METRIC-SPACE s)
    (list 'FORALL 'w (list 'IMPLIES '(SUMMABLE-WEIGHT w)
      (cmim-stmt vars body))))))
(define (cmim-termwise vars body-of-n)
  (cmim-full vars (list 'FORALL 'n_ (list 'IMPLIES '(IN n_ NN) (body-of-n 'n_)))))

(define (cmim-di-landed-1!)
  (let loop ((n 0))
    (let ((new (dk-landed* (lambda () (di)))))
      (cond ((pair? new)
             (if (null? (cdr new)) (car new)
                 (error "cmim-di-landed-1!: expected 1" (map expression->string new))))
            ((> n 5) (error "cmim-di-landed-1!: di landed no assumption"))
            (#t (loop (+ n 1)))))))

;; the PTS(s)-typed eigenvariables of the focus context, peel order
(define (cmim-points)
  (reverse (map cadr (filter (lambda (a) (and (pair? a) (eq? (car a) 'IN)
                                              (equal? (caddr a) cmim-P)))
                             (dk-asms)))))
(define (cmim-open! n)
  (let loop ((k 0))
    (if (< (length (cmim-points)) n)
        (begin (if (> k 20) (error "cmim-open!: stuck"))
               (di) (loop (+ k 1)))))
  (cmim-points))

;; the NN-typed eigenvariable of the focus context, peeling for it if needed
(define (cmim-index!)
  (let loop ((k 0))
    (let ((a (find-first (lambda (f) (and (pair? f) (eq? (car f) 'IN) (eq? (caddr f) 'NN)))
                         (dk-asms))))
      (cond (a (cadr a))
            ((> k 6) (error "cmim-index!: no NN index landed"))
            (#t (di) (loop (+ k 1)))))))

(define (cmim-asm? f) (if (member f (dk-asms)) #t #f))
(define (cmim-once! f thunk) (if (not (cmim-asm? f)) (thunk)))

;; the conjuncts of a context (< a b), landed without destroying it
(define (cmim-from-lt! a b)
  (let ((lt (list '< a b)))
    (for-each
     (lambda (part)
       (dk-have! part (lambda ()
                        (dk-split! (dk-landed-find (lambda () (mac-h '< lt))
                                                   (lambda (f) (eq? (car f) 'AND))))
                        (ass))))
     (list (list '<= a b) (list 'NOT (list '= a b))))))

;; beta-reduce every redex in the goal
(define (cmim-beta!)
  (let loop ((k 0))
    (let ((g (dk-goal)))
      (if (and (< k 8) (dk-contains? g 'VNB-LAMBDA))
          (begin (lam-b) (if (not (equal? (dk-goal) g)) (loop (+ k 1))))))))

;; open SUMMABLE-WEIGHT(w): w in FUN(NN,RR), the positivity universal, the series
(define cmim-wpos #f)
(define (cmim-setup!)
  (dk-split! (dk-landed-find (lambda () (mac-h 'summable-weight '(SUMMABLE-WEIGHT w)))
                             (lambda (f) (eq? (car f) 'AND))))
  (set! cmim-wpos (dk-pick (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                                            (dk-contains? a '<)))
                           "w positivity")))

;; w(n) in RR, 0 < w(n), 0 <= w(n), 0 /= w(n), w(n) /= 0
(define (cmim-weight! n)
  (cmim-once! (list 'IN (list 'w n) 'RR)
              (lambda ()
                (fact 'fun-apply-type-c 'w 'NN 'RR n)
                (inst+ cmim-wpos n)
                (cmim-from-lt! 0 (list 'w n))))
  (cmim-once! (list 'NOT (list '= (list 'w n) 0))
              (lambda ()
                (dk-have! (list 'NOT (list '= (list 'w n) 0))
                          (lambda ()
                            (di)
                            (have! (list '= 0 (list 'w n))
                                   (lambda () (subst (list '= (list 'w n) 0)) (arith)))
                            (dk-focus-having! (list '= 0 (list 'w n)))
                            (ai (list 'NOT (list '= 0 (list 'w n)))))))))

;; the min(1,d) facts: typed, between 0 and both 1 and d
(define (cmim-min! d)
  (cmim-once! '(IN 1 RR) (lambda () (fact 'rr-one-in)))
  (cmim-once! '(<= 0 1) (lambda () (dk-have! '(<= 0 1) (lambda () (arith)))))
  (let ((m (list 'min 1 d)))
    (cmim-once! (list 'IN m 'RR) (lambda () (fact 'rr-min-closed 1 d)))
    (cmim-once! (list '<= m 1) (lambda () (fact 'rr-min-le-left 1 d)))
    (cmim-once! (list '<= m d) (lambda () (fact 'rr-min-le-right 1 d)))
    (cmim-once! (list '<= 0 m) (lambda () (fact 'rr-le-min 1 d 0)))
    m))

;; everything the n-th term at (x,y) owes; returns the term
(define (cmim-term! x y n)
  (let* ((d (cmim-d x y n)) (t (cmim-term x y n)) (dn (list '(DISTS s) n)))
    (cmim-weight! n)
    (cmim-once! (list 'IN d 'RR) (lambda () (fact 'c-metric-dist-real 's n x y)))
    (cmim-once! (list 'IS-PSEUDOMETRIC dn cmim-P)
                (lambda () (fact 'c-metric-pseudometric-at 's n)))
    (cmim-once! (list '<= 0 d) (lambda () (fact 'pseudometric-pos dn cmim-P x y)))
    (cmim-min! d)
    (if (not (cmim-asm? (list 'IN t 'RR)))
        (begin
          (fact 'c-metric-term-bound 's n x y (list 'w n))
          (dk-split! (list 'AND (list 'IN t 'RR)
                           (list 'AND (list '<= 0 t) (list '<= t (list 'w n)))))))
    t))

;; di-split the focus AND goal to its leaves and run CLOSER on each
(define (cmim-and! closer)
  (let ((g (dk-goal)))
    (if (and (pair? g) (eq? (car g) 'AND))
        (for-each (lambda (k) (dk-focus! k) (cmim-and! closer))
                  (dk-opened (lambda () (di))))
        (closer))))

;; split the focus AND goal all the way down; return the atom leaves
(define (cmim-split-goal!)
  (let walk ((n (proof-state-focus *ps*)) (acc '()))
    (dk-focus! n)
    (let ((g (dk-goal)))
      (if (and (pair? g) (eq? (car g) 'AND))
          (let loop ((ks (dk-opened (lambda () (di)))) (acc acc))
            (if (null? ks) acc (loop (cdr ks) (walk (car ks) acc))))
          (cons n acc)))))

;; `di' every open leaf whose goal is a FORALL/IMPLIES/AND, to exhaustion
(define (cmim-drive!)
  (let loop ((fuel 60))
    (let ((n (find-first (lambda (n)
                           (let ((g (dk-goal-of n)))
                             (and (not (sequent-node-grounded? n))
                                  (pair? g) (memq (car g) '(FORALL IMPLIES AND)))))
                         (proof-leaves))))
      (if (and n (> fuel 0)) (begin (dk-focus! n) (di) (loop (- fuel 1))) #t))))

;;; =====================================================================
;;; L1.  cmim-dist-in-rr -- the canonical distance is a real number.
;;; =====================================================================

(sp (make-wff (cmim-full '(x y) (list 'IN (cmim-dd 'x 'y) 'RR))))
(cmim-open! 2)
(fact 'c-metric-term-seq-in-fun 's 'w 'x 'y)
(fact 'c-metric-summable 's 'w 'x 'y)
(fact 'series-limit-in-rr (cmim-lam 'x 'y))
(fact 'c-metric-distance 's 'w 'x 'y)
(mac 'c-metric-distance)
(ass)
(qed 'cmim-dist-in-rr)

;;; =====================================================================
;;; L2, L3.  Non-negativity: termwise, then the sum dominates its 0-th term.
;;; =====================================================================

(sp (make-wff (cmim-termwise '(x y)
      (lambda (n) (list '<= 0 (list (cmim-lam 'x 'y) n))))))
(cmim-open! 2)
(cmim-setup!)
(let ((n_ (cmim-index!)))
  (cmim-beta!)
  (cmim-term! 'x 'y n_)
  (ass))
(qed 'cmim-term-nonneg)

(sp (make-wff (cmim-full '(x y) (list '<= 0 (cmim-dd 'x 'y)))))
(cmim-open! 2)
(let* ((d (cmim-dd 'x 'y)) (lam (cmim-lam 'x 'y)))
  (fact 'c-metric-dist-converges 's 'w 'x 'y)
  (fact 'c-metric-term-seq-in-fun 's 'w 'x 'y)
  (fact 'cmim-dist-in-rr 's 'w 'x 'y)
  (let ((nn- (dk-fact! 'cmim-term-nonneg 's 'w 'x 'y)))
    (fact 'nn-zero-in)
    (fact 'series-term-le-sum lam d 0)
    (inst+ nn- 0)
    (fact 'fun-apply-type-c lam 'NN 'RR 0)
    (dk-ineq! (list '<= (list lam 0) d) (list '<= 0 (list lam 0)))))
(qed 'cmim-dist-nonneg)

;;; =====================================================================
;;; L4, L5.  D(x,x) = 0.  The terms vanish (d_n(x,x) = 0, and min(1,0) = 0),
;;; so series-limit-add at f = g = h reads S = S + S.
;;; =====================================================================

(sp (make-wff (cmim-termwise '(x)
      (lambda (n) (list '= (list (cmim-lam 'x 'x) n) 0)))))
(cmim-open! 1)
(cmim-setup!)
(let ((n_ (cmim-index!)))
  (cmim-beta!)
  (cmim-term! 'x 'x n_)
  (let* ((d (cmim-d 'x 'x n_)) (m (cmim-m 'x 'x n_)))
    (fact 'pseudometric-self-zero (list '(DISTS s) n_) cmim-P 'x)
    (dk-have! (list '= m 0)
              (lambda () (dk-ineq! (list '<= m d) (list '<= 0 m) (list '= d 0))))
    (subst (list '= m 0))
    (crs)))
(qed 'cmim-term-self-zero)

(sp (make-wff (cmim-full '(x) (list '= (cmim-dd 'x 'x) 0))))
(cmim-open! 1)
(let* ((lam (cmim-lam 'x 'x)) (sl (list 'SERIES-LIMIT lam)))
  (fact 'c-metric-term-seq-in-fun 's 'w 'x 'x)
  (fact 'c-metric-summable 's 'w 'x 'x)
  (let ((sz (dk-fact! 'cmim-term-self-zero 's 'w 'x)))
    (dk-have! (list 'FORALL 'i_ (list 'IMPLIES '(IN i_ NN)
                (list '= (list lam 'i_) (list '+ (list lam 'i_) (list lam 'i_)))))
      (lambda ()
        (let ((i (cadr (cmim-di-landed-1!))))
          (inst+ sz i)
          (subst (list '= (list lam i) 0))
          (arith)))))
  (fact 'series-limit-add lam lam lam)
  (fact 'series-limit-in-rr lam)
  (mac 'c-metric-distance)
  (dk-ineq! (list '= sl (list '+ sl sl))))
(qed 'cmim-dist-self-zero)

;;; =====================================================================
;;; L6, L7.  D(x,y) = 0 => x = y.  Each term lies between 0 and D = 0, so it
;;; vanishes; w(n) > 0 makes min(1, d_n) vanish (`rr-no-zero-divisors'); then
;;; `rr-min-cases': min(1,d_n) = 1 contradicts it, min(1,d_n) = d_n gives
;;; d_n = 0.  Every d_n(x,y) vanishes, and the separation law closes.
;;; =====================================================================

(sp (make-wff (cmim-termwise '(x y)
      (lambda (n) (list 'IMPLIES (list '= (list (cmim-lam 'x 'y) n) 0)
                        (list '= (cmim-d 'x 'y n) 0))))))
(cmim-open! 2)
(dk-peel-to! '=)
(cmim-setup!)
(let* ((n_ (cmim-index!))
       (lam (cmim-lam 'x 'y))
       (t (cmim-term! 'x 'y n_))
       (d (cmim-d 'x 'y n_))
       (m (cmim-m 'x 'y n_))
       (wn (list 'w n_)))
  (dk-have! (list '= (list lam n_) t) (lambda () (lam-b) (rfl)))
  (dk-have! (list '= t 0)
            (lambda () (subst (list '= t (list lam n_))) (ass)))
  (fact 'rr-no-zero-divisors wn m)
  (dk-have! (list '= m 0)
    (lambda ()
      (use-cases (list (list '= wn 0) (list '= m 0))
        (lambda () (dk-ineq! (list '< 0 wn) (list '= wn 0)))
        (lambda () (ass)))))
  (fact 'rr-min-cases 1 d)
  (use-cases (list (list '= m 1) (list '= m d))
    (lambda () (dk-ineq! (list '= m 1) (list '= m 0)))
    (lambda () (dk-ineq! (list '= m d) (list '= m 0)))))
(qed 'cmim-term-zero)

(sp (make-wff (cmim-full '(x y)
      (list 'IMPLIES (list '= (cmim-dd 'x 'y) 0) '(= x y)))))
(cmim-open! 2)
(dk-peel-to! '=)
(let* ((d (cmim-dd 'x 'y)) (lam (cmim-lam 'x 'y)))
  (fact 'c-metric-dist-converges 's 'w 'x 'y)
  (fact 'c-metric-term-seq-in-fun 's 'w 'x 'y)
  (fact 'cmim-dist-in-rr 's 'w 'x 'y)
  (let* ((nn- (dk-fact! 'cmim-term-nonneg 's 'w 'x 'y))
         (le  (dk-fact! 'series-term-le-sum lam d))
         (zt  (dk-fact! 'cmim-term-zero 's 'w 'x 'y))
         (all0 (list 'FORALL 'k_ (list 'IMPLIES '(IN k_ NN)
                 (list '= (cmim-d 'x 'y 'k_) 0)))))
    (dk-have! all0
      (lambda ()
        (let ((k (cadr (cmim-di-landed-1!))))
          (inst+ le k)
          (inst+ nn- k)
          (fact 'fun-apply-type-c lam 'NN 'RR k)
          (dk-have! (list '= (list lam k) 0)
            (lambda () (dk-ineq! (list '<= (list lam k) d)
                                 (list '= d 0)
                                 (list '<= 0 (list lam k)))))
          (inst+ zt k)
          (ass))))
    (mac-h 'IS-C-METRIC-SPACE '(IS-C-METRIC-SPACE s))
    (dk-split-all!)
    (let ((sep (dk-pick (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                                         (dk-contains? a 'DISTS)
                                         (not (dk-contains? a 'IS-PSEUDOMETRIC))))
                        "the separation law")))
      (inst*! sep 'x 'y)
      (ass))))
(qed 'cmim-dist-zero-eq)

;;; =====================================================================
;;; L8, L9.  Symmetry: termwise (as a <=, read both ways), then
;;; `series-limit-le' in both directions.
;;; =====================================================================

(sp (make-wff (cmim-termwise '(x y)
      (lambda (n) (list '<= (list (cmim-lam 'x 'y) n) (list (cmim-lam 'y 'x) n))))))
(cmim-open! 2)
(cmim-setup!)
(let ((n_ (cmim-index!)))
  (cmim-beta!)
  (cmim-term! 'x 'y n_)
  (cmim-term! 'y 'x n_)
  (fact 'pseudometric-sym (list '(DISTS s) n_) cmim-P 'x 'y)
  (subst (list '= (cmim-d 'x 'y n_) (cmim-d 'y 'x n_)))
  (dk-ineq!))
(qed 'cmim-term-sym)

(sp (make-wff (cmim-full '(x y) (list '= (cmim-dd 'x 'y) (cmim-dd 'y 'x)))))
(cmim-open! 2)
(fact 'c-metric-dist-converges 's 'w 'x 'y)
(fact 'c-metric-dist-converges 's 'w 'y 'x)
(fact 'c-metric-term-seq-in-fun 's 'w 'x 'y)
(fact 'c-metric-term-seq-in-fun 's 'w 'y 'x)
(fact 'cmim-dist-in-rr 's 'w 'x 'y)
(fact 'cmim-dist-in-rr 's 'w 'y 'x)
(fact 'cmim-term-sym 's 'w 'x 'y)
(fact 'cmim-term-sym 's 'w 'y 'x)
(fact 'series-limit-le (cmim-lam 'x 'y) (cmim-lam 'y 'x) (cmim-dd 'x 'y) (cmim-dd 'y 'x))
(fact 'series-limit-le (cmim-lam 'y 'x) (cmim-lam 'x 'y) (cmim-dd 'y 'x) (cmim-dd 'x 'y))
(dk-ineq! (list '<= (cmim-dd 'x 'y) (cmim-dd 'y 'x)) (list '<= (cmim-dd 'y 'x) (cmim-dd 'x 'y)))
(qed 'cmim-dist-sym)

;;; =====================================================================
;;; L10-L13.  The triangle inequality.  Termwise:
;;;   min(1, d(x,z)) <= min(1, d(x,y) + d(y,z)) <= min(1, d(x,y)) + min(1, d(y,z))
;;; by `rr-min-one-mono' and `rr-min-one-subadditive', scaled by w(n) >= 0
;;; through `rr-leq-mul-nonneg' on the difference; then `series-limit-le'
;;; against the sum sequence, whose sum `series-converges-to-add' names.
;;; =====================================================================

(sp (make-wff (cmim-full '(x y z) (list 'IN (cmim-sumlam 'x 'y 'z) '(FUN NN RR)))))
(cmim-open! 3)
(cmim-setup!)
(dk-lam-t!)
(let ((n_ (cmim-index!)))
  (let ((t1 (cmim-term! 'x 'y n_)) (t2 (cmim-term! 'y 'z n_)))
    (dk-have! (list 'AND (list 'IN t1 'RR) (list 'IN t2 'RR)))
    (fact 'rr-add-closed t1 t2)
    (ass)))
(qed 'cmim-sum-seq-in-fun)

(sp (make-wff (cmim-full '(x y z)
      (list 'FORALL 'i_ (list 'IMPLIES '(IN i_ NN)
            (list '= (list (cmim-sumlam 'x 'y 'z) 'i_)
                     (list '+ (list (cmim-lam 'x 'y) 'i_) (list (cmim-lam 'y 'z) 'i_))))))))
(cmim-open! 3)
(cmim-setup!)
(let ((n_ (cmim-index!)))
  (cmim-beta!)
  (cmim-term! 'x 'y n_) (cmim-term! 'y 'z n_)
  (crs))
(qed 'cmim-sum-seq-split)

(sp (make-wff (cmim-termwise '(x y z)
      (lambda (n) (list '<= (list (cmim-lam 'x 'z) n) (list (cmim-sumlam 'x 'y 'z) n))))))
(cmim-open! 3)
(cmim-setup!)
(let ((n_ (cmim-index!)))
  (cmim-beta!)
  (let* ((txz (cmim-term! 'x 'z n_))
         (txy (cmim-term! 'x 'y n_))
         (tyz (cmim-term! 'y 'z n_))
         (dxz (cmim-d 'x 'z n_)) (dxy (cmim-d 'x 'y n_)) (dyz (cmim-d 'y 'z n_))
         (mxz (cmim-m 'x 'z n_)) (mxy (cmim-m 'x 'y n_)) (myz (cmim-m 'y 'z n_))
         (ds  (list '+ dxy dyz))
         (mds (list 'min 1 ds))
         (msum (list '+ mxy myz))
         (dif (list '- msum mxz))
         (wn  (list 'w n_))
         (wd  (list '* wn dif)))
    (fact 'pseudometric-triangle (list '(DISTS s) n_) cmim-P 'x 'y 'z)
    (dk-have! (list 'AND (list 'IN dxy 'RR) (list 'IN dyz 'RR)))
    (fact 'rr-add-closed dxy dyz)
    (fact 'rr-min-one-mono dxz ds)
    (fact 'rr-min-one-subadditive dxy dyz)
    (fact 'rr-min-closed 1 ds)
    (dk-have! (list 'AND (list 'IN mxy 'RR) (list 'IN myz 'RR)))
    (fact 'rr-add-closed mxy myz)
    (fact 'rr-sub-in-rr msum mxz)
    (dk-have! (list '<= 0 dif)
              (lambda () (dk-ineq! (list '<= mxz mds) (list '<= mds msum))))
    (dk-have! (list 'AND (list 'IN wn 'RR) (list 'IN dif 'RR)))
    (fact 'rr-mul-closed wn dif)
    (dk-have! (list 'AND (list '<= 0 wn) (list '<= 0 dif)))
    (fact 'rr-leq-mul-nonneg wn dif)
    (dk-have! (list '= wd (list '- (list '+ txy tyz) txz)) (lambda () (crs)))
    (dk-ineq! (list '<= 0 wd) (list '= wd (list '- (list '+ txy tyz) txz)))))
(qed 'cmim-term-triangle)

(sp (make-wff (cmim-full '(x y z)
      (list '<= (cmim-dd 'x 'z) (list '+ (cmim-dd 'x 'y) (cmim-dd 'y 'z))))))
(cmim-open! 3)
(let ((h (cmim-sumlam 'x 'y 'z)))
  (fact 'c-metric-dist-converges 's 'w 'x 'y)
  (fact 'c-metric-dist-converges 's 'w 'y 'z)
  (fact 'c-metric-dist-converges 's 'w 'x 'z)
  (fact 'c-metric-term-seq-in-fun 's 'w 'x 'y)
  (fact 'c-metric-term-seq-in-fun 's 'w 'y 'z)
  (fact 'c-metric-term-seq-in-fun 's 'w 'x 'z)
  (fact 'cmim-dist-in-rr 's 'w 'x 'y)
  (fact 'cmim-dist-in-rr 's 'w 'y 'z)
  (fact 'cmim-dist-in-rr 's 'w 'x 'z)
  (fact 'cmim-sum-seq-in-fun 's 'w 'x 'y 'z)
  (fact 'cmim-sum-seq-split 's 'w 'x 'y 'z)
  (fact 'series-converges-to-add (cmim-lam 'x 'y) (cmim-lam 'y 'z) h
        (cmim-dd 'x 'y) (cmim-dd 'y 'z))
  (fact 'cmim-term-triangle 's 'w 'x 'y 'z)
  (dk-have! (list 'AND (list 'IN (cmim-dd 'x 'y) 'RR) (list 'IN (cmim-dd 'y 'z) 'RR)))
  (fact 'rr-add-closed (cmim-dd 'x 'y) (cmim-dd 'y 'z))
  (fact 'series-limit-le (cmim-lam 'x 'z) h (cmim-dd 'x 'z)
        (list '+ (cmim-dd 'x 'y) (cmim-dd 'y 'z)))
  (ass))
(qed 'cmim-dist-triangle)

;;; =====================================================================
;;; THE STRUCTURE PREDICATE.  The four conjuncts of the IS-METRIC-SPACE
;;; unfold: length 2, PTS in SET (off IS-C-METRIC-SPACE), the DIST typing (the
;;; IOTA is SERIES-LIMIT, `series-limit-iota', real by `series-limit-in-rr'),
;;; and is-metric, whose five laws are L3, L5, L7, L9, L13 by citation.
;;; =====================================================================

;; (IN (PTS s) SET), off IS-C-METRIC-SPACE(s), destroyed in this leaf only
(define (cmim-pts-set!)
  (if (dk-asm? (dk-goal))
      (ass)
      (begin
        (mac-h 'IS-C-METRIC-SPACE '(IS-C-METRIC-SPACE s))
        (dk-split-all!)
        (ass))))

(define (cmim-dist-typing!)
  (mac 'C-METRIC-W)
  (slot 'DIST)
  (nth-r)
  (for-each
   (lambda (k)
     (dk-focus! k)
     (let ((g (dk-goal)))
       (if (and (eq? (car g) 'IN) (eq? (caddr g) 'SET))
           (begin (mac 'cartesian-set-iff)
                  (cmim-and! (lambda () (cmim-pts-set!))))
           (begin
             (dk-peel!)
             ;; read the two points off the GOAL
             (let* ((gl  (dk-goal))
                    (lam (cadr (caddr (cadr gl))))       ; IOTA -> SCT -> sequence
                    (app (caddr (caddr (cadddr lam))))   ; d_k(x_, y_)
                    (x_  (cadr app))
                    (y_  (caddr app)))
               (fact 'series-limit-iota lam)
               (fact 'c-metric-term-seq-in-fun 's 'w x_ y_)
               (fact 'c-metric-summable 's 'w x_ y_)
               (fact 'series-limit-in-rr lam)
               (subst (list '== (list 'IOTA 'L (list 'SERIES-CONVERGES-TO lam 'L))
                                (list 'SERIES-LIMIT lam)))
               (ass))))))
   (dk-opened (lambda () (lam-t)))))

(define (cmim-law!)
  (let ((g (dk-goal)))
    (cond ((and (eq? (car g) '=) (equal? (caddr g) 0))
           (fact 'cmim-dist-self-zero 's 'w (cadr (cadr g))) (ass))
          ((and (eq? (car g) '<=) (equal? (cadr g) 0))
           (let ((d (caddr g))) (fact 'cmim-dist-nonneg 's 'w (cadr d) (caddr d)) (ass)))
          ((and (eq? (car g) '=) (symbol? (cadr g)) (symbol? (caddr g)))
           (fact 'cmim-dist-zero-eq 's 'w (cadr g) (caddr g)) (ass))
          ((eq? (car g) '=)
           (let ((d (cadr g))) (fact 'cmim-dist-sym 's 'w (cadr d) (caddr d)) (ass)))
          ((eq? (car g) '<=)
           (let* ((lhs (cadr g)) (rhs (caddr g))
                  (u (cadr lhs)) (z (caddr lhs)) (v (caddr (cadr rhs))))
             (fact 'cmim-dist-triangle 's 'w u v z)
             (ass)))
          (#t (error "cmim-law!: unexpected leaf" g)))))

(sp (make-wff '(FORALL s (IMPLIES (IS-C-METRIC-SPACE s)
     (FORALL w (IMPLIES (SUMMABLE-WEIGHT w)
       (IS-METRIC-SPACE (C-METRIC-W s w))))))))
(dk-peel-to! 'IS-METRIC-SPACE)
(mac 'IS-METRIC-SPACE)                       ; the GOAL only
(mac 'c-metric-carrier)                      ; PTS(C-METRIC-W s w) -> PTS(s)
(define cmim-conjuncts (cmim-split-goal!))
(for-each
 (lambda (n)
   (if (not (sequent-node-grounded? n))
       (begin
         (dk-focus! n)
         (let ((g (dk-goal)))
           (cond
             ((and (eq? (car g) '=) (pair? (cadr g)) (eq? (car (cadr g)) 'LENGTH))
              (mac 'C-METRIC-W) (len-r) (arith))
             ((equal? g '(IN (PTS s) SET)) (cmim-pts-set!))
             ((eq? (car g) 'IN) (cmim-dist-typing!))
             (#t 'is-metric-later))))))
 cmim-conjuncts)
(dk-focus-goal! "is-metric(")
(mac 'is-metric)
(cmim-drive!)
(for-each (lambda (n)
            (if (not (sequent-node-grounded? n))
                (begin (dk-focus! n) (cmim-law!))))
          (proof-leaves))
(qed 'c-metric-w-is-metric-space)
(topic! 'c-metric-w-is-metric-space 'constructions)
(alias! 'c-metric-w-is-metric-space
        "the weighted canonical metric of a countably-metrised space is a metric space")

;;; ---- the canonical instance -----------------------------------------

(sp (make-wff '(FORALL s (IMPLIES (IS-C-METRIC-SPACE s)
                  (IS-METRIC-SPACE (C-METRIC s))))))
(dk-peel-to! 'IS-METRIC-SPACE)
(mac 'C-METRIC)
(let* ((gl (dk-goal)) (cw (cadr gl)) (dw (caddr cw)))
  (fact 'product-metric-default-summable)
  (fact 'c-metric-w-is-metric-space 's dw)
  (ass))
(qed 'c-metric-is-metric-space)
(topic! 'c-metric-is-metric-space 'constructions)
(alias! 'c-metric-is-metric-space
        "the canonical metric of a countably-metrised space is a metric space")
