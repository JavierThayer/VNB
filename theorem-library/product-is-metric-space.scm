;;; product-is-metric-space.scm -- THE COUNTABLE PRODUCT OF METRIC SPACES IS A
;;; METRIC SPACE, proven -- retiring the asserted `product-is-metric-space' of
;;; structure-library/product-metric.scm (line 79).
;;;
;;;   IS-MS-SEQUENCE(ms), SUMMABLE-WEIGHT(w)  =>  IS-METRIC-SPACE(PRODUCT-METRIC-W(ms,w))
;;;
;;;   D_w(x,y) = SUM_n w(n) * rho_n(x(n), y(n)),   rho_n = d_n/(1+d_n).
;;;
;;; THE FOUR CONJUNCTS of the IS-METRIC-SPACE unfold, and where each is paid:
;;;
;;;   length = 2                unfold the functoid, `len-r', `arith'.
;;;   PTS in SET                PRODUCT-CARRIER is a SEP over FUN(NN, BIG-UNION_n
;;;                             PTS(ms n)), so `sep-set' + `fun-set-iff' + `bu-set'
;;;                             reduce it to NN in SET and PTS(ms n) in SET, the
;;;                             latter off the folded IS-METRIC-SPACE(ms n).
;;;   DIST typing               `lam-t' on the tupled lambda; the pointwise leaf is
;;;                             the IOTA being DEFINED, i.e. `series-limit-in-rr'
;;;                             at the term sequence -- reached through L2, which
;;;                             names the IOTA as SERIES-LIMIT.
;;;   is-metric                 the five laws, below.
;;;
;;; THE FIVE LAWS ARE ALL THE SAME MOVE: the termwise statement, plus ONE
;;; transfer from terms to sums.  The transfer is L1 (`series-limit-le'), and
;;; every law but the zero law is one citation of it:
;;;
;;;   0 <= D            `series-term-le-sum' at n = 0 (the sum dominates a term)
;;;   D(x,x) = 0        the terms vanish, so `series-limit-add' at f = g = h reads
;;;                     S = S + S.  NO "a series of zeros sums to zero" lemma is
;;;                     needed, and that is the one place the obvious route would
;;;                     have cost a CONVERGES-TO argument from scratch.
;;;   D(x,y) = 0 => x=y `series-term-le-sum' again -- each term is between 0 and
;;;                     D = 0 -- then w(n) > 0 and `rr-no-zero-divisors' give
;;;                     rho_n = 0, `metric-zero-eq' gives x(n) = y(n), and
;;;                     `fun-domain-extensionality' gives x = y.
;;;   D(x,y) = D(y,x)   L1 both ways, on termwise `metric-sym'.
;;;   triangle          L1 against the sequence n |-> w(n)rho_n(x,y) + w(n)rho_n(y,z),
;;;                     whose sum is D(x,y) + D(y,z) by `series-converges-to-add'.
;;;
;;; L1 itself is `series-partial-sum-le-termwise' (partial sums compare) read
;;; through `rr-limit-le' (limits compare) -- the two halves existed and had
;;; never been composed.
;;;
;;; WINDOW.  lo: theorem-library/product-summable -- product-metric-carrier,
;;; product-carrier-coord, product-carrier-unfold, bdd-metric-weight-bound,
;;; product-term-seq-in-fun, product-weighted-summable, product-metric-distance,
;;; product-metric-dist-converges.  Also theorem-library/limit-arithmetic
;;; (rr-limit-le, series-converges-to-add, series-limit-add),
;;; theorem-library/mono-le-limit (series-term-le-sum),
;;; theorem-library/dominated-convergence (series-limit-in-rr),
;;; theorem-library/comparison-test-proof (series-partial-sum-le-termwise,
;;; series-partial-sum-seq-in-fun, series-partial-sum-seq-apply),
;;; theorem-library/bdd-metric-basics (bdd-metric-is-metric-space,
;;; bdd-metric-bounded), theorem-library/bdd-metric-carrier,
;;; theorem-library/rr-order-basics (rr-no-zero-divisors),
;;; theorem-library/op-typing (metric-dist-real), structure-library/metric-laws.
;;; hi: theorem-library/tychonoff-proof, the earliest citer.
;;; product-summable currently loads BELOW tychonoff-proof and must move above
;;; it; nothing it needs loads later than dominated-convergence.
;;;
;;; Helper prefix: pim-.
;;; ---- the pim- kit ----------------------------------------------------

(define pim-P '(PRODUCT-CARRIER ms))

(define (pim-rho msn a b) (list (list 'DIST (list 'BDD-METRIC msn)) a b))
(define (pim-term x y n) (list '* (list 'w n) (pim-rho (list 'ms n) (list x n) (list y n))))
(define (pim-lam x y) (list 'VNB-LAMBDA 'n 'NN (pim-term x y 'n)))
(define (pim-sumlam x y z)
  (list 'VNB-LAMBDA 'n 'NN (list '+ (pim-term x y 'n) (pim-term y z 'n))))
(define (pim-D x y) (list '(DIST (PRODUCT-METRIC-W ms w)) x y))
(define (pim-psq s) (list 'VNB-LAMBDA 'k 'NN (list 'SERIES-PARTIAL-SUM s 'k)))

(define (pim-stmt vars body)
  (let loop ((vs vars))
    (if (null? vs) body
        (list 'FORALL (car vs)
              (list 'IMPLIES (list 'IN (car vs) pim-P) (loop (cdr vs)))))))
(define (pim-full vars body)
  (list 'FORALL 'ms (list 'IMPLIES '(IS-MS-SEQUENCE ms)
    (list 'FORALL 'w (list 'IMPLIES '(SUMMABLE-WEIGHT w)
      (pim-stmt vars body))))))

(define (pim-di-landed!)
  (let loop ((n 0))
    (let ((new (dk-landed* (lambda () (di)))))
      (cond ((pair? new) new)
            ((> n 5) (error "pim-di-landed!: di landed no assumption"))
            (#t (loop (+ n 1)))))))
(define (pim-di-landed-1!)
  (let ((new (pim-di-landed!)))
    (if (null? (cdr new)) (car new)
        (error "pim-di-landed-1!: expected 1" (map expression->string new)))))

;; the PRODUCT-CARRIER-typed eigenvariables of the focus context, peel order
(define (pim-points)
  (reverse (map cadr (filter (lambda (a) (and (pair? a) (eq? (car a) 'IN)
                                              (equal? (caddr a) pim-P)))
                             (dk-asms)))))
;; peel the standard prefix until N carrier points have landed.  `di' is GREEDY
;; over a guarded binder list, so one call can land every point AND the index.
(define (pim-open! n)
  (let loop ((k 0))
    (if (< (length (pim-points)) n)
        (begin (if (> k 20) (error "pim-open!: stuck"))
               (di) (loop (+ k 1)))))
  (pim-points))

;; the NN-typed eigenvariable of the focus context, peeling for it if needed
(define (pim-index!)
  (let loop ((k 0))
    (let ((a (find-first (lambda (f) (and (pair? f) (eq? (car f) 'IN) (eq? (caddr f) 'NN)))
                         (dk-asms))))
      (cond (a (cadr a))
            ((> k 6) (error "pim-index!: no NN index landed"))
            (#t (di) (loop (+ k 1)))))))

(define (pim-asm? f) (if (member f (dk-asms)) #t #f))
(define (pim-once! f thunk) (if (not (pim-asm? f)) (thunk)))

;; `ineq' with premises named by formula rather than by position
(define (pim-idx form)
  (let loop ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "pim-idx: not in context" form))
          ((equal? (car l) form) i) (#t (loop (cdr l) (+ i 1))))))
(define (pim-ineq . forms) (apply ineq (map pim-idx forms)))

;; the conjuncts of a context (< a b), landed without destroying it
(define (pim-from-lt! a b)
  (let ((lt (list '< a b)))
    (for-each
     (lambda (part)
       (dk-have! part (lambda ()
                        (dk-split! (dk-landed-find (lambda () (mac-h '< lt))
                                                   (lambda (f) (eq? (car f) 'AND))))
                        (ass))))
     (list (list '<= a b) (list 'NOT (list '= a b))))))

;; beta-reduce every redex in the goal
(define (pim-beta!)
  (let loop ((k 0))
    (let ((g (dk-goal)))
      (if (and (< k 8) (dk-contains? g 'VNB-LAMBDA))
          (begin (lam-b) (if (not (equal? (dk-goal) g)) (loop (+ k 1))))))))

;; the two hypothesis universals pim-coord! instantiates
(define pim-msu #f)
(define pim-wpos #f)
(define (pim-setup!)
  (dk-split! (dk-landed-find (lambda () (mac-h 'summable-weight '(SUMMABLE-WEIGHT w)))
                             (lambda (f) (eq? (car f) 'AND))))
  (mac-h 'is-ms-sequence '(IS-MS-SEQUENCE ms))
  (set! pim-msu (dk-pick (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                                          (dk-contains? a 'IS-METRIC-SPACE)))
                         "ms universal"))
  (set! pim-wpos (dk-pick (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                                           (dk-contains? a '<)))
                          "w positivity")))

;; the n-th factor is a metric space; its bounded metric too
(define (pim-factor! n)
  (pim-once! (list 'IS-METRIC-SPACE (list 'ms n)) (lambda () (inst+ pim-msu n)))
  (pim-once! (list 'IS-METRIC-SPACE (list 'BDD-METRIC (list 'ms n)))
             (lambda () (fact 'bdd-metric-is-metric-space (list 'ms n)))))

;; x(n) in PTS(ms n)  and  in PTS(BDD-METRIC (ms n))
(define (pim-pt! x n)
  (pim-once! (list 'IN (list x n) (list 'PTS (list 'ms n)))
             (lambda () (fact 'product-carrier-coord 'ms x n)))
  (pim-once! (list 'IN (list x n) (list 'PTS (list 'BDD-METRIC (list 'ms n))))
             (lambda ()
               (fact 'bdd-metric-carrier (list 'ms n))
               (dk-have! (list 'IN (list x n) (list 'PTS (list 'BDD-METRIC (list 'ms n))))
                         (lambda () (mac 'bdd-metric-carrier) (ass))))))

;; w(n) in RR, 0 < w(n), 0 <= w(n), w(n) /= 0
(define (pim-weight! n)
  (pim-once! (list 'IN (list 'w n) 'RR)
             (lambda ()
               (fact 'fun-apply-type-c 'w 'NN 'RR n)
               (inst+ pim-wpos n)
               (pim-from-lt! 0 (list 'w n))))
  ;; `pim-from-lt!' lands (NOT (= 0 w(n))).  `prop' reads an equation as an
  ;; OPAQUE atom, so the other orientation is a DIFFERENT atom to it and has to
  ;; be landed as well.  Assume w(n) = 0; then 0 = w(n) is 0 = 0 after one
  ;; subst, and the landed negation refutes it.  (Not `contra': that tactic
  ;; loads after the copilot, far below this file -- the cold load of
  ;; 2026-09-16 found it unbound here.)
  (pim-once! (list 'NOT (list '= (list 'w n) 0))
             (lambda ()
               (dk-have! (list 'NOT (list '= (list 'w n) 0))
                         (lambda ()
                           (di)
                           (have! (list '= 0 (list 'w n))
                                  (lambda () (subst (list '= (list 'w n) 0)) (arith)))
                           (dk-focus-having! (list '= 0 (list 'w n)))
                           (ai (list 'NOT (list '= 0 (list 'w n)))))))))

;; rho_n(x(n), y(n)) is a real number
(define (pim-rho-real! x y n)
  (pim-once! (list 'IN (pim-rho (list 'ms n) (list x n) (list y n)) 'RR)
             (lambda () (fact 'metric-dist-real (list 'BDD-METRIC (list 'ms n))
                              (list x n) (list y n)))))

;; everything one weighted coordinate distance owes; returns the term
(define (pim-coord! x y n)
  (let ((t (pim-term x y n)))
    (pim-factor! n) (pim-pt! x n) (pim-pt! y n) (pim-weight! n)
    (pim-rho-real! x y n)
    (if (not (pim-asm? (list 'IN t 'RR)))
        (begin
          (fact 'bdd-metric-weight-bound (list 'ms n) (list x n) (list y n) (list 'w n))
          (dk-split! (list 'AND (list 'IN t 'RR)
                           (list 'AND (list '<= 0 t) (list '<= t (list 'w n)))))))
    t))

;; (IN NN SET)?
(define (pim-nn-set-goal?) (equal? (dk-goal) '(IN NN SET)))

;; di-split the focus AND goal to its leaves and run CLOSER on each
(define (pim-and! closer)
  (let ((g (dk-goal)))
    (if (and (pair? g) (eq? (car g) 'AND))
        (for-each (lambda (k) (dk-focus! k) (pim-and! closer))
                  (dk-opened (lambda () (di))))
        (closer))))

;; split the focus AND goal all the way down; return the atom leaves
(define (pim-split-goal!)
  (let walk ((n (proof-state-focus *ps*)) (acc '()))
    (dk-focus! n)
    (let ((g (dk-goal)))
      (if (and (pair? g) (eq? (car g) 'AND))
          (let loop ((ks (dk-opened (lambda () (di)))) (acc acc))
            (if (null? ks) acc (loop (cdr ks) (walk (car ks) acc))))
          (cons n acc)))))

;; `di' every open leaf whose goal is a FORALL/IMPLIES/AND, to exhaustion
(define (pim-drive!)
  (let loop ((fuel 60))
    (let ((n (find-first (lambda (n)
                           (let ((g (dk-goal-of n)))
                             (and (not (sequent-node-grounded? n))
                                  (pair? g) (memq (car g) '(FORALL IMPLIES AND)))))
                         (proof-leaves))))
      (if (and n (> fuel 0)) (begin (dk-focus! n) (di) (loop (- fuel 1))) #t))))

;; (IN (PTS (ms n)) SET), off the folded IS-MS-SEQUENCE(ms).  `mac-h' is
;; destructive, but each leaf is its own sequent node, so the siblings keep it.
(define (pim-pts-set! n)
  (mac-h 'is-ms-sequence '(IS-MS-SEQUENCE ms))
  (let ((u (dk-pick (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                                     (dk-contains? a 'IS-METRIC-SPACE)))
                    "ms universal")))
    (inst+ u n))
  (mac-h 'IS-METRIC-SPACE (list 'IS-METRIC-SPACE (list 'ms n)))
  (dk-split-all!)
  (ass))

;; the focus goal is (IN (PRODUCT-CARRIER ms) SET)
(define (pim-carrier-set!)
  (mac 'PRODUCT-CARRIER)
  (sep-set)
  (mac 'fun-set-iff)
  (pim-and!
   (lambda ()
     (if (pim-nn-set-goal?)
         (begin (fact 'nn-is-set) (ass))
         (begin
           (bu-set)
           (pim-and!
            (lambda ()
              (if (pim-nn-set-goal?)
                  (begin (fact 'nn-is-set) (ass))
                  (pim-pts-set! (cadr (dk-landed-1 (lambda () (di))))))))))))) 

;;; =====================================================================
;;; L1.  series-limit-le -- A TERMWISE INEQUALITY BETWEEN TWO CONVERGENT
;;; SERIES PASSES TO THEIR SUMS.  `series-partial-sum-le-termwise' compares
;;; the partial sums; `rr-limit-le' compares the limits of two convergent
;;; sequences.  Both existed; nothing had composed them.
;;; =====================================================================

(sp (make-wff "forall([f in fun(nn,rr), g in fun(nn,rr), lv in rr, mv in rr],
     forall([n_ in nn], f(n_) <= g(n_)) implies
     series-converges-to(f, lv) implies series-converges-to(g, mv) implies
     lv <= mv)"))
(dk-peel-to! '<=)
(fact 'series-partial-sum-le-termwise 'f 'g)
(define pim-ps-le
  (dk-pick (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                            (dk-contains? a 'SERIES-PARTIAL-SUM)))
           "partial-sum termwise"))
(fact 'series-partial-sum-seq-in-fun 'f)
(fact 'series-partial-sum-seq-in-fun 'g)
;; the same comparison in the LAMBDA language rr-limit-le speaks
(dk-have! (list 'FORALL 'k_ (list 'IMPLIES '(IN k_ NN)
            (list '<= (list (pim-psq 'f) 'k_) (list (pim-psq 'g) 'k_))))
  (lambda ()
    (let ((k (cadr (pim-di-landed-1!))))
      (mac 'series-partial-sum-seq-apply)
      (inst+ pim-ps-le k)
      (ass))))
(mac-h 'series-converges-to '(SERIES-CONVERGES-TO f lv))
(mac-h 'series-converges-to '(SERIES-CONVERGES-TO g mv))
(fact 'rr-limit-le (pim-psq 'f) (pim-psq 'g) 'lv 'mv)
(ass)
(qed 'series-limit-le)
(topic! 'series-limit-le 'analysis)
(alias! 'series-limit-le "a termwise inequality passes to the sums")

;;; =====================================================================
;;; L2.  series-limit-iota -- the functoid's defining equation, as a THEOREM,
;;; and READ BACKWARDS.  `mac SERIES-LIMIT' turns SERIES-LIMIT(f) into the
;;; description; what the DIST typing leaf needs is the other direction, the
;;; goal there being the literal IOTA that PRODUCT-METRIC-W's lambda body is.
;;; =====================================================================

(sp (make-wff '(FORALL f (== (IOTA L (SERIES-CONVERGES-TO f L)) (SERIES-LIMIT f)))))
(di)
(mac 'SERIES-LIMIT)
(qrfl)
(qed 'series-limit-iota)
(topic! 'series-limit-iota 'analysis)
(alias! 'series-limit-iota "the sum of a series, as a description")

;;; =====================================================================
;;; L3.  product-dist-in-rr -- the product distance is a real number.
;;; =====================================================================

(sp (make-wff (pim-full '(x y) (list 'IN (pim-D 'x 'y) 'RR))))
(pim-open! 2)
(fact 'product-term-seq-in-fun 'ms 'w 'x 'y)
(fact 'product-weighted-summable 'ms 'w 'x 'y)
(fact 'series-limit-in-rr (pim-lam 'x 'y))
(mac 'product-metric-distance)
(ass)
(qed 'product-dist-in-rr)
(topic! 'product-dist-in-rr 'constructions)
(alias! 'product-dist-in-rr "the product distance is real")

;;; =====================================================================
;;; L4.  product-term-nonneg -- the terms of the defining series are >= 0.
;;; =====================================================================

(sp (make-wff (pim-full '(x y)
      (list 'FORALL 'n_ (list 'IMPLIES '(IN n_ NN)
            (list '<= 0 (list (pim-lam 'x 'y) 'n_)))))))
(pim-open! 2)
(pim-setup!)
(let ((n_ (pim-index!)))
  (pim-beta!)
  (pim-coord! 'x 'y n_)
  (ass))
(qed 'product-term-nonneg)
(topic! 'product-term-nonneg 'constructions)
(alias! 'product-term-nonneg "the terms of the product series are nonnegative")

;;; =====================================================================
;;; L5.  product-term-self-zero -- on the diagonal every term vanishes.
;;; =====================================================================

(sp (make-wff (pim-full '(x)
      (list 'FORALL 'n_ (list 'IMPLIES '(IN n_ NN)
            (list '= (list (pim-lam 'x 'x) 'n_) 0))))))
(pim-open! 1)
(pim-setup!)
(let ((n_ (pim-index!)))
  (pim-beta!)
  (pim-coord! 'x 'x n_)
  (fact 'metric-self-zero (list 'BDD-METRIC (list 'ms n_)) (list 'x n_))
  (subst (list '= (pim-rho (list 'ms n_) (list 'x n_) (list 'x n_)) 0))
  (crs))
(qed 'product-term-self-zero)
(topic! 'product-term-self-zero 'constructions)
(alias! 'product-term-self-zero "the diagonal terms of the product series vanish")

;;; =====================================================================
;;; L6.  product-term-sym -- termwise symmetry (as a `<=', so that L1 reads it
;;; in BOTH directions from the one statement, at (x,y) and at (y,x)).
;;; =====================================================================

(sp (make-wff (pim-full '(x y)
      (list 'FORALL 'n_ (list 'IMPLIES '(IN n_ NN)
            (list '<= (list (pim-lam 'x 'y) 'n_) (list (pim-lam 'y 'x) 'n_)))))))
(pim-open! 2)
(pim-setup!)
(let ((n_ (pim-index!)))
  (pim-beta!)
  (pim-coord! 'x 'y n_)
  (pim-coord! 'y 'x n_)
  (fact 'metric-sym (list 'BDD-METRIC (list 'ms n_)) (list 'x n_) (list 'y n_))
  (subst (list '= (pim-rho (list 'ms n_) (list 'x n_) (list 'y n_))
                  (pim-rho (list 'ms n_) (list 'y n_) (list 'x n_))))
  (pim-ineq))
(qed 'product-term-sym)
(topic! 'product-term-sym 'constructions)
(alias! 'product-term-sym "the product series is termwise symmetric")

;;; =====================================================================
;;; L7.  product-sum-seq-in-fun -- the termwise SUM of two coordinate series
;;; is a real sequence.  It is the `h' of series-converges-to-add.
;;; =====================================================================

(sp (make-wff (pim-full '(x y z) (list 'IN (pim-sumlam 'x 'y 'z) '(FUN NN RR)))))
(pim-open! 3)
(pim-setup!)
(dk-lam-t!)
(let ((n_ (pim-index!)))
  (let ((t1 (pim-coord! 'x 'y n_)) (t2 (pim-coord! 'y 'z n_)))
    (dk-have! (list 'AND (list 'IN t1 'RR) (list 'IN t2 'RR)))
    (fact 'rr-add-closed t1 t2)
    (ass)))
(qed 'product-sum-seq-in-fun)
(topic! 'product-sum-seq-in-fun 'constructions)
(alias! 'product-sum-seq-in-fun "the termwise sum of two coordinate series")

;;; =====================================================================
;;; L8.  product-sum-seq-split -- and it IS the termwise sum.
;;; =====================================================================

(sp (make-wff (pim-full '(x y z)
      (list 'FORALL 'i_ (list 'IMPLIES '(IN i_ NN)
            (list '= (list (pim-sumlam 'x 'y 'z) 'i_)
                     (list '+ (list (pim-lam 'x 'y) 'i_) (list (pim-lam 'y 'z) 'i_))))))))
(pim-open! 3)
(pim-setup!)
(let ((n_ (pim-index!)))
  (pim-beta!)
  (pim-coord! 'x 'y n_) (pim-coord! 'y 'z n_)
  (crs))
(qed 'product-sum-seq-split)
(topic! 'product-sum-seq-split 'constructions)
(alias! 'product-sum-seq-split "the sum sequence splits termwise")

;;; =====================================================================
;;; L9.  product-term-triangle -- the per-factor bounded triangle inequality,
;;; weighted.  rho_n is a metric (bdd-metric-is-metric-space), so
;;; rho(x,z) <= rho(x,y) + rho(y,z); multiplying by w(n) >= 0 is NOT linear,
;;; so it goes through `rr-leq-mul-nonneg' on the difference, as
;;; product-summable's own weight bound does.
;;; =====================================================================

(sp (make-wff (pim-full '(x y z)
      (list 'FORALL 'n_ (list 'IMPLIES '(IN n_ NN)
            (list '<= (list (pim-lam 'x 'z) 'n_) (list (pim-sumlam 'x 'y 'z) 'n_)))))))
(pim-open! 3)
(pim-setup!)
(let ((n_ (pim-index!)))
  (pim-beta!)
  (let* ((txz (pim-coord! 'x 'z n_))
         (txy (pim-coord! 'x 'y n_))
         (tyz (pim-coord! 'y 'z n_))
         (rxz (pim-rho (list 'ms n_) (list 'x n_) (list 'z n_)))
         (rxy (pim-rho (list 'ms n_) (list 'x n_) (list 'y n_)))
         (ryz (pim-rho (list 'ms n_) (list 'y n_) (list 'z n_)))
         (sum (list '+ rxy ryz))
         (dif (list '- sum rxz))
         (wn  (list 'w n_))
         (wd  (list '* wn dif)))
    (fact 'metric-triangle (list 'BDD-METRIC (list 'ms n_))
          (list 'x n_) (list 'y n_) (list 'z n_))
    (dk-have! (list 'AND (list 'IN rxy 'RR) (list 'IN ryz 'RR)))
    (fact 'rr-add-closed rxy ryz)
    (fact 'rr-sub-in-rr sum rxz)
    (dk-have! (list '<= 0 dif) (lambda () (pim-ineq (list '<= rxz sum))))
    (dk-have! (list 'AND (list 'IN wn 'RR) (list 'IN dif 'RR)))
    (fact 'rr-mul-closed wn dif)
    (dk-have! (list 'AND (list '<= 0 wn) (list '<= 0 dif)))
    (fact 'rr-leq-mul-nonneg wn dif)
    (dk-have! (list '= wd (list '- (list '+ txy tyz) txz)) (lambda () (crs)))
    (pim-ineq (list '<= 0 wd) (list '= wd (list '- (list '+ txy tyz) txz)))))
(qed 'product-term-triangle)
(topic! 'product-term-triangle 'constructions)
(alias! 'product-term-triangle "the weighted per-factor triangle inequality")

;;; =====================================================================
;;; THE THEOREM.  Statement VERBATIM from the support this file retires
;;; (structure-library/product-metric.scm:79).
;;; =====================================================================

;;; ---- the DIST slot typing -------------------------------------------
(define (pim-dist-typing!)
  (mac 'PRODUCT-METRIC-W)
  (slot 'DIST)
  (nth-r)
  (for-each
   (lambda (k)
     (dk-focus! k)
     (let ((g (dk-goal)))
       (if (and (eq? (car g) 'IN) (eq? (caddr g) 'SET))
           ;; the SETHOOD leaf lam-t always owes
           (begin (mac 'cartesian-set-iff)
                  (pim-and! (lambda () (pim-carrier-set!))))
           ;; the pointwise typing: the IOTA has to DENOTE
           (begin
             (dk-peel!)
             ;; read the two points off the GOAL, never off the context: the
             ;; assumption list is not in peel order here, and a swap builds a
             ;; term sequence that is alpha-INEQUIVALENT to the goal's.
             (let* ((gl  (dk-goal))
                    (lam (cadr (caddr (cadr gl))))       ; IOTA -> SCT -> sequence
                    (app (caddr (cadddr lam)))           ; (rho (x_ n) (y_ n))
                    (x_  (car (cadr app)))
                    (y_  (car (caddr app))))
               (fact 'series-limit-iota lam)
               (fact 'product-term-seq-in-fun 'ms 'w x_ y_)
               (fact 'product-weighted-summable 'ms 'w x_ y_)
               (fact 'series-limit-in-rr lam)
               (subst (list '== (list 'IOTA 'L (list 'SERIES-CONVERGES-TO lam 'L))
                                (list 'SERIES-LIMIT lam)))
               (ass))))))
   (dk-opened (lambda () (lam-t)))))

;;; ---- x in FUN(NN), for fun-domain-extensionality ---------------------
(define (pim-fun-typing! x)
  (mac-h 'product-carrier-unfold (list 'IN x '(PRODUCT-CARRIER ms)))
  (sep-me (dk-pick (lambda (a) (and (pair? a) (eq? (car a) 'IN) (equal? (cadr a) x)
                                    (pair? (caddr a)) (eq? (car (caddr a)) 'SEP)))
                   "sep membership"))
  (dk-split! (dk-landed-find
              (lambda ()
                (mac-h 'fun-codomain-iff
                       (dk-pick (lambda (a) (and (pair? a) (eq? (car a) 'IN)
                                                 (equal? (cadr a) x)
                                                 (pair? (caddr a))
                                                 (eq? (car (caddr a)) 'FUN)
                                                 (= (length (caddr a)) 3)))
                                "fun typing")))
              (lambda (f) (eq? (car f) 'AND)))))

;;; ---- the five metric laws -------------------------------------------
(define (pim-law-nonneg!)
  (let* ((g (dk-goal)) (d (caddr g)) (u (cadr d)) (v (caddr d)) (lam (pim-lam u v)))
    (fact 'product-metric-dist-converges 'ms 'w u v)
    (fact 'product-term-seq-in-fun 'ms 'w u v)
    (fact 'product-dist-in-rr 'ms 'w u v)
    (let ((nn- (dk-fact! 'product-term-nonneg 'ms 'w u v)))
      (fact 'nn-zero-in)
      (fact 'series-term-le-sum lam d 0)
      (inst+ nn- 0)
      (fact 'fun-apply-type-c lam 'NN 'RR 0)
      (pim-ineq (list '<= (list lam 0) d) (list '<= 0 (list lam 0))))))

(define (pim-law-zero!)
  (let* ((g (dk-goal)) (d (cadr g)) (u (cadr d)) (lam (pim-lam u u))
         (sl (list 'SERIES-LIMIT lam)))
    (fact 'product-term-seq-in-fun 'ms 'w u u)
    (fact 'product-weighted-summable 'ms 'w u u)
    (let ((sz (dk-fact! 'product-term-self-zero 'ms 'w u)))
      (dk-have! (list 'FORALL 'i_ (list 'IMPLIES '(IN i_ NN)
                  (list '= (list lam 'i_) (list '+ (list lam 'i_) (list lam 'i_)))))
        (lambda ()
          (let ((i (cadr (pim-di-landed-1!))))
            (inst+ sz i)
            (subst (list '= (list lam i) 0))
            (arith)))))
    (fact 'series-limit-add lam lam lam)
    (fact 'series-limit-in-rr lam)
    (mac 'product-metric-distance)
    (pim-ineq (list '= sl (list '+ sl sl)))))

(define (pim-law-sym!)
  (let* ((g (dk-goal)) (a (cadr g)) (u (cadr a)) (v (caddr a)))
    (fact 'product-metric-dist-converges 'ms 'w u v)
    (fact 'product-metric-dist-converges 'ms 'w v u)
    (fact 'product-term-seq-in-fun 'ms 'w u v)
    (fact 'product-term-seq-in-fun 'ms 'w v u)
    (fact 'product-dist-in-rr 'ms 'w u v)
    (fact 'product-dist-in-rr 'ms 'w v u)
    (fact 'product-term-sym 'ms 'w u v)
    (fact 'product-term-sym 'ms 'w v u)
    (fact 'series-limit-le (pim-lam u v) (pim-lam v u) (pim-D u v) (pim-D v u))
    (fact 'series-limit-le (pim-lam v u) (pim-lam u v) (pim-D v u) (pim-D u v))
    (pim-ineq (list '<= (pim-D u v) (pim-D v u)) (list '<= (pim-D v u) (pim-D u v)))))

(define (pim-law-triangle!)
  (let* ((g (dk-goal)) (lhs (cadr g)) (rhs (caddr g))
         (u (cadr lhs)) (z (caddr lhs)) (v (caddr (cadr rhs)))
         (h (pim-sumlam u v z)))
    (fact 'product-metric-dist-converges 'ms 'w u v)
    (fact 'product-metric-dist-converges 'ms 'w v z)
    (fact 'product-metric-dist-converges 'ms 'w u z)
    (fact 'product-term-seq-in-fun 'ms 'w u v)
    (fact 'product-term-seq-in-fun 'ms 'w v z)
    (fact 'product-term-seq-in-fun 'ms 'w u z)
    (fact 'product-dist-in-rr 'ms 'w u v)
    (fact 'product-dist-in-rr 'ms 'w v z)
    (fact 'product-dist-in-rr 'ms 'w u z)
    (fact 'product-sum-seq-in-fun 'ms 'w u v z)
    (fact 'product-sum-seq-split 'ms 'w u v z)
    (fact 'series-converges-to-add (pim-lam u v) (pim-lam v z) h
          (pim-D u v) (pim-D v z))
    (fact 'product-term-triangle 'ms 'w u v z)
    (dk-have! (list 'AND (list 'IN (pim-D u v) 'RR) (list 'IN (pim-D v z) 'RR)))
    (fact 'rr-add-closed (pim-D u v) (pim-D v z))
    (fact 'series-limit-le (pim-lam u z) h (pim-D u z)
          (list '+ (pim-D u v) (pim-D v z)))
    (ass)))

(define (pim-law-zero-eq!)
  (let* ((g (dk-goal)) (u (cadr g)) (v (caddr g))
         (d (pim-D u v)) (lam (pim-lam u v)))
    (fact 'product-metric-dist-converges 'ms 'w u v)
    (fact 'product-term-seq-in-fun 'ms 'w u v)
    (fact 'product-dist-in-rr 'ms 'w u v)
    (let* ((nn- (dk-fact! 'product-term-nonneg 'ms 'w u v))
           (le  (dk-fact! 'series-term-le-sum lam d)))
      (pim-setup!)
      (dk-have! (list 'FORALL 'k_ (list 'IMPLIES '(IN k_ NN)
                  (list '= (list u 'k_) (list v 'k_))))
        (lambda ()
          (let ((k (cadr (pim-di-landed-1!))))
            (inst+ le k)
            (inst+ nn- k)
            (fact 'fun-apply-type-c lam 'NN 'RR k)
            (let* ((t   (pim-coord! u v k))
                   (rho (pim-rho (list 'ms k) (list u k) (list v k)))
                   (wk  (list 'w k)))
              (dk-have! (list '= (list lam k) t) (lambda () (lam-b) (rfl)))
              (dk-have! (list '= t 0)
                (lambda () (pim-ineq (list '= (list lam k) t)
                                     (list '<= (list lam k) d)
                                     (list '= d 0)
                                     (list '<= 0 t))))
              (fact 'rr-no-zero-divisors wk rho)
              (dk-have! (list '= rho 0) (lambda () (prop)))
              (fact 'metric-zero-eq (list 'BDD-METRIC (list 'ms k)) (list u k) (list v k))
              (ass))))))
    (pim-fun-typing! u)
    (pim-fun-typing! v)
    (fact 'fun-domain-extensionality 'NN u v)
    (ass)))

(define (pim-law!)
  (let ((g (dk-goal)))
    (cond ((and (eq? (car g) '=) (equal? (caddr g) 0))          (pim-law-zero!))
          ((and (eq? (car g) '<=) (equal? (cadr g) 0))          (pim-law-nonneg!))
          ((and (eq? (car g) '=) (symbol? (cadr g)) (symbol? (caddr g)))
                                                                (pim-law-zero-eq!))
          ((eq? (car g) '=)                                     (pim-law-sym!))
          ((eq? (car g) '<=)                                    (pim-law-triangle!))
          (#t (error "pim-law!: unexpected leaf" g)))))

;;; ---- the driver ------------------------------------------------------
(sp (make-wff '(FORALL ms (IMPLIES (IS-MS-SEQUENCE ms)
     (FORALL w (IMPLIES (SUMMABLE-WEIGHT w)
       (IS-METRIC-SPACE (PRODUCT-METRIC-W ms w))))))))
(dk-peel-to! 'IS-METRIC-SPACE)
(mac 'IS-METRIC-SPACE)                       ; the GOAL only
(mac 'product-metric-carrier)                ; PTS(PRODUCT-METRIC-W ms w) -> PRODUCT-CARRIER ms
(define pim-conjuncts (pim-split-goal!))

;; everything but `is-metric', which is left for last so pim-drive! sees only
;; its own descendants.
(for-each
 (lambda (n)
   (if (not (sequent-node-grounded? n))
       (begin
         (dk-focus! n)
         (let ((g (dk-goal)))
           (cond
             ((and (eq? (car g) '=) (pair? (cadr g)) (eq? (car (cadr g)) 'LENGTH))
              (mac 'PRODUCT-METRIC-W) (len-r) (arith))
             ((equal? g '(IN (PRODUCT-CARRIER ms) SET)) (pim-carrier-set!))
             ((eq? (car g) 'IN) (pim-dist-typing!))
             (#t 'is-metric-later))))))
 pim-conjuncts)

;; now the metric laws.
(dk-focus-goal! "is-metric(")
(mac 'is-metric)
(pim-drive!)
(for-each (lambda (n)
            (if (not (sequent-node-grounded? n))
                (begin (dk-focus! n) (pim-law!))))
          (proof-leaves))
(qed 'product-is-metric-space)
