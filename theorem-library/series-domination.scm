;;; series-domination.scm -- SHIFTING AND EVENTUAL DOMINATION FOR REAL SERIES.
;;; Batch 26-A, 2026-09-24.  The two lemmas the batch-25 report named as standing
;;; in the way of Proposition 2.10 (theorem-library/cc-power-series-deriv.scm):
;;;
;;;   series-shift-partial-sum   S(f, k+1) = f(0) + S(g, k)  when g(k) = f(k+1)
;;;   series-shift-converges-iff for f >= 0 and g(k) = f(k+1):
;;;                              sum f converges iff sum g converges
;;;   series-eventually-dominated-converges
;;;                              f, g >= 0, f(k) <= g(k) from an index N on,
;;;                              sum g converges  =>  sum f converges
;;;
;;; SERIES-PARTIAL-SUM(f, k) is the sum of f(j) for j < k (series-partial-sum-zero,
;;; series-partial-sum-succ).  The shifted series g is GIVEN BY ITS VALUES
;;; (g(k) = f(succ(k)) for every k), as cps-radius-factor gives its product
;;; sequence: no lambda is applied under a binder.
;;;
;;; THE ROUTE.  Both convergence facts go through BOUNDED PARTIAL SUMS
;;; (series-partial-sum-bounded one way, series-bounded-converges of
;;; theorem-library/limsup-tests.scm the other), which is why non-negativity is a
;;; hypothesis: every series these lemmas are used on (sum |a_k| r^k and its
;;; relatives) is non-negative.  The eventual domination is the bound
;;; S(f, k) <= S(f, N) + S(g, k), proven by induction on k.
;;;
;;; Helper prefix: cpd-sd-.  Theorem binders cpd..._ besides f, g.
;;; LOAD WINDOW: lo = theorem-library/limsup-tests (series-bounded-converges); the
;;; rest (series-partial-sum-*, dominated-convergence's series-partial-sum-bounded,
;;; nn- and rr- order facts) is far below.  hi: theorem-library/cc-power-series-deriv.

(define (cpd-sd-head g) (and (pair? g) (car g)))

;;; rewrite S(F, succ(K)) to S(F, K) + F(K) in the goal, by the instance of
;;; series-partial-sum-succ (its two typings must be in context), and nothing else
(define (cpd-sd-succ! fn k)
  (subst (dk-fact! 'series-partial-sum-succ fn k)))

(define cpd-sd-shift '(FORALL cpdj_ (IMPLIES (IN cpdj_ NN) (= (g cpdj_) (f (succ cpdj_))))))
(define cpd-sd-fnn '(FORALL cpdj_ (IMPLIES (IN cpdj_ NN) (<= 0 (f cpdj_)))))
(define cpd-sd-gnn '(FORALL cpdj_ (IMPLIES (IN cpdj_ NN) (<= 0 (g cpdj_)))))

;;; ======================================================================
;;; (1) S(f, k+1) = f(0) + S(g, k)
;;; ======================================================================
(sp (make-wff
  (list 'FORALL 'cpdk_ (list 'IMPLIES '(IN cpdk_ NN)
    (list 'FORALL 'f (list 'IMPLIES '(IN f (FUN NN RR))
      (list 'FORALL 'g (list 'IMPLIES '(IN g (FUN NN RR))
        (list 'IMPLIES cpd-sd-shift
          '(= (SERIES-PARTIAL-SUM f (succ cpdk_)) (+ (f 0) (SERIES-PARTIAL-SUM g cpdk_))))))))))))
(define cpd-sd-br (use-induction))
(dk-focus! (cdr (assq 'base cpd-sd-br)))
(dk-peel!)
(fact 'nn-zero-in)
(fact 'fun-apply-type-c 'f 'NN 'RR 0)
(fact 'series-partial-sum-in-rr 0 'f)
(cpd-sd-succ! 'f 0)
(mac 'series-partial-sum-zero)
(crs)
(dk-focus! (cdr (assq 'step cpd-sd-br)))
(define cpd-sd-v (cdr (assq 'var cpd-sd-br)))
(define cpd-sd-ih (cdr (assq 'ih cpd-sd-br)))
(dk-peel!)
(let* ((v cpd-sd-v) (sv (list 'succ v)))
  (dk-apply! cpd-sd-ih 'f 'g)
  (fact 'nn-succ-closed v)
  (fact 'nn-zero-in)
  (fact 'fun-apply-type-c 'f 'NN 'RR 0)
  (fact 'fun-apply-type-c 'f 'NN 'RR sv)
  (fact 'fun-apply-type-c 'g 'NN 'RR v)
  (fact 'series-partial-sum-in-rr sv 'f)
  (fact 'series-partial-sum-in-rr v 'g)
  (inst+ cpd-sd-shift v)
  (cpd-sd-succ! 'f sv)
  (cpd-sd-succ! 'g v)
  (subst (list '= (list 'SERIES-PARTIAL-SUM 'f sv) (list '+ '(f 0) (list 'SERIES-PARTIAL-SUM 'g v))))
  (subst (list '= (list 'g v) (list 'f sv)))
  (crs))
(qed 'series-shift-partial-sum)

;;; ======================================================================
;;; (2) for f >= 0: sum f converges iff sum_k f(k+1) converges
;;; ======================================================================
(sp (make-wff
  (list 'FORALL 'f (list 'IMPLIES '(IN f (FUN NN RR)) (list 'IMPLIES cpd-sd-fnn
    (list 'FORALL 'g (list 'IMPLIES '(IN g (FUN NN RR))
      (list 'IMPLIES cpd-sd-shift
        '(IFF (SERIES-CONVERGES f) (SERIES-CONVERGES g))))))))))
(dk-peel!)
(fact 'nn-zero-in)
(fact 'fun-apply-type-c 'f 'NN 'RR 0)
(inst+ cpd-sd-fnn 0)
(have! cpd-sd-gnn
  (lambda ()
    (let ((j (dk-di-var!)))
      (fact 'nn-succ-closed j)
      (inst+ cpd-sd-fnn (list 'succ j))
      (inst+ cpd-sd-shift j)
      (subst (list '= (list 'g j) (list 'f (list 'succ j))))
      (ass))))
(dk-iff!
  (lambda (g) (equal? g '(SERIES-CONVERGES g)))
  (lambda ()
    ;; sum f converges => S(f) <= B => S(g, k) = S(f, k+1) - f(0) <= B - f(0)
    (let* ((b (dk-skolem! (dk-fact! 'series-partial-sum-bounded 'f)))
           (bd (dk-pick (lambda (x) (and (eq? (cpd-sd-head x) 'FORALL) (dk-contains? x b))) "bound")))
      (fact 'rr-sub-in-rr b '(f 0))
      (have! (list 'FORALL 'cpdk_ (list 'IMPLIES '(IN cpdk_ NN)
                (list '<= '(SERIES-PARTIAL-SUM g cpdk_) (list '- b '(f 0)))))
        (lambda ()
          (let ((k (dk-di-var!)))
            (fact 'nn-succ-closed k)
            (inst+ bd (list 'succ k))
            (fact 'series-shift-partial-sum k 'f 'g)
            (fact 'series-partial-sum-in-rr k 'g)
            (fact 'series-partial-sum-in-rr (list 'succ k) 'f)
            (dk-ineq! (list '<= (list 'SERIES-PARTIAL-SUM 'f (list 'succ k)) b)
                      (list '= (list 'SERIES-PARTIAL-SUM 'f (list 'succ k))
                               (list '+ '(f 0) (list 'SERIES-PARTIAL-SUM 'g k)))))))
      (fact 'series-bounded-converges 'g (list '- b '(f 0)))
      (ass)))
  (lambda ()
    ;; sum g converges => S(g) <= B => S(f, k) <= S(f, k+1) = f(0) + S(g, k) <= f(0) + B
    (let* ((b (dk-skolem! (dk-fact! 'series-partial-sum-bounded 'g)))
           (bd (dk-pick (lambda (x) (and (eq? (cpd-sd-head x) 'FORALL) (dk-contains? x b))) "bound"))
           (mono (dk-deepest (lambda () (fact 'series-partial-sum-monotone-nonneg 'f)))))
      (fact 'rr-add-in-rr '(f 0) b)
      (have! (list 'FORALL 'cpdk_ (list 'IMPLIES '(IN cpdk_ NN)
                (list '<= '(SERIES-PARTIAL-SUM f cpdk_) (list '+ '(f 0) b))))
        (lambda ()
          (let ((k (dk-di-var!)))
            (inst+ bd k)
            (inst+ mono k)
            (fact 'series-shift-partial-sum k 'f 'g)
            (fact 'series-partial-sum-in-rr k 'g)
            (fact 'nn-succ-closed k)
            (fact 'series-partial-sum-in-rr k 'f)
            (fact 'series-partial-sum-in-rr (list 'succ k) 'f)
            (dk-ineq! (list '<= (list 'SERIES-PARTIAL-SUM 'g k) b)
                      (list '<= (list 'SERIES-PARTIAL-SUM 'f k) (list 'SERIES-PARTIAL-SUM 'f (list 'succ k)))
                      (list '= (list 'SERIES-PARTIAL-SUM 'f (list 'succ k))
                               (list '+ '(f 0) (list 'SERIES-PARTIAL-SUM 'g k)))))))
      (fact 'series-bounded-converges 'f (list '+ '(f 0) b))
      (ass))))
(qed 'series-shift-converges-iff)

;;; ======================================================================
;;; (3) eventual domination
;;; ======================================================================
(define cpd-sd-dom '(FORALL cpdj_ (IMPLIES (IN cpdj_ NN) (IMPLIES (<= cpdn_ cpdj_) (<= (f cpdj_) (g cpdj_))))))

;;; the bound S(f, k) <= S(f, N) + S(g, k), by induction on k
(sp (make-wff
  (list 'FORALL 'cpdk_ (list 'IMPLIES '(IN cpdk_ NN)
    (list 'FORALL 'f (list 'IMPLIES '(IN f (FUN NN RR)) (list 'IMPLIES cpd-sd-fnn
      (list 'FORALL 'g (list 'IMPLIES '(IN g (FUN NN RR)) (list 'IMPLIES cpd-sd-gnn
        (list 'FORALL 'cpdn_ (list 'IMPLIES '(IN cpdn_ NN)
          (list 'IMPLIES cpd-sd-dom
            '(<= (SERIES-PARTIAL-SUM f cpdk_)
                 (+ (SERIES-PARTIAL-SUM f cpdn_) (SERIES-PARTIAL-SUM g cpdk_))))))))))))))))
(define cpd-sd-br2 (use-induction))
(dk-focus! (cdr (assq 'base cpd-sd-br2)))
(dk-peel!)
(fact 'series-partial-sum-nonneg 'cpdn_ 'f)
(fact 'series-partial-sum-in-rr 'cpdn_ 'f)
(mac 'series-partial-sum-zero)
(dk-ineq! '(<= 0 (SERIES-PARTIAL-SUM f cpdn_)))
(dk-focus! (cdr (assq 'step cpd-sd-br2)))
(define cpd-sd-v2 (cdr (assq 'var cpd-sd-br2)))
(define cpd-sd-ih2 (cdr (assq 'ih cpd-sd-br2)))
(dk-peel!)
(let* ((v cpd-sd-v2) (sv (list 'succ v))
       (sfn '(SERIES-PARTIAL-SUM f cpdn_))
       (sfv (list 'SERIES-PARTIAL-SUM 'f v)) (sgv (list 'SERIES-PARTIAL-SUM 'g v))
       (sfs (list 'SERIES-PARTIAL-SUM 'f sv)) (sgs (list 'SERIES-PARTIAL-SUM 'g sv)))
  (fact 'nn-succ-closed v)
  (fact 'series-partial-sum-in-rr 'cpdn_ 'f)
  (fact 'series-partial-sum-in-rr v 'f)
  (fact 'series-partial-sum-in-rr v 'g)
  (fact 'series-partial-sum-in-rr sv 'f)
  (fact 'series-partial-sum-in-rr sv 'g)
  (fact 'series-partial-sum-nonneg sv 'g)
  (use-em (list '<= 'cpdn_ v)
    (lambda ()
      ;; N <= v: S(f, v+1) = S(f, v) + f(v) <= S(f, N) + S(g, v) + g(v)
      (dk-apply! cpd-sd-ih2 'f 'g 'cpdn_)
      (inst+ cpd-sd-dom v)
      (fact 'fun-apply-type-c 'f 'NN 'RR v)
      (fact 'fun-apply-type-c 'g 'NN 'RR v)
      (cpd-sd-succ! 'f v)
      (cpd-sd-succ! 'g v)
      (dk-ineq! (list '<= sfv (list '+ sfn sgv))
                (list '<= (list 'f v) (list 'g v))))
    (lambda ()
      ;; not N <= v: v+1 <= N, S(f, v+1) <= S(f, N) and S(g, v+1) >= 0
      (fact 'nn-not-le-succ-le 'cpdn_ v)
      (fact 'series-partial-sum-mono 'cpdn_ sv 'f)
      (dk-ineq! (list '<= sfs sfn) (list '<= 0 sgs)))))
(qed 'series-dominated-partial-bound)

(sp (make-wff
  (list 'FORALL 'f (list 'IMPLIES '(IN f (FUN NN RR)) (list 'IMPLIES cpd-sd-fnn
    (list 'FORALL 'g (list 'IMPLIES '(IN g (FUN NN RR)) (list 'IMPLIES cpd-sd-gnn
      (list 'FORALL 'cpdn_ (list 'IMPLIES '(IN cpdn_ NN)
        (list 'IMPLIES cpd-sd-dom
          '(IMPLIES (SERIES-CONVERGES g) (SERIES-CONVERGES f)))))))))))))
(dk-peel!)
(let* ((b (dk-skolem! (dk-fact! 'series-partial-sum-bounded 'g)))
       (bd (dk-pick (lambda (x) (and (eq? (cpd-sd-head x) 'FORALL) (dk-contains? x b))) "bound"))
       (sfn '(SERIES-PARTIAL-SUM f cpdn_))
       (tot (list '+ sfn b)))
  (fact 'series-partial-sum-in-rr 'cpdn_ 'f)
  (fact 'rr-add-in-rr sfn b)
  (have! (list 'FORALL 'cpdk_ (list 'IMPLIES '(IN cpdk_ NN) (list '<= '(SERIES-PARTIAL-SUM f cpdk_) tot)))
    (lambda ()
      (let ((k (dk-di-var!)))
        (inst+ bd k)
        (fact 'series-dominated-partial-bound k 'f 'g 'cpdn_)
        (fact 'series-partial-sum-in-rr k 'f)
        (fact 'series-partial-sum-in-rr k 'g)
        (dk-ineq! (list '<= (list 'SERIES-PARTIAL-SUM 'f k) (list '+ sfn (list 'SERIES-PARTIAL-SUM 'g k)))
                  (list '<= (list 'SERIES-PARTIAL-SUM 'g k) b)))))
  (fact 'series-bounded-converges 'f tot)
  (ass))
(qed 'series-eventually-dominated-converges)
