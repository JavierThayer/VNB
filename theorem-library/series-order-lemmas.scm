;;; series-order-lemmas.scm -- order facts about real partial sums and limits.
;;;
;;; These are the infinite-sum half of the inequality suite -- needed regardless
;;; of the linear-arithmetic oracle (which is finite/linear).  The keystone is
;;; monotone-convergence on RR, which comparison-test (power-series.scm) already
;;; cites by name as "not yet in the library"; the rest are the monotonicity and
;;; Cauchy-criterion facts that back comparison-test, summable-cauchy, and the
;;; absolute => convergent bridges.
;;;
;;; Real sequence vars are f, g (NOT `a' -> accessor A); index n_ / m (NOT `n'
;;; alone where it could fold with N); a bound is bnd; eps as usual.  Loads after
;;; power-series (SERIES-PARTIAL-SUM / SERIES-CONVERGES) and order-lemmas.
;;;
;;; Library-build phase: warranted well-known [[feedback-library-axioms-fine]].
;;; Dependencies: power-series.scm (SERIES-PARTIAL-SUM, SERIES-CONVERGES),
;;; metric-completeness.scm (CONVERGES), numeric-instances.scm (RR-MS),
;;; order-predicates.scm (POS-RR, <), number-systems.scm (RR, <=, abs).

;;; -----------------------------------------------------------------------
;;; Monotone convergence on RR -- the keystone comparison-test depends on.
;;; A nondecreasing real sequence bounded above converges (to its sup).
(support 'monotone-convergence-rr
  '(FORALL f (IMPLIES (IN f (FUN NN RR))
     (IMPLIES (AND (FORALL k (IMPLIES (IN k NN) (<= (f k) (f (succ k)))))
                   (FORSOME bnd (AND (IN bnd RR)
                     (FORALL k (IMPLIES (IN k NN) (<= (f k) bnd))))))
       (CONVERGES RR-MS f)))))
(warrant! 'monotone-convergence-rr 'well-known
  "A nondecreasing sequence bounded above converges to its supremum -- the
   order-completeness of RR (least-upper-bound property).  The eps-N witness:
   for eps>0 the sup minus eps is not an upper bound, so some f(N) exceeds it,
   and monotonicity keeps every later term within eps of the sup.  Standard;
   the named lemma comparison-test was waiting on.")

;;; -----------------------------------------------------------------------
;;; Partial-sum monotonicity.

;; Nonnegative terms => partial sums nondecreasing.
(support 'series-partial-sum-monotone-nonneg
  '(FORALL f (IMPLIES (IN f (FUN NN RR))
     (IMPLIES (FORALL n_ (IMPLIES (IN n_ NN) (<= 0 (f n_))))
       (FORALL k (IMPLIES (IN k NN)
         (<= (SERIES-PARTIAL-SUM f k) (SERIES-PARTIAL-SUM f (succ k)))))))))
(warrant! 'series-partial-sum-monotone-nonneg 'well-known
  "SERIES-PARTIAL-SUM f (succ k) = SERIES-PARTIAL-SUM f k + f(k) (the SUM-AG
   recurrence), and f(k) >= 0, so the partial sums are nondecreasing.")

;; Termwise <= => partial sums <= termwise.
(support 'series-partial-sum-le-termwise
  '(FORALL f (IMPLIES (IN f (FUN NN RR)) (FORALL g (IMPLIES (IN g (FUN NN RR))
     (IMPLIES (FORALL n_ (IMPLIES (IN n_ NN) (<= (f n_) (g n_))))
       (FORALL k (IMPLIES (IN k NN)
         (<= (SERIES-PARTIAL-SUM f k) (SERIES-PARTIAL-SUM g k))))))))))
(warrant! 'series-partial-sum-le-termwise 'well-known
  "Induction on k via the SUM-AG recurrence and rr-le-add: each added term
   f(k) <= g(k), so the running sums stay ordered.")

;;; -----------------------------------------------------------------------
;;; Series triangle inequality: |sum| <= sum of |.|.
(support 'series-partial-sum-abs-le
  '(FORALL f (IMPLIES (IN f (FUN NN RR))
     (FORALL k (IMPLIES (IN k NN)
       (<= (abs (SERIES-PARTIAL-SUM f k))
           (SERIES-PARTIAL-SUM (VNB-LAMBDA n_ (abs (f n_))) k)))))))
(warrant! 'series-partial-sum-abs-le 'well-known
  "|sum_{n<k} f(n)| <= sum_{n<k} |f(n)|: induction on k via the SUM-AG
   recurrence and rr-abs-triangle at each step.")

;;; -----------------------------------------------------------------------
;;; Cauchy criterion for real series: convergence => tails vanish.
(support 'series-cauchy-criterion
  '(FORALL f (IMPLIES (IN f (FUN NN RR))
     (IMPLIES (SERIES-CONVERGES f)
       (FORALL eps (IMPLIES (POS-RR eps)
         (FORSOME bnd (AND (IN bnd NN)
           (FORALL m (IMPLIES (IN m NN) (FORALL n_ (IMPLIES (IN n_ NN)
             (IMPLIES (AND (<= bnd m) (<= m n_))
               (<= (abs (- (SERIES-PARTIAL-SUM f n_)
                           (SERIES-PARTIAL-SUM f m))) eps))))))))))))))
(warrant! 'series-cauchy-criterion 'well-known
  "SERIES-CONVERGES f means the partial-sum sequence converges in RR-MS, hence
   is Cauchy: the block sum sum_{m<=i<n} f(i) = P(n)-P(m) is within eps once
   m,n are large.  The finite-block form of the tail going to 0.")
