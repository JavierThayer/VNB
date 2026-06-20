;;; product-metric.scm -- the countable product of metric spaces, as a metric
;;; space carrying the PRODUCT TOPOLOGY.  Library phase: functoids for the
;;; construction, warranted supports for the metric/topology facts.
;;;
;;; Given a sequence of metric spaces  ms : NN -> {metric spaces}  (each
;;; (ms n) = (X_n, d_n) a metric space) and a summable sequence of positive
;;; weights  w : NN -> RR  (w(n) > 0, SUM w(n) < oo), put
;;;
;;;     PRODUCT-METRIC-W(ms, w) = (P,  D_w),
;;;     P = { x in PROD_n X_n }  (sequences with x(n) in X_n),
;;;     D_w(x, y) = SUM_{n} w(n) * rho_n(x(n), y(n)),
;;;       rho_n = d_n/(1+d_n)  the per-factor BOUNDED metric (bounded-metric.scm).
;;;
;;; Each term is < w(n), so the series is dominated by SUM w(n) < oo and
;;; converges (comparison with the summable weights); D_w is finite.  D_w is a
;;; metric: nonnegativity/symmetry/zero-law termwise, triangle inequality by
;;; summing the per-factor (bounded) triangle inequalities.  Crucially, the
;;; TOPOLOGY it induces is the product topology -- a sequence converges in
;;; PRODUCT-METRIC-W iff it converges in every coordinate -- and this does NOT
;;; depend on the weights w or the choice of bounded metric: any summable
;;; positive w gives a topologically equivalent metric.  So the countable
;;; product is canonically a topological (metrizable) space, with INFINITELY
;;; many equivalent metrics realising it.
;;;
;;; The canonical instance uses w(n) = 2^-(n+1):
;;;     PRODUCT-METRIC(ms) = PRODUCT-METRIC-W(ms, n |-> 2^-(n+1)),  diameter <= 1.
;;;
;;; Loads after bounded-metric (BDD-METRIC) and power-series (SERIES-CONVERGES).

;;; A sequence of metric spaces: (ms n) is a metric space for every n in NN.
(def-predicate 'IS-MS-SEQUENCE '(ms)
  '(FORALL n (IMPLIES (IN n NN) (IS-METRIC-SPACE (ms n)))))

;;; A summable weight sequence: positive reals with a convergent series.
(def-predicate 'SUMMABLE-WEIGHT '(w)
  '(AND (IN w (FUN NN RR))
   (AND (FORALL n (IMPLIES (IN n NN) (< 0 (w n))))
        (SERIES-CONVERGES w))))

;;; The product carrier: sequences x with x(n) in X(ms n) for every n.
(def-functoid 'PRODUCT-CARRIER '(ms)
  '(SEP x (FUN NN (BIG-UNION n NN (X (ms n))))
        (FORALL n (IMPLIES (IN n NN) (IN (x n) (X (ms n)))))))

;;; The n-th projection  x |-> x(n)  :  P -> X(ms n).
(def-functoid 'PRODUCT-PROJ '(ms n)
  '(VNB-LAMBDA x (x n)))

;;; The weighted product metric.  The distance is the sum of the series of
;;; weighted per-factor bounded distances, named by IOTA (its limit, which
;;; exists by product-weighted-summable below).
(def-functoid 'PRODUCT-METRIC-W '(ms w)
  '(LIST (PRODUCT-CARRIER ms)
         (VNB-LAMBDA (LIST x y)
           (IOTA L (SERIES-CONVERGES-TO
                     (VNB-LAMBDA n (* (w n) ((D (BDD-METRIC (ms n))) (x n) (y n))))
                     L)))))

;;; The canonical instance, weights 2^-(n+1)  (diameter <= SUM 2^-(n+1) = 1).
(def-functoid 'PRODUCT-METRIC '(ms)
  '(PRODUCT-METRIC-W ms (VNB-LAMBDA n (/ 1 (power 2 (+ n 1))))))

;;; ----- carrier readout -----
(support 'product-metric-carrier
  '(FORALL ms (FORALL w (== (X (PRODUCT-METRIC-W ms w)) (PRODUCT-CARRIER ms)))))
(warrant! 'product-metric-carrier 'well-known
  "X(PRODUCT-METRIC-W(ms,w)) = PRODUCT-CARRIER(ms), the set of sequences x with
   x(n) in X(ms n) for all n.  Read off the functoid carrier slot.")

;;; ----- the defining series converges, so the distance is well-defined -----
(support 'product-weighted-summable
  '(FORALL ms (IMPLIES (IS-MS-SEQUENCE ms)
     (FORALL w (IMPLIES (SUMMABLE-WEIGHT w)
       (FORALL x (IMPLIES (IN x (PRODUCT-CARRIER ms))
         (FORALL y (IMPLIES (IN y (PRODUCT-CARRIER ms))
           (SERIES-CONVERGES
             (VNB-LAMBDA n (* (w n) ((D (BDD-METRIC (ms n))) (x n) (y n))))))))))))))
(warrant! 'product-weighted-summable 'well-known
  "The series defining D_w converges: 0 <= w(n)*rho_n < w(n) since the bounded
   metric rho_n < 1 (bdd-metric-bounded), so termwise it is dominated by the
   summable weight series SUM w(n); comparison test gives convergence.  Hence
   the IOTA limit in PRODUCT-METRIC-W is well-defined.")

;;; ----- the product is a bounded metric space -----
(support 'product-is-metric-space
  '(FORALL ms (IMPLIES (IS-MS-SEQUENCE ms)
     (FORALL w (IMPLIES (SUMMABLE-WEIGHT w)
       (IS-METRIC-SPACE (PRODUCT-METRIC-W ms w)))))))
(warrant! 'product-is-metric-space 'well-known
  "PRODUCT-METRIC-W(ms,w) is a metric space.  Nonnegativity, symmetry and the
   zero law are termwise (D_w(x,y)=0 iff every weighted term is 0 iff rho_n=0
   iff x(n)=y(n) for all n iff x=y, as w(n)>0).  The triangle inequality is the
   sum over n of the per-factor bounded triangle inequalities (each rho_n is a
   metric, bdd-metric-is-metric-space), the sums converging by
   product-weighted-summable.")

;;; ----- projections are continuous (lower bound on the topology) -----
(support 'product-projection-continuous
  '(FORALL ms (IMPLIES (IS-MS-SEQUENCE ms)
     (FORALL w (IMPLIES (SUMMABLE-WEIGHT w)
       (FORALL n (IMPLIES (IN n NN)
         (IS-CONTINUOUS (PRODUCT-METRIC-W ms w) (ms n) (PRODUCT-PROJ ms n)))))))))
(warrant! 'product-projection-continuous 'well-known
  "Each projection pi_n(x)=x(n) is continuous P -> X(ms n): w(n)*rho_n(x(n),y(n))
   <= D_w(x,y), and rho_n is topologically equivalent to d_n, so small product
   distance forces small d_n-distance in coordinate n.")

;;; ----- THE product topology: convergence is exactly coordinatewise -----
(support 'product-convergence-coordinatewise
  '(FORALL ms (IMPLIES (IS-MS-SEQUENCE ms)
     (FORALL w (IMPLIES (SUMMABLE-WEIGHT w)
       (FORALL seq (IMPLIES (IN seq (FUN NN (PRODUCT-CARRIER ms)))
         (FORALL L (IMPLIES (IN L (PRODUCT-CARRIER ms))
           (IFF (CONVERGES-TO (PRODUCT-METRIC-W ms w) seq L)
                (FORALL n (IMPLIES (IN n NN)
                  (CONVERGES-TO (ms n)
                    (VNB-LAMBDA k ((seq k) n)) (L n))))))))))))))
(warrant! 'product-convergence-coordinatewise 'well-known
  "A sequence converges in PRODUCT-METRIC-W iff it converges in every
   coordinate -- the defining property of the PRODUCT TOPOLOGY.  Forward:
   projections are continuous (product-projection-continuous).  Backward: given
   eps, choose N with the weight tail SUM_{n>=N} w(n) < eps/2 (w summable), then
   make the first N coordinates within eps/2 of L (finite intersection of
   coordinate conditions).  Independent of which summable w is used.")

;;; ----- infinitely many topologically equivalent metrics -----
(support 'product-weights-equivalent
  '(FORALL ms (IMPLIES (IS-MS-SEQUENCE ms)
     (FORALL w (IMPLIES (SUMMABLE-WEIGHT w)
       (FORALL w2 (IMPLIES (SUMMABLE-WEIGHT w2)
         (AND (IS-CONTINUOUS (PRODUCT-METRIC-W ms w) (PRODUCT-METRIC-W ms w2)
                             (VNB-LAMBDA x x))
              (IS-CONTINUOUS (PRODUCT-METRIC-W ms w2) (PRODUCT-METRIC-W ms w)
                             (VNB-LAMBDA x x))))))))))
(warrant! 'product-weights-equivalent 'well-known
  "Any two summable positive weight sequences give TOPOLOGICALLY EQUIVALENT
   product metrics: the identity between PRODUCT-METRIC-W(ms,w) and
   PRODUCT-METRIC-W(ms,w2) is bicontinuous, since both induce coordinatewise
   convergence (product-convergence-coordinatewise).  Hence the countable
   product carries one canonical topology realised by INFINITELY many distinct
   but equivalent metrics (vary w, or the bounded function rho).")

;;; ----- the canonical instance -----
(support 'product-metric-default-summable
  '(SUMMABLE-WEIGHT (VNB-LAMBDA n (/ 1 (power 2 (+ n 1))))))
(warrant! 'product-metric-default-summable 'well-known
  "The default weights w(n)=2^-(n+1) are a summable positive sequence
   (geometric, SUM = 1), so PRODUCT-METRIC(ms)=PRODUCT-METRIC-W(ms,2^-(n+1)) is
   a bounded metric (diameter <= 1) realising the product topology.")
