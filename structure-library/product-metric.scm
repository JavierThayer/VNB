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

;;; The product carrier: sequences x with x(n) in PTS(ms n) for every n.
(def-functoid 'PRODUCT-CARRIER '(ms)
  '(SEP x (FUN NN (BIG-UNION n NN (PTS (ms n))))
        (FORALL n (IMPLIES (IN n NN) (IN (x n) (PTS (ms n)))))))

;;; The n-th projection  x |-> x(n)  :  P -> PTS(ms n).
(def-functoid 'PRODUCT-PROJ '(ms n)
  '(VNB-LAMBDA x (PRODUCT-CARRIER ms) (x n)))

;;; The weighted product metric.  The distance is the sum of the series of
;;; weighted per-factor bounded distances, named by IOTA (its limit, which
;;; exists by product-weighted-summable, PROVEN in
;;; theorem-library/product-summable.scm).
(def-functoid 'PRODUCT-METRIC-W '(ms w)
  '(LIST (PRODUCT-CARRIER ms)
         (VNB-LAMBDA (LIST x y) (CARTESIAN (PRODUCT-CARRIER ms) (PRODUCT-CARRIER ms))
           (IOTA L (SERIES-CONVERGES-TO
                     (VNB-LAMBDA n NN (* (w n) ((DIST (BDD-METRIC (ms n))) (x n) (y n))))
                     L)))))

;;; The canonical instance, weights 2^-(n+1)  (diameter <= SUM 2^-(n+1) = 1).
(def-functoid 'PRODUCT-METRIC '(ms)
  '(PRODUCT-METRIC-W ms (VNB-LAMBDA n NN (/ 1 (power 2 (+ n 1))))))

;;; ----- carrier readout -----
;;; `product-metric-carrier' was asserted here until 2026-08-22, with the
;;; warrant "read off the functoid carrier slot".  Reading it off IS the proof:
;;; unfold the functoid, project with `slot', reduce the nth, and close by
;;; quasi-reflexivity.  PROVEN, `modulo 0', in theorem-library/
;;; product-summable.scm, which is where the rest of the product plumbing lives.

;;; ----- the defining series converges, so the distance is well-defined -----
;;; `product-weighted-summable' was asserted here until 2026-08-22.  It is now
;;; PROVEN, in theorem-library/product-summable.scm, from bdd-metric-bounded and
;;; the comparison test -- the proof has to live after theorem-library/
;;; comparison-test-proof, which is far below this file in load order.  Read the
;;; statement there; the argument is the one this warrant used to describe.

;;; ----- the product is a bounded metric space -----

;;; ----- projections are continuous (lower bound on the topology) -----
;;; RETIRED 2026-09-16 (proven): product-is-metric-space -- theorem-library/product-is-metric-space.scm

;;; product-projection-continuous RETIRED 2026-09-18 (rake batch 5): proven modulo 0 in theorem-library/rake-metric-constructions.scm

;;; ----- THE product topology: convergence is exactly coordinatewise -----
;;; `product-convergence-coordinatewise' was asserted here until 2026-08-23.  It
;;; is now PROVEN, in theorem-library/product-convergence.scm, and the proof has
;;; to live far below this file: it needs `dominated-null-series'
;;; (dominated-convergence.scm), `series-term-le-sum' (mono-le-limit.scm) and
;;; `converges-iff-dist-null' (converges-dist-null.scm), none of which exists at
;;; this point in the load.  Read the statement there; it is verbatim the one
;;; this support carried.  The retired warrant described the backward half as
;;; "choose N with the weight tail SUM_{n>=N} w(n) < eps/2, then make the first
;;; N coordinates within eps/2" -- that argument is not run here, because
;;; `dominated-null-series' IS it, once and for any dominated family.

;;; ----- infinitely many topologically equivalent metrics -----
;;; `product-weights-equivalent' was asserted here until 2026-08-23.  It is now
;;; PROVEN, in theorem-library/product-weights.scm.  The retired warrant had the
;;; argument exactly right -- "the identity is bicontinuous, since both induce
;;; coordinatewise convergence" -- and could not be run here for two reasons,
;;; both since removed: `product-convergence-coordinatewise' was itself asserted,
;;; and the tree had no bridge from CONVERGENCE to CONTINUITY.  That bridge is
;;; `continuous-at-iff-sequential' (theorem-library/sequential-continuity.scm).
;;; Read the statement there; it is verbatim the one this support carried.

;;; ----- the canonical instance -----
;;; `product-metric-default-summable' was asserted here until 2026-08-22.  It is
;;; now PROVEN, `modulo {nn-add-succ, nn-zero-le, nn-le-succ-cases}'
;;; [trust: well-known], in theorem-library/dyadic-weights.scm -- which has to
;;; live below comparison-test-proof (the partial-sum recurrence) and
;;; monotone-convergence-proof, both far below this file in load order.  The
;;; retired warrant read "geometric, SUM = 1", and the geometric series is
;;; exactly what the proof does NOT use: `geometric-series-converges-to' is
;;; itself asserted, it sums r^n rather than 2^-(n+1), and bridging the two
;;; wants a scalar multiple of a convergent series that the tree does not have.
;;; The proof is the closed form SERIES-PARTIAL-SUM(w,k) = 1 - 2^-k, by
;;; induction on k, which delivers both hypotheses of monotone convergence at
;;; once.  Read the statement there.

;;; -----------------------------------------------------------------------
;;; Notation -- the ENGLISH of these predicates, declared beside their
;;; definitions and read by wff->english / the proof reader (operators.scm).
;;; A def-predicate's reading cannot be derived the way a structure's noun can
;;; (noun vs adjective: IS-COMPLETE wants "s is complete", not "s is a complete"),
;;; so it is written here, once, next to what it means.
(notation! 'IS-MS-SEQUENCE 'kind 'predicate 'arity 1
           'english "$1 is a sequence of metric spaces")
(notation! 'SUMMABLE-WEIGHT 'kind 'predicate 'arity 1
           'english "$1 is a summable sequence of positive weights")
