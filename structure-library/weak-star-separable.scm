;;; tb6s-vocab.scm -- THE SEPARABLE BANACH-ALAOGLU (topological-vector-space.pdf Remark 3.30): definitions only.
;;; Agent TB-6 (worker-08), 2026-10-27 (NEW DEFINITIONS, the user's to confirm).
;;; DESTINATION: structure-library/weak-star-separable.scm.  Library: analysis.
;;; Load window: after product-metric (PRODUCT-METRIC, IS-MS-SEQUENCE), metric-subspace (SUBSPACE-MS),
;;; tb6-vocab (DUAL-UNIT-BALL).
;;;
;;;   PULLBACK-MS(mt, ss, jj)   the set ss with the distance d(u, v) = DIST(mt)(jj(u), jj(v)): a metric space when
;;;                             jj : ss -> PTS(mt) is injective (pullback-is-metric-space).
;;;   DBI(m, xs)                the sequence of compact intervals [-||x_n||, ||x_n||] as metric subspaces of RR-MS.
;;;   DBJ(m, xs)                f |-> (f(x_n))_n, the dual unit ball into the product of those intervals.
;;;   DUAL-BALL-MS(m, xs)       the dual unit ball with d(f, g) = sum_n 2^-(n+1) rho(f(x_n), g(x_n)), rho = t/(1+t) of
;;;                             |f(x_n) - g(x_n)| -- the tree's PRODUCT-METRIC pulled back along DBJ.
;;; Binders pbu_, pbv_, dbn_, dbf_ are used by nothing else.

(def-functoid 'PULLBACK-MS '(mt ss jj)
  '(LIST ss (VNB-LAMBDA (LIST pbu_ pbv_) (CARTESIAN ss ss) ((DIST mt) (jj pbu_) (jj pbv_)))))
(def-functoid 'DBI '(m xs)
  '(VNB-LAMBDA dbn_ NN (SUBSPACE-MS RR-MS (CCINT (- ((VNRM m) (xs dbn_))) ((VNRM m) (xs dbn_))))))
(def-functoid 'DBJ '(m xs)
  '(VNB-LAMBDA dbf_ (DUAL-UNIT-BALL m) (VNB-LAMBDA dbn_ NN (dbf_ (xs dbn_)))))
(def-functoid 'DUAL-BALL-MS '(m xs)
  '(PULLBACK-MS (PRODUCT-METRIC (DBI m xs)) (DUAL-UNIT-BALL m) (DBJ m xs)))

(notation! 'PULLBACK-MS 'kind 'functoid 'arity 3
           'english "the set $2 with the distance of $1 pulled back along $3")
(notation! 'DBI 'kind 'functoid 'arity 2
           'english "the intervals [-||x_n||, ||x_n||] of the sequence $2 in $1")
(notation! 'DBJ 'kind 'functoid 'arity 2
           'english "the evaluation of the dual unit ball of $1 along the sequence $2")
(notation! 'DUAL-BALL-MS 'kind 'functoid 'arity 2
           'english "the dual unit ball of $1 with the metric of the dense sequence $2")
