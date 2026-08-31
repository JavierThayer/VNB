;;; metric-space.scm -- METRIC-SPACE structure
;;;
;;; Carrier PTS, distance function DIST : PTS x PTS -> RR.
;;; Accessor indices: PTS -> 1, DIST -> 2.
;;; Real arithmetic uses built-in <= and +.

(declare-structure METRIC-SPACE
  (carriers PTS)
  (op DIST (CARTESIAN PTS PTS) RR)
  (property is-metric DIST PTS))

;;; The five metric laws -- non-negativity, the two identity-of-indiscernibles
;;; halves, SYMMETRY, and the triangle inequality -- are NOT separate axioms.
;;; They are constitutive of the definition of a metric and are already folded
;;; into IS-METRIC-SPACE via the (property is-metric DIST PTS) clause above:
;;; `is-metric' (operation-properties.scm) is the IFF that states all five.
;;; So metric-pos / metric-self-zero / metric-zero-eq / metric-sym /
;;; metric-triangle are PROVEN modulo 0 by projecting that property
;;; (structure-library/metric-laws.scm), not asserted here.  Registering them
;;; as standalone axioms was an oversight (they were redundant the whole time).

;;; The distance is real-valued -- the codomain typing of the metric op
;;; (DIST : PTS(s) x PTS(s) -> RR from the op-clause above).  Every eps-argument
;;; feeds d(s)(x,y) into the RR order axioms, which are gated on `... in RR',
;;; so this typing is needed pervasively.  Derivable from the op-clause via a
;;; cartesian-application of fun-apply-type; kept as a warranted PSS support
;;; rather than re-grinding the tuple typing in every metric proof.
;;; metric-dist-real is PROVEN (2026-08-31) in theorem-library/op-typing.scm, with the
;;; other six applied-form op typings: one driver over the IS-X unfold plus
;;; apply-tupling-2 and fun-apply-type-c -- the derivation the warrant here
;;; recited.

;;; Notation -- read by wff->english / the proof reader (operators.scm).
(notation! 'IS-METRIC-SPACE         'noun "metric space" 'article "a")
