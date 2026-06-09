;;; metric-space.scm -- METRIC-SPACE structure
;;;
;;; Carrier X, distance function D : X x X -> RR.
;;; Accessor indices: X -> 1, D -> 2.
;;; Real arithmetic uses built-in <= and +.

(def-structure-from-clauses 'METRIC-SPACE
  '((carriers X)
    (op D (CARTESIAN X X) RR)
    (property is-metric D X)))

;;; The five metric laws -- non-negativity, the two identity-of-indiscernibles
;;; halves, SYMMETRY, and the triangle inequality -- are NOT separate axioms.
;;; They are constitutive of the definition of a metric and are already folded
;;; into IS-METRIC-SPACE via the (property is-metric D X) clause above:
;;; `is-metric' (operation-properties.scm) is the IFF that states all five.
;;; So metric-pos / metric-self-zero / metric-zero-eq / metric-sym /
;;; metric-triangle are PROVEN modulo 0 by projecting that property
;;; (structure-library/metric-laws.scm), not asserted here.  Registering them
;;; as standalone axioms was an oversight (they were redundant the whole time).

;;; The distance is real-valued -- the codomain typing of the metric op
;;; (D : X(s) x X(s) -> RR from the op-clause above).  Every eps-argument
;;; feeds d(s)(x,y) into the RR order axioms, which are gated on `... in RR',
;;; so this typing is needed pervasively.  Derivable from the op-clause via a
;;; cartesian-application of fun-apply-type; kept as a warranted PSS support
;;; rather than re-grinding the tuple typing in every metric proof.
(support 'metric-dist-real
  '(FORALL s (IMPLIES (IS-METRIC-SPACE s)
     (FORALL x (IMPLIES (IN x (X s))
       (FORALL y (IMPLIES (IN y (X s))
         (IN ((D s) x y) RR))))))))
(warrant! 'metric-dist-real 'well-known
  "The distance is real-valued: D(s) maps X(s) x X(s) into RR, so d(s)(x,y) in RR.  Codomain typing of the metric op (the op-clause in the METRIC-SPACE declaration).")
