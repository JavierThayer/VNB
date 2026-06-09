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
