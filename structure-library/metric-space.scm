;;; metric-space.scm -- METRIC-SPACE structure
;;;
;;; Carrier X, distance function D : X x X -> RR.
;;; Accessor indices: X -> 1, D -> 2.
;;; Real arithmetic uses built-in <= and +.

(def-structure-from-clauses 'METRIC-SPACE
  '((carriers X)
    (op D (CARTESIAN X X) RR)
    (property is-metric D X)))

;;; The five axioms below CHARACTERISE the primitive IS-METRIC-SPACE: they are
;;; the standard textbook definition of a metric (non-negativity, identity of
;;; indiscernibles in two halves, symmetry, triangle inequality).  Asserted,
;;; not proven -- so each carries a `well-known' warrant for the proof-debt
;;; ledger (a metric proof should rest on a NAMED, justified base, not on a
;;; bare trust-none leaf).

;;; forall s. IS-METRIC-SPACE(s) => forall x,y in X(s). 0 <= D(s)(x,y)
(theory-add-axiom! *current-theory* 'metric-pos
  '(FORALL s
     (IMPLIES (IS-METRIC-SPACE s)
       (FORALL x (IMPLIES (IN x (X s))
         (FORALL y (IMPLIES (IN y (X s))
           (<= 0 ((D s) x y)))))))))
(warrant! 'metric-pos 'well-known
  "Non-negativity of the distance: one of the defining axioms of a metric space.")

;;; forall s. IS-METRIC-SPACE(s) => forall x in X(s). D(s)(x,x) = 0
(theory-add-axiom! *current-theory* 'metric-self-zero
  '(FORALL s
     (IMPLIES (IS-METRIC-SPACE s)
       (FORALL x (IMPLIES (IN x (X s))
         (= ((D s) x x) 0))))))
(warrant! 'metric-self-zero 'well-known
  "A point is at zero distance from itself: half of identity-of-indiscernibles, a defining axiom of a metric space.")

;;; forall s. IS-METRIC-SPACE(s) => forall x,y in X(s). D(s)(x,y) = 0 => x = y
(theory-add-axiom! *current-theory* 'metric-zero-eq
  '(FORALL s
     (IMPLIES (IS-METRIC-SPACE s)
       (FORALL x (IMPLIES (IN x (X s))
         (FORALL y (IMPLIES (IN y (X s))
           (IMPLIES (= ((D s) x y) 0) (= x y)))))))))
(warrant! 'metric-zero-eq 'well-known
  "Zero distance implies equality: the separating half of identity-of-indiscernibles, a defining axiom of a metric space.")

;;; forall s. IS-METRIC-SPACE(s) => forall x,y in X(s). D(s)(x,y) = D(s)(y,x)
(theory-add-axiom! *current-theory* 'metric-sym
  '(FORALL s
     (IMPLIES (IS-METRIC-SPACE s)
       (FORALL x (IMPLIES (IN x (X s))
         (FORALL y (IMPLIES (IN y (X s))
           (= ((D s) x y) ((D s) y x)))))))))
(warrant! 'metric-sym 'well-known
  "Symmetry of the distance: one of the defining axioms of a metric space.")

;;; forall s. IS-METRIC-SPACE(s) =>
;;;   forall x,y,z in X(s). D(s)(x,z) <= D(s)(x,y) + D(s)(y,z)
(theory-add-axiom! *current-theory* 'metric-triangle
  '(FORALL s
     (IMPLIES (IS-METRIC-SPACE s)
       (FORALL x (IMPLIES (IN x (X s))
         (FORALL y (IMPLIES (IN y (X s))
           (FORALL z (IMPLIES (IN z (X s))
             (<= ((D s) x z)
                 (+ ((D s) x y) ((D s) y z))))))))))))
(warrant! 'metric-triangle 'well-known
  "The triangle inequality: one of the defining axioms of a metric space.")
