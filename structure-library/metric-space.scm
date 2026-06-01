;;; metric-space.scm -- METRIC-SPACE structure
;;;
;;; Carrier X, distance function D : X x X -> RR.
;;; Accessor indices: X -> 1, D -> 2.
;;; Real arithmetic uses built-in <= and +.

(def-structure-from-clauses 'METRIC-SPACE
  '((carriers X)
    (op D (CARTESIAN X X) RR)
    (property is-metric D X)))

;;; forall s. IS-METRIC-SPACE(s) => forall x,y in X(s). 0 <= D(s)(x,y)
(theory-add-axiom! *current-theory* 'metric-pos
  '(FORALL s
     (IMPLIES (IS-METRIC-SPACE s)
       (FORALL x (IMPLIES (IN x (X s))
         (FORALL y (IMPLIES (IN y (X s))
           (<= 0 ((D s) x y)))))))))

;;; forall s. IS-METRIC-SPACE(s) => forall x in X(s). D(s)(x,x) = 0
(theory-add-axiom! *current-theory* 'metric-self-zero
  '(FORALL s
     (IMPLIES (IS-METRIC-SPACE s)
       (FORALL x (IMPLIES (IN x (X s))
         (= ((D s) x x) 0))))))

;;; forall s. IS-METRIC-SPACE(s) => forall x,y in X(s). D(s)(x,y) = 0 => x = y
(theory-add-axiom! *current-theory* 'metric-zero-eq
  '(FORALL s
     (IMPLIES (IS-METRIC-SPACE s)
       (FORALL x (IMPLIES (IN x (X s))
         (FORALL y (IMPLIES (IN y (X s))
           (IMPLIES (= ((D s) x y) 0) (= x y)))))))))

;;; forall s. IS-METRIC-SPACE(s) => forall x,y in X(s). D(s)(x,y) = D(s)(y,x)
(theory-add-axiom! *current-theory* 'metric-sym
  '(FORALL s
     (IMPLIES (IS-METRIC-SPACE s)
       (FORALL x (IMPLIES (IN x (X s))
         (FORALL y (IMPLIES (IN y (X s))
           (= ((D s) x y) ((D s) y x)))))))))

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
