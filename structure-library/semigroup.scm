;;; semigroup.scm -- SEMIGROUP structure
;;;
;;; Carrier A, binary operation MUL.
;;; Accessor indices: A -> 1, MUL -> 2.

(def-structure-from-clauses 'SEMIGROUP
  '((carriers A)
    (op MUL (CARTESIAN A A) A)
    (property is-associative MUL A)))

;;; forall s. IS-SEMIGROUP(s) => forall a,b,c in A(s). (a*b)*c = a*(b*c)
(theory-add-axiom! *current-theory* 'semigroup-assoc
  '(FORALL s
     (IMPLIES (IS-SEMIGROUP s)
       (FORALL a (IMPLIES (IN a (A s))
         (FORALL b (IMPLIES (IN b (A s))
           (FORALL c (IMPLIES (IN c (A s))
             (= ((MUL s) ((MUL s) a b) c)
                ((MUL s) a ((MUL s) b c))))))))))))
