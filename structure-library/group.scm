;;; group.scm -- GROUP structure
;;;
;;; Carrier A, operation MUL, identity E, inverse INV.
;;; Accessor indices: A -> 1, MUL -> 2, E -> 3, INV -> 4.
;;; Three axioms (left-only) suffice: assoc + left-id + left-inv.

(def-structure-from-clauses 'GROUP
  '((carriers CARR)
    (op MUL (CARTESIAN CARR CARR) CARR)
    (constant ID CARR)
    (op INV CARR CARR)
    (property is-associative MUL CARR)
    (property is-identity MUL ID CARR)
    (property has-inverses MUL ID INV CARR)))

;;; forall s. IS-GROUP(s) => forall a,b,c in A(s). (a*b)*c = a*(b*c)
(theory-add-axiom! *current-theory* 'group-assoc
  '(FORALL s
     (IMPLIES (IS-GROUP s)
       (FORALL a (IMPLIES (IN a (CARR s))
         (FORALL b (IMPLIES (IN b (CARR s))
           (FORALL c (IMPLIES (IN c (CARR s))
             (= ((MUL s) ((MUL s) a b) c)
                ((MUL s) a ((MUL s) b c))))))))))))

;;; forall s. IS-GROUP(s) => forall a in A(s). E(s)*a = a
(theory-add-axiom! *current-theory* 'group-left-id
  '(FORALL s
     (IMPLIES (IS-GROUP s)
       (FORALL a (IMPLIES (IN a (CARR s))
         (= ((MUL s) (ID s) a) a))))))

;;; forall s. IS-GROUP(s) => forall a in A(s). INV(s)(a)*a = E(s)
(theory-add-axiom! *current-theory* 'group-left-inv
  '(FORALL s
     (IMPLIES (IS-GROUP s)
       (FORALL a (IMPLIES (IN a (CARR s))
         (= ((MUL s) ((INV s) a) a) (ID s)))))))

;;; E(s) in A(s) when IS-GROUP(s).
;;; DERIVED: follows from the auto-generated IS-GROUP IFF -- the `constant E A`
;;; clause contributes the conjunct (IN (E s) (A s)).  Installed for direct
;;; use, mirroring monoid-identity-in in monoid.scm; demote when proven.
(theory-add-axiom! *current-theory* 'group-identity-in
  '(FORALL s (IMPLIES (IS-GROUP s) (IN (ID s) (CARR s)))))
