;;; group.scm -- GROUP structure
;;;
;;; Carrier A, operation MUL, identity E, inverse INV.
;;; Accessor indices: A -> 1, MUL -> 2, E -> 3, INV -> 4.
;;; Three axioms (left-only) suffice: assoc + left-id + left-inv.

(def-structure-from-clauses 'GROUP
  '((carriers A)
    (op MUL (CARTESIAN A A) A)
    (constant E A)
    (op INV A A)
    (property is-associative MUL A)
    (property is-identity MUL E A)
    (property has-inverses MUL E INV A)))

;;; forall s. IS-GROUP(s) => forall a,b,c in A(s). (a*b)*c = a*(b*c)
(theory-add-axiom! *current-theory* 'group-assoc
  '(FORALL s
     (IMPLIES (IS-GROUP s)
       (FORALL a (IMPLIES (IN a (A s))
         (FORALL b (IMPLIES (IN b (A s))
           (FORALL c (IMPLIES (IN c (A s))
             (= ((MUL s) ((MUL s) a b) c)
                ((MUL s) a ((MUL s) b c))))))))))))

;;; forall s. IS-GROUP(s) => forall a in A(s). E(s)*a = a
(theory-add-axiom! *current-theory* 'group-left-id
  '(FORALL s
     (IMPLIES (IS-GROUP s)
       (FORALL a (IMPLIES (IN a (A s))
         (= ((MUL s) (E s) a) a))))))

;;; forall s. IS-GROUP(s) => forall a in A(s). INV(s)(a)*a = E(s)
(theory-add-axiom! *current-theory* 'group-left-inv
  '(FORALL s
     (IMPLIES (IS-GROUP s)
       (FORALL a (IMPLIES (IN a (A s))
         (= ((MUL s) ((INV s) a) a) (E s)))))))

;;; E(s) in A(s) when IS-GROUP(s).
;;; DERIVED: follows from the auto-generated IS-GROUP IFF -- the `constant E A`
;;; clause contributes the conjunct (IN (E s) (A s)).  Installed for direct
;;; use, mirroring monoid-identity-in in monoid.scm; demote when proven.
(theory-add-axiom! *current-theory* 'group-identity-in
  '(FORALL s (IMPLIES (IS-GROUP s) (IN (E s) (A s)))))
