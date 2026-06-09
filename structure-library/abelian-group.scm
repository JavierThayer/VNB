;;; abelian-group.scm -- ABELIAN-GROUP structure
;;;
;;; Carrier A, operation MUL, identity E, inverse INV.
;;; Same shape (and accessor indices) as GROUP: A -> 1, MUL -> 2, E -> 3, INV -> 4.
;;; An abelian group is a group whose MUL is commutative.
;;;
;;; Pattern follows COMM-MONOID in monoid.scm: declare the structure with the
;;; same shape as the parent, then add a single subtype/bridge axiom plus the
;;; new constraint.  Associativity, identity, and inverse laws are imported
;;; via the bridge (use IS-GROUP at the call site).
;;;
;;; Dependencies: group.scm (GROUP, IS-GROUP).

(def-structure-from-clauses 'ABELIAN-GROUP
  '((carriers A)
    (op MUL (CARTESIAN A A) A)
    (constant E A)
    (op INV A A)
    (property is-associative MUL A)
    (property is-identity MUL E A)
    (property has-inverses MUL E INV A)
    (property is-commutative MUL A)))

;;; Every abelian group is a group (same shape, so this is a direct subtype).
;;; PROVEN modulo 0 via mac-h in structure-library/subtype-laws.scm (loaded
;;; after the interactive tactics); no longer asserted here.

;;; Commutativity of MUL.
(theory-add-axiom! *current-theory* 'abelian-group-mul-comm
  '(FORALL s
     (IMPLIES (IS-ABELIAN-GROUP s)
       (FORALL a (IMPLIES (IN a (A s))
         (FORALL b (IMPLIES (IN b (A s))
           (= ((MUL s) a b) ((MUL s) b a)))))))))
