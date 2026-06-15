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

;;; Commutativity of MUL: the is-commutative property projected out of
;;; IS-ABELIAN-GROUP.  PROVEN modulo 0 in structure-library/subtype-laws.scm
;;; (the metric-sym pattern); no longer asserted here.

;;; Idempotent => identity: in a group a*a = a forces a = E (from a*a=a,
;;; left-multiply by a^{-1}).  Standard; asserted in the library phase.  It
;;; specializes through every additive view-as -- crucially MODULE-VECTOR-AG
;;; (views.scm) -- delivering the cancellation endgame  a +_V a = a => a = 0_V
;;; on a module's vectors without re-deriving it from the raw property predicates.
(theory-add-axiom! *current-theory* 'abelian-group-idempotent-is-id
  '(FORALL s
     (IMPLIES (IS-ABELIAN-GROUP s)
       (FORALL a (IMPLIES (IN a (A s))
         (IMPLIES (= ((MUL s) a a) a) (= a (E s))))))))
