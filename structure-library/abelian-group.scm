;;; abelian-group.scm -- ABELIAN-GROUP structure
;;;
;;; Carrier CARR, operation MUL, identity ID, inverse INV.
;;; Same shape (and accessor indices) as GROUP: CARR -> 1, MUL -> 2, ID -> 3, INV -> 4.
;;; An abelian group is a group whose MUL is commutative.
;;;
;;; Pattern follows COMM-MONOID in monoid.scm: declare the structure with the
;;; same shape as the parent, then add a single subtype/bridge axiom plus the
;;; new constraint.  Associativity, identity, and inverse laws are imported
;;; via the bridge (use IS-GROUP at the call site).
;;;
;;; Dependencies: group.scm (GROUP, IS-GROUP).

(def-structure-from-clauses 'ABELIAN-GROUP
  '((carriers CARR)
    (op MUL (CARTESIAN CARR CARR) CARR)
    (constant ID CARR)
    (op INV CARR CARR)
    (property is-associative MUL CARR)
    (property is-identity MUL ID CARR)
    (property has-inverses MUL ID INV CARR)
    (property is-commutative MUL CARR)))

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
       (FORALL a (IMPLIES (IN a (CARR s))
         (IMPLIES (= ((MUL s) a a) a) (= a (ID s))))))))
