;;; RETIRED 2026-09-17 (proven): abelian-group-assoc, abelian-group-right-id,
;;; abelian-group-inverse-unique -- theorem-library/rake-algebra2.scm (which also rebuilds the
;;; three MODULE-VECTOR-AG companions that proofs cite by name).
;;; abelian-group.scm -- ABELIAN-GROUP structure
;;;
;;; Carrier CARR, operation OPR, identity IDEN, inverse INV.
;;; Same shape (and accessor indices) as GROUP: CARR -> 1, OPR -> 2, IDEN -> 3, INV -> 4.
;;; An abelian group is a group whose OPR is commutative.
;;;
;;; Pattern follows COMM-MONOID in monoid.scm: declare the structure with the
;;; same shape as the parent, then add a single subtype/bridge axiom plus the
;;; new constraint.  Associativity, identity, and inverse laws are imported
;;; via the bridge (use IS-GROUP at the call site).
;;;
;;; Dependencies: group.scm (GROUP, IS-GROUP).

(declare-structure ABELIAN-GROUP
  (carriers CARR)
  (op OPR (CARTESIAN CARR CARR) CARR)
  (constant IDEN CARR)
  (op INV CARR CARR)
  (property is-associative OPR CARR)
  (property is-identity OPR IDEN CARR)
  (property has-inverses OPR IDEN INV CARR)
  (property is-commutative OPR CARR))

;;; Every abelian group is a group (same shape, so this is a direct subtype).
;;; PROVEN modulo 0 via mac-h in structure-library/subtype-laws.scm (loaded
;;; after the interactive tactics); no longer asserted here.

;;; Commutativity of OPR: the is-commutative property projected out of
;;; IS-ABELIAN-GROUP.  PROVEN modulo 0 in structure-library/subtype-laws.scm
;;; (the metric-sym pattern); no longer asserted here.

;;; Idempotent => identity: in a group a*a = a forces a = E.  Asserted here, and
;;; never warranted, until 2026-08-10; with 14 dependent proofs it was the
;;; most-cited unjustified fact in the library.  Now PROVEN modulo 0 in
;;; theorem-library/cancellation.scm, from group-cancel-left plus the right
;;; identity (one commutation away in an abelian group).  It still specializes
;;; through every additive view-as -- crucially MODULE-VECTOR-AG (views.scm) --
;;; delivering the cancellation endgame  a +_V a = a => a = 0_V  on a module's
;;; vectors; because it is now proved AFTER views.scm loads, cancellation.scm
;;; re-runs the specializer for that view.

;;; Inverses are unique: a*b = e forces b = a^{-1}.  The sibling of
;;; idempotent-is-id, and it specializes through the same additive view-as
;;; machinery -- through MODULE-VECTOR-AG it reads  x + b = 0_V => b = -x,
;;; which is what module-act-neg-one ((-1).x = -x) needs to finish.
;;; A support, not an axiom: it is derived, and its bill should say so.

;;; a * e = a: the RIGHT identity.  group.scm has only group-left-id; in a
;;; commutative group the right identity is left-id + commutativity.  Surfaced
;;; because it specializes through MODULE-VECTOR-AG to (VADD md) v (VZERO md) = v
;;; -- the "+ 0 drops" step every coefficient-combination proof ends on.

;;; Associativity, surfaced for direct use (group-assoc is on IS-GROUP, which the
;;; ABELIAN-GROUP view-specializer does not carry across).  Specializes through
;;; MODULE-VECTOR-AG to VADD-associativity -- the "regroup a + b + c" step the
;;; spans-submodule-fg remainder algebra needs.

;;; Notation -- read by wff->english / the proof reader (operators.scm).
(notation! 'IS-ABELIAN-GROUP        'noun "abelian group" 'article "an")
