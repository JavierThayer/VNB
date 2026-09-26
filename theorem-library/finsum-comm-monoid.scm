;;; RETIRED 2026-09-17 (proven, modulo 0): finsum-comm-monoid-permutation-invariance,
;;; finsum-comm-monoid-well-defined -- theorem-library/rake-finsum-welldef.scm
;;; RETIRED 2026-09-17 (proven): finsum-comm-monoid-type -- theorem-library/rake-finsum-typing.scm
;;; theorem-library/finsum-comm-monoid.scm
;;;
;;; Finite sums over a COMMUTATIVE MONOID.
;;;
;;; SUM-AG / FINSUM (sequences.scm, finsum.scm) are DEFINED using only the
;;; monoid fragment of their structure argument -- `(OPR m)' folds and
;;; `(IDEN m)' seeds the empty sum.  Inverses (INV) and commutativity are never
;;; touched by the DEFINITION.  So FINSUM(m, f, S) already COMPUTES for any
;;; commutative monoid m; what was missing were the supporting THEOREMS,
;;; which the abelian-group layer states under IS-ABELIAN-GROUP.  This file
;;; restates the three that downstream summation needs -- closure,
;;; permutation invariance, enumeration-independence -- under IS-COMM-MONOID.
;;;
;;; This is exactly what the unordered RR-POS-STAR sum needs: RR-POS-STAR-ADD-MONOID
;;; (extended-reals-pos.scm) is a commutative monoid with NO inverses, so the
;;; abelian-group versions do not apply to it, but these do.
;;;
;;; All three carry WARRANTS (see *warrant-kinds*, macetes.scm): each is a
;;; routine generalization of a result the abelian-group layer already holds,
;;; obtained by deleting the inverse-using steps -- which, as noted below,
;;; the proofs never used.
;;;
;;; Dependencies: monoid.scm (COMM-MONOID, IS-COMM-MONOID, accessors A/OPR/E),
;;; finsum.scm (FINSUM, ENUM-FAM), sequences.scm (SUM-AG), cardinality
;;; (CARD/NN), bijection (BIJECTION), ordinals (ORD-SEGMENT).

;;; -----------------------------------------------------------------------
;;; Closure: FINSUM stays in the carrier.
;;;
;;; The abelian-group version is finsum-type.  The fold SUM-AG(m,_,n) starts
;;; at (IDEN m) -- in the carrier by the identity law -- and at each step applies
;;; (OPR m), which closes on the carrier by the monoid's binary-operation
;;; typing.  Neither fact uses inverses or commutativity, so finsum-type's
;;; induction goes through verbatim over a bare monoid.



;;; -----------------------------------------------------------------------
;;; Permutation invariance: reordering the summands does not change the sum.
;;;
;;; The abelian-group version is sum-ag-permutation-invariance.  Its proof
;;; (archived) is an NN induction whose step splices one summand out of the
;;; sum and reorders the rest -- using ONLY associativity and commutativity
;;; of (OPR m).  Inverses never appear (a sum is built up, never cancelled).
;;; Commutativity is exactly what IS-COMM-MONOID adds over IS-MONOID, so the
;;; identical argument is available here.



;;; -----------------------------------------------------------------------
;;; Enumeration-independence: FINSUM does not depend on the chosen listing.
;;;
;;; The abelian-group version is finsum-well-defined; it is derived purely
;;; from permutation invariance above (any two enumerations of S differ by a
;;; bijection of ORD-SEGMENT(|S|)).  That derivation, too, uses no inverses,
;;; so it holds for a commutative monoid given finsum-comm-monoid-permutation-
;;; invariance.


