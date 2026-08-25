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

(support 'finsum-comm-monoid-type
  '(FORALL m (IMPLIES (IS-COMM-MONOID m)
     (FORALL S (IMPLIES (IN S SET) (IMPLIES (IN (CARD S) NN)
     (FORALL f (IMPLIES (IN f (FUN S (CARR m)))
       (IN (FINSUM m f S) (CARR m))))))))))

(warrant! 'finsum-comm-monoid-type 'informal
  "Same induction as finsum-type: SUM-AG seeds at (IDEN m) -- in the carrier by
   the identity law -- and folds with (OPR m), which closes on the carrier by
   the binary-operation typing.  Neither step uses inverses, so the
   abelian-group proof carries over to a bare commutative monoid unchanged.")

;;; -----------------------------------------------------------------------
;;; Permutation invariance: reordering the summands does not change the sum.
;;;
;;; The abelian-group version is sum-ag-permutation-invariance.  Its proof
;;; (archived) is an NN induction whose step splices one summand out of the
;;; sum and reorders the rest -- using ONLY associativity and commutativity
;;; of (OPR m).  Inverses never appear (a sum is built up, never cancelled).
;;; Commutativity is exactly what IS-COMM-MONOID adds over IS-MONOID, so the
;;; identical argument is available here.

(support 'finsum-comm-monoid-permutation-invariance
  '(FORALL n (IMPLIES (IN n NN)
     (FORALL m (IMPLIES (IS-COMM-MONOID m)
     (FORALL g (IMPLIES (IN g (FUN NN (CARR m)))
     (FORALL h (IMPLIES (IN h (FUN NN (CARR m)))
     (FORALL phi (IMPLIES (IN phi (BIJECTION (ORD-SEGMENT n) (ORD-SEGMENT n)))
       (IMPLIES (FORALL i (IMPLIES (IN i (ORD-SEGMENT n)) (= (h i) (g (phi i)))))
         (= (SUM-AG m g n) (SUM-AG m h n))))))))))))))

(warrant! 'finsum-comm-monoid-permutation-invariance 'well-known
  "Commutativity and associativity alone make a finite sum independent of the
   order of its summands -- the standard fact underlying unordered summation.
   Concretely, the archived proof of sum-ag-permutation-invariance is an
   induction whose only steps are splice-out and rearrange, built purely from
   the associative and commutative laws of (OPR m); it never forms an inverse.
   Commutativity is precisely what IS-COMM-MONOID supplies, so that proof
   transfers verbatim.  (Candidate to discharge into a formal `proof' by
   reinstating the archived script over a monoid.)")

;;; -----------------------------------------------------------------------
;;; Enumeration-independence: FINSUM does not depend on the chosen listing.
;;;
;;; The abelian-group version is finsum-well-defined; it is derived purely
;;; from permutation invariance above (any two enumerations of S differ by a
;;; bijection of ORD-SEGMENT(|S|)).  That derivation, too, uses no inverses,
;;; so it holds for a commutative monoid given finsum-comm-monoid-permutation-
;;; invariance.

(support 'finsum-comm-monoid-well-defined
  '(FORALL S
     (IMPLIES (IN S SET)
     (IMPLIES (IN (CARD S) NN)
     (FORALL m
     (IMPLIES (IS-COMM-MONOID m)
     (FORALL f
     (IMPLIES (IN f (FUN S (CARR m)))
     (FORALL enm
     (IMPLIES (IN enm (BIJECTION (ORD-SEGMENT (CARD S)) S))
       (= (FINSUM m f S)
          (SUM-AG m (ENUM-FAM m f enm (CARD S)) (CARD S)))))))))))))

(warrant! 'finsum-comm-monoid-well-defined 'informal
  "Identical to finsum-well-defined: any two enumerations of S differ by a
   bijection of ORD-SEGMENT(|S|), so finsum-comm-monoid-permutation-invariance
   equates their folds.  The derivation uses no inverses, hence holds over a
   commutative monoid.")
