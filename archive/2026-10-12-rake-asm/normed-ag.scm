;;; normed-ag.scm -- NORMED-AG structure (normed abelian group)
;;;
;;; An abelian group (A, OPR, E, INV) carrying a real-valued norm NRM.
;;; Slots 1-4 are EXACTLY the ABELIAN-GROUP shape (same accessor indices:
;;; A->1, MUL->2, E->3, INV->4), with the norm added at slot 5:
;;;
;;;     A   -> 1   carrier
;;;     OPR -> 2   group operation        (CARTESIAN A A) A
;;;     E   -> 3   identity               A
;;;     INV -> 4   inverse                A A
;;;     NRM -> 5   norm                   A RR
;;;
;;; Keeping slots 1-4 aligned with ABELIAN-GROUP is deliberate: the additive
;;; group of a normed AG is recovered by the view-as NORMED-AG-AS-ABELIAN-GROUP
;;; (views.scm), which forgets NRM.  That projection is what lets the AG
;;; summation machinery -- FINSUM, sum-ag-permutation-invariance -- apply to
;;; the underlying group of a normed AG, which is the point: to sum and
;;; reorder f : X -> CARR we sum in NORMED-AG-AS-ABELIAN-GROUP(nag).
;;;
;;; The norm itself is the is-group-norm property (operation-properties.scm):
;;; nonnegative, zero only at E, inverse-invariant, subadditive over OPR.
;;; No multiplicativity -- a group has one operation, not a ring's two.
;;;
;;; As with NORMED-FIELD vs RING, NORMED-AG is a 5-tuple while ABELIAN-GROUP
;;; is a 4-slot predicate (pins length 4); so we do NOT assert
;;; (IS-NORMED-AG s) => (IS-ABELIAN-GROUP s) on the same tuple -- that would
;;; force 5 = 4.  The ABELIAN-GROUP world is reached only through the
;;; view-as projection.
;;;
;;; Dependencies: abelian-group.scm (ABELIAN-GROUP), operation-properties.scm
;;; (is-group-norm), number-systems.scm (RR).

(declare-structure NORMED-AG
  (carriers CARR)
  (op OPR (CARTESIAN CARR CARR) CARR)
  (constant IDEN CARR)
  (op INV CARR CARR)
  (op NRM CARR RR)
  (property is-associative OPR CARR)
  (property is-identity   OPR IDEN CARR)
  (property has-inverses  OPR IDEN INV CARR)
  (property is-commutative OPR CARR)
  (property is-group-norm NRM OPR INV IDEN CARR))

;;; Convenience restatement: the norm is a real-valued function on the carrier.
;;; (Immediate from is-group-norm; stated as a named axiom so callers need not
;;; peel the property's iff.)
(add-axiom! *library* 'normed-ag-nrm-type
  '(FORALL s (IMPLIES (IS-NORMED-AG s)
     (IN (NRM s) (FUN (CARR s) RR)))))

;;; The norm is nonnegative on the carrier.
(add-axiom! *library* 'normed-ag-nrm-nonneg
  '(FORALL s (IMPLIES (IS-NORMED-AG s)
     (FORALL a (IMPLIES (IN a (CARR s))
       (<= 0 ((NRM s) a)))))))

;;; Definiteness: the norm vanishes exactly at the identity.
(add-axiom! *library* 'normed-ag-nrm-definite
  '(FORALL s (IMPLIES (IS-NORMED-AG s)
     (FORALL a (IMPLIES (IN a (CARR s))
       (IFF (= ((NRM s) a) 0) (= a (IDEN s))))))))

;;; Subadditivity (the triangle inequality for the norm).
(add-axiom! *library* 'normed-ag-nrm-subadditive
  '(FORALL s (IMPLIES (IS-NORMED-AG s)
     (FORALL a (IMPLIES (IN a (CARR s))
       (FORALL b (IMPLIES (IN b (CARR s))
         (<= ((NRM s) ((OPR s) a b))
             (+ ((NRM s) a) ((NRM s) b))))))))))
