;;; theorem-library/finsum-well-defined.scm
;;;
;;; finsum-well-defined:  FINSUM does not depend on the choice of
;;; enumeration of S.  For any bijection enm : OS(|S|) -> S,
;;;   FINSUM(ag, f, S) = SUM-AG(ag, ENUM-FAM(ag, f, enm, |S|), |S|).
;;;
;;; This is the key result that promotes FINSUM from an
;;; enumeration-dependent definition to a genuine set-indexed sum.
;;; The original derivation went via sum-ag-permutation-invariance (PSS,
;;; see theorem-library/sum-ag-permutation-invariance.scm).
;;;
;;; PSS-promoted 2026-05-27 from proven-theorems.scm.  Original proof
;;; script archived in archive/proven-theorems-archive.scm.

(support 'finsum-well-defined
  '(FORALL S
     (IMPLIES (IN S SET)
     (IMPLIES (IN (CARD S) NN)
     (FORALL ag
     (IMPLIES (IS-ABELIAN-GROUP ag)
     (FORALL f
     (IMPLIES (IN f (FUN S (CARR ag)))
     (FORALL enm
     (IMPLIES (IN enm (BIJECTION (ORD-SEGMENT (CARD S)) S))
       (= (FINSUM ag f S)
          (SUM-AG ag (ENUM-FAM ag f enm (CARD S)) (CARD S)))))))))))))
