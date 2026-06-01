;;; theorem-library/finsum-type.scm
;;;
;;; finsum-type:  FINSUM(ag, f, S) inhabits the carrier (A ag) whenever
;;; the inputs have the right types.  Type lemma.
;;;
;;; PSS-promoted 2026-05-27 from proven-theorems.scm.  Original proof
;;; script archived in archive/proven-theorems-archive.scm.

(support 'finsum-type
  '(FORALL ag (IMPLIES (IS-ABELIAN-GROUP ag)
     (FORALL S (IMPLIES (IN S SET) (IMPLIES (IN (CARD S) NN)
     (FORALL f (IMPLIES (IN f (FUN S (A ag)))
       (IN (FINSUM ag f S) (A ag))))))))))
