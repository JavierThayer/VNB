;;; theorem-library/finsum-type.scm
;;;
;;; finsum-type:  FINSUM(ag, f, S) inhabits the carrier (CARR ag) whenever
;;; the inputs have the right types.  Type lemma.
;;;
;;; PSS-promoted 2026-05-27 from proven-theorems.scm.  Original proof
;;; script archived in archive/proven-theorems-archive.scm.

(support 'finsum-type
  '(FORALL ag (IMPLIES (IS-ABELIAN-GROUP ag)
     (FORALL S (IMPLIES (IN S SET) (IMPLIES (IN (CARD S) NN)
     (FORALL f (IMPLIES (IN f (FUN S (CARR ag)))
       (IN (FINSUM ag f S) (CARR ag))))))))))

(warrant! 'finsum-type 'informal
  "Mechanically proven before the 2026-05-27 PSS promotion; script archived at
   archive/proven-theorems-archive.scm (prove-and-install! 'finsum-type).
   FINSUM is a SUM-AG over an enumeration of S, and SUM-AG of a family into
   CARR(ag) stays in CARR(ag) by induction on the length.  Archive predates the
   E -> IDEN rename and the ==-sweep, so it records the argument only.")
