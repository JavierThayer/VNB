;;; theorem-library/finsum-empty.scm
;;;
;;; finsum-empty:  FINSUM over the empty set is the abelian-group
;;; identity element.  Base case for finsum recursion / induction.
;;;
;;; PSS-promoted 2026-05-27 from proven-theorems.scm.  Original proof
;;; script archived in archive/proven-theorems-archive.scm.

(support 'finsum-empty
  '(FORALL ag (FORALL f (== (FINSUM ag f EMPTY-SET) (IDEN ag)))))

(warrant! 'finsum-empty 'informal
  "Mechanically proven before the 2026-05-27 PSS promotion: mac FINSUM exposes
   SUM-AG over CARD(EMPTY-SET), card-empty rewrites that to 0, and sum-ag-zero
   collapses the empty sum to the identity.  Script archived at
   archive/proven-theorems-archive.scm (prove-and-install! 'finsum-empty).  The
   archive predates the E -> IDEN accessor rename and the ==-sweep, so it is a
   record of the argument rather than a runnable script -- which is why this is
   `informal' and not `proof'.")
