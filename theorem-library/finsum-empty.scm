;;; theorem-library/finsum-empty.scm
;;;
;;; finsum-empty:  FINSUM over the empty set is the abelian-group
;;; identity element.  Base case for finsum recursion / induction.
;;;
;;; PSS-promoted 2026-05-27 from proven-theorems.scm.  Original proof
;;; script archived in archive/proven-theorems-archive.scm.

(support 'finsum-empty
  '(FORALL ag (FORALL f (== (FINSUM ag f EMPTY-SET) (ID ag)))))
