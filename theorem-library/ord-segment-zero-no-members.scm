;;; theorem-library/ord-segment-zero-no-members.scm
;;;
;;; ord-segment-zero-no-members:  ORD-SEGMENT(0) is empty.
;;; Base case for many NN inductions.
;;;
;;; PSS-promoted 2026-05-27 from proven-theorems.scm.  Original proof
;;; script archived in archive/proven-theorems-archive.scm.

(support 'ord-segment-zero-no-members
  '(FORALL k (NOT (IN k (ORD-SEGMENT 0)))))

(warrant! 'ord-segment-zero-no-members 'informal
  "Mechanically proven before the 2026-05-27 PSS promotion; script archived at
   archive/proven-theorems-archive.scm (prove-and-install!
   'ord-segment-zero-no-members).  ORD-SEGMENT(0) is the set of ordinals below
   0, which is empty.  Base case for the NN inductions above.  Archive predates
   the E -> IDEN rename and the ==-sweep.")
