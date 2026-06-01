;;; theorem-library/ord-segment-zero-no-members.scm
;;;
;;; ord-segment-zero-no-members:  ORD-SEGMENT(0) is empty.
;;; Base case for many NN inductions.
;;;
;;; PSS-promoted 2026-05-27 from proven-theorems.scm.  Original proof
;;; script archived in archive/proven-theorems-archive.scm.

(support 'ord-segment-zero-no-members
  '(FORALL k (NOT (IN k (ORD-SEGMENT 0)))))
