;;; theorem-library/ord-segment-self.scm
;;;
;;; ord-segment-self:  for n in NN, n is not in ORD-SEGMENT(n).
;;; Anti-reflexive property of OS-membership.
;;;
;;; PSS-promoted 2026-05-27 from proven-theorems.scm.  Original proof
;;; script archived in archive/proven-theorems-archive.scm.

(support 'ord-segment-self
  '(FORALL n (IMPLIES (IN n NN) (NOT (IN n (ORD-SEGMENT n))))))
