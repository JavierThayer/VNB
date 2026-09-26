;;; theorem-library/ord-segment-self.scm
;;;
;;; ord-segment-self:  for n in NN, n is not in ORD-SEGMENT(n).
;;; Anti-reflexive property of OS-membership.
;;;
;;; PSS-promoted 2026-05-27 from proven-theorems.scm.  Original proof
;;; script archived in archive/proven-theorems-archive.scm.

(support 'ord-segment-self
  '(FORALL n (IMPLIES (IN n NN) (NOT (IN n (ORD-SEGMENT n))))))

(warrant! 'ord-segment-self 'informal
  "Mechanically proven before the 2026-05-27 PSS promotion; script archived at
   archive/proven-theorems-archive.scm (prove-and-install! 'ord-segment-self).
   Anti-reflexivity: n in ORD-SEGMENT(n) would make the ordinal n a member of
   itself, against foundation.  Archive predates the E -> IDEN rename and the
   ==-sweep.")
