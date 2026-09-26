;;; theorem-library/ord-segment-nn-succ.scm
;;;
;;; ord-segment-nn-succ:  NN-flavored ORD-SEGMENT successor characterization.
;;; For n in NN,  k in OS(succ n)  iff  k in OS(n)  or  k = n.
;;;
;;; PSS-promoted 2026-05-27 from proven-theorems.scm.  Original proof
;;; script archived in archive/proven-theorems-archive.scm.

(support 'ord-segment-nn-succ
  '(FORALL n (FORALL k (IMPLIES (IN n NN)
       (IFF (IN k (ORD-SEGMENT (succ n)))
            (OR (IN k (ORD-SEGMENT n)) (= k n)))))))

(warrant! 'ord-segment-nn-succ 'informal
  "Mechanically proven before the 2026-05-27 PSS promotion; script archived at
   archive/proven-theorems-archive.scm (prove-and-install! 'ord-segment-nn-succ).
   The NN-flavoured successor characterisation: ORD-SEGMENT(succ n) is
   ORD-SEGMENT(n) with n adjoined, which is the ordinal successor read at NN.
   Archive predates the E -> IDEN rename and the ==-sweep.")
