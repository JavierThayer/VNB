;;; theorem-library/ord-segment-nn-subset.scm
;;;
;;; ord-segment-nn-subset:  for m in NN, every member of ORD-SEGMENT(m)
;;; is itself a natural number.  Type-promotion lemma.
;;;
;;; PSS-promoted 2026-05-27 from proven-theorems.scm.  Original proof
;;; script archived in archive/proven-theorems-archive.scm.

(support 'ord-segment-nn-subset
  '(FORALL m (IMPLIES (IN m NN)
     (FORALL k (IMPLIES (IN k (ORD-SEGMENT m)) (IN k NN))))))

(warrant! 'ord-segment-nn-subset 'informal
  "Mechanically proven before the 2026-05-27 PSS promotion; script archived at
   archive/proven-theorems-archive.scm (prove-and-install! 'ord-segment-nn-subset).
   A member of ORD-SEGMENT(m) for m in NN is an ordinal below a natural, hence
   itself a natural, by NN-induction on m.  Archive predates the E -> IDEN
   rename and the ==-sweep, so it records the argument rather than running.")
