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
