;;; theorem-library/ord-segment-trans.scm
;;;
;;; ord-segment-trans:  transitivity of ORD-SEGMENT membership.
;;; For m in NN, if i in OS(k) and k in OS(m), then i in OS(m).
;;;
;;; PSS-promoted 2026-05-27 from proven-theorems.scm.  Original proof
;;; script archived in archive/proven-theorems-archive.scm.

(support 'ord-segment-trans
  '(FORALL m (IMPLIES (IN m NN)
     (FORALL k (FORALL i
       (IMPLIES (AND (IN i (ORD-SEGMENT k)) (IN k (ORD-SEGMENT m)))
                (IN i (ORD-SEGMENT m))))))))
