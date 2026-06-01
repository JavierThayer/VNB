;;; theorem-library/succ-nn-ord.scm
;;;
;;; succ-nn-ord:  for n in NN, the NN-flavored succ equals the
;;; ORD-flavored succ_ORD.  Bridges the two notations so macetes can fire
;;; on either side.
;;;
;;; PSS-promoted 2026-05-27 from proven-theorems.scm.  Original proof
;;; script archived in archive/proven-theorems-archive.scm.

(support 'succ-nn-ord
  '(FORALL n (IMPLIES (IN n NN) (= (succ n) (succ_ORD n)))))
