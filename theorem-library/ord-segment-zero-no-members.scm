;;; theorem-library/ord-segment-zero-no-members.scm
;;;
;;; ord-segment-zero-no-members:  ORD-SEGMENT(0) is empty.
;;; Base case for many NN inductions.
;;;
;;; IT IS NOW PROVEN, and the proof is in
;;; theorem-library/ord-segment-nn-subset-proof.scm, not here (it was also proven
;;; a second time in pigeonhole-segments.scm from 2026-08-05 until 2026-09-16): this file loads at a point where the tactic layer
;;; does not exist yet -- the whole "PSS-promoted foundational facts" block above
;;; it in load.scm is pure `support' declarations, and `interactive' loads eighty
;;; entries later.  So the support declaration that used to stand here is gone,
;;; and the file survives as the signpost.
;;;
;;; The argument, for the record: k in ORD-SEGMENT(0) gives ORD-LT k 0
;;; (ord-segment-membership, once 0 is typed in ORD via nn-subset-ord), which is
;;; ORD-LE k 0 together with k /= 0 (ord-lt-iff); ord-zero-least gives
;;; ORD-LE 0 k, and ord-le-antisymm then gives k = 0.  Contradiction.
;;;
;;; It had been a warranted support since the 2026-05-27 PSS promotion, with the
;;; original machine proof archived at archive/proven-theorems-archive.scm.
