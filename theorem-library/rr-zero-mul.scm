;;; rr-zero-mul.scm -- lemmas MOVED 2026-10-27 (integration of the 10-26/27 wave) out of
;;; theorem-library/taylor-proof.scm, so that files of library core may cite them (the library gate).
;;; The proofs are the originals, verbatim; the helper defines are a copy of taylor-proof.scm's.  Loaded
;;; immediately before taylor-proof.scm.
;;;   rr-zero-mul

;;; ---- helper defines copied from taylor-proof.scm ----


;;; ---- the moved proofs ----
(sp (make-wff '(FORALL v (IMPLIES (IN v RR) (= (* 0 v) 0)))))
(di) (crs)
(qed 'rr-zero-mul)
(topic! 'rr-zero-mul 'analysis)

