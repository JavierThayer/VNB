;;; cc-magnitude-zero.scm -- lemmas MOVED 2026-11-10 (integration of the 11-09/10 waves) out of theorem-library/cc-series.scm
;;; into library analysis, for the library gate: cited by five analysis files; CC arithmetic.
;;; The proofs are the originals, verbatim; the helper defines are a copy of the source's.
;;;   cc-magnitude-zero

;;; ---- the moved proofs ----
(sp (make-wff '(= (magnitude 0) 0)))
(fact 'cc-zero-in)
(fact 'cc-magnitude-zero-iff 0)
(have! '(= 0 0) (lambda () (rfl)))
(prop)
(qed 'cc-magnitude-zero)
(topic! 'cc-magnitude-zero 'analysis)
(alias! 'cc-magnitude-zero "the magnitude of 0 is 0")

