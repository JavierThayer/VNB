;;; subset-rr-power.scm -- lemmas MOVED 2026-10-27 (integration of the 10-26/27 wave) out of
;;; theorem-library/lebesgue-interval-length.scm, so that files of library analysis may cite them (the library gate).
;;; The proofs are the originals, verbatim; the helper defines are a copy of lebesgue-interval-length.scm's.  Loaded
;;; immediately before lebesgue-interval-length.scm.
;;;   subset-rr-in-power-rr

;;; ---- helper defines copied from lebesgue-interval-length.scm ----


;;; ---- the moved proofs ----
(sp (make-wff (forall-guarded '(es) '((SUBSET es RR)) '(IN es (POWER RR)))))
(dk-peel!)
(fact 'rr-is-set)
(fact 'subclass-of-set-is-set 'es 'RR)
(dk-have! '(FORALL z_ (IMPLIES (IN z_ es) (IN z_ RR)))
  (lambda () (let ((zv (dk-di-var!))) (fact 'subset-mem-fwd 'es 'RR zv) (ass))))
(fact 'power-mem-intro 'RR 'es)
(ass)
(qed 'subset-rr-in-power-rr)
(topic! 'subset-rr-in-power-rr 'plumbing)

