;;; rr-nonneg-below-all-zero.scm -- lemmas MOVED 2026-11-10 (integration of the 11-09/10 waves) out of theorem-library/mb35-souslin.scm
;;; into library analysis, for the library gate: cited by three CCR ch.3 files; RR order.
;;; The proofs are the originals, verbatim; the helper defines are a copy of the source's.
;;;   rr-nonneg-below-all-zero

;;; ---- the moved proofs ----
(sp (make-wff '(FORALL x (IMPLIES (IN x RR) (IMPLIES (<= 0 x) (IMPLIES (FORALL eps (IMPLIES (POS-RR eps) (<= x eps))) (= x 0)))))))
(dk-peel!)
(use-cases (dk-cite! 'rr-lt-trichotomy 0 'x)
  (lambda ()
    (let ((h (list '* 1/2 'x)))
      (dk-type! h 'RR)
      (dk-have! (list '< 0 h) (lambda () (dk-ineq! '(< 0 x))))
      (dk-cite! 'rr-pos-rr-of-lt h)
      (dk-apply! '(FORALL eps (IMPLIES (POS-RR eps) (<= x eps))) h)
      (dk-ineq! (list '<= 'x h) '(< 0 x))))
  (lambda () (dk-ineq! '(= 0 x)))
  (lambda () (dk-ineq! '(< x 0) '(<= 0 x))))
(qed 'rr-nonneg-below-all-zero)
(topic! 'rr-nonneg-below-all-zero 'analysis)

