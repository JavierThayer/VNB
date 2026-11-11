;;; cc-magnitude-sq.scm -- lemmas MOVED 2026-11-10 (integration of the 11-09/10 waves) out of theorem-library/cc-int-estimate.scm
;;; into library analysis, for the library gate: cited by cc-real-bound; CC arithmetic.
;;; The proofs are the originals, verbatim; the helper defines are a copy of the source's.
;;;   cc-magnitude-sq

;;; ---- the moved proofs ----
(sp (make-wff '(FORALL cqz_ (IMPLIES (IN cqz_ CC)
     (= (* (magnitude cqz_) (magnitude cqz_))
        (+ (* (real-part cqz_) (real-part cqz_))
           (* (imag-part cqz_) (imag-part cqz_))))))))
(dk-peel!)
(fact 'real-part-in-rr 'cqz_)
(fact 'imag-part-in-rr 'cqz_)
(fact 'rr-sq-nonneg '(real-part cqz_))
(fact 'rr-sq-nonneg '(imag-part cqz_))
(have! (list 'AND '(IN (real-part cqz_) RR) '(IN (real-part cqz_) RR)))
(fact 'rr-mul-closed '(real-part cqz_) '(real-part cqz_))
(have! (list 'AND '(IN (imag-part cqz_) RR) '(IN (imag-part cqz_) RR)))
(fact 'rr-mul-closed '(imag-part cqz_) '(imag-part cqz_))
(define cie-sq '(+ (* (real-part cqz_) (real-part cqz_))
                   (* (imag-part cqz_) (imag-part cqz_))))
(dk-have! (list '<= 0 cie-sq)
  (lambda ()
    (dk-ineq! '(<= 0 (* (real-part cqz_) (real-part cqz_)))
              '(<= 0 (* (imag-part cqz_) (imag-part cqz_)))
              '(IN (* (real-part cqz_) (real-part cqz_)) RR)
              '(IN (* (imag-part cqz_) (imag-part cqz_)) RR))))
(have! (list 'AND '(IN (* (real-part cqz_) (real-part cqz_)) RR)
                  '(IN (* (imag-part cqz_) (imag-part cqz_)) RR)))
(fact 'rr-add-closed '(* (real-part cqz_) (real-part cqz_))
                     '(* (imag-part cqz_) (imag-part cqz_)))
(mac 'magnitude-def)
;; `sqrt-sq' has a CONJUNCTIVE antecedent (a in rr and 0 <= a), which `fact'
;; will not split.
(have! (list 'AND (list 'IN cie-sq 'RR) (list '<= 0 cie-sq)))
(fact 'sqrt-sq cie-sq)
(ass)
(qed 'cc-magnitude-sq)
(topic! 'cc-magnitude-sq 'analysis)
(alias! 'cc-magnitude-sq "the square of the modulus is the sum of the squares of the coordinates")

