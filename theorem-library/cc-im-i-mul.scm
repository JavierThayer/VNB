;;; cc-im-i-mul.scm -- lemmas MOVED 2026-11-10 (integration of the 11-09/10 waves) out of theorem-library/triangle-orientation.scm
;;; into library analysis, for the library gate: cited by cc-real-bound; CC arithmetic.
;;; The proofs are the originals, verbatim; the helper defines are a copy of the source's.
;;;   cc-im-i-mul

(dk-skip-links!)   ; as in the source file

;;; ---- the moved proofs ----
(sp (make-wff '(FORALL aoz_ (IMPLIES (IN aoz_ CC) (= (imag-part (* +i aoz_)) (real-part aoz_))))))
(dk-peel!)
(fact 'cc-i-in)
(dk-split-all! (list (dk-cite! 'rb3-re-im-i)))
(fact 'real-part-in-rr 'aoz_) (fact 'imag-part-in-rr 'aoz_)
(subst (dk-cite! 'cc-im-mul '+i 'aoz_))
(subst '(= (real-part +i) 0)) (subst '(= (imag-part +i) 1))
(crs)
(qed 'cc-im-i-mul)

