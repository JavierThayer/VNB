;;; rr-mul-le-cancel.scm -- lemmas MOVED 2026-10-27 (integration of the 10-26/27 wave) out of
;;; theorem-library/primitive-uniform-limit.scm, so that files of library core may cite them (the library gate).
;;; The proofs are the originals, verbatim; the helper defines are a copy of primitive-uniform-limit.scm's.  Loaded
;;; immediately before primitive-uniform-limit.scm.
;;;   rr-mul-le-cancel-pos

;;; ---- helper defines copied from primitive-uniform-limit.scm ----


;;; ---- the moved proofs ----
(sp (make-wff "forall([pula_ in rr, pulc_ in rr, pulm_ in rr], 0 < pulc_ implies
   pula_ * pulc_ <= pulm_ * pulc_ implies pula_ <= pulm_)"))
(dk-peel!)
(for-each (lambda (pr) (dk-have! (list 'AND (list 'IN (car pr) 'RR) (list 'IN (cadr pr) 'RR)))
                       (fact 'rr-mul-closed (car pr) (cadr pr)))
          '((pula_ pulc_) (pulm_ pulc_)))
(fact 'rr-sub-in-rr 'pulm_ 'pula_)
(dk-have! '(AND (IN pulc_ RR) (IN (- pulm_ pula_) RR)))
(fact 'rr-mul-closed 'pulc_ '(- pulm_ pula_))
(dk-have! '(= (* pulc_ (- pulm_ pula_)) (- (* pulm_ pulc_) (* pula_ pulc_))) (lambda () (crs)))
(dk-have! '(<= 0 (* pulc_ (- pulm_ pula_)))
  (lambda ()
    (dk-ineq! '(<= (* pula_ pulc_) (* pulm_ pulc_))
              '(= (* pulc_ (- pulm_ pula_)) (- (* pulm_ pulc_) (* pula_ pulc_)))
              '(IN (* pula_ pulc_) RR) '(IN (* pulm_ pulc_) RR)
              '(IN (* pulc_ (- pulm_ pula_)) RR))))
(fact 'rr-nonneg-cancel-pos 'pulc_ '(- pulm_ pula_))
(dk-ineq! '(<= 0 (- pulm_ pula_)) '(IN pula_ RR) '(IN pulm_ RR))
(qed 'rr-mul-le-cancel-pos)
(topic! 'rr-mul-le-cancel-pos 'inequalities)

