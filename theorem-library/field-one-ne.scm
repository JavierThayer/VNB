;;; field-one-ne.scm -- lemmas MOVED 2026-10-27 (integration of the 10-26/27 wave) out of
;;; theorem-library/la-det-adjoint.scm, so that files of library algebra may cite them (the library gate).
;;; The proofs are the originals, verbatim; the helper defines are a copy of la-det-adjoint.scm's.  Loaded
;;; immediately before la-det-adjoint.scm.
;;;   ladet-field-one-ne

;;; ---- helper defines copied from la-det-adjoint.scm ----
(define (ladet-done! name)
  (if (not (proof-done? *ps*))
      (begin
        (display "\n*** la-det-adjoint: ") (display name) (display " did NOT close.\n")
        (for-each (lambda (l)
                    (display ";;   leaf: ")
                    (display (expression->string (dk-goal-of l))) (newline))
                  (dk-open-leaves))))
  (qed name))

;;; ---- the moved proofs ----
(sp (make-wff '(FORALL R (IMPLIES (IS-FIELD-RING R) (NOT (= (ONE R) (ZERO R)))))))
(dk-peel!)
(dk-project! '(NOT (= (ONE R) (ZERO R))) 'is-field-ring-def '(IS-FIELD-RING R))
(ass)
(ladet-done! 'ladet-field-one-ne)
(topic! 'ladet-field-one-ne 'plumbing)

