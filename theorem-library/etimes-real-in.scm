;;; etimes-real-in.scm -- lemmas MOVED 2026-11-10 (integration of the 11-09/10 waves) out of theorem-library/lp-convergence.scm
;;; into library analysis, for the library gate: cited by l2-families-2; extended reals.
;;; The proofs are the originals, verbatim; the helper defines are a copy of the source's.
;;;   etimes-real-in

(dk-skip-links!)   ; as in the source file

;;; ---- helper defines copied from lp-convergence.scm ----
(define (mdl-qed! name)
  (if (not (proof-done? *ps*))
      (for-each (lambda (l) (display ";; MDL OPEN ") (display (expression->string (dk-goal-of l))) (newline))
                (dk-open-leaves)))
  (qed name) (topic! name 'analysis))
(define (mdl-and! . fs)
  (let ((c (let loop ((l fs)) (if (null? (cdr l)) (car l) (list 'AND (car l) (loop (cdr l)))))))
    (if (not (dk-asm? c)) (dk-have! c (lambda () (dk-conj-close! (lambda () (dk-ass!))))))
    c))

;;; ---- the moved proofs ----
(sp (make-wff '(FORALL x (FORALL y (IMPLIES (IN x RR) (IMPLIES (<= 0 x) (IMPLIES (IN y RR) (IMPLIES (<= 0 y) (AND (IN (etimes x y) RR) (<= 0 (etimes x y)))))))))))
(dk-peel!)
(let ((e (dk-cite! 'etimes-real-defined 'x 'y)))
  (subst e)
  (dk-cite! 'bintimes-apply 'x 'y)
  (subst '(== (bintimes x y) (* x y)))
  (mdl-and! '(IN x RR) '(IN y RR))
  (dk-cite! 'rr-mul-closed 'x 'y)
  (dk-conj-close! (lambda () (if (not (dk-ass!)) (begin (mdl-and! '(<= 0 x) '(<= 0 y)) (dk-cite! 'rr-leq-mul-nonneg 'x 'y) (dk-ass!))))))
(mdl-qed! 'etimes-real-in)

