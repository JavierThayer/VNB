;;; cc-real-part-facts.scm -- lemmas MOVED 2026-11-10 (integration of the 11-09/10 waves) out of theorem-library/ca-lft-cayley.scm
;;; into library analysis, for the library gate: cited by cc-real-bound; CC arithmetic.
;;; The proofs are the originals, verbatim; the helper defines are a copy of the source's.
;;;   cc-real-of-im-zero rr-imag-part-zero

;;; ---- helper defines copied from ca-lft-cayley.scm ----
(define (clk-finish-ass!)
  (if (not (sequent-node-grounded? (proof-state-focus *ps*))) (ass)))

;;; ---- the moved proofs ----
(sp (make-wff "forall([x in rr], imag-part(x) = 0)"))
(let ((x (dk-di-var!)))
  (fact 'rr-zero-in) (fact 'cc-i-in)
  (dk-cite! 'rr-subset-cc x)
  (dk-have! (list '= x (list '+ x (list '* 0 '+i))) (lambda () (crs)))
  (dk-split-all! (list (dk-cite! 'cc-re-im-of x x 0)))
  (clk-finish-ass!))
(qed 'rr-imag-part-zero)

(sp (make-wff "forall([z in cc], imag-part(z) = 0 implies z in rr)"))
(let ((z (car (map cadr (filter (lambda (f) (dk-head-is? f 'IN)) (dk-peel!))))))
  (fact 'cc-i-in)
  (dk-cite! 'real-part-in-rr z)
  (let* ((e (dk-cite! 'cc-re-im-decompose z))
         (x (caddr e)))
    (dk-cite! 'rr-subset-cc (list 'real-part z))
    (dk-have! (list '= x (list 'real-part z))
      (lambda () (subst (list '= (list 'imag-part z) 0)) (crs)))
    (dk-rewrite-h! e x (list 'real-part z))
    (subst (list '= z (list 'real-part z)))
    (clk-finish-ass!)))
(qed 'cc-real-of-im-zero)

