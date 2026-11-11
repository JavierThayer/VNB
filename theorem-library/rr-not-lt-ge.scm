;;; rr-not-lt-ge.scm -- lemmas MOVED 2026-11-10 (integration of the 11-09/10 waves) out of theorem-library/ccr2-nv.scm
;;; into library core, for the library gate: cited by ccr4c-finite-char (algebra); RR order.
;;; The proofs are the originals, verbatim; the helper defines are a copy of the source's.
;;;   rr-not-lt-ge

;;; ---- helper defines copied from ccr2-nv.scm ----
(define (cw-or-each! o handler)
  (if (not (dk-head-is? o 'OR))
      (handler o)
      (dk-each-leaf! (lambda () (ai o))
        (lambda ()
          (cond ((dk-asm? (cadr o)) (handler (cadr o)))
                ((and (pair? (caddr o)) (eq? (car (caddr o)) 'OR)) (cw-or-each! (caddr o) handler))
                (#t (handler (caddr o))))))))
(define (cw-and! . fs)
  (let ((c (let loop ((fs fs)) (if (null? (cdr fs)) (car fs) `(AND ,(car fs) ,(loop (cdr fs)))))))
    (dk-have! c (lambda () (dk-conj-close! (lambda () (dk-ass!)))))
    c))

;;; ---- the moved proofs ----
(sp (make-wff '(FORALL cra (IMPLIES (IN cra RR) (FORALL crb (IMPLIES (IN crb RR) (IMPLIES (NOT (< cra crb)) (<= crb cra))))))))
(dk-peel!)
(cw-and! '(IN crb RR) '(IN cra RR))
(cw-or-each! (dk-cite! 'rr-leq-total 'crb 'cra)
  (lambda (o)
    (if (equal? o '(<= crb cra))
        (dk-ass!)
        (use-em '(= cra crb)
          (lambda () (dk-ineq! '(= cra crb)))
          (lambda ()
            (pbc)
            (cw-and! '(<= cra crb) '(NOT (= cra crb)))
            (dk-cite! 'rr-le-ne-lt 'cra 'crb)
            (ai '(NOT (< cra crb))))))))
(qed 'rr-not-lt-ge)

