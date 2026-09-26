;;; factorial-in-nn.scm -- n! is a natural number, PROVEN.
;;; Batch 27-A follow-on, 2026-09-24.
;;;
;;; The statement is the axiom of structure-library/injection.scm:221, copied
;;; literally.  Induction on n: 0! = succ(0) is in NN (factorial-zero), and
;;; (n+1)! = (n+1) n! is a product of naturals (factorial-succ, nn-mul-closed).
;;; NOTHING asserted.  Helper prefix: fnn-.
;;; LOAD WINDOW: lo = structure-library/injection (factorial-zero,
;;; factorial-succ); hi: none (no theorem-library file cites factorial-in-nn;
;;; taylor-proof.scm names it only in a comment).

(sp (make-wff '(FORALL n (IMPLIES (IN n NN) (IN (FACTORIAL n) NN)))))
(define fnn-br (use-induction))
(define fnn-v (cdr (assq 'var fnn-br)))
(define fnn-ih (cdr (assq 'ih fnn-br)))
(dk-focus! (cdr (assq 'base fnn-br)))
(fact 'nn-zero-in)
(fact 'nn-succ-closed 0)
(subst (dk-fact! 'factorial-zero))
(ass)
(dk-focus! (cdr (assq 'step fnn-br)))
(fact 'nn-succ-closed fnn-v)
(subst (dk-fact! 'factorial-succ fnn-v))
(dk-have! (list 'AND (list 'IN (list 'succ fnn-v) 'NN) (list 'IN (list 'FACTORIAL fnn-v) 'NN))
  (lambda () (dk-conj-close! (lambda () (ass)))))
(fact 'nn-mul-closed (list 'succ fnn-v) (list 'FACTORIAL fnn-v))
(ass)
(qed 'factorial-in-nn)
