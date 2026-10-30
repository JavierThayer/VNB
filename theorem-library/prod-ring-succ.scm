;;; prod-ring-succ.scm -- lemmas MOVED 2026-10-27 (integration of the 10-26/27 wave) out of
;;; theorem-library/la-z2-diag.scm, so that files of library algebra may cite them (the library gate).
;;; The proofs are the originals, verbatim; the helper defines are a copy of la-z2-diag.scm's.  Loaded
;;; immediately before la-z2-diag.scm.
;;;   lzd-prod-succ

;;; ---- helper defines copied from la-z2-diag.scm ----
(define (lzd-done! name)
  (if (not (proof-done? *ps*))
      (begin
        (display "\n*** la-z2-diag: ") (display name) (display " did NOT close.\n")
        (for-each (lambda (l)
                    (display ";;   leaf: ")
                    (display (expression->string (dk-goal-of l))) (newline))
                  (dk-open-leaves))))
  (qed name))
(define (lzd-contra! notf)
  (if (not (eq? (dk-goal) 'FALSITY)) (pbc))
  (ai notf))

;;; ---- the moved proofs ----
(sp (make-wff (forall-guarded '(R s g)
                '((IS-COMMUTATIVE-RING R) (IN s NN)
                  (FORALL z_ (IMPLIES (IN z_ (INTERVAL 1 (succ s))) (IN (g z_) (CARR R)))))
                '(= (PROD-RING R g (INTERVAL 1 (succ s))) ((MUL R) (PROD-RING R g (INTERVAL 1 s)) (g (succ s)))))))
(dk-peel!)
(fact 'nn-succ-closed 's)
(fact 'interval-in-set 1 's) (fact 'interval-card-in-nn 1 's)
(fact 'membership-implies-sethood '(succ s) 'NN)
(dk-have! '(NOT (IN (succ s) (INTERVAL 1 s)))
  (lambda ()
    (di)
    (fact 'interval-hi 1 's '(succ s))
    (lzd-contra! (dk-cite! 'nn-succ-not-le 's))))
(let* ((e (dk-cite! 'interval-succ-insert 's))
       (u (caddr e))
       (h (dk-rewrite-h! '(FORALL z_ (IMPLIES (IN z_ (INTERVAL 1 (succ s))) (IN (g z_) (CARR R)))) '(INTERVAL 1 (succ s)) u)))
  (subst e)
  (dk-cite! 'prod-ring-insert-ptwise 'R '(INTERVAL 1 s) '(succ s) 'g)
  (ass))
(lzd-done! 'lzd-prod-succ)
(topic! 'lzd-prod-succ 'plumbing)

