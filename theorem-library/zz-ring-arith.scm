;;; zz-ring-arith.scm -- lemmas MOVED 2026-10-27 (integration of the 10-26/27 wave) out of
;;; theorem-library/la-z5-zzmod.scm, so that files of library algebra may cite them (the library gate).
;;; The proofs are the originals, verbatim; the helper defines are a copy of la-z5-zzmod.scm's.  Loaded
;;; immediately before la-z5-zzmod.scm.
;;;   zz-ring-add-neg zz-ring-mul-is-mul

;;; ---- helper defines copied from la-z5-zzmod.scm ----
(define (lz5z-done! name)
  (if (not (proof-done? *ps*))
      (begin
        (display "\n*** la-z5-zzmod: ") (display name) (display " did NOT close.\n")
        (for-each (lambda (l)
                    (display ";;   leaf: ")
                    (display (expression->string (dk-goal-of l))) (newline)
                    (for-each (lambda (a) (display ";;      asm: ") (display (expression->string a)) (newline))
                              (dk-asms-of l)))
                  (dk-open-leaves))))
  (qed name)
  (topic! name 'algebra))

;;; ---- the moved proofs ----
(sp (make-wff (forall-guarded '(x y) '((IN x ZZ) (IN y ZZ))
  '(= ((ADD ZZ-RING) x ((NEG ZZ-RING) y)) (+ x (- y))))))
(dk-peel!)
(fact 'zz-neg-closed 'y)
(dk-have! '(AND (IN x ZZ) (IN (- y) ZZ)) (lambda () (dk-conj-close! (lambda () (ass)))))
(fact 'zz-add-closed 'x '(- y))
(slot 'NEG)
(dk-lam-b!)
(slot 'ADD)
(if (not (dk-lam-b!)) (rfl))
(lz5z-done! 'zz-ring-add-neg)

(sp (make-wff (forall-guarded '(t b) '((IN t ZZ) (IN b ZZ))
  '(= ((MUL ZZ-RING) t b) (* t b)))))
(dk-peel!)
(dk-have! '(AND (IN t ZZ) (IN b ZZ)) (lambda () (dk-conj-close! (lambda () (ass)))))
(fact 'zz-mul-closed 't 'b)
(slot 'MUL)
(if (not (dk-lam-b!)) (rfl))
(lz5z-done! 'zz-ring-mul-is-mul)

