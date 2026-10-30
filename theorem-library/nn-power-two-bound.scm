;;; nn-power-two-bound.scm -- lemmas MOVED 2026-10-27 (integration of the 10-26/27 wave) out of
;;; theorem-library/goursat-bricks.scm, so that files of library analysis may cite them (the library gate).
;;; The proofs are the originals, verbatim; the helper defines are a copy of goursat-bricks.scm's.  Loaded
;;; immediately before goursat-bricks.scm.
;;;   nn-succ-le-power-two

;;; ---- helper defines copied from goursat-bricks.scm ----
(define (gb-and! a b)
  (let ((f (list 'AND a b)))
    (if (not (dk-asm? f)) (dk-have! f (lambda () (dk-conj-close! (lambda () (ass))))))
    f))

;;; ---- the moved proofs ----
(sp (make-wff '(FORALL gbk_ (IMPLIES (IN gbk_ NN) (<= (+ gbk_ 1) (power 2 gbk_))))))
(define gb-pl-br (use-induction))
(dk-focus! (cdr (assq 'base gb-pl-br)))
(dk-have! '(IN 2 CC) (lambda () (arith)))
(fact 'power-zero 2)
(subst '(= (power 2 0) 1))
(arith)
(dk-focus! (cdr (assq 'step gb-pl-br)))
(let ((k (cdr (assq 'var gb-pl-br)))
      (ih (cdr (assq 'ih gb-pl-br))))
  (dk-have! '(IN 2 CC) (lambda () (arith)))
  (gb-and! '(IN 2 CC) (list 'IN k 'NN))
  (subst (dk-cite! 'power-succ 2 k))
  (subst (dk-cite! 'nn-succ-plus-one k))
  (fact 'nn-in-rr k)
  (fact 'nn-zero-le k)
  (dk-type! (list 'power 2 k) 'RR)
  (dk-ineq! ih (list '<= 0 k)))
(qed 'nn-succ-le-power-two)

