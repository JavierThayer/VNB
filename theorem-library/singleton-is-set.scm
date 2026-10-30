;;; singleton-is-set.scm -- lemmas MOVED 2026-10-27 (integration of the 10-26/27 wave) out of
;;; theorem-library/ca-lft-plane.scm, so that files of library core may cite them (the library gate).
;;; The proofs are the originals, verbatim; the helper defines are a copy of ca-lft-plane.scm's.  Loaded
;;; immediately before ca-lft-plane.scm.
;;;   singleton-is-set

;;; ---- helper defines copied from ca-lft-plane.scm ----
(define (clp-finish-ass!)
  (if (not (sequent-node-grounded? (proof-state-focus *ps*))) (ass)))

;;; ---- the moved proofs ----
(sp (make-wff "forall([y in set], singleton(y) in set)"))
(let ((y (dk-di-var!)))
  (fact 'power-set y)
  (dk-have! (list 'SUBSET (list 'SINGLETON y) (list 'POWER y))
    (lambda ()
      (let ((x (subset-by-element!)))
        (fact 'singleton-membership y x)
        (let* ((pm  (dk-cite! 'power-set-membership y x))
               (all (caddr (caddr pm))))
          (dk-have! (list '= x y) (lambda () (prop)))
          (dk-have! (list 'IN x 'SET) (lambda () (prop)))
          (dk-have! all (lambda () (dk-peel!) (subst (list '= y x)) (ass)))
          (prop)))))
  (dk-cite! 'subclass-of-set-is-set (list 'SINGLETON y) (list 'POWER y))
  (clp-finish-ass!))
(qed 'singleton-is-set)

