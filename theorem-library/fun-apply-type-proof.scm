;;; fun-apply-type-proof.scm -- f : A -> B and x in A give f(x) in B, PROVEN.
;;;
;;; `fun-apply-type-c' was a PSS support in structure-library/order-lemmas.scm
;;; carrying the TOP warrant tier, `proof', with the text "Curried
;;; fun-apply-type: f:A->B and x in A give f(x) in B.  No AND antecedent."  That
;;; describes the statement, not a derivation, and no machine proof existed.
;;; The `warrant-invariant' gate cannot catch it: it excludes PSS supports by
;;; construction (load.scm), so a support can claim `proof' indefinitely.
;;;
;;; It is worth fixing first among the elementary gaps because it is the most
;;; widely cited of them -- it appears in the bills of `rr-complete' and
;;; `diagonalization' among others -- and because it is nearly free: the base
;;; theory already contains
;;;
;;;     fun-codomain-iff:  f in FUN(A,B)  iff  f in FUN(A) and
;;;                                            forall x in A. f(x) in B
;;;
;;; (theory.scm, inside make-vnb-base-theory, hence `primitive').  The proof is
;;; that IFF used left-to-right on the hypothesis, then its second conjunct
;;; instantiated at x -- six steps, and the resulting bill is `modulo 0'.
;;;
;;; The statement is deliberately CURRIED (nested implications, not one AND
;;; antecedent) so that `fact' peels and detaches both hypotheses in a single
;;; call.  That is not cosmetic: a conjunctive antecedent would force every
;;; caller to assemble the AND and `detach!' by hand, which is exactly the tax
;;; rr-add-closed imposes and rr-sup-in avoids.
;;;
;;; Loads after interactive/proof-debt and driver-kit, and before the earliest
;;; consumer that actually cites it in a proof (theorem-library/cancellation).
;;; Everything it needs is a base axiom, so it may sit as early as driver-kit.

;; ---- file-local helpers (fat- prefix; never named like a tactic) ----------
;; Select the assumption by CONTENT.  Never `(car (dk-asms))': picking the most
;; recent assumption by POSITION survives against a saved band -- a fixed
;; starting point, where landings always sit in the same order -- and breaks in
;; a fresh load, where they do not.
(define (fat-first-and)
  (let loop ((l (dk-asms)))
    (cond ((null? l) (error "fat-first-and: no conjunction in context"))
          ((and (pair? (car l)) (eq? (caar l) 'AND)) (car l))
          (else (loop (cdr l))))))

(define (fat-first-forall)
  (let loop ((l (dk-asms)))
    (cond ((null? l) (error "fat-first-forall: no universal in context"))
          ((and (pair? (car l)) (eq? (caar l) 'FORALL)) (car l))
          (else (loop (cdr l))))))

;;; fun-apply-type-c
(sp (make-wff '(FORALL f (FORALL a_ (FORALL b_ (FORALL x_
      (IMPLIES (IN f (FUN a_ b_))
        (IMPLIES (IN x_ a_) (IN (f x_) b_)))))))))
(di) (di) (di)
(mac-h 'fun-codomain-iff '(IN f (FUN a_ b_)))
(dk-split! (fat-first-and))
(inst+ (fat-first-forall) 'x_)
(ass)
(qed 'fun-apply-type-c)
(category! 'fun-apply-type-c 'plumbing)
