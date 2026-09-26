;;; =====================================================================
;;; bijection-from-inverse -- a map with a two-sided inverse is a bijection.
;;;
;;; Injectivity is psi applied to phi(a) = phi(b); surjectivity is the witness
;;; psi(w).  Nothing here is about finiteness, so it serves any reindexing.
;;; =====================================================================
(define r6a-bfi-stmt
  '(FORALL X (FORALL Y (FORALL phi (FORALL psi
     (IMPLIES (IN phi (FUN X Y))
      (IMPLIES (IN psi (FUN Y X))
       (IMPLIES (FORALL u_ (IMPLIES (IN u_ X) (= (psi (phi u_)) u_)))
        (IMPLIES (FORALL v_ (IMPLIES (IN v_ Y) (= (phi (psi v_)) v_)))
         (IN phi (BIJECTION X Y)))))))))))

;; the in-context universal whose body is an equation headed by `h'
(define (r6a-eq-head? h)
  (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                   (let ((b (caddr (caddr f))))
                     (and (pair? b) (eq? (car b) '=)
                          (pair? (cadr b)) (eq? (car (cadr b)) h))))))

(sp (make-wff r6a-bfi-stmt))
(dk-peel!)
(let ((left  (dk-pick (r6a-eq-head? 'psi) "psi(phi u) = u"))
      (right (dk-pick (r6a-eq-head? 'phi) "phi(psi v) = v")))
  (mac 'bijection-membership-iff)
  (dk-conj-close!
   (lambda ()
     (let ((g (dk-goal)))
       (cond
        ((eq? (car g) 'IN) (ass))                       ; phi in FUN(X,Y)
        ((r6a-any-subterm? (lambda (x) (eq? (car x) 'FORSOME)) g)
         (let ((wv (dk-di-var!)))                       ; surjectivity
           (fact 'fun-apply-type-c 'psi 'Y 'X wv)
           (dk-apply! right wv)
           (ew (list 'psi wv))
           (dk-conj-close!)))
        (#t                                             ; injectivity
         (dk-peel!)
         (let* ((gg (dk-goal)) (av (cadr gg)) (bv (caddr gg)))
           (dk-apply! left av)
           (dk-apply! left bv)
           (fact 'eq-sym (list 'psi (list 'phi av)) av)
           (subst (list '= av (list 'psi (list 'phi av))))
           (subst (list '= (list 'phi av) (list 'phi bv)))
           (ass))))))))
(r6a-done! 'bijection-from-inverse)
(gloss! 'bijection-from-inverse
  "A map with a two-sided inverse is a bijection: phi : X -> Y and psi : Y -> X
   with psi(phi u) = u on X and phi(psi v) = v on Y put phi in BIJECTION(X,Y).
   The bridge from an explicitly-inverted map to the BIJECTION term
   finsum-reindex-ag and its siblings demand.")

;;; =====================================================================
;;; lambda-compose-value -- ((z in D |-> ff(ph z)) pt) == ff(ph pt).
;;;
;;; ff and ph are VARIABLES, so the lambda body holds NO redex and `lam-b' has
;;; exactly one: the outer application.  That matters.  Fed a goal whose lambda
;;; body IS a redex, `lam-b' reduces UNDER the binder, and the membership it
;;; then owes is posted in the OUTER context -- where the binder variable is
;;; free and nothing constrains it, so the leaf is unprovable and nothing says
;;; so until `qed' (CLAUDE.md, "PEEL AND TYPE FIRST, THEN BETA").  This is the
;;; enum-fam-value device (rake-finsum-laws.scm) for the summand
;;; finsum-reindex-ag builds, which is an APPLIED lambda.
;;; =====================================================================
(sp (make-wff
  '(FORALL ff (FORALL ph (FORALL dm (FORALL pt
     (IMPLIES (IN pt dm)
       (== ((VNB-LAMBDA z dm (ff (ph z))) pt) (ff (ph pt))))))))))
(dk-peel!)
(lam-b)
(qrfl)
(r6a-done! 'lambda-compose-value)
(gloss! 'lambda-compose-value
  "The value of a reindexing lambda: (z in D |-> ff(ph z)) at pt in D is
   ff(ph pt).  Stated with ff and ph variables so a beta step can never fire
   under the binder.")

