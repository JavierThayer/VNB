;;; complex-inner-product-laws.scm -- what a sesquilinear form does in its SECOND
;;; argument, and the two expansion identities that follow.  All PROVEN modulo 0.
;;;
;;; structure-library/complex-inner-product.scm states the form minimally, the
;;; way a textbook does: additive and homogeneous in the FIRST argument,
;;; conjugate-symmetric, positive-definite.  Nothing there says what happens in
;;; the second argument, because nothing needs to: conjugating the first-argument
;;; laws gives it.  This file does that conjugating ONCE, and then does the only
;;; other thing every inner-product argument ever does -- expand <u,u> for a u
;;; built out of two vectors.
;;;
;;;   cc-conjugate-neg           conj(-a) = -conj(a)                    (in CC)
;;;   cips-ip-add-right          <x, y+z> = <x,y> + <x,z>
;;;   cips-ip-conj-homog-right   <x, a.y> = conj(a) <x,y>
;;;   cips-ip-zero-right         <x, 0> = 0
;;;   cips-expand-sum            <x+y, x+y> = <x,x> + <x,y> + conj<x,y> + <y,y>
;;;   cips-expand-two            <a.x + b.y, a.x + b.y>
;;;                                = a conj(a) <x,x> + a conj(b) <x,y>
;;;                                + b conj(a) conj<x,y> + b conj(b) <y,y>
;;;
;;; WHY THE TWO EXPANSIONS ARE THE POINT.  They are the whole of
;;; theorem-library/inner-product-inequalities.scm: Schwarz is `cips-expand-two'
;;; at (a,b) = (<y,y>, -<x,y>) plus one real cancellation, and Minkowski is
;;; `cips-expand-sum' plus Schwarz.  Proving the expansion once, in the general
;;; two-vector form, is what keeps those two proofs short -- the alternative is
;;; to re-run eight rewrites inside each of them.  A third inequality (the
;;; parallelogram law, polarization) would be a third instance of the same lemma.
;;;
;;; THE MECHANISM, and it is the same in all six proofs.  Land every law instance
;;; as a context EQUATION with `fact', rewrite them one at a time into the goal
;;; with `subst', and hand the residue -- which by then is a polynomial identity
;;; in the atoms <x,x>, <x,y>, conj<x,y>, <y,y>, a, b, conj a, conj b -- to
;;; `crs'.  That works because `ring-domain?' (ring-simplify.scm:190) accepts
;;; "cc": `crs' decides identities over the COMPLEX field as readily as over RR,
;;; and it treats `conjugate(t)' as an opaque generator, which is exactly right
;;; -- conjugation is not a ring operation, and every fact this file needs ABOUT
;;; it is supplied separately as one of the cc-conjugate-* axioms.  So each proof
;;; is a list of citations, a list of substitutions, and one `crs'.
;;;
;;; TWO TRAPS, both paid for in runs.
;;;
;;; * `subst' rewrites the GOAL only.  A chain like
;;;       <x,y+z> = conj<y+z,x> = conj(<y,x>+<z,x>) = conj<y,x> + conj<z,x>
;;;   is therefore not built forwards in the context; it is applied BACKWARDS to
;;;   the goal, each `subst' replacing the term the previous one exposed.  The
;;;   order of the `subst' calls below is that chain read from the top down, and
;;;   permuting them silently no-ops (a `subst' whose left side is not present
;;;   leaves the goal alone and says nothing).
;;;
;;; * MIT Scheme and the VNB reader both fold symbols to lowercase, so two
;;;   file-local term abbreviations differing only in case are ONE variable.
;;;   The first draft of inner-product-inequalities.scm defined `ii-p' for
;;;   <x,y> and `ii-P' for <x,y>conj<x,y>; the second clobbered the first, the
;;;   test vector went in as -|<x,y>|^2 instead of -<x,y>, and the only symptom
;;;   was a `crs' that declined an identity that was indeed not one.  The
;;;   abbreviations there are now ii-xy / ii-mod2.  This is the case-fold rule of
;;;   the working brief in its purest form: never distinguish two names by case.
;;;
;;; LOAD POSITION.  After structure-library/complex-inner-product (the CIPS
;;; projections it cites) and after interactive/proof-debt/driver-kit
;;; (sp/di/fact/have!/subst/crs/qed).  Nothing here needs SQRT or the order
;;; calculus; it is placed beside inner-product-inequalities.scm, its only
;;; consumer, which does.

;;; --------------------------------------------------------------------
;;; File-local driver helper (the `cip-' prefix -- never named like a tactic).

;;; Peel the whole FORALL/IMPLIES prefix.  Guarded on a fuel count as well as on
;;; the head: `di' only WARNS when it cannot decompose, so a head test alone
;;; spins forever on a no-op.
(define (cip-peel!)
  (let loop ((n 0))
    (let ((g (dk-goal)))
      (if (and (pair? g) (memq (car g) '(FORALL IMPLIES)) (< n 16))
          (begin (di) (loop (+ n 1))) #t))))


;; --- 1. cc-conjugate-neg -------------------------------------------------
(sp (make-wff '(FORALL a (IMPLIES (IN a CC) (= (conjugate (- a)) (- (conjugate a)))))))
(cip-peel!)
(fact 'cc-conjugate-closed 'a)
(have! '(IN -1 CC) (lambda () (arith)))
(have! '(IN -1 RR) (lambda () (arith)))
(have! '(= (- a) (* -1 a)) (lambda () (crs)))
(subst '(= (- a) (* -1 a)))
(have! '(AND (IN -1 CC) (IN a CC)))
(fact 'cc-conjugate-mul -1 'a)
(fact 'cc-conjugate-fixes-rr -1)
(subst '(= (conjugate (* -1 a)) (* (conjugate -1) (conjugate a))))
(subst '(= (conjugate -1) -1))
(crs)
(qed 'cc-conjugate-neg)
(topic! 'cc-conjugate-neg 'algebra)
(alias! 'cc-conjugate-neg "conjugation of a negative")

;; --- 2. cips-ip-add-right ------------------------------------------------
(sp (make-wff '(FORALL v (IMPLIES (IS-COMPLEX-INNER-PRODUCT-SPACE v)
  (FORALL x_ (IMPLIES (IN x_ (VEC v))
  (FORALL y_ (IMPLIES (IN y_ (VEC v))
  (FORALL z_ (IMPLIES (IN z_ (VEC v))
    (= ((IP v) x_ ((VADD v) y_ z_))
       (+ ((IP v) x_ y_) ((IP v) x_ z_)))))))))))))
(cip-peel!)
(fact 'cips-vadd-type 'v 'y_ 'z_)
(fact 'cips-ip-type 'v 'y_ 'x_)
(fact 'cips-ip-type 'v 'z_ 'x_)
(fact 'cc-conjugate-closed '((IP v) y_ x_))
(fact 'cc-conjugate-closed '((IP v) z_ x_))
(fact 'cips-ip-conj-sym 'v '((VADD v) y_ z_) 'x_)
(fact 'cips-ip-add-left 'v 'y_ 'z_ 'x_)
(have! '(AND (IN ((IP v) y_ x_) CC) (IN ((IP v) z_ x_) CC)))
(fact 'cc-conjugate-add '((IP v) y_ x_) '((IP v) z_ x_))
(fact 'cips-ip-conj-sym 'v 'y_ 'x_)
(fact 'cips-ip-conj-sym 'v 'z_ 'x_)
(subst '(= ((IP v) x_ ((VADD v) y_ z_)) (conjugate ((IP v) ((VADD v) y_ z_) x_))))
(subst '(= ((IP v) ((VADD v) y_ z_) x_) (+ ((IP v) y_ x_) ((IP v) z_ x_))))
(subst '(= (conjugate (+ ((IP v) y_ x_) ((IP v) z_ x_))) (+ (conjugate ((IP v) y_ x_)) (conjugate ((IP v) z_ x_)))))
(subst '(= ((IP v) x_ y_) (conjugate ((IP v) y_ x_))))
(subst '(= ((IP v) x_ z_) (conjugate ((IP v) z_ x_))))
(crs)
(qed 'cips-ip-add-right)
(topic! 'cips-ip-add-right 'algebra)
(alias! 'cips-ip-add-right "additivity of the inner product in its second argument")

;; --- 3. cips-ip-conj-homog-right ----------------------------------------
(sp (make-wff '(FORALL v (IMPLIES (IS-COMPLEX-INNER-PRODUCT-SPACE v)
  (FORALL a_ (IMPLIES (IN a_ CC)
  (FORALL x_ (IMPLIES (IN x_ (VEC v))
  (FORALL y_ (IMPLIES (IN y_ (VEC v))
    (= ((IP v) x_ ((ACT v) a_ y_))
       (* (conjugate a_) ((IP v) x_ y_))))))))))))) 
(cip-peel!)
(fact 'cips-act-type 'v 'a_ 'y_)
(fact 'cips-ip-type 'v 'y_ 'x_)
(fact 'cc-conjugate-closed 'a_)
(fact 'cc-conjugate-closed '((IP v) y_ x_))
(fact 'cips-ip-conj-sym 'v '((ACT v) a_ y_) 'x_)
(fact 'cips-ip-homog-left 'v 'a_ 'y_ 'x_)
(have! '(AND (IN a_ CC) (IN ((IP v) y_ x_) CC)))
(fact 'cc-conjugate-mul 'a_ '((IP v) y_ x_))
(fact 'cips-ip-conj-sym 'v 'y_ 'x_)
(subst '(= ((IP v) x_ ((ACT v) a_ y_)) (conjugate ((IP v) ((ACT v) a_ y_) x_))))
(subst '(= ((IP v) ((ACT v) a_ y_) x_) (* a_ ((IP v) y_ x_))))
(subst '(= (conjugate (* a_ ((IP v) y_ x_))) (* (conjugate a_) (conjugate ((IP v) y_ x_)))))
(subst '(= ((IP v) x_ y_) (conjugate ((IP v) y_ x_))))
(crs)
(qed 'cips-ip-conj-homog-right)
(topic! 'cips-ip-conj-homog-right 'algebra)
(alias! 'cips-ip-conj-homog-right "conjugate-homogeneity of the inner product in its second argument")

;; --- 4. cips-ip-zero-right ----------------------------------------------
(sp (make-wff '(FORALL v (IMPLIES (IS-COMPLEX-INNER-PRODUCT-SPACE v)
  (FORALL x_ (IMPLIES (IN x_ (VEC v))
    (= ((IP v) x_ (VZERO v)) 0)))))))
(cip-peel!)
(fact 'cips-vzero-in 'v)
(fact 'cips-ip-type 'v 'x_ '(VZERO v))
(fact 'cips-vadd-vzero 'v '(VZERO v))
(fact 'cips-ip-add-right 'v 'x_ '(VZERO v) '(VZERO v))
(have! '(= (+ ((IP v) x_ (VZERO v)) ((IP v) x_ (VZERO v))) ((IP v) x_ (VZERO v)))
       (lambda ()
         (subst '(= (+ ((IP v) x_ (VZERO v)) ((IP v) x_ (VZERO v)))
                    ((IP v) x_ ((VADD v) (VZERO v) (VZERO v)))))
         (subst '(= ((VADD v) (VZERO v) (VZERO v)) (VZERO v)))
         (crs)))
(have! '(= ((IP v) x_ (VZERO v))
           (+ (+ ((IP v) x_ (VZERO v)) ((IP v) x_ (VZERO v))) (- ((IP v) x_ (VZERO v)))))
       (lambda () (crs)))
(subst '(= ((IP v) x_ (VZERO v))
           (+ (+ ((IP v) x_ (VZERO v)) ((IP v) x_ (VZERO v))) (- ((IP v) x_ (VZERO v))))))
(subst '(= (+ ((IP v) x_ (VZERO v)) ((IP v) x_ (VZERO v))) ((IP v) x_ (VZERO v))))
(crs)
(qed 'cips-ip-zero-right)
(topic! 'cips-ip-zero-right 'algebra)
(alias! 'cips-ip-zero-right "the inner product with the zero vector vanishes")

;; --- 5. cips-expand-sum -------------------------------------------------
(sp (make-wff '(FORALL v (IMPLIES (IS-COMPLEX-INNER-PRODUCT-SPACE v)
  (FORALL x_ (IMPLIES (IN x_ (VEC v))
  (FORALL y_ (IMPLIES (IN y_ (VEC v))
    (= ((IP v) ((VADD v) x_ y_) ((VADD v) x_ y_))
       (+ (+ ((IP v) x_ x_) ((IP v) x_ y_))
          (+ (conjugate ((IP v) x_ y_)) ((IP v) y_ y_))))))))))))
(cip-peel!)
(fact 'cips-vadd-type 'v 'x_ 'y_)
(fact 'cips-ip-type 'v 'x_ 'x_)
(fact 'cips-ip-type 'v 'x_ 'y_)
(fact 'cips-ip-type 'v 'y_ 'x_)
(fact 'cips-ip-type 'v 'y_ 'y_)
(fact 'cc-conjugate-closed '((IP v) x_ y_))
(fact 'cips-ip-add-left 'v 'x_ 'y_ '((VADD v) x_ y_))
(fact 'cips-ip-add-right 'v 'x_ 'x_ 'y_)
(fact 'cips-ip-add-right 'v 'y_ 'x_ 'y_)
(fact 'cips-ip-conj-sym 'v 'x_ 'y_)
(subst '(= ((IP v) ((VADD v) x_ y_) ((VADD v) x_ y_))
           (+ ((IP v) x_ ((VADD v) x_ y_)) ((IP v) y_ ((VADD v) x_ y_)))))
(subst '(= ((IP v) x_ ((VADD v) x_ y_)) (+ ((IP v) x_ x_) ((IP v) x_ y_))))
(subst '(= ((IP v) y_ ((VADD v) x_ y_)) (+ ((IP v) y_ x_) ((IP v) y_ y_))))
(subst '(= ((IP v) y_ x_) (conjugate ((IP v) x_ y_))))
(crs)
(qed 'cips-expand-sum)
(topic! 'cips-expand-sum 'algebra)
(alias! 'cips-expand-sum "expansion of the inner product of a sum with itself")

;; --- 6. cips-expand-two -------------------------------------------------
(sp (make-wff
     (forall-guarded '(v a_ b_ x_ y_)
       (list '(IS-COMPLEX-INNER-PRODUCT-SPACE v) '(IN a_ CC) '(IN b_ CC)
             '(IN x_ (VEC v)) '(IN y_ (VEC v)))
       '(= ((IP v) ((VADD v) ((ACT v) a_ x_) ((ACT v) b_ y_))
                   ((VADD v) ((ACT v) a_ x_) ((ACT v) b_ y_)))
           (+ (+ (* (* a_ (conjugate a_)) ((IP v) x_ x_))
                 (* (* a_ (conjugate b_)) ((IP v) x_ y_)))
              (+ (* (* b_ (conjugate a_)) (conjugate ((IP v) x_ y_)))
                 (* (* b_ (conjugate b_)) ((IP v) y_ y_))))))))
(cip-peel!)
(fact 'cips-act-type 'v 'a_ 'x_)
(fact 'cips-act-type 'v 'b_ 'y_)
(fact 'cips-vadd-type 'v '((ACT v) a_ x_) '((ACT v) b_ y_))
(fact 'cips-ip-type 'v 'x_ 'x_)
(fact 'cips-ip-type 'v 'x_ 'y_)
(fact 'cips-ip-type 'v 'y_ 'x_)
(fact 'cips-ip-type 'v 'y_ 'y_)
(fact 'cc-conjugate-closed 'a_)
(fact 'cc-conjugate-closed 'b_)
(fact 'cc-conjugate-closed '((IP v) x_ y_))
(fact 'cips-ip-add-left 'v '((ACT v) a_ x_) '((ACT v) b_ y_)
      '((VADD v) ((ACT v) a_ x_) ((ACT v) b_ y_)))
(fact 'cips-ip-homog-left 'v 'a_ 'x_ '((VADD v) ((ACT v) a_ x_) ((ACT v) b_ y_)))
(fact 'cips-ip-homog-left 'v 'b_ 'y_ '((VADD v) ((ACT v) a_ x_) ((ACT v) b_ y_)))
(fact 'cips-ip-add-right 'v 'x_ '((ACT v) a_ x_) '((ACT v) b_ y_))
(fact 'cips-ip-add-right 'v 'y_ '((ACT v) a_ x_) '((ACT v) b_ y_))
(fact 'cips-ip-conj-homog-right 'v 'a_ 'x_ 'x_)
(fact 'cips-ip-conj-homog-right 'v 'b_ 'x_ 'y_)
(fact 'cips-ip-conj-homog-right 'v 'a_ 'y_ 'x_)
(fact 'cips-ip-conj-homog-right 'v 'b_ 'y_ 'y_)
(fact 'cips-ip-conj-sym 'v 'x_ 'y_)
(subst '(= ((IP v) ((VADD v) ((ACT v) a_ x_) ((ACT v) b_ y_))
                   ((VADD v) ((ACT v) a_ x_) ((ACT v) b_ y_)))
           (+ ((IP v) ((ACT v) a_ x_) ((VADD v) ((ACT v) a_ x_) ((ACT v) b_ y_)))
              ((IP v) ((ACT v) b_ y_) ((VADD v) ((ACT v) a_ x_) ((ACT v) b_ y_))))))
(subst '(= ((IP v) ((ACT v) a_ x_) ((VADD v) ((ACT v) a_ x_) ((ACT v) b_ y_)))
           (* a_ ((IP v) x_ ((VADD v) ((ACT v) a_ x_) ((ACT v) b_ y_))))))
(subst '(= ((IP v) ((ACT v) b_ y_) ((VADD v) ((ACT v) a_ x_) ((ACT v) b_ y_)))
           (* b_ ((IP v) y_ ((VADD v) ((ACT v) a_ x_) ((ACT v) b_ y_))))))
(subst '(= ((IP v) x_ ((VADD v) ((ACT v) a_ x_) ((ACT v) b_ y_)))
           (+ ((IP v) x_ ((ACT v) a_ x_)) ((IP v) x_ ((ACT v) b_ y_)))))
(subst '(= ((IP v) y_ ((VADD v) ((ACT v) a_ x_) ((ACT v) b_ y_)))
           (+ ((IP v) y_ ((ACT v) a_ x_)) ((IP v) y_ ((ACT v) b_ y_)))))
(subst '(= ((IP v) x_ ((ACT v) a_ x_)) (* (conjugate a_) ((IP v) x_ x_))))
(subst '(= ((IP v) x_ ((ACT v) b_ y_)) (* (conjugate b_) ((IP v) x_ y_))))
(subst '(= ((IP v) y_ ((ACT v) a_ x_)) (* (conjugate a_) ((IP v) y_ x_))))
(subst '(= ((IP v) y_ ((ACT v) b_ y_)) (* (conjugate b_) ((IP v) y_ y_))))
(subst '(= ((IP v) y_ x_) (conjugate ((IP v) x_ y_))))
(crs)
(qed 'cips-expand-two)
(topic! 'cips-expand-two 'algebra)
(alias! 'cips-expand-two "expansion of the inner product of a linear combination with itself")
