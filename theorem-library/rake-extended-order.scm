;;; theorem-library/rake-extended-order.scm -- the order and addition theory of
;;; RR-POS-STAR = [0, +inf], built on the user's new axiom `pos-inf-above-reals'
;;; (structure-library/extended-reals.scm, stamped `primitive', 2026-09-18).
;;;
;;; Rake batch 5b-H.  The bricks are the ones theorem-library/rake-measure.scm's
;;; closing block names X1-X3 and X5-X8; every measure leaf that is blocked
;;; today is blocked on them.  They did not exist: before this file no theorem
;;; or axiom in the tree mentioned `eplus' and `<=' in the same formula, and the
;;; only order facts about POS-INF were the two BOUNDS.
;;;
;;; WHAT MAKES THEM PROVABLE.  `pos-inf-above-reals' -- forall x in RR.
;;; NOT (POS-INF <= x) -- is the one fact that lets a case split on
;;; `rr-pos-star-membership' DISCARD the POS-INF case: below a real there is no
;;; infinity, so an element of [0,+inf] that lies below a real is a real, and
;;; the RR order axioms (all guarded on IN _ RR) take over.  That one step is
;;; isolated here as `rr-pos-star-le-real-in-rr' and every later proof uses it.
;;;
;;; CONTENTS
;;;   rr-pos-star-le-real-in-rr   x in RR-POS-STAR, t in RR, x <= t => x in RR
;;;   rr-pos-star-le-refl         X1
;;;   rr-pos-star-le-trans        X2
;;;   rr-pos-star-le-antisymm     X3   (so ESUP, hence ESUM/EINF/INTEGRAL, is
;;;                                     pinned down by its characterising axioms)
;;;   eplus-closed                x,y in RR-POS-STAR => eplus(x,y) in RR-POS-STAR
;;;   eplus-zero-left / -right    X5
;;;   eplus-comm, eplus-assoc     X6   (proved from the three eplus equations
;;;                                     DIRECTLY, not read off the asserted
;;;                                     `rr-pos-star-is-comm-monoid': a case
;;;                                     split is cheaper than a view read-off
;;;                                     and it keeps that assertion off the bill)
;;;   eplus-le-left               X7
;;;   eplus-mono                  X8
;;;   esum-bounded-implies-finite the (<=) half of the support below
;;;   esum-finite-iff-bounded     the support (extended-sum.scm:79), RETIRE IT
;;;
;;; LOAD WINDOW [247, end).  lo = 247 is forced by ONE citation, `finsum-empty'
;;; (theorem-library/finsum-insert, position 246); everything else this file
;;; cites is far earlier -- number-systems (34), numeric-instances (71),
;;; extended-reals (78), extended-reals-pos (79), cardinality (85),
;;; extended-sum (124) -- and the tactics are `interactive' (139),
;;; `driver-kit' (143), `prop' (148).  Nothing PROVEN cites any of these names
;;; (summability.scm mentions esum-finite-iff-bounded only in comments), so no
;;; citer forces `hi'.  Without the ESUM block the file would sit at [149, end).
;;;
;;; Helper prefix: r6h-.

;;; -----------------------------------------------------------------------
;;; The case split every proof in this file opens with.
;;;
;;; rr-pos-star-membership says x in RR-POS-STAR iff (x in RR and 0 <= x) or
;;; x = POS-INF.  `fact' lands the instance, `prop' turns it plus the typing
;;; hypothesis into the disjunction, and `use-cases' splits it -- with no
;;; exhaustiveness obligation, since the disjunction is already in context.

(define (r6h-real-case tm) (list 'AND (list 'IN tm 'RR) (list '<= 0 tm)))
(define (r6h-inf-case  tm) (list '= tm 'POS-INF))

;;; The lane weakens down to the membership iff and the typing before calling
;;; `prop': the contexts here run past prop's atom cap once two case splits are
;;; nested, and a declined `prop' reads as "not propositional" when it means
;;; "I did not look at the right atoms" (CLAUDE.md).
(define (r6h-star-cases! tm real-body inf-body)
  (have! (list 'OR (r6h-real-case tm) (r6h-inf-case tm))
         (lambda ()
           (let ((inst (dk-fact! 'rr-pos-star-membership tm)))
             (dk-only! inst (list 'IN tm 'RR-POS-STAR))
             (prop))))
  (use-cases (list (r6h-real-case tm) (r6h-inf-case tm)) real-body inf-body))

;;; Close a goal that IS (IN POS-INF RR-POS-STAR), in a branch holding
;;; (= TM POS-INF) and (IN TM RR-POS-STAR).  `have!' cannot be used for this:
;;; cutting the focus goal itself is an alpha self-loop.
(define (r6h-close-inf-typed! tm)
  (fact 'equality-symmetry tm 'POS-INF)
  (subst (list '= 'POS-INF tm))
  (ass))

;;; In a branch holding (= TM POS-INF) and (IN TM RR-POS-STAR): land
;;; (= POS-INF TM), (IN POS-INF RR-POS-STAR) and (<= POS-INF POS-INF).
;;; The typing is taken off TM rather than from `pos-inf-in-rr-pos-star', which
;;; keeps that axiom off the bill; `rr-pos-star-below-pos-inf' cannot be avoided
;;; -- it is the only axiom that says anything lies below POS-INF.
(define (r6h-pos-inf-facts! tm)
  (fact 'equality-symmetry tm 'POS-INF)
  (have! '(IN POS-INF RR-POS-STAR)
         (lambda () (subst (list '= 'POS-INF tm)) (ass)))
  (fact 'rr-pos-star-below-pos-inf 'POS-INF))

;;; A bare (ineq) passes ZERO premises to the oracle (calc.scm:73), so every
;;; call here names them.  The lane weakens the context down to the arithmetic
;;; facts first and then hands the oracle every index: a non-arithmetic premise
;;; is skipped, but an `=' between non-real terms would poison the call.
(define (r6h-indices n)
  (let loop ((k n) (acc '())) (if (= k 0) acc (loop (- k 1) (cons k acc)))))

(define (r6h-ineq! claim . keepers)
  (have! claim
         (lambda ()
           (apply dk-only! keepers)
           (apply ineq (r6h-indices (length (dk-asms)))))))

;;; The same, on the focus goal itself (a `have!' of the goal is a self-loop).
;;; Only ever called on a leaf this closes, so the weakening costs nothing.
(define (r6h-ineq-close! . keepers)
  (apply dk-only! keepers)
  (apply ineq (r6h-indices (length (dk-asms)))))

;;; Goal-side rewrites of the three `eplus' equations.  The `sub-' pair is the
;;; rewrite ALONE, for a second use of an equation already landed: a repeated
;;; `fact' of the same instance moves nothing and would be reported as an inert
;;; step (interactive.scm's boundary notice).
(define (r6h-sub-inf-left! tm)            ; eplus(POS-INF, tm) -> POS-INF
  (subst (list '= (list 'eplus 'POS-INF tm) 'POS-INF)))
(define (r6h-sub-inf-right! tm)           ; eplus(tm, POS-INF) -> POS-INF
  (subst (list '= (list 'eplus tm 'POS-INF) 'POS-INF)))

(define (r6h-eplus-inf-left! tm)
  (fact 'eplus-pos-inf-left tm)
  (r6h-sub-inf-left! tm))

(define (r6h-eplus-inf-right! tm)
  (fact 'eplus-pos-inf-right tm)
  (r6h-sub-inf-right! tm))

;;; `eplus-real-defined' (theorem-library/rake-eplus-defined.scm) is the finite case of
;;; the DEFINED eplus: curried, and guarded 0 <= a, 0 <= b -- the old axiom `eplus-real'
;;; held for all reals and was one half of an inconsistency (2026-09-18).  So the
;;; nonnegativity of each argument is landed first, from whichever source the context has.
(define (r6h-nonneg! tm)
  (let ((claim (list '<= 0 tm)))
    (if (not (dk-asm? claim))
        (cond ((equal? tm 0) (have! claim (lambda () (arith))))
              ((dk-asm? (list 'IN tm 'RR-POS-STAR)) (fact 'rr-pos-star-nonneg tm))
              ((and (pair? tm) (eq? (car tm) '+))
               (r6h-ineq! claim
                          (list '<= 0 (cadr tm)) (list '<= 0 (caddr tm))
                          (list 'IN (cadr tm) 'RR) (list 'IN (caddr tm) 'RR)
                          (list 'IN tm 'RR)))
              (#t (error "r6h-nonneg!: no source for" claim))))))

(define (r6h-eplus-real! a b)             ; eplus(a, b) -> (+ a b), a, b real and >= 0
  (have! (list 'AND (list 'IN a 'RR) (list 'IN b 'RR)))
  (r6h-nonneg! a)
  (r6h-nonneg! b)
  (fact 'eplus-real-defined a b)
  (subst (list '= (list 'eplus a b) (list 'binplus a b)))
  (fact 'binplus-apply a b)
  (subst (list '== (list 'binplus a b) (list '+ a b))))

;;; -----------------------------------------------------------------------
;;; X1  rr-pos-star-le-refl:  x in RR-POS-STAR => x <= x.

(sp (make-wff '(FORALL x (IMPLIES (IN x RR-POS-STAR) (<= x x)))))
(dk-peel!)
(r6h-star-cases! 'x
  (lambda ()
    (dk-split! (r6h-real-case 'x))
    (fact 'rr-leq-reflexive 'x)
    (ass))
  (lambda ()
    (subst '(= x POS-INF))
    (r6h-pos-inf-facts! 'x)
    (ass)))
(qed 'rr-pos-star-le-refl)
(topic! 'rr-pos-star-le-refl 'analysis)

;;; -----------------------------------------------------------------------
;;; rr-pos-star-le-real-in-rr:  an element of [0,+inf] that lies below a REAL
;;; is itself real.  This is the whole content of `pos-inf-above-reals', in the
;;; form every later proof wants.

(sp (make-wff
     '(FORALL x (FORALL y
        (IMPLIES (AND (IN x RR-POS-STAR) (IN y RR))
          (IMPLIES (<= x y) (IN x RR)))))))
(dk-peel!)
(dk-split! '(AND (IN x RR-POS-STAR) (IN y RR)))
(r6h-star-cases! 'x
  (lambda ()
    (dk-split! (r6h-real-case 'x))
    (ass))
  (lambda ()
    (fact 'equality-symmetry 'x 'POS-INF)
    (have! '(<= POS-INF y)
           (lambda () (subst '(= POS-INF x)) (ass)))
    (fact 'pos-inf-above-reals 'y)
    (ai '(NOT (<= POS-INF y)))))
(qed 'rr-pos-star-le-real-in-rr)
(topic! 'rr-pos-star-le-real-in-rr 'analysis)

;;; -----------------------------------------------------------------------
;;; X2  rr-pos-star-le-trans.
;;;
;;; The POS-INF case is discharged at the TOP element: if z = POS-INF the
;;; conclusion is `rr-pos-star-below-pos-inf' and neither hypothesis is used.
;;; If z is real then y is real (it lies below z) and then x is real, and
;;; `rr-leq-transitive' applies.

(sp (make-wff
     '(FORALL x (FORALL y (FORALL z
        (IMPLIES (AND (IN x RR-POS-STAR) (AND (IN y RR-POS-STAR) (IN z RR-POS-STAR)))
          (IMPLIES (AND (<= x y) (<= y z)) (<= x z))))))))
(dk-peel!)
(dk-split! '(AND (IN x RR-POS-STAR) (AND (IN y RR-POS-STAR) (IN z RR-POS-STAR))))
(dk-split! '(AND (<= x y) (<= y z)))
(r6h-star-cases! 'z
  (lambda ()
    (dk-split! (r6h-real-case 'z))
    (have! '(AND (IN y RR-POS-STAR) (IN z RR)))
    (fact 'rr-pos-star-le-real-in-rr 'y 'z)
    (have! '(AND (IN x RR-POS-STAR) (IN y RR)))
    (fact 'rr-pos-star-le-real-in-rr 'x 'y)
    (have! '(AND (IN x RR) (AND (IN y RR) (IN z RR))))
    (have! '(AND (<= x y) (<= y z)))
    (fact 'rr-leq-transitive 'x 'y 'z)
    (ass))
  (lambda ()
    (subst '(= z POS-INF))
    (fact 'rr-pos-star-below-pos-inf 'x)
    (ass)))
(qed 'rr-pos-star-le-trans)
(topic! 'rr-pos-star-le-trans 'analysis)

;;; -----------------------------------------------------------------------
;;; X3  rr-pos-star-le-antisymm.  This is the fact extended-reals-pos.scm's
;;; header assumes when it says the least upper bound is unique, so it is what
;;; makes ESUP -- and with it ESUM, EINF, ELIMINF, ELIMSUP and INTEGRAL --
;;; determined by its characterising axioms.

(sp (make-wff
     '(FORALL x (FORALL y
        (IMPLIES (AND (IN x RR-POS-STAR) (IN y RR-POS-STAR))
          (IMPLIES (AND (<= x y) (<= y x)) (= x y)))))))
(dk-peel!)
(dk-split! '(AND (IN x RR-POS-STAR) (IN y RR-POS-STAR)))
(dk-split! '(AND (<= x y) (<= y x)))
(r6h-star-cases! 'y
  (lambda ()
    (dk-split! (r6h-real-case 'y))
    (have! '(AND (IN x RR-POS-STAR) (IN y RR)))
    (fact 'rr-pos-star-le-real-in-rr 'x 'y)
    (have! '(AND (IN x RR) (IN y RR)))
    (have! '(AND (<= x y) (<= y x)))
    (fact 'rr-leq-antisymmetric 'x 'y)
    (ass))
  (lambda ()
    (fact 'equality-symmetry 'y 'POS-INF)
    (r6h-star-cases! 'x
      (lambda ()
        (dk-split! (r6h-real-case 'x))
        (have! '(<= POS-INF x) (lambda () (subst '(= POS-INF y)) (ass)))
        (fact 'pos-inf-above-reals 'x)
        (ai '(NOT (<= POS-INF x))))
      (lambda ()
        (have! '(AND (= x POS-INF) (= POS-INF y)))
        (fact 'equality-transitivity 'x 'POS-INF 'y)
        (ass)))))
(qed 'rr-pos-star-le-antisymm)
(topic! 'rr-pos-star-le-antisymm 'analysis)

;;; -----------------------------------------------------------------------
;;; eplus-closed:  [0,+inf] is closed under extended addition.
;;;
;;; `eplus-in-fun' asserts the same thing as a FUN typing; this is the applied
;;; form, and it is proved from the three defining equations instead, so the
;;; sethood claim `eplus-in-fun' makes stays off the bill.  Every absorbing case
;;; is POS-INF; the finite case is `rr-add-closed' plus the nonnegativity of a
;;; sum of nonnegatives.

(sp (make-wff
     '(FORALL x (FORALL y
        (IMPLIES (AND (IN x RR-POS-STAR) (IN y RR-POS-STAR))
          (IN (eplus x y) RR-POS-STAR))))))
(dk-peel!)
(dk-split! '(AND (IN x RR-POS-STAR) (IN y RR-POS-STAR)))
(r6h-star-cases! 'x
  (lambda ()
    (dk-split! (r6h-real-case 'x))
    (r6h-star-cases! 'y
      (lambda ()
        (dk-split! (r6h-real-case 'y))
        (r6h-eplus-real! 'x 'y)
        (r6h-ineq! '(<= 0 (+ x y)) '(IN x RR) '(IN y RR) '(<= 0 x) '(<= 0 y))
        (fact 'rr-add-closed 'x 'y)
        (let ((inst (dk-fact! 'rr-pos-star-membership '(+ x y))))
          (dk-only! inst '(IN (+ x y) RR) '(<= 0 (+ x y)))
          (prop)))
      (lambda ()
        (subst '(= y POS-INF))
        (r6h-eplus-inf-right! 'x)
        (r6h-close-inf-typed! 'y))))
  (lambda ()
    (subst '(= x POS-INF))
    (r6h-eplus-inf-left! 'y)
    (r6h-close-inf-typed! 'x)))
(qed 'eplus-closed)
(topic! 'eplus-closed 'analysis)

;;; -----------------------------------------------------------------------
;;; X5  eplus-zero-left / eplus-zero-right:  0 is the identity of eplus.

(sp (make-wff '(FORALL x (IMPLIES (IN x RR-POS-STAR) (= (eplus 0 x) x)))))
(dk-peel!)
(fact 'rr-zero-in)
(r6h-star-cases! 'x
  (lambda ()
    (dk-split! (r6h-real-case 'x))
    (r6h-eplus-real! 0 'x)
    (fact 'rr-add-comm 0 'x)
    (subst '(= (+ 0 x) (+ x 0)))
    (fact 'rr-add-zero 'x)
    (ass))
  (lambda ()
    (subst '(= x POS-INF))
    (have! '(IN 0 RR-POS-STAR) (lambda () (fact 'zero-in-rr-pos-star) (ass)))
    (r6h-eplus-inf-right! 0)
    (rfl)))
(qed 'eplus-zero-left)
(topic! 'eplus-zero-left 'analysis)

(sp (make-wff '(FORALL x (IMPLIES (IN x RR-POS-STAR) (= (eplus x 0) x)))))
(dk-peel!)
(fact 'rr-zero-in)
(r6h-star-cases! 'x
  (lambda ()
    (dk-split! (r6h-real-case 'x))
    (r6h-eplus-real! 'x 0)
    (fact 'rr-add-zero 'x)
    (ass))
  (lambda ()
    (subst '(= x POS-INF))
    (have! '(IN 0 RR-POS-STAR) (lambda () (fact 'zero-in-rr-pos-star) (ass)))
    (r6h-eplus-inf-left! 0)
    (rfl)))
(qed 'eplus-zero-right)
(topic! 'eplus-zero-right 'analysis)

;;; -----------------------------------------------------------------------
;;; X6  eplus-comm and eplus-assoc.
;;;
;;; These are two of the three laws packed inside the asserted
;;; `rr-pos-star-is-comm-monoid'.  They are proved here from the three eplus
;;; equations by cases, NOT read off the monoid: a read-off would put that
;;; assertion (warrant `well-known') on the bill of every later measure proof,
;;; and the case split is shorter than the view read-off would be.

(sp (make-wff
     '(FORALL x (FORALL y
        (IMPLIES (AND (IN x RR-POS-STAR) (IN y RR-POS-STAR))
          (= (eplus x y) (eplus y x)))))))
(dk-peel!)
(dk-split! '(AND (IN x RR-POS-STAR) (IN y RR-POS-STAR)))
(r6h-star-cases! 'x
  (lambda ()
    (dk-split! (r6h-real-case 'x))
    (r6h-star-cases! 'y
      (lambda ()
        (dk-split! (r6h-real-case 'y))
        (r6h-eplus-real! 'x 'y)
        (r6h-eplus-real! 'y 'x)
        (fact 'rr-add-comm 'x 'y)
        (ass))
      (lambda ()
        (subst '(= y POS-INF))
        (r6h-eplus-inf-right! 'x)
        (r6h-eplus-inf-left! 'x)
        (rfl))))
  (lambda ()
    (subst '(= x POS-INF))
    (r6h-eplus-inf-left! 'y)
    (r6h-eplus-inf-right! 'y)
    (rfl)))
(qed 'eplus-comm)
(topic! 'eplus-comm 'analysis)

(sp (make-wff
     '(FORALL x (FORALL y (FORALL z
        (IMPLIES (AND (IN x RR-POS-STAR) (AND (IN y RR-POS-STAR) (IN z RR-POS-STAR)))
          (= (eplus (eplus x y) z) (eplus x (eplus y z)))))))))
(dk-peel!)
(dk-split! '(AND (IN x RR-POS-STAR) (AND (IN y RR-POS-STAR) (IN z RR-POS-STAR))))
(have! '(AND (IN x RR-POS-STAR) (IN y RR-POS-STAR)))
(fact 'eplus-closed 'x 'y)
(have! '(AND (IN y RR-POS-STAR) (IN z RR-POS-STAR)))
(fact 'eplus-closed 'y 'z)
(r6h-star-cases! 'x
  (lambda ()
    (dk-split! (r6h-real-case 'x))
    (r6h-star-cases! 'y
      (lambda ()
        (dk-split! (r6h-real-case 'y))
        (r6h-star-cases! 'z
          (lambda ()
            (dk-split! (r6h-real-case 'z))
            (r6h-eplus-real! 'x 'y)
            (r6h-eplus-real! 'y 'z)
            (fact 'rr-add-closed 'x 'y)
            (fact 'rr-add-closed 'y 'z)
            (r6h-eplus-real! '(+ x y) 'z)
            (r6h-eplus-real! 'x '(+ y z))
            (have! '(AND (IN x RR) (AND (IN y RR) (IN z RR))))
            (fact 'rr-add-assoc 'x 'y 'z)
            (ass))
          (lambda ()
            (subst '(= z POS-INF))
            (fact 'eplus-pos-inf-right '(eplus x y))
            (fact 'eplus-pos-inf-right 'y)
            (fact 'eplus-pos-inf-right 'x)
            (r6h-sub-inf-right! '(eplus x y))
            (r6h-sub-inf-right! 'y)
            (r6h-sub-inf-right! 'x)
            (rfl))))
      (lambda ()
        (subst '(= y POS-INF))
        (fact 'eplus-pos-inf-left 'z)
        (fact 'eplus-pos-inf-right 'x)
        (r6h-sub-inf-left! 'z)
        (r6h-sub-inf-right! 'x)
        (r6h-sub-inf-left! 'z)
        (rfl))))
  (lambda ()
    (subst '(= x POS-INF))
    (fact 'eplus-pos-inf-left 'y)
    (fact 'eplus-pos-inf-left 'z)
    (fact 'eplus-pos-inf-left '(eplus y z))
    (r6h-sub-inf-left! 'y)
    (r6h-sub-inf-left! '(eplus y z))
    (r6h-sub-inf-left! 'z)
    (rfl)))
(qed 'eplus-assoc)
(topic! 'eplus-assoc 'analysis)

;;; -----------------------------------------------------------------------
;;; X7  eplus-le-left:  x <= eplus(x, y).  Adding a nonnegative extended real
;;; never decreases; at POS-INF both sides collapse to the top.

(sp (make-wff
     '(FORALL x (FORALL y
        (IMPLIES (AND (IN x RR-POS-STAR) (IN y RR-POS-STAR))
          (<= x (eplus x y)))))))
(dk-peel!)
(dk-split! '(AND (IN x RR-POS-STAR) (IN y RR-POS-STAR)))
(r6h-star-cases! 'x
  (lambda ()
    (dk-split! (r6h-real-case 'x))
    (r6h-star-cases! 'y
      (lambda ()
        (dk-split! (r6h-real-case 'y))
        (r6h-eplus-real! 'x 'y)
        (r6h-ineq-close! '(IN x RR) '(IN y RR) '(<= 0 y)))
      (lambda ()
        (subst '(= y POS-INF))
        (r6h-eplus-inf-right! 'x)
        (fact 'rr-pos-star-below-pos-inf 'x)
        (ass))))
  (lambda ()
    (subst '(= x POS-INF))
    (r6h-eplus-inf-left! 'y)
    (r6h-pos-inf-facts! 'x)
    (ass)))
(qed 'eplus-le-left)
(topic! 'eplus-le-left 'analysis)

;;; -----------------------------------------------------------------------
;;; X8  eplus-mono:  eplus is monotone in both arguments.

(sp (make-wff
     '(FORALL x (FORALL y (FORALL u (FORALL v
        (IMPLIES (AND (IN x RR-POS-STAR)
                      (AND (IN y RR-POS-STAR) (AND (IN u RR-POS-STAR) (IN v RR-POS-STAR))))
          (IMPLIES (AND (<= x u) (<= y v))
            (<= (eplus x y) (eplus u v))))))))))
(dk-peel!)
(dk-split! '(AND (IN x RR-POS-STAR)
                 (AND (IN y RR-POS-STAR) (AND (IN u RR-POS-STAR) (IN v RR-POS-STAR)))))
(dk-split! '(AND (<= x u) (<= y v)))
(have! '(AND (IN x RR-POS-STAR) (IN y RR-POS-STAR)))
(fact 'eplus-closed 'x 'y)
(r6h-star-cases! 'u
  (lambda ()
    (dk-split! (r6h-real-case 'u))
    (r6h-star-cases! 'v
      (lambda ()
        (dk-split! (r6h-real-case 'v))
        (have! '(AND (IN x RR-POS-STAR) (IN u RR)))
        (fact 'rr-pos-star-le-real-in-rr 'x 'u)
        (have! '(AND (IN y RR-POS-STAR) (IN v RR)))
        (fact 'rr-pos-star-le-real-in-rr 'y 'v)
        (r6h-eplus-real! 'x 'y)
        (r6h-eplus-real! 'u 'v)
        (r6h-ineq-close! '(IN x RR) '(IN y RR) '(IN u RR) '(IN v RR)
                         '(<= x u) '(<= y v)))
      (lambda ()
        (subst '(= v POS-INF))
        (r6h-eplus-inf-right! 'u)
        (fact 'rr-pos-star-below-pos-inf '(eplus x y))
        (ass))))
  (lambda ()
    (subst '(= u POS-INF))
    (r6h-eplus-inf-left! 'v)
    (fact 'rr-pos-star-below-pos-inf '(eplus x y))
    (ass)))
(qed 'eplus-mono)
(topic! 'eplus-mono 'analysis)

;;; The block "ESUM: the finiteness dichotomy" (esum-bounded-implies-finite,
;;; esum-finite-iff-bounded) that closed this file until 2026-09-19 is now
;;; theorem-library/rake-esum-finite.scm.  ESUM became a DEFINED operator that day and its
;;; three laws are theorems of rake-esum-defined.scm, which needs THIS file's order laws
;;; (through rake-esup-defined) and rake-finsum-cm-ptwise; a block citing esum-* could
;;; not stay above them.
