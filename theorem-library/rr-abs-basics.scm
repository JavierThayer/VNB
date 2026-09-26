;;; rr-abs-basics.scm -- absolute value on RR, PROVEN from its DEFINITION.
;;;
;;; WHAT CHANGED, AND WHY IT WAS NOT MERELY AN OVERSIGHT.  Until 2026-08-17
;;; number-systems.scm characterised `abs' by five NORM-shaped axioms --
;;; rr-abs-closed, rr-abs-nonneg, rr-abs-zero, rr-abs-triangle, rr-abs-mult --
;;; and not one of them related |x| to x.  They say abs is *a* norm on the
;;; ordered field; they do not say WHICH one.  The map x |-> sqrt(|x|) satisfies
;;; all five (nonneg, vanishing only at 0, multiplicative, subadditive), so
;;; |2| = sqrt 2 was a model of the theory as stated.  Everything that pins |x|
;;; to one of x, -x -- x <= |x| (`rr-le-abs'), the two-sided bound
;;; (`rr-abs-bound'), the reverse triangle inequality -- was therefore
;;; INDEPENDENT of those axioms, not unproved, and each had been asserted as a
;;; `well-known' support in structure-library/order-lemmas.scm.  Its own header
;;; said so, and said that pinning |x| "needs an axiom the theory does not
;;; state".
;;;
;;; The missing statement is not an axiom but a DEFINITION.  number-systems.scm
;;; now carries `rr-abs-def',
;;;
;;;     forall x in RR.  (0 <= x  implies  |x| = x)
;;;                and   (not (0 <= x)  implies  |x| = -x)
;;;
;;; -- the textbook definition by cases, exhaustive and exclusive on a total
;;; order, hence a conservative definition and `primitive' provenance (that file
;;; is in load.scm's *primitive-files*).  This file cashes it: the five axioms
;;; are DELETED from number-systems.scm and PROVEN here `modulo 0', together
;;; with the three supports and the six order/algebra facts around them.
;;;
;;; THE MECHANISM, not bulk.  Every proof below is the same three moves:
;;;
;;;   1. `ab-sign-cases!' -- rr-leq-total at (0, v) gives 0 <= v or v <= 0, and
;;;      each branch lands the corresponding abs equation (rr-abs-of-nonneg /
;;;      rr-abs-of-nonpos).  The two branches OVERLAP at v = 0, which is exactly
;;;      why the case split needs no trichotomy and no `<': at 0 both equations
;;;      hold.
;;;   2. the abs equation makes |v| a LINEAR expression in v, so
;;;   3. `ineq' (Fourier-Motzkin over linear RR) closes the leaf.
;;;
;;; Nothing here needs `rr-no-zero-divisors' or any nonlinear reasoning -- not
;;; even multiplicativity, whose four sign branches each reduce the product's
;;; sign to rr-leq-mul-nonneg at a negated argument, land the third abs
;;; equation, and finish with `crs' on a ring identity.  (Contrast the old proof
;;; of rr-abs-neg in rr-order-basics.scm, which could only get |-a| = |a| out of
;;; the axioms through |a|^2 = |-a|^2 and a difference-of-squares zero-divisor
;;; argument.  With the definition it is four lines.)
;;;
;;; WHERE THE STATEMENTS CAME FROM.  Five were axioms in number-systems.scm;
;;; three were supports in structure-library/order-lemmas.scm (rr-le-abs,
;;; rr-abs-bound, rr-abs-reverse-triangle); one more, `rr-le-abs-self', was a
;;; verbatim duplicate of rr-le-abs declared with `add-to-pss' INSIDE
;;; theorem-library/vector-taylor-proof.scm -- the species of hiding place the
;;; header of rr-order-basics.scm describes.  All are deleted at their old
;;; homes.  Three (rr-abs-neg, rr-abs-triangle-c, rr-abs-sub-sym) MOVED here
;;; from rr-order-basics.scm, which proved them from the axioms this file
;;; replaces and must therefore no longer mention abs at all.
;;;
;;; LOAD POSITION.  Immediately after theorem-library/rr-order-basics, whose
;;; rr-lt-implies-le this file cites, and before every consumer of abs: the
;;; earliest is theorem-library/rr-metric-space-proof (RR as a metric space,
;;; whose distance IS abs of the difference).

;;; --------------------------------------------------------------------
;;; File-local driver helpers (the `ab-' prefix -- never named like a tactic;
;;; see the case-fold section of the working brief).

;;; The body of rr-abs-def at the eigenvariable `x', which `fact' lands as ONE
;;; conjunction and `dk-split!' takes apart.
(define ab-def-and
  '(AND (IMPLIES (<= 0 x) (= (abs x) x))
        (IMPLIES (NOT (<= 0 x)) (= (abs x) (- x)))))

;;; Peel the whole FORALL/IMPLIES prefix.  `di' is greedy WITHIN one binder
;;; level but stops at the next, so a guarded FORALL followed by an implication
;;; takes two calls.  Guarded on the head AND on a fuel count: `di' only WARNS
;;; when it cannot decompose, so a head test alone spins forever on a no-op.
(define (ab-peel!)
  (let loop ((n 0))
    (let ((g (dk-goal)))
      (if (and (pair? g) (memq (car g) '(FORALL IMPLIES)) (< n 12))
          (begin (di) (loop (+ n 1)))
          #t))))

;;; `ai' every conjunction in the context, to exhaustion.  Note this REPLACES
;;; the conjunction by its conjuncts, so a later `fact' whose antecedent is that
;;; same AND (rr-add-closed, rr-mul-closed) needs it `have!'d back.
(define (ab-split!)
  (let loop ((l (dk-asms)) (n 0))
    (cond ((or (null? l) (> n 12)) #t)
          ((and (pair? (car l)) (eq? (caar l) 'AND))
           (ai (car l)) (loop (dk-asms) (+ n 1)))
          (else (loop (cdr l) n)))))

;;; The 1-based indices of the ORDER-SHAPED assumptions, which is what `ineq'
;;; wants.  Every context equation in this file is between reals (or between abs
;;; terms, which ineq-atom-rr-ok? certifies on sight), so the shape test is the
;;; right filter here; `contra--usable-indices' (contra.scm) is the general
;;; version, which asks the oracle itself.
(define (ab-idx)
  (let loop ((l (dk-asms)) (i 1) (acc '()))
    (cond ((null? l) (reverse acc))
          ((and (pair? (car l)) (memq (caar l) '(< <= =)))
           (loop (cdr l) (+ i 1) (cons i acc)))
          (else (loop (cdr l) (+ i 1) acc)))))

(define (ab-ineq!) (apply ineq (ab-idx)))

;;; peel, then decide -- splitting a conjunctive GOAL into its conjuncts and a
;;; conjunctive HYPOTHESIS into its own (the oracle reads neither).
(define (ab-finish!)
  (ab-peel!)
  (let ((g (dk-goal)))
    (if (and (pair? g) (eq? (car g) 'AND))
        (for-each (lambda (k) (dk-focus! k) (ab-finish!)) (dk-opened (lambda () (di))))
        (begin (ab-split!) (ab-ineq!)))))

;;; An IFF goal: `di' is iff-intro, opening one leaf per direction.
(define (ab-iff!)
  (for-each (lambda (k) (dk-focus! k) (ab-finish!)) (dk-opened (lambda () (di)))))

;;; --------------------------------------------------------------------
;;; THE TWO HALVES OF THE DEFINITION, as citable conditional equations.
;;;
;;; rr-abs-def is one conjunction under one guard, which is the right shape for
;;; a definition and the wrong one for a citation: every caller would `fact' it,
;;; `ai' it and `detach!' the branch.  These two do that once.  They are also
;;; the pair that makes `mac' usable -- each has a bare `abs(x)' on the left of
;;; an equation, so it is a conditional rewrite whose side condition the context
;;; discharges.

;;; |x| = x  for  0 <= x.
(sp (make-wff '(FORALL x (IMPLIES (IN x RR) (IMPLIES (<= 0 x) (= (abs x) x))))))
(ab-peel!)
(fact 'rr-abs-def 'x)
(dk-split! ab-def-and)
(detach! '(IMPLIES (<= 0 x) (= (abs x) x)))
(ass)
(qed 'rr-abs-of-nonneg)
(topic! 'rr-abs-of-nonneg 'inequalities)

;;; |x| = -x  for  x <= 0.  NOT the second conjunct of the definition, whose
;;; guard is `not (0 <= x)': the two disagree exactly at x = 0, where this one
;;; still has to be proved.  It is, from the FIRST conjunct -- 0 <= x and x <= 0
;;; give x = 0 by antisymmetry, and then |x| = x = 0 = -x is linear.
(sp (make-wff '(FORALL x (IMPLIES (IN x RR) (IMPLIES (<= x 0) (= (abs x) (- x)))))))
(ab-peel!)
(fact 'rr-abs-def 'x)
(dk-split! ab-def-and)
(use-em '(<= 0 x)
  (lambda ()
    (detach! '(IMPLIES (<= 0 x) (= (abs x) x)))
    (have! '(AND (IN 0 RR) (IN x RR)))
    (have! '(AND (<= 0 x) (<= x 0)))
    (fact 'rr-leq-antisymmetric 0 'x)
    (ab-ineq!))
  (lambda ()
    (detach! '(IMPLIES (NOT (<= 0 x)) (= (abs x) (- x))))
    (ass)))
(qed 'rr-abs-of-nonpos)
(topic! 'rr-abs-of-nonpos 'inequalities)

;;; The case split every proof below runs on.  rr-leq-total at (0, v) is
;;; exhaustive, the two branches overlap at v = 0, and each lands the abs
;;; equation for its sign -- so no trichotomy and no `<' is needed anywhere.
(define (ab-sign-cases! v pos neg)
  (have! (list 'AND (list 'IN 0 'RR) (list 'IN v 'RR)))
  (fact 'rr-leq-total 0 v)
  (use-cases (list (list '<= 0 v) (list '<= v 0))
    (lambda () (fact 'rr-abs-of-nonneg v) (pos))
    (lambda () (fact 'rr-abs-of-nonpos v) (neg))))

;;; |x| = -x for x STRICTLY negative -- the form a reader expects, and one
;;; weakening (rr-lt-implies-le) away from the one above.
(sp (make-wff '(FORALL x (IMPLIES (IN x RR) (IMPLIES (< x 0) (= (abs x) (- x)))))))
(ab-peel!)
(have! '(IN 0 RR))
(fact 'rr-lt-implies-le 'x 0)
(fact 'rr-abs-of-nonpos 'x)
(ass)
(qed 'rr-abs-of-neg)
(topic! 'rr-abs-of-neg 'inequalities)

;;; The definition read as a disjunction: |x| is x or -x, with the sign that
;;; made it so.  Pure propositional repackaging of rr-abs-def, so `prop' closes
;;; it outright once the conjunction is split.
(sp (make-wff '(FORALL x (IMPLIES (IN x RR)
      (OR (AND (<= 0 x) (= (abs x) x))
          (AND (NOT (<= 0 x)) (= (abs x) (- x))))))))
(ab-peel!)
(fact 'rr-abs-def 'x)
(dk-split! ab-def-and)
(prop)
(qed 'rr-abs-cases)
(topic! 'rr-abs-cases 'inequalities)

;;; --------------------------------------------------------------------
;;; THE FIVE THAT WERE AXIOMS.  Each was `add-axiom!' in
;;; number-systems.scm until 2026-08-17 and is deleted there.

;;; abs lands in RR.  `subst' the abs equation into the typing goal; in the
;;; negative branch rr-neg-closed supplies the rest.
(sp (make-wff '(FORALL a (IMPLIES (IN a RR) (IN (abs a) RR)))))
(ab-peel!)
(ab-sign-cases! 'a
  (lambda () (subst '(= (abs a) a)) (ass))
  (lambda () (subst '(= (abs a) (- a))) (fact 'rr-neg-closed 'a) (ass)))
(qed 'rr-abs-closed)
(topic! 'rr-abs-closed 'inequalities)

;;; 0 <= |a|.
(sp (make-wff '(FORALL a (IMPLIES (IN a RR) (<= 0 (abs a))))))
(ab-peel!)
(ab-sign-cases! 'a (lambda () (ab-ineq!)) (lambda () (ab-ineq!)))
(qed 'rr-abs-nonneg)
(topic! 'rr-abs-nonneg 'inequalities)

;;; |a| = 0 iff a = 0.
(sp (make-wff '(FORALL a (IMPLIES (IN a RR) (IFF (= (abs a) 0) (= a 0))))))
(ab-peel!)
(ab-sign-cases! 'a (lambda () (ab-iff!)) (lambda () (ab-iff!)))
(qed 'rr-abs-zero)
(topic! 'rr-abs-zero 'inequalities)

;;; --------------------------------------------------------------------
;;; THE TWO-SIDED BOUNDS.  These are the facts the axioms could not deliver,
;;; and they are what makes the triangle inequality linear below.

;;; x <= |x|.  (Was `rr-le-abs', a well-known support in order-lemmas.scm, and
;;; separately `rr-le-abs-self' inside vector-taylor-proof.scm.)
(sp (make-wff '(FORALL x (IMPLIES (IN x RR) (<= x (abs x))))))
(ab-peel!)
(ab-sign-cases! 'x (lambda () (ab-ineq!)) (lambda () (ab-ineq!)))
(qed 'rr-le-abs)
(topic! 'rr-le-abs 'inequalities)

;;; -|x| <= x -- the other side, and new.  With rr-le-abs it says
;;; -|x| <= x <= |x|, which is the whole content of the triangle inequality.
(sp (make-wff '(FORALL x (IMPLIES (IN x RR) (<= (- (abs x)) x)))))
(ab-peel!)
(ab-sign-cases! 'x (lambda () (ab-ineq!)) (lambda () (ab-ineq!)))
(qed 'rr-neg-abs-le)
(topic! 'rr-neg-abs-le 'inequalities)

;;; |x| <= c  iff  -c <= x <= c.  (Was `rr-abs-bound' in order-lemmas.scm.)  The
;;; form every continuity/limit argument uses to turn an absolute-value bound
;;; into a pair of linear ones; rr-complete-proof cites it five times.
(sp (make-wff '(FORALL x (IMPLIES (IN x RR) (FORALL c (IMPLIES (IN c RR)
     (IFF (<= (abs x) c)
          (AND (<= (- c) x) (<= x c)))))))))
(ab-peel!)
(ab-sign-cases! 'x (lambda () (ab-iff!)) (lambda () (ab-iff!)))
(qed 'rr-abs-bound)
(topic! 'rr-abs-bound 'inequalities)

;;; --------------------------------------------------------------------
;;; THE TRIANGLE INEQUALITY, and its curried sibling.

;;; |a+b| <= |a| + |b|.  Linear: -|a| <= a <= |a|, -|b| <= b <= |b|, and |a+b|
;;; is +-(a+b) by the sign split -- so the oracle does the rest in both
;;; branches.  Nothing in the argument is special to abs.
(sp (make-wff '(FORALL a (FORALL b
      (IMPLIES (AND (IN a RR) (IN b RR))
               (<= (abs (+ a b)) (+ (abs a) (abs b))))))))
(ab-peel!)
(ab-split!)
(fact 'rr-le-abs 'a)
(fact 'rr-neg-abs-le 'a)
(fact 'rr-le-abs 'b)
(fact 'rr-neg-abs-le 'b)
(have! '(AND (IN a RR) (IN b RR)))
(fact 'rr-add-closed 'a 'b)
(ab-sign-cases! '(+ a b) (lambda () (ab-ineq!)) (lambda () (ab-ineq!)))
(qed 'rr-abs-triangle)
(topic! 'rr-abs-triangle 'inequalities)

;;; The triangle inequality, CURRIED.  rr-abs-triangle states its two typings as
;;; one AND, which `fact' will not split, so every caller has to assemble the
;;; conjunction by hand with `have!' -- and `have!' ERRORS when the same
;;; conjunction is already proved under the same context, the kernel having
;;; hash-consed that sequent node.  A curried statement removes the occasion.
;;; Same shape and same reason as fun-apply-type-c.  (MOVED from
;;; theorem-library/rr-order-basics.scm, where it stood on the deleted axiom.)
(sp (make-wff (forall-guarded '(a b) (list '(IN a RR) '(IN b RR))
                '(<= (abs (+ a b)) (+ (abs a) (abs b))))))
(ab-peel!)
(have! '(AND (IN a RR) (IN b RR)))
(fact 'rr-abs-triangle 'a 'b)
(ass)
(qed 'rr-abs-triangle-c)
(topic! 'rr-abs-triangle-c 'inequalities)

;;; --------------------------------------------------------------------
;;; EVENNESS, and the one instance every metric uses.  Both MOVED from
;;; theorem-library/rr-order-basics.scm.

;;; |-a| = |a|.  The old proof needed multiplicativity, a ring identity, a
;;; difference of squares and rr-no-zero-divisors, because evenness was the ONLY
;;; sign fact the axioms could reach.  From the definition: in each branch the
;;; other one applies to -a, and both equations are linear.
(sp (make-wff (forall-guarded 'a '(IN a RR) '(= (abs (- a)) (abs a)))))
(ab-peel!)
(fact 'rr-neg-closed 'a)
(ab-sign-cases! 'a
  (lambda () (have! '(<= (- a) 0) (lambda () (ab-ineq!)))
             (fact 'rr-abs-of-nonpos '(- a))
             (ab-ineq!))
  (lambda () (have! '(<= 0 (- a)) (lambda () (ab-ineq!)))
             (fact 'rr-abs-of-nonneg '(- a))
             (ab-ineq!)))
(qed 'rr-abs-neg)
(topic! 'rr-abs-neg 'inequalities)

;;; |u - v| = |v - u| -- evenness at the one argument every metric uses.
(sp (make-wff (forall-guarded '(u v) (list '(IN u RR) '(IN v RR))
                '(= (abs (- u v)) (abs (- v u))))))
(ab-peel!)
(have! '(AND (IN v RR) (IN u RR)))
(fact 'rr-sub-in-rr 'v 'u)
(fact 'rr-abs-neg '(- v u))
(have! '(= (- u v) (- (- v u))) (lambda () (crs)))
(subst '(= (- u v) (- (- v u))))
(ass)
(qed 'rr-abs-sub-sym)
(topic! 'rr-abs-sub-sym 'inequalities)

;;; --------------------------------------------------------------------
;;; MULTIPLICATIVITY.  The one proof here with four branches, and the only place
;;; the ring simplifier is needed.
;;;
;;; In each branch the sign of the PRODUCT is reduced to rr-leq-mul-nonneg at
;;; negated arguments -- 0 <= a and b <= 0 give 0 <= a*(-b) = -(a*b), hence
;;; a*b <= 0, which is linear in the two product ATOMS once `crs' has supplied
;;; the identity relating them.  With the product's sign known, its abs equation
;;; lands, all three abs terms are substituted out of the goal, and what remains
;;; is a ring identity.
(sp (make-wff '(FORALL a (FORALL b
      (IMPLIES (AND (IN a RR) (IN b RR))
               (= (abs (* a b)) (* (abs a) (abs b))))))))
(ab-peel!)
(ab-split!)
(have! '(AND (IN a RR) (IN b RR)))
(fact 'rr-mul-closed 'a 'b)
(ab-sign-cases! 'a
  (lambda ()
    (ab-sign-cases! 'b
      (lambda ()                                  ; 0 <= a, 0 <= b
        (have! '(AND (<= 0 a) (<= 0 b)))
        (fact 'rr-leq-mul-nonneg 'a 'b)
        (fact 'rr-abs-of-nonneg '(* a b))
        (subst '(= (abs a) a))
        (subst '(= (abs b) b))
        (subst '(= (abs (* a b)) (* a b)))
        (rfl))
      (lambda ()                                  ; 0 <= a, b <= 0
        (fact 'rr-neg-closed 'b)
        (have! '(<= 0 (- b)) (lambda () (ab-ineq!)))
        (have! '(AND (IN a RR) (IN (- b) RR)))
        (have! '(AND (<= 0 a) (<= 0 (- b))))
        (fact 'rr-leq-mul-nonneg 'a '(- b))
        (fact 'rr-mul-closed 'a '(- b))
        (have! '(= (* a (- b)) (- (* a b))) (lambda () (crs)))
        (have! '(<= (* a b) 0) (lambda () (ab-ineq!)))
        (fact 'rr-abs-of-nonpos '(* a b))
        (subst '(= (abs a) a))
        (subst '(= (abs b) (- b)))
        (subst '(= (abs (* a b)) (- (* a b))))
        (crs))))
  (lambda ()
    (ab-sign-cases! 'b
      (lambda ()                                  ; a <= 0, 0 <= b
        (fact 'rr-neg-closed 'a)
        (have! '(<= 0 (- a)) (lambda () (ab-ineq!)))
        (have! '(AND (IN (- a) RR) (IN b RR)))
        (have! '(AND (<= 0 (- a)) (<= 0 b)))
        (fact 'rr-leq-mul-nonneg '(- a) 'b)
        (fact 'rr-mul-closed '(- a) 'b)
        (have! '(= (* (- a) b) (- (* a b))) (lambda () (crs)))
        (have! '(<= (* a b) 0) (lambda () (ab-ineq!)))
        (fact 'rr-abs-of-nonpos '(* a b))
        (subst '(= (abs a) (- a)))
        (subst '(= (abs b) b))
        (subst '(= (abs (* a b)) (- (* a b))))
        (crs))
      (lambda ()                                  ; a <= 0, b <= 0
        (fact 'rr-neg-closed 'a)
        (fact 'rr-neg-closed 'b)
        (have! '(<= 0 (- a)) (lambda () (ab-ineq!)))
        (have! '(<= 0 (- b)) (lambda () (ab-ineq!)))
        (have! '(AND (IN (- a) RR) (IN (- b) RR)))
        (have! '(AND (<= 0 (- a)) (<= 0 (- b))))
        (fact 'rr-leq-mul-nonneg '(- a) '(- b))
        (fact 'rr-mul-closed '(- a) '(- b))
        (have! '(= (* (- a) (- b)) (* a b)) (lambda () (crs)))
        (have! '(<= 0 (* a b)) (lambda () (ab-ineq!)))
        (fact 'rr-abs-of-nonneg '(* a b))
        (subst '(= (abs a) (- a)))
        (subst '(= (abs b) (- b)))
        (subst '(= (abs (* a b)) (* a b)))
        (crs)))))
(qed 'rr-abs-mult)
(topic! 'rr-abs-mult 'inequalities)

;;; --------------------------------------------------------------------
;;; THE REVERSE TRIANGLE INEQUALITY.  (Was `rr-abs-reverse-triangle', a
;;; well-known support in order-lemmas.scm.)
;;;
;;; |x| <= |x-y| + |y| and |y| <= |y-x| + |x| are the triangle inequality at
;;; (x-y) + y = x and (y-x) + x = y.  The rewriting is done OUTSIDE the abs --
;;; `crs' proves (x-y)+y = x, Leibniz lifts it to |(x-y)+y| = |x|, and the
;;; oracle chains that equation with the inequality rather than rewriting the
;;; hypothesis.  With rr-abs-sub-sym identifying |y-x| and |x-y| the two bounds
;;; say -|x-y| <= |x|-|y| <= |x-y|, and the sign split on |x|-|y| finishes it.
(sp (make-wff '(FORALL x (IMPLIES (IN x RR) (FORALL y (IMPLIES (IN y RR)
     (<= (abs (- (abs x) (abs y))) (abs (- x y)))))))))
(ab-peel!)
(fact 'rr-abs-closed 'x)
(fact 'rr-abs-closed 'y)
(fact 'rr-sub-in-rr 'x 'y)
(fact 'rr-sub-in-rr 'y 'x)
(fact 'rr-sub-in-rr '(abs x) '(abs y))
(fact 'rr-abs-triangle-c '(- x y) 'y)
(have! '(= (+ (- x y) y) x) (lambda () (crs)))
(have! '(= (abs (+ (- x y) y)) (abs x))
       (lambda () (subst '(= (+ (- x y) y) x)) (rfl)))
(fact 'rr-abs-triangle-c '(- y x) 'x)
(have! '(= (+ (- y x) x) y) (lambda () (crs)))
(have! '(= (abs (+ (- y x) x)) (abs y))
       (lambda () (subst '(= (+ (- y x) x) y)) (rfl)))
(fact 'rr-abs-sub-sym 'y 'x)
(ab-sign-cases! '(- (abs x) (abs y)) (lambda () (ab-ineq!)) (lambda () (ab-ineq!)))
(qed 'rr-abs-reverse-triangle)
(topic! 'rr-abs-reverse-triangle 'inequalities)

;;; --------------------------------------------------------------------
;;; THE eps/2 ESTIMATE, once and for all.
;;;
;;;   |u - p| <= h,  |v - q| <= h,  h + h = e   =>   |(u+v) - (p+q)| <= e
;;;
;;; This is the mathematical heart of `sum-continuous-at'
;;; (theorem-library/continuity-sum.scm): once the lambda plumbing is out of the
;;; way, the eps/2 argument for the sum of two maps continuous at a point comes
;;; down to this inequality and nothing else -- u, v are the values of the two
;;; maps at the moving point, p, q their values at the base point, and h is the
;;; half of eps each is within.  It is stated here rather than there because it
;;; is a fact about `abs' and has nothing to do with continuity; every eps/2
;;; split of a SUM wants exactly this.
;;;
;;; It is NOT the triangle inequality specialised, and that is why it is cheap:
;;; `rr-abs-bound' opens both hypotheses and the goal into pairs of LINEAR
;;; bounds -- -h <= u-p <= h and so on -- and (u+v)-(p+q) = (u-p) + (v-q) is
;;; linear too, so Farkas decides both halves.  The two-sided opening is done
;;; here by rr-le-abs / rr-neg-abs-le on the hypothesis side (which leaves the
;;; abs terms as ATOMS the oracle can certify with rr-abs-closed) and by `mac'
;;; with rr-abs-bound on the goal side, where the abs has to disappear.
(sp (make-wff (forall-guarded '(u v p q h_ e)
      (list '(IN u RR) '(IN v RR) '(IN p RR) '(IN q RR) '(IN h_ RR) '(IN e RR))
      '(IMPLIES (AND (AND (<= (abs (- u p)) h_) (<= (abs (- v q)) h_))
                     (= (+ h_ h_) e))
                (<= (abs (- (+ u v) (+ p q))) e)))))
(ab-peel!)
(ab-split!)
(fact 'rr-sub-in-rr 'u 'p)
(fact 'rr-sub-in-rr 'v 'q)
(have! '(AND (IN u RR) (IN v RR)))
(fact 'rr-add-closed 'u 'v)
(have! '(AND (IN p RR) (IN q RR)))
(fact 'rr-add-closed 'p 'q)
(fact 'rr-sub-in-rr '(+ u v) '(+ p q))
;; the two abs terms are atoms to the oracle, so each needs its RR certificate
(fact 'rr-abs-closed '(- u p))
(fact 'rr-abs-closed '(- v q))
;; ... and the two-sided bounds that relate each atom to its argument
(fact 'rr-le-abs '(- u p))
(fact 'rr-neg-abs-le '(- u p))
(fact 'rr-le-abs '(- v q))
(fact 'rr-neg-abs-le '(- v q))
(mac 'rr-abs-bound)
(ab-finish!)
(qed 'rr-abs-sum-bound)
(topic! 'rr-abs-sum-bound 'inequalities)
(alias! 'rr-abs-sum-bound "the eps/2 estimate for a sum")

;;; --------------------------------------------------------------------
;;; THE PRODUCT ESTIMATE, the same way.
;;;
;;;   |u| <= m,  |q| <= k,  |u-p| <= t,  |v-q| <= t,  (m+k)*t <= e
;;;      =>   |u*v - p*q| <= e
;;;
;;; The companion of rr-abs-sum-bound, and the heart of
;;; `product-continuous-at' (theorem-library/continuity-product.scm): u, v are
;;; the values of the two maps at one point, p, q their values at the other, m
;;; bounds the first factor and k the second, and t is the common closeness.
;;; The dissymmetry -- |u| and |q|, not |u| and |v| -- is not an accident: it is
;;; the pairing the identity below forces, and it is why a product argument has
;;; to bound ONE of the four values, hence why it needs a preliminary
;;; continuity step at eps = 1 where a sum argument needs none.
;;;
;;; The whole of it is one ring identity,
;;;
;;;     u*v - p*q  =  u*(v-q) + q*(u-p)             (`crs')
;;;
;;; the triangle inequality on that sum, `rr-abs-mult' to break each |product|
;;; into a product of absolute values, and `rr-prod-le-prod'
;;; (theorem-library/rr-order-basics.scm) twice -- which is exactly the step
;;; `ineq' cannot take, a product of two VARIABLES not being linear.  With
;;; |u|*|v-q| <= m*t and |q|*|u-p| <= k*t in hand, and (m+k)*t = m*t + k*t from
;;; `crs', the chain to e is linear again and Farkas closes it.
;;;
;;; Every atom the oracle sees needs its own (IN _ RR) certificate, which is
;;; what the long typing block is: |u|, |q|, |u-p|, |v-q|, the two products,
;;; their sum, u*v, p*q, m*t, k*t and (m+k)*t are eleven distinct atoms.
(sp (make-wff (forall-guarded '(u v p q m k t e)
      (list '(IN u RR) '(IN v RR) '(IN p RR) '(IN q RR)
            '(IN m RR) '(IN k RR) '(IN t RR) '(IN e RR))
      '(IMPLIES (AND (AND (AND (<= (abs u) m) (<= (abs q) k))
                          (AND (<= (abs (- u p)) t) (<= (abs (- v q)) t)))
                     (<= (* (+ m k) t) e))
                (<= (abs (- (* u v) (* p q))) e)))))
(ab-peel!)
(ab-split!)
(fact 'rr-sub-in-rr 'u 'p)
(fact 'rr-sub-in-rr 'v 'q)
;; rr-mul-closed and rr-abs-mult guard on the SAME conjunction, so they are
;; cited together: `have!' errors on a conjunction already proved under the
;; same context, and re-assembling it later is that error.
(have! '(AND (IN u RR) (IN (- v q) RR)))
(fact 'rr-mul-closed 'u '(- v q))
(fact 'rr-abs-mult 'u '(- v q))
(have! '(AND (IN q RR) (IN (- u p) RR)))
(fact 'rr-mul-closed 'q '(- u p))
(fact 'rr-abs-mult 'q '(- u p))
(have! '(AND (IN (* u (- v q)) RR) (IN (* q (- u p)) RR)))
(fact 'rr-add-closed '(* u (- v q)) '(* q (- u p)))
(fact 'rr-abs-triangle-c '(* u (- v q)) '(* q (- u p)))
(have! '(AND (IN u RR) (IN v RR)))
(fact 'rr-mul-closed 'u 'v)
(have! '(AND (IN p RR) (IN q RR)))
(fact 'rr-mul-closed 'p 'q)
(fact 'rr-abs-closed 'u)
(fact 'rr-abs-closed 'q)
(fact 'rr-abs-closed '(- u p))
(fact 'rr-abs-closed '(- v q))
(fact 'rr-abs-closed '(* u (- v q)))
(fact 'rr-abs-closed '(* q (- u p)))
(fact 'rr-abs-closed '(+ (* u (- v q)) (* q (- u p))))
(fact 'rr-abs-nonneg 'u)
(fact 'rr-abs-nonneg 'q)
(fact 'rr-abs-nonneg '(- u p))
(fact 'rr-abs-nonneg '(- v q))
(have! '(AND (AND (<= 0 (abs u)) (<= (abs u) m))
             (AND (<= 0 (abs (- v q))) (<= (abs (- v q)) t))))
(fact 'rr-prod-le-prod '(abs u) 'm '(abs (- v q)) 't)
(have! '(AND (AND (<= 0 (abs q)) (<= (abs q) k))
             (AND (<= 0 (abs (- u p))) (<= (abs (- u p)) t))))
(fact 'rr-prod-le-prod '(abs q) 'k '(abs (- u p)) 't)
(have! '(AND (IN m RR) (IN k RR)))
(fact 'rr-add-closed 'm 'k)
(have! '(AND (IN m RR) (IN t RR)))
(fact 'rr-mul-closed 'm 't)
(have! '(AND (IN k RR) (IN t RR)))
(fact 'rr-mul-closed 'k 't)
(have! '(AND (IN (+ m k) RR) (IN t RR)))
(fact 'rr-mul-closed '(+ m k) 't)
(have! '(AND (IN (abs u) RR) (IN (abs (- v q)) RR)))
(fact 'rr-mul-closed '(abs u) '(abs (- v q)))
(have! '(AND (IN (abs q) RR) (IN (abs (- u p)) RR)))
(fact 'rr-mul-closed '(abs q) '(abs (- u p)))
(have! '(= (* (+ m k) t) (+ (* m t) (* k t))) (lambda () (crs)))
(have! '(= (- (* u v) (* p q)) (+ (* u (- v q)) (* q (- u p)))) (lambda () (crs)))
(subst '(= (- (* u v) (* p q)) (+ (* u (- v q)) (* q (- u p)))))
(ab-ineq!)
(qed 'rr-abs-prod-bound)
(topic! 'rr-abs-prod-bound 'inequalities)
(alias! 'rr-abs-prod-bound "the eps/2 estimate for a product")
