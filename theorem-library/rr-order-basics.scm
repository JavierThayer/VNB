;;; rr-order-basics.scm -- the elementary RR order facts, PROVEN.
;;;
;;; WHY THESE WERE ASSERTABLE AND ARE NOW PROVABLE.  Every one of these was a
;;; warranted PSS support in structure-library/order-lemmas.scm, whose own header
;;; called them "one- or two-step consequences of the axioms, recorded so proofs
;;; (and the future inequality decision procedure) can lean on them by name".
;;; Two things have since happened that turn that sentence around:
;;;
;;;   * the inequality decision procedure EXISTS (structure-library/ineq-oracle.scm,
;;;     Fourier-Motzkin/Farkas over linear RR), and it reads `<' natively -- so the
;;;     facts that were its SPECIFICATION are now its OUTPUT;
;;;   * number-systems.scm became `primitive' on 2026-08-01 (load.scm's
;;;     *primitive-files*), so the ZZ/QQ/RR field and order axioms these rest on
;;;     contribute {} to every bill.  A proof from them is `modulo 0'; the
;;;     assertion they replaced was `well-known' debt.
;;;
;;; theorem-library/rr-recip-order.scm said exactly this in its own header --
;;; "the rr-lt-* lemmas -- scale-pos, trichotomy, trans, implies-le, add,
;;; diff-pos/neg -- are the remaining elementary loose ends on the strict order,
;;; and each of them is derivable from the ordered-field axioms" -- and named the
;;; work without doing it.  This file does it.
;;;
;;; THE MECHANISM, not bulk.  Twenty of the twenty-nine theorems below are ONE
;;; call to `ineq' after the binders are peeled and any conjunctive antecedent is
;;; split (`ro-farkas!'): `<' is `lt' to the oracle (ineq-rel-of,
;;; ineq-oracle.scm:71) and every atom is an RR-typed eigenvariable, so Farkas
;;; decides them.  Three more are not order relations at all -- rr-sub-ne-zero
;;; and rr-pos-ne-zero (a NOT goal), rr-le-cases / rr-le-ne-lt / rr-lt-trichotomy
;;; (a disjunctive goal) -- and each of those goes through the DEFINITION of `<'
;;; (order-predicates.scm: x<y iff x<=y and x/=y), unfolded with `mac' in the
;;; goal or `mac-h' in an assumption.
;;;
;;; The rest are NONLINEAR, and they all turn on ONE new lemma:
;;; `rr-no-zero-divisors', proved here from rr-recip-closed / rr-recip-inverse.
;;; What the strict scaling law, the cancellation law and the evenness of abs
;;; need is not a further order axiom but the fact that RR is a FIELD.
;;;
;;; WHERE THE STATEMENTS CAME FROM.  Twenty were supports in order-lemmas.scm,
;;; deleted there in the same change.  Four were declared with `add-to-pss'
;;; INSIDE calculus proof files -- rr-le-cases and rr-le-ne-lt in rolle-proof.scm,
;;; rr-diff-zero-eq in mvt-proof.scm, rr-pos-ne-zero in taylor-proof.scm -- which
;;; is the species of hiding place that also concealed rr-lt-trichotomy in
;;; deriv-constant-proof.scm until 2026-08-04: a fact stated inside a proof is
;;; invisible to everything that loads before it.  Those declarations are deleted
;;; too; the theorems are here, where the whole library can see them.  The
;;; remaining five (rr-no-zero-divisors, rr-abs-neg, rr-abs-sub-sym,
;;; rr-abs-triangle-c, and the curried rr-le-ne-lt) are new names, and exist
;;; because theorem-library/rr-metric-space-proof.scm needs them.
;;;
;;; LOAD POSITION.  After interactive/proof-debt (sp/di/mac/fact/qed), after
;;; driver-kit, after the ineq oracle -- and BEFORE the earliest citer, which is
;;; theorem-library/rr-recip-order (rr-lt-trichotomy), with compact-separable-proof
;;; (rr-lt-trans) and the whole calculus arc further down.

;;; --------------------------------------------------------------------
;;; File-local driver helpers (the `ro-' prefix -- never named like a tactic;
;;; see the case-fold section of the working brief).

;;; Peel the whole FORALL/IMPLIES prefix.  `di' is greedy WITHIN one binder level
;;; but stops at the next, so a guarded FORALL followed by an implication takes
;;; two calls.  Guarded on the head AND on a fuel count: `di' only WARNS when it
;;; cannot decompose, so a head test alone spins forever on a no-op.
(define (ro-peel!)
  (let loop ((n 0))
    (let ((g (dk-goal)))
      (if (and (pair? g) (memq (car g) '(FORALL IMPLIES)) (< n 12))
          (begin (di) (loop (+ n 1)))
          #t))))

;;; `ai' every conjunction in the context, to exhaustion.  `fact' will not split
;;; a conjunctive antecedent and neither will `di', so a hypothesis stated as
;;; (AND (< x y) (< y z)) reaches the oracle only after this.
(define (ro-split!)
  (let loop ((l (dk-asms)) (n 0))
    (cond ((or (null? l) (> n 12)) #t)
          ((and (pair? (car l)) (eq? (caar l) 'AND))
           (ai (car l)) (loop (dk-asms) (+ n 1)))
          (else (loop (cdr l) n)))))

;;; The 1-based indices of the ORDER-SHAPED assumptions, which is what `ineq'
;;; wants.  Naming the typings as well would be harmless since 2026-08-15 (a
;;; non-arithmetic premise is skipped rather than fatal, ineq-oracle.scm), but
;;; naming an EQUATION between non-arithmetic terms is not: an `=' is arithmetic
;;; in SHAPE, so it contributes atoms that can never be certified in RR and
;;; poisons the whole call.  Here every context equation is between reals, so the
;;; shape test is the right filter; `contra--usable-indices' (contra.scm) is the
;;; general version, which asks the oracle itself.
(define (ro-idx)
  (let loop ((l (dk-asms)) (i 1) (acc '()))
    (cond ((null? l) (reverse acc))
          ((and (pair? (car l)) (memq (caar l) '(< <= =)))
           (loop (cdr l) (+ i 1) (cons i acc)))
          (else (loop (cdr l) (+ i 1) acc)))))

(define (ro-ineq!) (apply ineq (ro-idx)))

;;; peel, split, decide -- the shape of eleven of the thirteen proofs below.
(define (ro-farkas!) (ro-peel!) (ro-split!) (ro-ineq!))

;;; Close every leaf a branching tactic just opened by `ass'.  Used on an AND
;;; goal whose conjuncts are all in context (the two halves of an unfolded `<').
(define (ro-ass-opened! thunk)
  (for-each (lambda (k) (dk-focus! k) (ass)) (dk-opened thunk)))

;;; --------------------------------------------------------------------
;;; CHAINING: strict transitivity, and the two mixed forms.
;;;
;;; The primitive is rr-leq-transitive, on `<=' and with an AND antecedent.  The
;;; oracle needs neither: it takes the strict and non-strict premises together
;;; and returns a Farkas certificate.

(sp (make-wff '(FORALL x (IMPLIES (IN x RR) (FORALL y (IMPLIES (IN y RR)
     (FORALL z (IMPLIES (IN z RR)
       (IMPLIES (AND (< x y) (< y z)) (< x z))))))))))
(ro-farkas!)
(qed 'rr-lt-trans)
(topic! 'rr-lt-trans 'inequalities)

(sp (make-wff '(FORALL x (IMPLIES (IN x RR) (FORALL y (IMPLIES (IN y RR)
     (FORALL z (IMPLIES (IN z RR)
       (IMPLIES (AND (< x y) (<= y z)) (< x z))))))))))
(ro-farkas!)
(qed 'rr-lt-le-trans)
(topic! 'rr-lt-le-trans 'inequalities)

(sp (make-wff '(FORALL x (IMPLIES (IN x RR) (FORALL y (IMPLIES (IN y RR)
     (FORALL z (IMPLIES (IN z RR)
       (IMPLIES (AND (<= x y) (< y z)) (< x z))))))))))
(ro-farkas!)
(qed 'rr-le-lt-trans)
(topic! 'rr-le-lt-trans 'inequalities)

;;; Weakening.  `<' is `<=' AND `/=' by definition, so this is the left conjunct;
;;; the oracle gets there without unfolding, `lt' entailing `le'.
(sp (make-wff '(FORALL x (IMPLIES (IN x RR) (FORALL y (IMPLIES (IN y RR)
     (IMPLIES (< x y) (<= x y))))))))
(ro-farkas!)
(qed 'rr-lt-implies-le)
(topic! 'rr-lt-implies-le 'inequalities)

;;; --------------------------------------------------------------------
;;; SIGN OF A DIFFERENCE.  Moving a term across the relation -- the step the
;;; Caratheodory mean-value arc takes in every direction.

(sp (make-wff '(FORALL u (IMPLIES (IN u RR) (FORALL v (IMPLIES (IN v RR)
     (IMPLIES (<= u v) (<= (- u v) 0))))))))
(ro-farkas!)
(qed 'rr-le-diff-nonpos)
(topic! 'rr-le-diff-nonpos 'inequalities)

(sp (make-wff '(FORALL u (IMPLIES (IN u RR) (FORALL v (IMPLIES (IN v RR)
     (IMPLIES (< u v) (< 0 (- v u)))))))))
(ro-farkas!)
(qed 'rr-lt-diff-pos)
(topic! 'rr-lt-diff-pos 'inequalities)

(sp (make-wff '(FORALL u (IMPLIES (IN u RR) (FORALL v (IMPLIES (IN v RR)
     (IMPLIES (< u v) (< (- u v) 0))))))))
(ro-farkas!)
(qed 'rr-lt-diff-neg)
(topic! 'rr-lt-diff-neg 'inequalities)

;;; 0 = u - v  =>  u = v.  An `=' goal, which the oracle also decides (an
;;; equality premise splits into its two `<=' directions, ineq-hyp-constraints).
(sp (make-wff '(FORALL u (IMPLIES (IN u RR) (FORALL v (IMPLIES (IN v RR)
     (IMPLIES (= 0 (- u v)) (= u v))))))))
(ro-farkas!)
(qed 'rr-diff-zero-eq)
(topic! 'rr-diff-zero-eq 'inequalities)

;;; --------------------------------------------------------------------
;;; NEGATION AND ORDER.

(sp (make-wff '(FORALL u (IMPLIES (IN u RR) (FORALL v (IMPLIES (IN v RR)
     (IMPLIES (<= u v) (<= (- v) (- u)))))))))
(ro-farkas!)
(qed 'rr-le-neg)
(topic! 'rr-le-neg 'inequalities)

(sp (make-wff '(FORALL u (IMPLIES (IN u RR) (IMPLIES (= (- u) 0) (= u 0))))))
(ro-farkas!)
(qed 'rr-neg-eq-zero)
(topic! 'rr-neg-eq-zero 'inequalities)

;;; --------------------------------------------------------------------
;;; THE THREE THAT ARE NOT ORDER GOALS.
;;;
;;; A NOT or an OR is invisible to Farkas -- correctly: the oracle decides linear
;;; consequence, and neither shape is one.  Each is reduced to a shape that is,
;;; through the DEFINITION of `<' rather than through a new assertion.

;;; u /= v  =>  u - v /= 0.  Contrapositive: `di' on a NOT goal assumes the
;;; positive with goal FALSITY, the oracle proves u = v from u - v = 0, and `ai'
;;; on the negation closes.  (`ai' on a NOT is NOT-ELIM: it fires only when the
;;; positive is ALREADY in context, so the `have!' must come first.)
(sp (make-wff '(FORALL u (IMPLIES (IN u RR) (FORALL v (IMPLIES (IN v RR)
     (IMPLIES (NOT (= u v)) (NOT (= (- u v) 0)))))))))
(ro-peel!)
(di)                                       ; assume (= (- u v) 0), goal falsity
(have! '(= u v) (lambda () (ro-ineq!)))
(ai '(NOT (= u v)))
(qed 'rr-sub-ne-zero)
(topic! 'rr-sub-ne-zero 'inequalities)

;;; 0 < c  =>  c /= 0.  Purely definitional once `<' is unfolded IN THE
;;; ASSUMPTION: it leaves 0 <= c and not(0 = c), and `neq-sym' turns the second
;;; into the goal.  No arithmetic at all.
(sp (make-wff '(FORALL c (IMPLIES (IN c RR) (IMPLIES (< 0 c) (NOT (= c 0)))))))
(ro-peel!)
(mac-h '< '(< 0 c))
(dk-split! '(AND (<= 0 c) (NOT (= 0 c))))
(fact 'neq-sym 0 'c)
(ass)
(qed 'rr-pos-ne-zero)
(topic! 'rr-pos-ne-zero 'inequalities)

;;; IRREFLEXIVITY of the strict order: not (a < a).
;;;
;;; MOVED HERE on 2026-09-19 (batch 8-K2) from theorem-library/c-int-oriented.scm,
;;; where it was proved because nothing before it had needed to rule a branch of
;;; a conditional OUT, and where it was stranded at load position 537 -- below
;;; theorem-library/rpow-star (545), its only other citer, and below everything
;;; else that might want it.  It is an RR ORDER fact and belongs with the rest
;;; of them; the original text is archive/2026-09-19-batch8/c-int-oriented.scm.
;;;
;;; `ineq' cannot supply it: the goal is a NOT (CLAUDE.md, "the tactics' real
;;; behaviour").  It is instead purely definitional -- `<' is `<= and /='
;;; (order-predicates.scm), so irreflexivity is the reflexivity of `=' read
;;; through the unfolded assumption.
(sp (make-wff '(FORALL a (IMPLIES (IN a RR) (NOT (< a a))))))
(ro-peel!)
(di)                                       ; assume a < a, goal falsity
(mac-h '< '(< a a))
(have! '(= a a) (lambda () (rfl)))
(prop)
(qed 'rr-lt-irrefl)
(topic! 'rr-lt-irrefl 'inequalities)
(alias! 'rr-lt-irrefl "no real is less than itself")

;;; u <= v  =>  u < v or u = v.  The excluded middle on (= u v), and then the
;;; unfolded `<' is exactly the pair of facts in context.
(sp (make-wff '(FORALL u (IMPLIES (IN u RR) (FORALL v (IMPLIES (IN v RR)
     (IMPLIES (<= u v) (OR (< u v) (= u v)))))))))
(ro-peel!)
(mac '<)
(use-em '(= u v)
  (lambda () (oi-r) (ass))
  (lambda () (oi-l) (ro-ass-opened! (lambda () (di)))))
(qed 'rr-le-cases)
(topic! 'rr-le-cases 'inequalities)

;;; u <= v and u /= v  =>  u < v.  The definition of `<' read forward; stated
;;; separately because rolle-proof cites it in that direction.
(sp (make-wff '(FORALL u (IMPLIES (IN u RR) (FORALL v (IMPLIES (IN v RR)
     (IMPLIES (AND (<= u v) (NOT (= u v))) (< u v))))))))
(ro-peel!)
(ro-split!)
(mac '<)
(ro-ass-opened! (lambda () (di)))
(qed 'rr-le-ne-lt)
(topic! 'rr-le-ne-lt 'inequalities)

;;; --------------------------------------------------------------------
;;; ADDING INEQUALITIES, and moving a term across one.  All four are the
;;; oracle's home ground: nothing here leaves the linear fragment.

(sp (make-wff (forall-guarded '(x y u v)
                (list '(IN x RR) '(IN y RR) '(IN u RR) '(IN v RR))
                '(IMPLIES (AND (<= x y) (<= u v)) (<= (+ x u) (+ y v))))))
(ro-farkas!)
(qed 'rr-le-add)
(topic! 'rr-le-add 'inequalities)

(sp (make-wff (forall-guarded '(x y u v)
                (list '(IN x RR) '(IN y RR) '(IN u RR) '(IN v RR))
                '(IMPLIES (AND (< x y) (<= u v)) (< (+ x u) (+ y v))))))
(ro-farkas!)
(qed 'rr-lt-add)
(topic! 'rr-lt-add 'inequalities)

(sp (make-wff (forall-guarded '(x y) (list '(IN x RR) '(IN y RR))
                '(IMPLIES (AND (<= 0 x) (<= 0 y)) (<= 0 (+ x y))))))
(ro-farkas!)
(qed 'rr-add-nonneg)
(topic! 'rr-add-nonneg 'inequalities)

(sp (make-wff (forall-guarded '(x y) (list '(IN x RR) '(IN y RR))
                '(IMPLIES (<= 0 (- y x)) (<= x y)))))
(ro-farkas!)
(qed 'rr-le-from-diff-nonneg)
(topic! 'rr-le-from-diff-nonneg 'inequalities)

(sp (make-wff (forall-guarded 'x '(IN x RR)
                '(IMPLIES (<= 0 (+ x x)) (<= 0 x)))))
(ro-farkas!)
(qed 'rr-double-nonneg)
(topic! 'rr-double-nonneg 'inequalities)

;;; --------------------------------------------------------------------
;;; RR HAS NO ZERO DIVISORS -- the one genuinely FIELD-theoretic fact in this
;;; file, and the thing Farkas cannot reach.
;;;
;;; The remaining order lemmas below are NONLINEAR: they multiply by a variable,
;;; and the oracle linearises only over + - * with a CONSTANT factor.  What makes
;;; them provable is not the order axioms at all but rr-recip-closed /
;;; rr-recip-inverse -- RR is a field, so a product is zero only if a factor is.
;;; The proof is theorem-library/zz-integral-domain.scm's, one system down: four
;;; rewrites, reassociate / cancel / drop the unit.
(sp (make-wff (forall-guarded '(a b) (list '(IN a RR) '(IN b RR))
                '(IMPLIES (= (* a b) 0) (OR (= a 0) (= b 0))))))
(ro-peel!)
(use-em '(= b 0)
  ;; b = 0: the right disjunct is the hypothesis.
  (lambda () (oi-r) (ass))
  ;; b /= 0: b is invertible, so a is 0.  rr-recip-closed / -inverse / rr-mul-assoc
  ;; all guard on a CONJUNCTION, which `fact' will not split -- hence each have!.
  (lambda ()
    (oi-l)
    (have! '(AND (IN b RR) (NOT (= b 0))))
    (fact 'rr-recip-closed 'b)
    (fact 'rr-recip-inverse 'b)                ; b * recip b = 1
    (have! '(AND (IN a RR) (AND (IN b RR) (IN (recip b) RR))))
    (fact 'rr-mul-assoc 'a 'b '(recip b))
    (have! '(= (* (* a b) (recip b)) a)
           (lambda ()
             (subst '(= (* (* a b) (recip b)) (* a (* b (recip b)))))
             (subst '(= (* b (recip b)) 1))
             (crs)))                            ; a * 1 = a
    (subst '(= a (* (* a b) (recip b))))
    (subst '(= (* a b) 0))
    (crs)))                                     ; 0 * recip b = 0
(qed 'rr-no-zero-divisors)
(topic! 'rr-no-zero-divisors 'algebra)

;;; RIGHT CANCELLATION.  u*c = v*c with c /= 0 gives u = v: the difference
;;; (u-v)*c is u*c - v*c = 0, and c is not the vanishing factor.
(sp (make-wff (forall-guarded '(u v c) (list '(IN u RR) '(IN v RR) '(IN c RR))
                '(IMPLIES (NOT (= c 0)) (IMPLIES (= (* u c) (* v c)) (= u v))))))
(ro-peel!)
(have! '(AND (IN u RR) (IN v RR)))
(fact 'rr-sub-in-rr 'u 'v)
(have! '(AND (IN (- u v) RR) (IN c RR)))
(fact 'rr-mul-closed '(- u v) 'c)
(have! '(AND (IN u RR) (IN c RR)))
(fact 'rr-mul-closed 'u 'c)
(have! '(AND (IN v RR) (IN c RR)))
(fact 'rr-mul-closed 'v 'c)
(have! '(= (* (- u v) c) (- (* u c) (* v c))) (lambda () (crs)))
(have! '(= (* (- u v) c) 0) (lambda () (ro-ineq!)))
(fact 'rr-no-zero-divisors '(- u v) 'c)
(use-cases '((= (- u v) 0) (= c 0))
  (lambda () (ro-ineq!))
  (lambda () (ai '(NOT (= c 0)))))
(qed 'rr-cancel-mul-right)
(topic! 'rr-cancel-mul-right 'algebra)

;;; SCALING A STRICT INEQUALITY BY A POSITIVE FACTOR.
;;;
;;;   0 < c  and  x < y   =>   c*x < c*y
;;;
;;; rr-leq-mul-nonneg (primitive) gives only the NONSTRICT half, and only in the
;;; form 0 <= c*(y-x); the ring identity c*(y-x) = c*y - c*x turns it into
;;; c*x <= c*y for the oracle.  The STRICT half is where the field comes in: if
;;; c*x = c*y then c*(y-x) = 0, and with c /= 0 and y /= x that contradicts
;;; rr-no-zero-divisors.
;;;
;;; This was the last unwarranted leaf of rr-mul-pos and (with rr-lt-trichotomy,
;;; above) of rr-recip-pos, both in theorem-library/rr-recip-order.scm, whose
;;; header named `scale-pos' first in its list of loose ends.
(sp (make-wff (forall-guarded '(c x y) (list '(IN c RR) '(IN x RR) '(IN y RR))
                '(IMPLIES (AND (< 0 c) (< x y)) (< (* c x) (* c y))))))
(ro-peel!)
(ro-split!)
(mac-h '< '(< 0 c))
(dk-split! '(AND (<= 0 c) (NOT (= 0 c))))
(fact 'neq-sym 0 'c)
(mac-h '< '(< x y))
(dk-split! '(AND (<= x y) (NOT (= x y))))
;; every atom the oracle will see has to carry a literal (IN t RR).
(have! '(AND (IN y RR) (IN x RR)))
(fact 'rr-sub-in-rr 'y 'x)
(have! '(AND (IN c RR) (IN x RR)))
(fact 'rr-mul-closed 'c 'x)
(have! '(AND (IN c RR) (IN y RR)))
(fact 'rr-mul-closed 'c 'y)
(have! '(AND (IN c RR) (IN (- y x) RR)))
(fact 'rr-mul-closed 'c '(- y x))
(have! '(<= 0 (- y x)) (lambda () (ro-ineq!)))
(have! '(AND (<= 0 c) (<= 0 (- y x))))
(fact 'rr-leq-mul-nonneg 'c '(- y x))            ; 0 <= c * (y - x)
(have! '(= (* c (- y x)) (- (* c y) (* c x))) (lambda () (crs)))
(mac '<)                                         ; goal: c*x <= c*y and c*x /= c*y
(for-each
 (lambda (k)
   (dk-focus! k)
   (if (eq? (car (dk-goal)) 'NOT)
       (begin
         (di)                                    ; assume c*x = c*y, goal falsity
         (have! '(= (* c (- y x)) 0) (lambda () (ro-ineq!)))
         (fact 'rr-no-zero-divisors 'c '(- y x))
         (use-cases '((= c 0) (= (- y x) 0))
           (lambda () (ai '(NOT (= c 0))))
           (lambda () (have! '(= x y) (lambda () (ro-ineq!)))
                      (ai '(NOT (= x y))))))
       (ro-ineq!)))
 (dk-opened (lambda () (di))))
(qed 'rr-lt-scale-pos)
(topic! 'rr-lt-scale-pos 'inequalities)

;;; SCALING BY A NONNEGATIVE FACTOR -- the nonstrict half of the same argument,
;;; which needs no field theory at all, only rr-leq-mul-nonneg and one ring
;;; identity.
(sp (make-wff (forall-guarded '(c x y) (list '(IN c RR) '(IN x RR) '(IN y RR))
                '(IMPLIES (AND (<= 0 c) (<= x y)) (<= (* c x) (* c y))))))
(ro-peel!)
(ro-split!)
(have! '(AND (IN y RR) (IN x RR)))
(fact 'rr-sub-in-rr 'y 'x)
(have! '(AND (IN c RR) (IN x RR)))
(fact 'rr-mul-closed 'c 'x)
(have! '(AND (IN c RR) (IN y RR)))
(fact 'rr-mul-closed 'c 'y)
(have! '(AND (IN c RR) (IN (- y x) RR)))
(fact 'rr-mul-closed 'c '(- y x))
(have! '(<= 0 (- y x)) (lambda () (ro-ineq!)))
(have! '(AND (<= 0 c) (<= 0 (- y x))))
(fact 'rr-leq-mul-nonneg 'c '(- y x))
(have! '(= (* c (- y x)) (- (* c y) (* c x))) (lambda () (crs)))
(ro-ineq!)
(qed 'rr-le-scale-nonneg)
(topic! 'rr-le-scale-nonneg 'inequalities)

;;; A SQUARE IS NONNEGATIVE.  rr-leq-mul-nonneg wants both factors nonnegative,
;;; so the negative case runs it on -x and rides back on x*x = (-x)*(-x).  Total
;;; order supplies the case split; there is no appeal to a sign function.
(sp (make-wff (forall-guarded 'x '(IN x RR) '(<= 0 (* x x)))))
(ro-peel!)
(fact 'rr-zero-in)
(have! '(AND (IN 0 RR) (IN x RR)))
(fact 'rr-leq-total 0 'x)
(use-cases '((<= 0 x) (<= x 0))
  (lambda ()
    (have! '(AND (IN x RR) (IN x RR)))
    (have! '(AND (<= 0 x) (<= 0 x)))
    (fact 'rr-leq-mul-nonneg 'x 'x)
    (ass))
  (lambda ()
    (fact 'rr-neg-closed 'x)
    (have! '(<= 0 (- x)) (lambda () (ro-ineq!)))
    (have! '(AND (IN (- x) RR) (IN (- x) RR)))
    (have! '(AND (<= 0 (- x)) (<= 0 (- x))))
    (fact 'rr-leq-mul-nonneg '(- x) '(- x))
    (have! '(= (* x x) (* (- x) (- x))) (lambda () (crs)))
    (subst '(= (* x x) (* (- x) (- x))))
    (ass)))
(qed 'rr-sq-nonneg)
(topic! 'rr-sq-nonneg 'inequalities)

;;; --------------------------------------------------------------------
;;; THE THREE ABS THEOREMS THAT STOOD HERE MOVED 2026-08-17 to
;;; theorem-library/rr-abs-basics.scm: rr-abs-neg (|-a| = |a|), rr-abs-triangle-c
;;; (the curried triangle inequality) and rr-abs-sub-sym (|u-v| = |v-u|).
;;;
;;; They had to move, not merely to keep the abs material together: they were
;;; proved FROM the five norm-shaped abs axioms of number-systems.scm, and those
;;; axioms are gone -- replaced by the definition `rr-abs-def' and re-proved in
;;; that file, which loads immediately after this one.  This file no longer
;;; mentions abs at all.
;;;
;;; The old proof of rr-abs-neg is worth remembering as the measure of what the
;;; axioms could reach: evenness was the ONLY sign fact derivable from them, and
;;; getting it took multiplicativity, the ring identity a*a = (-a)*(-a), a
;;; difference of squares and `rr-no-zero-divisors' (proved above).  From the
;;; definition it is four lines and one `ineq'.

;;; --------------------------------------------------------------------
;;; TRICHOTOMY.  rr-leq-total (primitive) gives u<=v or v<=u; the excluded middle
;;; on (= u v) splits the equal case off; `neq-sym' supplies not(v = u) for the
;;; right-hand branch, since `=' has no symmetry lemma in the tree and the two
;;; disequalities are distinct atoms.
(sp (make-wff '(FORALL u (IMPLIES (IN u RR) (FORALL v (IMPLIES (IN v RR)
     (OR (< u v) (OR (= u v) (< v u)))))))))
(ro-peel!)
(have! '(AND (IN u RR) (IN v RR)))
(fact 'rr-leq-total 'u 'v)
(use-em '(= u v)
  (lambda () (oi-r) (oi-l) (ass))
  (lambda ()
    (fact 'neq-sym 'u 'v)
    (use-cases '((<= u v) (<= v u))
      (lambda () (oi-l) (mac '<) (ro-ass-opened! (lambda () (di))))
      (lambda () (oi-r) (oi-r) (mac '<) (ro-ass-opened! (lambda () (di)))))))
(qed 'rr-lt-trichotomy)
(topic! 'rr-lt-trichotomy 'analysis)

;;; --------------------------------------------------------------------
;;; A COMMON UPPER BOUND of two reals -- "max(u,v) exists", stated
;;; existentially so that no MAX operator has to be introduced.  Every
;;; creeping argument that merges two local bounds into one needs it
;;; (theorem-library/ccint-bounded.scm, theorem-library/evt-proof.scm): the
;;; bound inherited from the left part of the interval and the bound
;;; continuity gives near the right end are unrelated, and the merged bound
;;; is the larger of the two.  `rr-leq-total' decides which.
(sp (make-wff (forall-guarded '(u v) (list '(IN u RR) '(IN v RR))
     '(FORSOME w_ (AND (IN w_ RR) (AND (<= u w_) (<= v w_)))))))
(ro-peel!)
(have! '(AND (IN u RR) (IN v RR)))
(fact 'rr-leq-total 'u 'v)
(fact 'rr-leq-reflexive 'u)
(fact 'rr-leq-reflexive 'v)
(use-cases '((<= u v) (<= v u))
  (lambda () (ew 'v) (from-context!))
  (lambda () (ew 'u) (from-context!)))
(qed 'rr-upper-of-two)
(topic! 'rr-upper-of-two 'inequalities)
(alias! 'rr-upper-of-two "common upper bound of two reals" "max of two reals exists")

;;; The same, with a CEILING both reals stay under: if u and v are both below
;;; m, some common upper bound of the two is still below m.  `rr-upper-of-two'
;;; will not do here -- it returns SOME upper bound, which may overshoot m --
;;; and the attainment half of EVT (theorem-library/evt-proof.scm) needs the
;;; merged bound to stay strictly below the supremum, which is the whole point
;;; of the set it creeps along.  The witness is one of u, v, so it inherits the
;;; strict bound.
(sp (make-wff (forall-guarded '(u v m)
     (list '(IN u RR) '(IN v RR) '(IN m RR) '(< u m) '(< v m))
     '(FORSOME w_ (AND (IN w_ RR) (AND (<= u w_) (AND (<= v w_) (< w_ m))))))))
(ro-peel!)
(have! '(AND (IN u RR) (IN v RR)))
(fact 'rr-leq-total 'u 'v)
(fact 'rr-leq-reflexive 'u)
(fact 'rr-leq-reflexive 'v)
(use-cases '((<= u v) (<= v u))
  (lambda () (ew 'v) (from-context!))
  (lambda () (ew 'u) (from-context!)))
(qed 'rr-upper-of-two-below)
(topic! 'rr-upper-of-two-below 'inequalities)

;;; The dual of rr-upper-of-two, and the form every eps/delta proof actually
;;; wants: a POSITIVE lower bound of two positives.  Stated with the positivity
;;; built in rather than as a bare "min exists", because a delta is useless
;;; without it -- and stated existentially, so no MIN operator is introduced.
;;; The witness is one of u, v, so its positivity is inherited.
(sp (make-wff (forall-guarded '(u v) (list '(IN u RR) '(IN v RR) '(< 0 u) '(< 0 v))
     '(FORSOME w_ (AND (IN w_ RR) (AND (< 0 w_) (AND (<= w_ u) (<= w_ v))))))))
(ro-peel!)
(have! '(AND (IN u RR) (IN v RR)))
(fact 'rr-leq-total 'u 'v)
(fact 'rr-leq-reflexive 'u)
(fact 'rr-leq-reflexive 'v)
(use-cases '((<= u v) (<= v u))
  (lambda () (ew 'u) (from-context!))
  (lambda () (ew 'v) (from-context!)))
(qed 'rr-min-pos)
(topic! 'rr-min-pos 'inequalities)

;;; PRODUCT OF TWO BOUNDS.  0 <= a <= b and 0 <= u <= v give a*u <= b*v.  It is
;;; rr-le-scale-nonneg twice and one transitivity, but it is worth its own name:
;;; it is the step `ineq' cannot take (a product of two VARIABLES is not linear),
;;; and every eps/delta estimate that bounds |f(x)-f(a)| by a product of two
;;; separately-bounded factors needs exactly this and nothing more.
(sp (make-wff (forall-guarded '(a b u v)
     (list '(IN a RR) '(IN b RR) '(IN u RR) '(IN v RR))
     '(IMPLIES (AND (AND (<= 0 a) (<= a b)) (AND (<= 0 u) (<= u v)))
               (<= (* a u) (* b v))))))
(ro-peel!)
(ro-split!)
(have! '(<= 0 v) (lambda () (ro-ineq!)))
(have! '(AND (<= 0 a) (<= u v)))
(fact 'rr-le-scale-nonneg 'a 'u 'v)              ; a*u <= a*v
(have! '(AND (<= 0 v) (<= a b)))
(fact 'rr-le-scale-nonneg 'v 'a 'b)              ; v*a <= v*b
(have! '(AND (IN a RR) (IN u RR)))
(fact 'rr-mul-closed 'a 'u)
(have! '(AND (IN a RR) (IN v RR)))
(fact 'rr-mul-closed 'a 'v)
(have! '(AND (IN b RR) (IN v RR)))
(fact 'rr-mul-closed 'b 'v)
;; a*v <= b*v is v*a <= v*b with both sides commuted -- `crs' supplies the two
;; equations, `subst' turns the goal into the fact already in context.
(have! '(= (* a v) (* v a)) (lambda () (crs)))
(have! '(= (* b v) (* v b)) (lambda () (crs)))
(have! '(<= (* a v) (* b v))
  (lambda () (subst '(= (* a v) (* v a))) (subst '(= (* b v) (* v b))) (ass)))
(have! '(AND (IN (* a u) RR) (AND (IN (* a v) RR) (IN (* b v) RR))))
(have! '(AND (<= (* a u) (* a v)) (<= (* a v) (* b v))))
(fact 'rr-leq-transitive '(* a u) '(* a v) '(* b v))
(ass)
(qed 'rr-prod-le-prod)
(topic! 'rr-prod-le-prod 'inequalities)

;;; --------------------------------------------------------------------
;;; rr-nonneg-cancel-pos: 0 < c and 0 <= c*d  =>  0 <= d.
;;;
;;; Cancelling a POSITIVE factor out of a nonnegativity.  Added 2026-08-18 for
;;; theorem-library/inner-product-inequalities.scm, where the Schwarz inequality
;;; arrives as 0 <= <y,y> * (<y,y><x,x> - |<x,y>|^2) and the factor <y,y> has to
;;; come off.  It is the multiplicative companion of rr-le-from-diff-nonneg and
;;; belongs with the rest of the order calculus rather than beside its consumer.
;;;
;;; NOT one call to `ineq', and the reason is worth recording: `vnb->linear'
;;; (ineq-oracle.scm:61-65) turns a product of two VARIABLES into a maximal ATOM,
;;; so `c*d' is an opaque symbol to the oracle and no Farkas certificate can
;;; relate it to c and d.  The proof therefore does the case analysis by hand --
;;; rr-lt-trichotomy on d -- and uses `ineq' only where the goal really is linear
;;; in its atoms: the d<0 branch closes because rr-lt-scale-pos gives c*d < c*0 = 0
;;; against the hypothesis 0 <= c*d, and rr-le-lt-trans turns that pair into the
;;; numeric absurdity 0 < 0, from which one `ineq' naming THAT premise alone
;;; explodes.
;;;
;;; `ineq' with NO index arguments uses NO premises (cmd-ineq passes idxs
;;; straight through, proof-commands.scm:717): it closes only goals true outright.
;;; Every call below names its premise.
(define (ro-idx-of f)
  (let loop ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "ro-idx-of: not in context" f))
          ((equal? (car l) f) i)
          (else (loop (cdr l) (+ i 1))))))

(sp (make-wff (forall-guarded '(c d)
     (list '(IN c RR) '(IN d RR) '(< 0 c) '(<= 0 (* c d)))
     '(<= 0 d))))
(ro-peel!)
(have! '(IN 0 RR) (lambda () (arith)))
(have! '(AND (IN c RR) (IN d RR)))
(fact 'rr-mul-closed 'c 'd)
(fact 'rr-lt-trichotomy 'd 0)
(use-cases '((< d 0) (= d 0) (< 0 d))
  ;; d < 0: then c*d < c*0 = 0, contradicting 0 <= c*d.
  (lambda ()
    (have! '(AND (< 0 c) (< d 0)))
    (fact 'rr-lt-scale-pos 'c 'd 0)
    (have! '(= (* c 0) 0) (lambda () (crs)))
    (have! '(< (* c d) 0) (lambda () (subst '(= 0 (* c 0))) (ass)))
    (have! '(AND (<= 0 (* c d)) (< (* c d) 0)))
    (fact 'rr-le-lt-trans 0 '(* c d) 0)
    (ineq (ro-idx-of '(< 0 0))))
  (lambda () (subst '(= d 0)) (arith))
  (lambda () (ineq (ro-idx-of '(< 0 d)))))
(qed 'rr-nonneg-cancel-pos)
(topic! 'rr-nonneg-cancel-pos 'inequalities)
(alias! 'rr-nonneg-cancel-pos "cancelling a positive factor from a nonnegativity")

;;; -----------------------------------------------------------------------
;;; TOTALITY of <= on RR.  Added 2026-08-19, moved here from
;;; theorem-library/rr-max-basics.scm where it was first needed and where it did
;;; not belong -- it is an ORDER fact and says nothing about MAX.
;;;
;;; It was also badly named there (`rr-not-le-le`, which reads as three
;;; relations in a row).  `rr-le-total' is the name a reader looks for, and the
;;; one I looked for and did not find; stating the DISJUNCTION rather than the
;;; implication form is what makes the name honest, and the implication a caller
;;; usually wants -- `not(v <= u)' therefore `u <= v' -- is disjunctive
;;; syllogism, which `prop' decides with both relations opaque.
;;;
;;; `ineq' cannot supply this and it is worth saying why: Fourier-Motzkin will
;;; not NEGATE a `<=' premise, so `not(v <= u) |- u <= v' fails with "goal not a
;;; linear-RR consequence" -- which reads as a defect in the goal and is really
;;; the oracle declining a step that is not linear-arithmetical at all.
;;; Totality is an ORDER axiom's business, and here it comes from
;;; `rr-lt-trichotomy'.
(sp (make-wff-from-string "forall([u in rr, v in rr], u <= v or v <= u)"))
(ro-peel!)
(fact 'rr-lt-trichotomy 'u 'v)
(use-cases '((< u v) (= u v) (< v u))
  (lambda () (have! '(<= u v) (lambda () (ineq (ro-idx-of '(< u v))
                                               (ro-idx-of '(IN u RR))
                                               (ro-idx-of '(IN v RR)))))
             (prop))
  (lambda () (have! '(<= u v) (lambda () (ineq (ro-idx-of '(= u v))
                                               (ro-idx-of '(IN u RR))
                                               (ro-idx-of '(IN v RR)))))
             (prop))
  (lambda () (have! '(<= v u) (lambda () (ineq (ro-idx-of '(< v u))
                                               (ro-idx-of '(IN u RR))
                                               (ro-idx-of '(IN v RR)))))
             (prop)))
(qed 'rr-le-total)
(topic! 'rr-le-total 'inequalities)
(alias! 'rr-le-total "totality of the order on the reals")

;;; =====================================================================
;;; The two bridges between `<' and the negation of `<=' (batch 12-F, 2026-09-20;
;;; proven in metric-closure-laws.scm and moved here at integration).
;;; `rr-lt-asymm' relates two STRICT inequalities and `rr-le-ne-lt' goes the
;;; other way; neither of these shapes was in the tree.
;;; =====================================================================

(sp (make-wff '(FORALL a (IMPLIES (IN a RR)
     (FORALL b (IMPLIES (IN b RR)
       (IMPLIES (< a b) (NOT (<= b a)))))))))
(dk-peel!)
(di)                                          ; assume (<= b a); goal FALSITY
(dk-split! (dk-landed-1 (lambda () (mac-h '< '(< a b)))))
(have! '(AND (IN a RR) (IN b RR)))
(have! '(AND (<= a b) (<= b a)))
(dk-fact! 'rr-leq-antisymmetric 'a 'b)
(ai '(NOT (= a b)))
(qed 'rr-lt-not-le)
(gloss! 'rr-lt-not-le
  "A strict inequality rules the reverse non-strict one out: a < b implies not(b <= a).
   The step every \"the point is OUTSIDE the closed ball\" argument needs.")
(topic! 'rr-lt-not-le 'inequalities)

(sp (make-wff '(FORALL a (IMPLIES (IN a RR)
     (FORALL b (IMPLIES (IN b RR)
       (IMPLIES (NOT (<= a b)) (< b a))))))))
(dk-peel!)
(have! '(AND (IN a RR) (IN b RR)))
(dk-fact! 'rr-leq-total 'a 'b)
(use-cases '((<= a b) (<= b a))
  (lambda () (ai '(NOT (<= a b))))
  (lambda ()
    (have! '(NOT (= b a))
      (lambda ()
        (di)
        (have! '(<= a b) (lambda () (subst '(= b a)) (fact 'rr-leq-reflexive 'a) (ass)))
        (ai '(NOT (<= a b)))))
    (have! '(AND (<= b a) (NOT (= b a))))
    (dk-fact! 'rr-le-ne-lt 'b 'a)
    (ass)))
(qed 'rr-not-le-lt)
(gloss! 'rr-not-le-lt
  "The converse bridge: not(a <= b) implies b < a, by totality of <= plus
   reflexivity to rule the equal case out.")
(topic! 'rr-not-le-lt 'inequalities)
