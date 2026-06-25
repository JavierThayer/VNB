;;; order-lemmas.scm -- the finite order calculus of RR.
;;;
;;; number-systems.scm gives the static order axioms (rr-leq reflexive /
;;; antisymmetric / transitive / total / add-compatible, mul-nonneg) and the abs
;;; axioms (closed / nonneg / zero-iff / triangle / mult).  Those alone do not
;;; give the everyday moves of an epsilon-argument: adding two inequalities,
;;; mixing < with <=, scaling by a nonnegative factor, x <= |x|.  This file
;;; supplies that workhorse layer as warranted PSS supports -- each one a one-
;;; or two-step consequence of the axioms, recorded so proofs (and the future
;;; inequality decision procedure) can lean on them by name.
;;;
;;; All over RR.  Bound vars avoid the case-fold traps: NOT `a' (-> accessor A),
;;; NOT `e' (-> identity accessor E), NOT `n'/`N' collisions; reals are
;;; x y z u v, a nonneg/pos factor is c, a bound is bnd.
;;;
;;; Library-build phase: warranted well-known [[feedback-library-axioms-fine]].
;;; These are exactly the cases the linear-arithmetic oracle must also decide,
;;; so they double as its specification.  Dependencies: number-systems.scm
;;; (RR, <=, +, *, -, abs), order-predicates.scm (<, POS-RR).

;;; -----------------------------------------------------------------------
;;; Chaining: mixed strict / non-strict transitivity, and weakening.

(support 'rr-lt-implies-le
  '(FORALL x (IMPLIES (IN x RR) (FORALL y (IMPLIES (IN y RR)
     (IMPLIES (< x y) (<= x y)))))))
(warrant! 'rr-lt-implies-le 'well-known
  "x < y is (x <= y and x =/= y) by definition, so in particular x <= y.")

(support 'rr-lt-trans
  '(FORALL x (IMPLIES (IN x RR) (FORALL y (IMPLIES (IN y RR)
     (FORALL z (IMPLIES (IN z RR)
       (IMPLIES (AND (< x y) (< y z)) (< x z)))))))))
(warrant! 'rr-lt-trans 'well-known
  "Strict order is transitive: from x<y<z, x<=z by rr-leq-transitive and x=/=z
   (else y would be both > and < x).")

(support 'nn-in-rr
  '(FORALL k (IMPLIES (IN k NN) (IN k RR))))
(warrant! 'nn-in-rr 'proof
  "The inclusion chain NN subset ZZ subset QQ subset RR (nn-subset-zz,
   zz-subset-qq, qq-subset-rr) composed: a natural number is a real.")

(support 'nn-le-refl
  '(FORALL k (IMPLIES (IN k NN) (<= k k))))
(warrant! 'nn-le-refl 'proof
  "k in NN gives k in RR (nn-in-rr); rr-leq-reflexive then gives k <= k.")

(support 'rr-le-trans
  '(FORALL x (IMPLIES (IN x RR) (FORALL y (IMPLIES (IN y RR)
     (FORALL z (IMPLIES (IN z RR)
       (IMPLIES (AND (<= x y) (<= y z)) (<= x z)))))))))
(warrant! 'rr-le-trans 'well-known
  "Non-strict order is transitive: x <= y <= z gives x <= z (rr-leq-transitive).")

(support 'rr-lt-le-trans
  '(FORALL x (IMPLIES (IN x RR) (FORALL y (IMPLIES (IN y RR)
     (FORALL z (IMPLIES (IN z RR)
       (IMPLIES (AND (< x y) (<= y z)) (< x z)))))))))
(warrant! 'rr-lt-le-trans 'well-known
  "x < y <= z gives x < z (transitivity; x=z would force y=x against x<y).")

(support 'rr-le-lt-trans
  '(FORALL x (IMPLIES (IN x RR) (FORALL y (IMPLIES (IN y RR)
     (FORALL z (IMPLIES (IN z RR)
       (IMPLIES (AND (<= x y) (< y z)) (< x z)))))))))
(warrant! 'rr-le-lt-trans 'well-known
  "x <= y < z gives x < z (symmetric to rr-lt-le-trans).")

;;; -----------------------------------------------------------------------
;;; Adding inequalities -- the central epsilon-argument move.

(support 'rr-le-add
  '(FORALL x (IMPLIES (IN x RR) (FORALL y (IMPLIES (IN y RR)
     (FORALL u (IMPLIES (IN u RR) (FORALL v (IMPLIES (IN v RR)
       (IMPLIES (AND (<= x y) (<= u v)) (<= (+ x u) (+ y v))))))))))))
(warrant! 'rr-le-add 'well-known
  "Add two inequalities: x<=y gives x+u<=y+u (rr-leq-add-compatible), u<=v gives
   y+u<=y+v, then transitivity.  The workhorse behind every triangle-sum and
   eps/2+eps/2 bound.")

(support 'rr-add-nonneg
  '(FORALL x (IMPLIES (IN x RR) (FORALL y (IMPLIES (IN y RR)
     (IMPLIES (AND (<= 0 x) (<= 0 y)) (<= 0 (+ x y))))))) )
(warrant! 'rr-add-nonneg 'well-known
  "0<=x and 0<=y give 0 = 0+0 <= x+y by rr-le-add.")

(support 'rr-lt-add
  '(FORALL x (IMPLIES (IN x RR) (FORALL y (IMPLIES (IN y RR)
     (FORALL u (IMPLIES (IN u RR) (FORALL v (IMPLIES (IN v RR)
       (IMPLIES (AND (< x y) (<= u v)) (< (+ x u) (+ y v))))))))))))
(warrant! 'rr-lt-add 'well-known
  "A strict and a non-strict inequality add to a strict one: x+u < y+u <= y+v.")

;;; -----------------------------------------------------------------------
;;; Scaling by a nonnegative / positive factor.

(support 'rr-le-scale-nonneg
  '(FORALL c (IMPLIES (IN c RR) (FORALL x (IMPLIES (IN x RR)
     (FORALL y (IMPLIES (IN y RR)
       (IMPLIES (AND (<= 0 c) (<= x y)) (<= (* c x) (* c y))))))))))
(warrant! 'rr-le-scale-nonneg 'well-known
  "x<=y means 0<=y-x; with 0<=c, mul-nonneg gives 0<=c*(y-x)=c*y-c*x, i.e.
   c*x<=c*y.")

(support 'rr-lt-scale-pos
  '(FORALL c (IMPLIES (IN c RR) (FORALL x (IMPLIES (IN x RR)
     (FORALL y (IMPLIES (IN y RR)
       (IMPLIES (AND (< 0 c) (< x y)) (< (* c x) (* c y))))))))))
(warrant! 'rr-lt-scale-pos 'well-known
  "Multiplying a strict inequality by a strictly positive c keeps it strict
   (c*(y-x) > 0 since both factors are > 0).")

;;; -----------------------------------------------------------------------
;;; Absolute value beyond the number-systems axioms.

(support 'rr-le-abs
  '(FORALL x (IMPLIES (IN x RR) (<= x (abs x)))))
(warrant! 'rr-le-abs 'well-known
  "x <= |x| for every real (equality if x>=0; if x<0 then x<0<=|x|).")

(support 'rr-abs-bound
  '(FORALL x (IMPLIES (IN x RR) (FORALL c (IMPLIES (IN c RR)
     (IFF (<= (abs x) c)
          (AND (<= (- c) x) (<= x c))))))))
(warrant! 'rr-abs-bound 'well-known
  "|x| <= c  iff  -c <= x <= c.  The standard two-sided unpacking of an absolute-
   value bound; the form continuity/limit arguments use to turn |x| <= c into a
   pair of linear bounds.")

(support 'rr-abs-reverse-triangle
  '(FORALL x (IMPLIES (IN x RR) (FORALL y (IMPLIES (IN y RR)
     (<= (abs (- (abs x) (abs y))) (abs (- x y))))))))
(warrant! 'rr-abs-reverse-triangle 'well-known
  "||x|-|y|| <= |x-y|.  From the triangle inequality applied to x=(x-y)+y and
   y=(y-x)+x; standard.")

;;; -----------------------------------------------------------------------
;;; Squares are nonnegative, and the two order/arithmetic glue moves that
;;; turn a sum-of-squares certificate into a goal `<='.  Together with crs
;;; (which verifies the polynomial identity behind the certificate) these
;;; close every elementary polynomial inequality, e.g.
;;;   x*y <= x^2 + y^2   via   2*(x^2+y^2-x*y) = (x-y)^2 + x^2 + y^2.
;;; The missing real-line counterpart of cc-self-conj-nonneg (0 <= a*conj a).

(support 'rr-sq-nonneg
  '(FORALL x (IMPLIES (IN x RR) (<= 0 (* x x)))))
(warrant! 'rr-sq-nonneg 'well-known
  "0 <= x*x for every real.  If 0<=x, mul-nonneg gives 0<=x*x; if x<=0 then
   0<=(-x) and 0<=(-x)*(-x)=x*x.  The base square-positivity fact; the seed of
   every sum-of-squares inequality (Cauchy-Schwarz, AM-GM, x*y<=x^2+y^2).")

(support 'rr-le-from-diff-nonneg
  '(FORALL x (IMPLIES (IN x RR) (FORALL y (IMPLIES (IN y RR)
     (IMPLIES (<= 0 (- y x)) (<= x y)))))))
(warrant! 'rr-le-from-diff-nonneg 'well-known
  "0 <= y-x gives x <= y.  Add x to both sides of 0<=y-x (rr-leq-add-compatible)
   and simplify y-x+x=y.  The standard `move everything to one side' step that
   reduces an inequality goal to a nonnegativity goal.")

(support 'rr-double-nonneg
  '(FORALL x (IMPLIES (IN x RR)
     (IMPLIES (<= 0 (+ x x)) (<= 0 x)))))
(warrant! 'rr-double-nonneg 'well-known
  "0 <= x+x gives 0 <= x.  Contrapositive: x<0 adds to x+x<0 (rr-leq-add-compat).
   Lets a doubled sum-of-squares certificate (which avoids fractional 1/2
   coefficients) discharge the undoubled goal.")
