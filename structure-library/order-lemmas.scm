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
