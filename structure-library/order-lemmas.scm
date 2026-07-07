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

(support 'nn-pair-upper-bound
  '(FORALL a (IMPLIES (IN a NN)
     (FORALL b (IMPLIES (IN b NN)
       (FORSOME c (AND (IN c NN) (AND (<= a c) (<= b c)))))))))
(warrant! 'nn-pair-upper-bound 'proof
  "NN is directed: any two naturals a, b have a common upper bound c (take
   c = a + b, or max(a,b)).  Lets a proof pick one threshold dominating two.")

(support 'rr-le-trans
  '(FORALL x (IMPLIES (IN x RR) (FORALL y (IMPLIES (IN y RR)
     (FORALL z (IMPLIES (IN z RR)
       (IMPLIES (AND (<= x y) (<= y z)) (<= x z)))))))))
(warrant! 'rr-le-trans 'well-known
  "Non-strict order is transitive: x <= y <= z gives x <= z (rr-leq-transitive).")

;; Curried siblings (no AND antecedent) so a forward `fact' discharges each
;; guard from context without a cut -- the shape interactive assembly wants.
(support 'rr-le-trans-c
  '(FORALL x (IMPLIES (IN x RR) (FORALL y (IMPLIES (IN y RR)
     (FORALL z (IMPLIES (IN z RR)
       (IMPLIES (<= x y) (IMPLIES (<= y z) (<= x z))))))))))
(warrant! 'rr-le-trans-c 'proof
  "Curried rr-le-trans: x<=y then y<=z gives x<=z.  Same fact, no AND antecedent.")

(support 'fun-apply-type-c
  '(FORALL f (FORALL A (FORALL B (FORALL x
     (IMPLIES (IN f (FUN A B)) (IMPLIES (IN x A) (IN (f x) B))))))))
(warrant! 'fun-apply-type-c 'proof
  "Curried fun-apply-type: f:A->B and x in A give f(x) in B.  No AND antecedent.")

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

;;; --------------------------------------------------------------------
;;; Sign of a difference, and sign of a product from the sign of a factor.
;;; The nonlinear product-sign facts (Farkas cannot see them) plus the
;;; difference<->order glue that the Caratheodory mean-value arc needs.
(support 'rr-le-diff-nonpos
  '(FORALL u (IMPLIES (IN u RR) (FORALL v (IMPLIES (IN v RR)
     (IMPLIES (<= u v) (<= (- u v) 0)))))))
(warrant! 'rr-le-diff-nonpos 'well-known "u<=v => u-v<=0.")
(support 'rr-lt-diff-pos
  '(FORALL u (IMPLIES (IN u RR) (FORALL v (IMPLIES (IN v RR)
     (IMPLIES (< u v) (< 0 (- v u))))))))
(warrant! 'rr-lt-diff-pos 'well-known "u<v => 0<v-u.")
(support 'rr-lt-diff-neg
  '(FORALL u (IMPLIES (IN u RR) (FORALL v (IMPLIES (IN v RR)
     (IMPLIES (< u v) (< (- u v) 0)))))))
(warrant! 'rr-lt-diff-neg 'well-known "u<v => u-v<0.")
(support 'rr-prod-nonpos-pos
  '(FORALL u (IMPLIES (IN u RR) (FORALL v (IMPLIES (IN v RR)
     (IMPLIES (AND (< 0 v) (<= (* u v) 0)) (<= u 0)))))))
(warrant! 'rr-prod-nonpos-pos 'well-known "u*v<=0 with v>0 forces u<=0.")
(support 'rr-prod-nonpos-neg
  '(FORALL u (IMPLIES (IN u RR) (FORALL v (IMPLIES (IN v RR)
     (IMPLIES (AND (< v 0) (<= (* u v) 0)) (<= 0 u)))))))
(warrant! 'rr-prod-nonpos-neg 'well-known "u*v<=0 with v<0 forces u>=0.")

;;; Negation and order: flips <=, and -u=0 forces u=0 (used by interior-min via
;;; the reduction to interior-max applied to -f).
(support 'rr-le-neg
  '(FORALL u (IMPLIES (IN u RR) (FORALL v (IMPLIES (IN v RR)
     (IMPLIES (<= u v) (<= (- v) (- u))))))))
(warrant! 'rr-le-neg 'well-known "u<=v => -v<=-u.")
(support 'rr-neg-eq-zero
  '(FORALL u (IMPLIES (IN u RR) (IMPLIES (= (- u) 0) (= u 0)))))
(warrant! 'rr-neg-eq-zero 'well-known "-u=0 => u=0.")

;;; --------------------------------------------------------------------
;;; Equality glue (symmetry / transitivity of the partial =) and the two RR
;;; arithmetic facts an eps-free cancellation argument needs (right cancellation,
;;; subtraction closure + its nonzero-difference companion).  All one-liners of
;;; the field axioms; named so a forward `fact' chains them (uniqueness of the
;;; Caratheodory derivative factor, differentiation.scm, is the first customer).
(support 'eq-sym
  '(FORALL a (FORALL b (IMPLIES (= a b) (= b a)))))
(warrant! 'eq-sym 'well-known "Symmetry of (partial) equality.")
(category! 'eq-sym 'plumbing)

(support 'eq-trans
  '(FORALL a (FORALL b (FORALL c (IMPLIES (= a b) (IMPLIES (= b c) (= a c)))))))
(warrant! 'eq-trans 'well-known "Transitivity of (partial) equality.")
(category! 'eq-trans 'plumbing)

(support 'rr-cancel-mul-right
  '(FORALL u (IMPLIES (IN u RR) (FORALL v (IMPLIES (IN v RR) (FORALL c (IMPLIES (IN c RR) (IMPLIES (NOT (= c 0)) (IMPLIES (= (* u c) (* v c)) (= u v))))))))))
(warrant! 'rr-cancel-mul-right 'well-known
  "u*c=v*c with c/=0 gives u=v (multiply by 1/c).  The right-factor companion of
   rr-cancel-mul-left (taylor-proof.scm).")
(category! 'rr-cancel-mul-right 'algebra)

(support 'rr-sub-in-rr
  '(FORALL u (IMPLIES (IN u RR) (FORALL v (IMPLIES (IN v RR) (IN (- u v) RR))))))
(warrant! 'rr-sub-in-rr 'well-known "RR is closed under subtraction.")
(category! 'rr-sub-in-rr 'plumbing)

(support 'rr-sub-ne-zero
  '(FORALL u (IMPLIES (IN u RR) (FORALL v (IMPLIES (IN v RR) (IMPLIES (NOT (= u v)) (NOT (= (- u v) 0))))))))
(warrant! 'rr-sub-ne-zero 'well-known "u/=v => u-v/=0.")
(category! 'rr-sub-ne-zero 'inequalities)

;;; -----------------------------------------------------------------------
;;; NN order facts for the Smith row/column clearing induction (clear-first-row).
;;; Elementary discreteness/positivity of NN; warranted well-known.
(support 'nn-le-succ-cases
  '(FORALL k (IMPLIES (IN k NN) (FORALL j (IMPLIES (IN j NN)
     (IMPLIES (<= j (succ k)) (OR (<= j k) (= j (succ k)))))))))
(warrant! 'nn-le-succ-cases 'well-known
  "j <= succ k => j <= k or j = succ k, for j,k in NN (discreteness of NN).")
(category! 'nn-le-succ-cases 'inequalities)

(support 'nn-not-le-zero-pos
  '(FORALL j (IMPLIES (IN j NN) (IMPLIES (<= 1 j) (NOT (<= j 0))))))
(warrant! 'nn-not-le-zero-pos 'well-known
  "1 <= j => not(j <= 0) for j in NN (0 is least, and j >= 1 > 0).")
(category! 'nn-not-le-zero-pos 'inequalities)

(support 'nn-le-imp-neq-succ
  '(FORALL k (IMPLIES (IN k NN) (FORALL j (IMPLIES (IN j NN)
     (IMPLIES (<= j k) (NOT (= j (succ k)))))))))
(warrant! 'nn-le-imp-neq-succ 'well-known
  "j <= k => j /= succ k for j,k in NN (succ k > k >= j).")
(category! 'nn-le-imp-neq-succ 'inequalities)

;;; Interval read-offs (forward direction of interval-membership), warranted
;;; well-known -- used to pull IN i NN / the bounds out of IN i (INTERVAL a b).
(support 'interval-elt-in-nn
  '(FORALL a (FORALL b (FORALL i (IMPLIES (IN i (INTERVAL a b)) (IN i NN)))))) 
(warrant! 'interval-elt-in-nn 'well-known "i in INTERVAL(a,b) => i in NN (interval-membership).")
(category! 'interval-elt-in-nn 'plumbing)

(support 'interval-lo
  '(FORALL a (FORALL b (FORALL i (IMPLIES (IN i (INTERVAL a b)) (<= a i))))))
(warrant! 'interval-lo 'well-known "i in INTERVAL(a,b) => a <= i (interval-membership).")
(category! 'interval-lo 'inequalities)

(support 'interval-hi
  '(FORALL a (FORALL b (FORALL i (IMPLIES (IN i (INTERVAL a b)) (<= i b))))))
(warrant! 'interval-hi 'well-known "i in INTERVAL(a,b) => i <= b (interval-membership).")
(category! 'interval-hi 'inequalities)

;;; Symmetry of disequality -- fact-able, needed early (Smith clearing uses it
;;; well before noetherian-maximal-proof, its former home).
(support 'neq-sym '(FORALL a (FORALL b (IMPLIES (NOT (= a b)) (NOT (= b a))))))
(warrant! 'neq-sym 'well-known "Symmetry of disequality.")
(category! 'neq-sym 'plumbing)

;;; NN-MINUS(succ z, 1) = z -- the monus predecessor of a successor.  Used by
;;; border-mult to reduce a shifted block index.
(support 'nn-minus-succ-1
  '(FORALL z (IMPLIES (IN z NN) (= (NN-MINUS (succ z) 1) z))))
(warrant! 'nn-minus-succ-1 'well-known
  "NN-MINUS(succ z, 1) = z: 1 <= succ z, so the monus is (succ z) - 1 = z
   (nn-minus-def + bt-succ-minus-1).")
(category! 'nn-minus-succ-1 'plumbing)

;;; Interval membership helpers for border-mult's block indexing.
(support 'one-in-interval
  '(FORALL n (IMPLIES (IN n NN) (IN 1 (INTERVAL 1 (succ n))))))
(warrant! 'one-in-interval 'well-known "1 in [1, succ n] (1 <= 1 <= succ n).")
(category! 'one-in-interval 'inequalities)

(support 'pred-in-interval
  '(FORALL p (FORALL i (IMPLIES (IN i (INTERVAL 1 (succ p))) (IMPLIES (NOT (= i 1))
     (IN (NN-MINUS i 1) (INTERVAL 1 p)))))))
(warrant! 'pred-in-interval 'well-known
  "i in [2, succ p] => i-1 in [1, p]: the monus predecessor of an index past 1
   lands in the block range.")
(category! 'pred-in-interval 'inequalities)

;;; succ of an index: stays in the shifted interval, and is never 1 (>= 2).
(support 'succ-in-interval
  '(FORALL q (FORALL z (IMPLIES (IN z (INTERVAL 1 q)) (IN (succ z) (INTERVAL 1 (succ q)))))))
(warrant! 'succ-in-interval 'well-known
  "z in [1,q] => succ z in [1, succ q] (2 <= succ z <= succ q).")
(category! 'succ-in-interval 'inequalities)

(support 'succ-not-one
  '(FORALL q (FORALL z (IMPLIES (IN z (INTERVAL 1 q)) (NOT (= (succ z) 1))))))
(warrant! 'succ-not-one 'well-known "z in [1,q] => succ z >= 2, so succ z /= 1.")
(category! 'succ-not-one 'inequalities)
