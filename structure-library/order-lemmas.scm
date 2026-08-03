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
;;; All over RR.  Bound vars avoid the case-fold traps as they stood when this
;;; was written: NOT `a' (the carrier accessor, `A' then, `CARR' now), NOT `e'
;;; (the identity accessor, `E' then, `IDEN' now), NOT `n'/`N' collisions; reals are
;;; x y z u v, a nonneg/pos factor is c, a bound is bnd.
;;;
;;; Library-build phase: warranted well-known [[feedback-library-axioms-fine]].
;;; These are exactly the cases the linear-arithmetic oracle must also decide,
;;; so they double as its specification.  Dependencies: number-systems.scm
;;; (RR, <=, +, *, -, abs), order-predicates.scm (<, POS-RR).

;;; -----------------------------------------------------------------------
;;; Chaining: mixed strict / non-strict transitivity, and weakening.

;;; nn-le-trans -- RESTORED unguarded 2026-08-02, deliberately and temporarily.
;;;
;;; It is stated with NO guards, which is stronger than the axioms license:
;;; nothing constrains `<=' off the numeric chain, so this asserts transitivity
;;; of the order relation on arbitrary objects.  It is consistent (read `<=' as
;;; the real order and nothing else and it holds vacuously off RR) but
;;; unlicensed, and it contradicts how the library's own trusted oracle behaves
;;; -- `ineq' refuses to certify an atom without a literal (IN t RR).  The name
;;; compounds it: despite the `nn-' prefix the statement mentions NN nowhere.
;;;
;;; The guarded replacement IS PROVEN, `modulo 0', as `nn-le-trans-guarded' in
;;; theorem-library/nn-order-basics.scm.  Swapping it in is a MIGRATION, not a
;;; rename: guarding it broke four proofs that were chaining transitivity
;;; through terms they had never typed -- always a succ(...) or a sum of things
;;; already in hand.  Three are now fixed (nn-order-basics' nn-le-add-right,
;;; nn-order-proof's nn-le-add, two sites in nn-pairing); what remains is
;;; nn-pairing's nn-add-le-mono / nnpair-diag-bound / nnpair-cross.  Finish
;;; those, point the callers at nn-le-trans-guarded, and delete this.
(support 'nn-le-trans
  '(FORALL a (FORALL b (FORALL c (IMPLIES (<= a b) (IMPLIES (<= b c) (<= a c)))))))
(warrant! 'nn-le-trans 'well-known "<= is transitive (a<=b, b<=c => a<=c).  UNGUARDED -- see the note above; superseded by the proven nn-le-trans-guarded once its callers are migrated.")
(category! 'nn-le-trans 'inequalities)

;;; rr-le-trans and rr-le-trans-c MOVED 2026-08-02 to
;;; theorem-library/nn-order-basics.scm, where all three are PROVEN from the
;;; primitive rr-leq-transitive.  rr-le-trans-c was a fourth support claiming the
;;; `proof' warrant tier with no machine proof.  nn-le-trans CHANGED CONTENT: it
;;; was stated with NO guards, which is stronger than the axioms license (nothing
;;; constrains `<=' off the numeric chain) and inconsistent with how `ineq'
;;; treats order atoms; it is now guarded on NN, which is what its name always
;;; implied and its formula never said.

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

;;; nn-in-rr MOVED 2026-08-02 to theorem-library/nn-order-basics.scm, where it is
;;; PROVEN.  Its warrant here claimed the top tier `proof' and then described the
;;; derivation -- the inclusion chain composed -- which nobody had run.  Third of
;;; that kind found in this file, after nn-le-refl and nn-pair-upper-bound.

;;; nn-le-refl and nn-pair-upper-bound MOVED 2026-08-02 to
;;; theorem-library/nn-order-basics.scm, where they are PROVEN.  Both were
;;; supports here carrying the top warrant tier `proof' while naming no machine
;;; proof -- nn-le-refl's warrant WAS its derivation (nn-in-rr, then
;;; rr-leq-reflexive) and nn-pair-upper-bound's was "take c = a + b"; neither
;;; had been run.  nn-le-add-right (m <= m + n, by induction on n) is proved
;;; there too and is what the pair bound now rests on.


;; Curried siblings (no AND antecedent) so a forward `fact' discharges each
;; guard from context without a cut -- the shape interactive assembly wants.

;;; fun-apply-type-c MOVED 2026-08-02 to theorem-library/fun-apply-type-proof.scm,
;;; where it is PROVEN `modulo 0' from the base axiom fun-codomain-iff.  It was a
;;; support here claiming the top warrant tier `proof' while naming no machine
;;; proof.  Kept CURRIED there for the same reason it was curried here: `fact'
;;; peels and detaches both hypotheses in one call, where a conjunctive
;;; antecedent would make every caller assemble the AND by hand.

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
;;; -----------------------------------------------------------------------
;;; calc-chain composition lemmas: UNTYPED CURRIED transitivity for every
;;; (relation, relation) combination the `calc' order composer folds through.
;;; They mirror eq-trans / nn-le-trans (untyped, curried, well-known) so a
;;; forward `fact' discharges both order antecedents from context with no RR
;;; typing guard.  The `co-' (compose) prefix keeps them off the surface.
(support 'co-le-trans
  '(FORALL a (FORALL b (FORALL c (IMPLIES (<= a b) (IMPLIES (<= b c) (<= a c)))))))
(warrant! 'co-le-trans 'well-known "a<=b then b<=c gives a<=c.")
(category! 'co-le-trans 'inequalities)
(support 'co-lt-trans
  '(FORALL a (FORALL b (FORALL c (IMPLIES (< a b) (IMPLIES (< b c) (< a c)))))))
(warrant! 'co-lt-trans 'well-known "a<b then b<c gives a<c.")
(category! 'co-lt-trans 'inequalities)
(support 'co-le-lt-trans
  '(FORALL a (FORALL b (FORALL c (IMPLIES (<= a b) (IMPLIES (< b c) (< a c)))))))
(warrant! 'co-le-lt-trans 'well-known "a<=b then b<c gives a<c.")
(category! 'co-le-lt-trans 'inequalities)
(support 'co-lt-le-trans
  '(FORALL a (FORALL b (FORALL c (IMPLIES (< a b) (IMPLIES (<= b c) (< a c)))))))
(warrant! 'co-lt-le-trans 'well-known "a<b then b<=c gives a<c.")
(category! 'co-lt-le-trans 'inequalities)
(support 'co-le-eq-trans
  '(FORALL a (FORALL b (FORALL c (IMPLIES (<= a b) (IMPLIES (= b c) (<= a c)))))))
(warrant! 'co-le-eq-trans 'well-known "a<=b then b=c gives a<=c.")
(category! 'co-le-eq-trans 'inequalities)
(support 'co-lt-eq-trans
  '(FORALL a (FORALL b (FORALL c (IMPLIES (< a b) (IMPLIES (= b c) (< a c)))))))
(warrant! 'co-lt-eq-trans 'well-known "a<b then b=c gives a<c.")
(category! 'co-lt-eq-trans 'inequalities)
(support 'co-eq-le-trans
  '(FORALL a (FORALL b (FORALL c (IMPLIES (= a b) (IMPLIES (<= b c) (<= a c)))))))
(warrant! 'co-eq-le-trans 'well-known "a=b then b<=c gives a<=c.")
(category! 'co-eq-le-trans 'inequalities)
(support 'co-eq-lt-trans
  '(FORALL a (FORALL b (FORALL c (IMPLIES (= a b) (IMPLIES (< b c) (< a c)))))))
(warrant! 'co-eq-lt-trans 'well-known "a=b then b<c gives a<c.")
(category! 'co-eq-lt-trans 'inequalities)

;;; Discreteness of NN: a nonzero natural is strictly positive.  0<=k (nn-zero-le)
;;; and k/=0 give 0<k.  This is the single fact that made sqrt2 ASSERT nn-lt-double
;;; (trust:reference); as a well-known support it lets `calc' PROVE nn-lt-double.
(support 'nn-pos-of-nonzero
  '(FORALL k (IMPLIES (IN k NN) (IMPLIES (NOT (= k 0)) (< 0 k)))))
(warrant! 'nn-pos-of-nonzero 'well-known
  "k in NN, k/=0 => 0<k: 0<=k (nn-zero-le) and 0/=k give the strict inequality.")
(category! 'nn-pos-of-nonzero 'inequalities)

(support 'rr-cancel-mul-right
  '(FORALL u (IMPLIES (IN u RR) (FORALL v (IMPLIES (IN v RR) (FORALL c (IMPLIES (IN c RR) (IMPLIES (NOT (= c 0)) (IMPLIES (= (* u c) (* v c)) (= u v))))))))))
(warrant! 'rr-cancel-mul-right 'well-known
  "u*c=v*c with c/=0 gives u=v (multiply by 1/c).  The right-factor companion of
   rr-cancel-mul-left (taylor-proof.scm).")
(category! 'rr-cancel-mul-right 'algebra)

;;; rr-sub-in-rr MOVED 2026-08-01 to theorem-library/binary-minus-laws.scm, where
;;; it is PROVEN rather than asserted.  It was a `well-known' support here, and
;;; looked like a triviality restating rr-add-closed; it was in fact the only
;;; constraint in the tree on the binary `(- u v)', which had no defining axiom
;;; until number-systems.scm gained `binary-minus-def' the same day.  Its one
;;; consumer (theorem-library/differentiation.scm) loads after the proof.

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


(support 'nn-pos-is-succ
  '(FORALL n (IMPLIES (IN n NN) (IMPLIES (<= 1 n)
     (FORSOME q (AND (IN q NN) (= n (succ q))))))))
(warrant! 'nn-pos-is-succ 'well-known "a positive nat is a successor (n>=1 => n = succ(n-1), n-1 in NN).")
(category! 'nn-pos-is-succ 'inequalities)

(support 'nn-le-imp-neq-succ
  '(FORALL k (IMPLIES (IN k NN) (FORALL j (IMPLIES (IN j NN)
     (IMPLIES (<= j k) (NOT (= j (succ k)))))))))
(warrant! 'nn-le-imp-neq-succ 'well-known
  "j <= k => j /= succ k for j,k in NN (succ k > k >= j).")
(category! 'nn-le-imp-neq-succ 'inequalities)

;;; Interval read-offs (forward direction of interval-membership), warranted
;;; well-known -- used to pull IN i NN / the bounds out of IN i (INTERVAL a b).
 
;;; Symmetry of disequality -- fact-able, needed early (Smith clearing uses it
;;; well before noetherian-maximal-proof, its former home).
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

;;; monus-by-1 is injective on indices >= 1 (needed to compare BORDER's block to
;;; IDENTMAT's Kronecker delta in border-identity).
(support 'nn-minus-1-inj
  '(FORALL i (FORALL j (IMPLIES (IN i NN) (IMPLIES (IN j NN)
     (IMPLIES (<= 1 i) (IMPLIES (<= 1 j)
       (IMPLIES (NOT (= i j)) (NOT (= (NN-MINUS i 1) (NN-MINUS j 1)))))))))))
(warrant! 'nn-minus-1-inj 'well-known
  "i /= j and 1 <= i,j => i-1 /= j-1 (monus by 1 is injective on [1,inf)).")
(category! 'nn-minus-1-inj 'inequalities)

;;; succ(i-1) = i for i >= 1 -- the inverse of monus-by-1 on positive indices;
;;; used to see that BORDER(b, SUBMAT(C)) restores C's lower-right block.
(support 'succ-nn-minus-1
  '(FORALL i (IMPLIES (IN i NN) (IMPLIES (<= 1 i) (= (succ (NN-MINUS i 1)) i)))))
(warrant! 'succ-nn-minus-1 'well-known
  "succ(i-1) = i for i >= 1 (monus by 1 then succ is the identity on [1,inf)).")
(category! 'succ-nn-minus-1 'inequalities)

;;; -----------------------------------------------------------------------
;;; Interval membership introduction + the NN trichotomy step the rank bound
;;; (Prop 3.41) needs to turn NOT(m <= n) into a legal row index succ n <= m.

(support 'interval-mem-intro
  '(FORALL a (FORALL b (FORALL i (IMPLIES (IN i NN)
     (IMPLIES (<= a i) (IMPLIES (<= i b) (IN i (INTERVAL a b)))))))))
(warrant! 'interval-mem-intro 'proof
  "Converse of interval-lo/interval-hi: i in NN with a<=i<=b lies in INTERVAL(a,b)
   (the right-to-left direction of interval-membership's SEP iff).")
(category! 'interval-mem-intro 'plumbing)

(support 'nn-not-le-succ-le
  '(FORALL m (IMPLIES (IN m NN) (FORALL n (IMPLIES (IN n NN)
     (IMPLIES (NOT (<= m n)) (<= (succ n) m)))))))
(warrant! 'nn-not-le-succ-le 'well-known
  "NN is totally ordered and discrete: not(m<=n) gives n<m, hence succ n <= m.")
(category! 'nn-not-le-succ-le 'inequalities)

(support 'nn-one-le-succ
  '(FORALL n (IMPLIES (IN n NN) (<= 1 (succ n)))))
(warrant! 'nn-one-le-succ 'well-known "1 <= succ n for every n in NN.")
(category! 'nn-one-le-succ 'inequalities)

;; n <= succ n.  Was declared inside theorem-library/noetherian-maximal-proof.scm
;; (via add-to-pss) -- a plumbing fact hiding in a proof file, and unavailable to
;; anything that loads before it (e.g. the span-bricks).  Moved here 2026-07-10.
(support 'nn-le-succ
  '(FORALL k (IMPLIES (IN k NN) (<= k (succ k)))))
(warrant! 'nn-le-succ 'well-known "k <= succ k on NN.")
(category! 'nn-le-succ 'plumbing)

;; 1 in NN.  Needed for nn-le-refl at 1 (the <= 1 1 that BLOCK/SNOC typings owe).
(support 'nn-one-in '(IN 1 NN))
(warrant! 'nn-one-in 'well-known "1 = succ 0 in NN.")
(category! 'nn-one-in 'plumbing)

(support 'one-in-interval-1 '(IN 1 (INTERVAL 1 1)))
(warrant! 'one-in-interval-1 'proof
  "1 in INTERVAL(1,1): 1 in NN and 1<=1<=1.  The column index of a column vector.")
(category! 'one-in-interval-1 'plumbing)

;;; -----------------------------------------------------------------------
;;; succ is monotone and reflects <= ; 0 is least.  The Smith staircase
;;; induction needs all three to carry its index bound k <= m across a
;;; BORDER step (k' <= k  <=>  succ k' <= succ k).

(support 'nn-zero-le
  '(FORALL n (IMPLIES (IN n NN) (<= 0 n))))
(warrant! 'nn-zero-le 'well-known "0 is the least natural number.")
(category! 'nn-zero-le 'inequalities)

(support 'nn-succ-mono
  '(FORALL a (IMPLIES (IN a NN) (FORALL b (IMPLIES (IN b NN)
     (IMPLIES (<= a b) (<= (succ a) (succ b))))))))
(warrant! 'nn-succ-mono 'well-known "a <= b => succ a <= succ b.")
(category! 'nn-succ-mono 'inequalities)

(support 'nn-succ-le-cancel
  '(FORALL a (IMPLIES (IN a NN) (FORALL b (IMPLIES (IN b NN)
     (IMPLIES (<= (succ a) (succ b)) (<= a b)))))))
(warrant! 'nn-succ-le-cancel 'well-known "succ a <= succ b => a <= b.")
(category! 'nn-succ-le-cancel 'inequalities)

;;; --- reverse-direction DEFINEDNESS facts (added 2026-07-27) ------------------
;;; The forward recip/mul axioms (rr-recip-closed, rr-recip-inverse) only run
;;; q/=0 => ...; these run the other way, RECOVERING q/=0 from the fact that a term
;;; mentioning recip(q) is defined.  Stated on the definedness predicate (= t t)
;;; (primitive-inferences.scm: "(= t t) IS the definedness predicate"), NOT on
;;; membership -- the membership form is UNSOUND (i*(-i)=1 in RR yet i not in RR).

;; recip is partial on the nonzero reals (RECIP : NON-ZERO -> NON-ZERO, field.scm),
;; so recip(0) is undefined; a DEFINED recip(q) therefore forces q /= 0.
(support 'recip-defined-nonzero
  '(FORALL q (IMPLIES (= (recip q) (recip q)) (NOT (= q 0)))))
(warrant! 'recip-defined-nonzero 'informal
  "recip is defined only off zero (RECIP : NON-ZERO -> NON-ZERO); a defined recip(q) forces q /= 0.")
(category! 'recip-defined-nonzero 'inequalities)

;; Multiplication is STRICT: a defined product has both factors defined.  Only
;; DEFINEDNESS propagates to the factors -- membership does not (i*(-i)=1 in RR,
;; i not in RR) -- so the conclusion is (= a a) AND (= b b), never (IN a RR) etc.
(support 'mul-defined-factors
  '(FORALL a (FORALL b (IMPLIES (= (* a b) (* a b)) (AND (= a a) (= b b))))))
(warrant! 'mul-defined-factors 'informal
  "Multiplication is strict: a defined product a*b has both factors defined.  Definedness (= t t) propagates, NOT membership.")
(category! 'mul-defined-factors 'algebra)
