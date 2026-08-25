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

;;; nn-le-trans -- GONE 2026-08-03, migration complete.
;;;
;;; It was stated with NO guards, which is stronger than the axioms license:
;;; nothing constrains `<=' off the numeric chain, so it asserted transitivity of
;;; the order on arbitrary objects, and the library's own trusted `ineq' oracle
;;; refuses to certify an atom without a literal (IN t RR).  The name compounded
;;; it -- despite the `nn-' prefix the statement mentioned NN nowhere.
;;;
;;; The guarded replacement `nn-le-trans-guarded' is PROVEN `modulo 0'
;;; (theorem-library/nn-order-basics.scm) and all twelve callers now cite it:
;;; nn-pairing (3), nn-order-proof (2), nn-order-basics (1), interval-widen (1),
;;; smith-staircase-proof (4), smith-diagonalization-proof (1).
;;;
;;; THE MIGRATION WAS THE POINT.  Guarding transitivity is what exposed the
;;; proofs that were chaining through terms they had never typed, and every
;;; single site it broke was such a proof:
;;;   nn-add-le-mono      chained through a_+b_ and succ(a_+c_) untyped; fixing
;;;                       it also brought back nnpair-diag-bound and
;;;                       nnpair-cross, which had cascaded from it.
;;;   interval-widen      chained through BOTH b and c untyped -- nothing in its
;;;                       statement typed either; now guarded on both.
;;;   smith-staircase     succ kp / succ p / succ q, and the interval indices,
;;;   smith-diagonalization  never named as naturals.
;;; Each repair is one or two `fact' lines landing the typing before the
;;; citation.  Nothing needed new mathematics.

;;; rr-le-trans and rr-le-trans-c MOVED 2026-08-02 to
;;; theorem-library/nn-order-basics.scm, where all three are PROVEN from the
;;; primitive rr-leq-transitive.  rr-le-trans-c was a fourth support claiming the
;;; `proof' warrant tier with no machine proof.  nn-le-trans CHANGED CONTENT: it
;;; was stated with NO guards, which is stronger than the axioms license (nothing
;;; constrains `<=' off the numeric chain) and inconsistent with how `ineq'
;;; treats order atoms; it is now guarded on NN, which is what its name always
;;; implied and its formula never said.

;;; NINETEEN SUPPORTS MOVED 2026-08-16 to theorem-library/rr-order-basics.scm,
;;; where every one of them is PROVEN `modulo 0':
;;;   chaining      rr-lt-trans  rr-lt-le-trans  rr-le-lt-trans  rr-lt-implies-le
;;;   trichotomy    rr-lt-trichotomy
;;;   differences   rr-le-diff-nonpos  rr-lt-diff-pos  rr-lt-diff-neg
;;;                 rr-le-neg  rr-neg-eq-zero  rr-sub-ne-zero
;;;   sums          rr-le-add  rr-lt-add  rr-add-nonneg
;;;                 rr-le-from-diff-nonneg  rr-double-nonneg
;;;   products      rr-le-scale-nonneg  rr-lt-scale-pos  rr-sq-nonneg
;;;                 rr-cancel-mul-right
;;; (Trichotomy had itself been moved HERE on 2026-08-04 out of
;;; theorem-library/deriv-constant-proof.scm, for the same reason: a fact
;;; declared inside a calculus proof is invisible to everything above it.)
;;;
;;; They were `well-known' supports, and this file's header called them the
;;; specification of "the future inequality decision procedure".  That procedure
;;; now exists (structure-library/ineq-oracle.scm) and reads `<' natively, and
;;; number-systems.scm has been `primitive' since 2026-08-01 -- so most of them
;;; are ONE `ineq' call after the binders are peeled, and the spec has become the
;;; output.  The four that are NOT linear (the scaling laws, the square, the
;;; cancellation) go through `rr-no-zero-divisors', proved there from
;;; rr-recip-closed / rr-recip-inverse: what they need is not the order axioms
;;; but the fact that RR is a FIELD.
;;;
;;; THE THREE ABS SUPPORTS ARE GONE TOO (2026-08-17), and the paragraph that
;;; stood here explaining why they could not go is the point.  It read: `rr-le-abs'
;;; (x <= |x|), `rr-abs-bound' (|x| <= c iff -c <= x <= c) and
;;; `rr-abs-reverse-triangle' "are NOT derivable from the abs axioms in
;;; number-systems.scm and are not oversights: those five axioms (closed /
;;; nonneg / zero-iff / triangle / multiplicative) do not determine abs.
;;; x |-> sqrt(|x|) satisfies all five, and falsifies rr-le-abs and rr-abs-bound
;;; at x = 2.  Pinning |x| to one of x, -x needs an axiom the theory does not
;;; state."  That diagnosis was right, and the cure was not another axiom: the
;;; missing statement is the DEFINITION of abs, which number-systems.scm now
;;; carries as `rr-abs-def' (definition by cases on the sign).  All three are
;;; PROVEN `modulo 0' in theorem-library/rr-abs-basics.scm, along with the five
;;; axioms themselves, which are deleted from number-systems.scm.
;;; The product-SIGN facts (rr-prod-nonpos-pos / -neg) are derivable and simply
;;; not done yet.

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



;;; -----------------------------------------------------------------------
;;; Adding inequalities -- the central epsilon-argument move.




;;; -----------------------------------------------------------------------
;;; Scaling by a nonnegative / positive factor.



;;; -----------------------------------------------------------------------
;;; Absolute value: NOTHING remains here.  rr-le-abs, rr-abs-bound and
;;; rr-abs-reverse-triangle were the three supports of this section; all three
;;; are PROVEN in theorem-library/rr-abs-basics.scm (see the note in this file's
;;; header).

;;; -----------------------------------------------------------------------
;;; Squares are nonnegative, and the two order/arithmetic glue moves that
;;; turn a sum-of-squares certificate into a goal `<='.  Together with crs
;;; (which verifies the polynomial identity behind the certificate) these
;;; close every elementary polynomial inequality, e.g.
;;;   x*y <= x^2 + y^2   via   2*(x^2+y^2-x*y) = (x-y)^2 + x^2 + y^2.
;;; The missing real-line counterpart of cc-self-conj-nonneg (0 <= a*conj a).




;;; --------------------------------------------------------------------
;;; Sign of a difference, and sign of a product from the sign of a factor.
;;; The nonlinear product-sign facts (Farkas cannot see them) plus the
;;; difference<->order glue that the Caratheodory mean-value arc needs.
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
(topic! 'co-le-trans 'inequalities)
(support 'co-lt-trans
  '(FORALL a (FORALL b (FORALL c (IMPLIES (< a b) (IMPLIES (< b c) (< a c)))))))
(warrant! 'co-lt-trans 'well-known "a<b then b<c gives a<c.")
(topic! 'co-lt-trans 'inequalities)
(support 'co-le-lt-trans
  '(FORALL a (FORALL b (FORALL c (IMPLIES (<= a b) (IMPLIES (< b c) (< a c)))))))
(warrant! 'co-le-lt-trans 'well-known "a<=b then b<c gives a<c.")
(topic! 'co-le-lt-trans 'inequalities)
(support 'co-lt-le-trans
  '(FORALL a (FORALL b (FORALL c (IMPLIES (< a b) (IMPLIES (<= b c) (< a c)))))))
(warrant! 'co-lt-le-trans 'well-known "a<b then b<=c gives a<c.")
(topic! 'co-lt-le-trans 'inequalities)
(support 'co-le-eq-trans
  '(FORALL a (FORALL b (FORALL c (IMPLIES (<= a b) (IMPLIES (= b c) (<= a c)))))))
(warrant! 'co-le-eq-trans 'well-known "a<=b then b=c gives a<=c.")
(topic! 'co-le-eq-trans 'inequalities)
(support 'co-lt-eq-trans
  '(FORALL a (FORALL b (FORALL c (IMPLIES (< a b) (IMPLIES (= b c) (< a c)))))))
(warrant! 'co-lt-eq-trans 'well-known "a<b then b=c gives a<c.")
(topic! 'co-lt-eq-trans 'inequalities)
(support 'co-eq-le-trans
  '(FORALL a (FORALL b (FORALL c (IMPLIES (= a b) (IMPLIES (<= b c) (<= a c)))))))
(warrant! 'co-eq-le-trans 'well-known "a=b then b<=c gives a<=c.")
(topic! 'co-eq-le-trans 'inequalities)
(support 'co-eq-lt-trans
  '(FORALL a (FORALL b (FORALL c (IMPLIES (= a b) (IMPLIES (< b c) (< a c)))))))
(warrant! 'co-eq-lt-trans 'well-known "a=b then b<c gives a<c.")
(topic! 'co-eq-lt-trans 'inequalities)

;;; Discreteness of NN: a nonzero natural is strictly positive.  0<=k (nn-zero-le)
;;; and k/=0 give 0<k.  This is the single fact that made sqrt2 ASSERT nn-lt-double
;;; (trust:reference); as a well-known support it lets `calc' PROVE nn-lt-double.
(support 'nn-pos-of-nonzero
  '(FORALL k (IMPLIES (IN k NN) (IMPLIES (NOT (= k 0)) (< 0 k)))))
(warrant! 'nn-pos-of-nonzero 'well-known
  "k in NN, k/=0 => 0<k: 0<=k (nn-zero-le) and 0/=k give the strict inequality.")
(topic! 'nn-pos-of-nonzero 'inequalities)

;;; rr-cancel-mul-right MOVED 2026-08-16 to theorem-library/rr-order-basics.scm,
;;; where it is PROVEN `modulo 0' from rr-no-zero-divisors.  Its warrant here was
;;; "multiply by 1/c" -- the derivation, written down and never run.  (Its
;;; left-factor twin rr-cancel-mul-left is still asserted, inside
;;; theorem-library/taylor-proof.scm; the same four lines would do it.)

;;; rr-sub-in-rr MOVED 2026-08-01 to theorem-library/binary-minus-laws.scm, where
;;; it is PROVEN rather than asserted.  It was a `well-known' support here, and
;;; looked like a triviality restating rr-add-closed; it was in fact the only
;;; constraint in the tree on the binary `(- u v)', which had no defining axiom
;;; until number-systems.scm gained `binary-minus-def' the same day.  Its one
;;; consumer (theorem-library/differentiation.scm) loads after the proof.


;;; -----------------------------------------------------------------------
;;; NN order facts for the Smith row/column clearing induction (clear-first-row).
;;; Elementary discreteness/positivity of NN; warranted well-known.
;;; nn-le-succ-cases MOVED 2026-08-24 to theorem-library/nn-order-ord.scm, where
;;; it is PROVEN `modulo 0'.  Its warrant here read "discreteness of NN", which
;;; is true and is not an NN axiom: NN's base (nn-zero-in, nn-succ-closed,
;;; nn-induction) does not state it and cannot prove it.  The ordinals do.

(support 'nn-not-le-zero-pos
  '(FORALL j (IMPLIES (IN j NN) (IMPLIES (<= 1 j) (NOT (<= j 0))))))
(warrant! 'nn-not-le-zero-pos 'well-known
  "1 <= j => not(j <= 0) for j in NN (0 is least, and j >= 1 > 0).")
(topic! 'nn-not-le-zero-pos 'inequalities)


(support 'nn-pos-is-succ
  '(FORALL n (IMPLIES (IN n NN) (IMPLIES (<= 1 n)
     (FORSOME q (AND (IN q NN) (= n (succ q))))))))
(warrant! 'nn-pos-is-succ 'well-known "a positive nat is a successor (n>=1 => n = succ(n-1), n-1 in NN).")
(topic! 'nn-pos-is-succ 'inequalities)

;;; nn-le-imp-neq-succ MOVED 2026-08-24 to theorem-library/nn-order-ord.scm,
;;; where it is PROVEN `modulo 0'.  It is the fact under `nn-succ-nonzero'.

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
(topic! 'nn-minus-succ-1 'plumbing)

;;; Interval membership helpers for border-mult's block indexing.
(support 'one-in-interval
  '(FORALL n (IMPLIES (IN n NN) (IN 1 (INTERVAL 1 (succ n))))))
(warrant! 'one-in-interval 'well-known "1 in [1, succ n] (1 <= 1 <= succ n).")
(topic! 'one-in-interval 'inequalities)

(support 'pred-in-interval
  '(FORALL p (FORALL i (IMPLIES (IN i (INTERVAL 1 (succ p))) (IMPLIES (NOT (= i 1))
     (IN (NN-MINUS i 1) (INTERVAL 1 p)))))))
(warrant! 'pred-in-interval 'well-known
  "i in [2, succ p] => i-1 in [1, p]: the monus predecessor of an index past 1
   lands in the block range.")
(topic! 'pred-in-interval 'inequalities)

;;; succ of an index: stays in the shifted interval, and is never 1 (>= 2).
(support 'succ-in-interval
  '(FORALL q (FORALL z (IMPLIES (IN z (INTERVAL 1 q)) (IN (succ z) (INTERVAL 1 (succ q)))))))
(warrant! 'succ-in-interval 'well-known
  "z in [1,q] => succ z in [1, succ q] (2 <= succ z <= succ q).")
(topic! 'succ-in-interval 'inequalities)

(support 'succ-not-one
  '(FORALL q (FORALL z (IMPLIES (IN z (INTERVAL 1 q)) (NOT (= (succ z) 1))))))
(warrant! 'succ-not-one 'well-known "z in [1,q] => succ z >= 2, so succ z /= 1.")
(topic! 'succ-not-one 'inequalities)

;;; monus-by-1 is injective on indices >= 1 (needed to compare BORDER's block to
;;; IDENTMAT's Kronecker delta in border-identity).
(support 'nn-minus-1-inj
  '(FORALL i (FORALL j (IMPLIES (IN i NN) (IMPLIES (IN j NN)
     (IMPLIES (<= 1 i) (IMPLIES (<= 1 j)
       (IMPLIES (NOT (= i j)) (NOT (= (NN-MINUS i 1) (NN-MINUS j 1)))))))))))
(warrant! 'nn-minus-1-inj 'well-known
  "i /= j and 1 <= i,j => i-1 /= j-1 (monus by 1 is injective on [1,inf)).")
(topic! 'nn-minus-1-inj 'inequalities)

;;; succ(i-1) = i for i >= 1 -- the inverse of monus-by-1 on positive indices;
;;; used to see that BORDER(b, SUBMAT(C)) restores C's lower-right block.
(support 'succ-nn-minus-1
  '(FORALL i (IMPLIES (IN i NN) (IMPLIES (<= 1 i) (= (succ (NN-MINUS i 1)) i)))))
(warrant! 'succ-nn-minus-1 'well-known
  "succ(i-1) = i for i >= 1 (monus by 1 then succ is the identity on [1,inf)).")
(topic! 'succ-nn-minus-1 'inequalities)

;;; -----------------------------------------------------------------------
;;; Interval membership introduction + the NN trichotomy step the rank bound
;;; (Prop 3.41) needs to turn NOT(m <= n) into a legal row index succ n <= m.

(support 'interval-mem-intro
  '(FORALL a (FORALL b (FORALL i (IMPLIES (IN i NN)
     (IMPLIES (<= a i) (IMPLIES (<= i b) (IN i (INTERVAL a b)))))))))
(warrant! 'interval-mem-intro 'proof
  "Converse of interval-lo/interval-hi: i in NN with a<=i<=b lies in INTERVAL(a,b)
   (the right-to-left direction of interval-membership's SEP iff).")
(topic! 'interval-mem-intro 'plumbing)

(support 'nn-not-le-succ-le
  '(FORALL m (IMPLIES (IN m NN) (FORALL n (IMPLIES (IN n NN)
     (IMPLIES (NOT (<= m n)) (<= (succ n) m)))))))
(warrant! 'nn-not-le-succ-le 'well-known
  "NN is totally ordered and discrete: not(m<=n) gives n<m, hence succ n <= m.")
(topic! 'nn-not-le-succ-le 'inequalities)

;;; nn-one-le-succ MOVED 2026-08-24 to theorem-library/nn-order-ord.scm, where
;;; it is PROVEN `modulo 0' (nn-succ-mono at 0 <= n, then 1 = succ 0).

;; n <= succ n.  Was declared inside theorem-library/noetherian-maximal-proof.scm
;; (via add-to-pss) -- a plumbing fact hiding in a proof file, and unavailable to
;; anything that loads before it (e.g. the span-bricks).  Moved here 2026-07-10,
;; and MOVED AGAIN 2026-08-24 to theorem-library/nn-order-ord.scm, where it is
;; PROVEN `modulo 0' from ord-succ-above.  It was the most-cited support of the
;; NN order block (27 citations).

;; nn-one-in (1 in NN) MOVED 2026-08-24 to theorem-library/nn-order-ord.scm.
;; Its warrant WAS the derivation -- "1 = succ 0 in NN" -- i.e. nn-zero-in,
;; nn-succ-closed and one ground `arith' step, written down and never run.

(support 'one-in-interval-1 '(IN 1 (INTERVAL 1 1)))
(warrant! 'one-in-interval-1 'proof
  "1 in INTERVAL(1,1): 1 in NN and 1<=1<=1.  The column index of a column vector.")
(topic! 'one-in-interval-1 'plumbing)

;;; -----------------------------------------------------------------------
;;; succ is monotone and reflects <= ; 0 is least.  The Smith staircase
;;; induction needs all three to carry its index bound k <= m across a
;;; BORDER step (k' <= k  <=>  succ k' <= succ k).

;;; nn-zero-le and nn-succ-mono MOVED 2026-08-24 to
;;; theorem-library/nn-order-ord.scm, both PROVEN `modulo 0'.  nn-zero-le is
;;; ord-zero-least read through ord-le-nn-compat; nn-succ-mono is
;;; ord-succ-immediate with nn-le-imp-neq-succ supplying its disequality.
;;;
;;; nn-succ-le-cancel below did NOT move, and the reason is a measurement, not
;;; an obstacle: no bill in the library names it (its one citation,
;;; smith-staircase-proof, is not itself proven), so proving it would move
;;; nothing.  The neighbours that WOULD pay, measured 2026-08-24 over the 702
;;; bills, are
;;;
;;;   nn-not-le-zero-pos   named in 30 bills, SOLE unwarranted leaf of 3
;;;   nn-not-le-succ-le    named in 24, sole leaf of 1
;;;   nn-succ-le-antisym   named in 22, sole leaf of 0 (shadowed everywhere)
;;;
;;; and the first of those is driven in
;;; prove-scripts/drives/nn-not-le-zero-pos-drive.scm.  The ordinal route
;;; reaches all three; `nn-pos-of-nonzero' (4 bills, sole leaf of 0) is cheaper
;;; still, being nothing but the `<' unfold over the now-proven nn-zero-le.

(support 'nn-succ-le-cancel
  '(FORALL a (IMPLIES (IN a NN) (FORALL b (IMPLIES (IN b NN)
     (IMPLIES (<= (succ a) (succ b)) (<= a b)))))))
(warrant! 'nn-succ-le-cancel 'well-known "succ a <= succ b => a <= b.")
(topic! 'nn-succ-le-cancel 'inequalities)

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
(topic! 'recip-defined-nonzero 'inequalities)

;; Multiplication is STRICT: a defined product has both factors defined.  Only
;; DEFINEDNESS propagates to the factors -- membership does not (i*(-i)=1 in RR,
;; i not in RR) -- so the conclusion is (= a a) AND (= b b), never (IN a RR) etc.
(support 'mul-defined-factors
  '(FORALL a (FORALL b (IMPLIES (= (* a b) (* a b)) (AND (= a a) (= b b))))))
(warrant! 'mul-defined-factors 'informal
  "Multiplication is strict: a defined product a*b has both factors defined.  Definedness (= t t) propagates, NOT membership.")
(topic! 'mul-defined-factors 'algebra)
