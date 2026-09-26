;;; =====================================================================
;;; NOT PROVEN HERE: `zz-division', the division algorithm on ZZ.
;;;
;;; This block is the statement and the step plan.  It is written out because
;;; the block above exists FOR it: `zz-is-euclidean-ring' (numeric-instances.scm
;;; :317) is the library's last `trust: none' bill -- it enters through
;;; zz-bezout -- and the division algorithm is the only thing standing between
;;; the assertion and a proof.
;;;
;;; THE STATEMENT, in the shape `is-euclidean-ring-def' asks for.  The
;;; EUCLIDEAN-RING law (structure-library/euclidean-ring.scm:30-35) reads
;;;
;;;     forsome dg in fun(carr(s), nn).
;;;       forall a, b in carr(s).  b /= zero(s) =>
;;;         forsome q, r in carr(s).
;;;           a = add(s)(mul(s)(q, b), r)  and  (r = zero(s) or succ(dg r) <= dg b)
;;;
;;; so at s := ZZ-RING, with dg := abs, the surface statement is
;;;
;;;   (FORALL a_ (IMPLIES (IN a_ ZZ)
;;;     (FORALL b_ (IMPLIES (IN b_ ZZ)
;;;       (IMPLIES (NOT (= b_ 0))
;;;         (FORSOME q_ (AND (IN q_ ZZ)
;;;           (FORSOME r_ (AND (IN r_ ZZ)
;;;             (AND (= a_ (+ (* q_ b_) r_))
;;;                  (OR (= r_ 0) (<= (succ (abs r_)) (abs b_)))))))))))))
;;;
;;; Note the remainder condition is `succ(|r|) <= |b|', NOT `0 <= r < |b|'.  The
;;; Euclidean law asks only for a SIZE bound, so a negative remainder is legal,
;;; and taking it is what makes the sign bookkeeping below four one-line cases
;;; instead of four cases with a correction step.  A canonical non-negative
;;; remainder is a separate (and easy) refinement and is not what the Euclidean
;;; ring needs.
;;;
;;; ---------------------------------------------------------------------
;;; STEP 0 (the prerequisite, and the only induction): `nn-division'.
;;;
;;;   forall a, b in NN.  b /= 0  =>
;;;     forsome q, r in NN.  a = q*b + r  and  succ r <= b
;;;
;;; NOTHING of this shape exists.  The tree has only the fixed small moduli --
;;; `nn-parity' (b = 2: n = 2k or succ(2k), nn-parity-proof.scm:307) and
;;; `nn-trichotomy-3' (b = 3, nn-mod3-proof.scm) -- each proved by its own
;;; induction with the remainders enumerated literally.  Neither generalises:
;;; they conclude a DISJUNCTION over a fixed list of remainders, where the
;;; general statement has to quantify over r.  So the induction has to be
;;; written once more, on `a', with `b' fixed:
;;;
;;;   BASE a = 0:  q := 0, r := 0.  `0 = 0*b + 0' is `crs'.  `succ 0 <= b' is
;;;     `nn-one-is-succ-zero' (succ 0 = 1) plus "b /= 0 => 1 <= b", which is
;;;     `nn-nonzero-is-succ' then `nn-one-le-succ' -- the same two lines the
;;;     positive case of `zz-discrete' above runs.
;;;   STEP a -> succ a:  the IH gives q, r with a = q*b + r and succ r <= b.
;;;     Split on whether that inequality is strict:
;;;       `rr-le-cases' (rr-order-basics) turns `succ r <= b' into
;;;       `succ r < b' or `succ r = b'.
;;;       (i)  succ r < b:  `zz-lt-succ-le' (THIS FILE, at the integers succ r
;;;            and b, which are naturals hence integers by `nn-subset-zz')
;;;            gives succ r + 1 <= b, i.e. succ(succ r) <= b by
;;;            `nn-succ-plus-one'.  Take q' := q, r' := succ r; the equation
;;;            succ a = q*b + succ r is `nn-add-succ'.
;;;       (ii) succ r = b:  take q' := succ q, r' := 0.  The equation is
;;;            succ a = succ(q*b + r) = q*b + succ r = q*b + b = (succ q)*b,
;;;            i.e. `nn-add-succ' then `nn-mul-succ' (both proven).  The
;;;            remainder condition is the base case's again.
;;;     The frame is `use-induction' (driver-kit.scm), which labels the two
;;;     branches and captures the IH by diff.
;;;
;;; This is the ONE piece of real work left; everything below it is bookkeeping.
;;;
;;; ---------------------------------------------------------------------
;;; STEP 1: reduce zz-division to nn-division at (|a|, |b|).
;;;
;;;   `zz-abs-in-nn' (this file) gives A := |a| and B := |b| in NN.
;;;   B /= 0 comes from b /= 0 by `rr-abs-zero' (rr-abs-basics: |x| = 0 iff
;;;   x = 0) with `zz-in-rr'.
;;;   `nn-division' at (A, B) gives Q, R in NN with A = Q*B + R and succ R <= B.
;;;   `nn-subset-zz' carries Q and R into ZZ; `zz-neg-closed' their negatives.
;;;
;;; STEP 2: the four sign cases, and which fact each uses.
;;;
;;;   `zz-abs-cases' (this file) at a gives  a = A  or  a = -A;
;;;   `zz-abs-cases' at b gives              b = B  or  b = -B.
;;;   `use-cases' twice, so four branches, and in each the witnesses are read
;;;   straight off A = Q*B + R -- no adjustment, because a negative remainder is
;;;   allowed:
;;;
;;;     a =  A, b =  B:   q :=  Q,  r :=  R
;;;     a =  A, b = -B:   q := -Q,  r :=  R
;;;     a = -A, b =  B:   q := -Q,  r := -R
;;;     a = -A, b = -B:   q :=  Q,  r := -R
;;;
;;;   Each equation `a = q*b + r' is a ring identity over the surface operators
;;;   once the two sign equations are in context, so `crs' decides it in one
;;;   move (this is the same reason zz-parity-proof.scm's multiplicative facts
;;;   are one-liners: crs speaks the `-' surface).
;;;
;;; STEP 3: the remainder condition, in all four cases at once.
;;;
;;;   |r| = R in every branch: where r = R it is `rr-abs-of-nonneg' with
;;;   `nn-zero-le'; where r = -R it is `rr-abs-neg' (|-x| = |x|, rr-abs-basics)
;;;   composed with the same.  And |b| = B by construction.  So the goal
;;;   `succ(|r|) <= |b|' IS `succ R <= B', which nn-division handed over.  The
;;;   `r = 0' disjunct of the conclusion is never needed -- succ R <= B holds
;;;   outright -- so `oi-r' every time.
;;;
;;;   WHERE `zz-trichotomy' AND `zz-nonneg-in-nn' GO.  Not here: this route goes
;;;   through `abs' and never needs to know the sign of a or b separately.  They
;;;   are for the CONSUMERS -- `zz-trichotomy' for the canonical-remainder
;;;   refinement (0 <= r < |b|, which needs one correction step chosen by the
;;;   sign of r), and `zz-nonneg-in-nn' for the Euclid descent, where the
;;;   remainder sequence has to be handed to an NN well-ordering.
;;;
;;; ---------------------------------------------------------------------
;;; STEP 4: `zz-is-euclidean-ring' from zz-division.
;;;
;;;   The degree function the law quantifies over must be a genuine SET function
;;;   ZZ -> NN, so exhibit `VNB-LAMBDA a_ ZZ. abs(a_)' and type it with `lam-t',
;;;   whose two leaves are the pointwise typing -- `zz-abs-in-nn', exactly this
;;;   file's first theorem -- and the sethood of the domain, `zz-is-set'
;;;   (number-systems.scm:20, primitive).  Then unfold `is-euclidean-ring-def',
;;;   `ew' that lambda, and surface the accessors of ZZ-RING (ADD -> binplus,
;;;   MUL -> bintimes, ZERO -> 0) with `slot' + `nth-r' as
;;;   theorem-library/zz-ring-is-ring.scm does; the integral-domain conjunct is
;;;   `zz-is-integral-domain', PROVEN (theorem-library/zz-integral-domain.scm).
;;;   `lam-b' the two applications of the degree function BEFORE citing
;;;   zz-division, with the arguments typed first (CLAUDE.md: peel and type,
;;;   then beta).
;;;
;;; The bill would be `modulo 0' throughout: every fact named above is proven or
;;; primitive today except `nn-division' itself.
