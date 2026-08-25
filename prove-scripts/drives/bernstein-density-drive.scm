;;; bernstein-density-drive.scm -- the NEXT rung, handed over (2026-08-24).
;;;
;;; Proposition 5.4 of docs/calculus.pdf is DONE.  All four identities are in
;;; theorem-library/bernstein-moments.scm, each `trust: well-known':
;;;
;;;   bernstein-partition        (75)  sum_l B_{l,n}(x) = 1        [bernstein-basis.scm]
;;;   bernstein-moment-1         (78)  sum_l l B_{l,n}(x) = n x
;;;   bernstein-moment-2         (79)  sum_l l(l-1) B_{l,n}(x) = n(n-1) x^2
;;;   bernstein-variance         (80)  sum_l (l - n x)^2 B_{l,n}(x) = n x (1-x)
;;;   bernstein-variance-bound   (76)  (1/n) sum_l (l - n x)^2 B_{l,n}(x) <= 1
;;;
;;; What is left of Chapter 5 section 1 is THEOREM 5.2, the density statement:
;;; for f continuous on [0,1], the Bernstein polynomials
;;;
;;;     (B_n f)(x)  =  sum_{l=0}^{n} f(l/n) B_{l,n}(x)
;;;
;;; converge to f UNIFORMLY on [0,1].  This file is the hand-off: what the
;;; classical proof needs, which parts the tree now has, and the one part it
;;; does not.
;;;
;;; -------------------------------------------------------------------------
;;; THE ARGUMENT, AND WHERE EACH PIECE IS
;;; -------------------------------------------------------------------------
;;; Fix eps > 0.  Uniform continuity gives delta with |u - v| < delta =>
;;; |f(u) - f(v)| < eps/2.  Then, using (75) to write f(x) = sum_l f(x) B_l(x),
;;;
;;;   |(B_n f)(x) - f(x)|  <=  sum_l |f(l/n) - f(x)| B_{l,n}(x)
;;;
;;; and the index set splits in two:
;;;
;;;   NEAR   |l/n - x| <  delta :  each term < eps/2, and sum_l B_l(x) = 1,
;;;                                so the near part is < eps/2.        [(75)]
;;;   FAR    |l/n - x| >= delta :  then 1 <= (l - n x)^2 / (n delta)^2,
;;;                                so the far part is at most
;;;                                (2M/(n delta^2)) * (1/n) sum (l-nx)^2 B_l(x)
;;;                                <= 2M/(n delta^2)                    [(76)]
;;;                                which is < eps/2 for n large.
;;;
;;; HAVE:      (75) and (76) -- this rung.
;;; HAVE:      B_{l,n}(x) >= 0 on [0,1]?  NO -- see the OBSTACLE below.
;;; HAVE:      partial-sum linearity, pointwise/transfer form, `modulo 0'
;;;            (theorem-library/series-linearity.scm): -in-rr-ptwise, -add-ptwise,
;;;            -scale-ptwise, and series-partial-sum-le-termwise /
;;;            -monotone-nonneg (comparison-test-proof.scm) for the estimates.
;;; MISSING 1: UNIFORM CONTINUITY on a closed interval.  Not in the tree.  Its
;;;            own drive exists -- prove-scripts/drives/uniform-continuity-ccint-
;;;            drive.scm -- with three of `ccint-creep''s four hypotheses already
;;;            discharged; the cost is ccint-bounded's proof run with TWO points
;;;            instead of one, and the four-way case split is the whole expense.
;;; MISSING 2: BOUNDEDNESS of f on [0,1] -- the M above.  This one is DONE:
;;;            `ccint-bounded' / the EVT proofs (theorem-library/evt-proof.scm,
;;;            both forms PROVEN 2026-08-17 by the SUP route).
;;; MISSING 3: SPLITTING A PARTIAL SUM ON A PREDICATE.  The near/far split is a
;;;            sum over {l : |l/n - x| < delta} plus a sum over its complement,
;;;            and SERIES-PARTIAL-SUM has no such decomposition.  The cheap
;;;            route AVOIDS it, and that is the recommendation below.
;;;
;;; -------------------------------------------------------------------------
;;; THE RECOMMENDED ROUTE: NO INDEX SPLIT
;;; -------------------------------------------------------------------------
;;; The split is an artefact of the textbook presentation.  Bound each term
;;; UNIFORMLY instead, by the pointwise inequality
;;;
;;;     |f(l/n) - f(x)|  <=  eps/2  +  (2M/(n delta)^2) (l - n x)^2
;;;
;;; which holds for EVERY l -- if |l/n - x| < delta the first term does it, and
;;; otherwise (l - nx)^2 >= (n delta)^2 makes the second at least 2M.  Multiply
;;; by B_l(x) >= 0, sum with `series-partial-sum-le-termwise', and (75) and (80)
;;; finish it in one line each.  One pointwise lemma with a two-case proof
;;; replaces a decomposition of the index set that the tree cannot express.
;;;
;;; -------------------------------------------------------------------------
;;; THE OBSTACLE, and it is the one to look at first
;;; -------------------------------------------------------------------------
;;; NON-NEGATIVITY of the basis, B_{l,n}(x) >= 0 for 0 <= x <= 1, is NOT in the
;;; tree and is the first thing the estimate needs -- every step above multiplies
;;; an inequality by B_l(x).  Note that NOTHING in bernstein-moments.scm needs
;;; it: (75), (78), (79), (80) and (76) are all ALGEBRAIC identities, valid at
;;; every real x, and even the bound (76) is unconditional -- `sos' certifies
;;; 1 - x(1-x) = (x - 1/2)^2 + 3/4 with no order hypothesis.  [0,1] enters the
;;; chapter for the first time HERE.
;;;
;;; It should be a short induction on n from `bernstein-basis-succ',
;;;
;;;     B_{k,n+1}(x)  =  x B_{k-1,n}(x)  +  (1-x) B_{k,n}(x),
;;;
;;; both coefficients being >= 0 on [0,1] -- EXCEPT at the base, where
;;; B_{k,0}(x) is `IF k = 0 THEN 1 ELSE 0' and the case split is on a ZZ index.
;;; That is the same four-way split, on the same missing ZZ order theory, that
;;; blocked the textbook absorption identity k C(n,k) = n C(n-1,k-1) and drove
;;; this rung to the weighted expansion instead (see the long note at
;;; `series-partial-sum-weighted-expansion', series-linearity.scm).  It may be
;;; escapable here: non-negativity needs only `B(0)(k) >= 0', not a case
;;; analysis of its VALUE, so `comb-kk-null' (k<0), `comb-kk-above' (k>0) and
;;; `comb-kk-0-0' (k=0) may cover the three ranges without any betweenness fact.
;;; MEASURE THAT FIRST -- it decides whether the rung is cheap or blocked.
;;;
;;; -------------------------------------------------------------------------
;;; THE LEAF, to drive
;;; -------------------------------------------------------------------------
;;; Run:   ./prover -i prove-scripts/drives/bernstein-density-drive.scm

(define bd-stmt
  (forall-guarded '(n_ x_ k_)
    (list '(IN n_ NN) '(IN x_ RR) '(<= 0 x_) '(<= x_ 1) '(IN k_ ZZ))
    '(<= 0 ((BERNSTEIN-BASIS n_ x_) k_))))

(display "\n;;; ---- bernstein-basis-nonneg: the gate on Theorem 5.2 ----\n")
(display (expression->string (make-wff bd-stmt)))
(newline)
(display "\n;;; Induction on n_ -- state it with n_ OUTERMOST, which it is, so\n")
(display ";;; (use-induction) fires.  The STEP is bernstein-basis-succ plus\n")
(display ";;; 0 <= x, 0 <= 1-x and the IH at k_-1 and k_ (ineq closes it once the\n")
(display ";;; four atoms are typed).  The BASE is the question above: can\n")
(display ";;; comb-kk-null / comb-kk-above / comb-kk-0-0 cover k<0, k>0 and k=0\n")
(display ";;; without a betweenness fact about ZZ?  If they cannot, STOP and\n")
(display ";;; report it -- a ZZ order theory is a foundational piece of work of\n")
(display ";;; its own, and the ordinal route is unavailable (ZZ does not embed\n")
(display ";;; in ORD: negative integers are not ordinals).\n\n")

(sp (make-wff bd-stmt))
(display ";;; (what-now) on the goal, or (use-induction) to open the two branches.\n")
