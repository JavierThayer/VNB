;;; MOVED 2026-09-20 (batch 12-A) from theorem-library/: this file is VOCABULARY --
;;; definitions, notation and warranted supports, not one proof -- and every theorem
;;; stated with it had to load below it.  Its load.scm slot is unchanged.
;;; power-series.scm -- real power series  Sum_{n>=0} coef(n) x^n  in RR.
;;;
;;; A power series is nothing but its coefficient sequence
;;;
;;;     coef : NN -> RR ,
;;;
;;; evaluated at a real point x and centered at 0 (a center c is recovered
;;; later by x |-> x - c, so no separate parameter now).  We build three
;;; layers, each on existing machinery, none new:
;;;
;;;   PS-PARTIAL-SUM(coef, x, k)   = Sum_{n<k} coef(n) x^n   -- ordered finite sum
;;;   PS-CONVERGES-TO-AT(coef,x,L) = those partial sums -> L in RR
;;;   PS-CONVERGES-AT(coef, x)     = ... -> some real limit
;;;
;;; The ordered partial sum is SUM-AG over the additive group of RR: SUM-AG
;;; is by construction  f(0) + f(1) + ... + f(k-1)  in the supplied abelian
;;; group, and NORMED-FIELD-ADDITIVE-AG(RR-NORMED-FIELD) is exactly (RR, +, 0, -).
;;; Convergence is the ORDERED limit of partial sums in the complete metric
;;; space RR-MS -- the classical meaning of "Sum coef(n) x^n = L".  Inside
;;; the radius this also coincides with absolute / unconditional summability
;;; (IS-ABSOLUTELY-SUMMABLE, SUMS-TO); that bridge is a later brick, not here.
;;;
;;; Case-fold notes (the reader folds case): the coefficient sequence is
;;; `coef', NOT `a' -- `a' folds to the carrier accessor `A'.  The partial-sum
;;; bound is `k', the term index `n' -- `N' would fold onto `n' (capture).
;;;
;;; Dependencies: sequences.scm (SUM-AG), views.scm (NORMED-FIELD-ADDITIVE-AG),
;;; numeric-instances.scm (RR-NORMED-FIELD, RR-MS), number-systems.scm (power),
;;; metric-completeness.scm (CONVERGES, CONVERGES-TO).

;;; -----------------------------------------------------------------------
;;; Closure: a real raised to a natural power is real.
;;;
;;; The kernel `power' axioms (number-systems.scm) only type power into CC
;;; (power-typing-nonneg).  The real refinement is what the partial sum needs,
;;; since SUM-AG folds in RR.  Provable by induction on n from power-zero
;;; (x^0 = 1 in RR) and power-succ (x^{n+1} = x * x^n, RR closed under *);
;;; asserted for the library-build phase.
;; power-real-closed MOVED 2026-08-22 to theorem-library/dyadic-weights.scm,
;; where it is PROVEN `modulo 0' -- it is exactly the induction its warrant
;; described ("x^0 = 1 in RR; x^{n+1} = x * x^n stays in RR ... a candidate to
;; discharge into a formal `proof' later"), twelve lines, and it had no citer
;; in the tree until that file needed it.  The induction runs at
;; `power-closed-at' with the EXPONENT outermost (`ni' tests the goal's shape
;; literally) and the statement above is recovered from it in three lines.

;;; -----------------------------------------------------------------------
;;; PS-PARTIAL-SUM(coef, x, k) = Sum_{n<k} coef(n) x^n.
;;;
;;; SUM-AG(ag, f, k) = f(0) (OPR ag) ... (OPR ag) f(k-1); with ag the additive
;;; group of RR this is the ordinary ordered partial sum.  The term function
;;; n |-> coef(n) x^n is left inline (no name): it is just (* (coef n)
;;; (power x n)).
(def-functoid 'PS-PARTIAL-SUM '(coef x k)
  '(SUM-AG (NORMED-FIELD-ADDITIVE-AG RR-NORMED-FIELD)
           (VNB-LAMBDA n NN (* (coef n) (power x n)))
           k))

;;; -----------------------------------------------------------------------
;;; PS-CONVERGES-TO-AT(coef, x, L): the series converges at x to the real L,
;;; meaning the SEQUENCE of partial sums k |-> PS-PARTIAL-SUM(coef,x,k)
;;; converges to L in RR-MS.  This is the ordered (Abel) sum.
(def-predicate 'PS-CONVERGES-TO-AT '(coef x L)
  '(CONVERGES-TO RR-MS (VNB-LAMBDA k NN (PS-PARTIAL-SUM coef x k)) L))

;;; -----------------------------------------------------------------------
;;; PS-CONVERGES-AT(coef, x): the series converges at x (to some real limit).
(def-predicate 'PS-CONVERGES-AT '(coef x)
  '(CONVERGES RR-MS (VNB-LAMBDA k NN (PS-PARTIAL-SUM coef x k))))

;;; =======================================================================
;;; Brick 2 -- the ratio (d'Alembert) test.
;;;
;;; We take the RATIO route to the radius "for now" (dodging limsup): assume
;;; the limit  L = lim_n |coef(n+1) / coef(n)|  exists in RR.  Rather than
;;; package the radius R = 1/L as a separate object (which would force
;;; 1/0 = +inf bookkeeping), we state the convergence test directly as
;;;
;;;     |x| . L < 1        ( <=>  |x| < R = 1/L  when L > 0;  all x when L = 0 ).
;;;
;;; So L = 0 (radius +inf) is automatic and needs no special case.

;;; -----------------------------------------------------------------------
;;; PS-RATIO-LIMIT(coef, L): the sequence of successive-coefficient ratios
;;; |coef(n+1)/coef(n)| converges to L in RR.  Reused by the radius brick.
;;; (Meaningful only when the coefficients are eventually nonzero; the test
;;; below carries that hypothesis explicitly.)
(def-predicate 'PS-RATIO-LIMIT '(coef L)
  '(CONVERGES-TO RR-MS
     (VNB-LAMBDA n NN (abs (* (coef (succ n)) (recip (coef n)))))
     L))

;;; -----------------------------------------------------------------------
;;; ratio-test-converges: if the coefficients never vanish, the ratio limit
;;; is L, and |x|.L < 1, then the series converges at x.
;;;
;;; This is d'Alembert specialised to a power series: the term ratio
;;; |coef(n+1)x^{n+1} / coef(n)x^n| = |coef(n+1)/coef(n)| . |x| -> L|x| < 1,
;;; so from some N on the terms are dominated by a geometric series of ratio
;;; r with L|x| < r < 1; that majorant is absolutely summable, RR is complete,
;;; hence the partial sums converge (PS-CONVERGES-AT).  Asserted + warranted
;;; for the library-build phase.
;;; ratio-test-converges PROVEN 2026-09-24 (batch 27-A) in theorem-library/ratio-test-proof.scm; the support and its warrant retired.


;;; =======================================================================
;;; Brick 3 -- absolute convergence, and absolute => convergent.
;;;
;;; The series of absolute values of  Sum coef(n) x^n  is itself a power
;;; series: termwise  |coef(n) x^n| = |coef(n)| . |x|^n  (abs is multiplicative
;;; and |x^n| = |x|^n).  So "the power series converges absolutely at x" is
;;; nothing but ORDINARY convergence (PS-CONVERGES-AT) of the abs'd
;;; coefficients (n |-> |coef(n)|) at the point |x|.  This keeps the whole
;;; notion inside the RR ordered-sum world already built -- no ESUM, no
;;; NORMED-AG, no unordered net.  (Connecting absolute convergence to the
;;; UNCONDITIONAL net IS-SUMMABLE / IS-ABSOLUTELY-SUMMABLE of summability.scm
;;; is a separate later bridge: it would need a NORMED-FIELD -> NORMED-AG view
;;; and an ordered-limit = net-sum reconciliation.)

;;; -----------------------------------------------------------------------
;;; ps-abs-term: the n-th absolute term is the n-th term of the abs'd series.
;;; |coef(n) x^n| = |coef(n)| . |x|^n.  This is what certifies that the
;;; definition below really expresses absolute convergence.
;; ps-abs-term MOVED 2026-09-04 to theorem-library/ps-series-bridges.scm, where
;; it is PROVEN `modulo 0'.  Its warrant proposed the route and called the power
;; law "induction on n from power-zero/power-succ" -- that induction is now
;; `rr-abs-power' (geometric-series.scm, 2026-09-02), so the fact is
;; multiplicativity of abs plus one rewrite, run BACKWARDS: the goal carries
;; |x|^n where the rr-abs-mult instance carries |x^n|.

(def-predicate 'PS-ABSOLUTELY-CONVERGES-AT '(coef x)
  '(PS-CONVERGES-AT (VNB-LAMBDA n NN (abs (coef n))) (abs x)))

;;; -----------------------------------------------------------------------
;;; ps-absolute-implies-convergent: absolute convergence implies convergence,
;;; in RR.  The classical Cauchy-criterion argument, leaning on completeness
;;; of RR (rr-complete).  Asserted + warranted for the library-build phase.
;;; ps-absolute-implies-convergent RETIRED 2026-09-18 (rake batch 5): proven modulo 0 in theorem-library/rake-series.scm


;;; =======================================================================
;;; Brick 4 -- bare real series, the geometric series, and comparison.
;;;
;;; A power series is the series of its term sequence; comparison and the
;;; geometric majorant are termwise facts about a plain real series Sum_n f(n),
;;; so we name that bare object and state the two foundational lemmas there.
;;; (Conceptually the bare series is MORE primitive than the power series;
;;; it sits here only because power-series.scm was built first.)
;;;
;;; SERIES-PARTIAL-SUM(f, k) = Sum_{n<k} f(n)  is just SUM-AG over RR's additive
;;; group -- the same fold PS-PARTIAL-SUM uses -- so PS-PARTIAL-SUM(coef,x,k)
;;; equals SERIES-PARTIAL-SUM applied to the term sequence n |-> coef(n) x^n
;;; (ps-partial-sum-as-series), whence the convergence bridge
;;; ps-converges-as-series.

;;; -----------------------------------------------------------------------
;;; The bare series  Sum_n f(n)  and its partial sums.  (Sequence var is `f',
;;; not `a' -- `a' folds to the carrier accessor `A'.)
(def-functoid 'SERIES-PARTIAL-SUM '(f k)
  '(SUM-AG (NORMED-FIELD-ADDITIVE-AG RR-NORMED-FIELD) f k))

(def-predicate 'SERIES-CONVERGES-TO '(f L)
  '(CONVERGES-TO RR-MS (VNB-LAMBDA k NN (SERIES-PARTIAL-SUM f k)) L))

(def-predicate 'SERIES-CONVERGES '(f)
  '(CONVERGES RR-MS (VNB-LAMBDA k NN (SERIES-PARTIAL-SUM f k))))

;;; -----------------------------------------------------------------------
;;; Bridge: a power series IS the bare series of its term sequence.
;;; Both sides unfold to the same SUM-AG, so this is an equality by
;;; definitional unfolding; asserted + warranted for the library phase.
;; ps-partial-sum-as-series and ps-converges-as-series MOVED 2026-09-04 to
;; theorem-library/ps-series-bridges.scm, both PROVEN `modulo 0'.  The first is
;; the pure definitional unfold this warrant described -- both functoids reduce
;; to the same SUM-AG, so after `mac' on each the goal is X = X (the only cost is
;; `rfl's definedness guard, which wants the sum typed first).  The second is NOT
;; immediate from it, and the reason is worth knowing: `mac' will not descend
;; into a VNB-LAMBDA body, so the two CONVERGES statements cannot be made
;; textually identical; they are related POINTWISE instead, through the new
;; `rr-converges-ptwise-eq'.

;;; -----------------------------------------------------------------------
;;; Geometric series.  Closed-form partial sum (r /= 1):
;;;   Sum_{n<k} r^n = (1 - r^k) / (1 - r).
;; geometric-partial-sum MOVED 2026-09-02 to theorem-library/geometric-series.scm,
;; where it is PROVEN `modulo 0'.  The route is the one this warrant described --
;; telescoping, then divide by 1-r -- but in two steps rather than one, and the
;; order matters: the DIVISION-FREE identity (1-r).S_k = 1 - r^k is proved first
;; by induction (`geometric-partial-sum-mul', which needs no r /= 1 at all), and
;; the recip form is one citation of `rr-recip-solve' off it.  Doing it in one
;; step fails, because `crs' declines any identity containing a `recip' and the
;; induction step is exactly such an identity.

;;; And the sum, for |r| < 1:  Sum_{n>=0} r^n = 1/(1-r).
;;; geometric-series-converges-to RETIRED 2026-09-18 (rake batch 5c): proven in theorem-library/rake-series2.scm


;;; -----------------------------------------------------------------------
;;; Comparison test.  If 0 <= f(n) <= g(n) for all n and the dominating series
;;; Sum g converges, then Sum f converges.
;; comparison-test MOVED 2026-08-20 to theorem-library/comparison-test-proof.scm,
;; where it is PROVEN, billing `modulo {nn-zero-le, nn-le-succ-cases}'
;; [trust: well-known] -- resting on nothing but the two NN-order supports of
;; structure-library/order-lemmas.scm, inherited through the monotone lift.
;; The retired `informal' warrant read: "The partial sums F_k are nondecreasing
;; (f >= 0) and bounded above by the limit of G_k (since f <= g termwise gives
;; F_k <= G_k <= lim G) ... all three ingredients are now in the library, so
;; this is a PSS->proven candidate -- the chain is assembled, not missing."
;; The chain was one rung SHORT: "G_k <= lim G" is the lemma "a nondecreasing
;; sequence converging to L satisfies x_k <= L for every k", which the tree did
;; not have.  It is also not needed -- monotone convergence wants SOME bound,
;; not the sharp one -- and the proof takes eps = 1 in CONVERGES-TO instead,
;; getting L + 1 as a bound for the whole sequence in two instantiations and one
;; case split (`monotone-convergent-bounded-above', proven in the same file).

;;; -----------------------------------------------------------------------
;;; Notation -- the ENGLISH of these predicates, declared beside their
;;; definitions and read by wff->english / the proof reader (operators.scm).
;;; A def-predicate's reading cannot be derived the way a structure's noun can
;;; (noun vs adjective: IS-COMPLETE wants "s is complete", not "s is a complete"),
;;; so it is written here, once, next to what it means.
(notation! 'SERIES-CONVERGES 'kind 'predicate 'arity 1
           'english "the series $1 converges")
(notation! 'SERIES-CONVERGES-TO 'kind 'predicate 'arity 2
           'english "the series $1 converges to $2")
(notation! 'PS-CONVERGES-AT 'kind 'predicate 'arity 2
           'english "the power series with coefficients $1 converges at $2")
(notation! 'PS-CONVERGES-TO-AT 'kind 'predicate 'arity 3
           'english "the power series with coefficients $1 converges to $3 at $2")
(notation! 'PS-ABSOLUTELY-CONVERGES-AT 'kind 'predicate 'arity 2
           'english "the power series with coefficients $1 converges absolutely at $2")
(notation! 'PS-RATIO-LIMIT 'kind 'predicate 'arity 2
           'english "the coefficients $1 have ratio limit $2")
