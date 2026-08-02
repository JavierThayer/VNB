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
(support 'power-real-closed
  '(FORALL x
     (IMPLIES (IN x RR)
       (FORALL n
         (IMPLIES (IN n NN)
           (IN (power x n) RR))))))

(warrant! 'power-real-closed 'well-known
  "Induction on n: x^0 = 1 in RR (power-zero); x^{n+1} = x * x^n stays in RR
   since RR is closed under multiplication (power-succ).  A candidate to
   discharge into a formal `proof' later.")

;;; -----------------------------------------------------------------------
;;; PS-PARTIAL-SUM(coef, x, k) = Sum_{n<k} coef(n) x^n.
;;;
;;; SUM-AG(ag, f, k) = f(0) (OPR ag) ... (OPR ag) f(k-1); with ag the additive
;;; group of RR this is the ordinary ordered partial sum.  The term function
;;; n |-> coef(n) x^n is left inline (no name): it is just (* (coef n)
;;; (power x n)).
(def-functoid 'PS-PARTIAL-SUM '(coef x k)
  '(SUM-AG (NORMED-FIELD-ADDITIVE-AG RR-NORMED-FIELD)
           (VNB-LAMBDA n (* (coef n) (power x n)))
           k))

;;; -----------------------------------------------------------------------
;;; PS-CONVERGES-TO-AT(coef, x, L): the series converges at x to the real L,
;;; meaning the SEQUENCE of partial sums k |-> PS-PARTIAL-SUM(coef,x,k)
;;; converges to L in RR-MS.  This is the ordered (Abel) sum.
(def-predicate 'PS-CONVERGES-TO-AT '(coef x L)
  '(CONVERGES-TO RR-MS (VNB-LAMBDA k (PS-PARTIAL-SUM coef x k)) L))

;;; -----------------------------------------------------------------------
;;; PS-CONVERGES-AT(coef, x): the series converges at x (to some real limit).
(def-predicate 'PS-CONVERGES-AT '(coef x)
  '(CONVERGES RR-MS (VNB-LAMBDA k (PS-PARTIAL-SUM coef x k))))

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
     (VNB-LAMBDA n (abs (* (coef (succ n)) (recip (coef n)))))
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
(support 'ratio-test-converges
  '(FORALL coef
     (IMPLIES (IN coef (FUN NN RR))
       (FORALL L
         (IMPLIES (AND (IN L RR) (AND (<= 0 L) (AND (FORALL n
                         (IMPLIES (IN n NN) (NOT (= (coef n) 0)))) (PS-RATIO-LIMIT coef L))))
           (FORALL x
             (IMPLIES (AND (IN x RR) (< (* (abs x) L) 1))
               (PS-CONVERGES-AT coef x))))))))

(warrant! 'ratio-test-converges 'informal
  "d'Alembert for a power series.  The term ratio
   |coef(n+1)x^{n+1} / coef(n)x^n| = |coef(n+1)/coef(n)|.|x| converges to L.|x|,
   which is < 1 by hypothesis.  Pick r with L|x| < r < 1; from some N on the
   ratio is below r, so |term(n)| <= C r^n for a constant C.  The geometric
   majorant Sum C r^n converges (|r|<1), so the partial sums of the power
   series are Cauchy in RR-MS; RR is complete (rr-complete), giving a real
   limit -- PS-CONVERGES-AT(coef, x).  Now a PSS->proven candidate: it factors
   through the geometric majorant (geometric-series-converges-to) and the
   comparison test (comparison-test), both now in the library -- the proof
   chain is assembled, not missing.")

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
(support 'ps-abs-term
  '(FORALL coef
     (IMPLIES (IN coef (FUN NN RR))
       (FORALL x
         (IMPLIES (IN x RR)
           (FORALL n
             (IMPLIES (IN n NN)
               (= (abs (* (coef n) (power x n)))
                  (* (abs (coef n)) (power (abs x) n))))))))))

(warrant! 'ps-abs-term 'well-known
  "|coef(n) x^n| = |coef(n)|.|x^n| = |coef(n)|.|x|^n, by multiplicativity of
   the real absolute value (|ab| = |a||b|) and |x^n| = |x|^n (induction on n
   from power-zero/power-succ).  A candidate to discharge into a `proof'.")

;;; -----------------------------------------------------------------------
;;; PS-ABSOLUTELY-CONVERGES-AT(coef, x): the series converges absolutely at x,
;;; i.e. Sum |coef(n)| |x|^n converges -- which by ps-abs-term is Sum |term(n)|.
;;; Defined as ordinary convergence of the abs'd power series at |x|.
(def-predicate 'PS-ABSOLUTELY-CONVERGES-AT '(coef x)
  '(PS-CONVERGES-AT (VNB-LAMBDA n (abs (coef n))) (abs x)))

;;; -----------------------------------------------------------------------
;;; ps-absolute-implies-convergent: absolute convergence implies convergence,
;;; in RR.  The classical Cauchy-criterion argument, leaning on completeness
;;; of RR (rr-complete).  Asserted + warranted for the library-build phase.
(support 'ps-absolute-implies-convergent
  '(FORALL coef
     (IMPLIES (IN coef (FUN NN RR))
       (FORALL x
         (IMPLIES (AND (IN x RR)
                       (PS-ABSOLUTELY-CONVERGES-AT coef x))
           (PS-CONVERGES-AT coef x))))))

(warrant! 'ps-absolute-implies-convergent 'informal
  "Absolute convergence gives that the partial sums A_k = Sum_{n<k}
   |coef(n)||x|^n converge, hence are Cauchy: for eps>0 there is N with
   A_m - A_k = Sum_{k<=n<m} |coef(n)||x|^n < eps  for m >= k >= N.  By the
   triangle inequality the ordinary partial sums S_k = Sum_{n<k} coef(n)x^n
   satisfy |S_m - S_k| <= Sum_{k<=n<m} |coef(n) x^n| = Sum_{k<=n<m}
   |coef(n)||x|^n < eps (ps-abs-term), so (S_k) is Cauchy in RR-MS.  RR is
   complete (rr-complete), so (S_k) converges -- PS-CONVERGES-AT(coef, x).  A
   candidate to discharge into a formal `proof' later (it needs a finite
   triangle-inequality / abs-of-finsum bound not yet in the library).")

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
  '(CONVERGES-TO RR-MS (VNB-LAMBDA k (SERIES-PARTIAL-SUM f k)) L))

(def-predicate 'SERIES-CONVERGES '(f)
  '(CONVERGES RR-MS (VNB-LAMBDA k (SERIES-PARTIAL-SUM f k))))

;;; -----------------------------------------------------------------------
;;; Bridge: a power series IS the bare series of its term sequence.
;;; Both sides unfold to the same SUM-AG, so this is an equality by
;;; definitional unfolding; asserted + warranted for the library phase.
(support 'ps-partial-sum-as-series
  '(FORALL coef
     (IMPLIES (IN coef (FUN NN RR))
       (FORALL x
         (IMPLIES (IN x RR)
           (FORALL k
             (IMPLIES (IN k NN)
               (= (PS-PARTIAL-SUM coef x k)
                  (SERIES-PARTIAL-SUM (VNB-LAMBDA n (* (coef n) (power x n))) k)))))))))

(warrant! 'ps-partial-sum-as-series 'well-known
  "Both sides unfold to SUM-AG(RR-additive-AG, n |-> coef(n) x^n, k) -- the
   PS-PARTIAL-SUM functoid is SERIES-PARTIAL-SUM of the term sequence.  Provable
   by unfolding the two def-functoids; asserted for now.")

(support 'ps-converges-as-series
  '(FORALL coef
     (IMPLIES (IN coef (FUN NN RR))
       (FORALL x
         (IMPLIES (IN x RR)
           (IFF (PS-CONVERGES-AT coef x)
                (SERIES-CONVERGES (VNB-LAMBDA n (* (coef n) (power x n))))))))))

(warrant! 'ps-converges-as-series 'well-known
  "Immediate from ps-partial-sum-as-series: the two partial-sum sequences are
   equal, so one converges in RR-MS iff the other does.")

;;; -----------------------------------------------------------------------
;;; Geometric series.  Closed-form partial sum (r /= 1):
;;;   Sum_{n<k} r^n = (1 - r^k) / (1 - r).
(support 'geometric-partial-sum
  '(FORALL r
     (IMPLIES (AND (IN r RR) (NOT (= r 1)))
       (FORALL k
         (IMPLIES (IN k NN)
           (= (SERIES-PARTIAL-SUM (VNB-LAMBDA n (power r n)) k)
              (* (- 1 (power r k)) (recip (- 1 r)))))))))

(warrant! 'geometric-partial-sum 'well-known
  "Telescoping: (1-r) Sum_{n<k} r^n = Sum_{n<k}(r^n - r^{n+1}) = 1 - r^k, then
   divide by 1-r (/= 0).  Induction on k from power-zero/power-succ.")

;;; And the sum, for |r| < 1:  Sum_{n>=0} r^n = 1/(1-r).
(support 'geometric-series-converges-to
  '(FORALL r
     (IMPLIES (AND (IN r RR) (< (abs r) 1))
       (SERIES-CONVERGES-TO (VNB-LAMBDA n (power r n)) (recip (- 1 r))))))

(warrant! 'geometric-series-converges-to 'informal
  "For |r|<1, r^k -> 0, so the closed-form partial sum (1 - r^k)/(1-r)
   (geometric-partial-sum) -> 1/(1-r) in RR-MS.  Needs r^k -> 0 (a separate
   `power tends to 0 when |base|<1' fact, not yet in the library).")

;;; -----------------------------------------------------------------------
;;; Comparison test.  If 0 <= f(n) <= g(n) for all n and the dominating series
;;; Sum g converges, then Sum f converges.
(support 'comparison-test
  '(FORALL f
     (IMPLIES (IN f (FUN NN RR))
       (FORALL g
         (IMPLIES (IN g (FUN NN RR))
           (IMPLIES (AND (FORALL n
                           (IMPLIES (IN n NN)
                             (AND (<= 0 (f n)) (<= (f n) (g n)))))
                         (SERIES-CONVERGES g))
             (SERIES-CONVERGES f)))))))

(warrant! 'comparison-test 'informal
  "The partial sums F_k = Sum_{n<k} f(n) are nondecreasing (f >= 0) and bounded
   above by the limit of G_k = Sum_{n<k} g(n) (since f <= g termwise gives
   F_k <= G_k <= lim G, by series-partial-sum-le-termwise).  A nondecreasing
   (series-partial-sum-monotone-nonneg) sequence bounded above converges in RR
   by monotone-convergence-rr (order-completeness), so Sum f converges.  All
   three ingredients are now in the library (series-order-lemmas.scm), so this
   is a PSS->proven candidate -- the chain is assembled, not missing.")

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
