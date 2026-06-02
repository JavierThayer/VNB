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
;;; group, and NORMED-FIELD-ADDITIVE-AG(RR-RING) is exactly (RR, +, 0, -).
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
;;; numeric-instances.scm (RR-RING, RR-MS), number-systems.scm (power),
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
;;; SUM-AG(ag, f, k) = f(0) (MUL ag) ... (MUL ag) f(k-1); with ag the additive
;;; group of RR this is the ordinary ordered partial sum.  The term function
;;; n |-> coef(n) x^n is left inline (no name): it is just (* (coef n)
;;; (power x n)).
(def-functoid 'PS-PARTIAL-SUM '(coef x k)
  '(SUM-AG (NORMED-FIELD-ADDITIVE-AG RR-RING)
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
         (IMPLIES (AND (IN L RR)
                       (<= 0 L)
                       (FORALL n
                         (IMPLIES (IN n NN) (NOT (= (coef n) 0))))
                       (PS-RATIO-LIMIT coef L))
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
   limit -- PS-CONVERGES-AT(coef, x).  A candidate to discharge into a formal
   `proof' later (it factors through a geometric-series lemma + comparison,
   neither yet in the library).")
