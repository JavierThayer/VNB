;;; rando-dieudonne-mvineq.scm -- WORKED EXAMPLE: reject-and-rebuild.
;;; A probe (NOT in load.scm).  Run:  ./prover calculus/rando-dieudonne-mvineq.scm
;;;
;;; THE SCENARIO.  RANDO keeps VNB's trusted machinery (foundational axioms,
;;; inference rules, tactics) but rejects the library's differential calculus,
;;; which builds the Mean Value Theorem the classical way:
;;;
;;;     mvt  <-  rolle  <-  interior-extremum  <-  extreme-value-max
;;;                                                (asserted; warrant 'reference)
;;;
;;; `extreme-value-max' -- "a continuous function on a compact interval ATTAINS
;;; its sup" -- is the non-constructive node.  RANDO prefers Dieudonne
;;; (Foundations of Modern Analysis, 8.5), who proves the mean value INEQUALITY
;;; ||f(b)-f(a)|| <= (b-a) sup||f'|| by an l.u.b./connectedness argument that
;;; attains no maximum and never invokes the extreme value theorem.
;;;
;;; WHAT RANDO DOES.
;;;   1. Audits via the ledger: `mvt's bill bottoms out at `extreme-value-max',
;;;      provenance `asserted'.  He rejects that leaf.
;;;   2. THE SUBSTRATE CUT (the load-list surgery, done for real by truncating
;;;      *vnb-files*): keep the list THROUGH "theorem-library/differentiation"
;;;      (RR, its completeness, continuity, the derivative + its rules -- all he
;;;      accepts) and DROP from "theorem-library/extreme-value" down (EVT, Rolle,
;;;      MVT, Taylor).  Verified sound: differentiation loads upstream of the EVT
;;;      tower and cites none of it, so the substrate stands alone.  (No named
;;;      load target for this yet -- it is a hand-cut of *vnb-files*.)
;;;   3. Asserts Dieudonne's inequality as his OWN primitive (below) and rebuilds.
;;;
;;; THE GUARANTEE.  This probe runs in the FULL prover -- so `extreme-value-max'
;;; is loaded and available -- and still the corollary's bill EXCLUDES it.  That
;;; is the stronger claim: not "it's absent so it can't be used" but "it's present
;;; and the proof provably does not touch it."  The ledger, not trust, certifies
;;; RANDO's development is free of the node he rejects.
;;; ====================================================================

;;; (1) RANDO's asserted primitive -- the real-valued mean value inequality.
;;; Identical statement to the library's `mvt-upper-bound', but ASSERTED with a
;;; Dieudonne citation instead of DERIVED from mvt <- ... <- extreme-value-max.
(support 'mvineq-dieudonne
  '(FORALL f (FORALL a (FORALL b (FORALL M
     (IMPLIES (AND (IN f (FUN RR RR)) (AND (IN a RR) (AND (IN b RR) (AND (IN M RR) (< a b)))))
     (IMPLIES (FORALL x (IMPLIES (IN x (CCINT a b)) (IS-CONTINUOUS-AT RR-MS RR-MS f x)))
     (IMPLIES (FORALL x (IMPLIES (AND (< a x) (< x b))
                 (FORSOME L (AND (IS-DIFF-AT f x L) (<= L M)))))
       (<= (- (f b) (f a)) (* M (- b a)))))))))))
(warrant! 'mvineq-dieudonne 'reference '(dieudonne "8.5.1 (real form 8.5.3)" 178))
(gloss! 'mvineq-dieudonne
  "Mean value inequality (Dieudonne, FMA 8.5.1; real form 8.5.3): f continuous on
   [a,b], differentiable on (a,b) with f' <= M there, gives f(b)-f(a) <= M(b-a).
   RANDO's asserted primitive for the differential calculus -- Dieudonne's
   l.u.b./connectedness proof attains no maximum, so a development on this base
   never touches the extreme value theorem.")
(topic! 'mvineq-dieudonne 'analysis)

;;; (2) RANDO's corollary, proved ON the inequality: the M=0 increment bound
;;; f' <= 0 on (a,b)  =>  f(b) - f(a) <= 0*(b-a)   (f does not increase across [a,b]).
;;; Hypotheses are given in exactly mvineq's antecedent shapes so `fact'
;;; auto-detaches; the proof is one forward application of the primitive.
(sp '(FORALL f (FORALL a (FORALL b
     (IMPLIES (AND (IN f (FUN RR RR)) (AND (IN a RR) (AND (IN b RR) (AND (IN 0 RR) (< a b)))))
     (IMPLIES (FORALL x (IMPLIES (IN x (CCINT a b)) (IS-CONTINUOUS-AT RR-MS RR-MS f x)))
     (IMPLIES (FORALL x (IMPLIES (AND (< a x) (< x b))
                 (FORSOME L (AND (IS-DIFF-AT f x L) (<= L 0)))))
       (<= (- (f b) (f a)) (* 0 (- b a))))))))))
(quietly (lambda () (di)(di)(di)(di)(di)(di)))    ; f a b TYP CONT DIFF (TYP kept whole)
(define RANDO-GOAL (dc-gf))
(quietly (lambda () (fact 'mvineq-dieudonne 'f 'a 'b 0)))
(dc-focus! RANDO-GOAL)
(quietly (lambda () (ass-all)))
(qed 'rando-nonincreasing)

;;; (3) Exhibit the bill: the corollary rests on the Dieudonne primitive and NOT
;;; on extreme-value-max -- the mechanical certificate of RANDO's rejection.
(newline)
(let ((bill (debt-of-proof 'rando-nonincreasing)))
  (display ";;=== RANDO worked-example result ===") (newline)
  (display ";;bill (modulo): ") (write bill) (newline)
  (display ";;uses mvineq-dieudonne? ")
  (display (if (memq 'mvineq-dieudonne bill) "yes" "NO (BUG)")) (newline)
  (display ";;uses extreme-value-max? ")
  (display (if (memq 'extreme-value-max bill) "YES (BAD)" "no -- EVT rejected, as intended")) (newline))
(exit 0)
