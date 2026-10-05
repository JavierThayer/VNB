;;; gamma-function.scm -- THE IMPROPER INTEGRAL ON (0, +inf) AND THE GAMMA FUNCTION
;;; (complex-analysis.pdf ch. 3, section 3.9: equations (96)-(99), Definition 3.58).
;;; DEFINITIONS ONLY; every law is PROVEN in theorem-library/gamma-function.scm.
;;; Agent CA-6 of week 3 of the October roadmap (scratchpad/triage/WEEK3.md), 2026-10-04.
;;;
;;; THE NOTES.  For 0 < re z the truncations
;;;     g_{r,R}(z) = int_r^R e^{-t} t^{z-1} dt                                        (97)
;;; converge as r -> 0 and R -> +inf, and Gamma(z) is DEFINED as that limit (Def. 3.58,
;;; (99)).  The tree had no improper integral; this file adds the notes' notion and
;;; nothing more:
;;;
;;;   IMPROPER-INT-CONVERGES-TO(f, L)   L in CC, and for every eps > 0 there are
;;;                                     delta > 0 and M in RR such that
;;;                                     |int_r^R f - L| <= eps whenever
;;;                                     0 < r < delta, M < R and r < R
;;;   IMPROPER-INT(f)                   the L above (a definite description)
;;;   GAMMA-INTEGRAND(z)                w |-> exp((z - 1) log w) * exp(-w) on the open right
;;;                                     half-plane H = {w in CC : 0 < re w}
;;;   GAMMA-FUNCTION(z)                 IMPROPER-INT(GAMMA-INTEGRAND(z))
;;;
;;; HOW THIS RELATES TO THE TREE'S INTEGRALS.  int_r^R f is CC-INT(f, r, R)
;;; (structure-library/path-integral.scm, equation (44) of the notes: the integral of a
;;; CC-valued function over a COMPACT interval, componentwise through the regulated
;;; primitives of Dieudonne VIII.7).  CC-INT reads f only at the points of [r, R], so f
;;; may be any CC-valued function whose domain contains (0, +inf) -- here the half-plane
;;; H.  The improper integral is the double limit r -> 0+, R -> +inf of these compact
;;; integrals, exactly (97); no new integral is introduced and the regulated primitives
;;; do all the work.  The guard r < R keeps CC-INT on its domain of definition (it is a
;;; definite description and says nothing about a degenerate or reversed interval).
;;;
;;; WHY THE INTEGRAND LIVES ON THE HALF-PLANE, AND WHY CC-LOG RATHER THAN RPOW.  The
;;; notes write t^{z-1} = exp((z - 1) ln t) for real t > 0 (section 2.3.3.2).  RPOW
;;; (real-powers.scm) has a REAL exponent only, so it cannot carry z - 1; the brief's
;;; second spelling, CC-EXP((z - 1) * LOG t), uses the real LOG.  This file writes the
;;; principal logarithm CC-LOG, which agrees with LOG on (0, +inf) (`cc-log-real',
;;; theorem-library/analytic-log-laws.scm), and lets w range over the open half-plane
;;; H.  The function so defined is the holomorphic extension of t |-> t^{z-1} e^{-t};
;;; its restriction to (0, +inf) is the notes' integrand, and on H it is HOLOMORPHIC in
;;; w (CC-LOG is holomorphic on the slit plane, which contains H).  That is what lets
;;; the proofs take continuity, integrability and every primitive from the line-integral
;;; laws (the fundamental theorem `line-int-of-derivative' over the real segment) with no
;;; real-variable calculus.  The membership t in H for real t > 0 is one lemma.
;;;
;;; STATEMENT CHECKS (CLAUDE.md, the species of false or underdetermined statement).
;;; (1) IMPROPER-INT and GAMMA-FUNCTION are TERMS defined by IOTA: they denote only where the limit
;;;     exists (and limits in CC are unique, proven).  The domain of Gamma, the open right
;;;     half-plane, is a hypothesis of the laws (`gamma-converges'), not of the term.
;;; (2) GAMMA-INTEGRAND(z) is a VNB-LAMBDA, a set, for every z in CC; nothing here asserts
;;;     an equation.  The integrand's binder is gmw_, the half-plane's gmu_; the improper
;;;     integral's are ipe_, ipd_, ipm_, ipr_, ipq_ (r and R would fold together: the two
;;;     bounds are ipr_ and ipq_).  None folds onto a class name, an accessor or a
;;;     registered constant; no other body binds a gm*_ or ip*_ name.
;;; (3) THE NAME.  `GAMMA' alone cannot be a registered head: theorem-library binds a variable
;;;     `gamma' (ord-le-trans), and case folding makes the two one symbol (constant-binder-audit).
;;; (4) 1 is the complex unit as everywhere in the CC files (`(- gmz_ 1)').
;;;
;;; Dependencies: path-integral.scm (CC-INT), cc-elementary.scm (CC-EXP), analytic-log.scm
;;; (CC-LOG).  Load slot: after structure-library/analytic-log (any later slot before the
;;; proof file will do).

(def-predicate 'IMPROPER-INT-CONVERGES-TO '(ipf_ ipl_)
  '(AND (IN ipl_ CC)
        (FORALL ipe_ (IMPLIES (POS-RR ipe_)
          (FORSOME ipd_ (AND (POS-RR ipd_)
            (FORSOME ipm_ (AND (IN ipm_ RR)
              (FORALL ipr_ (IMPLIES (IN ipr_ RR)
                (FORALL ipq_ (IMPLIES (IN ipq_ RR)
                  (IMPLIES (< 0 ipr_)
                    (IMPLIES (< ipr_ ipd_)
                      (IMPLIES (< ipm_ ipq_)
                        (IMPLIES (< ipr_ ipq_)
                          (<= (magnitude (- (CC-INT ipf_ ipr_ ipq_) ipl_)) ipe_)))))))))))))))))

(notation! 'IMPROPER-INT-CONVERGES-TO 'kind 'predicate 'arity 2
           'english "the improper integral of $1 over (0, +inf) converges to $2")

(def-functoid 'IMPROPER-INT '(ipf_)
  '(IOTA ipv_ (IMPROPER-INT-CONVERGES-TO ipf_ ipv_)))

(notation! 'IMPROPER-INT 'kind 'functoid 'arity 1
           'english "the improper integral of $1 over (0, +inf)"
           'tex "\\int_0^{\\infty} $1")

(def-functoid 'GAMMA-INTEGRAND '(gmz_)
  '(VNB-LAMBDA gmw_ (SEP gmu_ CC (< 0 (real-part gmu_)))
     (* (CC-EXP (* (- gmz_ 1) (CC-LOG gmw_))) (CC-EXP (- gmw_)))))

(notation! 'GAMMA-INTEGRAND 'kind 'functoid 'arity 1
           'english "the Gamma integrand t |-> t^($1 - 1) e^(-t)")

(def-functoid 'GAMMA-FUNCTION '(gmz_)
  '(IMPROPER-INT (GAMMA-INTEGRAND gmz_)))

(notation! 'GAMMA-FUNCTION 'kind 'functoid 'arity 1
           'english "Gamma($1)"
           'noun "the Gamma function at $1"
           'tex "\\Gamma($1)")
