;;; real-integral.scm -- THE INTEGRAL OF A REAL-VALUED FUNCTION: positive and
;;; negative parts, real measurability, integrability, the real integral.
;;; Definitions only; nothing here is asserted and nothing is proved.  The
;;; proofs are theorem-library/real-integral.scm (MEASURE-4-C, 2026-10-10).
;;;
;;; SOURCE.  Thayer, Construction of Measures, Chapter 2, Def. 2.12 (p. 11):
;;; "A measurable function f : X -> [-inf, +inf] is mu-integrable if and only if
;;; the integrals of f+ and f- are finite.  In this case the integral of f is the
;;; integral of f+ minus the integral of f-."  Prop. 2.21 and Prop. 2.24
;;; (pp. 16-17) are proved for real f in the theorem file.
;;;
;;; THE DIVERGENCE FROM THE SOURCE, AND WHY.  The functions here are REAL-valued
;;; and TOTAL on omega (f in FUN(omega, RR)), not [-inf, +inf]-valued and not
;;; "mu-functions defined on a conull set" (Def. 2.20).  The user's decision of
;;; 2026-10-09/10: "almost everywhere" is a clause "except on a null set"
;;; (IS-NULL-SET, structure-library/outer-measure-construction.scm) in the
;;; statement, with no quotient by equality a.e.  An integrable [-inf, +inf]
;;; function is finite off a null set (Prop. 2.23), so nothing is lost for the
;;; integral by asking for real values.
;;;
;;; THE VOCABULARY.
;;;
;;;   * POS-PART(omega, f), NEG-PART(omega, f) -- f+ and f-, the functions
;;;     x |-> max(f(x), 0) and x |-> max(-f(x), 0) on omega.  The maximum is
;;;     written as a case split on the SAME condition 0 <= f(x) in both (the
;;;     condition `abs' is defined by, rr-abs-def), so that one case split at a
;;;     point resolves both parts:
;;;        f+(x) = IF(0 <= f(x), f(x), 0),    f-(x) = IF(0 <= f(x), 0, -f(x)).
;;;     For f in FUN(omega, RR) both are [0, +inf)-valued, hence members of
;;;     FUN(omega, RR-POS-STAR), the functions INTEGRAL (simple-integral.scm)
;;;     integrates; and f(x) = f+(x) - f-(x), |f(x)| = f+(x) + f-(x).
;;;   * ABS-FN(omega, f) -- x |-> |f(x)| on omega.
;;;   * IS-REAL-MEASURABLE-FN(omega, cA, f) -- f in FUN(omega, RR) and both parts
;;;     are IS-MEASURABLE-FN (the tail criterion of integral.scm).  The
;;;     preimage form -- { x : alpha < f(x) } in cA for every real alpha -- is the
;;;     theorem `real-measurable-fn-tails'.  The parts form is the definition
;;;     because every use of measurability in the integral goes through the
;;;     parts.
;;;   * IS-INTEGRABLE(omega, cA, mu, f) -- real measurable, and the integrals of
;;;     both parts are finite (members of RR).  IS-MEASURE is not a conjunct;
;;;     every statement carries it beside.
;;;   * RINTEGRAL(omega, cA, mu, f) -- INTEGRAL(f+) - INTEGRAL(f-).  The term is
;;;     formed for any f; it is the integral of f only under IS-INTEGRABLE, which
;;;     is where every theorem uses it.
;;;
;;; THE INTEGRAL OVER A SET A in cA is not a new head: it is RINTEGRAL of the
;;; function x |-> f(x) * INDICATOR(omega, A)(x), Thayer Def. 2.11 read for a
;;; real f, and the theorems state it that way.  Sums and scalar multiples of
;;; real functions are likewise written as explicit VNB-LAMBDA terms.
;;;
;;; BINDERS ppx_ npx_ afx_ are used by nothing else in the tree.  `def-functoid'
;;; installs only a rewrite macete; the unfold EQUATIONS are proved as theorems
;;; at the head of theorem-library/real-integral.scm so that `mac-h' can name
;;; them.
;;;
;;; Dependencies: integral.scm and simple-integral.scm (IS-MEASURABLE-FN,
;;; INTEGRAL), the kernel (IF, VNB-LAMBDA, FUN), abs (rr-abs-def).
;;; ====================================================================

(def-functoid 'POS-PART '(omega f)
  '(VNB-LAMBDA ppx_ omega (IF (<= 0 (f ppx_)) (f ppx_) 0)))

(def-functoid 'NEG-PART '(omega f)
  '(VNB-LAMBDA npx_ omega (IF (<= 0 (f npx_)) 0 (- (f npx_)))))

(def-functoid 'ABS-FN '(omega f)
  '(VNB-LAMBDA afx_ omega (abs (f afx_))))

(notation! 'POS-PART 'kind 'functoid 'arity 2
           'english "the positive part of $2 on $1")
(notation! 'NEG-PART 'kind 'functoid 'arity 2
           'english "the negative part of $2 on $1")
(notation! 'ABS-FN 'kind 'functoid 'arity 2
           'english "the absolute value of $2 on $1")

(def-predicate 'IS-REAL-MEASURABLE-FN '(omega cA f)
  (conjuncts->and
    (list
      '(IN f (FUN omega RR))
      '(IS-MEASURABLE-FN omega cA (POS-PART omega f))
      '(IS-MEASURABLE-FN omega cA (NEG-PART omega f)))))

(notation! 'IS-REAL-MEASURABLE-FN 'kind 'predicate 'arity 3
           'english "$3 is a measurable real-valued function on $1 with $2")

(def-predicate 'IS-INTEGRABLE '(omega cA mu f)
  (conjuncts->and
    (list
      '(IS-REAL-MEASURABLE-FN omega cA f)
      '(IN (INTEGRAL omega cA mu (POS-PART omega f)) RR)
      '(IN (INTEGRAL omega cA mu (NEG-PART omega f)) RR))))

(notation! 'IS-INTEGRABLE 'kind 'predicate 'arity 4
           'english "$4 is integrable on $1 with respect to the measure $3")

(def-functoid 'RINTEGRAL '(omega cA mu f)
  '(- (INTEGRAL omega cA mu (POS-PART omega f))
      (INTEGRAL omega cA mu (NEG-PART omega f))))

(notation! 'RINTEGRAL 'kind 'functoid 'arity 4
           'english "the integral of the real function $4 over $1 with respect to $3")
