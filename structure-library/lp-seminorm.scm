;;; lp-seminorm.scm -- THE L^p SEMINORM OF A REAL-VALUED FUNCTION.
;;; Definitions only; nothing here is asserted and nothing is proved.  The laws
;;; are proved in theorem-library/lp-seminorm.scm (MEASURE-4-C, 2026-10-10).
;;;
;;; SOURCE.  Thayer, Construction of Measures, Ch. 2, Def. 2.22 (p. 16):
;;; ||f||_p = ( integral |f|^p dmu )^(1/p), 1 <= p < inf.
;;;
;;; LP-NORM(omega, cA, mu, p, f) = EP-NORM(omega, cA, mu, p, ABS-FN(omega, f)):
;;; the notes' I_p (EP-NORM, structure-library/lp-inequalities.scm) of the
;;; absolute value |f| (ABS-FN, structure-library/real-integral.scm).  It is a
;;; point of [0, +inf] for every real measurable f and real p > 0; it is a
;;; SEMINORM, not a norm: under the user's decision of 2026-10-09/10 there is no
;;; quotient by equality almost everywhere, and LP-NORM(f - g) = 0 says exactly
;;; that f = g except on a null set (theorem lp-norm-zero-iff).  The parameter
;;; order follows EP-NORM's (omega cA mu p f).  L^p itself (the f with
;;; LP-NORM(f) finite) is not given a name: the statements say "LP-NORM(f) in RR"
;;; where they need it.
;;;
;;; The binders lpp_ lpf_ are used by nothing else in the tree.
;;;
;;; Dependencies: real-integral (ABS-FN), lp-inequalities (EP-NORM).
;;; ====================================================================

(def-functoid 'LP-NORM '(omega cA mu lpp_ lpf_)
  '(EP-NORM omega cA mu lpp_ (ABS-FN omega lpf_)))

(notation! 'LP-NORM 'kind 'functoid 'arity 5
           'english "the L^$4 seminorm of $5 over $1 with respect to $3"
           'noun "||$5||_{$4}"
           'tex "\\|{$5}\\|_{$4}")
