;;; lp-inequalities.scm -- POWERS IN [0,+inf] AND THE p-TH POWER INTEGRAL I_p.
;;; Definitions only; nothing here is asserted and nothing is proved.  The laws
;;; and the inequalities of Hoelder and Minkowski are proved in
;;; theorem-library/lp-inequalities.scm (MEASURE-4-B, 2026-10-10).
;;;
;;; SOURCE.  Thayer, Construction of Measures, Chapter 2, Section 3 (pp. 14-16):
;;; (27) conjugate exponents, Prop. 2.17 (Hoelder), Lemma 2.18 (Young),
;;; Prop. 2.19 (Minkowski).  In the proof of Prop. 2.17 the notes write, for
;;; r >= 1 and a measurable h : X -> [0,+inf],
;;;
;;;        I_r(h) = ( integral_X h(x)^r dmu(x) )^(1/r).
;;;
;;; THE VOCABULARY (decided by MEASURE-4-B under the brief of 2026-10-09, to be
;;; confirmed by the user).
;;;
;;; (1) EPOW(t, p) -- the power t^p of a point t of [0,+inf], for a real
;;;     exponent p:
;;;
;;;        EPOW(t, p) = +inf            if t = +inf,
;;;                   = RPOW-STAR(t, p) otherwise.
;;;
;;;     RPOW-STAR (theorem-library/rpow-star.scm) is exp(p log t) for t > 0, and
;;;     at t = 0 it is 0 for p > 0 (1 otherwise).  So for p > 0: 0^p = 0,
;;;     (+inf)^p = +inf, and t^p = exp(p log t) for a real t > 0 -- the
;;;     convention of the notes.  The definition is stated for every p; the
;;;     laws carry the guard p > 0 (p real), outside which (+inf)^p = +inf is
;;;     not the convention anyone holds.
;;;
;;; (2) PTWISE-EPOW(omega, f, p) -- the function x |-> f(x)^p on omega, a
;;;     VNB-LAMBDA over the explicit ambient omega, like PTWISE-ETIMES and the
;;;     other pointwise operations of structure-library/integral.scm.
;;;
;;; (3) EP-NORM(omega, cA, mu, p, f) -- the notes' I_p(f):
;;;
;;;        EP-NORM(omega, cA, mu, p, f)
;;;          = EPOW( INTEGRAL(omega, cA, mu, PTWISE-EPOW(omega, f, p)), 1/p ).
;;;
;;;     A point of [0,+inf] for every measurable f : omega -> [0,+inf] and every
;;;     real p > 0.  It is NOT a norm on a space of functions: there is no
;;;     quotient by equality almost everywhere (the user's decision of
;;;     2026-10-09: functions stay total on omega, and "almost everywhere" is a
;;;     clause "except on a null set" in each statement).  The name says
;;;     "extended p-norm" only as a reading of I_p.
;;;
;;; THE BINDERS (ept_ epp_ epx_ epf_ epo_) are used by nothing else in the tree.
;;; `def-functoid' installs only a rewrite macete; the unfold EQUATIONS are
;;; proved as theorems at the head of theorem-library/lp-inequalities.scm, so
;;; `mac-h' can name them.
;;;
;;; Dependencies: extended-reals-pos (RR-POS-STAR, POS-INF), rpow-star
;;; (RPOW-STAR, a def-functoid of theorem-library/rpow-star.scm), integral and
;;; simple-integral (INTEGRAL).  Load after theorem-library/rpow-star and after
;;; structure-library/simple-integral.
;;; ====================================================================

(def-functoid 'EPOW '(ept_ epp_)
  '(IF (= ept_ POS-INF) POS-INF (RPOW-STAR ept_ epp_)))

(notation! 'EPOW 'kind 'functoid 'arity 2
           'english "$1 to the power $2 in [0,+inf]"
           'noun "$1 to the power $2"
           'tex "{$1}^{$2}")

(def-functoid 'PTWISE-EPOW '(epo_ epf_ epp_)
  '(VNB-LAMBDA epx_ epo_ (EPOW (epf_ epx_) epp_)))

(notation! 'PTWISE-EPOW 'kind 'functoid 'arity 3
           'english "the pointwise power $3 of $2 on $1")

(def-functoid 'EP-NORM '(omega cA mu epp_ epf_)
  '(EPOW (INTEGRAL omega cA mu (PTWISE-EPOW omega epf_ epp_)) (recip epp_)))

(notation! 'EP-NORM 'kind 'functoid 'arity 5
           'english "the $4-th power integral norm of $5 over $1 with respect to $3"
           'noun "I_{$4}($5)"
           'tex "I_{$4}({$5})")
