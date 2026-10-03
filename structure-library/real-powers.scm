;;; real-powers.scm -- the real power RPOW and the square root SQRT.
;;;
;;; RPOW(a, b) is REGISTERED here and DEFINED later in the load, in
;;; theorem-library/rpow-defined.scm (the user's decision, 2026-10-03):
;;;
;;;     RPOW(a, b)  ==  RPOW-STAR(a, b)  ==  if(0 < a, r-exp(b * log(a)), if(0 < b, 0, 1))
;;;
;;; the definitional quasi-equation `rpow-def', and the fifteen laws that stood
;;; here as `well-known' SUPPORTS from 2026-08 to 2026-10-03 -- rpow-pos, -zero,
;;; -one, -add, -mul-base, -pow, -neg, -nat, -zero-base, -zero-zero, -mono-base,
;;; -mono-exp-ge1, -mono-exp-le1, sqrt-rpow, amgm-2-sqrt -- are THEOREMS there,
;;; under the same names and statements, all `modulo 0'.  The registration must
;;; stay this early because the PSS supports of theorem-library/analysis-
;;; inequalities.scm (Hoelder, Minkowski) mention RPOW in their statements, and
;;; RPOW-STAR (LOG, R-EXP) does not exist until late in the load.  The last two
;;; of the original seventeen, young-inequality and bernoulli-rpow, are theorems
;;; in rpow-defined.scm as well, from their real-exponent RPOW-STAR forms in
;;; theorem-library/rpow-star-convexity.scm (the tangent line 1 + z <= exp z
;;; from the MVT, log w <= w - 1, two-point Jensen for log).  Nothing in this
;;; file is asserted any more.
;;;
;;; Operators:
;;;   RPOW(a, b)  = a^b.   Registered here, defined in rpow-defined.scm.
;;;   SQRT(a)     = a^(1/2) for a >= 0.                Always >= 0.  DEFINED.
;;;
;;; Loads after number-systems (RR/QQ, the NN-power `power', recip, abs).

(register-constant! 'RPOW 'operator)

;;; =======================================================================
;;; SQUARE ROOT, DEFINED (2026-08-17).
;;;
;;;     SQRT(a)  ==  IOTA x.  x in RR  and  0 <= x  and  x*x = a
;;;
;;; "the unique nonnegative real whose square is a".  Until today SQRT was a
;;; bare `register-constant!' pinned by five `well-known' supports -- sqrt-nonneg,
;;; sqrt-sq, sqrt-of-sq, sqrt-mono, sqrt-mul -- and those five were the ENTIRE
;;; bill of cc-is-metric-space and of the whole cc-magnitude-* family.  All five
;;; are now THEOREMS, in theorem-library/sqrt-defined.scm, off the description
;;; above: existence is the intermediate value theorem applied to z |-> z*z on
;;; [0, 1+a] (theorem-library/ivt-proof.scm, `modulo 0'; continuity of the
;;; square is theorem-library/sq-continuous.scm), and uniqueness is the
;;; difference of squares against rr-no-zero-divisors.
;;;
;;; THE TYPING `x in RR' INSIDE THE DESCRIPTION IS LOAD-BEARING.  `<=' is
;;; primitive and unguarded: the RR order axioms constrain it on reals without
;;; forbidding it to relate a real to a non-real (the same point ivt-proof.scm's
;;; header makes about its witness).  Drop the typing and uniqueness is not
;;; provable, so the description would not describe.
;;;
;;; `sqrt-rpow' (SQRT(a) = a^(1/2)) is proven in theorem-library/rpow-defined.scm
;;; since 2026-10-03: both sides nonnegative, both square to a, sqrt-unique.
(def-functoid 'SQRT '(a_)
  '(IOTA x_ (AND (IN x_ RR) (AND (<= 0 x_) (= (* x_ x_) a_)))))
(notation! 'SQRT 'kind 'functoid 'arity 1
           'english "the square root of $1"
           'tex "\\sqrt{$1}")

;;; =======================================================================
;;; The power laws for a^b stood here, as supports, until 2026-10-03.  They are
;;; theorems in theorem-library/rpow-defined.scm; the conventions 0^b = 0 (b > 0)
;;; and 0^0 = 1 are rpow-zero-base and rpow-zero-zero there, inherited from
;;; RPOW-STAR's definition by cases.
;;; =======================================================================

;;; =======================================================================
;;; Square root  SQRT(a) = a^(1/2),  a >= 0.
;;;
;;; sqrt-nonneg, sqrt-sq, sqrt-of-sq, sqrt-mono and sqrt-mul stood HERE as
;;; `well-known' supports until 2026-08-17.  They are now PROVEN, from the
;;; definition at the head of this file, in theorem-library/sqrt-defined.scm.
;;; Their statements are unchanged, so every citation of them still reads the
;;; same; only the bills moved.
