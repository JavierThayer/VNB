;;; real-powers.scm -- rational powers of positive reals,  a^b  for a > 0 real
;;; and b in QQ, introduced AXIOMATICALLY (warranted supports), together with
;;; the square root SQRT.  The alternative -- constructing a^b via the
;;; intermediate value theorem (b |-> a^b as the continuous extension of the
;;; rational-power map) -- would delay every root-form inequality behind a
;;; substantial development; positing the power laws now puts Young, AM-GM,
;;; Hoelder, Minkowski and the l^2 triangle inequality into the PSS today.
;;; (A later IVT construction can DISCHARGE these axioms; until then they are
;;; warranted 'well-known.)  For SQRT that construction has now HAPPENED --
;;; see below; for RPOW it has not.
;;;
;;; Operators:
;;;   RPOW(a, b)  = a^b   for a > 0 (real), b in QQ.   Always > 0.  Axiomatic.
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
;;; `sqrt-rpow' below is deliberately NOT retired: it ties this defined SQRT to
;;; a still-axiomatic RPOW, and is a claim about RPOW, not about SQRT.
(def-functoid 'SQRT '(a_)
  '(IOTA x_ (AND (IN x_ RR) (AND (<= 0 x_) (= (* x_ x_) a_)))))
(notation! 'SQRT 'kind 'functoid 'arity 1
           'english "the square root of $1"
           'tex "\\sqrt{$1}")

;;; =======================================================================
;;; The power laws for  a^b,  a > 0, b in QQ.

;;; Typing + positivity:  a^b is a positive real.
(support 'rpow-pos
  '(FORALL a (IMPLIES (AND (IN a RR) (< 0 a))
     (FORALL b (IMPLIES (IN b QQ)
       (AND (IN (RPOW a b) RR) (< 0 (RPOW a b))))))))
(warrant! 'rpow-pos 'well-known
  "a^b is a positive real for a > 0 and rational b.  Axiomatic introduction of
   RPOW; provable once a^b is constructed (IVT continuous extension).")

;;; a^0 = 1.
(support 'rpow-zero
  '(FORALL a (IMPLIES (AND (IN a RR) (< 0 a)) (= (RPOW a 0) 1))))
(warrant! 'rpow-zero 'well-known "a^0 = 1 for a > 0.")

;;; a^1 = a.
(support 'rpow-one
  '(FORALL a (IMPLIES (AND (IN a RR) (< 0 a)) (= (RPOW a 1) a))))
(warrant! 'rpow-one 'well-known "a^1 = a for a > 0.")

;;; a^(b+d) = a^b * a^d   (the additive law).
(support 'rpow-add
  '(FORALL a (IMPLIES (AND (IN a RR) (< 0 a))
     (FORALL b (IMPLIES (IN b QQ) (FORALL d (IMPLIES (IN d QQ)
       (= (RPOW a (+ b d)) (* (RPOW a b) (RPOW a d))))))))))
(warrant! 'rpow-add 'well-known
  "a^(b+d) = a^b * a^d, the defining homomorphism QQ -> (RR>0, *) of x |-> a^x.")

;;; (a*c)^b = a^b * c^b   (multiplicativity in the base).
(support 'rpow-mul-base
  '(FORALL a (IMPLIES (AND (IN a RR) (< 0 a))
     (FORALL c (IMPLIES (AND (IN c RR) (< 0 c))
       (FORALL b (IMPLIES (IN b QQ)
         (= (RPOW (* a c) b) (* (RPOW a b) (RPOW c b))))))))))
(warrant! 'rpow-mul-base 'well-known "(a*c)^b = a^b * c^b for a,c > 0.")

;;; (a^b)^d = a^(b*d)   (the iterated-power law).
(support 'rpow-pow
  '(FORALL a (IMPLIES (AND (IN a RR) (< 0 a))
     (FORALL b (IMPLIES (IN b QQ) (FORALL d (IMPLIES (IN d QQ)
       (= (RPOW (RPOW a b) d) (RPOW a (* b d))))))))))
(warrant! 'rpow-pow 'well-known
  "(a^b)^d = a^(b*d) for a > 0.  In particular (a^(1/n))^n = a: a^(1/n) is the
   n-th root.")

;;; a^(-b) = 1/a^b.
(support 'rpow-neg
  '(FORALL a (IMPLIES (AND (IN a RR) (< 0 a))
     (FORALL b (IMPLIES (IN b QQ)
       (= (RPOW a (- 0 b)) (recip (RPOW a b))))))))
(warrant! 'rpow-neg 'well-known
  "a^(-b) = 1/a^b for a > 0 (the b + (-b) = 0 case of rpow-add).")

;;; Agreement with the NN-power `power':  a^n = power(a,n) for n in NN.
(support 'rpow-nat
  '(FORALL a (IMPLIES (AND (IN a RR) (< 0 a))
     (FORALL n (IMPLIES (IN n NN) (= (RPOW a n) (power a n)))))))
(warrant! 'rpow-nat 'well-known
  "a^n agrees with the natural-number power (power a n) for n in NN -- RPOW
   extends the existing integer power.  NN subseteq QQ, so the LHS is typed.")

;;; The standard convention  0^b = 0  for b > 0 (so RPOW is total on a >= 0 for
;;; positive exponents; this is what makes Hoelder hold with zero entries).
;;; The companion 0^0 = 1 is rpow-zero-zero below -- the convention adopted
;;; project-wide and shared with the NN-power `power' ((power 0 0) = 1).
(support 'rpow-zero-base
  '(FORALL b (IMPLIES (AND (IN b QQ) (< 0 b)) (= (RPOW 0 b) 0))))
(warrant! 'rpow-zero-base 'well-known
  "0^b = 0 for rational b > 0 (the limiting/standard convention), extending
   RPOW to base 0 with positive exponent.  The exponent is strictly positive,
   so this never touches 0^0 (= 1, rpow-zero-zero).")

;;; 0^0 = 1: the project-wide adopted convention, consistent with the NN-power
;;; ((power 0 0) = 1) and with rpow-zero (a^0 = 1 for a > 0), so a^0 = 1 for
;;; EVERY a >= 0.
(support 'rpow-zero-zero
  '(= (RPOW 0 0) 1))
(warrant! 'rpow-zero-zero 'well-known
  "0^0 = 1 -- the standard convention adopted project-wide and matching the
   NN-power (power 0 0) = 1.  Together with rpow-zero (a^0 = 1 for a > 0) this
   gives a^0 = 1 for all a >= 0.")

;;; ----- monotonicity -----

;;; Increasing in the base for a nonnegative exponent:
;;;   0 < a <= c, 0 <= b  =>  a^b <= c^b.
(support 'rpow-mono-base
  '(FORALL a (IMPLIES (AND (IN a RR) (< 0 a))
     (FORALL c (IMPLIES (AND (IN c RR) (<= a c))
       (FORALL b (IMPLIES (AND (IN b QQ) (<= 0 b))
         (<= (RPOW a b) (RPOW c b)))))))))
(warrant! 'rpow-mono-base 'well-known
  "a^b is nondecreasing in the base for a nonnegative exponent: 0<a<=c and
   0<=b give a^b <= c^b.")

;;; Increasing in the exponent when the base is >= 1:
;;;   a >= 1, b <= d  =>  a^b <= a^d.
(support 'rpow-mono-exp-ge1
  '(FORALL a (IMPLIES (AND (IN a RR) (<= 1 a))
     (FORALL b (IMPLIES (IN b QQ) (FORALL d (IMPLIES (AND (IN d QQ) (<= b d))
       (<= (RPOW a b) (RPOW a d)))))))))
(warrant! 'rpow-mono-exp-ge1 'well-known
  "For base a >= 1, a^x is nondecreasing in x: b <= d gives a^b <= a^d.")

;;; Decreasing in the exponent when 0 < base <= 1:
;;;   0 < a <= 1, b <= d  =>  a^d <= a^b.
(support 'rpow-mono-exp-le1
  '(FORALL a (IMPLIES (AND (IN a RR) (AND (< 0 a) (<= a 1)))
     (FORALL b (IMPLIES (IN b QQ) (FORALL d (IMPLIES (AND (IN d QQ) (<= b d))
       (<= (RPOW a d) (RPOW a b)))))))))
(warrant! 'rpow-mono-exp-le1 'well-known
  "For base 0 < a <= 1, a^x is nonincreasing in x: b <= d gives a^d <= a^b.")

;;; =======================================================================
;;; Square root  SQRT(a) = a^(1/2),  a >= 0.
;;;
;;; sqrt-nonneg, sqrt-sq, sqrt-of-sq, sqrt-mono and sqrt-mul stood HERE as
;;; `well-known' supports until 2026-08-17.  They are now PROVEN, from the
;;; definition at the head of this file, in theorem-library/sqrt-defined.scm.
;;; Their statements are unchanged, so every citation of them still reads the
;;; same; only the bills moved.

(support 'sqrt-rpow
  '(FORALL a (IMPLIES (AND (IN a RR) (< 0 a)) (= (SQRT a) (RPOW a (/ 1 2))))))
(warrant! 'sqrt-rpow 'well-known "sqrt(a) = a^(1/2) for a > 0 (SQRT is the 1/2 power).")

;;; =======================================================================
;;; Scalar inequalities unlocked by powers/roots (warranted PSS supports).

;;; AM-GM for two terms, ROOT form:  sqrt(a*b) <= (a+b)/2  for a,b >= 0.
(support 'amgm-2-sqrt
  '(FORALL a (IMPLIES (AND (IN a RR) (<= 0 a)) (FORALL b (IMPLIES (AND (IN b RR) (<= 0 b))
     (<= (SQRT (* a b)) (/ (+ a b) 2)))))))
(warrant! 'amgm-2-sqrt 'well-known
  "Geometric mean <= arithmetic mean (two terms):  sqrt(a*b) <= (a+b)/2 for
   a,b >= 0.  Squaring is the SOS fact 4ab <= (a+b)^2 (rr-amgm-2).")

;;; Young's inequality (general conjugate exponents):
;;;   a,b > 0, p,q > 1 rational, 1/p + 1/q = 1  =>  a*b <= a^p/p + b^q/q.
(support 'young-inequality
  '(FORALL a (IMPLIES (AND (IN a RR) (< 0 a)) (FORALL b (IMPLIES (AND (IN b RR) (< 0 b))
     (FORALL p (IMPLIES (AND (IN p QQ) (< 1 p)) (FORALL q (IMPLIES (AND (IN q QQ) (< 1 q))
       (IMPLIES (= (+ (/ 1 p) (/ 1 q)) 1)
         (<= (* a b) (+ (/ (RPOW a p) p) (/ (RPOW b q) q)))))))))))))
(warrant! 'young-inequality 'well-known
  "Young's inequality:  a*b <= a^p/p + b^q/q  for a,b > 0 and conjugate
   exponents 1/p + 1/q = 1 (p,q > 1).  By concavity of log; the p=q=2 case is
   rr-young-2.  The engine for Hoelder's inequality.")

;;; Bernoulli's inequality, real (rational) exponent >= 1:
;;;   1 + x > 0, b >= 1 rational  =>  1 + b*x <= (1+x)^b.
(support 'bernoulli-rpow
  '(FORALL x (IMPLIES (AND (IN x RR) (< 0 (+ 1 x)))
     (FORALL b (IMPLIES (AND (IN b QQ) (<= 1 b))
       (<= (+ 1 (* b x)) (RPOW (+ 1 x) b)))))))
(warrant! 'bernoulli-rpow 'well-known
  "Bernoulli with real exponent:  (1+x)^b >= 1 + b*x  for 1+x > 0 and rational
   b >= 1 (convexity of t |-> (1+x)^t, or t^b).  For 0 <= b <= 1 the inequality
   reverses; stated here for the b >= 1 branch.")

;;; ----- Plain-English gloss (PSS review 2026-06-26): 3+-line statement -----
(gloss! 'young-inequality
  "For positive reals a, b and conjugate exponents p,q>1 (rational, 1/p+1/q=1): the product a*b is at most a^p/p + b^q/q.  Young's inequality -- the engine behind Holder.")
