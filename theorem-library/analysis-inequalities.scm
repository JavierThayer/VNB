;;; analysis-inequalities.scm -- important FINITE-SUM inequalities over RR,
;;; asserted as warranted PSS supports (library phase).  These are the
;;; FINSUM-level analogues of the scalar facts in scalar-inequalities.scm:
;;; Cauchy-Schwarz, the nonnegativity of a sum of squares, the sum triangle
;;; inequality, and termwise monotonicity.  Loads after finsum-additive.scm.
;;;
;;; A finite sum over a finite index set S is  (FINSUM ag f S)  with ag the
;;; additive abelian group of RR-NORMED-FIELD; here f is built with  (VNB-LAMBDA i ...)
;;; from the coefficient functions  a, b : S -> RR.  Square roots / p-th powers
;;; are not yet in the surface, so the inequalities are stated in their SQUARE
;;; form (Cauchy-Schwarz) -- the root forms (the l^2 triangle inequality,
;;; Minkowski, the general power mean) follow once SQRT is available and are
;;; left for then.

;;; The additive abelian group of RR, the monoid every sum below runs over.
;;; (Inlined in each wff; named here only as documentation.)
;;;   (COMMUTATIVE-RING-ADDITIVE-AG RR-NORMED-FIELD)

;;; Sum of squares is nonnegative:  0 <= SUM_{i in S} a(i)^2.
;;; finsum-sq-nonneg RETIRED 2026-09-18 (rake batch 5): proven modulo 0 in theorem-library/rake-inequalities.scm

;;; Termwise monotonicity:  a(i) <= b(i) for all i in S  =>  SUM a <= SUM b.
;;; finsum-le-termwise RETIRED 2026-09-18 (rake batch 5): proven modulo 0 in theorem-library/rake-inequalities.scm

;;; Triangle inequality for the finite sum:  |SUM a| <= SUM |a|.
;;; finsum-abs-triangle RETIRED 2026-09-18 (rake batch 5): proven modulo 0 in theorem-library/rake-inequalities.scm

;;; Cauchy-Schwarz for finite sums, SQUARE form:
;;;   (SUM_i a(i) b(i))^2 <= (SUM_i a(i)^2)(SUM_i b(i)^2).
;;; cauchy-schwarz-finite RAKE-ASM-B1 2026-10-12: PROVEN in theorem-library/rake-asm-b1.scm under this name; the assumption is retired.

;;; ----- root-form inequalities, via SQRT / RPOW (real-powers.scm) -----

;;; Cauchy-Schwarz, ROOT form:  |SUM a_i b_i| <= sqrt(SUM a_i^2) sqrt(SUM b_i^2).
;;; cauchy-schwarz-sqrt RAKE-ASM-B1 2026-10-12: PROVEN in theorem-library/rake-asm-b1.scm under this name; the assumption is retired.

;;; Minkowski / l^2 triangle inequality:
;;;   sqrt(SUM (a_i+b_i)^2) <= sqrt(SUM a_i^2) + sqrt(SUM b_i^2).
;;; minkowski-l2 RAKE-ASM-B1 2026-10-12: PROVEN in theorem-library/rake-asm-b1.scm under this name; the assumption is retired.

;;; Hoelder's inequality (conjugate exponents 1/p + 1/q = 1):
;;;   SUM |a_i b_i| <= (SUM |a_i|^p)^(1/p) (SUM |b_i|^q)^(1/q).
;;; holder-finite RAKE-ASM-B1 2026-10-12: PROVEN in theorem-library/rake-asm-b1.scm under this name; the assumption is retired.

;;; ----- Plain-English glosses (PSS review 2026-06-26): 3+-line statements -----
(gloss! 'cauchy-schwarz-finite
  "For any finite index set S and real vectors a, b on S: the square of the dot product SUM a(i)*b(i) is at most the product of the two squared norms, (SUM a(i)^2)*(SUM b(i)^2).  Cauchy-Schwarz for finite sums, square form.")
(gloss! 'minkowski-l2
  "For any finite index set S and real vectors a, b on S: the Euclidean norm of the coordinatewise sum, sqrt(SUM (a_i+b_i)^2), is at most the sum of the Euclidean norms sqrt(SUM a_i^2) + sqrt(SUM b_i^2).  The l^2 triangle inequality.")
(gloss! 'holder-finite
  "For any finite index set S, real vectors a, b on S, and conjugate exponents p,q>1 (rational, 1/p+1/q=1): the sum of |a(i)*b(i)| over S is at most the product of the p-norm of a and the q-norm of b -- (SUM |a_i|^p)^(1/p) times (SUM |b_i|^q)^(1/q).  Holder's inequality for finite sums.")
