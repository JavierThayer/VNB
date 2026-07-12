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
(support 'finsum-sq-nonneg
  '(FORALL S (IMPLIES (AND (IN S SET) (IN (CARD S) NN))
     (FORALL a (IMPLIES (IN a (FUN S RR))
       (<= 0 (FINSUM (COMMUTATIVE-RING-ADDITIVE-AG RR-NORMED-FIELD)
                     (VNB-LAMBDA i (* (a i) (a i))) S)))))))
(warrant! 'finsum-sq-nonneg 'well-known
  "0 <= SUM_i a(i)^2: a finite sum of squares is nonnegative, each term being
   a square (rr-sq-nonneg) and finite sums of nonnegatives nonnegative.")

;;; Termwise monotonicity:  a(i) <= b(i) for all i in S  =>  SUM a <= SUM b.
(support 'finsum-le-termwise
  '(FORALL S (IMPLIES (AND (IN S SET) (IN (CARD S) NN))
     (FORALL a (IMPLIES (IN a (FUN S RR)) (FORALL b (IMPLIES (IN b (FUN S RR))
       (IMPLIES (FORALL i (IMPLIES (IN i S) (<= (a i) (b i))))
         (<= (FINSUM (COMMUTATIVE-RING-ADDITIVE-AG RR-NORMED-FIELD) a S)
             (FINSUM (COMMUTATIVE-RING-ADDITIVE-AG RR-NORMED-FIELD) b S))))))))))
(warrant! 'finsum-le-termwise 'well-known
  "Monotonicity of the finite sum: if a(i) <= b(i) for every index i in S then
   SUM_i a(i) <= SUM_i b(i).  Termwise application of rr-le-add over S.")

;;; Triangle inequality for the finite sum:  |SUM a| <= SUM |a|.
(support 'finsum-abs-triangle
  '(FORALL S (IMPLIES (AND (IN S SET) (IN (CARD S) NN))
     (FORALL a (IMPLIES (IN a (FUN S RR))
       (<= (abs (FINSUM (COMMUTATIVE-RING-ADDITIVE-AG RR-NORMED-FIELD) a S))
           (FINSUM (COMMUTATIVE-RING-ADDITIVE-AG RR-NORMED-FIELD)
                   (VNB-LAMBDA i (abs (a i))) S)))))))
(warrant! 'finsum-abs-triangle 'well-known
  "|SUM_i a(i)| <= SUM_i |a(i)|: the triangle inequality for finite sums,
   by induction over S from the two-term rr-abs-triangle.")

;;; Cauchy-Schwarz for finite sums, SQUARE form:
;;;   (SUM_i a(i) b(i))^2 <= (SUM_i a(i)^2)(SUM_i b(i)^2).
(support 'cauchy-schwarz-finite
  '(FORALL S (IMPLIES (AND (IN S SET) (IN (CARD S) NN))
     (FORALL a (IMPLIES (IN a (FUN S RR))
       (FORALL b (IMPLIES (IN b (FUN S RR))
         (<= (* (FINSUM (COMMUTATIVE-RING-ADDITIVE-AG RR-NORMED-FIELD)
                        (VNB-LAMBDA i (* (a i) (b i))) S)
                (FINSUM (COMMUTATIVE-RING-ADDITIVE-AG RR-NORMED-FIELD)
                        (VNB-LAMBDA i (* (a i) (b i))) S))
             (* (FINSUM (COMMUTATIVE-RING-ADDITIVE-AG RR-NORMED-FIELD)
                        (VNB-LAMBDA i (* (a i) (a i))) S)
                (FINSUM (COMMUTATIVE-RING-ADDITIVE-AG RR-NORMED-FIELD)
                        (VNB-LAMBDA i (* (b i) (b i))) S))))))))))
(warrant! 'cauchy-schwarz-finite 'well-known
  "Cauchy-Schwarz for finite sums:  (SUM a_i b_i)^2 <= (SUM a_i^2)(SUM b_i^2).
   The difference is the Lagrange identity SUM_{i<j} (a_i b_j - a_j b_i)^2 >= 0
   (a finite sum of squares).  Square form -- the root form is
   cauchy-schwarz-sqrt below (now that SQRT exists, real-powers.scm).")

;;; ----- root-form inequalities, via SQRT / RPOW (real-powers.scm) -----

;;; Cauchy-Schwarz, ROOT form:  |SUM a_i b_i| <= sqrt(SUM a_i^2) sqrt(SUM b_i^2).
(support 'cauchy-schwarz-sqrt
  '(FORALL S (IMPLIES (AND (IN S SET) (IN (CARD S) NN))
     (FORALL a (IMPLIES (IN a (FUN S RR)) (FORALL b (IMPLIES (IN b (FUN S RR))
       (<= (abs (FINSUM (COMMUTATIVE-RING-ADDITIVE-AG RR-NORMED-FIELD)
                        (VNB-LAMBDA i (* (a i) (b i))) S))
           (* (SQRT (FINSUM (COMMUTATIVE-RING-ADDITIVE-AG RR-NORMED-FIELD)
                            (VNB-LAMBDA i (* (a i) (a i))) S))
              (SQRT (FINSUM (COMMUTATIVE-RING-ADDITIVE-AG RR-NORMED-FIELD)
                            (VNB-LAMBDA i (* (b i) (b i))) S)))))))))))
(warrant! 'cauchy-schwarz-sqrt 'well-known
  "Cauchy-Schwarz, root form:  |SUM a_i b_i| <= sqrt(SUM a_i^2) * sqrt(SUM b_i^2).
   Take square roots in cauchy-schwarz-finite (both sides nonnegative); the
   left side is bounded using |SUM| <= sqrt((SUM)^2).")

;;; Minkowski / l^2 triangle inequality:
;;;   sqrt(SUM (a_i+b_i)^2) <= sqrt(SUM a_i^2) + sqrt(SUM b_i^2).
(support 'minkowski-l2
  '(FORALL S (IMPLIES (AND (IN S SET) (IN (CARD S) NN))
     (FORALL a (IMPLIES (IN a (FUN S RR)) (FORALL b (IMPLIES (IN b (FUN S RR))
       (<= (SQRT (FINSUM (COMMUTATIVE-RING-ADDITIVE-AG RR-NORMED-FIELD)
                         (VNB-LAMBDA i (* (+ (a i) (b i)) (+ (a i) (b i)))) S))
           (+ (SQRT (FINSUM (COMMUTATIVE-RING-ADDITIVE-AG RR-NORMED-FIELD)
                            (VNB-LAMBDA i (* (a i) (a i))) S))
              (SQRT (FINSUM (COMMUTATIVE-RING-ADDITIVE-AG RR-NORMED-FIELD)
                            (VNB-LAMBDA i (* (b i) (b i))) S)))))))))))
(warrant! 'minkowski-l2 'well-known
  "Minkowski (l^2 triangle inequality):  the Euclidean norm
   sqrt(SUM (a_i+b_i)^2) <= sqrt(SUM a_i^2) + sqrt(SUM b_i^2).  Square and apply
   cauchy-schwarz-sqrt to the cross term.  This is the triangle inequality for
   the Euclidean metric on R^n.")

;;; Hoelder's inequality (conjugate exponents 1/p + 1/q = 1):
;;;   SUM |a_i b_i| <= (SUM |a_i|^p)^(1/p) (SUM |b_i|^q)^(1/q).
(support 'holder-finite
  '(FORALL S (IMPLIES (AND (IN S SET) (IN (CARD S) NN))
     (FORALL a (IMPLIES (IN a (FUN S RR)) (FORALL b (IMPLIES (IN b (FUN S RR))
       (FORALL p (IMPLIES (AND (IN p QQ) (< 1 p)) (FORALL q (IMPLIES (AND (IN q QQ) (< 1 q))
         (IMPLIES (= (+ (/ 1 p) (/ 1 q)) 1)
           (<= (FINSUM (COMMUTATIVE-RING-ADDITIVE-AG RR-NORMED-FIELD)
                       (VNB-LAMBDA i (abs (* (a i) (b i)))) S)
               (* (RPOW (FINSUM (COMMUTATIVE-RING-ADDITIVE-AG RR-NORMED-FIELD)
                                (VNB-LAMBDA i (RPOW (abs (a i)) p)) S) (/ 1 p))
                  (RPOW (FINSUM (COMMUTATIVE-RING-ADDITIVE-AG RR-NORMED-FIELD)
                                (VNB-LAMBDA i (RPOW (abs (b i)) q)) S) (/ 1 q))))))))))))))))
(warrant! 'holder-finite 'well-known
  "Hoelder's inequality:  SUM |a_i b_i| <= (SUM |a_i|^p)^(1/p) (SUM |b_i|^q)^(1/q)
   for conjugate exponents 1/p+1/q=1 (p,q>1).  Termwise Young (young-inequality)
   on the normalised vectors, summed.  Cauchy-Schwarz is the p=q=2 case.  Zero
   entries are handled by the 0^p=0 convention (rpow-zero-base).")

;;; ----- Plain-English glosses (PSS review 2026-06-26): 3+-line statements -----
(gloss! 'cauchy-schwarz-finite
  "For any finite index set S and real vectors a, b on S: the square of the dot product SUM a(i)*b(i) is at most the product of the two squared norms, (SUM a(i)^2)*(SUM b(i)^2).  Cauchy-Schwarz for finite sums, square form.")
(gloss! 'minkowski-l2
  "For any finite index set S and real vectors a, b on S: the Euclidean norm of the coordinatewise sum, sqrt(SUM (a_i+b_i)^2), is at most the sum of the Euclidean norms sqrt(SUM a_i^2) + sqrt(SUM b_i^2).  The l^2 triangle inequality.")
(gloss! 'holder-finite
  "For any finite index set S, real vectors a, b on S, and conjugate exponents p,q>1 (rational, 1/p+1/q=1): the sum of |a(i)*b(i)| over S is at most the product of the p-norm of a and the q-norm of b -- (SUM |a_i|^p)^(1/p) times (SUM |b_i|^q)^(1/q).  Holder's inequality for finite sums.")
