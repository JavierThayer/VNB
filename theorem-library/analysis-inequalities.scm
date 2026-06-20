;;; analysis-inequalities.scm -- important FINITE-SUM inequalities over RR,
;;; asserted as warranted PSS supports (library phase).  These are the
;;; FINSUM-level analogues of the scalar facts in scalar-inequalities.scm:
;;; Cauchy-Schwarz, the nonnegativity of a sum of squares, the sum triangle
;;; inequality, and termwise monotonicity.  Loads after finsum-additive.scm.
;;;
;;; A finite sum over a finite index set S is  (FINSUM ag f S)  with ag the
;;; additive abelian group of RR-RING; here f is built with  (VNB-LAMBDA i ...)
;;; from the coefficient functions  a, b : S -> RR.  Square roots / p-th powers
;;; are not yet in the surface, so the inequalities are stated in their SQUARE
;;; form (Cauchy-Schwarz) -- the root forms (the l^2 triangle inequality,
;;; Minkowski, the general power mean) follow once SQRT is available and are
;;; left for then.

;;; The additive abelian group of RR, the monoid every sum below runs over.
;;; (Inlined in each wff; named here only as documentation.)
;;;   (COMMUTATIVE-RING-ADDITIVE-AG RR-RING)

;;; Sum of squares is nonnegative:  0 <= SUM_{i in S} a(i)^2.
(support 'finsum-sq-nonneg
  '(FORALL S (IMPLIES (AND (IN S SET) (IN (CARD S) NN))
     (FORALL a (IMPLIES (IN a (FUN S RR))
       (<= 0 (FINSUM (COMMUTATIVE-RING-ADDITIVE-AG RR-RING)
                     (VNB-LAMBDA i (* (a i) (a i))) S)))))))
(warrant! 'finsum-sq-nonneg 'well-known
  "0 <= SUM_i a(i)^2: a finite sum of squares is nonnegative, each term being
   a square (rr-sq-nonneg) and finite sums of nonnegatives nonnegative.")

;;; Termwise monotonicity:  a(i) <= b(i) for all i in S  =>  SUM a <= SUM b.
(support 'finsum-le-termwise
  '(FORALL S (IMPLIES (AND (IN S SET) (IN (CARD S) NN))
     (FORALL a (IMPLIES (IN a (FUN S RR)) (FORALL b (IMPLIES (IN b (FUN S RR))
       (IMPLIES (FORALL i (IMPLIES (IN i S) (<= (a i) (b i))))
         (<= (FINSUM (COMMUTATIVE-RING-ADDITIVE-AG RR-RING) a S)
             (FINSUM (COMMUTATIVE-RING-ADDITIVE-AG RR-RING) b S))))))))))
(warrant! 'finsum-le-termwise 'well-known
  "Monotonicity of the finite sum: if a(i) <= b(i) for every index i in S then
   SUM_i a(i) <= SUM_i b(i).  Termwise application of rr-le-add over S.")

;;; Triangle inequality for the finite sum:  |SUM a| <= SUM |a|.
(support 'finsum-abs-triangle
  '(FORALL S (IMPLIES (AND (IN S SET) (IN (CARD S) NN))
     (FORALL a (IMPLIES (IN a (FUN S RR))
       (<= (abs (FINSUM (COMMUTATIVE-RING-ADDITIVE-AG RR-RING) a S))
           (FINSUM (COMMUTATIVE-RING-ADDITIVE-AG RR-RING)
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
         (<= (* (FINSUM (COMMUTATIVE-RING-ADDITIVE-AG RR-RING)
                        (VNB-LAMBDA i (* (a i) (b i))) S)
                (FINSUM (COMMUTATIVE-RING-ADDITIVE-AG RR-RING)
                        (VNB-LAMBDA i (* (a i) (b i))) S))
             (* (FINSUM (COMMUTATIVE-RING-ADDITIVE-AG RR-RING)
                        (VNB-LAMBDA i (* (a i) (a i))) S)
                (FINSUM (COMMUTATIVE-RING-ADDITIVE-AG RR-RING)
                        (VNB-LAMBDA i (* (b i) (b i))) S))))))))))
(warrant! 'cauchy-schwarz-finite 'well-known
  "Cauchy-Schwarz for finite sums:  (SUM a_i b_i)^2 <= (SUM a_i^2)(SUM b_i^2).
   The difference is the Lagrange identity SUM_{i<j} (a_i b_j - a_j b_i)^2 >= 0
   (a finite sum of squares).  Square form -- the root form
   |SUM a_i b_i| <= sqrt(SUM a_i^2) sqrt(SUM b_i^2) and the l^2 triangle
   inequality (Minkowski) follow once SQRT is in the surface.")
