;;; poly-fn-vocab.scm -- POLYNOMIAL FUNCTIONS (CA-MONTEL "POLY", 2026-10-26).  Destination: structure-library/.
;;;
;;; The tree's polynomial ring POLY(R) is formal (finitely supported sequences); the analysis files write a
;;; polynomial function as the explicit term  sum_{k < n} c(k) x^k  (series-partial-sum over RR,
;;; cc-series-partial-sum over CC: deriv-polynomial, polynomial-holomorphic, taylor-exact-polynomial).  No
;;; predicate said "f IS a polynomial function".  These definitions say it, over any subring K of CC (RR and
;;; CC are the cases the notes use), on any subset A of K.
;;;
;;;   IS-CC-SUBRING(K)       K subset CC, 0, 1 in K, K closed under + and *
;;;   IS-POLY-FN-ON(K, A, f) f in FUN(A, K) and, for some n in NN and coefficients c in FUN(NN, K) vanishing
;;;                          from n on, f(z) = sum_{j < n} c(j) z^j for every z in A (the sum is
;;;                          CC-SERIES-PARTIAL-SUM; for K = RR its value is real)
;;;   CF-CONS(b, c)          the coefficient sequence b, c(0), c(1), ...  (b + z * (the polynomial of c)),
;;;                          written b 0^k + (1 - 0^k) c(k - 1) so that no IF term is needed
;;;
;;; Library: analysis (the same file serves complex-analysis).  Load window: after the files defining
;;; CC-SERIES-PARTIAL-SUM and NN-MINUS; before poly-fn-laws.
(def-predicate 'IS-CC-SUBRING '(kk)
  '(AND (SUBSET kk CC)
        (AND (IN 0 kk)
             (AND (IN 1 kk)
                  (AND (FORALL psu_ (IMPLIES (IN psu_ kk) (FORALL psv_ (IMPLIES (IN psv_ kk) (IN (+ psu_ psv_) kk)))))
                       (FORALL psu_ (IMPLIES (IN psu_ kk) (FORALL psv_ (IMPLIES (IN psv_ kk) (IN (* psu_ psv_) kk))))))))))
(notation! 'IS-CC-SUBRING 'kind 'predicate 'arity 1 'english "$1 is a subring of the complex numbers")

(def-predicate 'IS-POLY-FN-ON '(kk a f)
  '(AND (SUBSET a kk)
        (AND (IN f (FUN a kk))
             (FORSOME pfn_ (AND (IN pfn_ NN)
               (FORSOME pfc_ (AND (IN pfc_ (FUN NN kk))
                 (AND (FORALL pfk_ (IMPLIES (IN pfk_ NN) (IMPLIES (<= pfn_ pfk_) (= (pfc_ pfk_) 0))))
                      (FORALL pfz_ (IMPLIES (IN pfz_ a)
                        (= (f pfz_) (CC-SERIES-PARTIAL-SUM (VNB-LAMBDA pfj_ NN (* (pfc_ pfj_) (power pfz_ pfj_))) pfn_))))))))))))
(notation! 'IS-POLY-FN-ON 'kind 'predicate 'arity 3 'english "$3 is a polynomial function on $2 with coefficients in $1")

(def-functoid 'CF-CONS '(b c)
  '(VNB-LAMBDA pfk_ NN (+ (* b (power 0 pfk_)) (* (- 1 (power 0 pfk_)) (c (NN-MINUS pfk_ 1))))))
(notation! 'CF-CONS 'kind 'functoid 'arity 2 'english "the sequence $1 followed by $2")

;;; DEGREE (POLY-2).  IS-POLY-DEG(K, A, f, n): f is a polynomial function on A of degree n -- some
;;; coefficient sequence of length n + 1 represents f on A and its n-th coefficient is not 0.  On an
;;; infinite A the degree is unique (poly-deg-unique), and DEG(K, A, f) is that n (deg-value).
(def-predicate 'IS-POLY-DEG '(kk a f n)
  '(AND (SUBSET a kk)
        (AND (IN f (FUN a kk))
             (FORSOME pfc_ (AND (IN pfc_ (FUN NN kk))
               (AND (FORALL pfk_ (IMPLIES (IN pfk_ NN) (IMPLIES (<= (succ n) pfk_) (= (pfc_ pfk_) 0))))
                    (AND (NOT (= (pfc_ n) 0))
                         (FORALL pfz_ (IMPLIES (IN pfz_ a)
                           (= (f pfz_) (CC-SERIES-PARTIAL-SUM (VNB-LAMBDA pfj_ NN (* (pfc_ pfj_) (power pfz_ pfj_))) (succ n))))))))))))
(notation! 'IS-POLY-DEG 'kind 'predicate 'arity 4 'english "$3 is a polynomial function of degree $4 on $2 with coefficients in $1")
(def-functoid 'POLY-FN-DEG '(kk a f)
  '(IOTA pdgn_ (AND (IN pdgn_ NN) (IS-POLY-DEG kk a f pdgn_))))
(notation! 'POLY-FN-DEG 'kind 'functoid 'arity 3 'english "the degree of the polynomial function $3 on $2")
