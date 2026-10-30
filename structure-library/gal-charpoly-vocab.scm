;;; gal-charpoly-vocab.scm -- the companion matrix and the characteristic polynomial (galois-theory notes,
;;; section 7, eq. (37), (38), Proposition 1.37) (GALOIS B6, 2026-10-26).  DEFINITIONS ONLY.
;;; Destination: structure-library/gal-charpoly-vocab.scm, library linear-algebra.  Load window: after
;;; matrix.scm (MATOF, ENTRY), determinant.scm (DET), poly-degree.scm (MONOMIAL).
;;;
;;; The monic polynomial p(x) = x^n + a(n) x^(n-1) + ... + a(1) is written with its coefficients
;;; indexed from 1 (a(i) is the coefficient of x^(i-1)); the notes' a_(i-1) is a(i) here.

;;; MONIC-POLY(F, a, n): the coefficient sequence of x^n + a(n) x^(n-1) + ... + a(1).
(def-functoid 'MONIC-POLY '(F a n)
  '(VNB-LAMBDA gmk_ NN (IF (= gmk_ n) (ONE F) (IF (< gmk_ n) (a (succ gmk_)) (ZERO F)))))
(notation! 'MONIC-POLY 'arity 3 'english "the monic polynomial of degree $3 with lower coefficients $2")

;;; COMPANION(F, a, n): the n x n companion matrix (37): 1 on the subdiagonal, -a(i) in the last column.
(def-functoid 'COMPANION '(F a n)
  '(MATOF n n (VNB-LAMBDA (LIST gci_ gcj_) (CARTESIAN (INTERVAL 1 n) (INTERVAL 1 n))
     (IF (= gcj_ n) ((NEG F) (a gci_)) (IF (= gci_ (succ gcj_)) (ONE F) (ZERO F))))))
(notation! 'COMPANION 'arity 3 'english "the companion matrix of the monic polynomial with coefficients $2")

;;; CHAR-MAT(F, A, n) = x I - A, an n x n matrix over F[x].
(def-functoid 'CHAR-MAT '(F A n)
  '(MATOF n n (VNB-LAMBDA (LIST gmi_ gmj_) (CARTESIAN (INTERVAL 1 n) (INTERVAL 1 n))
     ((ADD (POLY F)) (IF (= gmi_ gmj_) (MONOMIAL F (ONE F) 1) (ZERO (POLY F)))
                     ((NEG (POLY F)) (MONOMIAL F (ENTRY A gmi_ gmj_) 0))))))
(notation! 'CHAR-MAT 'arity 3 'english "the matrix x I - $2 over $1[x]")

;;; CHAR-POLY(F, A, n) = det(x I - A), the characteristic polynomial (38).
(def-functoid 'CHAR-POLY '(F A n) '(DET (POLY F) n (CHAR-MAT F A n)))
(notation! 'CHAR-POLY 'arity 3 'english "the characteristic polynomial of $2")
