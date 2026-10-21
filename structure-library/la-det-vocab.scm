;;; la-det-vocab.scm -- triangular matrices and the formal adjoint (LA-DET, 2026-10-18).
;;;
;;; THE SOURCE.  The user's linear-algebra notes (linear-algebra.tex): the corollary
;;; after the expansion by minors ("If A is a lower triangular matrix, then det A is the
;;; product of the diagonal entries.  The same is true for upper triangular matrices")
;;; and the definition before Cramer's rule ("The formal adjoint of a matrix A is the
;;; matrix A~ with entries a~_ij = (-1)^(i+j) det(A[j, i])").  The notes define the first
;;; word after the column-step proposition: "A lower triangular matrix is one in which all
;;; non-zero entries are below the diagonal" (on or below: the diagonal entries are free);
;;; "upper triangular" is the mirror image, used in the corollary without a definition.
;;;
;;; THE DEFINITIONS.
;;;   IS-LOWER-TRIANGULAR(A, n, D)  -- every entry of D ABOVE the diagonal is ZERO(A):
;;;                                    i, j in [1, n], i < j  =>  D_ij = 0.
;;;   IS-UPPER-TRIANGULAR(A, n, D)  -- every entry BELOW the diagonal is ZERO(A).
;;;   ADJ(R, n, A)                  -- the formal adjoint of the (n+1)-square matrix A:
;;;                                    the (n+1)-square tabulation with (i, j) entry
;;;                                    (-1)^(i+j) det(R, n, MINOR(A, j, i, n)).
;;; The argument order of the predicates follows IS-DIAGONAL(A, m, n, D)
;;; (structure-library/mat-equiv.scm): the ring first, then the size, then the matrix.
;;; ADJ is stated at size succ(n) for the reason det-expand-row and det-expand-col are:
;;; the cofactors of an (n+1)-square matrix are n-square, and DET's recursion is keyed on
;;; succ(n); the 0-by-0 matrix has no cofactors.  The sign is the one DET's own
;;; recursion uses, MPOW of -1 in R's multiplicative monoid.  The notes write the product
;;; of the diagonal entries as a finite product; it is PROD-RING(R, k |-> D_kk, [1, n])
;;; (structure-library/finprod.scm), written inline in the theorems, not named.
;;;
;;; Binders: ltu_ / ltv_ (the predicates), adu_ / adv_ (the tabulation): names no
;;; predicate body, statement or driver uses.
;;; Needs: structure-library/matrix (MATOF, ENTRY, INTERVAL), determinant (DET, MINOR),
;;; views (RING-MULTIPLICATIVE-MONOID), monoid-power (MPOW).
;;; LOAD WINDOW: after "structure-library/determinant" (load.scm:479), before
;;; "theorem-library/la-det-adjoint".  Library: linear-algebra.
;;; No axiom, support or stamp.

(def-predicate 'IS-LOWER-TRIANGULAR '(A n D)
  '(FORALL ltu_ (FORALL ltv_
     (IMPLIES (IN ltu_ (INTERVAL 1 n)) (IMPLIES (IN ltv_ (INTERVAL 1 n))
       (IMPLIES (< ltu_ ltv_) (= (ENTRY D ltu_ ltv_) (ZERO A))))))))

(def-predicate 'IS-UPPER-TRIANGULAR '(A n D)
  '(FORALL ltu_ (FORALL ltv_
     (IMPLIES (IN ltu_ (INTERVAL 1 n)) (IMPLIES (IN ltv_ (INTERVAL 1 n))
       (IMPLIES (< ltv_ ltu_) (= (ENTRY D ltu_ ltv_) (ZERO A))))))))

(def-functoid 'ADJ '(R n A)
  '(MATOF (succ n) (succ n)
     (VNB-LAMBDA (LIST adu_ adv_) (CARTESIAN (INTERVAL 1 (succ n)) (INTERVAL 1 (succ n)))
       ((MUL R) (MPOW (RING-MULTIPLICATIVE-MONOID R) ((NEG R) (ONE R)) (+ adu_ adv_))
                (DET R n (MINOR A adv_ adu_ n))))))

(notation! 'IS-LOWER-TRIANGULAR 'kind 'predicate 'arity 3 'english "$3 is a lower triangular $2-by-$2 matrix over $1")
(notation! 'IS-UPPER-TRIANGULAR 'kind 'predicate 'arity 3 'english "$3 is an upper triangular $2-by-$2 matrix over $1")
(notation! 'ADJ 'kind 'functoid 'arity 3 'english "adj($3)")
