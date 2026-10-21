;;; la-elem-vocab.scm -- elementary column matrices as a class, the subgroup they
;;; generate, column equivalence and column step matrices (LA-DET2, 2026-10-18).
;;;
;;; THE SOURCE.  The user's linear-algebra notes (linear-algebra.tex): the definition of
;;; the elementary column matrices F^col[k,l], G^col[r,k,l] and H^col[r,k] ("for
;;; H^col[r,k] we add the requirement that r be invertible in the ring R"), the
;;; definition "Matrices A, B are column equivalent if and only if B can be obtained from
;;; A by a sequence of elementary column operations", the definition of a column step
;;; matrix after the column-step proposition ("all non-zero entries are below the
;;; diagonal, and the diagonal entries are either 0 or 1"), and Corollary 3.13 ("the
;;; n x n elementary column matrices generate the group of invertible matrices").
;;;
;;; THE DEFINITIONS.
;;;   IS-ELEMENTARY(R, n, E)   -- E is one of the n-by-n elementary column matrices:
;;;                               ELEM-F(R,n,k,l) or ELEM-G(R,n,r,k,l) with k, l in [1,n],
;;;                               k /= l, r in CARR R; or ELEM-H(R,n,r,k) with k in
;;;                               [1,n] and r a UNIT of R (r s = 1 = s r for some s).
;;;                               ELEM-F, ELEM-G, ELEM-H: structure-library/elementary-matrix.
;;;   ELEM-GEN(R, n)           -- the set of products of elementary column matrices
;;;                               (the empty product I included): the INTERSECTION-OF the
;;;                               subsets of MAT(n,n,CARR R) that contain IDENTMAT(R,n) and
;;;                               are closed under X |-> X E for E elementary.  The
;;;                               minimal-set definition gives induction over ELEM-GEN for
;;;                               free; the tree has no ordered product of a finite list
;;;                               of matrices (FINPROD is commutative).
;;;   COL-EQUIV(R, n, A, B)    -- A, B column equivalent: B = A P with P in ELEM-GEN(R, n).
;;;                               A "sequence of elementary column operations" applied to
;;;                               A is right multiplication by C_1 ... C_k, i.e. by a
;;;                               member of ELEM-GEN; n is the number of COLUMNS of A.
;;;   IS-COLUMN-STEP(R, m, n, B) -- B (m-by-n) is a column step matrix: B_ij = 0 for
;;;                               i < j, and each diagonal entry B_ii (i <= m, i <= n) is
;;;                               ZERO(R) or ONE(R).
;;;   COL-STEP-ROW(R, n, B, i) -- row i of B is a row of a REDUCED column step matrix:
;;;                               B_ij = 0 for i < j <= n; and when i <= n, B_ii is 0 or
;;;                               1, and if it is 1 then every other entry of row i is 0.
;;;                               Not in the notes: it is the invariant of the proof of
;;;                               the column-step proposition (theorem-library/la-elem-gen),
;;;                               which clears the WHOLE pivot row, so that 3.12 needs no
;;;                               second elimination below the diagonal.
;;; The argument order follows IS-DIAGONAL / IS-LOWER-TRIANGULAR: the ring, the sizes,
;;; the matrix.  3.13 is stated as IS-INVERTIBLE-MAT(R, n, A) iff A in ELEM-GEN(R, n):
;;; the tree has no group of units of MAT-RING, and none is built here.
;;;
;;; Binders: elk_ ell_ elr_ els_ (IS-ELEMENTARY), egs_ egx_ ege_ (ELEM-GEN), cep_
;;; (COL-EQUIV), csi_ csj_ (IS-COLUMN-STEP, COL-STEP-ROW): names no predicate body,
;;; statement or driver uses elsewhere.
;;; Needs: structure-library/matrix (MAT, MATMUL, IDENTMAT, ENTRY, INTERVAL),
;;; elementary-matrix (ELEM-F, ELEM-G, ELEM-H), intersection-of (INTERSECTION-OF).
;;; LOAD WINDOW: after "structure-library/determinant" (load.scm:479; elementary-matrix
;;; is at 472, intersection-of at 158), before "theorem-library/la-elem-gen".
;;; Library: linear-algebra.  No axiom, support or stamp.

(def-predicate 'IS-ELEMENTARY '(R n E)
  '(OR (FORSOME elk_ (FORSOME ell_
         (AND (IN elk_ (INTERVAL 1 n))
              (AND (IN ell_ (INTERVAL 1 n))
                   (AND (NOT (= elk_ ell_)) (= E (ELEM-F R n elk_ ell_)))))))
       (OR (FORSOME elr_ (FORSOME elk_ (FORSOME ell_
             (AND (IN elr_ (CARR R))
                  (AND (IN elk_ (INTERVAL 1 n))
                       (AND (IN ell_ (INTERVAL 1 n))
                            (AND (NOT (= elk_ ell_)) (= E (ELEM-G R n elr_ elk_ ell_)))))))))
           (FORSOME elr_ (FORSOME elk_
             (AND (IN elr_ (CARR R))
                  (AND (FORSOME els_ (AND (IN els_ (CARR R))
                                          (AND (= ((MUL R) elr_ els_) (ONE R))
                                               (= ((MUL R) els_ elr_) (ONE R)))))
                       (AND (IN elk_ (INTERVAL 1 n)) (= E (ELEM-H R n elr_ elk_))))))))))

(def-functoid 'ELEM-GEN '(R n)
  '(INTERSECTION-OF
     (SEP egs_ (POWER (MAT n n (CARR R)))
       (AND (IN (IDENTMAT R n) egs_)
            (FORALL egx_ (IMPLIES (IN egx_ egs_)
              (FORALL ege_ (IMPLIES (IS-ELEMENTARY R n ege_)
                (IN (MATMUL R egx_ ege_) egs_)))))))))

(def-predicate 'COL-EQUIV '(R n A B)
  '(FORSOME cep_ (AND (IN cep_ (ELEM-GEN R n)) (= B (MATMUL R A cep_)))))

(def-predicate 'IS-COLUMN-STEP '(R m n B)
  '(AND (FORALL csi_ (IMPLIES (IN csi_ (INTERVAL 1 m))
          (FORALL csj_ (IMPLIES (IN csj_ (INTERVAL 1 n))
            (IMPLIES (< csi_ csj_) (= (ENTRY B csi_ csj_) (ZERO R)))))))
        (FORALL csi_ (IMPLIES (IN csi_ (INTERVAL 1 m))
          (IMPLIES (IN csi_ (INTERVAL 1 n))
            (OR (= (ENTRY B csi_ csi_) (ZERO R)) (= (ENTRY B csi_ csi_) (ONE R))))))))

(def-predicate 'COL-STEP-ROW '(R n B i)
  '(AND (FORALL csj_ (IMPLIES (IN csj_ (INTERVAL 1 n))
          (IMPLIES (< i csj_) (= (ENTRY B i csj_) (ZERO R)))))
        (IMPLIES (IN i (INTERVAL 1 n))
          (AND (OR (= (ENTRY B i i) (ZERO R)) (= (ENTRY B i i) (ONE R)))
               (IMPLIES (= (ENTRY B i i) (ONE R))
                 (FORALL csj_ (IMPLIES (IN csj_ (INTERVAL 1 n))
                   (IMPLIES (NOT (= csj_ i)) (= (ENTRY B i csj_) (ZERO R))))))))))

(notation! 'IS-ELEMENTARY 'kind 'predicate 'arity 3
           'english "$3 is an elementary column $2-by-$2 matrix over $1")
(notation! 'ELEM-GEN 'kind 'functoid 'arity 2
           'english "the set of products of elementary column $2-by-$2 matrices over $1")
(notation! 'COL-EQUIV 'kind 'predicate 'arity 4
           'english "$3 and $4 are column equivalent")
(notation! 'IS-COLUMN-STEP 'kind 'predicate 'arity 4
           'english "$4 is an $2-by-$3 column step matrix over $1")
(notation! 'COL-STEP-ROW 'kind 'predicate 'arity 4
           'english "row $4 of $3 is a row of a reduced column step matrix")
