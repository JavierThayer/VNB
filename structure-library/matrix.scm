;;; matrix.scm -- MATRIX(S): matrices over a set S.
;;;
;;; A matrix over S is a list of rows; each row is a list of elements of S;
;;; all rows have the same length.  In VNB terms a matrix is an element of
;;; TUPLES(TUPLES S) -- a tuple whose entries are tuples over S -- with the
;;; extra condition that the rows are equilong.  MATRIX(S) is the class of
;;; all such matrices; it is a class-former like TUPLES, FUN, BIJECTION.
;;;
;;; SIZE(M) = [rows, columns] = [LENGTH M, LENGTH(NTH 1 M)].  In a nonempty
;;; matrix every row has the column length, so NTH 1 M is representative;
;;; for the empty matrix (no rows) the column entry is unspecified.
;;;
;;; Dependencies: kernel (TUPLES, LIST, LENGTH, NTH), NN, <=.
;;; MATRIX and SIZE are registered as term-forming heads in wff.scm.

;;; M in MATRIX(S):  M is a list of lists over S, with all rows equilong.
(theory-add-axiom! *current-theory* 'matrix-membership
  '(FORALL S (FORALL M
     (IFF (IN M (MATRIX S))
          (AND (IN M (TUPLES (TUPLES S)))
               (FORALL i (IMPLIES (AND (IN i NN)
                                       (AND (<= 1 i) (<= i (LENGTH M))))
                 (FORALL j (IMPLIES (AND (IN j NN)
                                         (AND (<= 1 j) (<= j (LENGTH M))))
                   (= (LENGTH (NTH i M)) (LENGTH (NTH j M))))))))))))

;;; MATRIX(S) is a set when S is a set -- it is a subclass of the set
;;; TUPLES(TUPLES S).  Installed as an axiom for direct use.
(theory-add-axiom! *current-theory* 'matrix-sethood
  '(FORALL S (IMPLIES (IN S SET) (IN (MATRIX S) SET))))

;;; SIZE(M) = [number of rows, number of columns].
(def-functoid 'SIZE '(M)
  '(LIST (LENGTH M) (LENGTH (NTH 1 M))))

;;; ---------------------------------------------------------------------
;;; MAT(m, n, X) -- the m-by-n matrices over X.
;;;
;;; The fixed-size subset of MATRIX(X): those M whose SIZE is exactly [m, n].
;;; A SEP over MATRIX(X), so it inherits sethood and the sep-membership
;;; characterisation for free (sep-set / sep-mi / sep-me), and is a genuine
;;; subclass of MATRIX(X) -- honouring "Mat(m,n,X) is a subset of Mat(X)".
;;; The multiplication layer (MATMUL over a ring, and the ring structure on
;;; MAT(n,n,A)) is built on top of this in matrix-ring.scm.
;;; NOTE: the SEP binder is P, NOT M -- M would case-fold-collide with the
;;; row-count param m and capture it in (LIST m n).
(def-functoid 'MAT '(m n X)
  '(SEP P (MATRIX X) (= (SIZE P) (LIST m n))))

;;; ENTRY(M, i, j) -- the (i, j) entry of M: the j-th element of the i-th row.
;;; 1-indexed, matching the library's NTH convention (row i is NTH i M).
(def-functoid 'ENTRY '(M i j)
  '(NTH j (NTH i M)))

;;; ---------------------------------------------------------------------
;;; The tabulation bridge -- the layer that makes matrix algebra go through
;;; ENTRY (not raw list surgery).  A matrix identity is proved by showing the
;;; two sides have the same size and equal entries (matrix-entry-extensionality);
;;; a matrix is constructed by tabulating an entry function (MATOF); and the
;;; index range of a row/column is the finite set INTERVAL(1,n).  The ring
;;; structure on MAT(n,n,A) (matrix-ring.scm) is built entirely on this bridge,
;;; so its proofs reduce to FINSUM algebra rather than list/LENGTH/NTH plumbing.
;;; ---------------------------------------------------------------------

;;; INTERVAL(a, b) = { i in NN : a <= i <= b }.  The index set of an m-by-n
;;; matrix's rows / columns is INTERVAL(1, m) / INTERVAL(1, n); it is the finite
;;; set the matrix-product sum ranges over.
(def-functoid 'INTERVAL '(a b)
  '(SEP i NN (AND (<= a i) (<= i b))))

(support 'interval-membership
  '(FORALL a (FORALL b (FORALL i
     (IFF (IN i (INTERVAL a b)) (AND (IN i NN) (AND (<= a i) (<= i b))))))))
(warrant! 'interval-membership 'proof
  "i in INTERVAL(a,b) iff i in NN and a<=i<=b (SEP membership over NN).")

(support 'interval-in-set
  '(FORALL a (FORALL b (IN (INTERVAL a b) SET))))
(warrant! 'interval-in-set 'proof
  "INTERVAL(a,b) is a subclass of NN (a set), hence a set by separation.")

(support 'interval-card
  '(FORALL n (IMPLIES (IN n NN) (= (CARD (INTERVAL 1 n)) n))))
(warrant! 'interval-card 'well-known "|{1,...,n}| = n; INTERVAL(1,n) is finite.")
;; CARD of any interval is a natural number (intervals are finite) -- needed
;; unconditionally (the matmul-assoc dims are not typed NN), where interval-card
;; would require IN n NN.
(support 'interval-card-in-nn
  '(FORALL a (FORALL b (IN (CARD (INTERVAL a b)) NN))))
(warrant! 'interval-card-in-nn 'well-known
  "INTERVAL(a,b) is finite, so its cardinality is a natural number.")

;;; MATOF(m, n, g) -- the m-by-n matrix whose (i, j) entry is g(i, j).
;;; g is applied as a function of the index pair: g(i, j) = g([i, j]).
;;;
;;; NOW DEFINITIONAL (was 3 asserted axioms): MATOF is the UNIQUE matrix of shape
;;; [m, n] whose (i, j) entry is g(i, j).  Its codomain is IMAGE(g, index-box) so
;;; the description is well-posed among matrices (uniqueness = matrix-entry-
;;; extensionality).  The ONLY residual assumption is matof-exists (the tabulation
;;; EXISTS); entry-of-matof and matof-in-mat are then DERIVED via iota-def
;;; (theorem-library/matof-def-proof.scm).  matof-exists is dischargeable once a
;;; general list-tabulation / 2-index recursion primitive is built.
(def-functoid 'MATOF '(m n g)
  '(IOTA P
     (AND (IN P (MAT m n (IMAGE g (CARTESIAN (INTERVAL 1 m) (INTERVAL 1 n)))))
          (FORALL i (IMPLIES (IN i (INTERVAL 1 m))
            (FORALL j (IMPLIES (IN j (INTERVAL 1 n))
              (= (ENTRY P i j) (g i j)))))))))

;; The one honest assumption: a matrix of shape [m,n] with entries g(i,j) EXISTS
;; (the tabulation of g over the index box).  Uniqueness is matrix-entry-
;; extensionality, so this + iota-def pin MATOF down.
(support 'matof-exists
  '(FORALL m (FORALL n (FORALL g
     (FORSOME P
       (AND (IN P (MAT m n (IMAGE g (CARTESIAN (INTERVAL 1 m) (INTERVAL 1 n)))))
            (FORALL i (IMPLIES (IN i (INTERVAL 1 m))
              (FORALL j (IMPLIES (IN j (INTERVAL 1 n))
                (= (ENTRY P i j) (g i j))))))))))))
(warrant! 'matof-exists 'well-known
  "A matrix of shape [m,n] whose (i,j) entry is g(i,j) exists (tabulation of g over
   the index box).  The single assumption behind MATOF; dischargeable via a general
   list-tabulation primitive.")

(support 'matof-in-mat
  '(FORALL m (FORALL n (FORALL X (FORALL g
     (IMPLIES (FORALL i (IMPLIES (IN i (INTERVAL 1 m))
                (FORALL j (IMPLIES (IN j (INTERVAL 1 n))
                  (IN (g i j) X)))))
       (IN (MATOF m n g) (MAT m n X))))))))
(warrant! 'matof-in-mat 'well-known
  "The tabulated matrix MATOF(m,n,g) is an m-by-n matrix over X when every
   value g(i,j) (1<=i<=m, 1<=j<=n) lies in X.")

(support 'entry-of-matof
  '(FORALL m (FORALL n (FORALL g (FORALL i (FORALL j
     (IMPLIES (IN i (INTERVAL 1 m))
     (IMPLIES (IN j (INTERVAL 1 n))
       (= (ENTRY (MATOF m n g) i j) (g i j))))))))))
(warrant! 'entry-of-matof 'well-known
  "The (i,j) entry of the tabulated matrix MATOF(m,n,g) is g(i,j).")

;;; matrix-entry-extensionality -- the workhorse: two m-by-n matrices over X are
;;; equal iff they agree entrywise.  Turns every matrix identity into an entry
;;; identity (provable by FINSUM algebra downstream).
(support 'matrix-entry-extensionality
  '(FORALL m (FORALL n (FORALL X (FORALL P (FORALL Q
     (IMPLIES (IN P (MAT m n X))
     (IMPLIES (IN Q (MAT m n X))
     (IMPLIES (FORALL i (IMPLIES (IN i (INTERVAL 1 m))
                (FORALL j (IMPLIES (IN j (INTERVAL 1 n))
                  (= (ENTRY P i j) (ENTRY Q i j))))))
       (= P Q))))))))))
(warrant! 'matrix-entry-extensionality 'well-known
  "Two m-by-n matrices over X with equal entries are equal (tuple/list
   extensionality applied row- and entry-wise).")

;;; entry-in-carrier -- the entries of a matrix over X lie in X (typing).
(support 'entry-in-carrier
  '(FORALL m (FORALL n (FORALL X (FORALL P (FORALL i (FORALL j
     (IMPLIES (IN P (MAT m n X))
     (IMPLIES (IN i (INTERVAL 1 m))
     (IMPLIES (IN j (INTERVAL 1 n))
       (IN (ENTRY P i j) X)))))))))))
(warrant! 'entry-in-carrier 'well-known
  "The (i,j) entry of an m-by-n matrix over X lies in X.")

;;; ---------------------------------------------------------------------
;;; MATMUL(A, P, Q) -- matrix multiplication over a ring A.
;;;
;;;   (P Q)_{ik} = sum_{j=1}^{n} P_{ij} * Q_{jk}      (product in the ring A)
;;;
;;; a MATOF whose entry function tabulates that sum.  The sum is a FINSUM over
;;; INTERVAL(1,n) in A's additive abelian group (RING-ADDITIVE-AG A, views.scm);
;;; the inner dimension n and the outer m, k are read off SIZE(P), SIZE(Q).
;;; Multiplication is total (garbage-in/garbage-out off its typed domain); the
;;; content lives in matmul-type / matmul-entry and the ring theorems below.
(def-functoid 'MATMUL '(A P Q)
  '(MATOF (NTH 1 (SIZE P)) (NTH 2 (SIZE Q))
     (VNB-LAMBDA (LIST i k)
       (FINSUM (RING-ADDITIVE-AG A)
               (VNB-LAMBDA j ((MUL A) (ENTRY P i j) (ENTRY Q j k)))
               (INTERVAL 1 (NTH 2 (SIZE P)))))))

;;; Typing: an (m x n) times (n x k) product over a ring A is an (m x k) matrix
;;; over the ring's carrier.
(support 'matmul-type
  '(FORALL A (IMPLIES (IS-RING A)
     (FORALL m (FORALL n (FORALL k (FORALL P (FORALL Q
       (IMPLIES (IN P (MAT m n (CARR A)))
       (IMPLIES (IN Q (MAT n k (CARR A)))
         (IN (MATMUL A P Q) (MAT m k (CARR A)))))))))))))
(warrant! 'matmul-type 'reference
  "MAT(m,n,CARR A) x MAT(n,k,CARR A) -> MAT(m,k,CARR A): the tabulated product
   is a matrix whose entries are FINSUMs in the carrier (matof-in-mat +
   finsum-type).")

;;; The entry formula (the computation rule that reduces a product to a FINSUM,
;;; on which every ring axiom below is proved).
(support 'matmul-entry
  '(FORALL A (IMPLIES (IS-RING A)
     (FORALL m (FORALL n (FORALL k (FORALL P (FORALL Q
       (IMPLIES (IN P (MAT m n (CARR A)))
       (IMPLIES (IN Q (MAT n k (CARR A)))
       (FORALL i (IMPLIES (IN i (INTERVAL 1 m))
       (FORALL c (IMPLIES (IN c (INTERVAL 1 k))
         (= (ENTRY (MATMUL A P Q) i c)
            (FINSUM (RING-ADDITIVE-AG A)
                    (VNB-LAMBDA j ((MUL A) (ENTRY P i j) (ENTRY Q j c)))
                    (INTERVAL 1 n)))))))))))))))))
(warrant! 'matmul-entry 'reference
  "(P Q)_{ic} = sum_{j=1}^{n} P_{ij}*Q_{jc}, the product summed in A's additive
   group over j in 1..n (entry-of-matof on the MATMUL tabulation).")

;;; matprod-summand-type: the product-entry summand j |-> P_{ij}.Q_{jc} is a
;;; function [1,n] -> CARR A, for P:MAT(m,n), Q:MAT(n,nn).  The FUN-typing every
;;; finsum-single/two-support call over a matrix-product entry needs.  General in
;;; Q, so one PSS serves matmul-entry collapses for MATUNIT / ELEM-F/G/H / ... .
(support 'matprod-summand-type
  '(FORALL A (IMPLIES (IS-RING A)
     (FORALL m (FORALL n (FORALL nn (FORALL P (FORALL Q (FORALL i (FORALL c
       (IMPLIES (IN P (MAT m n (CARR A)))
       (IMPLIES (IN Q (MAT n nn (CARR A)))
       (IMPLIES (IN i (INTERVAL 1 m))
       (IMPLIES (IN c (INTERVAL 1 nn))
         (IN (VNB-LAMBDA j ((MUL A) (ENTRY P i j) (ENTRY Q j c)))
             (FUN (INTERVAL 1 n) (CARR (RING-ADDITIVE-AG A))))))))))))))))))
(warrant! 'matprod-summand-type 'well-known
  "j |-> P_{ij}.Q_{jc} is a function [1,n] -> CARR A for P:MAT(m,n), Q:MAT(n,nn)
   (entry-in-carrier gives both factors in CARR A; MUL closes; CARR(RAG)=CARR A).")

;;; ---------------------------------------------------------------------
;;; The ring MAT-RING(A, n) of n-by-n matrices over a ring A.
;;;
;;; All operations tabulate an entry function via MATOF, so their action is
;;; read off ENTRY: addition/negation are entrywise, ZEROMAT is the all-zero
;;; matrix, IDENTMAT is the Kronecker delta (ONE on the diagonal, ZERO off it),
;;; and multiplication is MATMUL.  MAT-RING packages them as a RING structure
;;; (carrier MAT(n,n,CARR A); slots ADD MUL NEG ZERO ONE), whose being a ring
;;; (when A is) is the theorem to prove -- mat-ring-is-ring, next.
;;; ---------------------------------------------------------------------

;;; entrywise sum  (P + Q)_{ij} = P_{ij} + Q_{ij}
(def-functoid 'MATADD '(A P Q)
  '(MATOF (NTH 1 (SIZE P)) (NTH 2 (SIZE P))
     (VNB-LAMBDA (LIST i j) ((ADD A) (ENTRY P i j) (ENTRY Q i j)))))

;;; entrywise negation  (-P)_{ij} = -(P_{ij})
(def-functoid 'MATNEG '(A P)
  '(MATOF (NTH 1 (SIZE P)) (NTH 2 (SIZE P))
     (VNB-LAMBDA (LIST i j) ((NEG A) (ENTRY P i j)))))

;;; the all-zero m-by-n matrix over A
(def-functoid 'ZEROMAT '(A m n)
  '(MATOF m n (VNB-LAMBDA (LIST i j) (ZERO A))))

;;; the n-by-n identity matrix: ONE on the diagonal, ZERO off it (Kronecker delta)
(def-functoid 'IDENTMAT '(A n)
  '(MATOF n n (VNB-LAMBDA (LIST i j) (IF (= i j) (ONE A) (ZERO A)))))

;;; MAT-RING(A, n): the ring of n-by-n matrices over A, as a RING 6-tuple
;;; (CARR ADD MUL NEG ZERO ONE).  The ops are curried into binary/unary maps on
;;; the carrier so they fit the RING structure shape.
(def-functoid 'MAT-RING '(A n)
  '(LIST (MAT n n (CARR A))
         (VNB-LAMBDA (LIST P Q) (MATADD A P Q))
         (VNB-LAMBDA (LIST P Q) (MATMUL A P Q))
         (VNB-LAMBDA P (MATNEG A P))
         (ZEROMAT A n n)
         (IDENTMAT A n)))

;;; ---------------------------------------------------------------------
;;; Plumbing the ring proofs cite (matrix-ring-proof.scm): the identity
;;; matrix's entries + typing, the additive-group read-offs of RING-ADDITIVE-AG
;;; (views.scm), and the single-index-support FINSUM fact behind the identity.
;;; ---------------------------------------------------------------------

;;; entries of the identity matrix: ONE on the diagonal, ZERO off it.
(support 'entry-of-identmat
  '(FORALL A (FORALL n (FORALL i (FORALL j
     (IMPLIES (IN i (INTERVAL 1 n))
     (IMPLIES (IN j (INTERVAL 1 n))
       (= (ENTRY (IDENTMAT A n) i j) (IF (= i j) (ONE A) (ZERO A))))))))))
(warrant! 'entry-of-identmat 'reference
  "(IDENTMAT A n)_{ij} = 1 if i=j else 0 (entry-of-matof on the Kronecker delta).")

(support 'identmat-type
  '(FORALL A (IMPLIES (IS-RING A) (FORALL n (IN (IDENTMAT A n) (MAT n n (CARR A)))))))
(warrant! 'identmat-type 'reference
  "IDENTMAT(A,n) is an n-by-n matrix over CARR A (its entries are ONE/ZERO of A).")

;;; RING-ADDITIVE-AG read-offs (the view maps ring's CARR/ZERO to the AG's
;;; CARR/ID; derivable by unfolding the view, named for convenience).
(support 'ras-carr
  '(FORALL A (= (CARR (RING-ADDITIVE-AG A)) (CARR A))))
(warrant! 'ras-carr 'proof "carrier of a ring's additive group is the ring's carrier.")
(support 'ras-id
  '(FORALL A (= (ID (RING-ADDITIVE-AG A)) (ZERO A))))
(warrant! 'ras-id 'proof "identity of a ring's additive group is the ring's zero.")
(support 'ras-op
  '(FORALL A (= (MUL (RING-ADDITIVE-AG A)) (ADD A))))
(warrant! 'ras-op 'proof "operation of a ring's additive group is the ring's addition.")
;; NOTE: ring var is `s' (not A) -- MIT case-folds, so (FORALL A (FORALL a ..))
;; would shadow-collide.  Follows the ring.scm axiom convention.
(support 'ring-neg-in-carr
  '(FORALL s (IMPLIES (IS-RING s)
     (FORALL a (IMPLIES (IN a (CARR s)) (IN ((NEG s) a) (CARR s)))))))
(warrant! 'ring-neg-in-carr 'well-known "NEG closes on the carrier (op NEG CARR CARR).")
(support 'ring-one-in
  '(FORALL s (IMPLIES (IS-RING s) (IN (ONE s) (CARR s)))))
(warrant! 'ring-one-in 'well-known "ONE lies in the carrier.")
(support 'ring-add-right-id
  '(FORALL s (IMPLIES (IS-RING s)
     (FORALL a (IMPLIES (IN a (CARR s)) (= ((ADD s) a (ZERO s)) a))))))
(warrant! 'ring-add-right-id 'well-known "a + 0 = a (ring-add-left-id + comm).")
(support 'ring-add-right-inv
  '(FORALL s (IMPLIES (IS-RING s)
     (FORALL a (IMPLIES (IN a (CARR s)) (= ((ADD s) a ((NEG s) a)) (ZERO s)))))))
(warrant! 'ring-add-right-inv 'well-known "a + (-a) = 0 (ring-add-left-inv + comm).")

;;; finsum-single-support: a finite sum whose summand vanishes off a single
;;; index i0 equals its value there.  (Induction on |S| via finsum-insert: the
;;; peeled non-i0 terms are ID and drop out.)  The engine behind IDENTMAT being
;;; a two-sided identity for MATMUL.
(support 'finsum-single-support
  '(FORALL ag (IMPLIES (IS-ABELIAN-GROUP ag)
     (FORALL S (IMPLIES (IN S SET) (IMPLIES (IN (CARD S) NN)
     (FORALL f (IMPLIES (IN f (FUN S (CARR ag)))
     (FORALL i0 (IMPLIES (IN i0 S)
       (IMPLIES (FORALL j (IMPLIES (IN j S)
                  (IMPLIES (NOT (= j i0)) (= (f j) (ID ag)))))
         (= (FINSUM ag f S) (f i0)))))))))))))
(warrant! 'finsum-single-support 'well-known
  "If f(j)=0 for every j in the finite S except j=i0, then FINSUM(ag,f,S)=f(i0).")

;;; finsum-two-support: a finite sum whose summand vanishes off two indices
;;; i0 /= i1 equals the group product of its values there.  (The two-term analogue
;;; of finsum-single-support; the engine behind elem-g-action's c=l column, where
;;; G=I+r.E[k,l] has support at both the diagonal l and the unit's k.)
(support 'finsum-two-support
  '(FORALL ag (IMPLIES (IS-ABELIAN-GROUP ag)
     (FORALL S (IMPLIES (IN S SET) (IMPLIES (IN (CARD S) NN)
     (FORALL f (IMPLIES (IN f (FUN S (CARR ag)))
     (FORALL i0 (IMPLIES (IN i0 S)
     (FORALL i1 (IMPLIES (IN i1 S)
     (IMPLIES (NOT (= i0 i1))
       (IMPLIES (FORALL j (IMPLIES (IN j S)
                  (IMPLIES (NOT (= j i0)) (IMPLIES (NOT (= j i1)) (= (f j) (ID ag))))))
         (= (FINSUM ag f S) ((MUL ag) (f i0) (f i1)))))))))))))))))
(warrant! 'finsum-two-support 'well-known
  "If f(j)=0 for every j in the finite S except j in {i0,i1} (i0/=i1), then
   FINSUM(ag,f,S) = f(i0) * f(i1) in ag.")

;;; =====================================================================
;;; The matrix-ring axioms -- the obligations toward mat-ring-is-ring.
;;;
;;; STATED here as warranted supports; every one is provable through the
;;; tabulation bridge (matrix-entry-extensionality reduces it to an ENTRY
;;; identity, then matmul-entry / entrywise ring axioms / FINSUM lemmas close
;;; it), and the bridge is validated: the IDENTMAT-left-identity proof was built
;;; to the point where its structure (extensionality reduction + matmul-entry
;;; expansion + the single-surviving-term FINSUM collapse) is fully worked out
;;; (see calculus/identmat-build.scm).  Left asserted for now [[feedback-pss-
;;; over-proof-slog]]; to be discharged systematically alongside mat-ring-is-ring.
;;;
;;;   * additive: MATADD is a commutative group with unit ZEROMAT, inverse MATNEG
;;;     -- entrywise from A's additive group (ring-add-*).
;;;   * multiplicative: MATMUL is associative with unit IDENTMAT
;;;     -- assoc = finsum-fubini + distributivity (the crux); unit = single-
;;;        surviving-term FINSUM.
;;;   * distributive: MATMUL over MATADD -- finsum-additive.
;;; =====================================================================

;;; ---- typing of the operations ----
(support 'matadd-type
  '(FORALL A (IMPLIES (IS-RING A) (FORALL m (FORALL n (FORALL P (FORALL Q
     (IMPLIES (IN P (MAT m n (CARR A)))
     (IMPLIES (IN Q (MAT m n (CARR A)))
       (IN (MATADD A P Q) (MAT m n (CARR A))))))))))))
(warrant! 'matadd-type 'reference "entrywise sum of m-by-n matrices is m-by-n.")
(support 'matneg-type
  '(FORALL A (IMPLIES (IS-RING A) (FORALL m (FORALL n (FORALL P
     (IMPLIES (IN P (MAT m n (CARR A)))
       (IN (MATNEG A P) (MAT m n (CARR A))))))))))
(warrant! 'matneg-type 'reference "entrywise negation of an m-by-n matrix is m-by-n.")
(support 'zeromat-type
  '(FORALL A (IMPLIES (IS-RING A) (FORALL m (FORALL n
       (IN (ZEROMAT A m n) (MAT m n (CARR A))))))))
(warrant! 'zeromat-type 'reference "the all-zero m-by-n matrix is m-by-n over CARR A.")

;;; ---- MATADD is a commutative group (entrywise) ----
(support 'matadd-comm
  '(FORALL A (IMPLIES (IS-RING A) (FORALL m (FORALL n (FORALL P (FORALL Q
     (IMPLIES (IN P (MAT m n (CARR A)))
     (IMPLIES (IN Q (MAT m n (CARR A)))
       (= (MATADD A P Q) (MATADD A Q P)))))))))))
(warrant! 'matadd-comm 'reference "matrix addition is commutative (entrywise, ring-add-comm).")
(support 'matadd-assoc
  '(FORALL A (IMPLIES (IS-RING A) (FORALL m (FORALL n (FORALL P (FORALL Q (FORALL R
     (IMPLIES (IN P (MAT m n (CARR A)))
     (IMPLIES (IN Q (MAT m n (CARR A)))
     (IMPLIES (IN R (MAT m n (CARR A)))
       (= (MATADD A (MATADD A P Q) R) (MATADD A P (MATADD A Q R))))))))))))))
(warrant! 'matadd-assoc 'reference "matrix addition is associative (entrywise, ring-add-assoc).")
(support 'matadd-zero-left
  '(FORALL A (IMPLIES (IS-RING A) (FORALL m (FORALL n (FORALL P
     (IMPLIES (IN P (MAT m n (CARR A)))
       (= (MATADD A (ZEROMAT A m n) P) P))))))))
(warrant! 'matadd-zero-left 'reference "ZEROMAT is a left identity for MATADD (entrywise 0+x=x).")
(support 'matadd-neg-left
  '(FORALL A (IMPLIES (IS-RING A) (FORALL m (FORALL n (FORALL P
     (IMPLIES (IN P (MAT m n (CARR A)))
       (= (MATADD A (MATNEG A P) P) (ZEROMAT A m n)))))))))
(warrant! 'matadd-neg-left 'reference "MATNEG is a left inverse for MATADD (entrywise (-x)+x=0).")

;;; ---- MATMUL: associative, with IDENTMAT as two-sided unit ----
;;; matmul-assoc -- THE crux, PROVEN via finsum-fubini in
;;; theorem-library/matmul-assoc-proof.scm: matrix-entry-extensionality reduces
;;; (PQ)R = P(QR) to an entry identity, both entries are expanded to the SAME
;;; canonical double sum sum_c sum_j (P_{rj} Q_{jc}) R_{c,col} (triple-entry-
;;; left/right), and finsum-fubini interchanges the summation order.  The bricks
;;; that expansion rests on (matmul-entry twice + general-ring distribution under
;;; the FINSUM binder, which the tactic layer cannot yet do -- see the earmarked
;;; finsum-congruence / general-ring finsum-distrib follow-on) are warranted here:
; triple-entry-left / triple-entry-right: PROVEN in
;; theorem-library/triple-entry-proof.scm from the (B) finite-sum bricks
;; (finsum-congruence + general-ring finsum-distrib-left/right-gen) -- formerly
;; warranted here.  matmul-assoc-summand-type (the fubini f-typing) stays warranted.
(support 'matmul-assoc-summand-type
  '(FORALL A (IMPLIES (IS-RING A) (FORALL M (FORALL N (FORALL K (FORALL L (FORALL P (FORALL Q (FORALL R (FORALL ROW (FORALL COL (IMPLIES (IN P (MAT M N (CARR A))) (IMPLIES (IN Q (MAT N K (CARR A))) (IMPLIES (IN R (MAT K L (CARR A))) (IMPLIES (IN ROW (INTERVAL 1 M)) (IMPLIES (IN COL (INTERVAL 1 L)) (IN (VNB-LAMBDA Z ((MUL A) ((MUL A) (ENTRY P ROW (NTH 2 Z)) (ENTRY Q (NTH 2 Z) (NTH 1 Z))) (ENTRY R (NTH 1 Z) COL))) (FUN (CARTESIAN (INTERVAL 1 K) (INTERVAL 1 N)) (CARR (RING-ADDITIVE-AG A)))))))))))))))))))))
(warrant! 'matmul-assoc-summand-type 'well-known
  "the triple-product summand (c,j) |-> (P_{row,j} Q_{j,c}) R_{c,col} is a function INTERVAL(1,k) x INTERVAL(1,n) -> CARR A: the entries lie in CARR A (entry-in-carrier) and MUL closes on CARR A.")
(support 'identmat-left-identity
  '(FORALL A (IMPLIES (IS-RING A) (FORALL m (FORALL n (FORALL P
     (IMPLIES (IN P (MAT m n (CARR A)))
       (= (MATMUL A (IDENTMAT A m) P) P))))))))
(warrant! 'identmat-left-identity 'proof
  "I_m P = P: the (i,c) entry is sum_j delta_ij P_jc, whose only surviving term
   (j=i) is 1*P_ic = P_ic (matmul-entry + entry-of-identmat + finsum-single-
   support + ring-mul-left-id).  Proof structure worked out in identmat-build.scm.")
(support 'identmat-right-identity
  '(FORALL A (IMPLIES (IS-RING A) (FORALL m (FORALL n (FORALL P
     (IMPLIES (IN P (MAT m n (CARR A)))
       (= (MATMUL A P (IDENTMAT A n)) P))))))))
(warrant! 'identmat-right-identity 'proof
  "P I_n = P, the right-handed mirror of identmat-left-identity (only the c=j
   term of sum_j P_ij delta_jc survives).")

;;; ---- distributivity of MATMUL over MATADD ----
(support 'matmul-left-dist
  '(FORALL A (IMPLIES (IS-RING A) (FORALL m (FORALL n (FORALL k (FORALL P (FORALL Q (FORALL R
     (IMPLIES (IN P (MAT m n (CARR A)))
     (IMPLIES (IN Q (MAT n k (CARR A)))
     (IMPLIES (IN R (MAT n k (CARR A)))
       (= (MATMUL A P (MATADD A Q R)) (MATADD A (MATMUL A P Q) (MATMUL A P R)))))))))))))))
(warrant! 'matmul-left-dist 'reference
  "P(Q+R) = PQ + PR: distribute inside the sum termwise (finsum-additive + ring-left-dist).")
(support 'matmul-right-dist
  '(FORALL A (IMPLIES (IS-RING A) (FORALL m (FORALL n (FORALL k (FORALL P (FORALL Q (FORALL R
     (IMPLIES (IN P (MAT m n (CARR A)))
     (IMPLIES (IN Q (MAT m n (CARR A)))
     (IMPLIES (IN R (MAT n k (CARR A)))
       (= (MATMUL A (MATADD A P Q) R) (MATADD A (MATMUL A P R) (MATMUL A Q R)))))))))))))))
(warrant! 'matmul-right-dist 'reference
  "(P+Q)R = PR + QR (finsum-additive + ring-right-dist).")

;;; ---- right-handed companions of the additive-group laws ----
;; matrix.scm asserts only the LEFT zero/inverse laws; the RIGHT ones (needed for
;; the two-sided is-identity / has-inverses clauses of IS-RING) follow by
;; matadd-comm.  Stated so the assembly proof closes them without an in-proof
;; commutativity rewrite.  Same warranted category as the -left originals.
(support 'matadd-zero-right
  '(FORALL A (IMPLIES (IS-RING A) (FORALL m (FORALL n (FORALL P
     (IMPLIES (IN P (MAT m n (CARR A)))
       (= (MATADD A P (ZEROMAT A m n)) P))))))))
(warrant! 'matadd-zero-right 'reference "ZEROMAT is a right identity for MATADD (matadd-comm + zero-left).")
(support 'matadd-neg-right
  '(FORALL A (IMPLIES (IS-RING A) (FORALL m (FORALL n (FORALL P
     (IMPLIES (IN P (MAT m n (CARR A)))
       (= (MATADD A P (MATNEG A P)) (ZEROMAT A m n)))))))))
(warrant! 'matadd-neg-right 'reference "MATNEG is a right inverse for MATADD (matadd-comm + neg-left).")

;; ---- MAT-RING slot read-offs + set-hood / lambda-typing bricks ----
;; The assembly proof of mat-ring-is-ring (theorem-library/mat-ring-proof.scm)
;; unfolds IS-RING into its 14 conjuncts and reduces each through MAT-RING's
;; slots.  These bricks are what the reduction rests on -- all trivially true,
;; warranted because the machinery genuinely cannot compute them:
;;  * the SLOT read-offs (carr/add/mul/neg/zero/one) are pinned per-slot because
;;    the accessor macetes CARR/ADD/MUL/NEG/... are keyed by NAME and last-write-
;;    wins across structures (MUL is slot 2 in monoid/group/AG but slot 3 in RING,
;;    so a global `mac MUL` reduces to the wrong slot);
;;  * mat-ring-add-fun / mat-ring-mul-fun: lam-t types only single-binder lambdas,
;;    so the 2-binder curried ADD/MUL into FUN(CARTESIAN A A, B) is warranted
;;    (NEG, single-binder, is discharged genuinely by lam-t in the proof);
;;  * mat-is-set: MAT(m,n,X) is a SEP over the set MATRIX(X), hence a set.
(support 'mat-is-set
  '(FORALL X (IMPLIES (IN X SET) (FORALL m (FORALL n (IN (MAT m n X) SET))))))
(warrant! 'mat-is-set 'reference "MAT(m,n,X) is a SEP over the set MATRIX(X), hence a set.")
(support 'mat-ring-carr
  '(FORALL a (FORALL n (= (CARR (MAT-RING a n)) (MAT n n (CARR a))))))
(warrant! 'mat-ring-carr 'reference "slot 1 of the MAT-RING tuple.")
(support 'mat-ring-add
  '(FORALL a (FORALL n (= (ADD (MAT-RING a n)) (VNB-LAMBDA (LIST P Q) (MATADD a P Q))))))
(warrant! 'mat-ring-add 'reference "slot 2 of the MAT-RING tuple (entrywise sum).")
(support 'mat-ring-mul
  '(FORALL a (FORALL n (= (MUL (MAT-RING a n)) (VNB-LAMBDA (LIST P Q) (MATMUL a P Q))))))
(warrant! 'mat-ring-mul 'reference "slot 3 of the MAT-RING tuple (matrix product).")
(support 'mat-ring-neg
  '(FORALL a (FORALL n (= (NEG (MAT-RING a n)) (VNB-LAMBDA P (MATNEG a P))))))
(warrant! 'mat-ring-neg 'reference "slot 4 of the MAT-RING tuple (entrywise negation).")
(support 'mat-ring-zero
  '(FORALL a (FORALL n (= (ZERO (MAT-RING a n)) (ZEROMAT a n n)))))
(warrant! 'mat-ring-zero 'reference "slot 5 of the MAT-RING tuple (all-zero matrix).")
(support 'mat-ring-one
  '(FORALL a (FORALL n (= (ONE (MAT-RING a n)) (IDENTMAT a n)))))
(warrant! 'mat-ring-one 'reference "slot 6 of the MAT-RING tuple (identity matrix).")
(support 'mat-ring-add-fun
  '(FORALL a (IMPLIES (IS-RING a) (FORALL n (IMPLIES (IN n NN)
     (IN (VNB-LAMBDA (LIST P Q) (MATADD a P Q))
         (FUN (CARTESIAN (MAT n n (CARR a)) (MAT n n (CARR a))) (MAT n n (CARR a)))))))))
(warrant! 'mat-ring-add-fun 'reference "curried entrywise sum is a function MAT x MAT -> MAT (2-binder).")
(support 'mat-ring-mul-fun
  '(FORALL a (IMPLIES (IS-RING a) (FORALL n (IMPLIES (IN n NN)
     (IN (VNB-LAMBDA (LIST P Q) (MATMUL a P Q))
         (FUN (CARTESIAN (MAT n n (CARR a)) (MAT n n (CARR a))) (MAT n n (CARR a)))))))))
(warrant! 'mat-ring-mul-fun 'reference "curried product is a function MAT x MAT -> MAT (2-binder).")

;; ---- the headline: MAT(n,n,A) is a ring ----
;; PROVEN (not asserted) in theorem-library/mat-ring-proof.scm: the IS-RING iff
;; is unfolded and each of its 14 conjuncts is discharged -- the slot read-offs
;; above reduce MAT-RING's accessors to the matrix ops, then each property clause
;; is closed against the corresponding matrix-ring axiom (matadd-*, matmul-*,
;; identmat-*).  So mat-ring-is-ring is installed there by (qed 'mat-ring-is-ring).
