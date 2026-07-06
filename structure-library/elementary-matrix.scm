;;; elementary-matrix.scm -- matrix units and elementary column operations
;;; (algebraic-numbers.pdf ch.3, Def 3.2-3.7).  The whole elementary-operation
;;; theory is over a COMMUTATIVE ring here; the euclidean assumption only enters
;;; later, at the reduction-to-diagonal (Smith) step, NOT here.
;;;
;;; Built on the tabulation bridge of matrix.scm (MATOF/ENTRY/matmul-entry/
;;; finsum-single-support), so proofs reduce to FINSUM algebra, not list surgery.
;;;
;;; Brick 1 (this file): the matrix unit E[k,l] = MATUNIT(A,n,k,l) and Lemma 3.3,
;;; the column-shift entry formula for right-multiplication by E[k,l].  The
;;; elementary column matrices F/G/H and Prop 3.5 (their action) build on this.

;;; ---------------------------------------------------------------------
;;; MATUNIT(A, n, k, l) -- the n-by-n matrix unit E_n[k,l]: ONE at position
;;; (k,l), ZERO everywhere else (the book's E_n[k,l]).  A MATOF over the
;;; ring's ONE/ZERO, in the same style as IDENTMAT.
(def-functoid 'MATUNIT '(A n k l)
  '(MATOF n n (VNB-LAMBDA (LIST i j)
     (IF (AND (= i k) (= j l)) (ONE A) (ZERO A)))))

;;; entries of a matrix unit: ONE iff (i,j) = (k,l), else ZERO.
(support 'entry-of-matunit
  '(FORALL A (FORALL n (FORALL k (FORALL l (FORALL i (FORALL j
     (IMPLIES (IN i (INTERVAL 1 n))
     (IMPLIES (IN j (INTERVAL 1 n))
       (= (ENTRY (MATUNIT A n k l) i j)
          (IF (AND (= i k) (= j l)) (ONE A) (ZERO A))))))))))))
(warrant! 'entry-of-matunit 'reference
  "(MATUNIT A n k l)_{ij} = 1 if (i=k and j=l) else 0 (entry-of-matof on the
   (k,l) unit-entry function).")

;;; typing: the matrix unit is an n-by-n matrix over the ring's carrier.
(support 'matunit-type
  '(FORALL A (IMPLIES (IS-RING A) (FORALL n (FORALL k (FORALL l
     (IN (MATUNIT A n k l) (MAT n n (CARR A)))))))))
(warrant! 'matunit-type 'reference
  "MATUNIT(A,n,k,l) is an n-by-n matrix over CARR A: its entries are ONE/ZERO of
   A (matof-in-mat on the unit-entry function).")

;;; ---------------------------------------------------------------------
;;; Lemma 3.3 -- the column-shift formula.  For an m-by-n matrix P over a ring A,
;;; right-multiplication by the n-by-n unit E[k,l] moves the k-th column of P into
;;; the l-th column and zeroes the rest:
;;;
;;;     (P . E[k,l])_{ij} = P_{ik}   if j = l,   else 0.
;;;
;;; This is the engine behind every elementary column operation (Prop 3.5): the
;;; elementary matrices F/G/H are built from I and matrix units, so their action
;;; on columns reduces to this lemma plus the identity's action.
;;;
;;; Proof route (matmul-entry + entry-of-matunit + finsum-single-support), the
;;; same finsum-collapse shape as identmat-left-identity in matrix.scm:
;;;   matmul-entry expands (P.E)_{ij} to FINSUM_{s in 1..n} P_{is} . E[k,l]_{sj};
;;;   entry-of-matunit rewrites E[k,l]_{sj} = (1 if s=k and j=l else 0).
;;;   Case j=l: the summand is P_{ik} at s=k (ring-mul-right-id) and P_{is}.0=0
;;;     off it (ring-mul-right-zero), so finsum-single-support yields P_{ik}.
;;;   Case j/=l: every summand is P_{is}.0 = 0 (ring-mul-right-zero), so the sum
;;;     is 0 (finsum of the zero function).
;;; PROVEN to (qed) in theorem-library/matunit-shift-proof.scm (trust: none) -- no
;;; longer asserted here.  The three PSS supports below feed that proof.
;; the product-entry summand j |-> P_{ij}.E[k,l]_{jc} is a function
;; INTERVAL(1,n) -> CARR A; the FUN-typing finsum-single-support needs.
(support 'matunit-summand-type
  '(FORALL A (IMPLIES (IS-RING A)
     (FORALL m (FORALL n (FORALL P (FORALL k (FORALL l (FORALL i (FORALL c
       (IMPLIES (IN P (MAT m n (CARR A)))
       (IMPLIES (IN i (INTERVAL 1 m))
       (IMPLIES (IN c (INTERVAL 1 n))
         (IN (VNB-LAMBDA j ((MUL A) (ENTRY P i j) (ENTRY (MATUNIT A n k l) j c)))
             (FUN (INTERVAL 1 n) (CARR (RING-ADDITIVE-AG A)))))))))))))))))
(warrant! 'matunit-summand-type 'well-known
  "j |-> P_{ij}.E[k,l]_{jc} is a function INTERVAL(1,n) -> CARR A (entry-in-carrier
   + matunit-type give both factors in CARR A; MUL closes on CARR A).")

;; PSS for the collapse: the matrix unit's entries off row k, and on row k.  Both
;; are entry-of-matunit with the (i=k) side of the AND resolved, so the summand
;; proof avoids AND/IF propositional reduction.
(support 'matunit-entry-off-row
  '(FORALL A (FORALL n (FORALL k (FORALL l (FORALL j (FORALL c
     (IMPLIES (IN j (INTERVAL 1 n))
     (IMPLIES (IN c (INTERVAL 1 n))
     (IMPLIES (NOT (= j k))
       (= (ENTRY (MATUNIT A n k l) j c) (ZERO A))))))))))))
(warrant! 'matunit-entry-off-row 'reference
  "E[k,l]_{jc} = 0 when j /= k (entry-of-matunit: the (j=k) conjunct is false).")
(support 'matunit-entry-k-row
  '(FORALL A (FORALL n (FORALL k (FORALL l (FORALL c
     (IMPLIES (IN k (INTERVAL 1 n))
     (IMPLIES (IN c (INTERVAL 1 n))
       (= (ENTRY (MATUNIT A n k l) k c) (IF (= c l) (ONE A) (ZERO A)))))))))))
(warrant! 'matunit-entry-k-row 'reference
  "E[k,l]_{kc} = 1 if c=l else 0 (entry-of-matunit with the (k=k) conjunct true).")

;;; =====================================================================
;;; Brick 2 -- the elementary COLUMN matrices (algebraic-numbers.pdf Def 3.2,
;;; eqs 48-50).  The book writes them as sums of the identity and matrix units
;;;   F^col_n[k,l]   = E[k,l] + E[l,k] + SUM{ E[i,i] : i /= k, i /= l }   (k /= l)
;;;   G^col_n[r,k,l] = I_n + r . E[k,l]                                   (k /= l)
;;;   H^col_n[r,k]   = I_n + (r - 1) . E[k,k]        (r invertible in A)
;;; but we install each DIRECTLY as a MATOF over its collapsed (i,j) entry
;;; function (the diagonal/unit sums evaluated once, by hand), NOT as a MATADD
;;; of IDENTMAT and MATUNIT.  Reason: the Prop-3.5 action proofs then reduce to
;;; matmul-entry + entry-of-matof (the same finsum-collapse the MATUNIT brick
;;; uses) instead of first having to distribute MATMUL over a matrix sum.
;;;
;;; Naming: ELEM-F / ELEM-G / ELEM-H keep the book's F/G/H letters; arg order is
;;; (ring, size, book-bracket params), matching MATUNIT's (A n k l).

;;; ---------------------------------------------------------------------
;;; ELEM-F(A, n, k, l) = F^col_n[k,l] -- the column-swap (transposition (k l))
;;; matrix.  Entry (i,j) = 1 exactly on the graph of the swap: (k,l), (l,k), and
;;; the untouched diagonal (i,i) for i /= k, l; else 0.  For k /= l these three
;;; cases are disjoint, so the book's E[k,l]+E[l,k]+SUM E[i,i] is just their
;;; union of ONE-entries.
(def-functoid 'ELEM-F '(A n k l)
  '(MATOF n n (VNB-LAMBDA (LIST i j)
     (IF (OR (AND (= i k) (= j l))
             (OR (AND (= i l) (= j k))
                 (AND (= i j) (AND (NOT (= i k)) (NOT (= i l))))))
         (ONE A) (ZERO A)))))

(support 'entry-of-elem-f
  '(FORALL A (FORALL n (FORALL k (FORALL l (FORALL i (FORALL j
     (IMPLIES (IN i (INTERVAL 1 n))
     (IMPLIES (IN j (INTERVAL 1 n))
       (= (ENTRY (ELEM-F A n k l) i j)
          (IF (OR (AND (= i k) (= j l))
                  (OR (AND (= i l) (= j k))
                      (AND (= i j) (AND (NOT (= i k)) (NOT (= i l))))))
              (ONE A) (ZERO A))))))))))))
(warrant! 'entry-of-elem-f 'reference
  "(ELEM-F A n k l)_{ij} = 1 on the swap graph {(k,l),(l,k)} and on the diagonal
   off k,l; else 0 (entry-of-matof on the transposition-(k l) entry function).")

(support 'elem-f-type
  '(FORALL A (IMPLIES (IS-RING A) (FORALL n (FORALL k (FORALL l
     (IN (ELEM-F A n k l) (MAT n n (CARR A)))))))))
(warrant! 'elem-f-type 'reference
  "ELEM-F(A,n,k,l) is an n-by-n matrix over CARR A (its entries are ONE/ZERO of A;
   matof-in-mat on the swap entry function).")

;;; ---------------------------------------------------------------------
;;; ELEM-G(A, n, r, k, l) = G^col_n[r,k,l] = I_n + r.E[k,l], for k /= l -- the
;;; transvection that adds r times column l to column k.  Entry (i,j) = ONE on
;;; the diagonal (i=j), = r at the single off-diagonal slot (k,l), else ZERO.
;;; For k /= l the (k,l) slot is off the diagonal, so the two nonzero cases never
;;; collide and the identity's ONE is undisturbed there.
(def-functoid 'ELEM-G '(A n r k l)
  '(MATOF n n (VNB-LAMBDA (LIST i j)
     (IF (= i j) (ONE A)
         (IF (AND (= i k) (= j l)) r (ZERO A))))))

(support 'entry-of-elem-g
  '(FORALL A (FORALL n (FORALL r (FORALL k (FORALL l (FORALL i (FORALL j
     (IMPLIES (IN i (INTERVAL 1 n))
     (IMPLIES (IN j (INTERVAL 1 n))
       (= (ENTRY (ELEM-G A n r k l) i j)
          (IF (= i j) (ONE A)
              (IF (AND (= i k) (= j l)) r (ZERO A))))))))))))))
(warrant! 'entry-of-elem-g 'reference
  "(ELEM-G A n r k l)_{ij} = 1 if i=j, r if (i,j)=(k,l), else 0 (entry-of-matof on
   the I + r.E[k,l] entry function; disjoint since k /= l).")

(support 'elem-g-type
  '(FORALL A (IMPLIES (IS-RING A) (FORALL n (FORALL r (FORALL k (FORALL l
     (IMPLIES (IN r (CARR A))
       (IN (ELEM-G A n r k l) (MAT n n (CARR A)))))))))))
(warrant! 'elem-g-type 'reference
  "ELEM-G(A,n,r,k,l) is an n-by-n matrix over CARR A when r in CARR A (entries are
   ONE/ZERO/r, all in CARR A; matof-in-mat).")

;; entry read-offs for the elem-g-action collapse.  Off column l (c/=l) G is the
;; identity column (single support); at column l (c=l) it has TWO supports -- the
;; diagonal l (value 1) and the unit's k (value r) -- hence the split below.
(support 'elem-g-entry-off-l-off-diag
  '(FORALL A (FORALL n (FORALL r (FORALL k (FORALL l (FORALL j (FORALL c
     (IMPLIES (IN j (INTERVAL 1 n))
     (IMPLIES (IN c (INTERVAL 1 n))
     (IMPLIES (NOT (= c l))
     (IMPLIES (NOT (= j c))
       (= (ENTRY (ELEM-G A n r k l) j c) (ZERO A))))))))))))))
(warrant! 'elem-g-entry-off-l-off-diag 'reference
  "G[r,k,l]_{jc} = 0 when c/=l and j/=c (off the diagonal, off the r-slot).")
(support 'elem-g-entry-off-l-diag
  '(FORALL A (FORALL n (FORALL r (FORALL k (FORALL l (FORALL c
     (IMPLIES (IN c (INTERVAL 1 n))
     (IMPLIES (NOT (= c l))
       (= (ENTRY (ELEM-G A n r k l) c c) (ONE A)))))))))))
(warrant! 'elem-g-entry-off-l-diag 'reference
  "G[r,k,l]_{cc} = 1 when c/=l (the diagonal, r-slot inactive).")
(support 'elem-g-entry-l-vanish
  '(FORALL A (FORALL n (FORALL r (FORALL k (FORALL l (FORALL j (FORALL c
     (IMPLIES (IN j (INTERVAL 1 n))
     (IMPLIES (IN c (INTERVAL 1 n))
     (IMPLIES (= c l)
     (IMPLIES (NOT (= j l))
     (IMPLIES (NOT (= j k))
       (= (ENTRY (ELEM-G A n r k l) j c) (ZERO A)))))))))))))))
(warrant! 'elem-g-entry-l-vanish 'reference
  "G[r,k,l]_{jc} = 0 when c=l and j is neither l (diagonal) nor k (r-slot).")
(support 'elem-g-entry-l-at-l
  '(FORALL A (FORALL n (FORALL r (FORALL k (FORALL l (FORALL c
     (IMPLIES (IN c (INTERVAL 1 n))
     (IMPLIES (= c l)
       (= (ENTRY (ELEM-G A n r k l) l c) (ONE A)))))))))))
(warrant! 'elem-g-entry-l-at-l 'reference
  "G[r,k,l]_{lc} = 1 when c=l (the diagonal entry of column l).")
(support 'elem-g-entry-l-at-k
  '(FORALL A (FORALL n (FORALL r (FORALL k (FORALL l (FORALL c
     (IMPLIES (IN c (INTERVAL 1 n))
     (IMPLIES (= c l)
     (IMPLIES (NOT (= k l))
       (= (ENTRY (ELEM-G A n r k l) k c) r)))))))))))
(warrant! 'elem-g-entry-l-at-k 'reference
  "G[r,k,l]_{kc} = r when c=l and k/=l (the r-slot in column l).")

;; whole-column read-offs of ELEM-G (row i, fixed column), for the elem-g-inverse
;; entry proof: column k (/=l) is an identity column, column l carries the r-slot
;; at row k, any other column c (/=l) is an identity column.
(support 'elem-g-col-k
  '(FORALL A (FORALL n (FORALL r (FORALL k (FORALL l (FORALL i
     (IMPLIES (NOT (= k l))
       (= (ENTRY (ELEM-G A n r k l) i k) (IF (= i k) (ONE A) (ZERO A)))))))))))
(warrant! 'elem-g-col-k 'reference
  "G[r,k,l]_{ik} = 1 if i=k else 0, when k/=l (column k is an identity column).")
(support 'elem-g-col-l
  '(FORALL A (FORALL n (FORALL r (FORALL k (FORALL l (FORALL i
       (= (ENTRY (ELEM-G A n r k l) i l)
          (IF (= i l) (ONE A) (IF (= i k) r (ZERO A)))))))))))
(warrant! 'elem-g-col-l 'reference
  "G[r,k,l]_{il} = 1 if i=l, r if i=k, else 0 (column l: diagonal + the r-slot).")
(support 'elem-g-col-other
  '(FORALL A (FORALL n (FORALL r (FORALL k (FORALL l (FORALL i (FORALL c
     (IMPLIES (NOT (= c l))
       (= (ENTRY (ELEM-G A n r k l) i c) (IF (= i c) (ONE A) (ZERO A))))))))))))
(warrant! 'elem-g-col-other 'reference
  "G[r,k,l]_{ic} = 1 if i=c else 0, when c/=l (any non-l column is identity).")

;; entry read-offs for the elem-f-action collapse.  F[k,l] is the transposition
;; permutation matrix: column k is supported at row l, column l at row k, any
;; other column c at row c.  One off/at pair per column-case (k/=l throughout).
(support 'elem-f-ck-off
  '(FORALL A (FORALL n (FORALL k (FORALL l (FORALL j (FORALL c
     (IMPLIES (IN j (INTERVAL 1 n))
     (IMPLIES (IN c (INTERVAL 1 n))
     (IMPLIES (= c k)
     (IMPLIES (NOT (= k l))
     (IMPLIES (NOT (= j l))
       (= (ENTRY (ELEM-F A n k l) j c) (ZERO A))))))))))))))
(warrant! 'elem-f-ck-off 'reference "F[k,l]_{jc} = 0 for c=k, j/=l.")
(support 'elem-f-ck-at
  '(FORALL A (FORALL n (FORALL k (FORALL l (FORALL c
     (IMPLIES (IN c (INTERVAL 1 n))
     (IMPLIES (= c k)
       (= (ENTRY (ELEM-F A n k l) l c) (ONE A))))))))))
(warrant! 'elem-f-ck-at 'reference "F[k,l]_{lc} = 1 for c=k.")
(support 'elem-f-cl-off
  '(FORALL A (FORALL n (FORALL k (FORALL l (FORALL j (FORALL c
     (IMPLIES (IN j (INTERVAL 1 n))
     (IMPLIES (IN c (INTERVAL 1 n))
     (IMPLIES (= c l)
     (IMPLIES (NOT (= k l))
     (IMPLIES (NOT (= j k))
       (= (ENTRY (ELEM-F A n k l) j c) (ZERO A))))))))))))))
(warrant! 'elem-f-cl-off 'reference "F[k,l]_{jc} = 0 for c=l, j/=k.")
(support 'elem-f-cl-at
  '(FORALL A (FORALL n (FORALL k (FORALL l (FORALL c
     (IMPLIES (IN c (INTERVAL 1 n))
     (IMPLIES (= c l)
       (= (ENTRY (ELEM-F A n k l) k c) (ONE A))))))))))
(warrant! 'elem-f-cl-at 'reference "F[k,l]_{kc} = 1 for c=l.")
(support 'elem-f-co-off
  '(FORALL A (FORALL n (FORALL k (FORALL l (FORALL j (FORALL c
     (IMPLIES (IN j (INTERVAL 1 n))
     (IMPLIES (IN c (INTERVAL 1 n))
     (IMPLIES (NOT (= c k))
     (IMPLIES (NOT (= c l))
     (IMPLIES (NOT (= j c))
       (= (ENTRY (ELEM-F A n k l) j c) (ZERO A))))))))))))))
(warrant! 'elem-f-co-off 'reference "F[k,l]_{jc} = 0 for c/=k, c/=l, j/=c.")
(support 'elem-f-co-at
  '(FORALL A (FORALL n (FORALL k (FORALL l (FORALL c
     (IMPLIES (IN c (INTERVAL 1 n))
     (IMPLIES (NOT (= c k))
     (IMPLIES (NOT (= c l))
       (= (ENTRY (ELEM-F A n k l) c c) (ONE A)))))))))))
(warrant! 'elem-f-co-at 'reference "F[k,l]_{cc} = 1 for c/=k, c/=l.")

;; whole-column read-offs of ELEM-F for the elem-f-inverse entry proof: column k
;; is supported at row l, column l at row k, any other column c at row c.
(support 'elem-f-col-k
  '(FORALL A (FORALL n (FORALL k (FORALL l (FORALL i
     (IMPLIES (NOT (= k l))
       (= (ENTRY (ELEM-F A n k l) i k) (IF (= i l) (ONE A) (ZERO A))))))))))
(warrant! 'elem-f-col-k 'reference "F[k,l]_{ik} = 1 if i=l else 0 (k/=l).")
(support 'elem-f-col-l
  '(FORALL A (FORALL n (FORALL k (FORALL l (FORALL i
     (IMPLIES (NOT (= k l))
       (= (ENTRY (ELEM-F A n k l) i l) (IF (= i k) (ONE A) (ZERO A))))))))))
(warrant! 'elem-f-col-l 'reference "F[k,l]_{il} = 1 if i=k else 0 (k/=l).")
(support 'elem-f-col-other
  '(FORALL A (FORALL n (FORALL k (FORALL l (FORALL i (FORALL c
     (IMPLIES (NOT (= c k))
     (IMPLIES (NOT (= c l))
       (= (ENTRY (ELEM-F A n k l) i c) (IF (= i c) (ONE A) (ZERO A))))))))))))
(warrant! 'elem-f-col-other 'reference "F[k,l]_{ic} = 1 if i=c else 0 (c/=k, c/=l).")

;;; ---------------------------------------------------------------------
;;; ELEM-H(A, n, r, k) = H^col_n[r,k] = I_n + (r-1).E[k,k] -- the scaling matrix
;;; that multiplies column k by r (r invertible in A for Cor 3.6, but the matrix
;;; and its action need only r in CARR A).  Entry (i,j) = ZERO off the diagonal;
;;; on the diagonal it is r at (k,k) and ONE elsewhere -- the book's 1+(r-1) = r
;;; at (k,k) collapsed by hand.
(def-functoid 'ELEM-H '(A n r k)
  '(MATOF n n (VNB-LAMBDA (LIST i j)
     (IF (= i j) (IF (= i k) r (ONE A)) (ZERO A)))))

(support 'entry-of-elem-h
  '(FORALL A (FORALL n (FORALL r (FORALL k (FORALL i (FORALL j
     (IMPLIES (IN i (INTERVAL 1 n))
     (IMPLIES (IN j (INTERVAL 1 n))
       (= (ENTRY (ELEM-H A n r k) i j)
          (IF (= i j) (IF (= i k) r (ONE A)) (ZERO A))))))))))))
(warrant! 'entry-of-elem-h 'reference
  "(ELEM-H A n r k)_{ij} = 0 off the diagonal, r at (k,k), 1 on the rest of the
   diagonal (entry-of-matof on the I + (r-1).E[k,k] entry function).")

(support 'elem-h-type
  '(FORALL A (IMPLIES (IS-RING A) (FORALL n (FORALL r (FORALL k
     (IMPLIES (IN r (CARR A))
       (IN (ELEM-H A n r k) (MAT n n (CARR A))))))))))
(warrant! 'elem-h-type 'reference
  "ELEM-H(A,n,r,k) is an n-by-n matrix over CARR A when r in CARR A (entries are
   ONE/ZERO/r, all in CARR A; matof-in-mat).")

;; entry read-offs for the elem-h-action collapse (the (i=j) conjunct resolved),
;; mirroring matunit-entry-off-row / -k-row.
(support 'elem-h-entry-off-diag
  '(FORALL A (FORALL n (FORALL r (FORALL k (FORALL j (FORALL c
     (IMPLIES (IN j (INTERVAL 1 n))
     (IMPLIES (IN c (INTERVAL 1 n))
     (IMPLIES (NOT (= j c))
       (= (ENTRY (ELEM-H A n r k) j c) (ZERO A))))))))))))
(warrant! 'elem-h-entry-off-diag 'reference
  "H[r,k]_{jc} = 0 when j /= c (entry-of-elem-h: the (j=c) conjunct is false).")
(support 'elem-h-entry-diag
  '(FORALL A (FORALL n (FORALL r (FORALL k (FORALL c
     (IMPLIES (IN c (INTERVAL 1 n))
       (= (ENTRY (ELEM-H A n r k) c c) (IF (= c k) r (ONE A))))))))))
(warrant! 'elem-h-entry-diag 'reference
  "H[r,k]_{cc} = r if c=k else 1 (entry-of-elem-h with the (c=c) conjunct true).")

;;; =====================================================================
;;; Brick 3 -- Prop 3.5: the ACTION of the elementary column matrices.  For an
;;; m-by-n matrix P over a ring A, right-multiplication P.(ELEM-x) is the
;;; corresponding elementary COLUMN operation on P (Def 3.4).  Each is stated as
;;; the (i,c)-entry of the product, in the exact shape of matunit-col-shift
;;; (Lemma 3.3), which is the engine: the book proves Prop 3.5 "immediately from
;;; Lemma 3.3".  Asserted (warrant 'proof) with the finsum-collapse route, same
;;; status as matunit-col-shift; to be driven to (qed) alongside it.

;;; ELEM-F: interchange of columns k and l.  (P.F[k,l])_{ic} = P_{il} at c=k,
;;; P_{ik} at c=l, P_{ic} elsewhere.  PROVEN to qed in
;;; theorem-library/elem-actions-proof.scm (trust: none), three single-support
;;; collapses under a 3-way case split on the column.

;;; ELEM-G: add r times column k to column l.  (P.G[r,k,l])_{ic} = P_{il}+P_{ik}.r
;;; at c=l, P_{ic} elsewhere.  PROVEN to qed in theorem-library/elem-actions-proof.scm
;;; (trust: none), via finsum-two-support on the l-column.

;;; ELEM-H: scale column k by r.  (P.H[r,k])_{ic} = P_{ik}.r at c=k, P_{ic}
;;; elsewhere.  PROVEN to qed in theorem-library/elem-actions-proof.scm (trust: none).

;;; =====================================================================
;;; Brick 4 -- Cor 3.6: the elementary column matrices are INVERTIBLE, with
;;; elementary inverses.  The book's proof is "apply Prop 3.5 by instantiating A
;;; with the identity matrix": each inverse product ELEM-x . ELEM-y is computed by
;;; the Prop 3.5 action (Brick 3) with P = the would-be inverse, then closed by
;;; matrix-entry-extensionality against IDENTMAT.  Over a COMMUTATIVE ring (Cor 3.6
;;; hypothesis).  Asserted (warrant 'proof), same status as the actions.

;;; F[k,l] is symmetric in k,l -- the swap graph {(k,l),(l,k)} + off-diagonal is
;;; symmetric under k<->l -- so the book's inverse F[l,k] is F[k,l] itself.
(support 'elem-f-symmetric
  '(FORALL A (IMPLIES (IS-RING A)
     (FORALL n (FORALL k (FORALL l
       (= (ELEM-F A n k l) (ELEM-F A n l k))))))))
(warrant! 'elem-f-symmetric 'reference
  "ELEM-F(A,n,k,l) = ELEM-F(A,n,l,k): the transposition-(k l) entry function is
   symmetric under k<->l (matrix-entry-extensionality on entry-of-elem-f).")

;;; Cor 3.6 -- the elementary matrices are invertible with elementary inverses:
;;;   F[k,l]^-1 = F[l,k],  G[r,k,l]^-1 = G[-r,k,l] (k/=l),  H[r,k]^-1 = H[r^-1,k]
;;; (r.s=1).  ALL PROVEN to qed in theorem-library/elem-inverses-proof.scm
;;; (trust: none), via matrix-entry-extensionality + the Prop 3.5 actions.
