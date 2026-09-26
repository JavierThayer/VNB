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
;;; RETIRED 2026-09-14 (proven): elem-g-type -- theorem-library/mat-typing-bundle.scm
;;; RETIRED 2026-09-14 (proven): matunit-summand-type -- theorem-library/lam-fun-bricks.scm (dk-lam-fun!)

;;; ---------------------------------------------------------------------
;;; MATUNIT(A, n, k, l) -- the n-by-n matrix unit E_n[k,l]: ONE at position
;;; (k,l), ZERO everywhere else (the book's E_n[k,l]).  A MATOF over the
;;; ring's ONE/ZERO, in the same style as IDENTMAT.
(def-functoid 'MATUNIT '(A n k l)
  '(MATOF n n (VNB-LAMBDA (LIST i j) (CARTESIAN (INTERVAL 1 n) (INTERVAL 1 n))
     (IF (AND (= i k) (= j l)) (ONE A) (ZERO A)))))

;;; entries of a matrix unit: ONE iff (i,j) = (k,l), else ZERO.
;;; entry-of-matunit MOVED 2026-09-15 (wave 8) to theorem-library/elem-entry-readoffs.scm, where it is PROVEN modulo {entry-of-matof} -- one eer-run! call, no per-theorem driver.

;;; typing: the matrix unit is an n-by-n matrix over the ring's carrier.
;;; matunit-type MOVED 2026-09-15 (wave 6) to theorem-library/matunit-matact-type.scm, where it is PROVEN.

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

;; PSS for the collapse: the matrix unit's entries off row k, and on row k.  Both
;; are entry-of-matunit with the (i=k) side of the AND resolved, so the summand
;; proof avoids AND/IF propositional reduction.
;;; matunit-entry-off-row MOVED 2026-09-15 (wave 8) to theorem-library/elem-entry-readoffs.scm, where it is PROVEN modulo {entry-of-matof} -- one eer-run! call, no per-theorem driver.
;;; matunit-entry-k-row MOVED 2026-09-15 (wave 8) to theorem-library/elem-entry-readoffs.scm, where it is PROVEN modulo {entry-of-matof} -- one eer-run! call, no per-theorem driver.

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
  '(MATOF n n (VNB-LAMBDA (LIST i j) (CARTESIAN (INTERVAL 1 n) (INTERVAL 1 n))
     (IF (OR (AND (= i k) (= j l))
             (OR (AND (= i l) (= j k))
                 (AND (= i j) (AND (NOT (= i k)) (NOT (= i l))))))
         (ONE A) (ZERO A)))))

;;; entry-of-elem-f MOVED 2026-09-15 (wave 8) to theorem-library/elem-entry-readoffs.scm, where it is PROVEN modulo {entry-of-matof} -- one eer-run! call, no per-theorem driver.

;;; elem-f-type / elem-h-type (the swap and scaling matrices are n-by-n over
;;; CARR A) were supports here until 2026-09-16; they are now THEOREMS, GUARDED
;;; on (IN n NN) as elem-g-type is: for n := 3/2 membership in
;;; MAT(3/2, 3/2, X) is false for every term (mat-rows-in-nn).
;;; RETIRED 2026-09-16 (proven): elem-f-type -- theorem-library/elem-entry-readoffs.scm

;;; ---------------------------------------------------------------------
;;; ELEM-G(A, n, r, k, l) = G^col_n[r,k,l] = I_n + r.E[k,l], for k /= l -- the
;;; transvection that adds r times column l to column k.  Entry (i,j) = ONE on
;;; the diagonal (i=j), = r at the single off-diagonal slot (k,l), else ZERO.
;;; For k /= l the (k,l) slot is off the diagonal, so the two nonzero cases never
;;; collide and the identity's ONE is undisturbed there.
(def-functoid 'ELEM-G '(A n r k l)
  '(MATOF n n (VNB-LAMBDA (LIST i j) (CARTESIAN (INTERVAL 1 n) (INTERVAL 1 n))
     (IF (= i j) (ONE A)
         (IF (AND (= i k) (= j l)) r (ZERO A))))))

;;; entry-of-elem-g MOVED 2026-09-15 (wave 8) to theorem-library/elem-entry-readoffs.scm, where it is PROVEN modulo {entry-of-matof} -- one eer-run! call, no per-theorem driver.


;; entry read-offs for the elem-g-action collapse.  Off column l (c/=l) G is the
;; identity column (single support); at column l (c=l) it has TWO supports -- the
;; diagonal l (value 1) and the unit's k (value r) -- hence the split below.
;;; elem-g-entry-off-l-off-diag MOVED 2026-09-15 (wave 8) to theorem-library/elem-entry-readoffs.scm, where it is PROVEN modulo {entry-of-matof} -- one eer-run! call, no per-theorem driver.
;;; elem-g-entry-off-l-diag MOVED 2026-09-15 (wave 8) to theorem-library/elem-entry-readoffs.scm, where it is PROVEN modulo {entry-of-matof} -- one eer-run! call, no per-theorem driver.
;;; elem-g-entry-l-vanish MOVED 2026-09-15 (wave 8) to theorem-library/elem-entry-readoffs.scm, where it is PROVEN modulo {entry-of-matof} -- one eer-run! call, no per-theorem driver.
;;; elem-g-entry-l-at-l MOVED 2026-09-15 (wave 8) to theorem-library/elem-entry-readoffs.scm, where it is PROVEN modulo {entry-of-matof} -- one eer-run! call, no per-theorem driver.
;;; elem-g-entry-l-at-k MOVED 2026-09-15 (wave 8) to theorem-library/elem-entry-readoffs.scm, PROVEN via the same eer-run! lane -- RESTATED with the ENTRY index typed (IN i (INTERVAL 1 n)).  Unguarded it claimed that ENTRY = NTH of NTH DENOTES past the end of a row, which nth-in-range does not grant.  User decision.  Citers needed no edit: all twelve sites already had the typing.

;; whole-column read-offs of ELEM-G (row i, fixed column), for the elem-g-inverse
;; entry proof: column k (/=l) is an identity column, column l carries the r-slot
;; at row k, any other column c (/=l) is an identity column.
;;; elem-g-col-k MOVED 2026-09-15 (wave 8) to theorem-library/elem-entry-readoffs.scm, PROVEN via the same eer-run! lane -- RESTATED with the ENTRY index typed (IN i (INTERVAL 1 n)).  Unguarded it claimed that ENTRY = NTH of NTH DENOTES past the end of a row, which nth-in-range does not grant.  User decision.  Citers needed no edit: all twelve sites already had the typing.
;;; elem-g-col-l MOVED 2026-09-15 (wave 8) to theorem-library/elem-entry-readoffs.scm, PROVEN via the same eer-run! lane -- RESTATED with the ENTRY index typed (IN i (INTERVAL 1 n)).  Unguarded it claimed that ENTRY = NTH of NTH DENOTES past the end of a row, which nth-in-range does not grant.  User decision.  Citers needed no edit: all twelve sites already had the typing.
;;; elem-g-col-other MOVED 2026-09-15 (wave 8) to theorem-library/elem-entry-readoffs.scm, PROVEN via the same eer-run! lane -- RESTATED with the ENTRY index typed (IN i (INTERVAL 1 n)).  Unguarded it claimed that ENTRY = NTH of NTH DENOTES past the end of a row, which nth-in-range does not grant.  User decision.  Citers needed no edit: all twelve sites already had the typing.

;; entry read-offs for the elem-f-action collapse.  F[k,l] is the transposition
;; permutation matrix: column k is supported at row l, column l at row k, any
;; other column c at row c.  One off/at pair per column-case (k/=l throughout).
;;; elem-f-ck-off MOVED 2026-09-15 (wave 8) to theorem-library/elem-entry-readoffs.scm, where it is PROVEN modulo {entry-of-matof} -- one eer-run! call, no per-theorem driver.
;;; elem-f-ck-at MOVED 2026-09-15 (wave 8) to theorem-library/elem-entry-readoffs.scm, PROVEN via the same eer-run! lane -- RESTATED with the ENTRY index typed (IN i (INTERVAL 1 n)).  Unguarded it claimed that ENTRY = NTH of NTH DENOTES past the end of a row, which nth-in-range does not grant.  User decision.  Citers needed no edit: all twelve sites already had the typing.
;;; elem-f-cl-off MOVED 2026-09-15 (wave 8) to theorem-library/elem-entry-readoffs.scm, where it is PROVEN modulo {entry-of-matof} -- one eer-run! call, no per-theorem driver.
;;; elem-f-cl-at MOVED 2026-09-15 (wave 8) to theorem-library/elem-entry-readoffs.scm, PROVEN via the same eer-run! lane -- RESTATED with the ENTRY index typed (IN i (INTERVAL 1 n)).  Unguarded it claimed that ENTRY = NTH of NTH DENOTES past the end of a row, which nth-in-range does not grant.  User decision.  Citers needed no edit: all twelve sites already had the typing.
;;; elem-f-co-off MOVED 2026-09-15 (wave 8) to theorem-library/elem-entry-readoffs.scm, where it is PROVEN modulo {entry-of-matof} -- one eer-run! call, no per-theorem driver.
;;; elem-f-co-at MOVED 2026-09-15 (wave 8) to theorem-library/elem-entry-readoffs.scm, where it is PROVEN modulo {entry-of-matof} -- one eer-run! call, no per-theorem driver.

;; whole-column read-offs of ELEM-F for the elem-f-inverse entry proof: column k
;; is supported at row l, column l at row k, any other column c at row c.
;;; elem-f-col-k MOVED 2026-09-15 (wave 8) to theorem-library/elem-entry-readoffs.scm, PROVEN via the same eer-run! lane -- RESTATED with the ENTRY index typed (IN i (INTERVAL 1 n)).  Unguarded it claimed that ENTRY = NTH of NTH DENOTES past the end of a row, which nth-in-range does not grant.  User decision.  Citers needed no edit: all twelve sites already had the typing.
;;; elem-f-col-l MOVED 2026-09-15 (wave 8) to theorem-library/elem-entry-readoffs.scm, PROVEN via the same eer-run! lane -- RESTATED with the ENTRY index typed (IN i (INTERVAL 1 n)).  Unguarded it claimed that ENTRY = NTH of NTH DENOTES past the end of a row, which nth-in-range does not grant.  User decision.  Citers needed no edit: all twelve sites already had the typing.
;;; elem-f-col-other MOVED 2026-09-15 (wave 8) to theorem-library/elem-entry-readoffs.scm, PROVEN via the same eer-run! lane -- RESTATED with the ENTRY index typed (IN i (INTERVAL 1 n)).  Unguarded it claimed that ENTRY = NTH of NTH DENOTES past the end of a row, which nth-in-range does not grant.  User decision.  Citers needed no edit: all twelve sites already had the typing.

;;; ---------------------------------------------------------------------
;;; ELEM-H(A, n, r, k) = H^col_n[r,k] = I_n + (r-1).E[k,k] -- the scaling matrix
;;; that multiplies column k by r (r invertible in A for Cor 3.6, but the matrix
;;; and its action need only r in CARR A).  Entry (i,j) = ZERO off the diagonal;
;;; on the diagonal it is r at (k,k) and ONE elsewhere -- the book's 1+(r-1) = r
;;; at (k,k) collapsed by hand.
(def-functoid 'ELEM-H '(A n r k)
  '(MATOF n n (VNB-LAMBDA (LIST i j) (CARTESIAN (INTERVAL 1 n) (INTERVAL 1 n))
     (IF (= i j) (IF (= i k) r (ONE A)) (ZERO A)))))

;;; entry-of-elem-h MOVED 2026-09-15 (wave 8) to theorem-library/elem-entry-readoffs.scm, where it is PROVEN modulo {entry-of-matof} -- one eer-run! call, no per-theorem driver.

;;; RETIRED 2026-09-16 (proven): elem-h-type -- theorem-library/mat-typing-bundle.scm

;; entry read-offs for the elem-h-action collapse (the (i=j) conjunct resolved),
;; mirroring matunit-entry-off-row / -k-row.
;;; elem-h-entry-off-diag MOVED 2026-09-15 (wave 8) to theorem-library/elem-entry-readoffs.scm, where it is PROVEN modulo {entry-of-matof} -- one eer-run! call, no per-theorem driver.
;;; elem-h-entry-diag MOVED 2026-09-15 (wave 8) to theorem-library/elem-entry-readoffs.scm, where it is PROVEN modulo {entry-of-matof} -- one eer-run! call, no per-theorem driver.

;;; ---------------------------------------------------------------------
;;; ROW entry read-offs (Brick 5 support): (ENTRY (ELEM-x A n ...) i j), row i
;;; fixed by a case hypothesis, j the sum var -- the left-mult analogues of the
;;; column read-offs above.  entry-of-elem-x + IF/AND/OR reduction; warrant 'reference.
;; ELEM-F rows (symmetric transposition): row k supported at col l, row l at col k, row i at col i.
;;; elem-f-rk-off MOVED 2026-09-15 (wave 8) to theorem-library/elem-entry-readoffs.scm, where it is PROVEN modulo {entry-of-matof} -- one eer-run! call, no per-theorem driver.

;;; elem-f-rk-at MOVED 2026-09-15 (wave 8) to theorem-library/elem-entry-readoffs.scm, PROVEN via the same eer-run! lane -- RESTATED with the ENTRY index typed (IN i (INTERVAL 1 n)).  Unguarded it claimed that ENTRY = NTH of NTH DENOTES past the end of a row, which nth-in-range does not grant.  User decision.  Citers needed no edit: all twelve sites already had the typing.

;;; elem-f-rl-off MOVED 2026-09-15 (wave 8) to theorem-library/elem-entry-readoffs.scm, where it is PROVEN modulo {entry-of-matof} -- one eer-run! call, no per-theorem driver.

;;; elem-f-rl-at MOVED 2026-09-15 (wave 8) to theorem-library/elem-entry-readoffs.scm, PROVEN via the same eer-run! lane -- RESTATED with the ENTRY index typed (IN i (INTERVAL 1 n)).  Unguarded it claimed that ENTRY = NTH of NTH DENOTES past the end of a row, which nth-in-range does not grant.  User decision.  Citers needed no edit: all twelve sites already had the typing.

;;; elem-f-ro-off MOVED 2026-09-15 (wave 8) to theorem-library/elem-entry-readoffs.scm, where it is PROVEN modulo {entry-of-matof} -- one eer-run! call, no per-theorem driver.

;;; elem-f-ro-at MOVED 2026-09-15 (wave 8) to theorem-library/elem-entry-readoffs.scm, PROVEN via the same eer-run! lane -- RESTATED with the ENTRY index typed (IN i (INTERVAL 1 n)).  Unguarded it claimed that ENTRY = NTH of NTH DENOTES past the end of a row, which nth-in-range does not grant.  User decision.  Citers needed no edit: all twelve sites already had the typing.

;; ELEM-G rows: row k has two supports (col k val 1, col l val r); other rows are identity.
;;; elem-g-rk-vanish MOVED 2026-09-15 (wave 8) to theorem-library/elem-entry-readoffs.scm, where it is PROVEN modulo {entry-of-matof} -- one eer-run! call, no per-theorem driver.

;;; elem-g-rk-at-k MOVED 2026-09-15 (wave 8) to theorem-library/elem-entry-readoffs.scm, PROVEN via the same eer-run! lane -- RESTATED with the ENTRY index typed (IN i (INTERVAL 1 n)).  Unguarded it claimed that ENTRY = NTH of NTH DENOTES past the end of a row, which nth-in-range does not grant.  User decision.  Citers needed no edit: all twelve sites already had the typing.

;;; elem-g-rk-at-l MOVED 2026-09-15 (wave 8) to theorem-library/elem-entry-readoffs.scm, PROVEN via the same eer-run! lane -- RESTATED with the ENTRY index typed (IN i (INTERVAL 1 n)).  Unguarded it claimed that ENTRY = NTH of NTH DENOTES past the end of a row, which nth-in-range does not grant.  User decision.  Citers needed no edit: all twelve sites already had the typing.

;;; elem-g-ro-off MOVED 2026-09-15 (wave 8) to theorem-library/elem-entry-readoffs.scm, where it is PROVEN modulo {entry-of-matof} -- one eer-run! call, no per-theorem driver.

;;; elem-g-ro-at MOVED 2026-09-15 (wave 8) to theorem-library/elem-entry-readoffs.scm, PROVEN via the same eer-run! lane -- RESTATED with the ENTRY index typed (IN i (INTERVAL 1 n)).  Unguarded it claimed that ENTRY = NTH of NTH DENOTES past the end of a row, which nth-in-range does not grant.  User decision.  Citers needed no edit: all twelve sites already had the typing.

;; ELEM-H rows (diagonal): off diagonal 0, on it r (at k) or 1.
;;; elem-h-ro-off MOVED 2026-09-15 (wave 8) to theorem-library/elem-entry-readoffs.scm, where it is PROVEN modulo {entry-of-matof} -- one eer-run! call, no per-theorem driver.

;;; elem-h-ro-at MOVED 2026-09-15 (wave 8) to theorem-library/elem-entry-readoffs.scm, where it is PROVEN modulo {entry-of-matof} -- one eer-run! call, no per-theorem driver.


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
;;; elem-f-symmetric was a support here until 2026-09-16; it is now a THEOREM
;;; (matrix-entry-extensionality on entry-of-elem-f), GUARDED on (IN n NN): for
;;; n := 3/2 neither side has a value (both are descriptions over the empty
;;; MAT(3/2, 3/2, ...)), so `=' fails.
;;; RETIRED 2026-09-16 (proven): elem-f-symmetric -- theorem-library/elem-entry-readoffs.scm

;;; Cor 3.6 -- the elementary matrices are invertible with elementary inverses:
;;;   F[k,l]^-1 = F[l,k],  G[r,k,l]^-1 = G[-r,k,l] (k/=l),  H[r,k]^-1 = H[r^-1,k]
;;; (r.s=1).  ALL PROVEN to qed in theorem-library/elem-inverses-proof.scm
;;; (trust: none), via matrix-entry-extensionality + the Prop 3.5 actions.

;;; =====================================================================
;;; Brick 5 (Phase B) -- ROW operations: the action of the elementary matrices
;;; by LEFT-multiplication (Prop 3.29's F^row/G^row/H^row, algebraic-numbers.pdf
;;; ch.3 p.43).  Smith/normal-form reduction (Prop 3.36) needs BOTH row and
;;; column operations; Bricks 3-4 gave the column ops (right-mult), these are the
;;; row ops.  The matrix is m-by-m and acts on the m rows of P in MAT(m,n).
;;;
;;; (E . P)_{ic} = FINSUM_j E_{ij} . P_{jc}  (matmul-entry), so a row of E picks
;;; out a row of P.  Same collapse shape as Bricks 3-4 (matmul-entry + finsum
;;; single/two-support + excluded-middle case split), but the surviving support
;;; is in E's ROW index i, not its column.  F and H are symmetric matrices so
;;; their row read-offs equal the proven column read-offs; G = I + r.E[k,l] is
;;; NOT symmetric, so its row (i=k) has supports at j=k (value 1) and j=l (value
;;; r) -- a finsum-two-support, mirroring the column proof's c=l case.
;;;
;;; The row-action THEOREMS themselves --
;;;   elem-f-row-action : F[k,l].P swaps rows k,l of P;
;;;   elem-g-row-action : G[r,k,l].P adds r.(row l) to row k (k/=l);
;;;   elem-h-row-action : H[r,k].P scales row k of P by r --
;;; are PROVEN to qed in theorem-library/elem-row-actions-proof.scm (trust: none),
;;; mirroring theorem-library/elem-actions-proof.scm with the elementary matrix as
;;; the LEFT factor.  The row read-offs above (elem-{f,g,h}-r*) are the support
;;; those proofs cite.
