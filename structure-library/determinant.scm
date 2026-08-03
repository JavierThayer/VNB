;;; determinant.scm -- the determinant of a square matrix over a ring, by
;;; RECURSIVE COFACTOR (Laplace) EXPANSION along the first row.  The pedestrian
;;; definition (user, 2026-07-23): no exterior algebra, no symmetric group, no
;;; sign-of-permutation -- just the recursion on size, minors, and FINSUM.
;;;
;;; DEFINITION (two definitional recursion axioms, no proof debt):
;;;   DET(R, 0,      A) == ONE(R)                       -- 0x0 = empty product
;;;   DET(R, succ n, A) == sum_{j=1..succ n}
;;;                          (-1)^(1+j)_R * A(1,j) * DET(R, n, MINOR(A,1,j,n))
;;; where the sign (-1)^(1+j) is taken IN THE RING via MPOW of R's multiplicative
;;; monoid, the sum is FINSUM over R's additive group, and MINOR(A,1,j,n) deletes
;;; row 1 and column j.  1x1 falls out: DET(R,1,A) = (+1)A(1,1)DET(R,0,-) = A(1,1).
;;;
;;; These are installed DEFINITIONAL (theory-add-definition!, like def-by-nn-
;;; recursion), so they owe no warrant.  They are hand-stated rather than machine-
;;; generated because the matrix SHRINKS in the recursive call (to its minor), so
;;; the size is not a fixed def-by-nn-recursion parameter; their consistency rests
;;; on DET being well-defined by this recursion (the projection of the legitimate
;;; size-indexed recursion MAT(n,n) -> CARR).
;;;
;;; COMPUTE-PHASE OBSTACLE (found 2026-07-23): `mac det-cofactor' does not fire on
;;; a goal with a LITERAL size like DET(R,1,A) -- the axiom is keyed on
;;; DET(R,succ n,A) and the numeral `1' is not seen as `succ 0'.  The numeral<->
;;; succ bridge ([[numeral_succ_match]]) is the first thing the property proofs
;;; below need; the two computational seeds det-1x1 / det-2x2 exist to force it.
;;;
;;; Needs: matrix (MAT/MATOF/ENTRY), monoid-power (MPOW), views (RING-ADDITIVE-AG,
;;; RING-MULTIPLICATIVE-MONOID), finsum (FINSUM), ring (IS-RING).  Sources:
;;; Hoffman & Kunze Ch. 5; Lima, Algebra Linear.
;;; ====================================================================

;;; ---- MINOR: delete row r and column c ---------------------------------
;;; MINOR(S,r,c,n): the n-by-n matrix from a (succ n)-by-(succ n) S with row r
;;; and column c removed.  skip(i,r) = i if i<r else succ i.
(def-functoid 'MINOR '(S r c n)
  '(MATOF n n (VNB-LAMBDA (LIST i j) (CARTESIAN (INTERVAL 1 n) (INTERVAL 1 n))
     (ENTRY S (IF (< i r) i (succ i)) (IF (< j c) j (succ j))))))

;; Row/col deleted are p, q (NOT r/c: `r' case-folds onto the ring R).
(support 'minor-type
  (forall-guarded '(R S p q n)
    (list '(IS-RING R) '(IN p NN) '(IN q NN) '(IN n NN)
          '(IN S (MAT (succ n) (succ n) (CARR R))))
    '(IN (MINOR S p q n) (MAT n n (CARR R)))))
(warrant! 'minor-type 'reference '(hoffman-kunze "Ch. 5"))
(gloss! 'minor-type
  "MINOR(S,r,c,n) -- S with row r, column c deleted -- is an n-by-n matrix over R
   when S is (succ n)-by-(succ n): each surviving entry is an entry of S.")
(category! 'minor-type 'algebra)

;;; ---- DET: the recursive definition ------------------------------------
;; english is a $N TEMPLATE STRING, not a lambda: operator-render-english calls
;; a procedure english as (proc arglist) -- the arg LIST as ONE argument
;; (operators.scm) -- so a multi-formal (lambda (r n a) ...) crashes if ever
;; reached.  DET's was latent (DET has no registered params, so the census
;; renders it argless and never invoked the lambda), but it is the same defect
;; my FINSUPP/MONALG lambdas hit; a string can never mis-arity.  "det($3)" reads
;; the matrix (3rd arg), hiding the ring and size, as the lambda intended.
(notation! 'DET 'arity 3 'english "det($3)")

(define det--cofactor-rhs
  '(FINSUM (RING-ADDITIVE-AG R)
     (VNB-LAMBDA j (INTERVAL 1 (succ n))
       ((MUL R)
         (MPOW (RING-MULTIPLICATIVE-MONOID R) ((NEG R) (ONE R)) (succ j))
         ((MUL R) (ENTRY A 1 j) (DET R n (MINOR A 1 j n)))))
     (INTERVAL 1 (succ n))))

(fluid-let ((*current-provenance* 'definitional))
  (theory-add-definition! *current-theory* 'DET
    (list (cons 'det-zero
                (forall-guarded '(R A) '() '(== (DET R 0 A) (ONE R))))
          (cons 'det-cofactor
                (forall-guarded '(R n A)
                  (list '(IS-RING R) '(IN n NN)
                        '(IN A (MAT (succ n) (succ n) (CARR R))))
                  (list '== '(DET R (succ n) A) det--cofactor-rhs))))))
(gloss! 'det-cofactor
  "Cofactor (Laplace) expansion along row 1: det(A) = sum_j (-1)^(1+j) A(1,j)
   det(minor_{1,j}).  The definition of DET over a ring, recursive on the size.")

;;; ---- theorem seeds (stated, not proved) -------------------------------
;;; The first menu of determinant facts.  Computational sanity checks first
;;; (det-1x1, det-2x2 -- these also force the numeral<->succ bridge), then the
;;; headline properties.  All asserted with a textbook citation; PROOFS DEFERRED.

;;; det(A) lands in R's carrier.
(support 'det-in-carrier
  (forall-guarded '(R n A)
    (list '(IS-RING R) '(IN n NN) '(IN A (MAT n n (CARR R))))
    '(IN (DET R n A) (CARR R))))
(warrant! 'det-in-carrier 'reference '(hoffman-kunze "Ch. 5"))
(gloss! 'det-in-carrier "The determinant of an n-by-n matrix over R is an element of R.")
(category! 'det-in-carrier 'algebra)

;;; 1x1: det = the sole entry.
(support 'det-1x1
  (forall-guarded '(R A)
    (list '(IS-RING R) '(IN A (MAT 1 1 (CARR R))))
    '(= (DET R 1 A) (ENTRY A 1 1))))
(warrant! 'det-1x1 'reference '(hoffman-kunze "Ch. 5"))
(gloss! 'det-1x1 "det of a 1-by-1 matrix is its single entry (the base of the recursion).")
(category! 'det-1x1 'algebra)

;;; 2x2: det = A11 A22 - A12 A21.
(support 'det-2x2
  (forall-guarded '(R A)
    (list '(IS-RING R) '(IN A (MAT 2 2 (CARR R))))
    '(= (DET R 2 A)
        ((ADD R) ((MUL R) (ENTRY A 1 1) (ENTRY A 2 2))
                 ((NEG R) ((MUL R) (ENTRY A 1 2) (ENTRY A 2 1)))))))
(warrant! 'det-2x2 'reference '(hoffman-kunze "Ch. 5"))
(gloss! 'det-2x2 "det[[a,b],[c,d]] = ad - bc, over any ring.")
(category! 'det-2x2 'algebra)

;;; det of the identity matrix is 1.
(support 'det-identity
  (forall-guarded '(R n)
    (list '(IS-RING R) '(IN n NN))
    '(= (DET R n (ONE (MAT-RING R n))) (ONE R))))
(warrant! 'det-identity 'reference '(hoffman-kunze "Ch. 5"))
(gloss! 'det-identity "det(I_n) = 1_R: the determinant of the identity matrix is the ring unit.")
(category! 'det-identity 'algebra)

;;; a matrix with two equal rows has determinant 0 (alternating in the rows).
(support 'det-alternating-rows
  (forall-guarded '(R n A p q)
    (list '(IS-RING R) '(IN n NN) '(IN A (MAT n n (CARR R)))
          '(IN p (INTERVAL 1 n)) '(IN q (INTERVAL 1 n)) '(NOT (= p q))
          '(FORALL k (IMPLIES (IN k (INTERVAL 1 n))
              (= (ENTRY A p k) (ENTRY A q k)))))
    '(= (DET R n A) (ZERO R))))
(warrant! 'det-alternating-rows 'reference '(hoffman-kunze "Ch. 5"))
(gloss! 'det-alternating-rows
  "Two equal rows force det = 0 (the alternating property).")
(category! 'det-alternating-rows 'algebra)

;;; multiplicativity: det(PQ) = det(P) det(Q), over a COMMUTATIVE ring.
(support 'det-multiplicative
  (forall-guarded '(R n P Q)
    (list '(IS-COMMUTATIVE-RING R) '(IN n NN)
          '(IN P (MAT n n (CARR R))) '(IN Q (MAT n n (CARR R))))
    '(= (DET R n (MATMUL R P Q)) ((MUL R) (DET R n P) (DET R n Q)))))
(warrant! 'det-multiplicative 'reference '(hoffman-kunze "Ch. 5"))
(gloss! 'det-multiplicative
  "det(PQ) = det(P) det(Q) over a commutative ring -- the product theorem.")
(category! 'det-multiplicative 'algebra)

;;; DEFERRED seeds (need machinery not yet in the tree):
;;;   det-transpose  det(A^T) = det(A)         -- needs a TRANSPOSE functoid.
;;;   det-cofactor-any-row / -any-column       -- expansion along any i/j equals
;;;                                               the row-1 value (justifies the
;;;                                               asymmetric definition).
;;;   det-cramer / adjugate, det-nonzero-iff-invertible.
