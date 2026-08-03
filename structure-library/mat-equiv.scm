;;; mat-equiv.scm -- the matrix EQUIVALENCE relation ~ (algebraic-numbers.pdf
;;; ch.3, Def 3.33 / Remark 3.35): C ~ D iff C can be carried to D by a sequence
;;; of elementary row and column operations, equivalently iff there are INVERTIBLE
;;; U (m-by-m), V (n-by-n) with D = U.C.V.  We take the invertible-matrices form
;;; (Remark 3.35) as the definition -- it is the cleanest for the Smith existence
;;; proof (Prop 3.36): each reduction step multiplies by a proven-invertible
;;; elementary matrix (Cor 3.6), and ~ is reflexive/transitive so the steps chain.
;;;
;;; Dependencies: matrix.scm (MAT/MATMUL/IDENTMAT), elementary-matrix.scm.

;;; IS-INVERTIBLE-MAT(A, n, U): U is an n-by-n matrix over A with a two-sided
;;; matrix inverse (an element of the group M_n^x(A) of Remark 3.32).
(def-predicate 'IS-INVERTIBLE-MAT '(A n U)
  '(AND (IN U (MAT n n (CARR A)))
        (FORSOME V (AND (IN V (MAT n n (CARR A)))
                        (AND (= (MATMUL A U V) (IDENTMAT A n))
                             (= (MATMUL A V U) (IDENTMAT A n)))))))

;;; MAT-EQUIV(A, m, n, C, D): C ~ D -- there are invertible U (m-by-m), V (n-by-n)
;;; with D = U.C.V.  Reflexive (U=V=I), symmetric (invert U,V), transitive
;;; (compose), and every elementary row/column op yields an equivalent matrix.
(def-predicate 'MAT-EQUIV '(A m n C D)
  '(FORSOME U (AND (IS-INVERTIBLE-MAT A m U)
     (FORSOME V (AND (IS-INVERTIBLE-MAT A n V)
       (= D (MATMUL A (MATMUL A U C) V)))))))

;;; -(-r) = r in any ring (additive-group double inverse) -- needed to see that
;;; ELEM-G[-r]'s inverse ELEM-G[-(-r)] is ELEM-G[r].
(support 'ring-neg-neg
  '(FORALL s (IMPLIES (IS-RING s) (FORALL r (IMPLIES (IN r (CARR s))
     (= ((NEG s) ((NEG s) r)) r))))))
(warrant! 'ring-neg-neg 'well-known
  "-(-r) = r in any ring: r's additive inverse's inverse is r (group double-inverse).")

;;; -----------------------------------------------------------------------
;;; SUBMAT(P, p, q): the lower-right p-by-q block of a (succ p)-by-(succ q)
;;; matrix P -- P with its first row and first column deleted.  The Smith
;;; recursion (Prop 3.36) applies to this block after the pivot clears row 1
;;; and column 1.  Entry (i,j) = P_{i+1, j+1}.
(def-functoid 'SUBMAT '(S p q)
  '(MATOF p q (VNB-LAMBDA (LIST i j) (CARTESIAN (INTERVAL 1 p) (INTERVAL 1 q)) (ENTRY S (succ i) (succ j)))))

;;; submat-type: SUBMAT(P,p,q) is a p-by-q matrix over A when P is
;;; (succ p)-by-(succ q) (each block entry P_{i+1,j+1} lies in CARR A).
;;; Warranted 'reference like the other MAT read-offs (matof-in-mat + the shift
;;; succ i in [1, succ p] for i in [1,p]).
(support 'submat-type
  '(FORALL A (FORALL p (FORALL q (FORALL S
     (IMPLIES (IN p NN) (IMPLIES (IN q NN)
       (IMPLIES (IN S (MAT (succ p) (succ q) (CARR A)))
         (IN (SUBMAT S p q) (MAT p q (CARR A)))))))))))
(warrant! 'submat-type 'reference
  "SUBMAT(P,p,q) in MAT(p,q,CARR A) for P in MAT(succ p, succ q, CARR A): each
   block entry is P_{succ i, succ j} in CARR A (entry-in-carrier; succ i in
   [1,succ p] for i in [1,p]), so matof-in-mat applies.")

;;; entry-of-submat: the (i,j) block entry is P_{i+1, j+1}.  A pure read-off,
;;; warranted 'reference like entry-of-matof (mac SUBMAT + entry-of-matof + beta
;;; reduces the goal to a reflexive equation; verified in scratchpad/submat.scm).
(support 'entry-of-submat
  '(FORALL S (FORALL p (FORALL q (FORALL i (FORALL j
     (IMPLIES (IN i (INTERVAL 1 p)) (IMPLIES (IN j (INTERVAL 1 q))
       (= (ENTRY (SUBMAT S p q) i j) (ENTRY S (succ i) (succ j)))))))))))
(warrant! 'entry-of-submat 'reference
  "SUBMAT(P,p,q)_{ij} = P_{succ i, succ j} for i in [1,p], j in [1,q]
   (entry-of-matof on the block tabulator, beta-reduced).")

;;; -----------------------------------------------------------------------
;;; BORDER(A, b, M, p, q): the (succ p)-by-(succ q) matrix with b in the (1,1)
;;; corner, zeros in the rest of row 1 and column 1, and the p-by-q block M in
;;; the lower-right -- the "direct sum" [[b, 0], [0, M]].  The inverse of SUBMAT
;;; on bordered matrices (SUBMAT(BORDER(A,b,M,p,q)) = M), it lets the Smith
;;; recursion lift an equivalence on the lower-right block back to the full
;;; matrix (bordering).  Entry (i,j): b if i=j=1, 0 if exactly one of i,j is 1,
;;; else M_{i-1,j-1} (NN-MINUS = monus, valid since i,j >= 2 there).
(def-functoid 'BORDER '(A b M p q)
  '(MATOF (succ p) (succ q)
     (VNB-LAMBDA (LIST i j) (CARTESIAN (INTERVAL 1 (succ p)) (INTERVAL 1 (succ q)))
       (IF (= i 1)
           (IF (= j 1) b (ZERO A))
           (IF (= j 1) (ZERO A) (ENTRY M (NN-MINUS i 1) (NN-MINUS j 1)))))))

;;; border-type: BORDER(A,b,M,p,q) in MAT(succ p, succ q, CARR A) when b in CARR A
;;; and M in MAT(p,q,CARR A) -- every tabulator value is b, ZERO A, or b block
;;; entry of M, all in CARR A (matof-in-mat).  Warranted 'reference like submat-type.
(support 'border-type
  '(FORALL A (FORALL b (FORALL M (FORALL p (FORALL q
     (IMPLIES (IN p NN) (IMPLIES (IN q NN)
       (IMPLIES (IN b (CARR A))
       (IMPLIES (IN M (MAT p q (CARR A)))
         (IN (BORDER A b M p q) (MAT (succ p) (succ q) (CARR A)))))))))))))
(warrant! 'border-type 'reference
  "BORDER(A,b,M,p,q) in MAT(succ p, succ q, CARR A): each tabulator value is b
   (in CARR A), ZERO A (in CARR A), or b block entry M_{i-1,j-1} (entry-in-carrier,
   i-1 in [1,p] for i in [2,succ p]); matof-in-mat applies.")

;;; The four entry read-offs (pure MATOF read-offs: entry-of-matof + beta + IF
;;; reduction + NN-MINUS(succ i,1)=i via nn-minus/bt-succ-minus-1).  Warranted
;;; 'reference like entry-of-submat / entry-of-identmat.
(support 'border-entry-11
  '(FORALL A (FORALL b (FORALL M (FORALL p (FORALL q
     (= (ENTRY (BORDER A b M p q) 1 1) b)))))))
(warrant! 'border-entry-11 'reference "BORDER(A,b,M,p,q)_{1,1} = b (i=j=1 branch).")

(support 'border-entry-1j
  '(FORALL A (FORALL b (FORALL M (FORALL p (FORALL q (FORALL j
     (IMPLIES (IN j (INTERVAL 1 (succ q))) (IMPLIES (NOT (= j 1))
       (= (ENTRY (BORDER A b M p q) 1 j) (ZERO A)))))))))))
(warrant! 'border-entry-1j 'reference
  "BORDER(A,b,M,p,q)_{1,j} = 0 for j /= 1 (i=1, j/=1 branch).")

(support 'border-entry-i1
  '(FORALL A (FORALL b (FORALL M (FORALL p (FORALL q (FORALL i
     (IMPLIES (IN i (INTERVAL 1 (succ p))) (IMPLIES (NOT (= i 1))
       (= (ENTRY (BORDER A b M p q) i 1) (ZERO A)))))))))))
(warrant! 'border-entry-i1 'reference
  "BORDER(A,b,M,p,q)_{i,1} = 0 for i /= 1 (i/=1, j=1 branch).")

(support 'border-entry-block
  '(FORALL A (FORALL b (FORALL M (FORALL p (FORALL q (FORALL i (FORALL j
     (IMPLIES (IN i (INTERVAL 1 p)) (IMPLIES (IN j (INTERVAL 1 q))
       (= (ENTRY (BORDER A b M p q) (succ i) (succ j)) (ENTRY M i j))))))))))))
(warrant! 'border-entry-block 'reference
  "BORDER(A,b,M,p,q)_{succ i, succ j} = M_{i,j} for i in [1,p], j in [1,q]
   (i/=1,j/=1 branch; NN-MINUS(succ i,1)=i).")

;;; border-entry-block2: same block read-off for GENERAL indices i,j >= 2 (in the
;;; border range, /= 1), NN-MINUS form -- lets border-mult read a block entry off a
;;; general index without destructuring it as a successor.
(support 'border-entry-block2
  '(FORALL A (FORALL b (FORALL M (FORALL p (FORALL q (FORALL i (FORALL j
     (IMPLIES (IN i (INTERVAL 1 (succ p))) (IMPLIES (NOT (= i 1))
     (IMPLIES (IN j (INTERVAL 1 (succ q))) (IMPLIES (NOT (= j 1))
       (= (ENTRY (BORDER A b M p q) i j) (ENTRY M (NN-MINUS i 1) (NN-MINUS j 1)))))))))))))))
(warrant! 'border-entry-block2 'reference
  "BORDER(A,b,M,p,q)_{i,j} = M_{i-1,j-1} for i,j /= 1 in the border range (the
   i/=1,j/=1 branch of the def; NN-MINUS = monus predecessor).")

;;; -----------------------------------------------------------------------
;;; min-degree-entry -- a matrix with a nonzero entry HAS a nonzero entry of
;;; MINIMAL degree -- used to be ASSERTED here, warranted 'well-known with the
;;; prose "apply nn-least-element to the degree set".  It is now PROVEN, in
;;; theorem-library/min-degree-entry-proof.scm, by the `minimize!' tactic
;;; (minimize.scm), whose one appeal is nn-least-element itself.  Nothing was
;;; lost in the move: the warrant's prose has become the tactic's proof.

;;; -----------------------------------------------------------------------
;;; IS-DIAGONAL(A, m, n, D): the m-by-n matrix D is diagonal -- every
;;; off-diagonal entry is zero.  The Smith reduction's TARGET shape (we take
;;; DIAGONALIZATION ONLY; the divisibility chain b11|b22|... is a later
;;; refinement).  The zero matrix is diagonal; a 0-row or 0-column matrix is
;;; vacuously diagonal (the base of the min(m,n) recursion).
(def-predicate 'IS-DIAGONAL '(A m n D)
  '(FORALL i (FORALL j
     (IMPLIES (IN i (INTERVAL 1 m)) (IMPLIES (IN j (INTERVAL 1 n))
       (IMPLIES (NOT (= i j)) (= (ENTRY D i j) (ZERO A))))))))

;;; SMITH-STAIRCASE(A, m, n, D, k): D is diagonal AND its nonzero diagonal entries
;;; form the INITIAL segment [1,k] -- entries D_ii for i <= k are nonzero, and every
;;; row past k is entirely zero.  This is what smith-diagonalization's recursion
;;; already builds (clear-pivot-cross always selects a NONZERO pivot, so the pivot
;;; of each BORDER level is nonzero and the zeros are pushed to the tail); recording
;;; it lets a caller take the leading k rows without reindexing round a zero.
(def-predicate 'SMITH-STAIRCASE '(A m n D k)
  '(AND (IS-DIAGONAL A m n D) (AND (<= k m) (AND (<= k n) (AND (FORALL i_ (IMPLIES (IN i_ (INTERVAL 1 k)) (NOT (= (ENTRY D i_ i_) (ZERO A))))) (FORALL i_ (IMPLIES (IN i_ (INTERVAL 1 m)) (IMPLIES (NOT (<= i_ k)) (FORALL j_ (IMPLIES (IN j_ (INTERVAL 1 n)) (= (ENTRY D i_ j_) (ZERO A))))))))))))

;;; -----------------------------------------------------------------------
;;; class-min-pivot: a matrix P (over a euclidean ring) with a nonzero entry
;;; is equivalent to a matrix B whose (1,1) entry is nonzero and of MINIMAL
;;; euclidean degree over the WHOLE equivalence class of P -- i.e. no matrix C
;;; equivalent to P has a nonzero entry of smaller degree.  This is the descent
;;; invariant that forces every euclidean remainder to vanish (pivot-clears-col):
;;; a nonzero remainder would sit in a matrix C ~ P with degree strictly below
;;; deg(B_{1,1}), contradicting minimality.
;;;
;;; It used to be ASSERTED here, warranted 'well-known.  That warrant swallowed
;;; four things at once: the well-ordering of NN, the formation of the class-
;;; degree set, swap-to-corner-gen, and the reflexivity/transitivity of ~ -- and
;;; the last three were already PROVEN elsewhere.  It is now PROVEN, in
;;; theorem-library/class-min-pivot-proof.scm, by the `minimize!' tactic
;;; (minimize.scm) plus swap-to-corner-gen (smith-proof.scm).

;;; nn-succ-le-antisym: for a,b in NN, succ a <= b makes b <= a impossible
;;; (succ a <= b => a < b => not b <= a).  Elementary NN order; used in the Smith
;;; descent to turn "remainder degree strictly below the minimal pivot degree"
;;; (succ(deg r) <= deg pivot) against class-minimality (deg pivot <= deg r) into
;;; a contradiction, forcing r = 0.
(support 'nn-succ-le-antisym
  '(FORALL a (IMPLIES (IN a NN) (FORALL b (IMPLIES (IN b NN)
     (IMPLIES (<= (succ a) b) (NOT (<= b a))))))))
(warrant! 'nn-succ-le-antisym 'well-known
  "succ a <= b => not(b <= a) for a,b in NN: succ a <= b gives a < b, so b <= a
   would give a < a.  Elementary order on NN.")

;;; Projection of IS-DIAGONAL, with the index guards CURRIED so a forward `fact'
;;; can detach them (the predicate's own body puts them in a shape `fact' will
;;; not unfold).  Off the diagonal, a diagonal matrix has zero entries.
(support 'diagonal-off-entry
  '(FORALL A (FORALL m (FORALL n (FORALL D
     (IMPLIES (IS-DIAGONAL A m n D)
     (FORALL i (IMPLIES (IN i (INTERVAL 1 m))
     (FORALL j (IMPLIES (IN j (INTERVAL 1 n))
     (IMPLIES (NOT (= i j))
       (= (ENTRY D i j) (ZERO A)))))))))))))
(warrant! 'diagonal-off-entry 'proof
  "D_{ij} = 0 for i /= j -- IS-DIAGONAL's defining body, re-quantified for `fact'.")

;;; -----------------------------------------------------------------------
;;; Notation -- the ENGLISH of these predicates, declared beside their
;;; definitions and read by wff->english / the proof reader (operators.scm).
;;; A def-predicate's reading cannot be derived the way a structure's noun can
;;; (noun vs adjective: IS-COMPLETE wants "s is complete", not "s is a complete"),
;;; so it is written here, once, next to what it means.
(notation! 'IS-DIAGONAL 'kind 'predicate 'arity 4
           'english "$4 is a diagonal $2-by-$3 matrix over $1")
(notation! 'IS-INVERTIBLE-MAT 'kind 'predicate 'arity 3
           'english "$3 is an invertible $2-by-$2 matrix over $1")
(notation! 'MAT-EQUIV 'kind 'predicate 'arity 5
           'english "$4 and $5 are equivalent $2-by-$3 matrices over $1")
(notation! 'SMITH-STAIRCASE 'kind 'predicate 'arity 5
           'english "$4 is in Smith staircase form of rank $5, as an $2-by-$3 matrix over $1")
