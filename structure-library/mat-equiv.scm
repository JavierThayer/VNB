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
(def-functoid 'SUBMAT '(P p q)
  '(MATOF p q (VNB-LAMBDA (LIST i j) (ENTRY P (succ i) (succ j)))))

;;; submat-type: SUBMAT(P,p,q) is a p-by-q matrix over A when P is
;;; (succ p)-by-(succ q) (each block entry P_{i+1,j+1} lies in CARR A).
;;; Warranted 'reference like the other MAT read-offs (matof-in-mat + the shift
;;; succ i in [1, succ p] for i in [1,p]).
(support 'submat-type
  '(FORALL A (FORALL p (FORALL q (FORALL P
     (IMPLIES (IN p NN) (IMPLIES (IN q NN)
       (IMPLIES (IN P (MAT (succ p) (succ q) (CARR A)))
         (IN (SUBMAT P p q) (MAT p q (CARR A)))))))))))
(warrant! 'submat-type 'reference
  "SUBMAT(P,p,q) in MAT(p,q,CARR A) for P in MAT(succ p, succ q, CARR A): each
   block entry is P_{succ i, succ j} in CARR A (entry-in-carrier; succ i in
   [1,succ p] for i in [1,p]), so matof-in-mat applies.")

;;; entry-of-submat: the (i,j) block entry is P_{i+1, j+1}.  A pure read-off,
;;; warranted 'reference like entry-of-matof (mac SUBMAT + entry-of-matof + beta
;;; reduces the goal to a reflexive equation; verified in scratchpad/submat.scm).
(support 'entry-of-submat
  '(FORALL P (FORALL p (FORALL q (FORALL i (FORALL j
     (IMPLIES (IN i (INTERVAL 1 p)) (IMPLIES (IN j (INTERVAL 1 q))
       (= (ENTRY (SUBMAT P p q) i j) (ENTRY P (succ i) (succ j)))))))))))
(warrant! 'entry-of-submat 'reference
  "SUBMAT(P,p,q)_{ij} = P_{succ i, succ j} for i in [1,p], j in [1,q]
   (entry-of-matof on the block tabulator, beta-reduced).")

;;; -----------------------------------------------------------------------
;;; min-degree-entry: a matrix with a nonzero entry HAS a nonzero entry of
;;; MINIMAL degree -- the "mu is achieved" fact that starts the Smith reduction
;;; (Prop 3.36): pick a nonzero pivot of least Euclidean degree, then division-
;;; with-remainder can only shrink it, forcing termination.  A direct application
;;; of the PROVEN well-ordering nn-least-element: the set
;;;   T = { d in NN : some nonzero entry P_ij has (GAUGE A)(P_ij) = d }
;;; is a nonempty subset of NN (nonempty by the hypothesis; a subset of NN since
;;; GAUGE(A) maps CARR A -> NN by gauge-is-degree), so nn-least-element gives a
;;; least degree d0, and its witnessing position (i*,j*) is the minimizer.
;;; Warranted 'well-known (the math is entirely in nn-least-element, which is
;;; machine-proven in theorem-library/nn-least-element.scm); QED route above.
(support 'min-degree-entry
  '(FORALL A (IMPLIES (IS-EUCLIDEAN-RING A) (FORALL m (FORALL n (FORALL P (IMPLIES (IN P (MAT m n (CARR A))) (IMPLIES (FORSOME i0 (FORSOME j0 (AND (IN i0 (INTERVAL 1 m)) (AND (IN j0 (INTERVAL 1 n)) (NOT (= (ENTRY P i0 j0) (ZERO A))))))) (FORSOME iS (FORSOME jS (AND (IN iS (INTERVAL 1 m)) (AND (IN jS (INTERVAL 1 n)) (AND (NOT (= (ENTRY P iS jS) (ZERO A))) (FORALL i (FORALL j (IMPLIES (IN i (INTERVAL 1 m)) (IMPLIES (IN j (INTERVAL 1 n)) (IMPLIES (NOT (= (ENTRY P i j) (ZERO A))) (<= ((GAUGE A) (ENTRY P iS jS)) ((GAUGE A) (ENTRY P i j)))))))))))))))))))))
(warrant! 'min-degree-entry 'well-known
  "Least-degree nonzero entry exists, by the well-ordering of NN (nn-least-element)
   applied to the degree set of the nonzero entries.  The Smith reduction's minimal
   pivot.")
