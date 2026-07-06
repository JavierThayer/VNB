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
