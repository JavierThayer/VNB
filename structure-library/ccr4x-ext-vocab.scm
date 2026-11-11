;;; ccr4x-ext-vocab.scm -- wave of 2026-11-09/10 (agent CCR-1109-C2), wired 2026-11-10 from scratchpad/ccr1109c2/ccr4x-ext-vocab.scm.
;;; Library: analysis.

;;; ccr4x-ext-vocab.scm -- CCR.pdf section 4.1 (algebraic extensions): a finite extension F of a normed field K
;;; given with a K-basis, the matrix of an operator in a basis, the multiplication operator M(xi) of (27), the
;;; norm map det M(xi) and the absolute value |xi|_F = |det M(xi)|_K of (30), and the NV valuation of a field.
;;; DEFINITIONS ONLY; the laws are in theorem-library/ccr4x-ext.scm.  Agent CCR-1109-C2, 2026-11-09.
;;; Destination: structure-library/ccr4x-ext-vocab.scm.  Library: analysis (the definitions mention FNRM and
;;; the ring view of a normed field; the matrix-of-an-operator part alone is linear algebra).
;;; Load window: after structure-library/mod-seq (MATACT, GENERATES, REL-FREE), la-z4-vocab (MAP-SEQ),
;;; normed-field, and the determinant (DET).
;;;
;;; THE MODEL.  The notes identify F with K^n through the basis e_0, ..., e_(n-1) and read M(xi) as an
;;; operator on K^n.  Here F is a field ring and a module md over the ring view V of K whose vectors are the
;;; elements of F, whose vector addition is the addition of F, and whose scalar action is compatible with the
;;; multiplication of F (x (r y) = r (x y)): F is a K-algebra.  A basis is a column u of n elements of F that
;;; generates md and is free (GENERATES, REL-FREE).  The scalar r of K is the element r 1 of F.
;;;
;;;   OP-MAT(md, n, u, T)        the matrix a of an operator T on md in the basis u, read with the rows as the
;;;                              images: T u_i = sum_j a_ij u_j, that is MAP-SEQ(T, n, u) = MATACT(md, a, u).
;;;                              Unique by REL-FREE (rel-free-matact-cancel), exists by GENERATES
;;;                              (generates-coeff-matrix): op-mat-spec.  With this convention the matrix of
;;;                              S o T is OP-MAT(T) OP-MAT(S) (op-mat-compose); for the commuting operators
;;;                              M(xi) the order is immaterial.  IS-MATRIX-OF (gal-op-vocab) is the column
;;;                              convention, the transpose; it is not used because no composition law for it
;;;                              is in the tree.
;;;   IS-FIN-EXT(K, F, md, n, u)  F is a finite extension of K of degree n with basis u, as above (n >= 1).
;;;   EXT-DEGREE(K, F, md)       the n of a basis (the degree [F : K]); that it does not depend on the basis is
;;;                              free-generating-length-unique, which asks for a Euclidean scalar ring.
;;;   MULT-OP(F, xi)             the operator phi |-> xi phi of (27).
;;;   MULT-MAT(md, n, u, F, xi)  M(xi), the matrix of MULT-OP(F, xi) in the basis u.
;;;   EXT-NORM(K, F, md, n, u, xi)  the norm map N(xi) = det M(xi), an element of K.
;;;   EXT-ABS(K, F, md, n, u, xi)   |xi|_F = |det M(xi)|_K, the absolute value (30).
;;;   EXT-ABS-ROOT(K, F, md, n, u, xi)  |xi|_F^(1/n), the normalised form which restricts to |.| on K itself
;;;                              (RPOW-STAR, RECIP-STAR: real n-th roots are in the tree, rpow-star.scm).
;;;   IS-NV-VALUATION(F, nu)     nu : F -> RR is a non-archimedean valuation of the field ring F: nu >= 0,
;;;                              nu(x) = 0 iff x = 0, nu(x y) = nu(x) nu(y), nu(x + y) <= max(nu(x), nu(y))
;;;                              (Definition 1.8 for a field given as a ring with a function to RR).
;;; Binders x4*_: names no other definition uses.  No axiom, support or stamp.

(def-functoid 'OP-MAT '(x4md_ x4n_ x4u_ x4t_)
  '(IOTA x4a_ (AND (IN x4a_ (MAT x4n_ x4n_ (CARR (SCAL x4md_))))
                   (= (MAP-SEQ x4t_ x4n_ x4u_) (MATACT x4md_ x4a_ x4u_)))))
(notation! 'OP-MAT 'kind 'functoid 'arity 4 'english "the matrix of $4 in the basis $3")

(def-predicate 'IS-FIN-EXT '(x4k_ x4f_ x4md_ x4n_ x4u_)
  '(AND (IS-NORMED-FIELD x4k_)
   (AND (IS-FIELD-RING x4f_)
   (AND (IS-MODULE x4md_)
   (AND (= (SCAL x4md_) (NORMED-FIELD-AS-COMMUTATIVE-RING x4k_))
   (AND (= (VEC x4md_) (CARR x4f_))
   (AND (= (VADD x4md_) (ADD x4f_))
   (AND (= (VZERO x4md_) (ZERO x4f_))
   (AND (= (VNEG x4md_) (NEG x4f_))
   (AND (FORALL x4r_ (IMPLIES (IN x4r_ (CARR x4k_)) (FORALL x4x_ (IMPLIES (IN x4x_ (CARR x4f_))
          (FORALL x4y_ (IMPLIES (IN x4y_ (CARR x4f_))
            (= ((MUL x4f_) x4x_ ((ACT x4md_) x4r_ x4y_)) ((ACT x4md_) x4r_ ((MUL x4f_) x4x_ x4y_)))))))))
   (AND (IN x4n_ NN)
   (AND (<= 1 x4n_)
   (AND (IN x4u_ (MAT x4n_ 1 (CARR x4f_)))
   (AND (GENERATES x4md_ x4n_ x4u_) (REL-FREE x4md_ x4n_ x4u_)))))))))))))))
(notation! 'IS-FIN-EXT 'kind 'predicate 'arity 5
           'english "$2 is an extension of $1 of degree $4 with basis $5 (the scalar action $3)")

(def-functoid 'EXT-DEGREE '(x4k_ x4f_ x4md_)
  '(IOTA x4d_ (FORSOME x4b_ (IS-FIN-EXT x4k_ x4f_ x4md_ x4d_ x4b_))))
(notation! 'EXT-DEGREE 'kind 'functoid 'arity 3 'english "the degree [$2 : $1]")

(def-functoid 'MULT-OP '(x4f_ x4xi_)
  '(VNB-LAMBDA x4p_ (CARR x4f_) ((MUL x4f_) x4xi_ x4p_)))
(notation! 'MULT-OP 'kind 'functoid 'arity 2 'english "multiplication by $2 in $1")

(def-functoid 'MULT-MAT '(x4md_ x4n_ x4u_ x4f_ x4xi_)
  '(OP-MAT x4md_ x4n_ x4u_ (MULT-OP x4f_ x4xi_)))
(notation! 'MULT-MAT 'kind 'functoid 'arity 5 'english "M($5), the matrix of multiplication by $5")

(def-functoid 'EXT-NORM '(x4k_ x4f_ x4md_ x4n_ x4u_ x4xi_)
  '(DET (NORMED-FIELD-AS-COMMUTATIVE-RING x4k_) x4n_ (MULT-MAT x4md_ x4n_ x4u_ x4f_ x4xi_)))
(notation! 'EXT-NORM 'kind 'functoid 'arity 6 'english "the norm det M($6) of $6")

(def-functoid 'EXT-ABS '(x4k_ x4f_ x4md_ x4n_ x4u_ x4xi_)
  '((FNRM x4k_) (EXT-NORM x4k_ x4f_ x4md_ x4n_ x4u_ x4xi_)))
(notation! 'EXT-ABS 'kind 'functoid 'arity 6 'english "|$6|_$2 = |det M($6)|")

(def-functoid 'EXT-ABS-ROOT '(x4k_ x4f_ x4md_ x4n_ x4u_ x4xi_)
  '(RPOW-STAR (EXT-ABS x4k_ x4f_ x4md_ x4n_ x4u_ x4xi_) (RECIP-STAR x4n_)))
(notation! 'EXT-ABS-ROOT 'kind 'functoid 'arity 6 'english "|$6|_$2^(1/$4)")

(def-predicate 'IS-NV-VALUATION '(x4f_ x4nu_)
  '(AND (IN x4nu_ (FUN (CARR x4f_) RR))
   (AND (FORALL x4x_ (IMPLIES (IN x4x_ (CARR x4f_)) (<= 0 (x4nu_ x4x_))))
   (AND (FORALL x4x_ (IMPLIES (IN x4x_ (CARR x4f_)) (IFF (= (x4nu_ x4x_) 0) (= x4x_ (ZERO x4f_)))))
   (AND (FORALL x4x_ (IMPLIES (IN x4x_ (CARR x4f_)) (FORALL x4y_ (IMPLIES (IN x4y_ (CARR x4f_))
          (= (x4nu_ ((MUL x4f_) x4x_ x4y_)) (* (x4nu_ x4x_) (x4nu_ x4y_)))))))
        (FORALL x4x_ (IMPLIES (IN x4x_ (CARR x4f_)) (FORALL x4y_ (IMPLIES (IN x4y_ (CARR x4f_))
          (<= (x4nu_ ((ADD x4f_) x4x_ x4y_)) (MAX (x4nu_ x4x_) (x4nu_ x4y_))))))))))))
(notation! 'IS-NV-VALUATION 'kind 'predicate 'arity 2 'english "$2 is a non-archimedean valuation of the field $1")
