;;; finprod.scm -- FINPROD / PROD-RING: finite PRODUCT of a function over a
;;;                finite set.
;;;
;;; A finite product is a finite sum in the multiplicative structure.  There
;;; is nothing new to fold: FINSUM(m, f, S) (finsum.scm) already enumerates S
;;; and folds with (OPR m) seeded at (IDEN m).  Take m to be a *multiplicative*
;;; commutative monoid and the same fold is the product.  So:
;;;
;;;   FINPROD(m, f, S)   := FINSUM(m, f, S)           -- product over comm-monoid m
;;;   PROD-RING(R, f, S) := FINPROD(R^x, f, S)        -- product over comm-ring R
;;;
;;; where R^x = COMMUTATIVE-RING-MULTIPLICATIVE-CM(R) is R's multiplicative
;;; commutative monoid (views.scm).  FINPROD is a thin readability alias --
;;; it reads as a product and keeps PROD-RING from spelling FINSUM at a view
;;; on every line -- and every finsum-comm-monoid theorem applies verbatim
;;; through it.  The product's own algebra (empty / singleton / insert /
;;; closure) and the product-of-sums expansion live in
;;; theorem-library/prod-of-sums.scm.
;;;
;;; Singletons and one-point extensions are written PAIR(x,x) / UNION(X,PAIR
;;; (k,k)) to mesh with card-insert and finite-set-induction (cardinality.scm).
;;;
;;; Dependencies: finsum.scm (FINSUM), views.scm (COMMUTATIVE-RING-
;;; MULTIPLICATIVE-CM).  Loaded after both.

(def-functoid 'FINPROD '(m f S)
  '(FINSUM m f S))

(def-functoid 'PROD-RING '(R f S)
  '(FINPROD (COMMUTATIVE-RING-MULTIPLICATIVE-CM R) f S))

;;; PROD-SET(cm, S, f): the product over a finite index set in a commutative monoid
;;; (notes-16 step 2), DEFINED 2026-09-19.  Until then it was a bare head with four
;;; characterising axioms in sequences.scm; they are theorems now
;;; (theorem-library/rake-prod-set-defined.scm).  A commutative monoid's slots are exactly
;;; what FINSUM reads, so no view is needed (contrast SUM-SET, finsum.scm).  It is FINPROD
;;; up to argument order; both names are kept.
(def-functoid 'PROD-SET '(cm S f) '(FINSUM cm f S))
