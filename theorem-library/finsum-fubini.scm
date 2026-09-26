;;; RETIRED 2026-09-17 (proven, modulo 0): finsum-fubini -- theorem-library/rake-finsum-core.scm
;;; (a double fold with every family a VARIABLE; ni on the row count).  finsum-fubini-c lives in
;;; theorem-library/rake-finsum-fubini-c.scm.
;;; RETIRED 2026-09-17 (proven modulo finsum-fubini): finsum-fubini-c -- theorem-library/rake-finsum-laws2.scm
;;; theorem-library/finsum-fubini.scm
;;;
;;; finsum-fubini:  interchange of the two summations in a double FINSUM
;;; over a product of finite sets, in an abelian group.
;;;
;;;   sum_{i in X} sum_{j in Y} f(i,j)  =  sum_{j in Y} sum_{i in X} f(i,j)
;;;
;;; The values lie in an abelian group; no ring or scalar action is needed.
;;; Well-definedness rests on the same ag-commutativity that gives FINSUM
;;; its index-independence (sum-ag-permutation-invariance via
;;; finsum-well-defined).
;;;
;;; f is typed on the Cartesian product X x Y so applications use the
;;; tupled form (f (LIST i j)); the curried form (f i j) is quasi-equal by
;;; apply-tupling-2.  Inner lambdas bind i, j (lowercase) -- distinct from
;;; outer X, Y under VNB's case-folding.  See [[no-case-variant-binders]].


;;; ----- Plain-English gloss (PSS review 2026-06-26): 3+-line statement -----
(gloss! 'finsum-fubini
  "For an abelian group ag, finite index sets X and Y, and a function f on the product X*Y valued in ag: summing f over Y inside and X outside gives the same result as summing over X inside and Y outside.  Fubini / order-of-summation for finite double sums.")

;;; finsum-fubini-c: finsum-fubini with the (IN X SET AND IN CARD X NN) premises
;;; CURRIED into separate implications, so a forward `fact' can detach each guard
;;; from context without a cut (fact does not split conjunctive antecedents).
;;; Identical conclusion; follows from finsum-fubini by AND-introduction.
