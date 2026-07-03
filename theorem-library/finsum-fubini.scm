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

(support 'finsum-fubini
  '(FORALL ag (IMPLIES (IS-ABELIAN-GROUP ag)
     (FORALL X (IMPLIES (AND (IN X SET) (IN (CARD X) NN))
     (FORALL Y (IMPLIES (AND (IN Y SET) (IN (CARD Y) NN))
     (FORALL f (IMPLIES (IN f (FUN (CARTESIAN X Y) (CARR ag)))
       (= (FINSUM ag (VNB-LAMBDA i (FINSUM ag (VNB-LAMBDA j (f (LIST i j))) Y)) X)
          (FINSUM ag (VNB-LAMBDA j (FINSUM ag (VNB-LAMBDA i (f (LIST i j))) X)) Y)))))))))))

;;; ----- Plain-English gloss (PSS review 2026-06-26): 3+-line statement -----
(gloss! 'finsum-fubini
  "For an abelian group ag, finite index sets X and Y, and a function f on the product X*Y valued in ag: summing f over Y inside and X outside gives the same result as summing over X inside and Y outside.  Fubini / order-of-summation for finite double sums.")

;;; finsum-fubini-c: finsum-fubini with the (IN X SET AND IN CARD X NN) premises
;;; CURRIED into separate implications, so a forward `fact' can detach each guard
;;; from context without a cut (fact does not split conjunctive antecedents).
;;; Identical conclusion; follows from finsum-fubini by AND-introduction.
(support 'finsum-fubini-c
  '(FORALL ag (IMPLIES (IS-ABELIAN-GROUP ag)
     (FORALL X (IMPLIES (IN X SET) (IMPLIES (IN (CARD X) NN)
     (FORALL Y (IMPLIES (IN Y SET) (IMPLIES (IN (CARD Y) NN)
     (FORALL f (IMPLIES (IN f (FUN (CARTESIAN X Y) (CARR ag)))
       (= (FINSUM ag (VNB-LAMBDA i (FINSUM ag (VNB-LAMBDA j (f (LIST i j))) Y)) X)
          (FINSUM ag (VNB-LAMBDA j (FINSUM ag (VNB-LAMBDA i (f (LIST i j))) X)) Y)))))))))))))
(warrant! 'finsum-fubini-c 'well-known
  "finsum-fubini with curried set/finiteness premises (AND-packaged), for fact-friendly forward use.")
