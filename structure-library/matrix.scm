;;; matrix.scm -- MATRIX(S): matrices over a set S.
;;;
;;; A matrix over S is a list of rows; each row is a list of elements of S;
;;; all rows have the same length.  In VNB terms a matrix is an element of
;;; TUPLES(TUPLES S) -- a tuple whose entries are tuples over S -- with the
;;; extra condition that the rows are equilong.  MATRIX(S) is the class of
;;; all such matrices; it is a class-former like TUPLES, FUN, BIJECTION.
;;;
;;; SIZE(M) = [rows, columns] = [LENGTH M, LENGTH(NTH 1 M)].  In a nonempty
;;; matrix every row has the column length, so NTH 1 M is representative;
;;; for the empty matrix (no rows) the column entry is unspecified.
;;;
;;; Dependencies: kernel (TUPLES, LIST, LENGTH, NTH), NN, <=.
;;; MATRIX and SIZE are registered as term-forming heads in wff.scm.

;;; M in MATRIX(S):  M is a list of lists over S, with all rows equilong.
(theory-add-axiom! *current-theory* 'matrix-membership
  '(FORALL S (FORALL M
     (IFF (IN M (MATRIX S))
          (AND (IN M (TUPLES (TUPLES S)))
               (FORALL i (IMPLIES (AND (IN i NN)
                                       (AND (<= 1 i) (<= i (LENGTH M))))
                 (FORALL j (IMPLIES (AND (IN j NN)
                                         (AND (<= 1 j) (<= j (LENGTH M))))
                   (= (LENGTH (NTH i M)) (LENGTH (NTH j M))))))))))))

;;; MATRIX(S) is a set when S is a set -- it is a subclass of the set
;;; TUPLES(TUPLES S).  Installed as an axiom for direct use.
(theory-add-axiom! *current-theory* 'matrix-sethood
  '(FORALL S (IMPLIES (IN S SET) (IN (MATRIX S) SET))))

;;; SIZE(M) = [number of rows, number of columns].
(def-functoid 'SIZE '(M)
  '(LIST (LENGTH M) (LENGTH (NTH 1 M))))
