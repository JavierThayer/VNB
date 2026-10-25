;;; la-z5-vocab.scm -- the norm N_E(F) of a submodule (linear algebra, the definition
;;; after Corollary 3.45, used by Corollary 3.52) (LA-Z5, 2026-10-25).  No proof in this
;;; file.
;;;
;;; THE SOURCE.  The user's linear-algebra notes: "We will denote the invariant of
;;; Corollary 3.45 by N_F(E) and call it the norm of F relative to E" (3.45: if v, u are
;;; free generating sequences of F, E and v = A . u, then |det A| does not depend on v, u);
;;; Corollary 3.52 writes it N_E(F).  THE ADOPTED DEFINITION (the brief of 2026-10-25):
;;; N_E(F) = |det A| when rank F = n = rank E, else 0.
;;;
;;; THE DEFINITIONS.
;;;   IS-NORM-DATA(md, sm, n, xs, ys, am) -- a presentation from which the norm is read:
;;;       xs is a free generating sequence of E = VEC(md) of length n, ys a relation-free
;;;       sequence of length n spanning F = sm, am an n-by-n integer matrix with
;;;       ys = am . xs.  (Sequences are columns in MAT(n, 1, VEC md), as in mod-seq.scm.)
;;;   SUBMODULE-NORM(md, sm) -- N_E(F): if some IS-NORM-DATA(md, sm, n, xs, ys, am)
;;;       holds, the unique value |det am| over all such data (well defined by 3.45,
;;;       norm-independent, and by 3.41: all free generating sequences of E have the same
;;;       length, so F has rank n = rank E exactly when such data exist); otherwise 0.
;;;
;;; Binders: nmn_ nmx_ nmy_ nma_ nmd_ -- names no predicate body, statement or driver
;;; uses elsewhere.
;;; Needs: structure-library/mod-seq (GENERATES, REL-FREE, SPANS, MATACT), matrix (MAT),
;;; determinant (DET), numeric-instances (ZZ-RING).
;;; Destination structure-library/; LOAD WINDOW after mod-seq, la-z2-vocab and the
;;; determinant vocabulary; before theorem-library/la-z5-norm.  Library: linear-algebra.
;;; No axiom, support or stamp.

(def-predicate 'IS-NORM-DATA '(md sm n xs ys am)
  '(AND (IN n NN)
   (AND (IN xs (MAT n 1 (VEC md)))
   (AND (GENERATES md n xs)
   (AND (REL-FREE md n xs)
   (AND (IN ys (MAT n 1 (VEC md)))
   (AND (SPANS md n ys sm)
   (AND (REL-FREE md n ys)
   (AND (IN am (MAT n n ZZ))
        (= ys (MATACT md am xs)))))))))))

(def-functoid 'SUBMODULE-NORM '(md sm)
  '(IF (FORSOME nmn_ (FORSOME nmx_ (FORSOME nmy_ (FORSOME nma_ (IS-NORM-DATA md sm nmn_ nmx_ nmy_ nma_)))))
       (IOTA nmd_ (FORSOME nmn_ (FORSOME nmx_ (FORSOME nmy_ (FORSOME nma_
         (AND (IS-NORM-DATA md sm nmn_ nmx_ nmy_ nma_) (= nmd_ (abs (DET ZZ-RING nmn_ nma_)))))))))
       0))

(notation! 'IS-NORM-DATA 'kind 'predicate 'arity 6
           'english "$4 freely generates $1, $5 is relation-free and spans $2, both of length $3, and $5 = $6 . $4")
(notation! 'SUBMODULE-NORM 'kind 'functoid 'arity 2
           'english "the norm N_E(F) of $2 relative to $1")
