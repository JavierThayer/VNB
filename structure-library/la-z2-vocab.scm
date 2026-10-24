;;; la-z2-vocab.scm -- the principal sequence of a subgroup (linear algebra, the
;;; definition after Corollary 3.45) (LA-Z2, 2026-10-23).  No proof in this file.
;;;
;;; The notes: if F is contained in E, E free of rank n, a sequence b = <b_1, ..., b_n>
;;; as in Proposition 3.44 -- free generators e_1, ..., e_n of E, non-negative integers
;;; b_i with b_i dividing b_{i+1}, and b_1 e_1, ..., b_n e_n generating F -- is a
;;; principal sequence for F corresponding to the basis e.
;;;
;;; Setting as in mod-seq.scm: a module md (over Z: SCAL(md) = ZZ-RING, stated by the
;;; theorems that use this), a sequence is a column es in MAT(n, 1, VEC md), and F is the
;;; set sm.  REPRESENTATION: the sequence b is the diagonal of an n-by-n diagonal integer
;;; matrix dm, so that b_1 e_1, ..., b_n e_n is the column MATACT(md, dm, es).  The
;;; divisibility clause is stated for every pair i <= j (equivalent to the notes'
;;; consecutive form by transitivity, and the form 3.36 uses).
;;;
;;; Destination structure-library/; after mod-seq, la-z-vocab and zz-divisibility.
;;; Library: linear-algebra.

(def-predicate 'IS-PRINCIPAL-SEQUENCE '(md n sm es dm)
  '(AND (IN es (MAT n 1 (VEC md)))
   (AND (GENERATES md n es)
   (AND (REL-FREE md n es)
   (AND (IN dm (MAT n n ZZ))
   (AND (IS-DIAGONAL ZZ-RING n n dm)
   (AND (FORALL psi_ (IMPLIES (IN psi_ (INTERVAL 1 n)) (<= 0 (ENTRY dm psi_ psi_))))
   (AND (FORALL psi_ (FORALL psj_ (IMPLIES (IN psi_ (INTERVAL 1 n)) (IMPLIES (IN psj_ (INTERVAL 1 n))
          (IMPLIES (<= psi_ psj_) (ZZ-DIVIDES (ENTRY dm psi_ psi_) (ENTRY dm psj_ psj_)))))))
        (SPANS md n (MATACT md dm es) sm)))))))))

(notation! 'IS-PRINCIPAL-SEQUENCE 'kind 'predicate 'arity 5
           'english "the diagonal of $5 is a principal sequence for $3 corresponding to the basis $4 of $1")
