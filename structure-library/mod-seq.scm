;;; mod-seq.scm -- matrices acting on sequences of module elements.
;;;
;;; Phase C of the linear-algebra arc (algebraic-numbers.pdf ch.3, sec 8.2).
;;; The book manipulates a finite sequence  u = <u1,...,un>  of elements of an
;;; abelian group E as a COLUMN VECTOR, and lets an integral m*n matrix A act
;;; on it (eq. 82):
;;;
;;;     v_i = sum_{j=1}^{n} a_ij u_j,    written   v_col = A . u_col.
;;;
;;; We generalize Z-abelian-group to MODULE-over-a-ring, because that is what
;;; the Smith arc actually proved: smith-diagonalization works over an
;;; arbitrary EUCLIDEAN RING A, and an abelian group is a ZZ-module (see
;;; [[project_ag_are_zz_modules]]), so the book's statements are the A = ZZ
;;; instances of what follows.
;;;
;;; REPRESENTATION DECISION.  A sequence of module elements is NOT a new kind
;;; of object: it is a matrix over the set (VEC md).  MAT is already generic in
;;; its entry set --  (MAT m n X) = {P in MATRIX(X) : SIZE P = [m,n]}  --  so a
;;; column sequence of length n is  u in (MAT n 1 (VEC md))  and  u_j is
;;; (ENTRY u j 1).  This buys, for free:
;;;
;;;   * typing            (MAT / entry-in-carrier, generic in X)
;;;   * uniqueness        (matrix-entry-extensionality, generic in X)
;;;   * tabulation        (MATOF / matof-exists / matof-in-mat, generic in X)
;;;   * the SUBMAT/BORDER read-offs, if a block argument ever needs them
;;;
;;; and, crucially, lets MATACT be defined with EXACTLY the shape of MATMUL, so
;;; the associativity law  A.(B.u) = (A B).u  (Remark 3.39) is provable by
;;; mirroring matmul-assoc-proof.scm (triple-entry + finsum-fubini) rather than
;;; by fresh double-sum theory.
;;;
;;; We do not restrict the second dimension to 1: MATACT is defined for
;;; u in MAT(n,q,VEC md), i.e. a q-tuple of column sequences.  The book's
;;; u_col is the q = 1 case.  Nothing costs extra and the associativity proof
;;; is the same either way.
;;;
;;; Dependencies: module.scm (MODULE, ACT, VEC, SCAL), views.scm
;;;   (MODULE-VECTOR-AG), matrix.scm (MAT, MATOF, ENTRY, SIZE), finsum.scm.
;;; MATACT is registered as a term-forming head in wff.scm.

;;; -----------------------------------------------------------------------
;;; The vector abelian group's slots, as rewrite bridges.
;;;
;;; MODULE-VECTOR-AG is a def-view-as, so (MODULE-VECTOR-AG md) unfolds to the
;;; 4-tuple (VEC md, VADD md, VZERO md, VNEG md) and the ABELIAN-GROUP accessor
;;; macetes (CARR = NTH 1, MUL = NTH 2, ID = NTH 3) reduce a slot read.  These
;;; three named equations do the reduction in one macete step, exactly as
;;; ras-carr / ras-op / ras-id do for RING-ADDITIVE-AG.  Note that ras-op must
;;; be applied with `mac' rather than fact+subst, because pi-eq-subst! does not
;;; rewrite operator-head positions; the same holds for mvag-op.

(support 'mvag-carr
  '(FORALL md (= (CARR (MODULE-VECTOR-AG md)) (VEC md))))
(warrant! 'mvag-carr 'proof
  "carrier of a module's vector abelian group is the module's vector set.")

(support 'mvag-op
  '(FORALL md (= (MUL (MODULE-VECTOR-AG md)) (VADD md))))
(warrant! 'mvag-op 'proof
  "operation of a module's vector abelian group is the module's vector addition.")

(support 'mvag-id
  '(FORALL md (= (ID (MODULE-VECTOR-AG md)) (VZERO md))))
(warrant! 'mvag-id 'proof
  "identity of a module's vector abelian group is the module's zero vector.")

;;; -----------------------------------------------------------------------
;;; MATACT(md, P, u) -- the matrix P acting on the sequence(s) u.
;;;
;;; P is an m*n matrix of SCALARS (entries in CARR(SCAL md)), u is an n*q
;;; matrix of VECTORS (entries in VEC md), and the product is the m*q matrix of
;;; vectors whose (i,c) entry is  sum_{j=1}^{n} P_{ij} . u_{jc}, summed in the
;;; module's vector abelian group.
;;;
;;; As with MATMUL, the dimensions are read off SIZE(P), SIZE(u) so that the
;;; functoid takes no dimension arguments; the action is total (garbage in,
;;; garbage out off its typed domain) and all content lives in matact-type /
;;; matact-entry below.

(def-functoid 'MATACT '(md P u)
  '(MATOF (NTH 1 (SIZE P)) (NTH 2 (SIZE u))
     (VNB-LAMBDA (LIST i c)
       (FINSUM (MODULE-VECTOR-AG md)
               (VNB-LAMBDA j ((ACT md) (ENTRY P i j) (ENTRY u j c)))
               (INTERVAL 1 (NTH 2 (SIZE P)))))))

;;; Typing: scalars (m*n) acting on vectors (n*q) gives vectors (m*q).
(support 'matact-type
  '(FORALL md (IMPLIES (IS-MODULE md)
     (FORALL m (FORALL n (FORALL q (FORALL P (FORALL u
       (IMPLIES (IN P (MAT m n (CARR (SCAL md))))
       (IMPLIES (IN u (MAT n q (VEC md)))
         (IN (MATACT md P u) (MAT m q (VEC md)))))))))))))
(warrant! 'matact-type 'reference
  "P.u is an m-by-q matrix of vectors for P an m-by-n scalar matrix and u an
   n-by-q matrix of vectors: matof-in-mat, whose values are FINSUMs in the
   vector abelian group, typed by finsum-type + mvag-carr.")

;;; The defining entry equation, read off MATOF (this is the eq. 82 of the book
;;; when q = 1: v_i = sum_j a_ij u_j).
(support 'matact-entry
  '(FORALL md (IMPLIES (IS-MODULE md)
     (FORALL m (FORALL n (FORALL q (FORALL P (FORALL u
       (IMPLIES (IN P (MAT m n (CARR (SCAL md))))
       (IMPLIES (IN u (MAT n q (VEC md)))
       (FORALL i (IMPLIES (IN i (INTERVAL 1 m))
       (FORALL c (IMPLIES (IN c (INTERVAL 1 q))
         (= (ENTRY (MATACT md P u) i c)
            (FINSUM (MODULE-VECTOR-AG md)
                    (VNB-LAMBDA j ((ACT md) (ENTRY P i j) (ENTRY u j c)))
                    (INTERVAL 1 n)))))))))))))))))
(warrant! 'matact-entry 'reference
  "(P.u)_{ic} = sum_{j=1}^{n} P_{ij} . u_{jc}, summed in the module's vector
   abelian group; the read-off of MATACT's MATOF tabulation via entry-of-matof
   (dimensions m, n, q recovered from SIZE P, SIZE u).")

;;; The summand of matact-entry is a function on the index interval -- the
;;; hypothesis every finsum lemma (finsum-type, finsum-single-support,
;;; finsum-congruence, ...) wants.  One PSS covers every use, as
;;; matprod-summand-type does for MATMUL.
(support 'matact-summand-type
  '(FORALL md (IMPLIES (IS-MODULE md)
     (FORALL m (FORALL n (FORALL q (FORALL P (FORALL u (FORALL i (FORALL c
       (IMPLIES (IN P (MAT m n (CARR (SCAL md))))
       (IMPLIES (IN u (MAT n q (VEC md)))
       (IMPLIES (IN i (INTERVAL 1 m))
       (IMPLIES (IN c (INTERVAL 1 q))
         (IN (VNB-LAMBDA j ((ACT md) (ENTRY P i j) (ENTRY u j c)))
             (FUN (INTERVAL 1 n) (CARR (MODULE-VECTOR-AG md))))))))))))))))))
(warrant! 'matact-summand-type 'well-known
  "j |-> P_{ij} . u_{jc} is a function [1,n] -> VEC md for P:MAT(m,n,CARR(SCAL md))
   and u:MAT(n,q,VEC md): entry-in-carrier types both arguments, module-act-type
   closes the action, and mvag-carr identifies CARR(MODULE-VECTOR-AG md) = VEC md.")

;;; -----------------------------------------------------------------------
;;; The action passes through a FINSUM, on either side.
;;;
;;; These are the two module analogues of finsum-ring-distrib-{left,right}-gen,
;;; and they are exactly the hypotheses the associativity law A.(B.u) = (AB).u
;;; needs.  Each says a certain map is an abelian-group homomorphism, so each
;;; is the usual induction on |S| via finsum-insert.  Set/finiteness premises
;;; are CURRIED (not AND-packaged) so a forward `fact' detaches them from
;;; context without a cut, following finsum-fubini-c.
;;;
;;;   (1) r . (sum_z f z) = sum_z (r . f z)     -- fixed scalar, sum of vectors
;;;   (2) (sum_z c z) . x = sum_z ((c z) . x)   -- sum of scalars, fixed vector
;;;
;;; In (1) both sums are in the vector abelian group.  In (2) the LEFT sum is in
;;; the SCALAR ring's additive group and the right sum is in the vector group:
;;; the map  r |-> r . x  carries one to the other.

(support 'finsum-act-distrib-gen
  '(FORALL md (IMPLIES (IS-MODULE md)
     (FORALL r (IMPLIES (IN r (CARR (SCAL md)))
     (FORALL S (IMPLIES (IN S SET) (IMPLIES (IN (CARD S) NN)
     (FORALL f (IMPLIES (IN f (FUN S (CARR (MODULE-VECTOR-AG md))))
       (= ((ACT md) r (FINSUM (MODULE-VECTOR-AG md) f S))
          (FINSUM (MODULE-VECTOR-AG md)
                  (VNB-LAMBDA z ((ACT md) r (f z)))
                  S))))))))))))
(warrant! 'finsum-act-distrib-gen 'well-known
  "r.(SUM_z f z) = SUM_z (r . f z) in a module: x |-> r.x is an endomorphism of
   the vector abelian group.  Induction on |S| via finsum-insert:
   r.(SUM_X f + f z0) = r.SUM_X f + r.(f z0) by module-act-distrib-vec, and the
   empty case is r.0 = 0, itself r.(0+0) = r.0 + r.0 killed by
   abelian-group-idempotent-is-id on the vector group (the module-zero-act route).")

(support 'finsum-act-collect-gen
  '(FORALL md (IMPLIES (IS-MODULE md)
     (FORALL x (IMPLIES (IN x (VEC md))
     (FORALL S (IMPLIES (IN S SET) (IMPLIES (IN (CARD S) NN)
     (FORALL c (IMPLIES (IN c (FUN S (CARR (SCAL md))))
       (= ((ACT md) (FINSUM (RING-ADDITIVE-AG (SCAL md)) c S) x)
          (FINSUM (MODULE-VECTOR-AG md)
                  (VNB-LAMBDA z ((ACT md) (c z) x))
                  S))))))))))))
(warrant! 'finsum-act-collect-gen 'well-known
  "(SUM_z c z).x = SUM_z ((c z).x) in a module: r |-> r.x is a homomorphism from
   the scalar ring's additive group to the vector abelian group.  Induction on
   |S| via finsum-insert: (SUM_X c + c z0).x = (SUM_X c).x + (c z0).x by
   module-act-distrib-scalar, and the empty case is 0.x = 0 (module-zero-act).")
