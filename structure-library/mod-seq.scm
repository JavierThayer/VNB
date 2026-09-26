;;; RETIRED 2026-09-17 (proven): finsum-act-collect-gen -- theorem-library/rake-finsum-core.scm
;;; RETIRED 2026-09-17 (proven): finsum-act-distrib-gen -- theorem-library/rake-finsum-laws2.scm
;;; RETIRED 2026-09-17 (proven): matact-entry -- theorem-library/rake-identmat.scm (the module twin of matmul-entry).
;;; RETIRED 2026-09-17 (proven): submodule-finsum-closed -- theorem-library/rake-finsum-typing.scm
;;; (by the fold-length induction `finsum-in-subset', not the finite-set induction its warrant named)
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
;;; MATACT is registered as a term-forming head in wff.scm; LINCOMB registers
;;; itself (def-functoid).
;;; RETIRED 2026-09-14 (proven): matact-summand-type -- theorem-library/lam-fun-bricks.scm (dk-lam-fun!)
;;; (matact-summand-type-le is NOT retired: class C -- k untyped; it was removed by an
;;; over-matching name pattern and put back.)

;;; -----------------------------------------------------------------------
;;; The vector abelian group's slots, as rewrite bridges.
;;;
;;; MODULE-VECTOR-AG is a def-functor, so (MODULE-VECTOR-AG md) unfolds to the
;;; 4-tuple (VEC md, VADD md, VZERO md, VNEG md) and the ABELIAN-GROUP accessor
;;; macetes (CARR = NTH 1, MUL = NTH 2, IDEN = NTH 3) reduce a slot read.  These
;;; three named equations do the reduction in one macete step, exactly as
;;; ras-carr / ras-op / ras-id do for RING-ADDITIVE-AG.  Note that ras-op must
;;; be applied with `mac' rather than fact+subst, because pi-eq-subst! does not
;;; rewrite operator-head positions; the same holds for mvag-op.

;;; mvag-carr MOVED 2026-09-15 (wave 6) to theorem-library/ag-view-read-offs.scm, where it is PROVEN modulo 0 -- RESTATED with an IS-MODULE guard (same reason).

;;; mvag-op MOVED 2026-09-15 (wave 6) to theorem-library/ag-view-read-offs.scm, where it is PROVEN modulo 0 -- RESTATED with an IS-MODULE guard (same reason).

;;; mvag-id MOVED 2026-09-15 (wave 6) to theorem-library/ag-view-read-offs.scm, where it is PROVEN modulo 0 -- RESTATED with an IS-MODULE guard (same reason).

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
     (VNB-LAMBDA (LIST i c) (CARTESIAN (INTERVAL 1 (NTH 1 (SIZE P))) (INTERVAL 1 (NTH 2 (SIZE u))))
       (FINSUM (MODULE-VECTOR-AG md)
               (VNB-LAMBDA j (INTERVAL 1 (NTH 2 (SIZE P))) ((ACT md) (ENTRY P i j) (ENTRY u j c)))
               (INTERVAL 1 (NTH 2 (SIZE P)))))))

;;; -----------------------------------------------------------------------
;;; LINCOMB(md, n, c, u) -- the linear combination  sum_{j=1}^{n} c_{1j} . u_{j1}
;;; of a length-n column sequence u with a coefficient row c, as a FINSUM in the
;;; module's vector abelian group.
;;;
;;; Defined DIRECTLY, not as the single entry of the 1-by-1 product
;;; MATACT(md, c, u), which is what GENERATES / REL-FREE / SPANS / SPAN /
;;; LASTCOEFF-SET read until 2026-09-16.  The two agree when n >= 1
;;; (theorem-library/span-bricks-proof.scm, `matact-lincomb'), and differ at
;;; n = 0: there u is [], a matrix with no rows does not determine its column
;;; count (matrix.scm), MATACT reads the column count off SIZE([]) = [0, 0],
;;; and the "1-by-1 product" is 1-by-0 -- its (1,1) entry is NTH(1, []), an
;;; unspecified value.  The empty combination must be VZERO, and as a FINSUM
;;; over INTERVAL(1, 0) it is (finsum-empty).  The user's decision, 2026-09-16.
(def-functoid 'LINCOMB '(md n c u)
  '(FINSUM (MODULE-VECTOR-AG md)
           (VNB-LAMBDA j (INTERVAL 1 n) ((ACT md) (ENTRY c 1 j) (ENTRY u j 1)))
           (INTERVAL 1 n)))


;;; Typing: scalars (m*n) acting on vectors (n*q) gives vectors (m*q).
;;; matact-type MOVED 2026-09-15 (wave 6) to theorem-library/matunit-matact-type.scm, where it is PROVEN.

;;; The defining entry equation, read off MATOF (this is the eq. 82 of the book
;;; when q = 1: v_i = sum_j a_ij u_j).
;;;
;;; GUARDED on 1 <= n (2026-09-16).  At n = 0 it is FALSE: P = [[]] is 1-by-0,
;;; u = [] is in MAT(0, 1, VEC md), MATACT reads the column count off
;;; SIZE([]) = [0, 0], so MATACT(md, P, u) is 1-by-0 and its (1,1) entry is
;;; NTH(1, []) -- while the right side is the empty sum VZERO(md), for every
;;; module md.  The guard is free at the citers that hold an index j in
;;; INTERVAL(1, n).

;;; The summand of matact-entry is a function on the index interval -- the
;;; hypothesis every finsum lemma (finsum-type, finsum-single-support,
;;; finsum-congruence, ...) wants.  One PSS covers every use, as
;;; matprod-summand-type does for MATMUL.

;;; The same summand is a function on any SUB-interval [1,k] with k <= n.  When a
;;; FINSUM over [1,succ n] is back-peeled (finsum-interval-peel), the leftover
;;; sum keeps the ORIGINAL summand (typed on [1,succ n]) but now ranges over
;;; [1,n]; finsum-congruence against a length-n summand then needs this shorter
;;; typing.  matact-summand-type is the k = n special case; every peel wants the
;;; k < n one.

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



;;; -----------------------------------------------------------------------
;;; Generating and relation-free sequences (book, start of sec 8.2).
;;;
;;; A length-n sequence of module elements is u in MAT(n,1,VEC md).  A row of
;;; coefficients is c in MAT(1,n,CARR(SCAL md)), and the linear combination is
;;;
;;;     c . u  =  LINCOMB(md, n, c, u)  =  sum_{j=1}^{n} c_{1j} . u_{j1},
;;;
;;; which for n >= 1 is the single entry of the 1-by-1 product MATACT(md,c,u)
;;; (`matact-lincomb'), so Lemma 3.40 (invertible matrices preserve both
;;; predicates) still comes from matact-assoc.  Until 2026-09-16 the predicates
;;; were stated with that entry itself, which is wrong at n = 0 (see LINCOMB).
;;;
;;; GENERATES: every vector is a coefficient combination of u.  (The book's
;;; "u generates E".)
(def-predicate 'GENERATES '(md n u)
  '(FORALL x_ (IMPLIES (IN x_ (VEC md))
     (FORSOME c_ (AND (IN c_ (MAT 1 n (CARR (SCAL md))))
                      (= x_ (LINCOMB md n c_ u)))))))

;;; REL-FREE: the only coefficient row annihilating u is the zero row.  (The
;;; book's "relation free", eq. 81.  Over a field this is linear independence.)
(def-predicate 'REL-FREE '(md n u)
  '(FORALL c_ (IMPLIES (IN c_ (MAT 1 n (CARR (SCAL md))))
     (IMPLIES (= (LINCOMB md n c_ u) (VZERO md))
       (FORALL j_ (IMPLIES (IN j_ (INTERVAL 1 n))
         (= (ENTRY c_ 1 j_) (ZERO (SCAL md)))))))))

;;; Assembling a coefficient MATRIX from a generating sequence.
;;;
;;; The book writes, without comment, "there are coefficients A = {a_ij} such
;;; that v_i = sum_j a_ij u_j", i.e. v_col = A . u_col.  That step is a CHOICE
;;; construction: GENERATES gives, for each i in [1,m] separately, SOME
;;; coefficient row for v_{i1}; one then picks a row for every i at once and
;;; tabulates.  It is the only choice step in this part of the development.
;;;
;;; GUARDED 2026-09-16: n = 0 forces m = 0.  With n = 0 and m >= 1, cm is
;;; m-by-0, u = [], and MATACT(md, cm, u) is m-by-0 (the column count is read
;;; off SIZE([]) = [0, 0]), never the m-by-1 v.  A zero middle dimension forces
;;; an empty product; this is that condition, with the outer column count 1.
;;; generates-coeff-matrix RETIRED 2026-09-19 (rake batch 6): proven modulo 0 in theorem-library/rake-generates-coeff.scm

;;; -----------------------------------------------------------------------
;;; SPANS(md, n, u, sm): the length-n sequence u generates the SUBMODULE sm.
;;;
;;; Same shape as GENERATES, but relativized to a submodule: u's own entries must
;;; lie in sm, and every element of sm is a coefficient combination of u.
;;; GENERATES(md,n,u) is the sm = (VEC md) case (the entry clause is then vacuous).
;;; The submodule variable is `sm', NOT `s' -- `S' is the finsum index set below and
;;; MIT case-folds.
(def-predicate 'SPANS '(md n u sm)
  '(AND (FORALL j_ (IMPLIES (IN j_ (INTERVAL 1 n)) (IN (ENTRY u j_ 1) sm)))
        (FORALL x_ (IMPLIES (IN x_ sm)
          (FORSOME c_ (AND (IN c_ (MAT 1 n (CARR (SCAL md))))
                           (= x_ (LINCOMB md n c_ u))))))))

;;; -----------------------------------------------------------------------
;;; SPAN(md, n, u) -- the set of coefficient combinations of u, as a SEP set.
;;;
;;; SPANS is a PREDICATE ("this submodule is spanned by u"); the induction of
;;; spans-submodule-fg has to CONSTRUCT the submodule spanned by a truncated
;;; sequence u_1..u_p, so it needs the set itself.  Everything about it is a
;;; theorem, not an axiom:
;;;   span-is-submodule   IS-SUBMODULE(md, SPAN(md,n,u))     [lincomb-row-add,
;;;                                                           lincomb-row-scale]
;;;   spans-span          SPANS(md, n, u, SPAN(md,n,u))      [lincomb-unitrow]
;;; both in theorem-library/span-bricks-proof.scm.
;;;
;;; The bound variable is x_ and the witness c_, per the file's inner-binder
;;; convention (MIT case-folds, and `c' is a column index in matact-entry).
(def-functoid 'SPAN '(md n u)
  '(SEP x_ (VEC md)
     (FORSOME c_ (AND (IN c_ (MAT 1 n (CARR (SCAL md))))
                      (= x_ (LINCOMB md n c_ u))))))

;;; The membership IFF.  `def-functoid' installs only a rewrite macete, never a
;;; theorem, so `mac' can unfold SPAN in a GOAL but `mac-h' -- which looks the
;;; name up in *theorem-table* to check it is an equivalence -- cannot touch an
;;; assumption.  Every use of SPAN reads an assumption `x in SPAN(md,n,u)', so
;;; state the IFF once.  It is DEFINITIONAL: the functoid unfold composed with
;;; the separation schema, both trusted base -- exactly the IFF `def-predicate'
;;; would have generated had SPAN been a predicate.  (hahn-banach-proof.scm's
;;; span-add-one-membership is the same read-off, but was asserted.)
(fluid-let ((*current-provenance* 'definitional))
  (theory-add-axiom! *current-theory* 'span-membership
    '(FORALL md (FORALL n (FORALL u (FORALL x_
       (IFF (IN x_ (SPAN md n u))
            (AND (IN x_ (VEC md))
                 (FORSOME c_ (AND (IN c_ (MAT 1 n (CARR (SCAL md))))
                                  (= x_ (LINCOMB md n c_ u))))))))))))

;;; -----------------------------------------------------------------------
;;; LASTCOEFF-SET(md, p, u, sm) -- the set of possible LAST coefficients of an
;;; element of sm, written as a length-(succ p) combination of u:
;;;   { r in CARR(SCAL md) : some c in MAT(1,succ p,CARR(SCAL md)) has
;;;                          c_{1,succ p} = r  and  c.u in sm }.
;;; The engine of the spans-submodule-fg descent: it is an IDEAL of SCAL md
;;; (lastcoeff-set-is-ideal), so over a euclidean ring it is principal, and its
;;; generator splits sm into "last coefficient a multiple of the generator".
;;; Same binder discipline as SPAN (x_ / c_; r_ is the last coefficient).
(def-functoid 'LASTCOEFF-SET '(md p u sm)
  '(SEP r_ (CARR (SCAL md))
     (FORSOME c_ (AND (IN c_ (MAT 1 (succ p) (CARR (SCAL md))))
                 (AND (= (ENTRY c_ 1 (succ p)) r_)
                      (IN (LINCOMB md (succ p) c_ u) sm))))))

(fluid-let ((*current-provenance* 'definitional))
  (theory-add-axiom! *current-theory* 'lastcoeff-set-membership
    '(FORALL md (FORALL p (FORALL u (FORALL sm (FORALL r_
       (IFF (IN r_ (LASTCOEFF-SET md p u sm))
            (AND (IN r_ (CARR (SCAL md)))
                 (FORSOME c_ (AND (IN c_ (MAT 1 (succ p) (CARR (SCAL md))))
                             (AND (= (ENTRY c_ 1 (succ p)) r_)
                                  (IN (LINCOMB md (succ p) c_ u) sm)))))))))))))

;;; A submodule is closed under finite sums of its elements.  IS-SUBMODULE gives
;;; closure under the binary VADD and contains VZERO; FINSUM is built from those by
;;; induction on |S| (finsum-empty for the base, finsum-insert for the step).

;;; -----------------------------------------------------------------------
;;; Notation -- the ENGLISH of these predicates, declared beside their
;;; definitions and read by wff->english / the proof reader (operators.scm).
;;; A def-predicate's reading cannot be derived the way a structure's noun can
;;; (noun vs adjective: IS-COMPLETE wants "s is complete", not "s is a complete"),
;;; so it is written here, once, next to what it means.
(notation! 'GENERATES 'kind 'predicate 'arity 3
           'english "the $2 vectors $3 generate $1")
(notation! 'REL-FREE 'kind 'predicate 'arity 3
           'english "the $2 vectors $3 are linearly independent in $1")
(notation! 'SPANS 'kind 'predicate 'arity 4
           'english "the $2 vectors $3 span $4 in $1")

;;; matact-summand-type-le MOVED 2026-09-15 (wave 7) to theorem-library/matact-summand-type-le-proof.scm as matact-summand-type-le-guarded: the unguarded form is FALSE (its whole content is [1,k] subset [1,n], which needs k in NN -- k <= n is the RR order and types nothing), so it now carries (IN k NN).  User's decision.
