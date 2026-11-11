;;; cnvs-vocab.scm -- wave of 2026-11-09/10 (agent CNVS), wired 2026-11-10 from scratchpad/cnvs-1109/cnvs-vocab.scm.
;;; Library: analysis.

;;; cnvs-vocab.scm -- COMPLEX NORMED VECTOR SPACES (CNVS, 2026-11-09).  Vocabulary only:
;;; no proof, no support, no axiom of its own (the three `def-functor' views install the
;;; usual definitional typing axioms, as every view in the tree does).
;;; Destination: structure-library/cnvs-vocab.scm.
;;;
;;; THE DESIGN IS THE USER'S (2026-11-09, following his design for complex spaces of
;;; 2026-10-18, scratchpad/triage/SIP-1.md and structure-library/sip-complex-vocab.scm): a
;;; complex space is a REAL space with a complex structure J.
;;;
;;; THE SHAPE: the seven slots of the real NORMED-VECTOR-SPACE (normed-vector-space.scm) at
;;; their indices (one name, one slot) and JOP at slot 8, an operation VEC -> VEC -- the slot
;;; that COMPLEX-SEMI-INNER-PRODUCT-SPACE gives J, at the same index:
;;;     1 SCAL  2 VEC  3 VADD  4 VZERO  5 VNEG  6 ACT (real scalars)  7 VNRM  8 JOP
;;; THE LAWS:
;;;   * the first seven slots form a normed vector space -- ONE law, IS-NORMED-VECTOR-SPACE
;;;     of the literal seven-list, which is exactly the view CNVS-AS-NVS below (so the view's
;;;     typing axiom is that law read off, as for CSIP-AS-SIP);
;;;   * JOP is real-linear and J^2 = -I (the predicates of sip-complex-vocab.scm, which read
;;;     only VEC, VADD, ACT, VNEG of their first argument);
;;;   * the norm is COMPLEX-homogeneous: ||c.x|| = |c| ||x|| for c in CC, where
;;;     c.x = CACT(s)(c, x) = Re(c).x + Im(c).Jx is the complex scalar multiplication of
;;;     sip-complex-vocab.scm (the notes' (37)), reused here unchanged: its body reads only
;;;     VADD, ACT, JOP, VEC, all at the indices above.
;;; Isometry of J (||Jx|| = ||x||) is not a law: it is the case c = i of the last one.
;;;
;;; THE VIEWS (the names follow normed-vector-space.scm and ba-vocab.scm):
;;;   CNVS-AS-NVS        forget J                     -> NORMED-VECTOR-SPACE
;;;   CNVS-AS-MODULE     forget J and the norm        -> MODULE (real scalars)
;;;   CNVS-AS-NORMED-AG  the additive normed group    -> NORMED-AG
;;; The view specializer transports every NVS / MODULE / NORMED-AG theorem present when this
;;; file loads to a companion `<name>-cnvs-as-nvs' (-cnvs-as-module, -cnvs-as-normed-ag).
;;; CNVS-METRIC-SPACE(v) is NAG-METRIC-SPACE of the third view (the CNA-METRIC-SPACE recipe);
;;; COMPLEX-BANACH-SPACE is the complete refinement.
;;;
;;; THE BRIDGES (proven in theorem-library/cnvs-*.scm):
;;;   CMOD-CNVS(m, nf)  the REALIFICATION of a module m over the complex numbers with a norm
;;;                     nf: real scalars acting by restriction, J = multiplication by i.  A
;;;                     MODULE with SCAL = CC and a complex-homogeneous norm gives a CNVS.
;;;   CIPS-CNVS(w)      a complex inner product space, through its module view, norm IP-NORM;
;;;   CSIP-CNVS(v)      a complex pre-Hilbert space, through CSIP-CIPS (sip-complex-vocab):
;;;                     CIPS-CNVS(CSIP-CIPS(v)), compatible with v by construction;
;;;   (CNA-CNVS(a), the module view of a complex normed algebra, is in cnvs-ba-vocab.scm:
;;;   it needs ba-vocab.scm, library operator-algebras.)
;;;
;;; BOUNDED OPERATORS between two CNVS (the book's B(X, Y)): complex-linear (additive and
;;; CACT-homogeneous) maps with a bound, CNVS-BOUNDED-OPS(v, w), the operator norm
;;; CNVS-OPNORM (the BA-BH OPNORM recipe with VNRM for IP-NORM), the pointwise operations
;;; CBOP-*, and the normed group CBOP-NORMED-AG(v, w) (the BOP-NORMED-AG recipe).
;;;
;;; Binders: cn?_ and cb?_ (cnx_ cny_ cnr_ cnc_ cnt_ cna_ cbx_ cby_ cbs_ cbt_ cbc_ cbm_ cba_),
;;; used by nothing else in the tree.
;;;
;;; LOAD WINDOW: after structure-library/sip-complex-vocab (CACT, IS-REAL-LINEAR-OP,
;;; IS-SQUARE-MINUS-ID, the JOP slot), structure-library/hilbert-space and
;;; structure-library/nvs-metric, and AFTER the NVS / MODULE / NORMED-AG theorem files whose
;;; companions the proofs cite (theorem-library/nvs-act-laws, nvs-norm-laws, frechet-metric,
;;; hahn-banach-sublinear: all far above 3836).  In practice: right after
;;; theorem-library/sip-quotient-complete (load.scm 3874).  Library: analysis (the library of
;;; normed-vector-space.scm and sip-complex-vocab.scm).

;;; ---- the structure -----------------------------------------------------------------------
(declare-structure COMPLEX-NORMED-VECTOR-SPACE
  (instance-var s)
  (substructure SCAL RING)
  (carriers VEC)
  (op VADD (CARTESIAN VEC VEC) VEC)
  (constant VZERO VEC)
  (op VNEG VEC VEC)
  (op ACT (CARTESIAN (CARR SCAL) VEC) VEC)
  (op VNRM VEC RR)
  (op JOP VEC VEC)
  (law "is-normed-vector-space([scal(s), vec(s), vadd(s), vzero(s), vneg(s), act(s), vnrm(s)])")
  (law "is-real-linear-op(s, jop(s))")
  (law "is-square-minus-id(s, jop(s))")
  (law "forall([cnc_ in cc, cnx_ in vec(s)], vnrm(s)(cact(s)(cnc_, cnx_)) = magnitude(cnc_) * vnrm(s)(cnx_))"))

;;; THE VIEWS
(def-functor 'CNVS-AS-NVS
  'COMPLEX-NORMED-VECTOR-SPACE '(SCAL VEC VADD VZERO VNEG ACT VNRM)
  'NORMED-VECTOR-SPACE         '(SCAL VEC VADD VZERO VNEG ACT VNRM))

(def-functor 'CNVS-AS-MODULE
  'COMPLEX-NORMED-VECTOR-SPACE '(SCAL VEC VADD VZERO VNEG ACT)
  'MODULE                      '(SCAL VEC VADD VZERO VNEG ACT))

(def-functor 'CNVS-AS-NORMED-AG
  'COMPLEX-NORMED-VECTOR-SPACE '(VEC VADD VZERO VNEG VNRM)
  'NORMED-AG                   '(CARR OPR IDEN INV NRM))

(def-functoid 'CNVS-METRIC-SPACE '(cnv_)
  '(NAG-METRIC-SPACE (CNVS-AS-NORMED-AG cnv_)))

(declare-structure COMPLEX-BANACH-SPACE
  (instance-var s)
  (same-shape-as COMPLEX-NORMED-VECTOR-SPACE)
  (law "is-complete(cnvs-metric-space(s))"))

;;; ---- the realification of a complex normed module ----------------------------------------
;;; m: a MODULE whose scalars are the complex numbers; nf: a norm on VEC(m).
(def-functoid 'CMOD-RACT '(m)
  '(VNB-LAMBDA (LIST cnr_ cnx_) (CARTESIAN RR (VEC m)) ((ACT m) cnr_ cnx_)))
(def-functoid 'CMOD-J '(m)
  '(VNB-LAMBDA cnx_ (VEC m) ((ACT m) +i cnx_)))
(def-functoid 'CMOD-CNVS '(m nf)
  '(LIST (NORMED-FIELD-AS-COMMUTATIVE-RING RR-NORMED-FIELD) (VEC m) (VADD m) (VZERO m) (VNEG m)
         (CMOD-RACT m) nf (CMOD-J m)))

;;; THE NORM HYPOTHESIS: nf is a norm on the complex module m, complex-homogeneous
(def-predicate 'IS-CMOD-NORM '(cnm_ cnf_)
  '(AND (IN cnf_ (FUN (VEC cnm_) RR))
   (AND (FORALL cnx_ (IMPLIES (IN cnx_ (VEC cnm_)) (<= 0 (cnf_ cnx_))))
   (AND (FORALL cnx_ (IMPLIES (IN cnx_ (VEC cnm_)) (IFF (= (cnf_ cnx_) 0) (= cnx_ (VZERO cnm_)))))
   (AND (FORALL cnc_ (IMPLIES (IN cnc_ CC) (FORALL cnx_ (IMPLIES (IN cnx_ (VEC cnm_))
          (= (cnf_ ((ACT cnm_) cnc_ cnx_)) (* (magnitude cnc_) (cnf_ cnx_)))))))
        (FORALL cnx_ (IMPLIES (IN cnx_ (VEC cnm_)) (FORALL cny_ (IMPLIES (IN cny_ (VEC cnm_))
          (<= (cnf_ ((VADD cnm_) cnx_ cny_)) (+ (cnf_ cnx_) (cnf_ cny_))))))))))))
;;; the underlying real normed space of CMOD-CNVS(m, nf): its first seven slots
(def-functoid 'CMOD-NVS '(m nf)
  '(LIST (NORMED-FIELD-AS-COMMUTATIVE-RING RR-NORMED-FIELD) (VEC m) (VADD m) (VZERO m) (VNEG m)
         (CMOD-RACT m) nf))

;;; the three instances
(def-functoid 'CIPS-VNRM '(w)
  '(VNB-LAMBDA cnx_ (VEC w) (IP-NORM w cnx_)))
(def-functoid 'CIPS-CNVS '(w)
  '(CMOD-CNVS (COMPLEX-INNER-PRODUCT-SPACE-AS-MODULE w) (CIPS-VNRM w)))
(def-functoid 'CSIP-CNVS '(v)
  '(CIPS-CNVS (CSIP-CIPS v)))

;;; ---- bounded operators between two complex normed vector spaces -------------------------
(def-predicate 'IS-CNVS-LINEAR-OP '(cbv_ cbw_ cbt_)
  '(AND (IN cbt_ (FUN (VEC cbv_) (VEC cbw_)))
   (AND (FORALL cbx_ (IMPLIES (IN cbx_ (VEC cbv_)) (FORALL cby_ (IMPLIES (IN cby_ (VEC cbv_))
          (= (cbt_ ((VADD cbv_) cbx_ cby_)) ((VADD cbw_) (cbt_ cbx_) (cbt_ cby_)))))))
        (FORALL cbc_ (IMPLIES (IN cbc_ CC) (FORALL cbx_ (IMPLIES (IN cbx_ (VEC cbv_))
          (= (cbt_ ((CACT cbv_) cbc_ cbx_)) ((CACT cbw_) cbc_ (cbt_ cbx_))))))))))

(def-predicate 'IS-CNVS-BOUNDED-OP '(cbv_ cbw_ cbt_)
  '(AND (IS-CNVS-LINEAR-OP cbv_ cbw_ cbt_)
        (FORSOME cbm_ (AND (IN cbm_ RR) (AND (<= 0 cbm_)
          (FORALL cbx_ (IMPLIES (IN cbx_ (VEC cbv_))
            (<= ((VNRM cbw_) (cbt_ cbx_)) (* cbm_ ((VNRM cbv_) cbx_))))))))))

(def-functoid 'CNVS-BOUNDED-OPS '(cbv_ cbw_)
  '(SEP cbt_ (FUN (VEC cbv_) (VEC cbw_)) (IS-CNVS-BOUNDED-OP cbv_ cbw_ cbt_)))

(def-functoid 'CNVS-OPNORM '(cbv_ cbw_ cbt_)
  '(SUP (SEP cba_ RR
          (OR (= cba_ 0)
              (FORSOME cbx_ (AND (IN cbx_ (VEC cbv_))
                            (AND (NOT (= ((VNRM cbv_) cbx_) 0))
                                 (= cba_ (* ((VNRM cbw_) (cbt_ cbx_)) (recip ((VNRM cbv_) cbx_)))))))))))

(def-functoid 'CBOP-SUM '(cbv_ cbw_ cbs_ cbt_)
  '(VNB-LAMBDA cbx_ (VEC cbv_) ((VADD cbw_) (cbs_ cbx_) (cbt_ cbx_))))
(def-functoid 'CBOP-ZERO '(cbv_ cbw_)
  '(VNB-LAMBDA cbx_ (VEC cbv_) (VZERO cbw_)))
(def-functoid 'CBOP-NEG '(cbv_ cbw_ cbt_)
  '(VNB-LAMBDA cbx_ (VEC cbv_) ((VNEG cbw_) (cbt_ cbx_))))
(def-functoid 'CBOP-SCALE '(cbv_ cbw_ cbc_ cbt_)
  '(VNB-LAMBDA cbx_ (VEC cbv_) ((CACT cbw_) cbc_ (cbt_ cbx_))))

(def-functoid 'CBOP-VADD '(cbv_ cbw_)
  '(VNB-LAMBDA (LIST cbs_ cbt_) (CARTESIAN (CNVS-BOUNDED-OPS cbv_ cbw_) (CNVS-BOUNDED-OPS cbv_ cbw_))
     (CBOP-SUM cbv_ cbw_ cbs_ cbt_)))
(def-functoid 'CBOP-VINV '(cbv_ cbw_)
  '(VNB-LAMBDA cbt_ (CNVS-BOUNDED-OPS cbv_ cbw_) (CBOP-NEG cbv_ cbw_ cbt_)))
(def-functoid 'CBOP-VNRM '(cbv_ cbw_)
  '(VNB-LAMBDA cbt_ (CNVS-BOUNDED-OPS cbv_ cbw_) (CNVS-OPNORM cbv_ cbw_ cbt_)))
(def-functoid 'CBOP-NORMED-AG '(cbv_ cbw_)
  '(LIST (CNVS-BOUNDED-OPS cbv_ cbw_) (CBOP-VADD cbv_ cbw_) (CBOP-ZERO cbv_ cbw_) (CBOP-VINV cbv_ cbw_)
         (CBOP-VNRM cbv_ cbw_)))

;;; ---- notation ----------------------------------------------------------------------------
(notation! 'IS-COMPLEX-NORMED-VECTOR-SPACE 'kind 'predicate 'arity 1
           'noun "complex normed vector space" 'article "a")
(notation! 'IS-COMPLEX-BANACH-SPACE 'kind 'predicate 'arity 1
           'noun "complex Banach space" 'article "a")
(notation! 'CNVS-METRIC-SPACE 'kind 'functoid 'arity 1 'english "the metric space of the normed space $1")
(notation! 'CMOD-RACT 'kind 'functoid 'arity 1 'english "the real scalar multiplication of the complex module $1")
(notation! 'CMOD-J 'kind 'functoid 'arity 1 'english "multiplication by i on $1")
(notation! 'IS-CMOD-NORM 'kind 'predicate 'arity 2 'english "$2 is a norm on the complex module $1")
(notation! 'CMOD-NVS 'kind 'functoid 'arity 2 'english "the real normed space underlying the complex module $1 with norm $2")
(notation! 'CMOD-CNVS 'kind 'functoid 'arity 2 'english "the complex module $1 with norm $2, as a real space with complex structure")
(notation! 'CIPS-VNRM 'kind 'functoid 'arity 1 'english "the norm of the inner product space $1")
(notation! 'CIPS-CNVS 'kind 'functoid 'arity 1 'english "$1 as a complex normed vector space")
(notation! 'CSIP-CNVS 'kind 'functoid 'arity 1 'english "$1 as a complex normed vector space")
(notation! 'IS-CNVS-LINEAR-OP 'kind 'predicate 'arity 3 'english "$3 is a complex-linear map from $1 to $2")
(notation! 'IS-CNVS-BOUNDED-OP 'kind 'predicate 'arity 3 'english "$3 is a bounded operator from $1 to $2")
(notation! 'CNVS-BOUNDED-OPS 'kind 'functoid 'arity 2 'english "the bounded operators from $1 to $2")
(notation! 'CNVS-OPNORM 'kind 'functoid 'arity 3 'english "the operator norm of $3")
(notation! 'CBOP-NORMED-AG 'kind 'functoid 'arity 2
           'english "the normed group of bounded operators from $1 to $2")
