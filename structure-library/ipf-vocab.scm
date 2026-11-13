;;; ipf-vocab.scm -- INNER PRODUCT FORMS ON A COMPLEX MODULE, the module carrying such a form, and the
;;; quotient of a module by the null space of a positive semi-definite form.  Agent BA-1111-A2,
;;; 2026-11-11.  Destination: structure-library/ipf-vocab.scm.  Library: analysis.
;;; DEFINITIONS ONLY: no proof, no support, no axiom.
;;;
;;; A module m over the complex numbers is an IS-MODULE m with SCAL(m) = the ring view of
;;; CC-NORMED-FIELD (the pinning of COMPLEX-INNER-PRODUCT-SPACE, complex-inner-product.scm).
;;; A form on m is a function f in FUN(VEC m x VEC m, CC), applied as f(x, y).
;;;
;;;   IS-HERMITIAN-FORM(m, f)      f is additive and homogeneous in the first argument and
;;;                                conjugate symmetric: the sesquilinear hermitian forms.
;;;   IS-PSD-FORM(m, f)            hermitian, with f(x, x) real and >= 0 (positive semi-definite).
;;;   IS-INNER-PRODUCT-FORM(m, f)  positive semi-definite, and f(x, x) = 0 only at the zero vector.
;;;   MODULE-WITH-FORM(m, f)       the seven-tuple [SCAL m, VEC m, VADD m, VZERO m, VNEG m, ACT m, f]
;;;                                in COMPLEX-INNER-PRODUCT-SPACE's layout.  It is a complex inner
;;;                                product space when m is a module over CC and f an inner
;;;                                product form (theorem cips-of-inner-product-form).
;;;   FORM-NULL(m, f)              { x in VEC m : f(x, x) = 0 }, the null space of a form.
;;;   FORM-QIP(m, f)               the form induced on the classes modulo FORM-NULL(m, f):
;;;                                DESCEND2 of f on QMOD-SETOID(m, FORM-NULL(m, f)).
;;;   FORM-QUOTIENT(m, f)          the quotient module m / FORM-NULL(m, f) (la-z3-vocab's
;;;                                QUOTIENT-MODULE) with the induced form: the pre-Hilbert space
;;;                                of a positive semi-definite form (theorem form-quotient-is-cips),
;;;                                the step GNS takes before completing.
;;;
;;; The laws are stated in exactly the shape of the corresponding conjuncts of
;;; IS-COMPLEX-INNER-PRODUCT-SPACE, so that an unfolded instance is closed conjunct by conjunct.
;;; Binders ipf*_ (ipfx_ ipfy_ ipfz_ ipfa_), used by no other file.
;;; LOAD WINDOW: after structure-library/complex-inner-product and structure-library/la-z3-vocab
;;; (QUOTIENT-MODULE, QMOD-SETOID).

(def-predicate 'IS-HERMITIAN-FORM '(ipfm_ ipff_)
  '(AND (IN ipff_ (FUN (CARTESIAN (VEC ipfm_) (VEC ipfm_)) CC))
   (AND (FORALL ipfx_ (IMPLIES (IN ipfx_ (VEC ipfm_)) (FORALL ipfy_ (IMPLIES (IN ipfy_ (VEC ipfm_)) (FORALL ipfz_ (IMPLIES (IN ipfz_ (VEC ipfm_)) (= (ipff_ ((VADD ipfm_) ipfx_ ipfy_) ipfz_) (+ (ipff_ ipfx_ ipfz_) (ipff_ ipfy_ ipfz_)))))))))
   (AND (FORALL ipfa_ (IMPLIES (IN ipfa_ CC) (FORALL ipfx_ (IMPLIES (IN ipfx_ (VEC ipfm_)) (FORALL ipfy_ (IMPLIES (IN ipfy_ (VEC ipfm_)) (= (ipff_ ((ACT ipfm_) ipfa_ ipfx_) ipfy_) (* ipfa_ (ipff_ ipfx_ ipfy_)))))))))
        (FORALL ipfx_ (IMPLIES (IN ipfx_ (VEC ipfm_)) (FORALL ipfy_ (IMPLIES (IN ipfy_ (VEC ipfm_)) (= (ipff_ ipfy_ ipfx_) (conjugate (ipff_ ipfx_ ipfy_)))))))))))

(def-predicate 'IS-PSD-FORM '(ipfm_ ipff_)
  '(AND (IS-HERMITIAN-FORM ipfm_ ipff_)
   (AND (FORALL ipfx_ (IMPLIES (IN ipfx_ (VEC ipfm_)) (IN (ipff_ ipfx_ ipfx_) RR)))
        (FORALL ipfx_ (IMPLIES (IN ipfx_ (VEC ipfm_)) (<= 0 (ipff_ ipfx_ ipfx_)))))))

(def-predicate 'IS-INNER-PRODUCT-FORM '(ipfm_ ipff_)
  '(AND (IS-PSD-FORM ipfm_ ipff_)
        (FORALL ipfx_ (IMPLIES (IN ipfx_ (VEC ipfm_))
          (IMPLIES (= (ipff_ ipfx_ ipfx_) 0) (= ipfx_ (VZERO ipfm_)))))))

(def-functoid 'MODULE-WITH-FORM '(ipfm_ ipff_)
  '(LIST (SCAL ipfm_) (VEC ipfm_) (VADD ipfm_) (VZERO ipfm_) (VNEG ipfm_) (ACT ipfm_) ipff_))

(def-functoid 'FORM-NULL '(ipfm_ ipff_)
  '(SEP ipfx_ (VEC ipfm_) (= (ipff_ ipfx_ ipfx_) 0)))

(def-functoid 'FORM-QIP '(ipfm_ ipff_)
  '(DESCEND2 (QMOD-SETOID ipfm_ (FORM-NULL ipfm_ ipff_)) ipff_))

(def-functoid 'FORM-QUOTIENT '(ipfm_ ipff_)
  '(MODULE-WITH-FORM (QUOTIENT-MODULE ipfm_ (FORM-NULL ipfm_ ipff_)) (FORM-QIP ipfm_ ipff_)))

(notation! 'IS-HERMITIAN-FORM 'kind 'predicate 'arity 2 'english "$2 is a hermitian sesquilinear form on $1")
(notation! 'IS-PSD-FORM 'kind 'predicate 'arity 2 'english "$2 is a positive semi-definite hermitian form on $1")
(notation! 'IS-INNER-PRODUCT-FORM 'kind 'predicate 'arity 2 'english "$2 is an inner product on $1")
(notation! 'MODULE-WITH-FORM 'kind 'functoid 'arity 2 'english "$1 with the inner product $2" 'tex "({$1}, {$2})")
(notation! 'FORM-NULL 'kind 'functoid 'arity 2 'english "the null space of the form $2" 'tex "N_{$2}")
(notation! 'FORM-QIP 'kind 'functoid 'arity 2 'english "the form induced by $2 on the quotient by its null space")
(notation! 'FORM-QUOTIENT 'kind 'functoid 'arity 2 'english "the quotient of $1 by the null space of $2, with the induced inner product" 'tex "{$1}/N_{$2}")
