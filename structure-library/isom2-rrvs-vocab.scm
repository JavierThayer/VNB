;;; isom2-rrvs-vocab.scm -- the real numbers as a FIELD instance, the vector space of
;;; real functions on RR in a set closed under the pointwise operations, and the set of
;;; antiderivable functions on [a, b] (calculus.pdf Prop 4.8).  DEFINITIONS ONLY; laws in
;;; theorem-library/isom2-rrfield.scm and isom2-rrvs.scm.  Agent ISOM, 2026-10-26
;;; (NEW DEFINITIONS, the user's to confirm).
;;;
;;;   RR-FIELD            the 8-tuple of FIELD (field.scm) on RR, the exact analogue of
;;;                       QQ-FIELD (numeric-instances.scm): slots 2-4 and 8 are lambdas.
;;;   RR-FN-SPACE(v)      for a set v of functions RR -> RR: the MODULE 6-tuple over the
;;;                       field ring FIELD-AS-INTEGRAL-DOMAIN(RR-FIELD) with the pointwise
;;;                       sum, the zero function, the pointwise negative and the pointwise
;;;                       scalar multiple; a vector space when v is closed under them
;;;                       (rr-fn-space-is-vector-space).  The RR analogue of CC-FN-MODULE.
;;;   ANTIDERIVABLE-FNS(a, b)
;;;                       { phi in FUN(RR, RR) : IS-ANTIDERIVABLE(phi, a, b) }.
;;;
;;; IS-ANTIDERIVABLE unfolds to IS-ANTIDERIVATIVE, IS-CONTINUOUS-AT and IS-DIFF-AT only:
;;; none of CLOSURE, INTERIOR, INTEGRAL, DESCEND, ZEN/ZUP or a J- head.
;;;
;;; BINDERS: x_ y_ (as in QQ-FIELD), rfv_ rff_ rfg_ rfx_ rfc_, ada_ adb_ adp_.

(declare-instance! 'RR-FIELD 'FIELD 'rr-field-def
  '(RR (VNB-LAMBDA (LIST x_ y_) (CARTESIAN RR RR) (+ x_ y_))
       (VNB-LAMBDA (LIST x_ y_) (CARTESIAN RR RR) (* x_ y_))
       (VNB-LAMBDA x_ RR (- x_))
       0 1
       (DIFFERENCE RR (SINGLETON 0))
       (VNB-LAMBDA x_ (DIFFERENCE RR (SINGLETON 0)) (recip x_))))

(def-functoid 'RR-FN-SPACE '(rfv_)
  '(LIST (FIELD-AS-INTEGRAL-DOMAIN RR-FIELD)
         rfv_
         (VNB-LAMBDA (LIST rff_ rfg_) (CARTESIAN rfv_ rfv_) (VNB-LAMBDA rfx_ RR (+ (rff_ rfx_) (rfg_ rfx_))))
         (VNB-LAMBDA rfx_ RR 0)
         (VNB-LAMBDA rff_ rfv_ (VNB-LAMBDA rfx_ RR (- (rff_ rfx_))))
         (VNB-LAMBDA (LIST rfc_ rff_) (CARTESIAN RR rfv_) (VNB-LAMBDA rfx_ RR (* rfc_ (rff_ rfx_))))))

(notation! 'RR-FN-SPACE 'kind 'functoid 'arity 1
           'english "the real vector space of the functions in $1 under the pointwise operations")

(def-functoid 'ANTIDERIVABLE-FNS '(ada_ adb_)
  '(SEP adp_ (FUN RR RR) (IS-ANTIDERIVABLE adp_ ada_ adb_)))

(notation! 'ANTIDERIVABLE-FNS 'kind 'functoid 'arity 2
           'english "the set of functions antiderivable on [$1, $2]")
