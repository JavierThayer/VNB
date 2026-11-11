;;; l2-families-vocab.scm -- wave of 2026-11-09/10 (agent BA-ONB2), wired 2026-11-10 from scratchpad/baonb2-1109/bo2-l2-vocab.scm.
;;; Library: analysis.

;;; bo2-l2-vocab.scm -- THE HILBERT SPACE l2(I) OF SQUARE-SUMMABLE COMPLEX FAMILIES.
;;; Vocabulary only: no proof, no support.  Agent BA-ONB2, 2026-11-09
;;; (scratchpad/triage/BA-ONB2.md, target 1).  The proofs are theorem-library/l2-families.scm
;;; (prefix `bl2-').
;;;
;;; DESTINATION: structure-library/l2-families-vocab.scm.  Library: analysis.
;;; Load window: after structure-library/complex-inner-product (the CIPS shape),
;;; structure-library/summability (SUMS-TO), structure-library/extended-sum (ESUM),
;;; structure-library/normed-ag (NORMED-AG); before theorem-library/l2-families.
;;;
;;; Source: Thayer, "Analise Funcional e Teoria Espectral" (th-main.pdf), s.2.1 (l2(I),
;;; the target of the unitary W of Prop. 2.6); BanachAlgebras.pdf s.2.1.
;;;
;;;   CC-NAG                the complex numbers as a normed abelian group: [CC, +, 0, -, |.|].
;;;                         The slots are the lambdas of CC-NORMED-FIELD (numeric-instances.scm),
;;;                         binder for binder, so NORMED-AG-AS-ABELIAN-GROUP(CC-NAG) and
;;;                         NORMED-FIELD-ADDITIVE-AG(CC-NORMED-FIELD) are the same 4-list.
;;;   CC-FAMILY-SUM(f)      the unordered sum in CC of a family f (the SUMS-TO limit in CC-NAG;
;;;                         a CHOICE, which denotes what it should once f is summable:
;;;                         sums-to-unique).
;;;   L2-FAMILIES(ix)       { c in FUN(ix, CC) : sum_i |c_i|^2 < +inf }  (the sum is ESUM).
;;;   L2-VADD, L2-VZERO, L2-VNEG, L2-ACT, L2-IP
;;;                         the pointwise operations and <a, b> = sum_i a_i conj(b_i).
;;;   L2-CIPS(ix)           the seven-tuple: l2(I) as a COMPLEX-INNER-PRODUCT-SPACE.
;;;
;;; Binders: x_ y_ in CC-NAG (those of CC-NORMED-FIELD, deliberately); csw_ (the sum); l2c_ l2k_
;;; l2a_ l2b_ l2z_ (the families), named so that nothing else binds them.

(declare-instance! 'CC-NAG 'NORMED-AG 'cc-nag-def
  '(CC (VNB-LAMBDA (LIST x_ y_) (CARTESIAN CC CC) (+ x_ y_))
       0
       (VNB-LAMBDA x_ CC (- x_))
       (VNB-LAMBDA x_ CC (magnitude x_))))

(def-functoid 'CC-FAMILY-SUM '(f)
  '(CHOICE (SEP csw_ CC (SUMS-TO CC-NAG f csw_))))

(def-functoid 'L2-FAMILIES '(ix)
  '(SEP l2c_ (FUN ix CC)
     (IN (ESUM (VNB-LAMBDA l2k_ ix (* (MAGNITUDE (l2c_ l2k_)) (MAGNITUDE (l2c_ l2k_))))) RR)))

(def-functoid 'L2F-VADD '(ix)
  '(VNB-LAMBDA (LIST l2a_ l2b_) (CARTESIAN (L2-FAMILIES ix) (L2-FAMILIES ix))
     (VNB-LAMBDA l2k_ ix (+ (l2a_ l2k_) (l2b_ l2k_)))))

(def-functoid 'L2F-VZERO '(ix)
  '(VNB-LAMBDA l2k_ ix 0))

(def-functoid 'L2F-VNEG '(ix)
  '(VNB-LAMBDA l2a_ (L2-FAMILIES ix)
     (VNB-LAMBDA l2k_ ix (- (l2a_ l2k_)))))

(def-functoid 'L2F-ACT '(ix)
  '(VNB-LAMBDA (LIST l2z_ l2a_) (CARTESIAN CC (L2-FAMILIES ix))
     (VNB-LAMBDA l2k_ ix (* l2z_ (l2a_ l2k_)))))

(def-functoid 'L2-IP '(ix)
  '(VNB-LAMBDA (LIST l2a_ l2b_) (CARTESIAN (L2-FAMILIES ix) (L2-FAMILIES ix))
     (CC-FAMILY-SUM (VNB-LAMBDA l2k_ ix (* (l2a_ l2k_) (conjugate (l2b_ l2k_)))))))

(def-functoid 'L2-CIPS '(ix)
  '(LIST (NORMED-FIELD-AS-COMMUTATIVE-RING CC-NORMED-FIELD) (L2-FAMILIES ix)
         (L2F-VADD ix) (L2F-VZERO ix) (L2F-VNEG ix) (L2F-ACT ix) (L2-IP ix)))

;;; Notation -- read by wff->english / the proof reader (operators.scm).
(notation! 'CC-FAMILY-SUM 'kind 'functoid 'arity 1
           'english "the sum in CC of the family $1")
(notation! 'L2-FAMILIES 'kind 'functoid 'arity 1
           'english "the square-summable complex families on $1")
(notation! 'L2-IP 'kind 'functoid 'arity 1
           'english "the inner product of l2($1)")
(notation! 'L2-CIPS 'kind 'functoid 'arity 1
           'english "l2($1) as a complex inner product space")
