;;; hc-vocab.scm -- THE HILBERT COMPLETION OF A PRE-HILBERT SPACE, CONCRETELY: the Cauchy sequences
;;; of the space as a module with pointwise operations, the limit form on them, and the quotient by
;;; its null space.  Agent BA-1111-A2, 2026-11-11.  Destination: structure-library/hc-vocab.scm.
;;; Library: analysis.  DEFINITIONS ONLY: no proof, no support, no axiom.
;;;
;;; THE INPUT.  A pre-Hilbert space is given as a pair (md, fq): md a module over CC (IS-MODULE md,
;;; SCAL(md) = the CC ring view) and fq an inner product form on it (IS-INNER-PRODUCT-FORM md fq,
;;; ipf-vocab.scm); the space itself is MODULE-WITH-FORM(md, fq), a complex inner product space
;;; (cips-of-inner-product-form).  This is the shape GNS produces: FORM-QUOTIENT(m, f) =
;;; MODULE-WITH-FORM(QUOTIENT-MODULE(..), FORM-QIP(..)), with form-quotient-inner-product-form.
;;;
;;;   FORM-MS(md, fq)          the metric space of the pre-Hilbert space: IP-METRIC-SPACE of
;;;                            MODULE-WITH-FORM(md, fq); points VEC(md), d(x, y) = sqrt(fq(x-y, x-y)).
;;;   FORM-CSEQ(md, fq)        its Cauchy sequences, CSEQ(FORM-MS(md, fq)) (metric-completion.scm).
;;;   SEQ-VADD / SEQ-VNEG / SEQ-ACT / SEQ-ZERO     the pointwise operations on sequences in VEC(md).
;;;   SEQ-FORM(fq, f, g)       the complex sequence n |-> fq(f(n), g(n)).
;;;   CSEQ-MODULE(md, fq)      the module of the Cauchy sequences, with the pointwise operations.
;;;   LIMIT-FORM(md, fq)       the form (f, g) |-> lim fq(f(n), g(n)) on the Cauchy sequences (the limit
;;;                            exists and is unique: CC is complete and the sequence is Cauchy).
;;;   HILBERT-COMPLETION(md, fq)  FORM-QUOTIENT(CSEQ-MODULE(md, fq), LIMIT-FORM(md, fq)): the Cauchy
;;;                            sequences modulo those of limit norm 0, with the induced inner product.
;;;   HC-EMBED(md, fq)         x |-> the class of the constant sequence x: VEC(md) -> the completion.
;;;
;;; Binders hc*_ (hcf_ hcg_ hcn_ hca_ hcc_ hcx_), used by no other file.
;;; LOAD WINDOW: after structure-library/ipf-vocab, structure-library/metric-completion,
;;; structure-library/hilbert-space (IP-METRIC-SPACE), structure-library/complex (CC-MS).

(def-functoid 'FORM-MS '(md fq) '(IP-METRIC-SPACE (MODULE-WITH-FORM md fq)))
(def-functoid 'FORM-CSEQ '(md fq) '(CSEQ (FORM-MS md fq)))

(def-functoid 'SEQ-VADD '(md f g) '(VNB-LAMBDA hcn_ NN ((VADD md) (f hcn_) (g hcn_))))
(def-functoid 'SEQ-VNEG '(md f) '(VNB-LAMBDA hcn_ NN ((VNEG md) (f hcn_))))
(def-functoid 'SEQ-ACT '(md a f) '(VNB-LAMBDA hcn_ NN ((ACT md) a (f hcn_))))
(def-functoid 'SEQ-ZERO '(md) '(VNB-LAMBDA hcn_ NN (VZERO md)))
(def-functoid 'SEQ-FORM '(fq f g) '(VNB-LAMBDA hcn_ NN (fq (f hcn_) (g hcn_))))

(def-functoid 'CSEQ-MODULE '(md fq)
  '(LIST (SCAL md) (FORM-CSEQ md fq)
         (VNB-LAMBDA (LIST hcf_ hcg_) (CARTESIAN (FORM-CSEQ md fq) (FORM-CSEQ md fq)) (SEQ-VADD md hcf_ hcg_))
         (SEQ-ZERO md)
         (VNB-LAMBDA hcf_ (FORM-CSEQ md fq) (SEQ-VNEG md hcf_))
         (VNB-LAMBDA (LIST hca_ hcf_) (CARTESIAN CC (FORM-CSEQ md fq)) (SEQ-ACT md hca_ hcf_))))

(def-functoid 'LIMIT-FORM '(md fq)
  '(VNB-LAMBDA (LIST hcf_ hcg_) (CARTESIAN (FORM-CSEQ md fq) (FORM-CSEQ md fq))
     (IOTA hcc_ (AND (IN hcc_ CC) (CONVERGES-TO CC-MS (SEQ-FORM fq hcf_ hcg_) hcc_)))))

(def-functoid 'HILBERT-COMPLETION '(md fq)
  '(FORM-QUOTIENT (CSEQ-MODULE md fq) (LIMIT-FORM md fq)))

(def-functoid 'HC-EMBED '(md fq)
  '(VNB-LAMBDA hcx_ (VEC md)
     (CLASS (QMOD-SETOID (CSEQ-MODULE md fq) (FORM-NULL (CSEQ-MODULE md fq) (LIMIT-FORM md fq)))
            (EMBED-SEQ (FORM-MS md fq) hcx_))))

(notation! 'FORM-MS 'kind 'functoid 'arity 2 'english "the metric space of the inner product $2 on $1")
(notation! 'FORM-CSEQ 'kind 'functoid 'arity 2 'english "the Cauchy sequences of the inner product space ($1, $2)")
(notation! 'SEQ-VADD 'kind 'functoid 'arity 3 'english "the pointwise sum of the sequences $2 and $3 in $1")
(notation! 'SEQ-VNEG 'kind 'functoid 'arity 2 'english "the pointwise negative of the sequence $2 in $1")
(notation! 'SEQ-ACT 'kind 'functoid 'arity 3 'english "the pointwise multiple of the sequence $3 by $2 in $1")
(notation! 'SEQ-ZERO 'kind 'functoid 'arity 1 'english "the zero sequence of $1")
(notation! 'SEQ-FORM 'kind 'functoid 'arity 3 'english "the sequence of the values of $1 at the terms of $2 and $3")
(notation! 'CSEQ-MODULE 'kind 'functoid 'arity 2 'english "the module of the Cauchy sequences of ($1, $2)")
(notation! 'LIMIT-FORM 'kind 'functoid 'arity 2 'english "the limit of the inner products of two Cauchy sequences of ($1, $2)")
(notation! 'HILBERT-COMPLETION 'kind 'functoid 'arity 2 'english "the Hilbert completion of the inner product space ($1, $2)")
(notation! 'HC-EMBED 'kind 'functoid 'arity 2 'english "the embedding of ($1, $2) in its Hilbert completion")
