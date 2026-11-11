;;; ccr4c-subnf-vocab.scm -- wave of 2026-11-09/10 (agent CCR-1109-C4), wired 2026-11-10 from scratchpad/ccr1109c4/ccr4c-subnf-vocab.scm.
;;; Library: analysis.

;;; ccr4c-subnf-vocab.scm -- THE RESTRICTION OF A NORMED FIELD TO A SUBFIELD (CCR-1109-C3 finding F2).
;;; DEFINITIONS ONLY; the laws are in theorem-library/ccr4c-subnf.scm.  Agent CCR-1109-C4, 2026-11-09.
;;; Destination: structure-library/ccr4c-subnf-vocab.scm.  Library: analysis (a NORMED-FIELD 7-tuple).
;;; Load window: after structure-library/normed-field (the 7-slot shape); it names no other vocabulary.
;;;
;;;   SUB-NF(K, S)    the normed field S with the operations, constants and absolute value of K restricted to S;
;;;                   a NORMED-FIELD 7-tuple, a normed field whenever S is a subfield of K (sub-nf-is-normed-field)
;;; Binders sn*_.

(def-functoid 'SUB-NF '(snk_ sns_)
  '(LIST sns_
         (VNB-LAMBDA (LIST snu_ snv_) (CARTESIAN sns_ sns_) ((ADD snk_) snu_ snv_))
         (VNB-LAMBDA (LIST snu_ snv_) (CARTESIAN sns_ sns_) ((MUL snk_) snu_ snv_))
         (VNB-LAMBDA snu_ sns_ ((NEG snk_) snu_))
         (ZERO snk_) (ONE snk_)
         (VNB-LAMBDA snu_ sns_ ((FNRM snk_) snu_))))
(notation! 'SUB-NF 'kind 'functoid 'arity 2 'english "the normed field $2 with the structure of $1 restricted to it")
