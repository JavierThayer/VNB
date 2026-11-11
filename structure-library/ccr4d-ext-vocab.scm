;;; ccr4d-ext-vocab.scm -- wave of 2026-11-09/10 (agent CCR-1109-C5), wired 2026-11-10 from scratchpad/ccr1109c5/ccr4d-ext-vocab.scm.
;;; Library: analysis.

;;; ccr4d-ext-vocab.scm -- A NORMED FIELD AS A MODULE OVER A SUBFIELD: the module structure that CCR-1109-C2's
;;; IS-FIN-EXT asks for when the extension is K itself and the base field is SUB-NF(K, S) (CCR 4.24, 4.27).
;;; DEFINITIONS ONLY; the laws are in theorem-library/ccr4d-ext.scm.  Agent CCR-1109-C5, 2026-11-10.
;;; Destination: structure-library/ccr4d-ext-vocab.scm.  Library: analysis (SUB-NF, the ring view of a normed
;;; field).  Load window: after structure-library/ccr4c-subnf-vocab (SUB-NF) and structure-library/normed-field.
;;;
;;;   NF-SUBFIELD-MODULE(K, S)   the MODULE 6-tuple [V, CARR F, ADD F, ZERO F, NEG F, ACT], where F is the ring
;;;                              view of K, V the ring view of SUB-NF(K, S), and ACT(r, x) = r x for r in S,
;;;                              x in K.  A module over V whenever S is a subfield (nf-subfield-module-is-module).
;;; Binders fm*_.

(def-functoid 'NF-SUBFIELD-MODULE '(fmk_ fms_)
  '(LIST (NORMED-FIELD-AS-COMMUTATIVE-RING (SUB-NF fmk_ fms_))
         (CARR (NORMED-FIELD-AS-COMMUTATIVE-RING fmk_))
         (ADD (NORMED-FIELD-AS-COMMUTATIVE-RING fmk_))
         (ZERO (NORMED-FIELD-AS-COMMUTATIVE-RING fmk_))
         (NEG (NORMED-FIELD-AS-COMMUTATIVE-RING fmk_))
         (VNB-LAMBDA (LIST fmr_ fmx_) (CARTESIAN fms_ (CARR (NORMED-FIELD-AS-COMMUTATIVE-RING fmk_)))
           ((MUL (NORMED-FIELD-AS-COMMUTATIVE-RING fmk_)) fmr_ fmx_))))
(notation! 'NF-SUBFIELD-MODULE 'kind 'functoid 'arity 2 'english "$1 as a module over its subfield $2")
