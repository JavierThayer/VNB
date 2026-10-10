;;; lebesgue-translate.scm -- the TRANSLATE of a set of reals.  Vocabulary only: no
;;; proof, no support.  Agent MEASURE-4-A, 2026-10-10 (scratchpad/triage/MEASURE-4-A.md).
;;; The proofs that use it are theorem-library/lebesgue-measure-unique.scm.
;;;
;;; WHAT AND WHY.
;;;
;;;   * TRANSLATE(es, c) -- the translate es + c = { x + c : x in es } of a set of
;;;     reals es by c.  It is written as a separation over RR,
;;;
;;;         TRANSLATE(es, c) = { z in RR : z - c in es },
;;;
;;;     not as the image of es under x |-> x + c: the separation needs no function
;;;     term, its membership is read off by one `sep-me', and it is the form in which
;;;     MEASURE-3 proved the translation invariance of Lebesgue outer measure
;;;     (lebesgue-outer-translate, theorem-library/lebesgue-interval-length.scm),
;;;     whose statement is TRANSLATE(es, c) unfolded, binder for binder.  For es a set
;;;     of reals and c real the two descriptions agree; for es not a set of reals the
;;;     separation keeps only the real points z with z - c in es.
;;;
;;; The binder `ltz_' is the one lebesgue-outer-translate uses, so that unfolding
;;; TRANSLATE produces that statement literally.  The parameter is `es', not `E'
;;; (case folding: E and e are one symbol).
;;; ====================================================================

(def-functoid 'TRANSLATE '(es c)
  '(SEP ltz_ RR (IN (- ltz_ c) es)))

(notation! 'TRANSLATE 'kind 'functoid 'arity 2
           'english "the translate of the set of reals $1 by $2"
           'tex "($1 + $2)")
