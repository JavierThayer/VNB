;;; bidual-vocab.scm -- THE CANONICAL MAP OF A NORMED SPACE INTO ITS BIDUAL.  Vocabulary only.
;;; Agent DUAL-FIX, 2026-10-26.  DESTINATION: structure-library/bidual.scm.  Library: analysis.
;;; Load window: after structure-library/dual-space.
;;;
;;;   BIDUAL-EVAL(m, x) = (f |-> f(x)) on DUAL-VEC(m): the image of x under the canonical map
;;;   iota_E : E -> E** of topological-vector-space.pdf, Prop 3.31.  It is a vector of
;;;   DUAL(DUAL(m)) when m is a normed vector space (bidual-eval-in-bidual, theorem-library/
;;;   tvs-bidual.scm).

(def-functoid 'BIDUAL-EVAL '(m x)
  '(VNB-LAMBDA bdef_ (DUAL-VEC m) (bdef_ x)))

(notation! 'BIDUAL-EVAL 'kind 'functoid 'arity 2
           'english "the evaluation at $2 of the bounded linear functionals on $1"
           'tex "\\iota_{$1}({$2})")
