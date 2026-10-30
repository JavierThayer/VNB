;;; tkr-vocab.scm -- closed sets of a topological space and the kernel of a functional (for
;;; topological-vector-space.pdf Prop 2.11).  Vocabulary only.  Agent DUAL-FIX, 2026-10-26 (NEW DEFINITIONS,
;;; the user's to confirm).  DESTINATION: structure-library/top-closed.scm.  Library: analysis.
;;; Load window: after structure-library/top-space and set-vocabulary (COMPLEMENT-IN).
;;;
;;;   IS-TOP-CLOSED(t, a)   a is a set of points of t whose complement in PTS(t) is open
;;;                         (the metric IS-CLOSED of metric-open-sets.scm is for metric spaces only)
;;;   FKER(m, f)            { z in VEC m : f(z) = 0 }, the hyperplane f^-1(0) of the notes

(def-predicate 'IS-TOP-CLOSED '(t a)
  '(AND (SUBSET a (PTS t)) (IN (COMPLEMENT-IN (PTS t) a) (OPENS t))))

(def-functoid 'FKER '(m f)
  '(SEP fkz_ (VEC m) (= (f fkz_) 0)))

(notation! 'IS-TOP-CLOSED 'kind 'predicate 'arity 2
           'english "$2 is closed in $1")
(notation! 'FKER 'kind 'functoid 'arity 2
           'english "the kernel of $2 on $1")
