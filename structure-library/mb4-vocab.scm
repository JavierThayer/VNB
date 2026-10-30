;;; mb4-vocab.scm -- vocabulary for construction of measures, chapter 5 (M-B4, 2026-10-26).
;;; Destination: structure-library/.  Library: measure (DIAM and IS-POLISH use only metric-space and
;;; extended-real vocabulary; they could sit in analysis).
;;;
;;;   DIAM(s, a)   the diameter of a subset a of a metric space s: the supremum in [0, +inf] of the distances
;;;                d(x, y), x, y in a (0 for the empty set, +inf for an unbounded set)
;;;   IS-POLISH(s) Definition 5.13: s is a complete separable metric space
;;;
;;; Load window: after structure-library/extended-reals-pos (ESUP), separable.scm (IS-SEPARABLE) and the
;;; completeness vocabulary (IS-COMPLETE).
;;; DIAM: DELETED here 2026-10-27 (integration; one definition per notion).  The definition kept is
;;; M-H's, structure-library/hausdorff-vocab.scm (loaded before this file): the same body up to the
;;; names of the binders.
(def-predicate 'IS-POLISH '(s)
  '(AND (IS-COMPLETE s) (IS-SEPARABLE s)))
(notation! 'IS-POLISH 'kind 'predicate 'arity 1 'english "$1 is a Polish space")
;;;   GRAPH-MS(s, a, g)  for a subset a of a metric space s and a real function g on a: the points of a with
;;;                  the distance d(x, y) + |g(x) - g(y)|, the distance the graph of g inherits from s x R
;;;                  (the sum metric).  It carries the notes' proof of Lemma 5.18 (an open set U of a Polish
;;;                  space is Polish, through the graph of x |-> 1 / d(x, X \ U)).
(def-functoid 'GRAPH-MS '(s a g)
  '(LIST a (VNB-LAMBDA (LIST gmu_ gmv_) (CARTESIAN a a) (+ ((DIST s) gmu_ gmv_) (ABS (- (g gmu_) (g gmv_)))))))
(notation! 'GRAPH-MS 'kind 'functoid 'arity 3 'english "the graph space of $3 over $2 in $1")
