;;; mink-vocab.scm -- absorbing and symmetric sets, the Minkowski functional (topological-vector-space.pdf
;;; section 3.3, Def 2.28).  Vocabulary only.  Agent DUAL-FIX, 2026-10-26 (NEW DEFINITIONS, the user's to
;;; confirm; added under the rule "missing vocabulary is not a stopping point").
;;; DESTINATION: structure-library/minkowski-functional.scm.  Library: analysis.
;;; Load window: after the INF vocabulary (RA-BASICS, scratchpad/rabasics/rabasics-vocab.scm).
;;;
;;; m is a module whose scalars are the reals (SCAL m = the ring view of RR-NORMED-FIELD, as in
;;; hbs-hahn-banach-sublinear); "x in r.V" is written (exists y in V) x = r.y.
;;;
;;;   IS-ABSORBING-SUBSET(m, cs)   cs is a set of vectors and every vector x is in r.cs for some r > 0
;;;   IS-SYMMETRIC-SUBSET(m, cs)   cs is a set of vectors and (-1).y is in cs for every y in cs
;;;                                (the notes' V = -V; -V = (-1).V in a real vector space)
;;;   MINK-SET(m, cs, x)           { r in RR : r > 0 and x in r.cs }
;;;   MINKOWSKI-FUNCTIONAL(m, cs)  x |-> INF(MINK-SET(m, cs, x)) on VEC m      (the notes' p_V)

(def-predicate 'IS-ABSORBING-SUBSET '(m cs)
  '(AND (SUBSET cs (VEC m))
        (FORALL abx_ (IMPLIES (IN abx_ (VEC m))
          (FORSOME abr_ (AND (IN abr_ RR) (AND (< 0 abr_)
            (FORSOME aby_ (AND (IN aby_ cs) (= abx_ ((ACT m) abr_ aby_)))))))))))

(def-predicate 'IS-SYMMETRIC-SUBSET '(m cs)
  '(AND (SUBSET cs (VEC m))
        (FORALL syx_ (IMPLIES (IN syx_ cs) (IN ((ACT m) (- 1) syx_) cs)))))

(def-functoid 'MINK-SET '(m cs x)
  '(SEP mkr_ RR (AND (< 0 mkr_) (FORSOME mky_ (AND (IN mky_ cs) (= x ((ACT m) mkr_ mky_)))))))

(def-functoid 'MINKOWSKI-FUNCTIONAL '(m cs)
  '(VNB-LAMBDA mkx_ (VEC m) (INF (MINK-SET m cs mkx_))))

(notation! 'IS-ABSORBING-SUBSET 'kind 'predicate 'arity 2
           'english "$2 is an absorbing subset of $1")
(notation! 'IS-SYMMETRIC-SUBSET 'kind 'predicate 'arity 2
           'english "$2 is a symmetric subset of $1")
(notation! 'MINK-SET 'kind 'functoid 'arity 3
           'english "the positive reals r with $3 in r times $2")
(notation! 'MINKOWSKI-FUNCTIONAL 'kind 'functoid 'arity 2
           'english "the Minkowski functional of $2 in $1"
           'tex "p_{$2}")
