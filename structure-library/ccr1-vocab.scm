;;; ccr1-vocab.scm -- ULTRAMETRIC SPACES (CCR.pdf, chapter 1, Definition 1.1 and the objects of
;;; Propositions 1.3-1.7).  DEFINITIONS ONLY; the laws are in theorem-library/ccr1-ultrametric.scm.
;;; Agent CCR-B1, wave MAP-1026, 2026-10-26.  Destination: structure-library/ccr1-vocab.scm.
;;; Library: analysis.  Load window: after structure-library/metric-topology (BALL, CLOSED-BALL),
;;; structure-library/setoid (SETOID, QUOTIENT) and the file defining IS-ULTRAMETRIC.
;;;
;;; IS-ULTRAMETRIC(s) (Definition 1.1) is NOT defined here: it is agent ISOM's definition in
;;; scratchpad/mb12/mb12-vocab.scm (the measures bundle B2, the prefix ultrametric on X^N), reused as is:
;;;     s is a metric space and d(x, y) <= max(d(x, z), d(z, y)) for all x, y, z in PTS(s).
;;;
;;;   SPHERE(s, c, r)    the notes' {x in X : d(x, a) = r} (Corollary 1.4), written with the centre first as
;;;                      BALL and CLOSED-BALL are: {y in PTS(s) : d(c, y) = r}.
;;;   EPS-REL(s, e)      the relation x ~e y iff d(x, y) < e (Proposition 1.5), as a set of pairs.
;;;   EPS-SETOID(s, e)   (PTS(s), EPS-REL(s, e)) as a SETOID; its QUOTIENT is the set of ~e classes
;;;                      (Proposition 1.7).
;;; Binders cuv*_.

(def-functoid 'SPHERE '(cuvs_ cuvc_ cuvr_)
  '(SEP cuvy_ (PTS cuvs_) (= ((DIST cuvs_) cuvc_ cuvy_) cuvr_)))
(notation! 'SPHERE 'kind 'functoid 'arity 3 'english "the sphere of $1 with centre $2 and radius $3")

(def-functoid 'EPS-REL '(cuvs_ cuve_)
  '(SEP cuvp_ (CARTESIAN (PTS cuvs_) (PTS cuvs_)) (< ((DIST cuvs_) (NTH 1 cuvp_) (NTH 2 cuvp_)) cuve_)))
(notation! 'EPS-REL 'kind 'functoid 'arity 2 'english "the relation d(x, y) < $2 on $1")

(def-functoid 'EPS-SETOID '(cuvs_ cuve_)
  '(LIST (PTS cuvs_) (EPS-REL cuvs_ cuve_)))
(notation! 'EPS-SETOID 'kind 'functoid 'arity 2 'english "the points of $1 under the relation d(x, y) < $2")
