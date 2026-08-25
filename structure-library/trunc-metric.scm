;;; trunc-metric.scm -- the TRUNCATED METRIC  d'(x,y) = min(1, d(x,y))  of a
;;; metric space, as an ENDOFUNCTOR of METRIC-SPACE.
;;;
;;;     TRUNC-METRIC(s) = (PTS(s),  d'),   d'(u,v) = min(1, d(u,v)).
;;;
;;; WHY min(1,.) AND NOT d/(1+d).  The tree already carries the other bounded
;;; transform, BDD-METRIC (structure-library/bounded-metric.scm).  The two are
;;; not interchangeable, and the argument is the one c-metric-space.scm's header
;;; makes at length: min(1,.) is TOTAL on RR, its laws are PROVEN
;;; (theorem-library/rr-min-basics.scm, and rr-min-one-subadditive there is
;;; exactly the triangle inequality for the truncation), and it introduces no
;;; `recip', which `crs' declines on.  BDD-METRIC's five facts are all asserted
;;; supports and its equivalence claim (bdd-metric-id-bicontinuous) is only
;;; TOPOLOGICAL.  Everything here is PROVEN and the equivalence is UNIFORM.
;;;
;;; AND THE MATHEMATICS DIFFERS, not only the bookkeeping.  d and d/(1+d) are
;;; uniformly equivalent as it happens, but a general bounded transform need not
;;; be; min(1,.) is uniformly equivalent for a reason that is one line long and
;;; is the point of the construction:  d' < 1  FORCES  d' = d.  So a delta below
;;; 1 transports an estimate back across the truncation unchanged, with no
;;; inverse function and no continuity of one.  See
;;; theorem-library/trunc-metric-proof.scm.
;;;
;;; WHY A CONSTRUCTED FUNCTOR AND NOT A BARE `def-functoid'.  TRUNC-METRIC maps
;;; METRIC-SPACE to METRIC-SPACE, and its object map is a BUILT term (the
;;; distance is computed from DIST, not selected from a slot), which is exactly
;;; what `def-constructed-functor' is for.  Two things come of that and neither
;;; is a convenience:
;;;
;;;   * The PROJECTIONS are precomputed, so `(slot 'PTS)' answers
;;;     PTS(TRUNC-METRIC s) = PTS(s) and `(slot 'DIST)' answers the distance
;;;     lambda, and the underlying TUPLE never enters a goal.  Reaching them by
;;;     hand means firing the accessor macete, which rewrites EVERY occurrence
;;;     -- including the (PTS s) inside the tuple -- and collapses the goal to
;;;     NTH form that no support matches (structures.scm,
;;;     install-functor-projections!, records this as a trap and not a chore).
;;;   * It ASSERTS NOTHING.  The constructor records two obligations,
;;;     trunc-metric-is-metric-space and trunc-metric-functorial, and
;;;     `functor-obligation-audit' lists any still owed at every load.  The
;;;     first is discharged in theorem-library/trunc-metric-proof.scm, modulo 0.
;;;     The second -- an isometry stays an isometry after truncation -- is OPEN
;;;     and deliberately so; `(functor-obligation 'trunc-metric-functorial)'
;;;     returns its statement, ready for `sp'.
;;;
;;; The distance lambda binds its two points `u, v' and not `x, y', following
;;; bounded-metric.scm: the point-set accessor was `X' when that convention was
;;; set, and although it is `PTS' now the names are kept so that the two
;;; constructions read the same.  [[feedback_no_case_variant_binders]]
;;;
;;; Dependencies: metric-space.scm (METRIC-SPACE, PTS, DIST) and the `min' head
;;; of number-systems.scm.  Nothing here needs IS-CONTINUOUS: the uniform
;;; equivalence is stated and proved in the theorem file.

(def-constructed-functor 'TRUNC-METRIC 'METRIC-SPACE 'METRIC-SPACE '(s)
  '(LIST (PTS s)
         (VNB-LAMBDA (LIST u v) (CARTESIAN (PTS s) (PTS s))
           (min 1 ((DIST s) u v)))))

(notation! 'TRUNC-METRIC 'kind 'functoid 'arity 1
           'english "the truncated metric space of $1")
