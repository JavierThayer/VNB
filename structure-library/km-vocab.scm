;;; km-vocab.scm -- wave of 2026-11-09/10 (agent BA-KM), wired 2026-11-10 from scratchpad/bakm-1109/km-vocab.scm.
;;; Library: analysis.

;;; km-vocab.scm -- vocabulary for the Krein-Milman theorem (BanachAlgebras.pdf, used in ch. 4: Prop 4.24,
;;; Remark 4.40, Cor 4.41).  DEFINITIONS ONLY.  Agent BA-KM, 2026-11-09 (new definitions).
;;; DESTINATION: structure-library/km-vocab.scm.  Library: analysis.
;;; Load window: after structure-library/cg4-vocab (IS-EXTREME-POINT), which loads after tvs-vocab (IS-TVS),
;;; sip-hilbert-vocab (IS-CONVEX-SUBSET) and top-closed (IS-TOP-CLOSED).
;;;
;;;   IS-LOCALLY-CONVEX-TVS(m, t)   t is a locally convex topology on the REAL vector space m: a topological
;;;                     vector space over RR-NORMED-FIELD (IS-TVS, Hausdorff by definition) in which every open
;;;                     neighbourhood U of a point x contains a convex open neighbourhood V of x.
;;;   EXTREME-POINTS(m, ks)         the set of extreme points of ks (IS-EXTREME-POINT, cg4-vocab.scm).
;;;   CLOSED-CONV-HULL(m, t, e)     the closed convex hull of e: the intersection of all closed convex sets of
;;;                     vectors containing e (the least closed convex superset of e).  Its points are vectors.
;;;
;;; BINDERS: lcx_ lcu_ lcv_ kez_ khx_ khc_ (tagged; nothing else binds them).

(def-predicate 'IS-LOCALLY-CONVEX-TVS '(m t)
  '(AND (IS-TVS RR-NORMED-FIELD m t)
        (FORALL lcx_ (IMPLIES (IN lcx_ (VEC m))
          (FORALL lcu_ (IMPLIES (IN lcu_ (OPENS t)) (IMPLIES (IN lcx_ lcu_)
            (FORSOME lcv_ (AND (IN lcv_ (OPENS t))
                               (AND (IN lcx_ lcv_) (AND (SUBSET lcv_ lcu_) (IS-CONVEX-SUBSET m lcv_))))))))))))
(notation! 'IS-LOCALLY-CONVEX-TVS 'kind 'predicate 'arity 2
           'english "$2 is a locally convex vector space topology on the real vector space $1")

(def-functoid 'EXTREME-POINTS '(m ks)
  '(SEP kez_ (VEC m) (IS-EXTREME-POINT m ks kez_)))
(notation! 'EXTREME-POINTS 'kind 'functoid 'arity 2
           'english "the set of extreme points of $2 in $1")

(def-functoid 'CLOSED-CONV-HULL '(m t e)
  '(SEP khx_ (VEC m)
     (FORALL khc_ (IMPLIES (IN khc_ SET) (IMPLIES (IS-CONVEX-SUBSET m khc_) (IMPLIES (IS-TOP-CLOSED t khc_) (IMPLIES (SUBSET e khc_)
       (IN khx_ khc_))))))))
(notation! 'CLOSED-CONV-HULL 'kind 'functoid 'arity 3
           'english "the closed convex hull of $3 in $1 for the topology $2")
