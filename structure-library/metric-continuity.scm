;;; RETIRED 2026-09-17 (proven): metric-hom-is-continuous -- theorem-library/rake-analysis2.scm
;;; metric-continuity.scm -- continuous maps between metric spaces.
;;;
;;; A map f : PTS(s) -> PTS(t) between two metric spaces s (domain) and t
;;; (codomain).  Three predicates, all in the established eps/delta idiom of
;;; metric-completeness.scm (POS-RR for "> 0", <= for the estimates -- VNB
;;; has no strict <):
;;;
;;;   IS-CONTINUOUS-AT(s, t, f, a)   f is continuous at the point a in PTS(s)
;;;   IS-CONTINUOUS(s, t, f)         f is continuous at every point of PTS(s)
;;;   IS-UNIFORMLY-CONTINUOUS(s,t,f) one delta works for all points at once
;;;
;;; These are the morphisms of the metric-space "structure": IS-CONTINUOUS is
;;; exactly the IS-HOM predicate the relational generic-for-struct? wants (so
;;; a view-as can one day carry continuity theorems across -- see the
;;; functor thread).  Composition / identity / the sequential characterization
;;; (CONVERGES-TO s g a => CONVERGES-TO t (f o g) (f a)) are deliberately left
;;; for the next increment: they need a function-composition operator that the
;;; library does not yet carry, and that is a design call to make explicitly.
;;;
;;; Bound-variable hygiene: points are `a' (centre) and `b' (varying), never
;;; `x' -- `X' is the carrier accessor and the reader/MIT Scheme would risk a
;;; case-fold capture (see [[feedback-no-case-variant-binders]]).  Spaces are
;;; `s' (domain) and `t' (codomain).
;;;
;;; Dependencies: metric-space.scm (IS-METRIC-SPACE, PTS, DIST), number-systems.scm
;;; (RR, <=), order-predicates.scm (POS-RR).  Loaded right after
;;; metric-completeness.scm so the metric cluster stays together.

;;; -----------------------------------------------------------------------
;;; IS-CONTINUOUS-AT(s, t, f, a): for every eps > 0 there is a delta > 0 such
;;; that f maps the delta-ball around a into the eps-ball around f(a).

(def-predicate 'IS-CONTINUOUS-AT '(s t f a)
  '(AND (IS-METRIC-SPACE s)
   (AND (IS-METRIC-SPACE t)
   (AND (IN f (FUN (PTS s) (PTS t)))
   (AND (IN a (PTS s))
        (FORALL eps (IMPLIES (POS-RR eps)
          (FORSOME delta (AND (POS-RR delta)
            (FORALL b (IMPLIES (IN b (PTS s))
              (IMPLIES (<= ((DIST s) a b) delta)
                       (<= ((DIST t) (f a) (f b)) eps)))))))))))))

;;; -----------------------------------------------------------------------
;;; IS-CONTINUOUS(s, t, f): continuous at every point of the domain.  The
;;; typing conjuncts are hoisted to the top (like IS-CAUCHY-SEQ) so a proof
;;; can read off IS-METRIC-SPACE / f-typing without first exhibiting a point.

(def-predicate 'IS-CONTINUOUS '(s t f)
  '(AND (IS-METRIC-SPACE s)
   (AND (IS-METRIC-SPACE t)
   (AND (IN f (FUN (PTS s) (PTS t)))
        (FORALL a (IMPLIES (IN a (PTS s))
          (IS-CONTINUOUS-AT s t f a)))))))

;;; -----------------------------------------------------------------------
;;; IS-UNIFORMLY-CONTINUOUS(s, t, f): the delta is chosen before the point --
;;; one delta works uniformly across all a, b in PTS(s).  This is the form the
;;; totally-bounded / completion arguments will need.

(def-predicate 'IS-UNIFORMLY-CONTINUOUS '(s t f)
  '(AND (IS-METRIC-SPACE s)
   (AND (IS-METRIC-SPACE t)
   (AND (IN f (FUN (PTS s) (PTS t)))
        (FORALL eps (IMPLIES (POS-RR eps)
          (FORSOME delta (AND (POS-RR delta)
            (FORALL a (IMPLIES (IN a (PTS s))
              (FORALL b (IMPLIES (IN b (PTS s))
                (IMPLIES (<= ((DIST s) a b) delta)
                         (<= ((DIST t) (f a) (f b)) eps))))))))))))))

;;; -----------------------------------------------------------------------
;;; continuous-is-continuous-at: the backchain-ready conjunct of IS-CONTINUOUS
;;; -- in a continuous map, every domain point is a point of continuity.
;;; Trivially derivable (it is the last conjunct of the unfolded definition);
;;; supplied as support because VNB macetes rewrite goals, not hypotheses
;;; [[reference-vnb-proof-mechanics]].  Library-build phase: asserted as
;;; support [[feedback-library-axioms-fine]].

;;; continuous-is-continuous-at RETIRED 2026-09-18 (rake batch 5): proven modulo 0 in theorem-library/rake-norm-metrics.scm

;;; -----------------------------------------------------------------------
;;; uniformly-continuous-is-continuous: a uniformly continuous map is
;;; continuous -- the uniform delta serves at each point.  A genuine (if
;;; one-line) implication, asserted in the library-build phase.

;;; uniformly-continuous-is-continuous RETIRED 2026-09-18 (rake batch 5): proven modulo 0 in theorem-library/rake-norm-metrics.scm

;;; Notation -- read by wff->english / the proof reader (operators.scm).
(notation! 'IS-CONTINUOUS         'kind 'predicate 'arity 3 'english "$3 is continuous from $1 to $2")
(notation! 'IS-CONTINUOUS-AT      'kind 'predicate 'arity 4 'english "$3 is continuous at $4")

;;; -----------------------------------------------------------------------
;;; THE MORPHISMS OF METRIC-SPACE ARE ITS ISOMETRIES.
;;;
;;; def-structure GENERATES IS-HOM-METRIC-SPACE as preservation of the DIST slot,
;;; d(t)(f(x), f(y)) = d(s)(x, y) -- an ISOMETRY.  That IS the metric category: its
;;; isomorphisms are the surjective isometries, and the metric does categorical work.
;;;
;;; An earlier cut OVERRODE this to IS-CONTINUOUS, reasoning the Met -> Top functor
;;; should carry continuous maps to continuous maps.  But a continuous bijection with
;;; continuous inverse is a HOMEOMORPHISM, so in (Met, continuous) an isomorphism forgets
;;; the metric entirely -- that category is Metrizable-Top wearing a metric as dead
;;; weight, not Met.  Continuity is topological; it now lives in the METRIZABLE-TOP-SPACE
;;; category and the Met -> Metrizable-Top functor (top-space.scm).
;;;
;;; So METRIC-SPACE keeps its GENERATED isometry hom -- NO declare-hom! override.  The
;;; functor's action on arrows (an isometry induces a continuous map) is a THEOREM, not
;;; an empty degeneracy: metric-hom-is-continuous below, cited by metric-top-functorial.

;;; IS-ISOMETRY names the same predicate as the generated IS-HOM-METRIC-SPACE (both are
;;; preservation of DIST); kept as the readable name -- the completion embedding is an
;;; isometry, and callers say so.
(def-predicate 'IS-ISOMETRY '(s t f)
  '(AND (IS-METRIC-SPACE s)
   (AND (IS-METRIC-SPACE t)
    (AND (IN f (FUN (PTS s) (PTS t)))
         (FORALL x (IMPLIES (IN x (PTS s))
           (FORALL y (IMPLIES (IN y (PTS s))
             (= ((DIST t) (f x) (f y)) ((DIST s) x y))))))))))

(notation! 'IS-ISOMETRY 'kind 'predicate 'arity 3
           'english "$3 is an isometry from $1 to $2")

;;; IS-HOM-METRIC-SPACE is the isometry hom (the generated preservation-of-DIST).
(notation! 'IS-HOM-METRIC-SPACE 'kind 'predicate 'arity 3
           'english "$3 is an isometry from $1 to $2")

;;; metric-hom-is-continuous: the Met -> Metrizable-Top functor's action on arrows --
;;; a metric-space morphism (isometry) is uniformly continuous (delta = eps), hence
;;; continuous.  Cited by metric-top-functorial.
;;; -----------------------------------------------------------------------
;;; Notation -- the ENGLISH of these predicates, declared beside their
;;; definitions and read by wff->english / the proof reader (operators.scm).
;;; A def-predicate's reading cannot be derived the way a structure's noun can
;;; (noun vs adjective: IS-COMPLETE wants "s is complete", not "s is a complete"),
;;; so it is written here, once, next to what it means.
(notation! 'IS-UNIFORMLY-CONTINUOUS 'kind 'predicate 'arity 3
           'english "$3 is uniformly continuous from $1 to $2")
