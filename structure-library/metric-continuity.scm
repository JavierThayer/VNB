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
;;; Dependencies: metric-space.scm (IS-METRIC-SPACE, X, D), number-systems.scm
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

(support 'continuous-is-continuous-at
  '(FORALL s (FORALL t (FORALL f
     (IMPLIES (IS-CONTINUOUS s t f)
       (FORALL a (IMPLIES (IN a (PTS s))
         (IS-CONTINUOUS-AT s t f a))))))))

;;; -----------------------------------------------------------------------
;;; uniformly-continuous-is-continuous: a uniformly continuous map is
;;; continuous -- the uniform delta serves at each point.  A genuine (if
;;; one-line) implication, asserted in the library-build phase.

(support 'uniformly-continuous-is-continuous
  '(FORALL s (FORALL t (FORALL f
     (IMPLIES (IS-UNIFORMLY-CONTINUOUS s t f)
       (IS-CONTINUOUS s t f))))))

;;; Notation -- read by wff->english / the proof reader (operators.scm).
(notation! 'IS-CONTINUOUS         'kind 'predicate 'arity 3 'english "$3 is continuous from $1 to $2")
(notation! 'IS-CONTINUOUS-AT      'kind 'predicate 'arity 4 'english "$3 is continuous at $4")

;;; -----------------------------------------------------------------------
;;; THE MORPHISMS OF A METRIC SPACE ARE ITS CONTINUOUS MAPS.
;;;
;;; def-structure GENERATES IS-HOM-X as preservation-of-slots, which for
;;; METRIC-SPACE reads d(t)(f(x), f(y)) = d(s)(x, y) -- an ISOMETRY.  That is a
;;; category, but it is not the one this library works in: the header of this
;;; file has said "these are the morphisms of the metric-space structure" about
;;; IS-CONTINUOUS since it was written, and nothing ever cited the generated hom.
;;; The two beliefs sat side by side until the METRIC-SPACE -> TOP-SPACE functor
;;; forced the question: that functor carries CONTINUOUS maps to continuous maps,
;;; and its functoriality obligation is only worth stating over them (over
;;; isometries it degenerates to "an isometry is continuous", true and empty).
;;;
;;; So the species DECLARES its morphisms and overrides the generated ones.
;;; declare-hom! supplies IS-METRIC-SPACE(s), IS-METRIC-SPACE(t) and the typing
;;; of f, so the body states only what is characteristic.
(declare-hom! 'METRIC-SPACE '(s t f)
  '(IS-CONTINUOUS s t f))

;;; The isometries do not disappear -- they stop being "the" hom and become a
;;; predicate of their own (the completion embedding is an isometry, not merely
;;; a continuous map).  This is exactly the formula def-structure used to
;;; generate for IS-HOM-METRIC-SPACE.
(def-predicate 'IS-ISOMETRY '(s t f)
  '(AND (IS-METRIC-SPACE s)
   (AND (IS-METRIC-SPACE t)
    (AND (IN f (FUN (PTS s) (PTS t)))
         (FORALL x (IMPLIES (IN x (PTS s))
           (FORALL y (IMPLIES (IN y (PTS s))
             (= ((DIST t) (f x) (f y)) ((DIST s) x y))))))))))

(notation! 'IS-ISOMETRY 'kind 'predicate 'arity 3
           'english "$3 is an isometry from $1 to $2")

;;; The metric hom is CONTINUITY, so "homomorphism" -- the default a generated hom
;;; gets -- is the wrong word for it.  A species that overrides its morphisms owes
;;; the reading, beside the override.
(notation! 'IS-HOM-METRIC-SPACE 'kind 'predicate 'arity 3
           'english "$3 is continuous from $1 to $2")

;;; -----------------------------------------------------------------------
;;; Notation -- the ENGLISH of these predicates, declared beside their
;;; definitions and read by wff->english / the proof reader (operators.scm).
;;; A def-predicate's reading cannot be derived the way a structure's noun can
;;; (noun vs adjective: IS-COMPLETE wants "s is complete", not "s is a complete"),
;;; so it is written here, once, next to what it means.
(notation! 'IS-UNIFORMLY-CONTINUOUS 'kind 'predicate 'arity 3
           'english "$3 is uniformly continuous from $1 to $2")
