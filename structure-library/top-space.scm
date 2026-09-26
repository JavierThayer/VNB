;;; top-space.scm -- TOPOLOGICAL SPACES, and the functor Met -> Top
;;;
;;; TOP-SPACE = [PTS, OPENS]: a carrier and a topology on it.  OPENS is not an
;;; operation but a CONSTANT slot -- a set of subsets, i.e. an element of
;;; POWER(POWER(PTS)) -- and the four topology laws are (law ...) conjuncts
;;; of IS-TOP-SPACE.
;;;
;;; This structure is the reason structures.scm carries the comment "TWO THINGS
;;; THE ALIST CANNOT DO", and it exercises both of them:
;;;
;;;   (1) ITS MORPHISMS ARE NOT ITS HOMOMORPHISMS.  The generated IS-HOM-X is
;;;       preservation-of-slots, which here would read OPENS(a) = OPENS(b) --
;;;       the two topologies literally equal.  Continuity is a PREIMAGE
;;;       condition, not a preservation law, so TOP-SPACE declares its morphisms
;;;       (declare-hom!) and overrides the generated ones.
;;;
;;;   (2) THE FUNCTOR'S OBJECT MAP IS A CONSTRUCTION, NOT A SELECTION.  The
;;;       metric topology is not a SLOT of a metric space; it is COMPUTED from
;;;       DIST -- the set of U that IS-OPEN(md, U).  No correspondence of
;;;       accessors yields it, so METRIC-TOP is a def-constructed-functor.
;;;
;;; And the two compose into the oddity that motivated the file: the natural
;;; functor Met -> Top is not shape-determined in EITHER coordinate.  Its object
;;; map is a construction, and its morphism map carries the CONTINUOUS maps --
;;; which is why metric-continuity.scm now declares those to be METRIC-SPACE's
;;; morphisms (they always were; the generated isometry hom was never cited).
;;;
;;; Dependencies: metric-space, metric-continuity (IS-CONTINUOUS, the metric hom
;;; override), metric-open-sets (IS-OPEN, PREIMAGE).

;;; -----------------------------------------------------------------------
;;; The structure.
;;;
;;; PTS is slot 1 here as it is in METRIC-SPACE -- the same name at the same
;;; index, which is what the one-name-one-slot rule requires (and what lets
;;; PREIMAGE, whose body is SEP over PTS(s), serve both species).

(declare-structure TOP-SPACE
  (instance-var s)                          ; the laws below range over the instance s
  (carriers PTS)
  (constant OPENS (POWER (POWER PTS)))
  ;; the empty set and the whole space are open
  (law (IN EMPTY-SET (OPENS s)))
  (law (IN (PTS s) (OPENS s)))
  ;; closed under BINARY intersection (hence finite, by induction)
  (law (FORALL u (IMPLIES (IN u (OPENS s))
         (FORALL v (IMPLIES (IN v (OPENS s))
           (IN (INTERSECTION u v) (OPENS s)))))))
  ;; closed under ARBITRARY union: any subfamily of the topology unions to an
  ;; open set.  (BIG-UNION u fam u) is the union of the members of fam.
  (law (FORALL fam (IMPLIES (SUBSET fam (OPENS s))
         (IN (BIG-UNION u fam u) (OPENS s))))))

;;; -----------------------------------------------------------------------
;;; The morphisms: f is continuous iff the preimage of every open set is open.
;;;
;;; declare-hom! supplies IS-TOP-SPACE(s), IS-TOP-SPACE(t) and (IN f (FUN (PTS s)
;;; (PTS t))), so the body states only what is characteristic.  The hom's
;;; variables are s and t, NOT a and b: PREIMAGE unfolds to (SEP a (PTS s) ...),
;;; and an `a' here would be captured by that binder.

(declare-hom! 'TOP-SPACE '(s t f)
  '(FORALL u (IMPLIES (IN u (OPENS t))
      (IN (PREIMAGE s f u) (OPENS s)))))

;;; -----------------------------------------------------------------------
;;; METRIZABLE-TOP-SPACE: the topological spaces that carry a compatible metric.
;;;
;;; A full subcategory of TOP-SPACE -- same shape [PTS, OPENS], same morphisms
;;; (continuity) -- refined by ONE property: the topology is INDUCED by some metric,
;;; i.e. s is the metric topology of some metric space md.  This is the category
;;; where continuity is the morphism; METRIC-SPACE's own morphisms are its isometries
;;; (metric-continuity.scm).  The law names the induced-topology tuple directly (it is
;;; METRIC-TOP(md) unfolded -- the functoid is declared just below, so cannot be named
;;; here yet).
(declare-structure METRIZABLE-TOP-SPACE
  (instance-var s)
  (same-shape-as TOP-SPACE)
  (law (FORSOME md (AND (IS-METRIC-SPACE md)
                    (== s (LIST (PTS md) (SEP u (POWER (PTS md)) (IS-OPEN md u))))))))

;;; Its morphisms are TOP-SPACE's -- continuity.  (same-shape-as inherits the shape,
;;; not the hom override, so it is stated here.)
(declare-hom! 'METRIZABLE-TOP-SPACE '(s t f)
  '(FORALL u (IMPLIES (IN u (OPENS t))
      (IN (PREIMAGE s f u) (OPENS s)))))
(notation! 'IS-METRIZABLE-TOP-SPACE 'kind 'predicate 'arity 1
           'english "$1 is a metrizable topological space")
(notation! 'IS-HOM-METRIZABLE-TOP-SPACE 'kind 'predicate 'arity 3
           'english "$3 is continuous from $1 to $2")

;;; -----------------------------------------------------------------------
;;; IS-HAUSDORFF(s): distinct points have disjoint open neighbourhoods (T2).
;;;
;;; Points are `a'/`b' (never `x' -- PTS folds onto x); the separating opens are
;;; `u'/`v'.  Every METRIC topology is Hausdorff (the balls of radius d(a,b)/2
;;; separate), so this adds nothing over metrizability -- but the pseudometric
;;; GAUGE topologies (forthcoming) need not be, and there Hausdorff is exactly
;;; the separation hypothesis that upgrades the pseudometric family to a metric.
;;; So it lives as a predicate to be assumed, not a fact to be derived.  The
;;; distinctness `(NOT (== a b))' is folded in as an antecedent, so the whole
;;; body is a guarded universal, not a hand-counted paren pyramid.
(def-predicate 'IS-HAUSDORFF '(s)
  (conjuncts->and
    (list
      '(IS-TOP-SPACE s)
      (forall-guarded '(a b)
        (list '(IN a (PTS s)) '(IN b (PTS s)) '(NOT (== a b)))
        (list 'FORSOME 'u
          (list 'FORSOME 'v
            (conjuncts->and
              (list '(IN u (OPENS s))
                    '(IN v (OPENS s))
                    '(IN a u)
                    '(IN b v)
                    '(== (INTERSECTION u v) EMPTY-SET)))))))))
(notation! 'IS-HAUSDORFF 'kind 'predicate 'arity 1 'english "$1 is Hausdorff")

;;; -----------------------------------------------------------------------
;;; The functor Met -> Metrizable-Top: a metric space carries the topology of its open
;;; sets, and that topology is metrizable BY CONSTRUCTION (the metric itself witnesses).
;;;
;;;   METRIC-TOP(md) = [PTS(md), { U in POWER(PTS(md)) : IS-OPEN(md, U) }]
;;;
;;; def-constructed-functor ASSERTS NOTHING.  It installs the object map as a functoid
;;; and records two obligations, reported by functor-obligation-audit until proven:
;;;
;;;   metric-top-is-metrizable-top-space : IS-METRIC-SPACE(md)
;;;                                          => IS-METRIZABLE-TOP-SPACE(METRIC-TOP md)
;;;       -- the metric opens form a topology (metric-open-sets.scm) AND it is
;;;          metrizable, with md itself the witness.
;;;
;;;   metric-top-functorial : IS-HOM-METRIC-SPACE(a, b, f)
;;;                             => IS-HOM-METRIZABLE-TOP-SPACE(METRIC-TOP a, METRIC-TOP b, f)
;;;       -- an isometry induces a continuous map: metric-hom-is-continuous
;;;          (metric-continuity.scm) then continuous => open-preimage.  The functor's
;;;          genuine action on arrows -- forgetful, well-defined, not empty.

(def-constructed-functor 'METRIC-TOP 'METRIC-SPACE 'METRIZABLE-TOP-SPACE '(md)
  '(LIST (PTS md)
         (SEP u (POWER (PTS md)) (IS-OPEN md u))))

;;; -----------------------------------------------------------------------
;;; Notation -- read by wff->english / the proof reader (operators.scm).

(notation! 'IS-TOP-SPACE     'kind 'predicate 'arity 1 'english "$1 is a topological space")
(notation! 'OPENS            'kind 'accessor  'arity 1 'english "the topology of $1")
(notation! 'IS-HOM-TOP-SPACE 'kind 'predicate 'arity 3
           'english "$3 is continuous from $1 to $2")
(notation! 'METRIC-TOP       'kind 'functoid  'arity 1
           'english "the metric topology of $1")

;;; -----------------------------------------------------------------------
;;; metrizable-has-metric-top: a metrizable space is (up to ==) the metric topology
;;; of SOME metric space -- the METRIZABLE-TOP-SPACE law with its tuple named
;;; METRIC-TOP.  The clean extraction dual of metric-top-is-metrizable-top-space, so
;;; a proof pulls a compatible metric out of metrizability without unfolding the raw
;;; LIST tuple of the defining law.
;;; metrizable-has-metric-top RETIRED 2026-09-19 (rake batch 6): proven modulo 0 in theorem-library/rake-bdd-metric.scm
