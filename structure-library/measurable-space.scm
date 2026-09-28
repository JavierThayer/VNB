;;; measurable-space.scm -- MEASURABLE-SPACE and MEASURE-SPACE as declared
;;; STRUCTURES.
;;;
;;;   MEASURABLE-SPACE   the pair   (X, A)        -- notes Def. 1.7
;;;   MEASURE-SPACE      the triple (X, A, mu)    -- notes Def. 1.16
;;;
;;; WHY THIS FILE EXISTS.  Until 2026-08-18 these were not objects at all.  A
;;; measurable space was spelled as the ARGUMENT LIST of a predicate --
;;; `IS-SIGMA-ALGEBRA(omega, cA)' -- and a measure space as
;;; `IS-MEASURE(omega, cA, mu)'.  That keeps a property of the components and
;;; throws away the thing they are components OF.  The user's ruling, and it is
;;; a standing design rule rather than a preference about this chapter:
;;;
;;;     "Structures in mathematics should be structures in VNB."
;;;
;;; Nothing about the logic ever forced the predicate form.  TOP-SPACE
;;; (structure-library/top-space.scm) is `(carriers PTS)' plus
;;; `(constant OPENS (POWER (POWER PTS)))' plus closure laws, which is EXACTLY
;;; the shape of a measurable space; swap OPENS for SIGMA and the closure laws
;;; for complement-and-countable-union and you have this file.  The split was
;;; chronology, not design: the metric/topology arc needed to quantify over
;;; spaces and map between them from the start, while sigma-algebra.scm was
;;; written as "VOCABULARY ONLY" for a chapter in which everything is about one
;;; fixed cA.  structures.scm states no criterion for structure-vs-predicate,
;;; so the choice was never defended.
;;;
;;; THIS IS AN ADDITION, NOT A MIGRATION, and that is the point.  The law clause
;;; of each declaration CITES the existing predicate rather than restating the
;;; closure conditions, so `IS-SIGMA-ALGEBRA(PTS(s), SIGMA(s))' is a LITERAL
;;; CONJUNCT of the generated biconditional.  Every one of the seven definitions
;;; and thirteen supports in structure-library/measure.scm therefore applies
;;; verbatim at (PTS m, SIGMA m, MEAS m) with nothing to prove and nothing to
;;; rewrite -- there is no bridging lemma, only a `mac' unfold.  Chapter 1 of
;;; the notes, which is about a single cA, is untouched and stays readable.
;;;
;;; THREE NAMING DECISIONS, each of which would have cost a debugging session:
;;;
;;;  (1) PTS, SHARED with METRIC-SPACE / TOP-SPACE / PSEUDOMETRIC-SPACE at slot
;;;      1.  Required by ONE NAME, ONE SLOT (register-accessor-index!): a name
;;;      that denoted two different indices would have its projection macete
;;;      withdrawn.  It is also the substantive choice -- a topological space
;;;      and a measurable space then answer the SAME accessor, so the Borel
;;;      sigma-algebra of a top-space t is written directly as
;;;      SIGMA-GENERATED(PTS(t), OPENS(t)), with no coercion between two notions
;;;      of underlying point set.  That is Example 1.10 of the notes.
;;;
;;;  (2) MEAS, not MU, for the measure slot.  `MU' is two characters, and every
;;;      measure proof in the world wants `mu' as a bound variable -- which
;;;      would then shadow a registered accessor and trip constant-binder-audit
;;;      (a HARD load failure), or worse, read as the accessor in head position.
;;;      See the case-folding section of CLAUDE.md; the danger zone is exactly
;;;      the one- and two-letter names.
;;;
;;;  (3) MEASURE-SPACE is NOT `same-shape-as' MEASURABLE-SPACE.  A different
;;;      shape is a different structure: the triple has a slot the pair does not,
;;;      and `same-shape-as' inherits the parent's slots and forbids declaring
;;;      new ones.  The two are related by the def-functor below, which FORGETS
;;;      the measure -- the same relationship NORMED-VECTOR-SPACE has to MODULE.
;;;
;;; Loads after measure.scm (IS-MEASURE) and sigma-algebra.scm
;;; (IS-SIGMA-ALGEBRA), hence after extended-reals-pos.scm (RR-POS-STAR).

;;; -----------------------------------------------------------------------
;;; MEASURABLE-SPACE -- the pair (X, A).  Notes Def. 1.7: "A pair (X, A) with A
;;; a sigma-algebra of subsets of X is called a measurable space."
;;;
;;; The shape supplies PTS(s) in SET and SIGMA(s) subset POWER(PTS(s)); the law
;;; supplies the three Rudin 1.3 clauses, by citation.
;;;
;;; SIGMA is a FAMILY slot (a set of subsets of the carrier PTS), not a constant
;;; (batch 39, 2026-09-28).  IS-MEASURABLE-SPACE is the same formula either way;
;;; the difference is the generated MORPHISM.  As a constant slot SIGMA generated
;;; the clause SIGMA(a) = SIGMA(b) and left f unconstrained -- the wrong arrows
;;; (docs/categories-per-structure-2026-09-28.md).  As a family it generates
;;;   forall u in SIGMA(t). PREIMAGE(s, f, u) in SIGMA(s),
;;; the measurable maps.
(declare-structure MEASURABLE-SPACE
  (instance-var s)
  (carriers PTS)
  (family SIGMA PTS)
  (law (IS-SIGMA-ALGEBRA (PTS s) (SIGMA s))))

;;; -----------------------------------------------------------------------
;;; MEASURE-SPACE -- the triple (X, A, mu).  Notes Def. 1.16.
;;;
;;; IS-MEASURE already carries IS-SIGMA-ALGEBRA as its first conjunct, so the
;;; single law below gives the whole of Def. 1.16 including Def. 1.7.
;;;
;;; MEAS is a FUNCTION ON THE FAMILY SIGMA (batch 39): typed as the old
;;; (op MEAS SIGMA RR-POS-STAR) typed it, and generating the transport clause
;;;   forall u in SIGMA(t). MEAS(t)(u) = MEAS(s)(PREIMAGE(s, f, u)),
;;; so the default arrows are the measure-preserving measurable maps (the old
;;; clause compared the two measures on the SAME sets).
(declare-structure MEASURE-SPACE
  (instance-var s)
  (carriers PTS)
  (family SIGMA PTS)
  (family-fun MEAS SIGMA RR-POS-STAR)
  (law (IS-MEASURE (PTS s) (SIGMA s) (MEAS s))))

;;; --- view-as edge: forget the measure ---------------------------------
(def-functor 'MEASURE-SPACE-AS-MEASURABLE-SPACE
  'MEASURE-SPACE     '(PTS SIGMA)
  'MEASURABLE-SPACE  '(PTS SIGMA))

;;; --- readings ---------------------------------------------------------
;;; the generated arrows (the family / family-fun rules of build-hom-axiom)
(notation! 'IS-HOM-MEASURABLE-SPACE 'kind 'predicate 'arity 3
           'english "$3 is a measurable map from $1 to $2")
(notation! 'IS-HOM-MEASURE-SPACE 'kind 'predicate 'arity 3
           'english "$3 is a measure-preserving measurable map from $1 to $2")
(notation! 'PTS   'kind 'accessor 'arity 1)
(notation! 'SIGMA 'kind 'accessor 'arity 1 'english "the sigma-algebra of $1")
(notation! 'MEAS  'kind 'accessor 'arity 1 'english "the measure of $1")
