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
;;; The functor Met -> Top: a metric space carries the topology of its open sets.
;;;
;;;   METRIC-TOP(md) = [PTS(md), { U in POWER(PTS(md)) : IS-OPEN(md, U) }]
;;;
;;; def-constructed-functor ASSERTS NOTHING.  It installs the object map as a
;;; functoid and records two obligations, which functor-obligation-audit reports
;;; until they are theorems -- a functor you have not proved is a functor you do
;;; not have:
;;;
;;;   metric-top-is-top-space : IS-METRIC-SPACE(md) => IS-TOP-SPACE(METRIC-TOP md)
;;;       -- the metric open sets form a topology.  metric-open-sets.scm already
;;;       has the pieces (open-union over a family, open-intersection, the whole
;;;       space and the empty set open).
;;;
;;;   metric-top-functorial : IS-HOM-METRIC-SPACE(a, b, f)
;;;                             => IS-HOM-TOP-SPACE(METRIC-TOP a, METRIC-TOP b, f)
;;;       -- eps-delta continuity implies the preimage of every open set is open.
;;;       THIS is the theorem the functor exists to force, and it is a theorem
;;;       only because the metric hom is continuity: over isometries it would
;;;       degenerate into "an isometry is continuous".

(def-constructed-functor 'METRIC-TOP 'METRIC-SPACE 'TOP-SPACE '(md)
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
