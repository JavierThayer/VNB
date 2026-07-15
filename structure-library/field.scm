;;; field.scm -- FIELD: a commutative ring in which every nonzero element
;;; has a multiplicative inverse.
;;;
;;; FIELD is its own shape structure, not a definitional refinement of
;;; INTEGRAL-DOMAIN.  Two extra slots make the multiplicative group of a
;;; field directly visible:
;;;
;;;   carriers:  A, NON-ZERO
;;;   ops:       ADD, MUL, NEG, RECIP   (RECIP : NON-ZERO -> NON-ZERO)
;;;   constants: ZERO, ONE
;;;
;;; Declaration order is chosen so the slots shared with RING keep RING's
;;; indices: A at 1, ADD at 2, MUL at 3, NEG at 4, ZERO at 5, ONE at 6, with
;;; NON-ZERO at 7 and RECIP at 8.  This avoids overwriting RING's accessor
;;; macetes; (ADD r), (MUL r), etc. still reduce to (NTH 2 r), (NTH 3 r),
;;; ... regardless of whether r is a RING or a FIELD.  See structures.scm
;;; for the declaration-order indexing rule.
;;;
;;; The view FIELD-MULTIPLICATIVE-GROUP picks out (NON-ZERO, MUL, ONE, RECIP)
;;; as a genuine group, and FIELD-AS-INTEGRAL-DOMAIN forgets the two extra
;;; slots so all ring/comm-ring/integral-domain theorems specialize back.
;;;
;;; Dependencies: ring.scm, commutative-ring.scm, integral-domain.scm.

(declare-structure FIELD
  ;; Slots 1-6: identical layout to RING, so shared accessor macetes
  ;; ADD/MUL/NEG/ZERO/ONE keep the same NTH index on FIELD tuples as on
  ;; RING tuples.
  (carriers CARR)
  (op ADD (CARTESIAN CARR CARR) CARR)
  (op MUL (CARTESIAN CARR CARR) CARR)
  (op NEG CARR CARR)
  (constant ZERO CARR)
  (constant ONE CARR)
  ;; Slots 7-8: FIELD-specific carrier and op.  NON-ZERO is DERIVED -- it is
  ;; CARR with the zero removed, not a set the tuple may choose freely.  Until
  ;; 2026-07-12 it was a plain carrier and IS-FIELD said NOTHING relating it to
  ;; CARR: a "field" could have had any set at all in slot 7, with RECIP an
  ;; arbitrary function on it.  The equation lived in a separate ASSERTED axiom
  ;; (field-non-zero-carrier, below), i.e. a support was finishing a definition.
  ;; Being derived also makes a field MORPHISM one map instead of two: NON-ZERO
  ;; is not an independent sort, so it rides CARR's map (structures.scm,
  ;; build-hom-axiom).
  (derived NON-ZERO CARR (DIFFERENCE CARR (SINGLETON ZERO)))
  (op RECIP NON-ZERO NON-ZERO)
  ;; Additive abelian group on A.
  (property is-associative ADD CARR)
  (property is-commutative ADD CARR)
  (property is-identity   ADD ZERO CARR)
  (property has-inverses  ADD ZERO NEG CARR)
  ;; Multiplicative commutative monoid on A; distributive.
  (property is-associative MUL CARR)
  (property is-commutative MUL CARR)
  (property is-identity   MUL ONE CARR)
  (property is-distributive ADD MUL CARR))

;;; Carrier relation: NON-ZERO is CARR with the zero element removed.  This is now
;;; a CONJUNCT of IS-FIELD (the `derived' slot above), so it is a projection of the
;;; definition -- definitional, not asserted debt.  It was asserted until
;;; 2026-07-12, which is how a definition came to depend on a support.
(fluid-let ((*current-provenance* 'definitional))
  (theory-add-axiom! *current-theory* 'field-non-zero-carrier
    '(FORALL s (IMPLIES (IS-FIELD s)
       (= (NON-ZERO s) (DIFFERENCE (CARR s) (SINGLETON (ZERO s))))))))

;;; Multiplicative inverse: RECIP is the right inverse of MUL on NON-ZERO.
(theory-add-axiom! *current-theory* 'field-mul-inverse
  '(FORALL s (IMPLIES (IS-FIELD s)
     (FORALL a (IMPLIES (IN a (NON-ZERO s))
       (= ((MUL s) a ((RECIP s) a)) (ONE s)))))))

;;; A field has at least two elements.
(theory-add-axiom! *current-theory* 'field-zero-not-one
  '(FORALL s (IMPLIES (IS-FIELD s) (NOT (= (ZERO s) (ONE s))))))

;;; Notation -- read by wff->english / the proof reader (operators.scm).
(notation! 'IS-FIELD              'kind 'predicate 'arity 1 'noun "field" 'article "a")
