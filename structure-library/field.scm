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


;;; -----------------------------------------------------------------------
;;; FIELD-RING -- fieldhood as a PROPERTY OF A 6-SLOT RING.
;;;
;;; FIELD above is an 8-slot SHAPE: it carries NON-ZERO and RECIP as data, and
;;; IS-FIELD therefore pins length(s) = 8.  That is the right shape for a field
;;; in its own right (it makes the multiplicative group a view, FIELD-
;;; MULTIPLICATIVE-GROUP), and it is the WRONG thing to demand of a SLOT that
;;; some other structure has already typed a RING.
;;;
;;; MODULE's scalar slot is exactly such a slot: `(substructure SCAL RING)'
;;; puts (IS-RING (SCAL s)) in the generated IFF, pinning length(scal(s)) = 6.
;;; VECTOR-SPACE (finite-dimensional.scm) is `(same-shape-as MODULE)' plus the
;;; law "the scalars are a field", and while that law read `is-field(scal(s))'
;;; it asserted 6 = 8: IS-VECTOR-SPACE was UNSATISFIABLE, and with it
;;; IS-FINITE-DIMENSIONAL, from the day it was written until 2026-08-23.  Same
;;; defect class as the NORMED-VECTOR-SPACE one repaired the same day, and it
;;; survived that repair untouched.
;;;
;;; IS-FIELD-RING says of a 6-tuple exactly what a field is, in the shape the
;;; slot already has: a commutative ring, nontrivial, in which every nonzero
;;; element has a multiplicative inverse.  It joins the RING refinement ladder
;;; (COMMUTATIVE-RING / INTEGRAL-DOMAIN / EUCLIDEAN-RING / PID) as one more
;;; `same-shape-as' member, so every ring theorem specializes to it for free
;;; and the satisfiability audit still SEES the slot's pin -- 6 against 6 --
;;; where an existential `forsome fld. is-field(fld) and scal(s) = ...' would
;;; have hidden it (the audit's conjunct walk does not descend into a FORSOME).
;;;
;;; WHY IT REFINES COMMUTATIVE-RING AND NOT INTEGRAL-DOMAIN.  A field-ring has
;;; no zero divisors, but that is DERIVABLE here (if a*b = 0 and a /= 0 then
;;; b = 1*b = (a^-1*a)*b = a^-1*(a*b) = 0), and a definition should not carry a
;;; conjunct its other conjuncts already give.  `IS-FIELD-RING(s) =>
;;; IS-INTEGRAL-DOMAIN(s)' is therefore a THEOREM, not a conjunct -- the same
;;; relation integral-domain-laws.scm proves for its own neighbours.  ONE /=
;;; ZERO is NOT derivable (the zero ring has 0 = 1 and vacuously invertible
;;; nonzero elements), so it is stated.
;;;
;;; RELATION TO FIELD.  The bridge is
;;;     IS-FIELD(f)  =>  IS-FIELD-RING(FIELD-AS-INTEGRAL-DOMAIN(f))
;;; -- forget NON-ZERO and RECIP, keep the invertibility as an existence claim.
;;; It cannot be stated in this file (FIELD-AS-INTEGRAL-DOMAIN is declared in
;;; views.scm, which loads later) and nothing in the library needs it yet, so
;;; it is NOT in the tree: it wants the shape of theorem-library/normed-field-
;;; ring-view.scm, six accessor read-offs off the projected LIST plus the
;;; invertibility witness RECIP(f)(a).  The converse direction is the one that
;;; is not free -- it must CHOOSE a RECIP -- and that asymmetry is the reason
;;; the slot holds a FIELD-RING rather than a projected FIELD.
(declare-structure FIELD-RING
  (instance-var s)
  (same-shape-as COMMUTATIVE-RING)
  (law "not(one(s) = zero(s))")
  (law "forall([a_ in carr(s)],
          not(a_ = zero(s)) implies
            forsome([b_ in carr(s)], mul(s)(a_, b_) = one(s)))"))

;;; Notation -- read by wff->english / the proof reader (operators.scm).
(notation! 'IS-FIELD              'kind 'predicate 'arity 1 'noun "field" 'article "a")
(notation! 'IS-FIELD-RING         'kind 'predicate 'arity 1 'noun "field" 'article "a")
