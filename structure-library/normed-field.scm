;;; normed-field.scm -- NORMED-FIELD: a commutative ring with multiplicative
;;; inverses and a structurally-carried norm into RR.
;;;
;;; Declared as its OWN shape (not a definitional refinement of FIELD): the
;;; norm FNRM is a real structural slot, not a FORSOME-existentially asserted
;;; component.  Slot order matches RING for slots 1-6 so the accessors
;;; A/ADD/MUL/NEG/ZERO/ONE keep their RING indices on a NORMED-FIELD tuple;
;;; FNRM lives at slot 7.
;;;
;;;   carriers: A
;;;   ops:      ADD, MUL, NEG, FNRM   (FNRM : CARR -> RR)
;;;   const:    ZERO, ONE
;;;
;;; The defining IFF (auto-generated from the property clauses) asserts the
;;; commutative-ring laws, is-norm for FNRM, and (two law clauses, since
;;; 2026-10-12) zero /= one and the existence of multiplicative inverses.
;;;
;;; FIELD remains an 8-slot shape carrying NON-ZERO and INV structurally;
;;; NORMED-FIELD is a separate, 7-slot shape carrying FNRM.  The two are
;;; related at the predicate level: every normed-field is a commutative
;;; ring (slots 1-6 match RING's layout, so IS-COMMUTATIVE-RING reads
;;; correctly off a NORMED-FIELD tuple).  A `def-functor' projection to
;;; COMMUTATIVE-RING can be added when a caller needs the structure-level
;;; transport.
;;;
;;; Witnessing norms for the numeric instances:
;;;   RR -- `abs'      (axiomatized in number-systems.scm)
;;;   CC -- `magnitude' (axiomatized in number-systems.scm)
;;;
;;; Dependencies: ring.scm, commutative-ring.scm, number-systems.scm
;;; (for RR and the abs/magnitude axioms), operation-properties.scm (is-norm).

(declare-structure NORMED-FIELD
  (instance-var s)
  ;; Slots 1-6 mirror RING so shared accessors keep their NTH indices.
  (carriers CARR)
  (op ADD (CARTESIAN CARR CARR) CARR)
  (op MUL (CARTESIAN CARR CARR) CARR)
  (op NEG CARR CARR)
  (constant ZERO CARR)
  (constant ONE CARR)
  ;; Slot 7: the structurally-carried norm.
  (op FNRM CARR RR)
  ;; Additive abelian group on A.
  (property is-associative ADD CARR)
  (property is-commutative ADD CARR)
  (property is-identity   ADD ZERO CARR)
  (property has-inverses  ADD ZERO NEG CARR)
  ;; Multiplicative commutative monoid; distributive.
  (property is-associative MUL CARR)
  (property is-commutative MUL CARR)
  (property is-identity   MUL ONE CARR)
  (property is-distributive ADD MUL CARR)
  ;; The norm.
  (property is-norm FNRM ADD MUL ZERO CARR)
  ;; That a normed field has two elements and that every nonzero element is
  ;; invertible: (law ...) clauses since 2026-10-12 (the user's decision).  They were
  ;; two ASSERTED axioms beside the declaration (normed-field-zero-not-one,
  ;; normed-field-mul-inverses) -- a support finishing a definition, the defect
  ;; FIELD had until 2026-09-15.  No slot carries the inverse, so the law is the
  ;; existential, as in FIELD-RING; the inverse is stated nonzero, as the old axiom
  ;; did.
  (law "not(zero(s) = one(s))")
  (law "forall([a_ in carr(s)],
          not(a_ = zero(s)) implies
            forsome([b_ in carr(s)], not(b_ = zero(s)) and mul(s)(a_, b_) = one(s)))"))

;;; normed-field-mul-inverses is a (law ...) clause of the NORMED-FIELD declaration since 2026-10-12 (the user's decision); the asserted axiom is retired, original in archive/2026-10-12-rake-asm/normed-field.scm.

;;; normed-field-zero-not-one is a (law ...) clause of the NORMED-FIELD declaration since 2026-10-12 (the user's decision); the asserted axiom is retired, original in archive/2026-10-12-rake-asm/normed-field.scm.

;;; Relation to the ring hierarchy.  A NORMED-FIELD is a 7-tuple; RING /
;;; COMMUTATIVE-RING / INTEGRAL-DOMAIN are 6-slot predicates that pin
;;; length(s)=6.  So a normed field does NOT satisfy them on the same tuple
;;; -- the earlier axioms `(IS-NORMED-FIELD s) => (IS-COMMUTATIVE-RING s)'
;;; etc. were inconsistent (they forced length 6 = length 7; removed
;;; 2026-05-30).  Just like FIELD (see field.scm / FIELD-AS-INTEGRAL-DOMAIN),
;;; NORMED-FIELD reaches the ring world through the view-as projections
;;; NORMED-FIELD-AS-COMMUTATIVE-RING and NORMED-FIELD-AS-INTEGRAL-DOMAIN
;;; (views.scm), which build a fresh 6-tuple from slots 1..6.

;;; Notation -- read by wff->english / the proof reader (operators.scm).
(notation! 'IS-NORMED-FIELD       'kind 'predicate 'arity 1 'noun "normed field" 'article "a")
