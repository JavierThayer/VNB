;;; normed-field.scm -- NORMED-FIELD: a commutative ring with multiplicative
;;; inverses and a structurally-carried norm into RR.
;;;
;;; Declared as its OWN shape (not a definitional refinement of FIELD): the
;;; norm NRM is a real structural slot, not a FORSOME-existentially asserted
;;; component.  Slot order matches RING for slots 1-6 so the accessors
;;; A/ADD/MUL/NEG/ZERO/ONE keep their RING indices on a NORMED-FIELD tuple;
;;; NRM lives at slot 7.
;;;
;;;   carriers: A
;;;   ops:      ADD, MUL, NEG, NRM   (NRM : A -> RR)
;;;   const:    ZERO, ONE
;;;
;;; The defining IFF (auto-generated from the property clauses) asserts the
;;; commutative-ring laws and is-norm for NRM.  Multiplicative inverses are
;;; asserted by the separate `normed-field-mul-inverses' axiom, matching
;;; field.scm's pattern (the existence-of-inverses law is not in the basic
;;; operation-properties vocabulary).
;;;
;;; FIELD remains an 8-slot shape carrying NON-ZERO and INV structurally;
;;; NORMED-FIELD is a separate, 7-slot shape carrying NRM.  The two are
;;; related at the predicate level: every normed-field is a commutative
;;; ring (slots 1-6 match RING's layout, so IS-COMMUTATIVE-RING reads
;;; correctly off a NORMED-FIELD tuple).  A `def-view-as' projection to
;;; COMMUTATIVE-RING can be added when a caller needs the structure-level
;;; transport.
;;;
;;; Witnessing norms for the numeric instances:
;;;   RR -- `abs'      (axiomatized in number-systems.scm)
;;;   CC -- `magnitude' (axiomatized in number-systems.scm)
;;;
;;; Dependencies: ring.scm, commutative-ring.scm, number-systems.scm
;;; (for RR and the abs/magnitude axioms), operation-properties.scm (is-norm).

(def-structure-from-clauses 'NORMED-FIELD
  '(;; Slots 1-6 mirror RING so shared accessors keep their NTH indices.
    (carriers A)
    (op ADD (CARTESIAN A A) A)
    (op MUL (CARTESIAN A A) A)
    (op NEG A A)
    (constant ZERO A)
    (constant ONE A)
    ;; Slot 7: the structurally-carried norm.
    (op NRM A RR)
    ;; Additive abelian group on A.
    (property is-associative ADD A)
    (property is-commutative ADD A)
    (property is-identity   ADD ZERO A)
    (property has-inverses  ADD ZERO NEG A)
    ;; Multiplicative commutative monoid; distributive.
    (property is-associative MUL A)
    (property is-commutative MUL A)
    (property is-identity   MUL ONE A)
    (property is-distributive ADD MUL A)
    ;; The norm.
    (property is-norm NRM ADD MUL ZERO A)))

;;; Multiplicative inverses: every nonzero element has a multiplicative
;;; inverse.  Asserted existentially (no structural INV slot in this shape).
(theory-add-axiom! *current-theory* 'normed-field-mul-inverses
  '(FORALL s (IMPLIES (IS-NORMED-FIELD s)
     (FORALL a (IMPLIES (AND (IN a (A s)) (NOT (= a (ZERO s))))
       (FORSOME b
         (AND (IN b (A s))
              (NOT (= b (ZERO s)))
              (= ((MUL s) a b) (ONE s)))))))))

;;; A normed-field has at least two elements.
(theory-add-axiom! *current-theory* 'normed-field-zero-not-one
  '(FORALL s (IMPLIES (IS-NORMED-FIELD s) (NOT (= (ZERO s) (ONE s))))))

;;; Relation to the ring hierarchy.  A NORMED-FIELD is a 7-tuple; RING /
;;; COMMUTATIVE-RING / INTEGRAL-DOMAIN are 6-slot predicates that pin
;;; length(s)=6.  So a normed field does NOT satisfy them on the same tuple
;;; -- the earlier axioms `(IS-NORMED-FIELD s) => (IS-COMMUTATIVE-RING s)'
;;; etc. were inconsistent (they forced length 6 = length 7; removed
;;; 2026-05-30).  Just like FIELD (see field.scm / FIELD-AS-INTEGRAL-DOMAIN),
;;; NORMED-FIELD reaches the ring world through the view-as projections
;;; NORMED-FIELD-AS-COMMUTATIVE-RING and NORMED-FIELD-AS-INTEGRAL-DOMAIN
;;; (views.scm), which build a fresh 6-tuple from slots 1..6.
