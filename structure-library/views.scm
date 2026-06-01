;;; views.scm -- view-as declarations between structures
;;;
;;; A view-as is a way to *see* one structure as another (RING as additive
;;; ABELIAN-GROUP, RING as multiplicative MONOID, ABELIAN-GROUP as MONOID,
;;; etc.).  Each declaration installs a constructor functoid and the
;;; corresponding typing axiom, and auto-specializes every target-structure
;;; theorem to the source structure.  See def-view-as in structures.scm.
;;;
;;; Why this file is separate: def-view-as must be called *after* both the
;;; source and target structures and all their theorems have been declared,
;;; so the auto-specialization at view-declaration time picks them all up.
;;;
;;; Dependencies: monoid, abelian-group, ring.

;;; -----------------------------------------------------------------------
;;; RING as additive ABELIAN-GROUP
;;;
;;; A ring's additive structure (A, ADD, ZERO, NEG) is an abelian group.
;;; AG's slot order from its def-structure-from-clauses is (A MUL E INV)
;;; -- the identity constant `E` comes before the unary inverse op `INV`.
;;; So the additive view maps:
;;;   ring's A    -> AG's A
;;;   ring's ADD  -> AG's MUL
;;;   ring's ZERO -> AG's E
;;;   ring's NEG  -> AG's INV

(def-view-as 'RING-ADDITIVE-AG
  'RING          '(A ADD ZERO NEG)
  'ABELIAN-GROUP '(A MUL E INV))

;;; -----------------------------------------------------------------------
;;; RING as multiplicative MONOID
;;;
;;; A ring's multiplicative structure (A, MUL, ONE) is a monoid.
;;; (Not a group: nonzero elements lack inverses in general rings.)
;;; MONOID's slot order is (A MUL E), so the multiplicative view maps:
;;;   ring's A   -> MONOID's A
;;;   ring's MUL -> MONOID's MUL
;;;   ring's ONE -> MONOID's E

(def-view-as 'RING-MULTIPLICATIVE-MONOID
  'RING   '(A MUL ONE)
  'MONOID '(A MUL E))

;;; -----------------------------------------------------------------------
;;; Additive abelian-group views for RING's definitional refinements
;;;
;;; COMMUTATIVE-RING, INTEGRAL-DOMAIN, FIELD, EUCLIDEAN-RING, NORMED-FIELD
;;; all share the RING shape (6 slots).  Each one is also a ring's additive
;;; abelian group.  The view component pattern is identical to
;;; RING-ADDITIVE-AG; only the source predicate differs (stronger as we
;;; descend the hierarchy).  Each view auto-specializes every
;;; ABELIAN-GROUP-quantified theorem to a theorem on the source structure.

(def-view-as 'COMMUTATIVE-RING-ADDITIVE-AG
  'COMMUTATIVE-RING '(A ADD ZERO NEG)
  'ABELIAN-GROUP    '(A MUL E INV))

(def-view-as 'INTEGRAL-DOMAIN-ADDITIVE-AG
  'INTEGRAL-DOMAIN '(A ADD ZERO NEG)
  'ABELIAN-GROUP   '(A MUL E INV))

(def-view-as 'FIELD-ADDITIVE-AG
  'FIELD         '(A ADD ZERO NEG)
  'ABELIAN-GROUP '(A MUL E INV))

(def-view-as 'EUCLIDEAN-RING-ADDITIVE-AG
  'EUCLIDEAN-RING '(A ADD ZERO NEG)
  'ABELIAN-GROUP  '(A MUL E INV))

(def-view-as 'NORMED-FIELD-ADDITIVE-AG
  'NORMED-FIELD  '(A ADD ZERO NEG)
  'ABELIAN-GROUP '(A MUL E INV))

;;; The underlying abelian group of a NORMED-AG: forget the norm slot.
;;; Slots align directly (NORMED-AG was shaped that way), so this is the
;;; identity projection on slots 1-4.  This view is the bridge that lets
;;; FINSUM / sum-ag-permutation-invariance sum a normed-AG-valued function.
(def-view-as 'NORMED-AG-AS-ABELIAN-GROUP
  'NORMED-AG     '(A MUL E INV)
  'ABELIAN-GROUP '(A MUL E INV))

;;; -----------------------------------------------------------------------
;;; Multiplicative monoid views for RING's definitional refinements
;;;
;;; In a general RING, the multiplicative structure (A, MUL, ONE) forms only
;;; a monoid (no inverses).  Even in INTEGRAL-DOMAIN and EUCLIDEAN-RING this
;;; is true.  In FIELD/NORMED-FIELD the *nonzero* part forms a group, but
;;; that requires a subset carrier — see views.scm comment block below on
;;; "the group of invertible elements" — and isn't expressible in the
;;; current def-view-as form.

(def-view-as 'COMMUTATIVE-RING-MULTIPLICATIVE-MONOID
  'COMMUTATIVE-RING '(A MUL ONE)
  'MONOID           '(A MUL E))

(def-view-as 'INTEGRAL-DOMAIN-MULTIPLICATIVE-MONOID
  'INTEGRAL-DOMAIN '(A MUL ONE)
  'MONOID          '(A MUL E))

;;; FIELD now carries NON-ZERO and INV as built-in slots (see field.scm
;;; reshape), so its nonzero elements form a genuine group, not just a
;;; monoid.  This replaces the old FIELD-MULTIPLICATIVE-MONOID view.
(def-view-as 'FIELD-MULTIPLICATIVE-GROUP
  'FIELD '(NON-ZERO MUL ONE INV)
  'GROUP '(A MUL E INV))

;;; Forget the extra slots to recover the integral-domain (and hence ring)
;;; view of a field.  This re-attaches FIELD to the RING-shape chain so
;;; every ring/comm-ring/integral-domain theorem auto-specializes back.
(def-view-as 'FIELD-AS-INTEGRAL-DOMAIN
  'FIELD            '(A ADD MUL NEG ZERO ONE)
  'INTEGRAL-DOMAIN  '(A ADD MUL NEG ZERO ONE))

;;; Every field is a Euclidean ring under the trivial degree function
;;; deg(x) = 0 — division is exact because every nonzero element is a unit:
;;; a = (a * b^-1) * b + 0.  The view component pattern is identical to
;;; FIELD-AS-INTEGRAL-DOMAIN since EUCLIDEAN-RING shares the RING shape.
(def-view-as 'FIELD-AS-EUCLIDEAN-RING
  'FIELD          '(A ADD MUL NEG ZERO ONE)
  'EUCLIDEAN-RING '(A ADD MUL NEG ZERO ONE))

(def-view-as 'EUCLIDEAN-RING-MULTIPLICATIVE-MONOID
  'EUCLIDEAN-RING '(A MUL ONE)
  'MONOID         '(A MUL E))

;;; -----------------------------------------------------------------------
;;; NORMED-FIELD as COMMUTATIVE-RING / INTEGRAL-DOMAIN
;;;
;;; NORMED-FIELD is a 7-slot shape; COMMUTATIVE-RING and INTEGRAL-DOMAIN are
;;; 6-slot predicates (length(s)=6).  A normed field therefore cannot satisfy
;;; them on the same tuple -- it reaches the ring world the way FIELD does
;;; (FIELD-AS-INTEGRAL-DOMAIN): by forgetting the norm slot and projecting
;;; slots 1..6 into a fresh 6-tuple.  These views replace the unsound
;;; same-tuple axioms normed-field-is-commutative-ring / -integral-domain
;;; (removed 2026-05-30) and auto-specialize every comm-ring / integral-domain
;;; theorem to RR-RING / CC-RING through the projection.

(def-view-as 'NORMED-FIELD-AS-COMMUTATIVE-RING
  'NORMED-FIELD     '(A ADD MUL NEG ZERO ONE)
  'COMMUTATIVE-RING '(A ADD MUL NEG ZERO ONE))

(def-view-as 'NORMED-FIELD-AS-INTEGRAL-DOMAIN
  'NORMED-FIELD    '(A ADD MUL NEG ZERO ONE)
  'INTEGRAL-DOMAIN '(A ADD MUL NEG ZERO ONE))

;;; NORMED-FIELD is its own 7-slot shape (carrier, ring ops, NRM at slot 7);
;;; no structural NON-ZERO / INV slots, so its multiplicative-group view is
;;; not registrable at the structure level here.  The "nonzero elements
;;; form a group" fact is captured semantically via normed-field-mul-inverses
;;; (an existence axiom in normed-field.scm); a view-as can be reintroduced
;;; once NORMED-FIELD's slot layout grows to carry NON-ZERO / INV.

;;; -----------------------------------------------------------------------
;;; The multiplicative group of a FIELD is implemented above by giving
;;; FIELD its own shape with NON-ZERO and INV as built-in slots; see
;;; field.scm for the design note.
