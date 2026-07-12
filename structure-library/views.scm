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
;;; AG's slot order from its def-structure-from-clauses is (CARR MUL IDEN INV)
;;; -- the identity constant `E` comes before the unary inverse op `INV`.
;;; So the additive view maps:
;;;   ring's A    -> AG's A
;;;   ring's ADD  -> AG's MUL
;;;   ring's ZERO -> AG's E
;;;   ring's NEG  -> AG's INV

(def-view-as 'RING-ADDITIVE-AG
  'RING          '(CARR ADD ZERO NEG)
  'ABELIAN-GROUP '(CARR OPR IDEN INV))

;;; -----------------------------------------------------------------------
;;; RING as multiplicative MONOID
;;;
;;; A ring's multiplicative structure (A, MUL, ONE) is a monoid.
;;; (Not a group: nonzero elements lack inverses in general rings.)
;;; MONOID's slot order is (CARR OPR IDEN), so the multiplicative view maps:
;;;   ring's A   -> MONOID's A
;;;   ring's OPR -> MONOID's OPR
;;;   ring's ONE -> MONOID's E

(def-view-as 'RING-MULTIPLICATIVE-MONOID
  'RING   '(CARR MUL ONE)
  'MONOID '(CARR OPR IDEN))

;;; -----------------------------------------------------------------------
;;; ABELIAN-GROUP as MONOID
;;;
;;; Forgetting the inverse, an abelian group (A, MUL, E, INV) is a monoid
;;; (A, OPR, E).  ABELIAN-GROUP's first three slots already are MONOID's
;;; three slots in the same order, so the view just projects them.  This is
;;; what lets the monoid power MPOW (monoid-power.scm) act on an abelian
;;; group: under the ADDITIVE view of a ring this MPOW is the n-fold sum
;;; n.a, the NN-action that zz-action.scm extends to a ZZ action.
;;;
;;; Auto-specializes every MONOID theorem (mpow-type, mpow-add, ...) to
;;; ABELIAN-GROUP, so the NN-power machinery is immediately available on
;;; groups without restating it.
(def-view-as 'ABELIAN-GROUP-AS-MONOID
  'ABELIAN-GROUP '(CARR OPR IDEN)
  'MONOID        '(CARR OPR IDEN))

;;; -----------------------------------------------------------------------
;;; Additive abelian-group views for RING's definitional refinements
;;;
;;; COMMUTATIVE-RING, INTEGRAL-DOMAIN, EUCLIDEAN-RING all share the RING
;;; shape (6 slots), so the additive view of each is the *identical*
;;; constructor RING-ADDITIVE-AG, only with a stronger source predicate.
;;; Because IS-INTEGRAL-DOMAIN ⇒ IS-RING etc. (the same-shape inclusion
;;; axioms), the RING-ADDITIVE-AG functoid and its auto-specialized AG
;;; theorems already apply to any integral domain / Euclidean ring via a
;;; one-step backchain on the inclusion.  So the standalone
;;; INTEGRAL-DOMAIN-ADDITIVE-AG / EUCLIDEAN-RING-ADDITIVE-AG views were
;;; redundant and were removed 2026-06-06 (both had zero references).
;;;
;;; COMMUTATIVE-RING-ADDITIVE-AG is kept: same redundancy in principle, but
;;; it is a live functoid in prod-of-sums-expansion (theorem-library/
;;; prod-of-sums.scm), so its name is load-bearing, not just a lemma handle.
;;;
;;; FIELD-ADDITIVE-AG / NORMED-FIELD-ADDITIVE-AG are NOT same-shape sub-types
;;; of RING (FIELD is 8-slot, NORMED-FIELD 7-slot), so the base view +
;;; inclusion does NOT regenerate their AG theorems — they earn their own
;;; declaration.  (NORMED-FIELD-ADDITIVE-AG is also live in power-series.scm.)

(def-view-as 'COMMUTATIVE-RING-ADDITIVE-AG
  'COMMUTATIVE-RING '(CARR ADD ZERO NEG)
  'ABELIAN-GROUP    '(CARR OPR IDEN INV))

(def-view-as 'FIELD-ADDITIVE-AG
  'FIELD         '(CARR ADD ZERO NEG)
  'ABELIAN-GROUP '(CARR OPR IDEN INV))

(def-view-as 'NORMED-FIELD-ADDITIVE-AG
  'NORMED-FIELD  '(CARR ADD ZERO NEG)
  'ABELIAN-GROUP '(CARR OPR IDEN INV))

;;; The underlying abelian group of a NORMED-AG: forget the norm slot.
;;; Slots align directly (NORMED-AG was shaped that way), so this is the
;;; identity projection on slots 1-4.  This view is the bridge that lets
;;; FINSUM / sum-ag-permutation-invariance sum a normed-AG-valued function.
(def-view-as 'NORMED-AG-AS-ABELIAN-GROUP
  'NORMED-AG     '(CARR OPR IDEN INV)
  'ABELIAN-GROUP '(CARR OPR IDEN INV))

;;; -----------------------------------------------------------------------
;;; Multiplicative monoid views for RING's definitional refinements
;;;
;;; In a general RING, the multiplicative structure (A, MUL, ONE) forms only
;;; a monoid (no inverses).  Even in INTEGRAL-DOMAIN and EUCLIDEAN-RING this
;;; is true.  In FIELD/NORMED-FIELD the *nonzero* part forms a group, but
;;; that requires a subset carrier — see views.scm comment block below on
;;; "the group of invertible elements" — and isn't expressible in the
;;; current def-view-as form.
;;;
;;; The bare-MONOID multiplicative views for COMMUTATIVE-RING /
;;; INTEGRAL-DOMAIN / EUCLIDEAN-RING were removed 2026-06-06: same-shape
;;; refinements of RING, so RING-MULTIPLICATIVE-MONOID + the IS-X ⇒ IS-RING
;;; inclusion already cover them, and all three were unreferenced.  (The
;;; COMMUTATIVE-RING-MULTIPLICATIVE-CM view below is NOT one of these — it
;;; reaches the stronger COMM-MONOID target and is live in finprod.)

;;; A COMMUTATIVE ring's multiplicative structure (A, MUL, ONE) is a
;;; *commutative* monoid -- the comm-ring property is exactly MUL-commutativity.
;;; This is the view the finite PRODUCT rides on: PROD-RING(R,f,X) =
;;; FINSUM(COMMUTATIVE-RING-MULTIPLICATIVE-CM(R), f, X) (finprod.scm), so the
;;; whole finsum-comm-monoid kit (closure / permutation-invariance /
;;; enumeration-independence) auto-specializes to commutative-ring products.
;;; Distinct from COMMUTATIVE-RING-MULTIPLICATIVE-MONOID above, which lands in
;;; bare MONOID (no commutativity) -- this one reaches COMM-MONOID.
(def-view-as 'COMMUTATIVE-RING-MULTIPLICATIVE-CM
  'COMMUTATIVE-RING '(CARR MUL ONE)
  'COMM-MONOID      '(CARR OPR IDEN))

;;; FIELD now carries NON-ZERO and RECIP as built-in slots (see field.scm
;;; reshape), so its nonzero elements form a genuine group, not just a
;;; monoid.  This replaces the old FIELD-MULTIPLICATIVE-MONOID view.
(def-view-as 'FIELD-MULTIPLICATIVE-GROUP
  'FIELD '(NON-ZERO MUL ONE RECIP)
  'GROUP '(CARR OPR IDEN INV))

;;; Forget the extra slots to recover the integral-domain (and hence ring)
;;; view of a field.  This re-attaches FIELD to the RING-shape chain so
;;; every ring/comm-ring/integral-domain theorem auto-specializes back.
(def-view-as 'FIELD-AS-INTEGRAL-DOMAIN
  'FIELD            '(CARR ADD MUL NEG ZERO ONE)
  'INTEGRAL-DOMAIN  '(CARR ADD MUL NEG ZERO ONE))

;;; Every field is a Euclidean ring under the trivial degree function
;;; deg(x) = 0 — division is exact because every nonzero element is a unit:
;;; a = (a * b^-1) * b + 0.  The view component pattern is identical to
;;; FIELD-AS-INTEGRAL-DOMAIN since EUCLIDEAN-RING shares the RING shape.
(def-view-as 'FIELD-AS-EUCLIDEAN-RING
  'FIELD          '(CARR ADD MUL NEG ZERO ONE)
  'EUCLIDEAN-RING '(CARR ADD MUL NEG ZERO ONE))

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
;;; theorem to RR-NORMED-FIELD / CC-NORMED-FIELD through the projection.

(def-view-as 'NORMED-FIELD-AS-COMMUTATIVE-RING
  'NORMED-FIELD     '(CARR ADD MUL NEG ZERO ONE)
  'COMMUTATIVE-RING '(CARR ADD MUL NEG ZERO ONE))

(def-view-as 'NORMED-FIELD-AS-INTEGRAL-DOMAIN
  'NORMED-FIELD    '(CARR ADD MUL NEG ZERO ONE)
  'INTEGRAL-DOMAIN '(CARR ADD MUL NEG ZERO ONE))

;;; NORMED-FIELD is its own 7-slot shape (carrier, ring ops, NRM at slot 7);
;;; no structural NON-ZERO / INV slots, so its multiplicative-group view is
;;; not registrable at the structure level here.  The "nonzero elements
;;; form a group" fact is captured semantically via normed-field-mul-inverses
;;; (an existence axiom in normed-field.scm); a view-as can be reintroduced
;;; once NORMED-FIELD's slot layout grows to carry NON-ZERO / INV.

;;; -----------------------------------------------------------------------
;;; A MODULE's vectors form an abelian group
;;;
;;; The vector part (VEC, VADD, VZERO, VNEG) of a module is an abelian group.
;;; This is the bridge the 0.x=0 proof needed: it specializes every
;;; ABELIAN-GROUP theorem (cancellation, idempotent-is-id, the monoid-derived
;;; identity laws, ...) to a module's additive structure, so module proofs cite
;;; ready-made group lemmas instead of re-deriving them from the raw property
;;; predicates folded into IS-MODULE.
(def-view-as 'MODULE-VECTOR-AG
  'MODULE        '(VEC VADD VZERO VNEG)
  'ABELIAN-GROUP '(CARR   OPR  IDEN     INV))

;;; -----------------------------------------------------------------------
;;; The multiplicative group of a FIELD is implemented above by giving
;;; FIELD its own shape with NON-ZERO and RECIP as built-in slots; see
;;; field.scm for the design note.
