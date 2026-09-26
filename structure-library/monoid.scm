;;; RETIRED 2026-09-17 (proven): comm-monoid-opr-comm (was an unwarranted axiom, no citers) --
;;; theorem-library/rake-finsum-core.scm
;;; RETIRED 2026-09-17 (proven): monoid-identity-in, monoid-carrier-closed-opr -- were UNWARRANTED
;;; axioms here; theorem-library/rake-algebra2.scm, projections of is-monoid-def, modulo 0.
;;; monoid.scm -- MONOID and COMM-MONOID structures
;;;
;;; MONOID: carrier CARR, operation OPR, identity IDEN.
;;; Accessor indices: CARR -> 1, OPR -> 2, IDEN -> 3.
;;; COMM-MONOID: same shape as MONOID with an extra commutativity axiom.

(declare-structure MONOID
  (carriers CARR)
  (op OPR (CARTESIAN CARR CARR) CARR)
  (constant IDEN CARR)
  (property is-associative OPR CARR)
  (property is-identity OPR IDEN CARR))

;;; forall s. IS-MONOID(s) => forall a,b,c in CARR(s). (a*b)*c = a*(b*c)
;;; monoid-assoc RETIRED 2026-09-18 (rake batch 5c): proven in theorem-library/rake-monoid-laws.scm

;;; forall s. IS-MONOID(s) => forall a in CARR(s). IDEN(s)*a = a
;;; monoid-left-id RETIRED 2026-09-18 (rake batch 5c): proven in theorem-library/rake-monoid-laws.scm

;;; forall s. IS-MONOID(s) => forall a in CARR(s). a*IDEN(s) = a
;;; monoid-right-id RETIRED 2026-09-18 (rake batch 5c): proven in theorem-library/rake-monoid-laws.scm

;;; IDEN(m) ∈ CARR(m) when IS-MONOID(m).
;;; DERIVED (REVIEW.md R-1): follows from the auto-generated IS-MONOID IFF.
;;; Carrier closed under OPR.
;;; DERIVED (REVIEW.md R-4): IS-MONOID IFF + fun-apply-type.
;;; -----------------------------------------------------------------------
;;; COMM-MONOID: commutative monoid -- a MONOID whose OPR is commutative.
;;; Same accessor layout as MONOID.

(declare-structure COMM-MONOID
  (carriers CARR)
  (op OPR (CARTESIAN CARR CARR) CARR)
  (constant IDEN CARR)
  (property is-associative OPR CARR)
  (property is-identity OPR IDEN CARR)
  (property is-commutative OPR CARR))

;;; Every commutative monoid is a monoid.  PROVEN modulo 0 in
;;; structure-library/subtype-laws.scm (the abelian-group-is-group shape: unfold
;;; IS-COMM-MONOID, and IS-MONOID's conjuncts are a subset of what falls out);
;;; asserted here, unwarranted, until 2026-08-10.


;;; Notation -- read by wff->english / the proof reader (operators.scm).
(notation! 'IS-MONOID               'noun "monoid" 'article "a")
