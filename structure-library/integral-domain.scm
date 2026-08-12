;;; integral-domain.scm -- INTEGRAL-DOMAIN: a commutative ring with ONE /= ZERO
;;; and no zero divisors.  Reuses the RING shape and accessors.
;;;
;;; See commutative-ring.scm for why IS-INTEGRAL-DOMAIN is a genuine IFF
;;; predicate rather than a def-structure shape check.  Dependencies:
;;; ring.scm, commutative-ring.scm.

;;; IS-INTEGRAL-DOMAIN: a commutative ring, nontrivial (ONE /= ZERO),
;;; with no zero divisors (a*b = 0  =>  a = 0 or b = 0).
(declare-structure INTEGRAL-DOMAIN
  (instance-var s)
  (same-shape-as COMMUTATIVE-RING)
  (law "not(one(s) = zero(s))")
  (law "forall([a in carr(s), b in carr(s)],
          mul(s)(a, b) = zero(s) implies (a = zero(s) or b = zero(s)))"))

;;; Relation: every integral domain is a commutative ring.
;;; PROVEN modulo 0 via mac-h in structure-library/subtype-laws.scm (unfold
;;; is-integral-domain-def; IS-COMMUTATIVE-RING is a literal RHS conjunct --
;;; guaranteed by (same-shape-as COMMUTATIVE-RING) above).  It used to be
;;; ASSERTED here, alone among the three: hand-assembly drift.

;;; Associated proper class INTEGRAL-DOMAIN = { s | IS-INTEGRAL-DOMAIN(s) }.
;;; See commutative-ring.scm for the NAME-class rationale.  Parent-class
;;; reading: s in INTEGRAL-DOMAIN <=> s in COMMUTATIVE-RING and ONE/=ZERO and
;;; no zero divisors.

;;; Projection: an integral domain is nontrivial (1 /= 0).  A conjunct of
;;; is-integral-domain-def, surfaced as a citable theorem -- and since
;;; 2026-08-10 PROVEN as one, in structure-library/integral-domain-laws.scm,
;;; rather than asserted here.  The old comment on the axiom said "a conjunct of
;;; is-integral-domain-def", which is the proof written in prose and not run.

;;; The cancellation form of "no zero divisors" (a*b = 0 with b /= 0 forces
;;; a = 0), shaped for a forward `fact', is NOT asserted here.  It is PROVEN in
;;; structure-library/integral-domain-laws.scm, which unfolds the
;;; is-integral-domain-def conjunct it is an instance of.  That file had existed
;;; for weeks without being listed in load.scm, so the proof never ran and this
;;; axiom stood in its place, unwarranted, in seven bills (found 2026-08-10).

;;; Notation -- read by wff->english / the proof reader (operators.scm).
(notation! 'IS-INTEGRAL-DOMAIN    'kind 'predicate 'arity 1 'noun "integral domain" 'article "an")
