;;; integral-domain.scm -- INTEGRAL-DOMAIN: a commutative ring with ONE /= ZERO
;;; and no zero divisors.  Reuses the RING shape and accessors.
;;;
;;; See commutative-ring.scm for why IS-INTEGRAL-DOMAIN is a genuine IFF
;;; predicate rather than a def-structure shape check.  Dependencies:
;;; ring.scm, commutative-ring.scm.

;;; IS-INTEGRAL-DOMAIN: a commutative ring, nontrivial (ONE /= ZERO),
;;; with no zero divisors (a*b = 0  =>  a = 0 or b = 0).
(declare-structure INTEGRAL-DOMAIN
  (same-shape-as COMMUTATIVE-RING)
  (law (NOT (= (ONE s) (ZERO s))))
  (law (FORALL a (IMPLIES (IN a (CARR s))
         (FORALL b (IMPLIES (IN b (CARR s))
           (IMPLIES (= ((MUL s) a b) (ZERO s))
                    (OR (= a (ZERO s)) (= b (ZERO s))))))))))

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
;;; is-integral-domain-def, surfaced as a citable theorem.
(theory-add-axiom! *current-theory* 'integral-domain-nontrivial
  '(FORALL s (IMPLIES (IS-INTEGRAL-DOMAIN s) (NOT (= (ONE s) (ZERO s))))))

;;; The cancellation form of "no zero divisors", shaped for a forward `fact':
;;; a*b = 0 with b /= 0 forces a = 0.
(theory-add-axiom! *current-theory* 'integral-domain-cancel-zero
  '(FORALL s (IMPLIES (IS-INTEGRAL-DOMAIN s)
     (FORALL a (IMPLIES (IN a (CARR s))
     (FORALL b (IMPLIES (IN b (CARR s))
       (IMPLIES (= ((MUL s) a b) (ZERO s))
       (IMPLIES (NOT (= b (ZERO s)))
         (= a (ZERO s)))))))))))

;;; Notation -- read by wff->english / the proof reader (operators.scm).
(notation! 'IS-INTEGRAL-DOMAIN    'kind 'predicate 'arity 1 'noun "integral domain" 'article "an")
