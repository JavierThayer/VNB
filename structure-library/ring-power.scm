;;; RETIRED 2026-09-17 (proven, rake batch P): ring-power-one, ring-power-add, ring-power-mult --
;;; theorem-library/rake-combinatorics.scm, modulo 0 (mpow laws through the multiplicative view).
;;; RETIRED 2026-09-17 (proven): ring-power-type -- theorem-library/rake-finsum-typing.scm
;;; ring-power.scm -- RING-POWER: the natural-number power x^n in a commutative ring.
;;;
;;; A thin convenience wrapper over the monoid power MPOW (monoid-power.scm).
;;; A commutative ring R's multiplicative part is the commutative monoid
;;; COMMUTATIVE-RING-MULTIPLICATIVE-CM(R) (views.scm) = [(CARR R), (MUL R), (ONE R)],
;;; so x^n in R is just MPOW on that monoid:
;;;
;;;   RING-POWER(R, x, n) = MPOW(COMMUTATIVE-RING-MULTIPLICATIVE-CM(R), x, n)
;;;
;;; The view identifies E |-> (ONE R), MUL |-> (MUL R), A |-> (CARR R), so every
;;; MPOW law restates directly in ring vocabulary.  The laws below are asserted
;;; as warranted support in the library-build phase [[feedback-library-axioms-fine]],
;;; each warrant naming the MPOW law it specializes; unfolding RING-POWER (its
;;; def-functoid macete) recovers the raw MPOW form for anything not listed.
;;;
;;; Note for the simplifier: RING-POWER is OPAQUE to (crs) -- the commutative
;;; normalizer knows ADD/MUL/NEG/ZERO/ONE only.  The ring-expression copilot
;;; (interactive.scm) therefore expands a LITERAL exponent x^k into k-fold
;;; multiplication so crs can normalize it, and emits RING-POWER only for a
;;; symbolic exponent x^n where it cannot.
;;;
;;; Dependencies: monoid-power.scm (MPOW + laws), views.scm
;;; (COMMUTATIVE-RING-MULTIPLICATIVE-CM), commutative-ring.scm, ring.scm.
;;; RETIRED 2026-09-14 (proven): ring-power-zero -- theorem-library/ring-zero-one-power.scm

(def-functoid 'RING-POWER '(R x n)
  '(MPOW (COMMUTATIVE-RING-MULTIPLICATIVE-CM R) x n))

;;; x^0 = 1 (the ring's ONE).  mpow-zero is unconditional; the view gives
;;; IDEN(COMMUTATIVE-RING-MULTIPLICATIVE-CM R) = (ONE R).

;;; x^1 = x.  mpow-one (uses the right-identity law, hence the typing).

;;; Carrier closure: x^n stays in CARR(R).  mpow-type via the view (A|->A).

;;; x^(j+k) = x^j * x^k.  mpow-add -- the monoid-hom law, no commutativity.

;;; (x*y)^n = x^n * y^n.  mpow-mult -- needs the multiplicative monoid to be
;;; commutative, which is exactly IS-COMMUTATIVE-RING(R).
