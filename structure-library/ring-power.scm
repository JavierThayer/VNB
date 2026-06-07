;;; ring-power.scm -- RING-POWER: the natural-number power x^n in a commutative ring.
;;;
;;; A thin convenience wrapper over the monoid power MPOW (monoid-power.scm).
;;; A commutative ring R's multiplicative part is the commutative monoid
;;; COMMUTATIVE-RING-MULTIPLICATIVE-CM(R) (views.scm) = [(A R), (MUL R), (ONE R)],
;;; so x^n in R is just MPOW on that monoid:
;;;
;;;   RING-POWER(R, x, n) = MPOW(COMMUTATIVE-RING-MULTIPLICATIVE-CM(R), x, n)
;;;
;;; The view identifies E |-> (ONE R), MUL |-> (MUL R), A |-> (A R), so every
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

(def-functoid 'RING-POWER '(R x n)
  '(MPOW (COMMUTATIVE-RING-MULTIPLICATIVE-CM R) x n))

;;; x^0 = 1 (the ring's ONE).  mpow-zero is unconditional; the view gives
;;; E(COMMUTATIVE-RING-MULTIPLICATIVE-CM R) = (ONE R).
(support 'ring-power-zero
  '(FORALL R (FORALL x (= (RING-POWER R x 0) (ONE R)))))
(warrant! 'ring-power-zero 'informal
  "mpow-zero: MPOW(m,x,0)=E(m); the view's E|->ONE slot gives E(COMMUTATIVE-RING-MULTIPLICATIVE-CM R)=(ONE R).")

;;; x^1 = x.  mpow-one (uses the right-identity law, hence the typing).
(support 'ring-power-one
  '(FORALL R (IMPLIES (IS-COMMUTATIVE-RING R)
     (FORALL x (IMPLIES (IN x (A R))
       (= (RING-POWER R x 1) x))))))
(warrant! 'ring-power-one 'informal
  "mpow-one on the multiplicative monoid: x^1 = MUL(x, x^0) = MUL(x, ONE) = x by the right-identity law.")

;;; Carrier closure: x^n stays in A(R).  mpow-type via the view (A|->A).
(support 'ring-power-type
  '(FORALL R (IMPLIES (IS-COMMUTATIVE-RING R)
     (FORALL x (IMPLIES (IN x (A R))
       (FORALL n (IMPLIES (IN n NN)
         (IN (RING-POWER R x n) (A R)))))))))
(warrant! 'ring-power-type 'informal
  "mpow-type on COMMUTATIVE-RING-MULTIPLICATIVE-CM(R): NN induction, base (ONE R) in A(R), step closes under (MUL R).")

;;; x^(j+k) = x^j * x^k.  mpow-add -- the monoid-hom law, no commutativity.
(support 'ring-power-add
  '(FORALL R (IMPLIES (IS-COMMUTATIVE-RING R)
     (FORALL x (IMPLIES (IN x (A R))
       (FORALL j (IMPLIES (IN j NN)
         (FORALL k (IMPLIES (IN k NN)
           (= (RING-POWER R x (+ j k))
              ((MUL R) (RING-POWER R x j) (RING-POWER R x k))))))))))))
(warrant! 'ring-power-add 'informal
  "mpow-add: n|->x^n is a monoid hom (NN,+,0)->((A R),(MUL R),(ONE R)).  NN induction on k; no commutativity used.")

;;; (x*y)^n = x^n * y^n.  mpow-mult -- needs the multiplicative monoid to be
;;; commutative, which is exactly IS-COMMUTATIVE-RING(R).
(support 'ring-power-mult
  '(FORALL R (IMPLIES (IS-COMMUTATIVE-RING R)
     (FORALL x (IMPLIES (IN x (A R))
       (FORALL y (IMPLIES (IN y (A R))
         (FORALL n (IMPLIES (IN n NN)
           (= (RING-POWER R ((MUL R) x y) n)
              ((MUL R) (RING-POWER R x n) (RING-POWER R y n))))))))))))
(warrant! 'ring-power-mult 'informal
  "mpow-mult on COMMUTATIVE-RING-MULTIPLICATIVE-CM(R); commutativity of (MUL R) is exactly IS-COMMUTATIVE-RING(R).")
