;;; poly-is-ring-proof.scm -- POLY(A) is a ring when A is a ring.
;;;
;;; The first REAL proof about the monoid-algebra construction (the ring laws
;;; themselves are seeded, pending the convolution-associativity grind).  It is
;;; a one-instantiation derivation: POLY(A) = MONALG(A, NN-ADD-MONOID), and
;;; monalg-is-ring gives MONALG(A,M) a ring for any monoid M, so the only work
;;; is discharging IS-MONOID(NN-ADD-MONOID) -- which is comm-monoid-is-monoid
;;; applied to the nn-add-monoid-is-comm-monoid axiom.
;;;
;;; Its bill is monalg-is-ring (reference) + the two NN-monoid facts, NOT the
;;; whole convolution: this proof is honest about resting on the seeded ring
;;; structure, and will tighten automatically the day monalg-is-ring is proved.

(sp (make-wff '(FORALL A (IMPLIES (IS-RING A) (IS-RING (POLY A))))))
(di)                                   ; strip forall A
(di)                                   ; assume IS-RING a; goal IS-RING(POLY a)
(mac 'poly)                            ; POLY a -> MONALG(a, NN-ADD-MONOID)
(fact 'nn-add-monoid-is-comm-monoid)   ; IS-COMM-MONOID(NN-ADD-MONOID)
(fact 'comm-monoid-is-monoid 'NN-ADD-MONOID)   ; -> IS-MONOID(NN-ADD-MONOID)
(fact 'monalg-is-ring 'A 'NN-ADD-MONOID)       ; -> IS-RING(MONALG a NN-ADD-MONOID)
(ass)
(qed 'poly-is-ring)
