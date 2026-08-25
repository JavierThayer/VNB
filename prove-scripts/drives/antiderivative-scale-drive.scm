;;; antiderivative-scale-drive.scm -- CLOSED 2026-08-25.  Kept as a record of
;;; what the hand-off was and what closed it; it is not a live leaf and it is
;;; not loaded.
;;;
;;; THE HAND-OFF (2026-08-24) was Proposition 4.8's SCALAR half,
;;;
;;;   c in RR,  IS-ANTIDERIVATIVE(f, phi, a, b)
;;;      ==>  IS-ANTIDERIVATIVE( x |-> c.f(x),  x |-> c.phi(x),  a, b )
;;;
;;; and the reason it was handed off was not the driver: two lemmas about the
;;; term x |-> c.f(x) were missing from the tree, where the SUM half needed
;;; neither because `sum-lam-in-fun' / `sum-continuous-at' already existed.
;;;
;;; BOTH ARE NOW PROVED, `modulo 0', in theorem-library/continuity-scale.scm:
;;;
;;;   scale-lam-in-fun     c in RR, f in FUN(RR,RR)
;;;                          =>  (VNB-LAMBDA x RR (* c (f x))) in FUN(RR,RR)
;;;                        Proved directly, the `sum-lam-in-fun' shape with one
;;;                        factor constant.  The derivative route was checked and
;;;                        does NOT work: `deriv-scalar-mult' + `diff-at-in-fun'
;;;                        types the term only where f is differentiable, and
;;;                        Def 4.6 gives that on the OPEN interval only.
;;;   scale-continuous-at  const-continuous-at, then product-continuous-at
;;;                        against the constant lambda, then
;;;                        cont-transfer-ptwise-eq to cross from
;;;                        x |-> (K x).(f x) to x |-> c.f(x).  No eps/delta.
;;;
;;; and the theorem itself is `antiderivative-scale' in
;;; theorem-library/antiderivative.scm (section 6), with `antiderivable-scale'
;;; one level up -- so Proposition 4.8 entire: the antiderivable functions on
;;; [a,b] are a vector space.  Both `modulo 0'.  Prop 4.12's scalar half,
;;; `c-int-scale', is in theorem-library/c-int.scm.
;;;
;;; The driver that was here is the one now in antiderivative.scm section 6,
;;; with the two `#t' placeholders replaced by the citations above.
