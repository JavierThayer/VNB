;;; winding-number.scm -- THE WINDING NUMBER AND THE CIRCLE AS A ROAD
;;; (complex-analysis.pdf ch. 3: Definition 3.26, equation (73); Example 3.13).
;;; DEFINITIONS ONLY; every law is PROVEN in theorem-library/winding-number-laws.scm.
;;; Agent CA-1 of the October roadmap, 2026-10-03.
;;;
;;; THE DECISION (the user, docs/roadmap-2026-10-03.md, decision 1): the winding number
;;; is DEFINED by the integral, (73) of the notes,
;;;
;;;     ind(gamma, u) = (1 / (2 pi i)) int_gamma dz / (z - u),
;;;
;;; and its integrality (Proposition 3.27) is a theorem of the arc, not a prerequisite.
;;;
;;;     WINDING(p, d, a, b, z)   recip((2 pi) i) * LINE-INT(w |-> recip(w - z), p, d, a, b),
;;;                              the integrand a VNB-LAMBDA over CC \ {z}
;;;     CIRCLE-PATH(c, r)        t |-> c + r exp(i t) on [0, 2 pi]   (Example 3.13)
;;;     CIRCLE-DERIV(c, r)       t |-> i (r exp(i t)) on [0, 2 pi], its derivative
;;;
;;; STATEMENT CHECKS (CLAUDE.md, the species of false or underdetermined statement).
;;; (1) WINDING is a TERM: it may fail to denote.  LINE-INT is defined where the road's
;;;     integrand has primitives, which the laws earn from a hypothesis (z off the trace:
;;;     `winding-in-cc').  Nothing here asserts an equation.  The road is the notes' path
;;;     gamma; Dieudonne's road carries its derivative explicitly (path-integral.scm), so
;;;     the winding number takes FIVE arguments, the road (p, d) on [a, b] and the point.
;;;     The notes ask gamma to be CLOSED; the definition does not, exactly as (73) does
;;;     not need it to make sense: closedness is a hypothesis of the laws that need it.
;;; (2) THE INTEGRAND'S DOMAIN is CC \ {z} (DIFFERENCE CC (SINGLETON z)), the largest set
;;;     on which w |-> 1/(w - z) is holomorphic.  A member of FUN(A, B) is defined exactly
;;;     on A, so the laws carry `not(z in trace)', which puts the trace inside the domain
;;;     (statement check (8) of path-integral.scm).
;;; (3) 2 pi i is written (* (* 2 PI) +i), the spelling of `cc-exp-two-pi-i' and of
;;;     `cc-exp-one-iff'; `+i' is the reader's complex literal, printed `1i'.
;;; (4) THE CIRCLE is parametrised on [0, 2 pi] exactly as Example 3.13 writes it,
;;;     gamma(t) = a + R exp(i t); the centre is a complex c, the radius a real r.  Its
;;;     derivative is written i (r exp(i t)), so that the winding integrand at the centre,
;;;     recip(gamma(t) - c) * gamma'(t), is recip(X) * (i X) with X = r exp(i t).  Nothing
;;;     here says r > 0: the laws carry it.  CIRCLE-DERIV takes the centre although its
;;;     value does not read it, so that a circle and its derivative are written with the
;;;     same arguments, as SEG-PATH(p, q) and SEG-DERIV(p, q) are.
;;; (5) BINDERS: wnw_ (the integrand), wnt_ (the circle's parameter); parameters wnp_ wnd_
;;;     wna_ wnb_ wnz_ wnc_ wnr_.  None folds onto a class name, an accessor or a
;;;     registered constant, and no other body or driver in the tree binds a wn*_ name.
;;;
;;; Dependencies: path-integral.scm (LINE-INT), cc-elementary.scm (CC-EXP), cc-pi.scm
;;; (PI), extreme-value.scm (CCINT), difference/singleton.  Load slot: after
;;; structure-library/cc-pi.

(def-functoid 'WINDING '(wnp_ wnd_ wna_ wnb_ wnz_)
  '(* (recip (* (* 2 PI) +i))
      (LINE-INT (VNB-LAMBDA wnw_ (DIFFERENCE CC (SINGLETON wnz_)) (recip (- wnw_ wnz_)))
                wnp_ wnd_ wna_ wnb_)))

(notation! 'WINDING 'kind 'functoid 'arity 5
           'english "the winding number about $5 of the road $1 with derivative $2 on [$3, $4]")

(def-functoid 'CIRCLE-PATH '(wnc_ wnr_)
  '(VNB-LAMBDA wnt_ (CCINT 0 (* 2 PI)) (+ wnc_ (* wnr_ (CC-EXP (* +i wnt_))))))

(notation! 'CIRCLE-PATH 'kind 'functoid 'arity 2
           'english "the circle of centre $1 and radius $2")

(def-functoid 'CIRCLE-DERIV '(wnc_ wnr_)
  '(VNB-LAMBDA wnt_ (CCINT 0 (* 2 PI)) (* +i (* wnr_ (CC-EXP (* +i wnt_))))))

(notation! 'CIRCLE-DERIV 'kind 'functoid 'arity 2
           'english "the derivative of the circle of centre $1 and radius $2")
