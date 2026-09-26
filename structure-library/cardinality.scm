;;; cardinality.scm -- CARD, the cardinality of a set, DEFINED.
;;;
;;;     CARD(A)  ==  IOTA alpha.  alpha in ORD
;;;                and  forsome phi. phi in BIJECTION(A, ORD-SEGMENT(alpha))
;;;                and  forall beta with ORD-LT(beta, alpha).
;;;                       not forsome psi. psi in BIJECTION(A, ORD-SEGMENT(beta))
;;;
;;; "the least ordinal whose segment A bijects onto" -- the meaning this file's
;;; header has stated since it was written.
;;;
;;; Dependencies: ordinals.scm (ORD, ORD-SEGMENT, ORD-LT), bijection.scm
;;; (BIJECTION), number-systems.scm (NN).  Nothing else: the definition is a
;;; description and costs no axiom.
;;;
;;; =======================================================================
;;; WHAT THIS FILE USED TO BE, AND WHY IT CHANGED (2026-09-20, the user's
;;; decision: "rename CARD-STAR to CARD and drop the axioms").
;;;
;;; From 2026-07-27 to 2026-09-19 CARD was a PRIMITIVE notion and this file
;;; installed seven axioms about it inside a `primitive' provenance block --
;;; card-in-ord, card-empty, card-insert, card-segment, card-finite-bij,
;;; card-union-disjoint, finite-set-induction -- with an eighth,
;;; card-image-injection, in injection.scm.  `primitive' contributes {} to
;;; every bill, so those eight facts were trusted base: a false one would have
;;; been invisible to the ledger, and one of them (card-insert, unguarded in A)
;;; WAS false of the intended meaning until its finiteness guard was added on
;;; 2026-09-18.
;;;
;;; All eight are now THEOREMS of the definition above, under their old names
;;; and in their old shapes, so no citation anywhere in the tree changed:
;;;
;;;   card-segment            theorem-library/card-defined.scm
;;;   card-empty              theorem-library/card-finite.scm
;;;   finite-set-induction    theorem-library/rake-card-star-laws.scm
;;;   card-in-ord, card-insert, card-finite-bij, card-union-disjoint,
;;;   card-image-injection    theorem-library/card-laws.scm
;;;
;;; and `well-ordering-principle', which used to be an asserted PSS entry
;;; STATED with the axiomatised CARD, is proven in
;;; theorem-library/rake-ord-pigeonhole.scm.  The whole development, and the
;;; load-order surgery it needed, is docs/card-defined-2026-09-20.md.
;;;
;;; THE FINITENESS GUARD ON card-insert IS REAL AND STAYS.  For A = omega and
;;; x = omega, A u {x} is omega + 1, which bijects with omega, so
;;; CARD(A u {x}) = omega while succ_ORD(CARD A) = omega + 1.  The equation
;;; holds exactly when A is finite, which is what (IN (CARD A) NN) says.  The
;;; same remark applies to card-union-disjoint and finite-set-induction, and
;;; each carries its guard.
;;; =======================================================================

(def-functoid 'CARD '(a_)
  '(IOTA alpha
     (AND (IN alpha ORD)
          (AND (FORSOME phi (IN phi (BIJECTION a_ (ORD-SEGMENT alpha))))
               (FORALL beta
                 (IMPLIES (ORD-LT beta alpha)
                   (NOT (FORSOME psi (IN psi (BIJECTION a_ (ORD-SEGMENT beta)))))))))))
(notation! 'CARD 'kind 'functoid 'arity 1
           'english "the cardinal of $1")

;;; THE DIRECTION OF THE BIJECTION IS A -> SEGMENT, and that is a decision, not
;;; a coin flip (user, 2026-08-05).  For A = ORD-SEGMENT(n), killing a candidate
;;; beta < n then means refuting a bijection S(n) -> S(beta), which is IN
;;; PARTICULAR an injection S(n) -> S(beta) -- pigeonhole-segments-gen, applied
;;; directly.  Segment-first would instead need the bijection INVERTED, and the
;;; library's only inverse, INVERSE-BIJ (bijection.scm), is defined via CHOICE,
;;; which this track is meant not to need.
;;;
;;; The description denotes for EVERY set (card-body-exists,
;;; theorem-library/rake-ord-pigeonhole.scm, from Zermelo's theorem), so CARD is
;;; total on SET; `CARD(A)' for a proper class A is an IOTA that need not denote,
;;; exactly like any other description in the tree.
