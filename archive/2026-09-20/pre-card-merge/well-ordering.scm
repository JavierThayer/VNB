;;; theorem-library/well-ordering.scm
;;;
;;; The Well-Ordering Principle, as a Proof Support Set entry.
;;;
;;; For every set S, the half-open ordinal interval [0, CARD(S)) bijects
;;; with S.  Generalises card-finite-bij (cardinality.scm) by dropping
;;; the (IN (CARD A) NN) finiteness hypothesis; the witness bijection
;;; supplies the canonical enumeration that well-orders S.

(support 'well-ordering-principle
  '(FORALL S (IMPLIES (IN S SET)
      (FORSOME phi
        (IN phi (BIJECTION (ORD-SEGMENT (CARD S)) S))))))

(warrant! 'well-ordering-principle 'well-known
  "The cardinal-assignment half of the well-ordering theorem: every set bijects
   with ORD-SEGMENT of its cardinal.  Standard from the CHOICE axiom of the base
   theory (theory.scm), which is GLOBAL choice in the NBG/Bourbaki sense --
   strictly stronger than ZFC's -- via the usual transfinite enumeration.
   Generalises card-finite-bij (cardinality.scm) by dropping finiteness.  Never
   mechanised; there is no script for it in archive/proven-theorems-archive.scm.
   NOTE, for triage rather than for this warrant: CARD is AXIOMATISED in
   cardinality.scm, not defined as the least ordinal in bijection, so this
   statement is part of what gives CARD its meaning.  It belongs in the same
   bucket as the card-* axioms -- a candidate for the primitive shelf by an
   explicit foundational decision, not for a warrant.")
