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
