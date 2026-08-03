;;; theorem-library/fin-enum-is-bijection.scm
;;;
;;; fin-enum-is-bijection:  FIN-ENUM(S) is a bijection
;;; ORD-SEGMENT(|S|) -> S for any finite set S.  Central fact about
;;; FIN-ENUM; foundational for finsum machinery.
;;;
;;; PSS-promoted 2026-05-27 from proven-theorems.scm.  Original proof
;;; script archived in archive/proven-theorems-archive.scm.

(support 'fin-enum-is-bijection
  '(FORALL S
     (IMPLIES (IN S SET)
     (IMPLIES (IN (CARD S) NN)
       (IN (FIN-ENUM S) (BIJECTION (ORD-SEGMENT (CARD S)) S))))))

(warrant! 'fin-enum-is-bijection 'informal
  "Mechanically proven before the 2026-05-27 PSS promotion; script archived at
   archive/proven-theorems-archive.scm (prove-and-install! 'fin-enum-is-bijection).
   FIN-ENUM(S) is the chosen enumeration of a finite S, and the choice is made
   from the bijections ORD-SEGMENT(|S|) -> S, which card-finite-bij
   (cardinality.scm) makes non-empty.  Foundational for the whole finsum layer.
   Archive predates the E -> IDEN rename and the ==-sweep.")
