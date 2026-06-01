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
