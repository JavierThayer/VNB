;;; theorem-library/card-singleton.scm
;;;
;;; card-singleton:  the cardinality of a singleton is 1.
;;; Note: in VNB the singleton {x} is represented as (PAIR x x) (the
;;; Kuratowski-pair convention degenerates to {{x}}), and 1 = succ 0.
;;;
;;; PSS-promoted 2026-05-27 from proven-theorems.scm.  Original proof
;;; script archived in archive/proven-theorems-archive.scm.

(support 'card-singleton
  '(FORALL x (IMPLIES (IN x SET)
     (= (CARD (PAIR x x)) (succ 0)))))
