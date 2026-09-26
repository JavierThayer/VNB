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

(warrant! 'card-singleton 'informal
  "Mechanically proven before the 2026-05-27 PSS promotion; script archived at
   archive/proven-theorems-archive.scm (prove-and-install! 'card-singleton).
   In VNB the singleton {x} is (PAIR x x) -- the Kuratowski convention
   degenerates to {{x}} -- and its cardinality is succ 0.  Archive predates the
   E -> IDEN rename and the ==-sweep, so it records the argument only.")
