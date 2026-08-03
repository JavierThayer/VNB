;;; theorem-library/finsum-singleton.scm
;;;
;;; finsum-singleton:  FINSUM over a singleton {x} reduces to f(x).
;;;
;;; PSS-promoted 2026-05-27 from proven-theorems.scm.  Original proof
;;; script archived in archive/proven-theorems-archive.scm.

(support 'finsum-singleton
  '(FORALL ag (IMPLIES (IS-ABELIAN-GROUP ag)
     (FORALL x (IMPLIES (IN x SET)
     (FORALL f (IMPLIES (IN f (FUN (PAIR x x) (CARR ag)))
       (= (FINSUM ag f (PAIR x x)) (f x)))))))))

(warrant! 'finsum-singleton 'informal
  "Mechanically proven before the 2026-05-27 PSS promotion; script archived at
   archive/proven-theorems-archive.scm (prove-and-install! 'finsum-singleton).
   FINSUM over {x} = (PAIR x x) unfolds through card-singleton (|{x}| = 1) to a
   one-term SUM-AG, which is f(x).  Archive predates the E -> IDEN rename and
   the ==-sweep, so it records the argument and does not run as-is.")
