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
