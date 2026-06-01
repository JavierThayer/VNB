;;; theorem-library/enum-fam-in-fun.scm
;;;
;;; enum-fam-in-fun:  ENUM-FAM(ag, f, phi, n) is in FUN(NN, A(ag))
;;; whenever the inputs have the right types.  Type lemma for ENUM-FAM.
;;;
;;; PSS-promoted 2026-05-27 from proven-theorems.scm.  Original proof
;;; script archived in archive/proven-theorems-archive.scm.

(support 'enum-fam-in-fun
  '(FORALL n (IMPLIES (IN n NN)
     (FORALL ag (IMPLIES (IS-GROUP ag)
     (FORALL S (FORALL phi (IMPLIES (IN phi (FUN (ORD-SEGMENT n) S))
     (FORALL f (IMPLIES (IN f (FUN S (A ag)))
       (IN (ENUM-FAM ag f phi n) (FUN NN (A ag)))))))))))))
