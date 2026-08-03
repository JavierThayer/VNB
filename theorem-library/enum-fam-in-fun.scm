;;; theorem-library/enum-fam-in-fun.scm
;;;
;;; enum-fam-in-fun:  ENUM-FAM(ag, f, phi, n) is in FUN(NN, CARR(ag))
;;; whenever the inputs have the right types.  Type lemma for ENUM-FAM.
;;;
;;; PSS-promoted 2026-05-27 from proven-theorems.scm.  Original proof
;;; script archived in archive/proven-theorems-archive.scm.

(support 'enum-fam-in-fun
  '(FORALL n (IMPLIES (IN n NN)
     (FORALL ag (IMPLIES (IS-GROUP ag)
     (FORALL S (FORALL phi (IMPLIES (IN phi (FUN (ORD-SEGMENT n) S))
     (FORALL f (IMPLIES (IN f (FUN S (CARR ag)))
       (IN (ENUM-FAM ag f phi n) (FUN NN (CARR ag)))))))))))))

(warrant! 'enum-fam-in-fun 'informal
  "Mechanically proven before the 2026-05-27 PSS promotion; script archived at
   archive/proven-theorems-archive.scm (prove-and-install! 'enum-fam-in-fun).
   ENUM-FAM(ag,f,phi,n) is f composed with phi below n and the identity of ag
   above it, so it is total on NN and lands in CARR(ag) either way.  Archive
   predates the E -> IDEN rename and the ==-sweep.")
