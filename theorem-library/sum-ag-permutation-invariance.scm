;;; theorem-library/sum-ag-permutation-invariance.scm
;;;
;;; Permutation invariance of finite abelian-group sums, as a Proof
;;; Support Set entry.
;;;
;;;   SUM-AG(ag, g, n) = SUM-AG(ag, h, n)
;;;     whenever h(i) = g(phi(i)) on ORD-SEGMENT(n) for some bijection
;;;     phi : ORD-SEGMENT(n) -> ORD-SEGMENT(n).
;;;
;;; Originally proven in proven-theorems.scm via NN induction whose step
;;; case used sum-ag-splice-out + the IH with the induced permutation
;;; INVERSE-BIJ(DELETE-AT inv K).  That proof and its supporting
;;; intermediates (sum-ag-splice-out, sum-ag-congruence, ag-mul-rearrange)
;;; have been archived in archive/proven-theorems-archive.scm.  Here we
;;; lift the result into the PSS so finsum and downstream development
;;; keep their foundational hook.

(support 'sum-ag-permutation-invariance
  '(FORALL n (IMPLIES (IN n NN)
     (FORALL ag (IMPLIES (IS-ABELIAN-GROUP ag)
     (FORALL g (IMPLIES (IN g (FUN NN (CARR ag)))
     (FORALL h (IMPLIES (IN h (FUN NN (CARR ag)))
     (FORALL phi (IMPLIES (IN phi (BIJECTION (ORD-SEGMENT n) (ORD-SEGMENT n)))
       (IMPLIES (FORALL i (IMPLIES (IN i (ORD-SEGMENT n)) (= (h i) (g (phi i)))))
         (= (SUM-AG ag g n) (SUM-AG ag h n))))))))))))))

(warrant! 'sum-ag-permutation-invariance 'informal
  "Mechanically proven before the 2026-05-27 PSS promotion; script archived at
   archive/proven-theorems-archive.scm (prove-and-install!
   'sum-ag-permutation-invariance), together with its intermediates
   sum-ag-splice-out, sum-ag-congruence and ag-mul-rearrange.  NN-induction
   whose step splices out the term at the top index and applies the IH to the
   induced permutation INVERSE-BIJ(DELETE-AT inv K).  This is the deepest
   argument in the promoted batch and the one finsum-well-defined rests on.
   Archive predates the E -> IDEN rename and the ==-sweep, so it does not run
   as-is -- `informal', not `proof'.")
