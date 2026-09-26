;;; RETIRED 2026-09-17 (proven, modulo 0): sum-ag-permutation-invariance -- theorem-library/
;;; rake-finsum-welldef.scm, by ONE-ENTRY REPLACEMENT and a re-routed permutation (no DELETE-AT, no
;;; inverse), not the archived splice-out argument.  The finsum floor is proven.
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


