;;; tb11-vocab.scm -- vocabulary for topological-vector-spaces Appendix A.3 (TB-11):
;;; finite products over a sequence in a monoid, and the subadditive regularisation of
;;; Proposition A.5.  DEFINITIONS ONLY.  Agent ISOM, 2026-10-26 (new definitions, the
;;; user's to confirm).
;;;
;;;   MPROD(m, u, n)
;;;       u(0) u(1) ... u(n-1) in the monoid m (IDEN m for n = 0), by recursion on n:
;;;       MPROD(m, u, succ n) = OPR(m)(MPROD(m, u, n), u(n)).  The notes' x_1 o ... o x_n,
;;;       indices from 0.
;;;   FACT-SUMS(m, g, x)
;;;       the set of the sums g(u_0) + ... + g(u_{n-1}) over the factorisations
;;;       x = u_0 ... u_{n-1} of x in m (n in NN, u in FUN(NN, CARR m)); the set in braces
;;;       of the notes' (136).
;;;   SUBADD-REG(m, g, x)
;;;       (136): the infimum (EINF, in [0, +inf]) of FACT-SUMS(m, g, x).
;;; BINDERS: mpm_ mpu_ mpn_ mpv_ fsm_ fsg_ fsx_ fsr_ fsn_ fsu_ fsi_ srm_ srg_ srx_.

(def-by-nn-recursion 'MPROD '(mpm_ mpu_)
  '(IDEN mpm_)
  '(mpn_ mpv_)
  '((OPR mpm_) mpv_ (mpu_ mpn_)))
(notation! 'MPROD 'kind 'functoid 'arity 3 'english "the product in $1 of the first $3 terms of $2")

(def-functoid 'FACT-SUMS '(fsm_ fsg_ fsx_)
  '(SEP fsr_ RR (FORSOME fsn_ (AND (IN fsn_ NN) (FORSOME fsu_ (AND (IN fsu_ (FUN NN (CARR fsm_)))
     (AND (= (MPROD fsm_ fsu_ fsn_) fsx_)
          (= fsr_ (SERIES-PARTIAL-SUM (VNB-LAMBDA fsi_ NN (fsg_ (fsu_ fsi_))) fsn_)))))))))
(notation! 'FACT-SUMS 'kind 'functoid 'arity 3
           'english "the sums of $2 over the factorisations of $3 in $1")

(def-functoid 'SUBADD-REG '(srm_ srg_ srx_)
  '(EINF (FACT-SUMS srm_ srg_ srx_)))
(notation! 'SUBADD-REG 'kind 'functoid 'arity 3
           'english "the infimum of the sums of $2 over the factorisations of $3 in $1")
