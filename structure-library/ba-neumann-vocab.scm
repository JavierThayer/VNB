;;; ba-neumann-vocab.scm -- wave of 2026-11-09/10 (agent BA-1), wired 2026-11-10 from scratchpad/ba1-1109/ba-neumann-vocab.scm.
;;; Library: operator-algebras.

;;; ba-neumann-vocab.scm -- BANACH ALGEBRAS: the partial sums of the Neumann series.
;;; F. J. Thayer, "Banach Algebras and Applications", Proposition 1.3:
;;;   NEUMANN-SUM(a, x, n) = sum_(k < n) x^k   (x^k = EL-POW(a, x, k), ba-vocab.scm)
;;; DEFINITIONS ONLY.  Agent BA-1, wave 2026-11-09.  Destination: structure-library/ba-neumann-vocab.scm.
;;; Library: operator-algebras.  Load window: after structure-library/ba-vocab.scm.
;;; Binders bn*_ (bna_ bnx_ bnk_ bnv_), used by no other file.

(def-by-nn-recursion 'NEUMANN-SUM '(bna_ bnx_)
  '(VZERO bna_)
  '(bnk_ bnv_)
  '((VADD bna_) bnv_ (EL-POW bna_ bnx_ bnk_)))

(notation! 'NEUMANN-SUM 'kind 'functoid 'arity 3 'english "the sum of the powers of $2 below $3 in $1"
           'tex "\\sum_{k < $3} {$2}^{k}")
