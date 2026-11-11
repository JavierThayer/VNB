;;; cnvs-ba-vocab.scm -- wave of 2026-11-09/10 (agent CNVS), wired 2026-11-10 from scratchpad/cnvs-1109/cnvs-ba-vocab.scm.
;;; Library: operator-algebras.

;;; cnvs-ba-vocab.scm -- A COMPLEX NORMED ALGEBRA AS A COMPLEX NORMED VECTOR SPACE (CNVS,
;;; 2026-11-09).  DEFINITIONS ONLY: no proof, no support, no axiom.
;;; Destination: structure-library/cnvs-ba-vocab.scm.  Library: operator-algebras.
;;; LOAD WINDOW: after structure-library/ba-vocab (COMPLEX-NORMED-ALGEBRA, CNA-AS-MODULE) and
;;; structure-library/cnvs-vocab (CMOD-CNVS).
;;;
;;; CNA-CNVS(a) is the realification CMOD-CNVS (cnvs-vocab.scm) of the module view of a with
;;; the algebra's own norm: the product is forgotten, the scalars are restricted to RR, and J
;;; is multiplication by i.

(def-functoid 'CNA-CNVS '(cna_)
  '(CMOD-CNVS (CNA-AS-MODULE cna_) (VNRM cna_)))

(notation! 'CNA-CNVS 'kind 'functoid 'arity 1 'english "the normed algebra $1 as a complex normed vector space")
