;;; cnvs-comp-vocab.scm -- wave of 2026-11-09/10 (agent CNVS2), wired 2026-11-10 from scratchpad/cnvs2-1109/cnvs2-comp-vocab.scm.
;;; Library: analysis.

;;; cnvs2-comp-vocab.scm -- COMPOSITION AND IDENTITY OF OPERATORS BETWEEN COMPLEX NORMED VECTOR
;;; SPACES (agent CNVS2, 2026-11-10).  DEFINITIONS ONLY: no proof, no support, no axiom.
;;; Destination: structure-library/cnvs-comp-vocab.scm.  Library: analysis (with cnvs-vocab).
;;; Load window: after structure-library/cnvs-vocab.
;;;
;;; S o T for T : u -> v, S : v -> w is the map x |-> S(T x) on VEC(u); the identity of u is
;;; x |-> x.  The BA-BH recipe (BOP-COMP, BOP-ID of ba-ops-vocab.scm) with one difference: the
;;; lambda binder cqx_ is spelled like NO parameter of the functoid, so the unfolding of
;;; CBOP-COMP fires under a binder of a caller whose binder is a parameter name (the rewriter
;;; refuses to descend under a VNB-LAMBDA whose bound variable is spelled like a schema
;;; variable of the macete; macetes.scm, rewrite-subexpressions).
;;; Binders: cqx_; parameters cqu_ cqs_ cqt_, used by nothing else in the tree.
(def-functoid 'CBOP-COMP '(cqu_ cqs_ cqt_)
  '(VNB-LAMBDA cqx_ (VEC cqu_) (cqs_ (cqt_ cqx_))))
(def-functoid 'CBOP-ID '(cqu_)
  '(VNB-LAMBDA cqx_ (VEC cqu_) cqx_))

(notation! 'CBOP-COMP 'kind 'functoid 'arity 3 'english "$2 $3" 'tex "{$2}{$3}")
(notation! 'CBOP-ID 'kind 'functoid 'arity 1 'english "the identity operator of $1" 'tex "1")
