;;; ba-trace-dual-vocab.scm -- Thayer, Banach Algebras and Applications, chapter 5 s.6-s.8 (spaces of
;;; ultraweakly continuous functionals, duals, transpose and module structure of L_*(H)).
;;; DEFINITIONS ONLY: no proof, no support, no axiom.
;;; Agent BA-1117-TRACE, 2026-11-17.  DESTINATION: structure-library/ba-trace-dual-vocab.scm, after
;;; structure-library/th3-vocab.scm (OP-TRACE, IS-POSITIVE-OP) and structure-library/ba-ops-vocab.scm
;;; (BOUNDED-OPS, BOP-COMP, OP-ADJOINT).  Library: operator-algebras.
;;;
;;;   TAU-OP(v, S)                 Def. 5.25: tau_S(A) = tr(A S), A in L(H)
;;;   FUNCTIONAL-STAR(v, f)        s.8: f*(A) = conj f(A*)  (the bar is lost in the pdf text; the
;;;                                notes call f |-> f* a conjugate-linear involution)
;;;   IS-SELF-ADJOINT-FUNCTIONAL(v, f)  s.8: f* = f, pointwise on L(H)
;;;   IS-POSITIVE-OP-FUNCTIONAL(v, f) s.8: f(A) >= 0 for every positive A in L(H)
;;;
;;; Binders td*_ (tdv_ tds_ tdf_ tda_), used by no other file.

(def-functoid 'TAU-OP '(tdv_ tds_)
  '(VNB-LAMBDA tda_ (BOUNDED-OPS tdv_ tdv_) (OP-TRACE tdv_ (BOP-COMP tdv_ tda_ tds_))))

(def-functoid 'FUNCTIONAL-STAR '(tdv_ tdf_)
  '(VNB-LAMBDA tda_ (BOUNDED-OPS tdv_ tdv_) (conjugate (tdf_ (OP-ADJOINT tdv_ tdv_ tda_)))))

(def-predicate 'IS-SELF-ADJOINT-FUNCTIONAL '(tdv_ tdf_)
  '(FORALL tda_ (IMPLIES (IN tda_ (BOUNDED-OPS tdv_ tdv_))
     (= (conjugate (tdf_ (OP-ADJOINT tdv_ tdv_ tda_))) (tdf_ tda_)))))

(def-predicate 'IS-POSITIVE-OP-FUNCTIONAL '(tdv_ tdf_)
  '(FORALL tda_ (IMPLIES (IS-POSITIVE-OP tdv_ tda_)
     (AND (IN (tdf_ tda_) RR) (<= 0 (tdf_ tda_))))))

(notation! 'TAU-OP 'kind 'functoid 'arity 2 'english "the trace functional of $2 on the bounded operators on $1" 'tex "\\tau_{$2}")
(notation! 'FUNCTIONAL-STAR 'kind 'functoid 'arity 2 'english "the adjoint functional of $2" 'tex "{$2}^{*}")
(notation! 'IS-SELF-ADJOINT-FUNCTIONAL 'kind 'predicate 'arity 2 'english "$2 is a self-adjoint functional on the bounded operators on $1")
(notation! 'IS-POSITIVE-OP-FUNCTIONAL 'kind 'predicate 'arity 2 'english "$2 is a positive functional on the bounded operators on $1")
