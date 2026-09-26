;;; id-fun.scm -- ID-FUN: the identity map of a set.
;;;
;;;   ID-FUN(A)  :=  VNB-LAMBDA idfx_ A idfx_          "the identity map of A"
;;;
;;; A VNB-LAMBDA, so an element of FUN(A, A) once A is a set (lam-t), and it
;;; reduces by lam-b at an argument typed in A.  Its laws are THEOREMS, proven in
;;; theorem-library/id-fun-laws.scm (sp/qed do not exist this early in load.scm):
;;;   id-fun-type       A in SET => ID-FUN(A) in FUN(A, A)
;;;   id-fun-apply      x in A   => ID-FUN(A)(x) = x
;;;   compose-id-left   COMPOSE(ID-FUN(B), f) = f        f in FUN(A, B)
;;;   compose-id-right  COMPOSE(f, ID-FUN(A)) = f        f in FUN(A, B)
;;;   compose-assoc     COMPOSE(h, COMPOSE(g, f)) = COMPOSE(COMPOSE(h, g), f)
;;;
;;; It is the identity ARROW of the category of the models of a structure
;;; (theorem-library/hom-laws.scm: hom-<name>-id).
;;;
;;; The binder `idfx_' is used by nothing else in the tree (batch 33, 2026-09-25),
;;; so the unfold never captures a caller's variable.
;;;
;;; Needs: VNB-LAMBDA (theory.scm).  Batch 33 (the user's decision 2026-09-25).

(def-functoid 'ID-FUN '(a_)
  '(VNB-LAMBDA idfx_ a_ idfx_))
(notation! 'ID-FUN 'kind 'functoid 'arity 1
           'english "the identity map of $1")
