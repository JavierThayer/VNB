;;; basw2-vocab.scm -- wave of 2026-11-09/10 (agent BA-SW2), wired 2026-11-10 from scratchpad/basw2-1109/basw2-vocab.scm.
;;; Library: operator-algebras.

;;; basw2-vocab.scm -- BANACH ALGEBRAS: the positive cone of an involutive algebra (Def. 1.34).
;;; DEFINITIONS ONLY: no proof, no support, no axiom.
;;; Agent BA-SW2, wave 2026-11-09.  FLAGGED for the integrator / BA-3: POS-CONE is not in BA-1's
;;; step-0 vocabulary; this is BA-SW's proposal (BA-SW-REPORT F6).
;;; Destination: structure-library/basw2-vocab.scm, after ba-vocab.  Library: operator-algebras.
;;;
;;;   POS-CONE(a)  the smallest subset of VEC(a) containing every x* x and closed under +: the
;;;                members of VEC(a) lying in every such subset.  It is "the finite sums of x* x"
;;;                without FINSUM; the nonnegative scalars of "the cone generated" are automatic in a
;;;                C*-algebra, since c x* x = (sqrt(c) x)* (sqrt(c) x).
;;;
;;; Binders pc*_ (pca_ pcx_ pcc_ pcy_ pcu_ pcv_), used by no other file.

(def-functoid 'POS-CONE '(pca_)
  '(SEP pcx_ (VEC pca_)
     (FORALL pcc_ (IMPLIES (IN pcc_ (POWER (VEC pca_)))
       (IMPLIES (FORALL pcy_ (IMPLIES (IN pcy_ (VEC pca_)) (IN ((VMUL pca_) ((VSTAR pca_) pcy_) pcy_) pcc_)))
         (IMPLIES (FORALL pcu_ (IMPLIES (IN pcu_ pcc_) (FORALL pcv_ (IMPLIES (IN pcv_ pcc_) (IN ((VADD pca_) pcu_ pcv_) pcc_)))))
           (IN pcx_ pcc_)))))))

(notation! 'POS-CONE 'kind 'functoid 'arity 1 'english "the positive cone of $1" 'tex "{$1}_{+}")
