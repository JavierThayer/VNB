;;; ba2-vocab.scm -- wave of 2026-11-09/10 (agent BA-2), wired 2026-11-10 from scratchpad/ba2-1109/ba2-vocab.scm.
;;; Library: operator-algebras.

;;; ba2-vocab.scm -- BANACH ALGEBRAS: unital C*-subalgebras (Proposition 1.29).
;;; F. J. Thayer, "Banach Algebras and Applications", ch. 1 s. 2.
;;; DEFINITIONS ONLY.  Agent BA-2, wave 2026-11-09.  Destination: structure-library/ba2-vocab.scm.
;;; Library: operator-algebras.  Load window: after structure-library/ba-vocab.
;;; Binders c2a_ c2b_ c2x_ c2y_ c2z_, used by no other file.
;;;
;;; "A subset B are C*-algebras with unit and A contains the unit of B" (1.29): both are unital
;;; C*-algebras, the carrier of A lies in the carrier of B, the units agree, and every operation
;;; of A (sum, product, negation, scalar action, involution, norm) is the restriction of B's.

(def-predicate 'IS-UNITAL-C-STAR-SUBALGEBRA '(c2a_ c2b_)
  '(AND (IS-UNITAL-C-STAR-ALGEBRA c2a_)
   (AND (IS-UNITAL-C-STAR-ALGEBRA c2b_)
   (AND (FORALL c2x_ (IMPLIES (IN c2x_ (VEC c2a_)) (IN c2x_ (VEC c2b_))))
   (AND (= (VONE c2a_) (VONE c2b_))
   (AND (FORALL c2x_ (IMPLIES (IN c2x_ (VEC c2a_)) (FORALL c2y_ (IMPLIES (IN c2y_ (VEC c2a_))
          (= ((VADD c2a_) c2x_ c2y_) ((VADD c2b_) c2x_ c2y_))))))
   (AND (FORALL c2x_ (IMPLIES (IN c2x_ (VEC c2a_)) (FORALL c2y_ (IMPLIES (IN c2y_ (VEC c2a_))
          (= ((VMUL c2a_) c2x_ c2y_) ((VMUL c2b_) c2x_ c2y_))))))
   (AND (FORALL c2z_ (IMPLIES (IN c2z_ CC) (FORALL c2x_ (IMPLIES (IN c2x_ (VEC c2a_))
          (= ((ACT c2a_) c2z_ c2x_) ((ACT c2b_) c2z_ c2x_))))))
   (AND (FORALL c2x_ (IMPLIES (IN c2x_ (VEC c2a_)) (= ((VNEG c2a_) c2x_) ((VNEG c2b_) c2x_))))
   (AND (FORALL c2x_ (IMPLIES (IN c2x_ (VEC c2a_)) (= ((VSTAR c2a_) c2x_) ((VSTAR c2b_) c2x_))))
        (FORALL c2x_ (IMPLIES (IN c2x_ (VEC c2a_)) (= ((VNRM c2a_) c2x_) ((VNRM c2b_) c2x_))))))))))))))

(notation! 'IS-UNITAL-C-STAR-SUBALGEBRA 'kind 'predicate 'arity 2
           'english "$1 is a unital C*-subalgebra of $2 containing its unit")
