;;; ca-angle-vocab.scm -- WAVE 2 (2026-10-27..30), wired 2026-10-30 from scratchpad/ch3e/ch3e-angle.scm (vocab).
;;; Library: complex-analysis.
;;; Proof-free: the definitions (with their notation! lines) moved here from the proof file(s) named above.

(def-functoid 'ANGLE '(ang1_ ang2_)
  '(+ PI (imag-part (CHOICE (SEP angz_ CC (AND (<= (- PI) (imag-part angz_)) (AND (< (imag-part angz_) PI)
       (= (CC-EXP angz_) (- (* ang1_ (conjugate ang2_)))))))))))
(notation! 'ANGLE 'kind 'functoid 'arity 2 'english "the angle from $2 to $1")
(def-predicate 'POSITIVELY-ORIENTED '(poa_ pob_ poc_)
  '(FORALL pou_ (IMPLIES (IN pou_ (INTERIOR CC-MS (CONV3 poa_ pob_ poc_)))
     (AND (< (ANGLE (- pob_ pou_) (- poa_ pou_)) PI)
     (AND (< (ANGLE (- poc_ pou_) (- pob_ pou_)) PI)
          (< (ANGLE (- poa_ pou_) (- poc_ pou_)) PI))))))
(notation! 'POSITIVELY-ORIENTED 'kind 'predicate 'arity 3 'english "the triangle $1 $2 $3 is positively oriented")
