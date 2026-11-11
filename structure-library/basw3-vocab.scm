;;; basw3-vocab.scm -- wave of 2026-11-09/10 (agent BA-SW3), wired 2026-11-10 from scratchpad/basw3-1109/basw3-vocab.scm.
;;; Library: operator-algebras.

;;; basw3-vocab.scm -- URYSOHN'S LEMMA FOR A COMPACT HAUSDORFF SPACE: the vocabulary of the
;;; construction.  DEFINITIONS ONLY.  Agent BA-SW3, wave 2026-11-09.
;;; Destination: structure-library/basw3-vocab.scm.  Library: analysis.
;;; Load window: after structure-library/top-space (OPENS, IS-TOP-CLOSED), extended-reals-pos (ESUP),
;;; the BA vocabulary (CCONT, for POINT-EVAL)
;;; and ordinals (def-by-nn-recursion); anywhere before theorem-library/basw3-urysohn.
;;;
;;; THE CONSTRUCTION (the halving scheme; no dyadic rationals are formed).  A CU pair of t is a
;;; pair [C, U] with C closed, U open and C a subset of U.  A pair c = [C, U] has two halves,
;;;     URY-L(t, c) = [C, V]      URY-R(t, c) = [K, U]
;;; where V open and K closed are CHOSEN with C subset V subset K subset U (on a compact Hausdorff
;;; space they exist: top-compact-hausdorff-shrink).  For a point x the approximants are
;;;     A_0(c)     = 0 if x in U, 1 otherwise
;;;     A_{n+1}(c) = (A_n(URY-L c) + A_n(URY-R c)) / 2,
;;; a recursion on n of a function on the CU pairs (x is a parameter: it never moves), and the
;;; Urysohn function is x |-> sup_n A_n(c)(x).  The choice is GLOBAL (CHOICE of the class of the
;;; admissible middles), made once for every pair, so no choice over a level is needed.
;;; Binders: ucw_ uvv_ uvk_ uat_ uax_ uac_ uan_ uav_ ulr_ uln_ (no other file uses them).

;;; the CU pairs [C, U] of t: C closed, U open, C subset U
(def-functoid 'CU-PAIRS '(uat_)
  '(SEP ucw_ (CARTESIAN (POWER (PTS uat_)) (OPENS uat_))
        (AND (IS-TOP-CLOSED uat_ (NTH 1 ucw_)) (SUBSET (NTH 1 ucw_) (NTH 2 ucw_)))))
;;; the chosen open middle V of c = [C, U]: C subset V, and some closed K has V subset K subset U
(def-functoid 'URY-V '(uat_ uac_)
  '(CHOICE (SEP uvv_ (OPENS uat_)
     (FORSOME uvk_ (AND (IN uvk_ (POWER (PTS uat_))) (AND (IS-TOP-CLOSED uat_ uvk_)
       (AND (SUBSET (NTH 1 uac_) uvv_) (AND (SUBSET uvv_ uvk_) (SUBSET uvk_ (NTH 2 uac_))))))))))
;;; the chosen closed middle K: V subset K subset U
(def-functoid 'URY-K '(uat_ uac_)
  '(CHOICE (SEP uvk_ (POWER (PTS uat_))
     (AND (IS-TOP-CLOSED uat_ uvk_) (AND (SUBSET (URY-V uat_ uac_) uvk_) (SUBSET uvk_ (NTH 2 uac_)))))))
;;; the two halves of c
(def-functoid 'URY-L '(uat_ uac_) '(LIST (NTH 1 uac_) (URY-V uat_ uac_)))
(def-functoid 'URY-R '(uat_ uac_) '(LIST (URY-K uat_ uac_) (NTH 2 uac_)))
;;; the approximants at the point x, a function on the CU pairs
(def-by-nn-recursion 'URY-APX '(uat_ uax_)
  '(VNB-LAMBDA uac_ (CU-PAIRS uat_) (IF (IN uax_ (NTH 2 uac_)) 0 1))
  '(uan_ uav_)
  '(VNB-LAMBDA uac_ (CU-PAIRS uat_) (* 1/2 (+ (uav_ (URY-L uat_ uac_)) (uav_ (URY-R uat_ uac_))))))
;;; their supremum: the value at x of the Urysohn function of c
(def-functoid 'URY-LIM '(uat_ uac_ uax_)
  '(ESUP (SEP ulr_ RR (FORSOME uln_ (AND (IN uln_ NN) (= ulr_ ((URY-APX uat_ uax_ uln_) uac_)))))))

(notation! 'CU-PAIRS 'kind 'functoid 'arity 1
           'english "the pairs [C, U] of a closed set inside an open set of $1")
(notation! 'URY-V 'kind 'functoid 'arity 2 'english "the chosen open middle of the pair $2 in $1")
(notation! 'URY-K 'kind 'functoid 'arity 2 'english "the chosen closed middle of the pair $2 in $1")
(notation! 'URY-L 'kind 'functoid 'arity 2 'english "the lower half of the pair $2 in $1")
(notation! 'URY-R 'kind 'functoid 'arity 2 'english "the upper half of the pair $2 in $1")
(notation! 'URY-APX 'kind 'functoid 'arity 3 'english "the $3-th Urysohn approximant at $2 in $1")
(notation! 'URY-LIM 'kind 'functoid 'arity 3 'english "the Urysohn function of the pair $2 in $1 at $3")

;;; ---- Remark 1.27 of the notes: the evaluation at a point x of t, a functional on C(t) ------------
;;; Binders uet_ uex_ uef_.
(def-functoid 'POINT-EVAL '(uet_ uex_) '(VNB-LAMBDA uef_ (CCONT uet_) (uef_ uex_)))
(notation! 'POINT-EVAL 'kind 'functoid 'arity 2 'english "the evaluation at $2 on the continuous functions on $1")
