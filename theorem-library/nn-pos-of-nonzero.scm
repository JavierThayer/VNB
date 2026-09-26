;;; nn-pos-of-nonzero.scm -- a nonzero natural is strictly positive.
;;;
;;;   nn-pos-of-nonzero    k in NN,  k /= 0  =>  0 < k
;;;
;;; THE ARGUMENT.  `<' is a def-predicate (structure-library/order-predicates.scm:24):
;;; (< x y) <=> (AND (<= x y) (NOT (= x y))).  So `mac '<' on the goal turns
;;; `0 < k' into the conjunction, and each half is one citation:
;;;
;;;   (<= 0 k)        nn-zero-le           (theorem-library/nn-order-ord.scm)
;;;   (NOT (= 0 k))   neq-sym at k, 0      (theorem-library/equality-basics.scm)
;;;                   applied to the hypothesis NOT (= k 0) already in context.
;;;
;;; The retired warrant ("0<=k (nn-zero-le) and 0/=k give the strict
;;; inequality") is exactly this, with the symmetry step left implicit -- the
;;; hypothesis is NOT (= k 0) and the unfolded conjunct is NOT (= 0 k), which
;;; are different S-expressions and want `neq-sym' between them.
;;;
;;; WHERE IT SITS.  After nn-order-ord (nn-zero-le) and equality-basics
;;; (neq-sym); BEFORE nn-integral, the earliest citer.  Retires the
;;; `well-known' support of the same name from structure-library/order-lemmas.scm,
;;; statement byte-identical.

(sp (make-wff '(FORALL k (IMPLIES (IN k NN) (IMPLIES (NOT (= k 0)) (< 0 k))))))
(dk-peel!)                               ; di to the head; guards on progress
(mac '<)                                 ; (AND (<= 0 k) (NOT (= 0 k)))
(fact 'nn-zero-le 'k)                    ; 0 <= k
(fact 'neq-sym 'k 0)                     ; NOT (= k 0) => NOT (= 0 k), detached
(di)                                     ; split the conjunctive goal
(ass)
(ass)
(qed 'nn-pos-of-nonzero)

(topic! 'nn-pos-of-nonzero 'inequalities)
(alias! 'nn-pos-of-nonzero "a nonzero natural is strictly positive")
