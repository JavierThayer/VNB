;;; nth-deriv.scm -- THE ITERATED DERIVATIVE ON AN OPEN SET, OVER A NORMED FIELD.
;;; DEFINITION ONLY; the laws are PROVEN in theorem-library/nth-deriv-laws.scm.
;;; Batch 36, 2026-09-26.
;;;
;;; The user's decision of 2026-09-26: define the k-th derivative by NN-recursion
;;; and restate the notes' Corollary 2.14 (f^(k)(0) = k! a_k) literally with it.
;;;
;;;     NTH-DERIV-ON(K, U, f, k)   the k-th derivative of f on the open set U over
;;;                                the normed field K, AS A FUNCTION ON U:
;;;         NTH-DERIV-ON(K, U, f, 0)       == f
;;;         NTH-DERIV-ON(K, U, f, succ n)  == vnb-lambda(z in U,
;;;                                              DERIV-ON(K, U, NTH-DERIV-ON(K, U, f, n), z))
;;;
;;; MECHANISM.  `def-by-nn-recursion' (ordinals.scm), the PARAMETRIC form with
;;; parameters K, U, f -- the same mechanism as the real NTH-DERIV
;;; (theorem-library/higher-derivatives.scm).  It installs the two recursion
;;; equations as DEFINITIONAL theorems, under the names
;;;     nth-deriv-on-zero   forall K U f. NTH-DERIV-ON(K, U, f, 0) == f
;;;     nth-deriv-on-succ   forall K U f. forall n in NN.
;;;                           NTH-DERIV-ON(K, U, f, succ n)
;;;                             == vnb-lambda(z in U, DERIV-ON(K, U, NTH-DERIV-ON(K, U, f, n), z))
;;; Both are THEOREMS (not only macetes, unlike a def-functoid), so `mac',
;;; `mac-h', `fact' and `subst' all reach them by name.  The equations are
;;; quasi-equalities (`=='), as def-by-nn-recursion writes every recursion
;;; equation: off-domain (K not a normed field, the (k-1)-th derivative not
;;; differentiable somewhere) both sides may be undefined.
;;;
;;; DERIV-ON is an IOTA (diff-on.scm): a member of CARR(K) only where the
;;; derivative exists and is unique.  So NTH-DERIV-ON(K, U, f, succ n) is a
;;; member of FUN(U, CARR K) exactly when NTH-DERIV-ON(K, U, f, n) is
;;; differentiable at every point of U (and K's norm has arbitrarily small
;;; nonzero elements, so that the derivative is unique): `nth-deriv-on-in-fun'.
;;;
;;; BINDERS.  Parameters ndvk_, ndvu_, ndvf_; step variables ndvn_, ndvv_; the
;;; lambda's binder ndvz_.  Nothing else in the tree uses the ndv prefix.
;;;
;;; Dependencies: diff-on.scm (DERIV-ON), ordinals.scm (def-by-nn-recursion),
;;; number-systems.scm (NN, succ).  LOAD SLOT: after structure-library/ordinals.

(def-by-nn-recursion 'NTH-DERIV-ON '(ndvk_ ndvu_ ndvf_)
  'ndvf_                                                  ; the 0-th derivative is f
  '(ndvn_ ndvv_)                                          ; ndvv_ = NTH-DERIV-ON(K, U, f, ndvn_)
  '(VNB-LAMBDA ndvz_ ndvu_ (DERIV-ON ndvk_ ndvu_ ndvv_ ndvz_)))

(notation! 'NTH-DERIV-ON 'kind 'functoid 'arity 4
           'english "the $4-th derivative of $3 on $2"
           'tex "$3^{($4)}")
