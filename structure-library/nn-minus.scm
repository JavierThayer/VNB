;;; nn-minus.scm -- truncated natural subtraction (monus), as VOCABULARY.
;;;
;;;   NN-MINUS(k, l) = IF l <= k THEN k - l ELSE 0          (k, l in NN)
;;;
;;; Defined EXPLICITLY as a closed term in existing vocabulary -- NOT by a
;;; recursion-shaped postulate.  NN subset ZZ, so for l <= k the integer
;;; difference k - l is already the right natural; below it, the conventional 0.
;;; An explicit definition is conservative by construction (eliminable by
;;; unfolding): no recursion theorem, no two-index recursion combinator, no
;;; consistency debt -- the monus recurrences nn-minus(n,0) = n,
;;; nn-minus(succ n, succ k) = nn-minus(n,k), nn-minus(0, succ k) = 0 are
;;; one-step THEOREMS (IF case split on l <= k + integer arithmetic), not axioms.
;;;
;;; HOISTED HERE 2026-09-20 (batch 12-A) from theorem-library/finsum-additive.scm,
;;; where the def-constant sat inside a support file at load.scm ~459 -- below
;;; structure-library/mat-equiv.scm (~412), which STATES the block-matrix
;;; recursion with the head (mat-equiv.scm:71).  Only number-systems (`-', `<=',
;;; IF, NN) is needed, so the definition belongs here.  Its name and its
;;; defining theorem `nn-minus-def' are unchanged; the typing support and every
;;; law keep their homes.

(def-constant 'NN-MINUS
  '(nn-minus-def
    (FORALL k (IMPLIES (IN k NN)
      (FORALL l (IMPLIES (IN l NN)
        (= (NN-MINUS k l) (IF (<= l k) (- k l) 0))))))))
