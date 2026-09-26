;;; nn-pos-is-succ.scm -- a natural at least 1 is a successor.
;;;
;;;   nn-pos-is-succ    n in NN,  1 <= n  =>  forsome q in NN.  n = succ(q)
;;;
;;; THE CONTENT IS ALREADY PROVEN.  `nn-nonzero-is-succ'
;;; (theorem-library/nn-parity-proof.scm:306, by induction) states the same
;;; conclusion -- character for character, same binder `q' -- under the
;;; hypothesis `n /= 0'.  All that is owed here is the bridge from `1 <= n' to
;;; `n /= 0', and that bridge is NOT free on NN: NN carries no order axioms
;;; beyond the succ family, so "1 <= n makes n positive" has to come from
;;; somewhere.  It comes from `nn-not-le-zero-pos'
;;; (theorem-library/nn-order-via-rr.scm, PROVEN modulo 0 by taking the
;;; contradiction in RR), which says 1 <= n forbids n <= 0.
;;;
;;; THE ARGUMENT.  Suppose n = 0.  Then n <= 0, because 0 <= 0 (nn-le-refl at
;;; 0, with nn-zero-in) and the equation rewrites it.  But nn-not-le-zero-pos
;;; at n, fed by the two hypotheses already in context, says not(n <= 0).
;;; So n /= 0, and nn-nonzero-is-succ at n lands the existential.
;;;
;;; WHERE IT SITS.  After nn-order-via-rr (nn-not-le-zero-pos, the LATEST of the
;;; citations), nn-parity-proof (nn-nonzero-is-succ) and nn-order-basics
;;; (nn-le-refl); BEFORE poly-degree-laws, the earliest citer.  Retires the
;;; `well-known' support of the same name from structure-library/order-lemmas.scm,
;;; statement byte-identical.

(sp (make-wff '(FORALL n (IMPLIES (IN n NN) (IMPLIES (<= 1 n)
     (FORSOME q (AND (IN q NN) (= n (succ q))))))))) 
(dk-peel!)                               ; di to the head; guards on progress
(fact 'nn-zero-in)                       ; 0 in NN
(fact 'nn-le-refl 0)                     ; 0 <= 0
(fact 'nn-not-le-zero-pos 'n)            ; not(n <= 0), both guards detached
(have! '(NOT (= n 0))
  (lambda ()
    (di)                                 ; assume n = 0; goal FALSITY
    (have! '(<= n 0) (lambda () (subst '(= n 0)) (ass)))
    (ai '(NOT (<= n 0)))))
(fact 'nn-nonzero-is-succ 'n)            ; the existential, guards detached
(ass)
(qed 'nn-pos-is-succ)

(topic! 'nn-pos-is-succ 'inequalities)
(alias! 'nn-pos-is-succ "a natural at least 1 is a successor")
