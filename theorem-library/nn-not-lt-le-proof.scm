;;; nn-not-lt-le-proof.scm -- NOT (k < j) => j <= k on NN, `modulo 0'.
;;;
;;;     nn-not-lt-le   forall k_ in NN, j_ in NN.  NOT (k_ < j_)  =>  j_ <= k_
;;;
;;; REPLACES the proof at theorem-library/finite-surgery.scm:41-62 (load.scm:909),
;;; which is the same script except for ONE citation: its transitivity step
;;; is the UNGUARDED asserted support `co-le-trans' (structure-library/
;;; order-lemmas.scm:180), so every bill through nn-not-lt-le carried that
;;; leaf.  Here the step is `nn-succ-closed' (primitive: succ j_ in NN) plus
;;; `nn-le-trans-guarded' (theorem-library/nn-order-basics.scm, proven), and
;;; the bill is empty.  Same statement, same binders.
;;;
;;; PLAN (totality, read off the definition of `<').  Either j_ = k_, and
;;; nn-le-refl closes it; or j_ /= k_, so NOT (k_ <= j_) (else k_ < j_ by
;;; `mac '<'), so succ j_ <= k_ (nn-not-le-succ-le), and j_ <= succ j_
;;; (nn-le-succ) chains to j_ <= k_.
;;;
;;; LOAD WINDOW [lo, hi):
;;;   lo = theorem-library/nn-order-basics (load.scm:675) -- nn-le-trans-guarded
;;;        and nn-le-refl, the latest citations; nn-not-le-succ-le (:669),
;;;        nn-order-ord (nn-le-succ, :668), equality-basics (neq-sym, :590)
;;;        and nn-succ-closed (number-systems, primitive) sit above it.
;;;   hi = theorem-library/finite-surgery (load.scm:909), whose :203 is the
;;;        earliest citer -- and whose :41-62 the integrator retires.
;;;
;;; Helper prefix: nnl- (none needed).

(sp (make-wff '(FORALL k_ (IMPLIES (IN k_ NN)
                 (FORALL j_ (IMPLIES (IN j_ NN)
                   (IMPLIES (NOT (< k_ j_)) (<= j_ k_))))))))
(di) (di)
(use-em '(= j_ k_)
  (lambda ()
    (subst '(= j_ k_))
    (fact 'nn-le-refl 'k_)
    (ass))
  (lambda ()
    (fact 'neq-sym 'j_ 'k_)
    (have! '(NOT (<= k_ j_))
           (lambda ()
             (di)
             (have! '(< k_ j_) (lambda () (mac '<) (from-context!)))
             (ai '(NOT (< k_ j_)))))
    (fact 'nn-not-le-succ-le 'k_ 'j_)
    (fact 'nn-le-succ 'j_)
    (fact 'nn-succ-closed 'j_)                          ; succ j_ in NN, for the guard
    (fact 'nn-le-trans-guarded 'j_ '(succ j_) 'k_)      ; j_ <= succ j_ <= k_
    (ass)))
(qed 'nn-not-lt-le)
(topic! 'nn-not-lt-le 'inequalities)
