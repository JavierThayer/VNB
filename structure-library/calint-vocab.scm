;;; calint-vocab.scm -- WAVE 2 (2026-10-27..30), wired 2026-10-30 from scratchpad/calint/calint-vocab.scm.
;;; Library: analysis.

;;; calint-vocab.scm -- CAL-INT vocabulary (2026-10-28).  Destination: structure-library/.
;;; HAS-DERIV-ON-CCINT(g, dg, a, b): dg is the derivative of g on the closed interval [a, b] in the
;;; sense of calculus.pdf Prop 4.16 ("f_k' is defined on [a, b]"): g and dg are real functions on
;;; [a, b], g has derivative dg(t) at every interior point, the right derivative dg(a) at a and the
;;; left derivative dg(b) at b.
;;; Library: analysis.  Load window: after structure-library/one-sided-derivative (HAS-RIGHT-DERIV-AT,
;;; HAS-LEFT-DERIV-AT) and the file defining HAS-DERIV-AT.
(def-predicate 'HAS-DERIV-ON-CCINT '(hdcg_ hdcd_ hdca_ hdcb_)
  (conjuncts->and
    (list '(IN hdca_ RR)
          '(IN hdcb_ RR)
          '(< hdca_ hdcb_)
          '(IN hdcg_ (FUN (CCINT hdca_ hdcb_) RR))
          '(IN hdcd_ (FUN (CCINT hdca_ hdcb_) RR))
          '(FORALL hdct_ (IMPLIES (IN hdct_ (OOINT hdca_ hdcb_)) (HAS-DERIV-AT hdcg_ hdct_ (hdcd_ hdct_))))
          '(HAS-RIGHT-DERIV-AT hdcg_ hdca_ (hdcd_ hdca_))
          '(HAS-LEFT-DERIV-AT hdcg_ hdcb_ (hdcd_ hdcb_)))))
(notation! 'HAS-DERIV-ON-CCINT 'kind 'predicate 'arity 4
           'english "$2 is the derivative of $1 on [$3, $4] (one-sided at the end points)")
