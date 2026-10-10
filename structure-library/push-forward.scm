;;; structure-library/push-forward.scm -- the push-forward of a measure along a
;;; map (RM-3B, 2026-10-10).  DEFINITIONS ONLY; every law is PROVEN in
;;; theorem-library/push-forward.scm (prefix pfw-).
;;;
;;; Source: Thayer, Construction of Measures, Prop. 1.19 (the push-forward is a
;;; measure) and Ch. 2 s. 7, Prop. 2.32 (the change of variables formula).
;;;
;;;   PUSH-FORWARD(omega, cB, mu, h)
;;;        the set function on cB sending b to mu({x in omega : h(x) in b}):
;;;        Thayer's psi_* mu for psi = h.  When mu is a measure on (omega, cA) and
;;;        h is measurable from (omega, cA) to (omega2, cB) it is a measure on
;;;        (omega2, cB) (pfw-push-forward-measure, from measure-pushforward of
;;;        measure-laws.scm, whose term this is up to the names of the binders).
;;;
;;; The composite f o h of a function f on omega2 with h is written out, as the
;;; lambda (VNB-LAMBDA pwz_ omega (f (h pwz_))), in the statements of the laws;
;;; it needs no name.
;;;
;;; BINDERS pwb_ pwx_ (and pwz_ in the laws) are used by nothing else in the tree.
;;; Dependencies: measure (IS-MEASURE, IS-MEASURABLE-MAP).  Library: measure.

(def-functoid 'PUSH-FORWARD '(omega cB mu h)
  '(VNB-LAMBDA pwb_ cB (mu (SEP pwx_ omega (IN (h pwx_) pwb_)))))

(notation! 'PUSH-FORWARD 'kind 'functoid 'arity 4
           'english "the push-forward along $4 of the measure $3, on the sets $2")
