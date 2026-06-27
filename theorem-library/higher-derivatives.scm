;;; higher-derivatives.scm -- calculus.pdf Def 2.2: the n-th derivative f^(n),
;;; by induction on n, built on DERIV / IS-DIFF-AT (differentiation.scm).
;;;
;;; NTH-DERIV(f, n) is the n-th derivative as a FUNCTION RR -> RR:
;;;     NTH-DERIV(f, 0)       = f
;;;     NTH-DERIV(f, succ n)  = x |-> DERIV(NTH-DERIV(f, n), x)
;;; i.e. the derivative function of the n-th derivative.  Then the value
;;; f^(n)(theta) of the notes is  (NTH-DERIV f n)(theta).  (The notes' rendered
;;; "f^(n+1)(t) = f^(n)(t)" in Def 2.2(2) is a typo for "= [f^(n)]'(t)"; this is
;;; the standard induction.)
;;;
;;; def-by-nn-recursion auto-installs the two characterizing axioms
;;;   nth-deriv-zero : (== (NTH-DERIV f 0) f)
;;;   nth-deriv-succ : forall n in NN. (== (NTH-DERIV f (succ n))
;;;                                        (VNB-LAMBDA x (DERIV (NTH-DERIV f n) x)))
;;; Both are pure REWRITES with no existential witness, so a dumb scout pass can
;;; assemble uses of f^(n) -- per the [[automatable-assembly]] criterion: the
;;; block is complete when search closes the target, no creative step required.

(def-by-nn-recursion 'NTH-DERIV '(f)
  'f                                    ; NTH-DERIV(f, 0) = f
  '(n val)                              ; step vars: n in NN, val = NTH-DERIV(f, n)
  '(VNB-LAMBDA x (DERIV val x)))        ; NTH-DERIV(f, succ n) = x |-> DERIV(val, x)

;;; f^(1) = the derivative function  x |-> f'(x)  (PROVEN).  The recursion axiom
;;; nth-deriv-succ now fires on the literal numeral 1 directly, thanks to the
;;; numeral<->succ matcher bridge (macetes.scm: a pattern (succ n) matches a
;;; positive integer m via n:=m-1).  So concrete orders need only the NN-guard
;;; (nn-zero-in) + the two recursion rewrites -- no cut/subst/arith dance.  This
;;; is dumb-assemblable: scout closes it unaided (see [[automatable-assembly]]).
(sp '(FORALL f (== (NTH-DERIV f 1) (VNB-LAMBDA x (DERIV f x)))))
(grind)
(fact 'nn-zero-in)
(mac 'nth-deriv-succ) (mac 'nth-deriv-zero) (qrfl)
(qed 'nth-deriv-one)
