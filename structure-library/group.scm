;;; group.scm -- GROUP structure
;;;
;;; Carrier CARR, operation OPR, identity IDEN, inverse INV.
;;; Accessor indices: CARR -> 1, OPR -> 2, IDEN -> 3, INV -> 4.
;;; Three axioms (left-only) suffice: assoc + left-id + left-inv.

(declare-structure GROUP
  (carriers CARR)
  (op OPR (CARTESIAN CARR CARR) CARR)
  (constant IDEN CARR)
  (op INV CARR CARR)
  (property is-associative OPR CARR)
  (property is-identity OPR IDEN CARR)
  (property has-inverses OPR IDEN INV CARR))

;;; The three group laws --
;;;
;;;   group-assoc        forall a,b,c in CARR(s). (a*b)*c = a*(b*c)
;;;   group-left-id      forall a in CARR(s). IDEN(s)*a = a
;;;   group-left-inv     forall a in CARR(s). INV(s)(a)*a = IDEN(s)
;;;
;;; -- and group-identity-in (IDEN(s) in CARR(s)) are each a conjunct of the
;;; IS-GROUP definition the declaration above generates: the first three unfold
;;; out of the `property' clauses, the last out of the `constant IDEN CARR' slot.
;;; They were asserted here, unwarranted, so every proof that used a group law
;;; billed `trust: none'.  All four are now PROVEN modulo 0 in
;;; structure-library/subtype-laws.scm (which loads after the interactive
;;; tactics); no longer asserted here.

;;; Notation -- read by wff->english / the proof reader (operators.scm).
(notation! 'IS-GROUP                'noun "group" 'article "a")
