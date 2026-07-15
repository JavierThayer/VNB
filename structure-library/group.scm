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

;;; forall s. IS-GROUP(s) => forall a,b,c in CARR(s). (a*b)*c = a*(b*c)
(theory-add-axiom! *current-theory* 'group-assoc
  '(FORALL s
     (IMPLIES (IS-GROUP s)
       (FORALL a (IMPLIES (IN a (CARR s))
         (FORALL b (IMPLIES (IN b (CARR s))
           (FORALL c (IMPLIES (IN c (CARR s))
             (= ((OPR s) ((OPR s) a b) c)
                ((OPR s) a ((OPR s) b c))))))))))))

;;; forall s. IS-GROUP(s) => forall a in CARR(s). IDEN(s)*a = a
(theory-add-axiom! *current-theory* 'group-left-id
  '(FORALL s
     (IMPLIES (IS-GROUP s)
       (FORALL a (IMPLIES (IN a (CARR s))
         (= ((OPR s) (IDEN s) a) a))))))

;;; forall s. IS-GROUP(s) => forall a in CARR(s). INV(s)(a)*a = IDEN(s)
(theory-add-axiom! *current-theory* 'group-left-inv
  '(FORALL s
     (IMPLIES (IS-GROUP s)
       (FORALL a (IMPLIES (IN a (CARR s))
         (= ((OPR s) ((INV s) a) a) (IDEN s)))))))

;;; IDEN(s) in CARR(s) when IS-GROUP(s).
;;; DERIVED: follows from the auto-generated IS-GROUP IFF -- the `constant E A`
;;; clause contributes the conjunct (IN (IDEN s) (CARR s)).  Installed for direct
;;; use, mirroring monoid-identity-in in monoid.scm; demote when proven.
(theory-add-axiom! *current-theory* 'group-identity-in
  '(FORALL s (IMPLIES (IS-GROUP s) (IN (IDEN s) (CARR s)))))

;;; Notation -- read by wff->english / the proof reader (operators.scm).
(notation! 'IS-GROUP                'noun "group" 'article "a")
