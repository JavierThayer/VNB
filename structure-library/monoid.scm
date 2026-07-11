;;; monoid.scm -- MONOID and COMM-MONOID structures
;;;
;;; MONOID: carrier CARR, operation MUL, identity IDEN.
;;; Accessor indices: CARR -> 1, MUL -> 2, IDEN -> 3.
;;; COMM-MONOID: same shape as MONOID with an extra commutativity axiom.

(def-structure-from-clauses 'MONOID
  '((carriers CARR)
    (op MUL (CARTESIAN CARR CARR) CARR)
    (constant IDEN CARR)
    (property is-associative MUL CARR)
    (property is-identity MUL IDEN CARR)))

;;; forall s. IS-MONOID(s) => forall a,b,c in CARR(s). (a*b)*c = a*(b*c)
(theory-add-axiom! *current-theory* 'monoid-assoc
  '(FORALL s
     (IMPLIES (IS-MONOID s)
       (FORALL a (IMPLIES (IN a (CARR s))
         (FORALL b (IMPLIES (IN b (CARR s))
           (FORALL c (IMPLIES (IN c (CARR s))
             (= ((MUL s) ((MUL s) a b) c)
                ((MUL s) a ((MUL s) b c))))))))))))

;;; forall s. IS-MONOID(s) => forall a in CARR(s). IDEN(s)*a = a
(theory-add-axiom! *current-theory* 'monoid-left-id
  '(FORALL s
     (IMPLIES (IS-MONOID s)
       (FORALL a (IMPLIES (IN a (CARR s))
         (= ((MUL s) (IDEN s) a) a))))))

;;; forall s. IS-MONOID(s) => forall a in CARR(s). a*IDEN(s) = a
(theory-add-axiom! *current-theory* 'monoid-right-id
  '(FORALL s
     (IMPLIES (IS-MONOID s)
       (FORALL a (IMPLIES (IN a (CARR s))
         (= ((MUL s) a (IDEN s)) a))))))

;;; IDEN(m) ∈ CARR(m) when IS-MONOID(m).
;;; DERIVED (REVIEW.md R-1): follows from the auto-generated IS-MONOID IFF.
(theory-add-axiom! *current-theory* 'monoid-identity-in
  '(FORALL m (IMPLIES (IS-MONOID m) (IN (IDEN m) (CARR m)))))

;;; Carrier closed under MUL.
;;; DERIVED (REVIEW.md R-4): IS-MONOID IFF + fun-apply-type.
(theory-add-axiom! *current-theory* 'monoid-carrier-closed-mul
  '(FORALL m (FORALL a (FORALL b
      (IMPLIES (AND (IS-MONOID m) (AND (IN a (CARR m)) (IN b (CARR m))))
               (IN ((MUL m) a b) (CARR m)))))))

;;; -----------------------------------------------------------------------
;;; COMM-MONOID: commutative monoid -- a MONOID whose MUL is commutative.
;;; Same accessor layout as MONOID.

(def-structure-from-clauses 'COMM-MONOID
  '((carriers CARR)
    (op MUL (CARTESIAN CARR CARR) CARR)
    (constant IDEN CARR)
    (property is-associative MUL CARR)
    (property is-identity MUL IDEN CARR)
    (property is-commutative MUL CARR)))

(theory-add-axiom! *current-theory* 'comm-monoid-is-monoid
  '(FORALL s (IMPLIES (IS-COMM-MONOID s) (IS-MONOID s))))

(theory-add-axiom! *current-theory* 'comm-monoid-mul-comm
  '(FORALL s
     (IMPLIES (IS-COMM-MONOID s)
       (FORALL a (IMPLIES (IN a (CARR s))
         (FORALL b (IMPLIES (IN b (CARR s))
           (= ((MUL s) a b) ((MUL s) b a)))))))))

;;; Notation -- read by wff->english / the proof reader (operators.scm).
(notation! 'IS-MONOID               'noun "monoid" 'article "a")
