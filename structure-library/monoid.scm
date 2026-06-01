;;; monoid.scm -- MONOID and COMM-MONOID structures
;;;
;;; MONOID: carrier A, operation MUL, identity E.
;;; Accessor indices: A -> 1, MUL -> 2, E -> 3.
;;; COMM-MONOID: same shape as MONOID with an extra commutativity axiom.

(def-structure-from-clauses 'MONOID
  '((carriers A)
    (op MUL (CARTESIAN A A) A)
    (constant E A)
    (property is-associative MUL A)
    (property is-identity MUL E A)))

;;; forall s. IS-MONOID(s) => forall a,b,c in A(s). (a*b)*c = a*(b*c)
(theory-add-axiom! *current-theory* 'monoid-assoc
  '(FORALL s
     (IMPLIES (IS-MONOID s)
       (FORALL a (IMPLIES (IN a (A s))
         (FORALL b (IMPLIES (IN b (A s))
           (FORALL c (IMPLIES (IN c (A s))
             (= ((MUL s) ((MUL s) a b) c)
                ((MUL s) a ((MUL s) b c))))))))))))

;;; forall s. IS-MONOID(s) => forall a in A(s). E(s)*a = a
(theory-add-axiom! *current-theory* 'monoid-left-id
  '(FORALL s
     (IMPLIES (IS-MONOID s)
       (FORALL a (IMPLIES (IN a (A s))
         (= ((MUL s) (E s) a) a))))))

;;; forall s. IS-MONOID(s) => forall a in A(s). a*E(s) = a
(theory-add-axiom! *current-theory* 'monoid-right-id
  '(FORALL s
     (IMPLIES (IS-MONOID s)
       (FORALL a (IMPLIES (IN a (A s))
         (= ((MUL s) a (E s)) a))))))

;;; E(m) ∈ A(m) when IS-MONOID(m).
;;; DERIVED (REVIEW.md R-1): follows from the auto-generated IS-MONOID IFF.
(theory-add-axiom! *current-theory* 'monoid-identity-in
  '(FORALL m (IMPLIES (IS-MONOID m) (IN (E m) (A m)))))

;;; Carrier closed under MUL.
;;; DERIVED (REVIEW.md R-4): IS-MONOID IFF + fun-apply-type.
(theory-add-axiom! *current-theory* 'monoid-carrier-closed-mul
  '(FORALL m (FORALL a (FORALL b
      (IMPLIES (AND (IS-MONOID m) (AND (IN a (A m)) (IN b (A m))))
               (IN ((MUL m) a b) (A m)))))))

;;; -----------------------------------------------------------------------
;;; COMM-MONOID: commutative monoid -- a MONOID whose MUL is commutative.
;;; Same accessor layout as MONOID.

(def-structure-from-clauses 'COMM-MONOID
  '((carriers A)
    (op MUL (CARTESIAN A A) A)
    (constant E A)
    (property is-associative MUL A)
    (property is-identity MUL E A)
    (property is-commutative MUL A)))

(theory-add-axiom! *current-theory* 'comm-monoid-is-monoid
  '(FORALL s (IMPLIES (IS-COMM-MONOID s) (IS-MONOID s))))

(theory-add-axiom! *current-theory* 'comm-monoid-mul-comm
  '(FORALL s
     (IMPLIES (IS-COMM-MONOID s)
       (FORALL a (IMPLIES (IN a (A s))
         (FORALL b (IMPLIES (IN b (A s))
           (= ((MUL s) a b) ((MUL s) b a)))))))))
