;;; operation-properties.scm -- named properties of operations.
;;;
;;; Associativity, commutativity, having an identity, having inverses,
;;; distributivity, being a metric -- each is an important concept in its
;;; own right, defined ONCE here as a predicate, then referenced by name in
;;; structure declarations via a (property NAME accessor ...) clause.
;;; build-is-axiom (structures.scm) conjoins the referenced property,
;;; applied to the structure's accessors, into the IS-X definition -- so a
;;; structure genuinely carries its axioms and IS-X means what it says.
;;;
;;; Parameter names avoid the registered accessor constants (A, MUL, E, INV,
;;; ADD, NEG, ZERO, ONE, X, D, ...): the reader case-folds, so a bound `A`
;;; would collide with the carrier accessor `A`.  Hence op / crr / unit /
;;; invop / dist, and inner element vars u, v, w.  These names are invisible
;;; to the structure declarations (the property clause names accessors; the
;;; matcher substitutes).  Dependencies: none beyond the kernel.

;;; is-associative(op, crr): op is associative on crr.
(def-predicate 'is-associative '(op crr)
  '(FORALL u (IMPLIES (IN u crr)
     (FORALL v (IMPLIES (IN v crr)
       (FORALL w (IMPLIES (IN w crr)
         (= (op (op u v) w) (op u (op v w))))))))))

;;; is-commutative(op, crr): op is commutative on crr.
(def-predicate 'is-commutative '(op crr)
  '(FORALL u (IMPLIES (IN u crr)
     (FORALL v (IMPLIES (IN v crr)
       (= (op u v) (op v u)))))))

;;; is-identity(op, unit, crr): unit is a two-sided identity for op on crr.
(def-predicate 'is-identity '(op unit crr)
  '(FORALL u (IMPLIES (IN u crr)
     (AND (= (op unit u) u) (= (op u unit) u)))))

;;; has-inverses(op, unit, invop, crr): invop gives two-sided op-inverses
;;; relative to the identity unit, on crr.
(def-predicate 'has-inverses '(op unit invop crr)
  '(FORALL u (IMPLIES (IN u crr)
     (AND (= (op (invop u) u) unit)
          (= (op u (invop u)) unit)))))

;;; is-distributive(addop, mulop, crr): mulop distributes over addop, both
;;; sides, on crr.
(def-predicate 'is-distributive '(addop mulop crr)
  '(FORALL u (IMPLIES (IN u crr)
     (FORALL v (IMPLIES (IN v crr)
       (FORALL w (IMPLIES (IN w crr)
         (AND (= (mulop u (addop v w))
                 (addop (mulop u v) (mulop u w)))
              (= (mulop (addop u v) w)
                 (addop (mulop u w) (mulop v w)))))))))))

;;; is-norm(nrm, addop, mulop, zero, crr): nrm : crr -> RR is a (multiplicative)
;;; norm on crr -- nonnegative, zero only at zero, multiplicative on mulop,
;;; subadditive on addop.  Used as the characteristic property of NORMED-FIELD.
(def-predicate 'is-norm '(nrm addop mulop zero crr)
  '(AND (IN nrm (FUN crr RR))
     (FORALL a (IMPLIES (IN a crr)
       (AND (<= 0 (nrm a))
         (AND (IFF (= (nrm a) 0) (= a zero))
           (FORALL b (IMPLIES (IN b crr)
             (AND (= (nrm (mulop a b)) (* (nrm a) (nrm b)))
                  (<= (nrm (addop a b))
                      (+ (nrm a) (nrm b))))))))))))

;;; is-group-norm(nrm, op, invop, unit, crr): nrm : crr -> RR is a norm on the
;;; abelian group (crr, op, unit, invop) -- nonnegative, zero only at the
;;; identity, invariant under inverse, and subadditive over op.  Unlike
;;; is-norm there is NO multiplicativity clause: a group carries one operation,
;;; not a ring's two.  Characteristic property of NORMED-AG.
(def-predicate 'is-group-norm '(nrm op invop unit crr)
  '(AND (IN nrm (FUN crr RR))
     (FORALL u (IMPLIES (IN u crr)
       (AND (<= 0 (nrm u))
         (AND (IFF (= (nrm u) 0) (= u unit))
           (AND (= (nrm (invop u)) (nrm u))
             (FORALL v (IMPLIES (IN v crr)
               (<= (nrm (op u v)) (+ (nrm u) (nrm v))))))))))))

;;; is-metric(dist, crr): dist is a metric on crr -- nonnegative, zero only
;;; on the diagonal, symmetric, and satisfying the triangle inequality.
;;; Conservative IFF definition of the property -> `definitional' (def-predicate
;;; stamps that at source).  The five metric laws (metric-pos/self-zero/zero-eq/
;;; sym/triangle) are PROVEN by projecting this body (metric-laws.scm), so they
;;; must rest on it as a definition, not as asserted debt.
(def-predicate 'is-metric '(dist crr)
  '(FORALL u (IMPLIES (IN u crr)
     (AND (= (dist u u) 0)
       (FORALL v (IMPLIES (IN v crr)
         (AND (<= 0 (dist u v))
           (AND (IMPLIES (= (dist u v) 0) (= u v))
             (AND (= (dist u v) (dist v u))
               (FORALL w (IMPLIES (IN w crr)
                 (<= (dist u w)
                     (+ (dist u v) (dist v w))))))))))))))
