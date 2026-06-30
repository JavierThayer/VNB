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
(def-predicate 'is-norm '(nm addop mulop zr crr)
  '(AND (IN nm (FUN crr RR))
     (FORALL a (IMPLIES (IN a crr)
       (AND (<= 0 (nm a))
         (AND (IFF (= (nm a) 0) (= a zr))
           (FORALL b (IMPLIES (IN b crr)
             (AND (= (nm (mulop a b)) (* (nm a) (nm b)))
                  (<= (nm (addop a b))
                      (+ (nm a) (nm b))))))))))))

;;; is-group-norm(nrm, op, invop, unit, crr): nrm : crr -> RR is a norm on the
;;; abelian group (crr, op, unit, invop) -- nonnegative, zero only at the
;;; identity, invariant under inverse, and subadditive over op.  Unlike
;;; is-norm there is NO multiplicativity clause: a group carries one operation,
;;; not a ring's two.  Characteristic property of NORMED-AG.
(def-predicate 'is-group-norm '(nm op invop unit crr)
  '(AND (IN nm (FUN crr RR))
     (FORALL u (IMPLIES (IN u crr)
       (AND (<= 0 (nm u))
         (AND (IFF (= (nm u) 0) (= u unit))
           (AND (= (nm (invop u)) (nm u))
             (FORALL v (IMPLIES (IN v crr)
               (<= (nm (op u v)) (+ (nm u) (nm v))))))))))))

;;; is-metric(dist, crr): dist is a metric on crr -- nonnegative, zero only
;;; on the diagonal, symmetric, and satisfying the triangle inequality.
;;; Conservative IFF definition of the property -> `definitional' (def-predicate
;;; stamps that at source).  The five metric laws (metric-pos/self-zero/zero-eq/
;;; sym/triangle) are PROVEN by projecting this body (metric-laws.scm), so they
;;; must rest on it as a definition, not as asserted debt.
(def-predicate 'is-metric '(dst crr)
  '(FORALL u (IMPLIES (IN u crr)
     (AND (= (dst u u) 0)
       (FORALL v (IMPLIES (IN v crr)
         (AND (<= 0 (dst u v))
           (AND (IMPLIES (= (dst u v) 0) (= u v))
             (AND (= (dst u v) (dst v u))
               (FORALL w (IMPLIES (IN w crr)
                 (<= (dst u w)
                     (+ (dst u v) (dst v w))))))))))))))
