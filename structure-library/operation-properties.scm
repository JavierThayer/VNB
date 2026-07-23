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
;;; Parameter names avoid the registered accessor constants (CARR, MUL, IDEN,
;;; INV, ADD, NEG, ZERO, ONE, PTS, DIST, ...): the reader case-folds, so a bound
;;; `CARR` would collide with the carrier accessor `CARR`.  (These were the single
;;; letters A, MUL, E, INV, ..., X, D when this was written; no accessor is a
;;; single letter now.)  Hence op / crr / unit /
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

;;; is-pseudometric(dist, crr): is-metric MINUS identity-of-indiscernibles --
;;; nonnegative, zero on the diagonal, symmetric, triangle, but d(u,v)=0 is
;;; ALLOWED for u /= v.  Exactly the is-metric body with the clause
;;; `(IMPLIES (= (dst u v) 0) (= u v))' dropped.  A metric is a pseudometric that
;;; additionally separates points; this is the property a gauge topology needs.
(def-predicate 'is-pseudometric '(dst crr)
  '(FORALL u (IMPLIES (IN u crr)
     (AND (= (dst u u) 0)
       (FORALL v (IMPLIES (IN v crr)
         (AND (<= 0 (dst u v))
           (AND (= (dst u v) (dst v u))
             (FORALL w (IMPLIES (IN w crr)
               (<= (dst u w)
                   (+ (dst u v) (dst v w)))))))))))))

;;; -----------------------------------------------------------------------
;;; Notation -- the ENGLISH of these predicates, declared beside their
;;; definitions and read by wff->english / the proof reader (operators.scm).
;;; A def-predicate's reading cannot be derived the way a structure's noun can
;;; (noun vs adjective: IS-COMPLETE wants "s is complete", not "s is a complete"),
;;; so it is written here, once, next to what it means.
(notation! 'IS-ASSOCIATIVE 'kind 'predicate 'arity 2
           'english "$1 is associative on $2")
(notation! 'IS-COMMUTATIVE 'kind 'predicate 'arity 2
           'english "$1 is commutative on $2")
(notation! 'IS-IDENTITY 'kind 'predicate 'arity 3
           'english "$2 is an identity for $1 on $3")
(notation! 'IS-DISTRIBUTIVE 'kind 'predicate 'arity 3
           'english "$2 distributes over $1 on $3")
(notation! 'HAS-INVERSES 'kind 'predicate 'arity 4
           'english "every element of $4 has an inverse under $1, given by $3, with unit $2")
(notation! 'IS-METRIC 'kind 'predicate 'arity 2
           'english "$1 is a metric on $2")
(notation! 'IS-PSEUDOMETRIC 'kind 'predicate 'arity 2
           'english "$1 is a pseudometric on $2")
(notation! 'IS-NORM 'kind 'predicate 'arity 5
           'english "$1 is a norm on $5")
(notation! 'IS-GROUP-NORM 'kind 'predicate 'arity 5
           'english "$1 is a group norm for $2 on $5")
