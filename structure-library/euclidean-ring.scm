;;; euclidean-ring.scm -- EUCLIDEAN-RING: an integral domain admitting a
;;; Euclidean (degree) function with division-with-remainder.
;;;
;;; The degree function deg : A -> NN is asserted to EXIST (FORSOME deg);
;;; it is not carried as structure data.  Division-with-remainder: for every
;;; a and every nonzero b there are q, r with  a = q*b + r  and either
;;; r = ZERO or deg(r) < deg(b).  "<" on NN is written  succ(deg r) <= deg b.
;;;
;;; See commutative-ring.scm for the IS-X-as-predicate rationale.
;;; Dependencies: ring.scm, commutative-ring.scm, integral-domain.scm,
;;; field.scm, number-systems.scm (NN, succ, <=).

;;; IS-EUCLIDEAN-RING: an integral domain with a Euclidean degree function.
;;; Conservative IFF definition of the fresh predicate -> `definitional', so
;;; unfolding it (euclidean-ring-is-integral-domain) carries no debt.
(fluid-let ((*current-provenance* 'definitional))
  (theory-add-axiom! *current-theory* 'is-euclidean-ring-def
    '(FORALL s
       (IFF (IS-EUCLIDEAN-RING s)
            (AND (IS-INTEGRAL-DOMAIN s)
              (FORSOME deg
                (AND (IN deg (FUN (A s) NN))
                  (FORALL a (IMPLIES (IN a (A s))
                    (FORALL b (IMPLIES (IN b (A s))
                      (IMPLIES (NOT (= b (ZERO s)))
                        (FORSOME q (AND (IN q (A s))
                          (FORSOME r (AND (IN r (A s))
                            (AND (= a ((ADD s) ((MUL s) q b) r))
                                 (OR (= r (ZERO s))
                                     (<= (succ (deg r)) (deg b))))))))))))))))))))

;;; Relation: every Euclidean ring is an integral domain.
;;; PROVEN modulo 0 via mac-h in structure-library/subtype-laws.scm (unfold
;;; is-euclidean-ring-def; IS-INTEGRAL-DOMAIN is a literal RHS conjunct).

;;; The "every field is a Euclidean ring (degree = constant 0)" relation is
;;; provided by the view FIELD-AS-EUCLIDEAN-RING in views.scm, since FIELD
;;; and EUCLIDEAN-RING have different shapes (FIELD's 8-slot shape includes
;;; NON-ZERO and INV which EUCLIDEAN-RING doesn't carry).

;;; Associated proper class EUCLIDEAN-RING = { s | IS-EUCLIDEAN-RING(s) }.
;;; See commutative-ring.scm for the NAME-class rationale.  Parent-class
;;; reading: s in EUCLIDEAN-RING <=> s in INTEGRAL-DOMAIN and a Euclidean
;;; degree function exists.
(theory-add-axiom! *current-theory* 'euclidean-ring-class
  '(FORALL s (IFF (IN s EUCLIDEAN-RING) (IS-EUCLIDEAN-RING s))))

(register-definitional-structure! 'EUCLIDEAN-RING 'INTEGRAL-DOMAIN)
