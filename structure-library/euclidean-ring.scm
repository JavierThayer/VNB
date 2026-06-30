;;; euclidean-ring.scm -- EUCLIDEAN-RING: an integral domain admitting a
;;; Euclidean (degree) function with division-with-remainder.
;;;
;;; The degree function deg : CARR -> NN is asserted to EXIST (FORSOME deg);
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
                (AND (IN deg (FUN (CARR s) NN))
                  (FORALL a (IMPLIES (IN a (CARR s))
                    (FORALL b (IMPLIES (IN b (CARR s))
                      (IMPLIES (NOT (= b (ZERO s)))
                        (FORSOME q (AND (IN q (CARR s))
                          (FORSOME r (AND (IN r (CARR s))
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

;;; -----------------------------------------------------------------------
;;; The Euclidean gauge as a NAMED function, via the global epsilon.
;;;
;;; is-euclidean-ring-def asserts a degree function EXISTS (FORSOME deg) but
;;; leaves it un-named, forcing existential-elimination into a throwaway
;;; eigenconstant every time it is used.  Following the centre-extraction
;;; pattern (compactness.scm: CENTRES/CENTRE-SET), we NAME it with the global
;;; Hilbert epsilon: GAUGE(s) is a chosen valid degree function, defined exactly
;;; when one exists (the iota/epsilon definedness proviso), i.e. when s is a
;;; Euclidean ring.  gauge-is-degree (proven, calculus/gauge-proof.scm) is the
;;; soundness fact: GAUGE(s) really is a degree function.

;;; HAS-DIV-REMAINDER(s, deg): deg gives division-with-remainder on s.  The body
;;; is the division-with-remainder clause of is-euclidean-ring-def, named once.
;;; (Inner element var a_ avoids the case-fold clash with the carrier accessor A.)
(def-predicate 'HAS-DIV-REMAINDER '(s deg)
  '(FORALL a_ (IMPLIES (IN a_ (CARR s))
     (FORALL b (IMPLIES (IN b (CARR s))
       (IMPLIES (NOT (= b (ZERO s)))
         (FORSOME q (AND (IN q (CARR s))
           (FORSOME r (AND (IN r (CARR s))
             (AND (= a_ ((ADD s) ((MUL s) q b) r))
                  (OR (= r (ZERO s))
                      (<= (succ (deg r)) (deg b))))))))))))))

;;; EUCLIDEAN-GAUGES(s): the set of valid degree functions on s.
(def-functoid 'EUCLIDEAN-GAUGES '(s)
  '(SEP dg (FUN (CARR s) NN) (HAS-DIV-REMAINDER s dg)))

;;; GAUGE(s): a chosen degree function -- the global epsilon pick of a valid one.
(def-functoid 'GAUGE '(s) '(CHOICE (EUCLIDEAN-GAUGES s)))

;;; A Euclidean ring HAS a gauge: the directly-usable existential conjunct of
;;; is-euclidean-ring-def (its division clause, named HAS-DIV-REMAINDER).
(support 'euclidean-ring-has-gauge
  '(FORALL s (IMPLIES (IS-EUCLIDEAN-RING s)
     (FORSOME deg (AND (IN deg (FUN (CARR s) NN)) (HAS-DIV-REMAINDER s deg))))))
(warrant! 'euclidean-ring-has-gauge 'well-known
  "The existential conjunct of is-euclidean-ring-def: a Euclidean ring admits a
   degree function deg : CARR(s) -> NN with division-with-remainder (HAS-DIV-
   REMAINDER s deg).  Definitional once HAS-DIV-REMAINDER names the clause.")

;;; SEP-membership slices of EUCLIDEAN-GAUGES (definitional).
(support 'gauges-mem-build
  '(FORALL s (FORALL dg (IMPLIES (IN dg (FUN (CARR s) NN))
       (IMPLIES (HAS-DIV-REMAINDER s dg) (IN dg (EUCLIDEAN-GAUGES s)))))))
(support 'gauges-in-fun
  '(FORALL s (FORALL dg (IMPLIES (IN dg (EUCLIDEAN-GAUGES s)) (IN dg (FUN (CARR s) NN))))))
(support 'gauges-spec
  '(FORALL s (FORALL dg (IMPLIES (IN dg (EUCLIDEAN-GAUGES s)) (HAS-DIV-REMAINDER s dg)))))
(warrant! 'gauges-mem-build 'well-known "SEP-membership of EUCLIDEAN-GAUGES (definitional).")
(warrant! 'gauges-in-fun    'well-known "EUCLIDEAN-GAUGES(s) is a SEP-subset of FUN(CARR s, NN) (definitional).")
(warrant! 'gauges-spec      'well-known "Each member of EUCLIDEAN-GAUGES(s) has division-with-remainder (definitional).")

;;; gauge-is-degree: the chosen GAUGE(s) really is a valid degree function --
;;; the soundness of the epsilon pick (defined because the gauge set is
;;; inhabited).  MACHINE-PROVEN in calculus/gauge-proof.scm.
(support 'gauge-is-degree
  '(FORALL s (IMPLIES (IS-EUCLIDEAN-RING s)
     (AND (IN (GAUGE s) (FUN (CARR s) NN))
          (HAS-DIV-REMAINDER s (GAUGE s))))))
(warrant! 'gauge-is-degree 'proof
  "GAUGE(s) = CHOICE(EUCLIDEAN-GAUGES s) is in FUN(CARR s, NN) and has division-
   with-remainder: IS-EUCLIDEAN-RING(s) makes EUCLIDEAN-GAUGES(s) inhabited
   (euclidean-ring-has-gauge + gauges-mem-build), so the epsilon pick lands in
   it (choice-axiom) and the SEP slices give both conjuncts.  MACHINE-PROVEN in
   calculus/gauge-proof.scm.")
