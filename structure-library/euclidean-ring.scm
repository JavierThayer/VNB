;;; euclidean-ring.scm -- EUCLIDEAN-RING: an integral domain admitting a
;;; Euclidean (degree) function with division-with-remainder.
;;;
;;; The degree function dg : CARR -> NN is asserted to EXIST (FORSOME dg);
;;; it is not carried as structure data.  Division-with-remainder: for every
;;; a and every nonzero b there are q, r with  a = q*b + r  and either
;;; r = ZERO or dg(r) < dg(b).  "<" on NN is written  succ(dg r) <= dg b.
;;;
;;; See commutative-ring.scm for the IS-X-as-predicate rationale.
;;; Dependencies: ring.scm, commutative-ring.scm, integral-domain.scm,
;;; field.scm, number-systems.scm (NN, succ, <=).
;;; RETIRED 2026-09-14 (proven): euclidean-ring-has-gauge -- theorem-library/gauge-is-degree.scm
;;; RETIRED 2026-09-14 (proven): gauges-mem-build -- theorem-library/gauge-is-degree.scm
;;; RETIRED 2026-09-14 (proven): gauges-in-fun -- theorem-library/gauge-is-degree.scm
;;; RETIRED 2026-09-14 (proven): gauges-spec -- theorem-library/gauge-is-degree.scm
;;; RETIRED 2026-09-14 (proven): gauge-is-degree -- theorem-library/gauge-is-degree.scm

;;; IS-EUCLIDEAN-RING: an integral domain with a Euclidean degree function.
;;; Conservative IFF definition of the fresh predicate -> `definitional', so
;;; unfolding it (euclidean-ring-is-integral-domain) carries no debt.
(declare-structure EUCLIDEAN-RING
  (instance-var s)
  (same-shape-as INTEGRAL-DOMAIN)
  ;; The degree function's binder is `dg', NOT `deg': `DEG' is a registered
  ;; functoid (the polynomial degree, structure-library/poly-degree.scm), and
  ;; the head registry is scope-blind -- a bound `deg' appearing APPLIED reads
  ;; as that constant, so the quantifier would bind a name the body never uses.
  ;; `constant-binder-audit' makes this FATAL.  `dg' is this file's own choice
  ;; everywhere else (EUCLIDEAN-GAUGES, gauges-mem-build, gauges-spec).
  (law "forsome([dg in fun(carr(s), nn)],
          forall([a in carr(s), b in carr(s)],
            not(b = zero(s)) implies
              forsome([q in carr(s), r in carr(s)],
                a = add(s)(mul(s)(q, b), r)
                and (r = zero(s) or succ(dg(r)) <= dg(b)))))"))

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

;;; -----------------------------------------------------------------------
;;; The Euclidean gauge as a NAMED function, via the global epsilon.
;;;
;;; is-euclidean-ring-def asserts a degree function EXISTS (FORSOME dg) but
;;; leaves it un-named, forcing existential-elimination into a throwaway
;;; eigenconstant every time it is used.  Following the centre-extraction
;;; pattern (compactness.scm: CENTRES/CENTRE-SET), we NAME it with the global
;;; Hilbert epsilon: GAUGE(s) is a chosen valid degree function, defined exactly
;;; when one exists (the iota/epsilon definedness proviso), i.e. when s is a
;;; Euclidean ring.  gauge-is-degree (proven, archive/calculus-pre-rename/gauge-proof.scm) is the
;;; soundness fact: GAUGE(s) really is a degree function.

;;; HAS-DIV-REMAINDER(s, dg): dg gives division-with-remainder on s.  The body
;;; is the division-with-remainder clause of is-euclidean-ring-def, named once.
;;; (Inner element var a_ avoids the case-fold clash with the carrier accessor,
;;; named `A' when this was written and `CARR' now; the name is kept.)
(def-predicate 'HAS-DIV-REMAINDER '(s dg)
  '(FORALL a_ (IMPLIES (IN a_ (CARR s))
     (FORALL b (IMPLIES (IN b (CARR s))
       (IMPLIES (NOT (= b (ZERO s)))
         (FORSOME q (AND (IN q (CARR s))
           (FORSOME r (AND (IN r (CARR s))
             (AND (= a_ ((ADD s) ((MUL s) q b) r))
                  (OR (= r (ZERO s))
                      (<= (succ (dg r)) (dg b))))))))))))))

;;; EUCLIDEAN-GAUGES(s): the set of valid degree functions on s.
(def-functoid 'EUCLIDEAN-GAUGES '(s)
  '(SEP dg (FUN (CARR s) NN) (HAS-DIV-REMAINDER s dg)))

;;; GAUGE(s): a chosen degree function -- the global epsilon pick of a valid one.
(def-functoid 'GAUGE '(s) '(CHOICE (EUCLIDEAN-GAUGES s)))

;;; A Euclidean ring HAS a gauge: the directly-usable existential conjunct of
;;; is-euclidean-ring-def (its division clause, named HAS-DIV-REMAINDER).

;;; SEP-membership slices of EUCLIDEAN-GAUGES (definitional).

;;; gauge-is-degree: the chosen GAUGE(s) really is a valid degree function --
;;; the soundness of the epsilon pick (defined because the gauge set is
;;; inhabited).  MACHINE-PROVEN in archive/calculus-pre-rename/gauge-proof.scm.

;;; Notation -- read by wff->english / the proof reader (operators.scm).
(notation! 'IS-EUCLIDEAN-RING     'kind 'predicate 'arity 1 'noun "Euclidean ring" 'article "a")

;;; -----------------------------------------------------------------------
;;; Notation -- the ENGLISH of these predicates, declared beside their
;;; definitions and read by wff->english / the proof reader (operators.scm).
;;; A def-predicate's reading cannot be derived the way a structure's noun can
;;; (noun vs adjective: IS-COMPLETE wants "s is complete", not "s is a complete"),
;;; so it is written here, once, next to what it means.
(notation! 'HAS-DIV-REMAINDER 'kind 'predicate 'arity 2
           'english "$1 has division with remainder for the degree function $2")
