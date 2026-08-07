;;; load.scm -- load the proof checker in dependency order
;;;
;;; File names are passed without extension so MIT Scheme picks the
;;; compiled .com file when present, falling back to the .scm source.
;;; Recompile with (compile-vnb!) below or via the Makefile.

(define *prover-dir*
  (directory-namestring (current-load-pathname)))

;; MIT's `current-load-pathname' SIGNALS "No file being loaded." at the REPL --
;; it does NOT return #f, as several call sites (install-theorem!, register-
;; operator!, def-functoid, ...) assume with a `(when src ...)' guard.  So a
;; theorem installed INTERACTIVELY -- the `qed' of a proof typed at the prompt --
;; threw before the guard.  The throw is NOT a normal condition (neither
;; ignore-errors nor bind-condition-handler on condition-type/error catches it),
;; so we cannot catch it -- we GATE on *vnb-loading* (held #t across the whole
;; library load below, #f at the REPL) and only call it when a load is active.
;; Ad-hoc `./prover file.scm' scripts also read #f here, so their theorems record
;; no source pathname -- harmless (source is used for the browser's library
;; links).  (2026-07-27; the user hit it doing (qed 'scratch) after a live proof.)
(define (safe-load-pathname)
  (and *vnb-loading* (current-load-pathname)))

;; Held #t for the whole load.  Several entries in *vnb-files* (the
;; theorem-library / calculus proof scripts) run real interactive
;; (sp ...) ... (qed ...) sequences, and every tactic ends in (show).  With
;; this flag off, a fresh load dumps ~250 full sequent states to the terminal
;; -- which then looks, to whoever just started the prover, like THEIR command
;; printed a giant foreign proof.  show consults this (interactive.scm) so the
;; library still verifies at load (the qed ledger lines use display, not show,
;; so they still print) without the per-tactic flood.  Reset to #f at end.
(define *vnb-loading* #t)

;;; Generated reference artifacts (THEOREMS.md, STRUCTURE-INDEX.md, the
;;; structure graph, ...) are written here, out of the source root.
(define *reference-dir*
  (string-append *prover-dir* "reference/"))

;;; Proof printouts (reader sketches, full step-traces) keep their .tex here,
;;; IN the source tree so they ride the source tarball -- unlike the PDFs, which
;;; are regenerable and stay in ~/.cache/vnb/tex/.  A reader must be able to read
;;; the proof output after unpacking without a running prover.
(define *printouts-dir*
  (string-append *prover-dir* "printouts/"))

(define *vnb-files*
  '(;; Core kernel
    "errors"
    "expressions"
    "operators"
    "wff"
    "sequents"
    "parser"
    "deduction-graphs"
    "primitive-inferences"
    "arith-eval"
    "macetes"
    "theory"
    "structures"
    ;; Book registry — sources a `reference' warrant may cite by key.  Must
    ;; precede every structure-library / theorem-library file that cites one.
    "structure-library/references"
    ;; Named operation properties — referenced by structure declarations.
    "structure-library/operation-properties"
    ;; Theorem library (axioms not yet derivable from kernel)
    "theorem-library/axioms"
    "theorem-library/well-ordering"
    ;; The NBG facts about SET the kernel rules do not give -- chiefly that a
    ;; class included in a set is a set.  Foundational: loaded with them.
    "structure-library/set-basics"
    ;; Function composition f o g -- a general FUN operation (needs only the
    ;; FUN/apply axioms in theory.scm), so loaded with the foundations.
    "structure-library/compose"
    ;; Structure library (algebraic structures, number-system instances,
    ;; ordinals, cardinality, sequences, complex extensions, ring-simplify)
    "structure-library/semigroup"
    "structure-library/monoid"
    "structure-library/group"
    "structure-library/abelian-group"
    "structure-library/ring"
    "structure-library/metric-space"
    "structure-library/setoid"
    ;; RINGOID = [R, I]: a ring with a distinguished two-sided ideal.  The ring
    ;; analogue of SETOID; the ideal induces the congruence a~b iff a-b in I, and
    ;; R/I is the setoid quotient with ring operations descended.  Needs ring +
    ;; setoid (the view target, wired in a later increment).
    "structure-library/ringoid"
    "structure-library/metric-topology"
    "structure-library/ring-simplify"
    ;; Commutative-ring identity decision procedure (multiset monomials);
    ;; reuses ring-simplify's poly plumbing, so loads right after it.
    "structure-library/comm-ring-simplify"
    ;; Linear-arithmetic decision core (Fourier-Motzkin + Farkas certificates),
    ;; the engine behind the (ineq) oracle.  Pure Scheme, no deps; the kernel
    ;; integration (term parsing, pi-ineq!, (ineq)) is a separate file.
    "structure-library/linear-arith"
    ;; The (ineq) oracle: linearizes a goal + named premises over RR (atoms =
    ;; maximal non-arithmetic subterms), runs the FM engine, closes via pi-ineq!
    ;; with a Farkas certificate.  Needs linear-arith + kernel (dg/sequent).
    "structure-library/ineq-oracle"
    ;; Exact-rational LP feasibility-with-witness (Phase-I simplex); the
    ;; nonnegative-combination solver behind the (sos) oracle.  Pure Scheme,
    ;; reuses linear-arith's alist helpers, so loads after it.
    "structure-library/sos-arith"
    ;; The (sos) sum-of-squares oracle: the nonlinear companion of (ineq).
    ;; Closes a <= b over RR from a supplied list of square certificates, via
    ;; crs's commutative-poly normal form + sos-arith's nonneg solve.  Needs
    ;; comm-ring-simplify + ineq-oracle + sos-arith + kernel.
    "structure-library/sos-oracle"
    "number-systems"
    ;; The recursion equations for + and * on NN (a + succ b = succ(a+b),
    ;; a * succ b = a*b + a).  number-systems gives NN's + and * their algebraic
    ;; laws and NEVER relates them to succ, so induction over NN arithmetic
    ;; cannot cross the succ/+ boundary.  Asserted, warranted `reference'; every
    ;; consequence (succ n = n+1, cancellation, parity) is PROVEN from them in
    ;; theorem-library/nn-parity-proof.
    "structure-library/nn-arith"
    ;; ZZ is GENERATED by NN (every integer is n or -n).  number-systems.scm
    ;; axiomatizes ZZ as a commutative ring containing NN -- of which QQ is a
    ;; model, so `2k /= 1' and the parity dichotomy are FALSE in a model of the
    ;; theory without this.  Asserted, warranted `reference'; parity is proved
    ;; from it in theorem-library/parity.
    "structure-library/zz-arith"
    "structure-library/order-predicates"
    ;; The finite order calculus of RR (chaining, adding inequalities, scaling,
    ;; abs bounds) -- workhorse PSS layer over the number-systems order axioms.
    "structure-library/order-lemmas"
    ;; Important elementary inequalities over RR (Young, AM-GM, QM-AM, Cauchy-
    ;; Schwarz(2), Bernoulli) plus the bounded-function family f(t)=t/(1+t);
    ;; warranted PSS supports.  Needs only the RR order calculus above.
    "structure-library/scalar-inequalities"
    ;; Rational powers a^b of positive reals (RPOW) + SQRT, introduced
    ;; axiomatically (power laws), with the scalar inequalities they unlock
    ;; (Young, AM-GM root form, Bernoulli).  Needs RR/QQ + power (number-systems).
    "structure-library/real-powers"
    ;; QQ is the fraction field of ZZ -- the one axiom number-systems.scm never
    ;; states (it gives QQ a field signature and the bare inclusion ZZ <= QQ, so
    ;; QQ = RR is a model).  Asserted, warranted `reference'; the raw material
    ;; for sqrt(2) irrational.  Needs QQ/NN (number-systems) + support/warrant!.
    "structure-library/qq-fractions"
    ;; Cauchy/convergence/completeness on a generic metric space; needs RR's
    ;; order (number-systems) and POS-RR (order-predicates).  Loaded before
    ;; complex.scm so cc-complete can be stated as IS-COMPLETE(CC-MS).
    "structure-library/metric-completeness"
    ;; Continuous maps between metric spaces (IS-CONTINUOUS(-AT),
    ;; IS-UNIFORMLY-CONTINUOUS): the morphisms of the metric-space structure.
    ;; Needs metric-space + order-predicates (POS-RR); kept with the metric
    ;; cluster, before the ring refinements.
    "structure-library/metric-continuity"
    ;; Open sets + the open-preimage characterisation of continuity.  Needs
    ;; metric-topology (BALL) and metric-continuity (IS-CONTINUOUS); stays
    ;; with the metric cluster.
    "structure-library/metric-open-sets"
    ;; TOP-SPACE [PTS, OPENS] + the functor Met -> Top (METRIC-TOP).  The two
    ;; things an accessor correspondence cannot do: TOP-SPACE's morphisms are a
    ;; PREIMAGE condition (declare-hom!, not preservation-of-slots) and the
    ;; metric topology is CONSTRUCTED from DIST (def-constructed-functor, whose
    ;; obligations are recorded, not asserted).  Needs IS-OPEN + PREIMAGE
    ;; (metric-open-sets) and the metric hom override (metric-continuity).
    "structure-library/top-space"
    ;; Compactness + the four-way characterization (calculus.pdf Prop 3.12):
    ;; IS-COMPACT / IS-OPEN-COVER / CLUSTER-POINT / HAS-FIP + the equivalences.
    ;; Needs IS-OPEN/IS-CLOSED (above), TOTALLY-BOUNDED/BALL (metric-topology),
    ;; IS-COMPLETE (metric-completeness).
    "structure-library/compactness"
    "structure-library/separable"
    ;; Algebras and sigma-algebras of sets (measure-theory vocabulary).  Needs
    ;; POWER / COMPLEMENT-IN / BIG-UNION (theory.scm) and NN (number-systems);
    ;; independent of the metric cluster it is filed after.
    "structure-library/sigma-algebra"
    ;; Restrictive ring/field structures (genuine IS-X predicates; need NN/RR
    ;; from number-systems, used by numeric-instances below).
    "structure-library/commutative-ring"
    "structure-library/integral-domain"
    "structure-library/field"
    ;; MODULE over a ring (scalar ring as a substructure slot; complete IS-MODULE
    ;; IFF incl. the four action laws).  Needs RING + operation-properties.
    "structure-library/module"
    ;; Finite-dimensional vector spaces, Zorn-free: IS-VECTOR-SPACE (module over
    ;; a field), IS-SUBMODULE, IS-NOETHERIAN (ascending chain condition), and
    ;; IS-FINITE-DIMENSIONAL (= noetherian vector space).  Vocabulary only.
    "structure-library/finite-dimensional"
    "structure-library/euclidean-ring"
    ;; Ideals, principal ideals, and principal-ideal domains over a commutative
    ;; ring (IS-IDEAL / PRINCIPAL-IDEAL / IS-PID), plus the well-ordering of NN
    ;; (nn-least-element).  Vocabulary for the Euclidean-ring => PID proof.
    "structure-library/ideal"
    "structure-library/normed-field"
    ;; Normed abelian group: AG subtype (slots CARR MUL IDEN INV) + norm NRM at
    ;; slot 5.  Needs abelian-group, operation-properties (is-group-norm),
    ;; and RR (number-systems).  Its AG view is registered in views.scm.
    "structure-library/normed-ag"
    ;; views.scm loads after all source structures (shape + definitional) so
    ;; def-functor can refer to any of them.
    "structure-library/views"
    ;; The metric space underlying a normed field (NF-METRIC-SPACE bridge).
    ;; Needs NORMED-FIELD + METRIC-SPACE; loaded after views (which finishes
    ;; the normed-field view-as declarations).
    "structure-library/normed-field-metric"
    ;; The metric space underlying a normed abelian group (NAG-METRIC-SPACE
    ;; bridge: d(u,v) = ||u . v^-1||).  Needs NORMED-AG + METRIC-SPACE; lets
    ;; "grp is complete" be stated as IS-COMPLETE(NAG-METRIC-SPACE grp).
    "structure-library/normed-ag-metric"
    ;; Real normed vector space (vocabulary): IS-NORMED-VECTOR-SPACE (module over
    ;; RR + a homogeneous norm VNRM), view-as to MODULE and NORMED-AG.  Loads
    ;; after module + normed-ag (it views into both).
    "structure-library/normed-vector-space"
    ;; Bounded linear functionals + dual norm on a normed vector space
    ;; (vocabulary): IS-LINEAR-FUNCTIONAL, IS-BOUNDED-LINEAR-FUNCTIONAL,
    ;; DUAL-NORM (IOTA least-upper-bound).  Loads after normed-vector-space.
    "structure-library/linear-functional"
    "structure-library/complex"
    ;; REDUCE + FAM-OF-LIST: kiddie n-ary <-> adult finite-fold bridge.
    ;; Consumed by numeric-instances (nary-plus-N-list axioms) and by
    ;; sequences (sum-ag-as-reduce); kernel-only deps (LIST/NTH/LENGTH/NN).
    "structure-library/reduce"
    "structure-library/numeric-instances"
    ;; Divisibility / Bezout combinations / gcd / coprimality on ZZ.  Vocabulary
    ;; only; needs ZZ + the surface arithmetic, and is stated at ZZ rather than
    ;; over a general Euclidean ring because `crs' decides the surface identities
    ;; the ideal proofs need and does not reach an abstract (ADD s).
    "structure-library/zz-divisibility"
    ;; The bounded metric d/(1+d) of a metric space + its topological
    ;; equivalence to d (identity bicontinuous); the RR-BOUNDED-MS instance.
    ;; Needs IS-CONTINUOUS (metric-continuity), RR-MS (numeric-instances above)
    ;; and the f(t)=t/(1+t) family (scalar-inequalities).
    "structure-library/bounded-metric"
    ;; PSEUDOMETRIC-SPACE + the gauge topology of a countable pseudometric family
    ;; (PSEUDO-GAUGE-TOP / IS-GAUGE-COUNTABLE), and the metrizability cluster
    ;; T2/T3/T4 as warranted supports.  Needs top-space (IS-METRIZABLE-TOP-SPACE,
    ;; METRIC-TOP, IS-HAUSDORFF) and bounded-metric (IS-BOUNDED-METRIC-SPACE).
    "structure-library/pseudometric"
    ;; Completion of a metric space = Cauchy sequences / null-distance, as a
    ;; concrete setoid quotient.  Needs setoid (QUOTIENT/CLASS), metric-
    ;; completeness (IS-CAUCHY-SEQ/CONVERGES-TO/IS-COMPLETE) and RR-MS
    ;; (numeric-instances, just above, for the real limit of d(f_n,g_n)).
    "structure-library/metric-completion"
    "structure-library/extended-reals"
    ;; RR+* = [0,+inf]: nonnegative extended reals, order-complete via ESUP.
    ;; Needs extended-reals (RR*, POS-INF) + set primitives (SUBSET).
    "structure-library/extended-reals-pos"
    "structure-library/ordinals"
    ;; MPOW (monoid power x^n) + ZZ-ACT (its extension to a ZZ action on an
    ;; abelian group).  Loaded after ordinals, which defines the
    ;; def-by-nn-recursion combinator both files use; the
    ;; ABELIAN-GROUP-AS-MONOID view they ride is declared earlier in views.
    "structure-library/monoid-power"
    "structure-library/zz-action"
    ;; RING-POWER x^n in a commutative ring = MPOW on its multiplicative
    ;; comm-monoid (COMMUTATIVE-RING-MULTIPLICATIVE-CM, views.scm).  Needs
    ;; monoid-power + that view + commutative-ring.
    "structure-library/ring-power"
    "structure-library/bijection"
    "structure-library/cardinality"
    "structure-library/injection"
    ;; RAN (range) + the mindless nested-application typing lemmas
    ;; (compose-type-2..5); needs IMAGE (injection) and DOM (theory).
    "structure-library/compose-typing"
    "structure-library/inf-subsets"
    ;; Dependent recursion / dependent choice on NN.  Foundational
    ;; sequence-building principle behind pigeonhole, subsequence-capture,
    ;; and the diagonalization argument.
    "theorem-library/dc-on-nn"
    "theorem-library/pigeonhole"
    ;; The metric-free core of block-family: nested infinite blocks captured
    ;; by a SEQUENCE OF FINITE COVERS (cover-block-step recursed via dc-on-nn).
    ;; No metric vocabulary; block-family/tb-block-step are its instances.
    "theorem-library/block-family-combinatorial"
    "theorem-library/subsequence-capture"
    ;; Totally bounded => every sequence has a Cauchy subsequence.  Assembles
    ;; pigeonhole + diagonalization + ball-2r-triangle; supplies the SUBSEQ /
    ;; STRICTLY-MONO-NN / IS-SUBSEQUENCE vocabulary.  Needs TOTALLY-BOUNDED/BALL
    ;; (metric-topology), IS-CAUCHY-SEQ (metric-completeness), INF-SUBSETS.
    "theorem-library/cauchy-subsequence"
    ;; The three generic supports the diagonalization PROOF rests on
    ;; (consecutive-mono, nested-chain, infinite-unbounded).  Data-level
    ;; (support/warrant!), so loaded here; the proof itself runs later,
    ;; after the interactive engine.  Needs STRICTLY-MONO-NN (above).
    "theorem-library/diagonalization-lemmas"
    "structure-library/sequences"
    "structure-library/finsum"
    ;; FINPROD / PROD-RING: finite product = FINSUM at a multiplicative
    ;; commutative monoid.  Needs finsum + the COMMUTATIVE-RING-MULTIPLICATIVE-
    ;; CM view (views.scm, already loaded).
    "structure-library/finprod"
    ;; PSS result over finite abelian-group sums (proof archived;
    ;; statement lifted as accepted-without-proof support).
    ;; finsum-congruence was here too but was dropped 2026-05-27: it
    ;; is an easy consequence of fun-domain-extensionality (apply it
    ;; to deduce f = g from pointwise agreement, then substitute).
    "theorem-library/sum-ag-permutation-invariance"
    "theorem-library/sum-set-left-scalar"
    "theorem-library/sum-set-right-scalar"
    "theorem-library/finsum-fubini"
    "structure-library/matrix"
    ;; Elementary matrices: matrix units + the column-shift lemma (ch.3 Def 3.2-3.7,
    ;; Lemma 3.3), foundation of the elementary-operation theory over a comm. ring.
    "structure-library/elementary-matrix"
    ;; The matrix equivalence relation ~ (Def 3.33 / Remark 3.35): C ~ D iff
    ;; D = U.C.V for invertible U,V.  Basis of the Smith normal-form theory.
    "structure-library/mat-equiv"
    ;; Determinant by recursive cofactor expansion (the pedestrian definition):
    ;; MINOR + DET's two definitional recursion axioms + the first theorem menu
    ;; (computational checks det-1x1/2x2, det-identity, alternating, product).
    "structure-library/determinant"
    ;; The monoid algebra A[M] (Bourbaki III.2): finitely-supported functions
    ;; M -> A, pointwise sum, convolution product, as a RING tuple.  POLY(A) =
    ;; A[NN-ADD-MONOID] is one-variable polynomials.  Ring laws seeded; the
    ;; convolution-associativity proof is deferred, poly-is-ring is derived.
    "structure-library/polynomial"
    ;; Phase C: a matrix of scalars acting on a matrix (column sequence) of
    ;; module elements -- MATACT, the book's A . u_col (eq. 82).
    "structure-library/mod-seq"
    ;; User-added structures (auto-managed by Build Structure button)
    "structure-library/user-additions"
    ;; Reclassify hand-written defining iffs (property/class/membership defs)
    ;; as definitional -- they were theory-add-axiom!'d without the stamp.
    ;; Loads after every file that defines one of them.
    "structure-library/definitional-reclass"
    ;; PSS-promoted foundational facts (formerly proven in proven-theorems.scm;
    ;; proofs archived to archive/proven-theorems-archive.scm).  Loaded in the
    ;; original prove-and-install! order so each entry's macete dependencies
    ;; (axioms / earlier PSS entries) are in place when registered.
    "theorem-library/succ-nn-ord"
    "theorem-library/ord-segment-nn-succ"
    "theorem-library/ord-segment-zero-no-members"
    "theorem-library/ord-segment-nn-subset"
    "theorem-library/ord-segment-trans"
    "theorem-library/ord-segment-self"
    "theorem-library/enum-fam-in-fun"
    "theorem-library/fin-enum-is-bijection"
    "theorem-library/finsum-well-defined"
    "theorem-library/union-empty-left"
    "theorem-library/finsum-empty"
    "theorem-library/card-singleton"
    "theorem-library/finsum-singleton"
    "theorem-library/finsum-type"
    ;; Finite sums over a commutative monoid (closure / permutation-invariance
    ;; / enumeration-independence): the IS-COMM-MONOID generalizations of the
    ;; abelian-group finsum lemmas, reusing the same FINSUM functoid.  Needed
    ;; for the unordered RR+* sum (RR+*-ADD-MONOID has no inverses).
    "theorem-library/finsum-comm-monoid"
    ;; Product-of-sums expansion (warranted PSS tower): set-difference axioms,
    ;; powerset finiteness + insert-split, the finite-product recurrence
    ;; (finsum-insert) and PROD-RING's laws, capped by prod-of-sums-expansion.
    ;; Needs finprod, injection (IMAGE), cardinality, comm-monoid view.
    "theorem-library/prod-of-sums"
    ;; FINSUM's ADDITIVE layer (finsum-add / -ring-distrib-left / -ring-scalar-zz
    ;; / -reindex), ord-segment-insert, ring-power-succ, and the CHOOSE / NN-MINUS
    ;; operators.  The additive twin of prod-of-sums' multiplicative layer; what
    ;; the binomial theorem needs.  Needs finsum + ring-power + zz-action + views.
    "theorem-library/finsum-additive"
    ;; Finite-sum inequalities over RR (Cauchy-Schwarz, sum-of-squares nonneg,
    ;; the sum triangle inequality, termwise monotonicity); warranted supports.
    ;; Needs FINSUM + the additive layer above + RR-NORMED-FIELD (numeric-instances).
    "theorem-library/analysis-inequalities"
    ;; The Binomial Theorem for commutative rings (asserted+warranted capstone,
    ;; like prod-of-sums-expansion).  Needs the additive layer above.
    "theorem-library/binomial"
    ;; ESUM: the unordered RR+* sum = sup of finite partial sums over RR+*-
    ;; ADD-MONOID.  Every RR+*-valued f is summable; value is +inf unless the
    ;; partial sums are bounded by a real.  Needs finsum-comm-monoid + RR+*.
    "theorem-library/extended-sum"
    ;; Unconditional summability of a normed-AG-valued function (SUMS-TO,
    ;; IS-SUMMABLE, sums-to-unique).  Needs FINSUM + the NORMED-AG view.
    "theorem-library/summability"
    ;; Real power series  Sum coef(n) x^n  (PS-PARTIAL-SUM via SUM-AG over
    ;; RR's additive group; PS-CONVERGES-(TO-)AT via CONVERGES on RR-MS).
    ;; Needs sequences (SUM-AG), views (NORMED-FIELD-ADDITIVE-AG), numeric-
    ;; instances (RR-NORMED-FIELD/RR-MS), number-systems (power), metric-completeness.
    "theorem-library/power-series"
    ;; Order facts about real partial sums + monotone-convergence on RR (the
    ;; keystone comparison-test cited as missing).  Needs power-series.
    "theorem-library/series-order-lemmas"
    ;; Telescoping bridge: consecutive distances bounded by a summable series
    ;; => Cauchy (and, if complete, convergent).  Needs power-series
    ;; (SERIES-CONVERGES) + metric-completeness (IS-CAUCHY-SEQ/IS-COMPLETE).
    "theorem-library/summable-cauchy"
    ;; The countable product of metric spaces (product topology): the weighted
    ;; product metric DIST_w = SUM w(n) d_n/(1+d_n), coordinatewise convergence,
    ;; infinitely many equivalent metrics.  Needs bounded-metric (BDD-METRIC),
    ;; power-series (SERIES-CONVERGES-TO), BIG-UNION/IOTA (kernel).
    "structure-library/product-metric"
    ;; Countable Tychonoff for compact metric spaces (a countable product of
    ;; compact metric spaces is compact), via sequential compactness + the
    ;; coordinate diagonalization keystone.  Needs product-metric (PRODUCT-METRIC
    ;; + product-convergence-coordinatewise), compactness (IS-COMPACT),
    ;; cauchy-subsequence (STRICTLY-MONO-NN/SUBSEQ), metric-completeness
    ;; (CONVERGES-TO).
    "theorem-library/seq-compact-product"
    ;; Retroactive warrants for founding PSS members admitted before warrants
    ;; were standard; loads after every result it warrants is installed.
    "theorem-library/founder-warrants"
    ;; Context and proof commands
    "contexts"
    "proof-commands"
    "interactive"
    ;; Generalized context-discharge + operator-remap engine: ring-term/ring-goal
    ;; lifted to any registered structure kind.  Loads after interactive so the
    ;; differential anchor (run-context-tests) can compare against live ring-goal.
    "input-context"
    ;; Surface-syntax accessors for the PARTS of a formula (part / match /
    ;; formula-kind): reach subterms by surface names, never by s-expr position.
    "parts"
    ;; The proof-driving helpers more than one driver needs (proof-leaves,
    ;; any-pred, the dc- kit, ...), formerly scattered through proof scripts that
    ;; leaked them into the global environment.  Loading it also ARMS the
    ;; containment below: every theorem-library/ and calculus/ file after this
    ;; point gets its own top-level environment.  Must follow interactive /
    ;; input-context (whose tactics it calls) and precede every proof file.
    "driver-kit"
    ;; Warrant / proof-debt ledger: records each qed proof's bill of asserted
    ;; facts it rests on (loads right after interactive so qed can call it).
    "proof-debt"
    ;; minimize! -- "choose v with MEASURE(v) least".  A composite tactic over
    ;; the cmd-* layer (no kernel rule); its one mathematical appeal is
    ;; nn-least-element, resolved by NAME at call time, so it may load here,
    ;; long before theorem-library/nn-least-element.
    "minimize"
    ;; The well-ordering of ORD, PROVEN from the transfinite-induction axiom and
    ;; nothing else (modulo 0).  It was asserted in ordinals.scm with a `proof'
    ;; warrant that named no file.  Needs interactive + driver-kit + proof-debt,
    ;; all directly above, and must precede nn-least-element and every use of
    ;; minimize!, which appeal to it.
    "theorem-library/ord-well-ordered-proof"
    ;; eq-sym / eq-trans / neq-sym, PROVEN.  eq-sym was an asserted DUPLICATE of
    ;; the primitive `equality-symmetry' and was cited by 52 bills; eq-trans is
    ;; the curried form of the primitive `equality-transitivity', which `fact'
    ;; needs because it will not split an AND antecedent.  Was in order-lemmas.
    "theorem-library/equality-basics"
    ;; INTERVAL's read-offs, PROVEN by separation from its def-functoid:
    ;; interval-in-set (60 bills), interval-elt-in-nn, interval-lo, interval-hi,
    ;; plus the citable unfolding equation.  Were in order-lemmas / matrix.
    "theorem-library/interval-basics"
    ;; binary-minus-laws -- what follows from number-systems.scm's binary-minus-def
    ;; (2026-08-01).  Proves rr-sub-in-rr, which was a `well-known' support in
    ;; order-lemmas until the defining equation for (- a b) existed.  Needs
    ;; interactive + proof-debt (above); must precede theorem-library/
    ;; differentiation, its one consumer.
    "theorem-library/binary-minus-laws"
    ;; fun-apply-type-proof -- f:A->B, x in A |- f(x) in B, PROVEN modulo 0 from
    ;; the base axiom fun-codomain-iff.  Was a support claiming the `proof'
    ;; warrant tier with no machine proof.  Needs only base axioms + driver-kit,
    ;; so it sits here; must precede theorem-library/cancellation, the earliest
    ;; file that cites it in an actual proof.
    "theorem-library/fun-apply-type-proof"
    ;; nn-order-basics -- nn-le-refl, nn-le-add-right (m <= m+n by induction on
    ;; n) and nn-pair-upper-bound, PROVEN.  The first and third were supports in
    ;; order-lemmas claiming the `proof' warrant tier with no machine proof.
    ;; Needs interactive + driver-kit (use-induction); must precede
    ;; theorem-library/nn-order-proof and coord-block-estimate-proof.
    "theorem-library/nn-order-basics"
    ;; rr-recip-order -- the L1 rung of the loose-ends ladder: a * 0 = 0,
    ;; 0 < 1, the product of positives is positive, and the one everything
    ;; analytic waits on, 0 < a => 0 < recip a.  Needs order-predicates (`<'),
    ;; order-lemmas (the rr-lt-* family), the ineq oracle and driver-kit.
    "theorem-library/rr-recip-order"
    ;; calc -- the directive/chain checker (notes-27): ground a goal (REL L0 Ln)
    ;; by a chain of intermediaries, proving each link (crs / ineq+bridge / cited)
    ;; and composing them (cong / iff / order composers).  A composite over the
    ;; cmd-* layer; the composition lemmas (co-*-trans) live in order-lemmas.
    ;; Needs interactive + driver-kit + ineq-oracle + order-lemmas, all above.
    "calc"
    ;; sketch -- the structured-proof surface (sketch/step/obtain/qed-sketch):
    ;; generalizes `calc' off chains onto the whole argument.  Each intermediate
    ;; claim is cut and discharged by a lane; a claim that will not discharge is
    ;; GRANTED to context and reported by name (the two-outcome calc contract).
    ;; Reuses calc's lane machinery, so it loads right after calc.
    "sketch"
    ;; vlet -- (vlet (names) FORMER): bind names to proof objects.  `match' selects
    ;; subterms of a context formula by a pattern with named holes; `choice' eliminates
    ;; an existential (present, or cut-as-debt) and binds its witness, landing the
    ;; witness's defining property for free.  Reuses driver-kit + sketch (sk--split!).
    "vlet"
    ;; transport! -- a law proved in a STRUCTURE, delivered at an INSTANCE in the
    ;; SURFACE language: specialize-structure, then the instance's own slot
    ;; macetes (ZZ-RING@ADD), then the surface bridges (binplus-apply).  All
    ;; three existed; nothing composed them, so nobody transported anything and
    ;; NN facts got re-proved by hand.  Needs the tactics (it PROVES what it
    ;; installs), so it loads here.
    "transport"
    ;; The four inclusion facts, PROVEN rather than asserted: subset-mem-fwd /
    ;; subset-mem / subset-trans off subset-def, and subclass-of-set-is-set off
    ;; class-extensionality + separation.  They sat asserted in set-basics (70)
    ;; and compactness (165) purely because `sp'/`qed' do not exist that early;
    ;; here is the first point at which they can be proved, and it precedes all
    ;; twelve call sites (earliest: theorem-library/diagonalization).
    "theorem-library/subset-lemmas"
    ;; Snapshot every procedure binding, then let prover-load check after each
    ;; later file that none was rebound to a non-procedure -- the case-fold trap
    ;; ((define BC ...) clobbering the `bc' tactic) that no other gate catches.
    "clobber-guard"
    ;; The trivial subtype-subsumption laws ("every X is a Y"), PROVEN via
    ;; mac-h instead of asserted -- formerly phantom debt leaves.  Needs the
    ;; interactive tactics + qed/proof-debt, so loads here.
    "structure-library/subtype-laws"
    ;; IS-RING(ZZ-RING), PROVED -- formerly the asserted axiom `zz-is-ring', which
    ;; every theorem reaching the integers through their ring structure was billed
    ;; for.  Unfold the IFF, push the accessors to the surface (surface-goal!),
    ;; and the conjuncts are the arithmetic axioms.  Must load BEFORE cancellation
    ;; (which transports through it).  Needs transport + crs + numeric-instances.
    "theorem-library/zz-ring-is-ring"
    ;; Cancellation, proved ONCE in GROUP and then carried: -> ABELIAN-GROUP ->
    ;; [RING-ADDITIVE-AG view] -> RING -> [transport!] -> ZZ/QQ in the SURFACE
    ;; language -> NN by restriction.  The worked example of the transport chain,
    ;; and the retraction of an induction proof that never needed induction.
    ;; Needs subtype-laws (abelian-group-opr-comm), views, numeric-instances,
    ;; transport.
    "theorem-library/cancellation"
    ;; The NN arithmetic support layer: cancellation, no-zero-divisors, and the
    ;; order fact k<2k, all DERIVED (not asserted) from ZZ being an ordered
    ;; integral domain via NN<=ZZ -- the integral-domain law is TRANSPORTED to
    ;; the surface (zz-mul-cancel-zero), then restricted.  Retires the reference
    ;; assertions number-theory proofs kept re-making.  Needs transport,
    ;; zz-is-integral-domain, nn-subset-zz, order-lemmas.
    "theorem-library/nn-integral"
    ;; Parity on NN, PROVED from the two Peano recursion equations (nn-arith):
    ;; the DICHOTOMY (every natural is 2k or succ(2k)) and the EXCLUSIVITY
    ;; (2x is never succ(2y)) -- the two halves of "even iff not odd", and the
    ;; engine for parity on ZZ.  Needs nn-arith, order-lemmas, driver-kit.
    "theorem-library/nn-parity-proof"
    ;; PRED, the predecessor on NN, DEFINED by definite description (IOTA) and
    ;; undefined at 0.  The finite-surgery kit's collapse map needs it and the
    ;; tree had no predecessor: NN-MINUS(n,1) is the total monus through ZZ,
    ;; whose laws are asserted (hand-wave / well-known), while the description's
    ;; two obligations are theorems -- nn-nonzero-is-succ and nn-succ-inj, both
    ;; directly above.  Needs nn-parity-proof and equality-basics.
    "theorem-library/nn-pred"
    ;; The segment/arithmetic bridges: j in S(n) iff j < n, and j in S(succ n)
    ;; iff j <= n.  Both IFFs, hence live macetes, and they are what lets a
    ;; finite-segment argument be argued in inequalities instead of chaining
    ;; three ordinal axioms by hand at every step.  Needs ordinals (primitive)
    ;; and order-lemmas (the NN discreteness supports).
    "theorem-library/ord-segment-arith"
    ;; finite-surgery -- the surgery kit's first member, COLLAPSE-AT(k): the
    ;; map that deletes k from NN, identity below it and predecessor above.
    ;; DEFINITIONAL (a def-functoid), so the construction costs no debt; what
    ;; the bills carry is the NN order supports its arithmetic cites.  Plus the
    ;; two discreteness read-offs nn-not-lt-le / nn-lt-succ-le.  Needs nn-pred
    ;; (PRED), ord-segment-arith (the bridges) and nn-order-basics (nn-in-rr).
    "theorem-library/finite-surgery"
    ;; pigeonhole-segments -- Track A of the CARD plan: the finite pigeonhole
    ;; the definition of CARD needs.  Base case proven; the induction step is
    ;; the consumer of COLLAPSE-AT above.  Needs bijection/injection
    ;; (structure-library), the surgery kit and driver-kit.
    "theorem-library/pigeonhole-segments"
    ;; mod-3 arithmetic on NN, the mirror of nn-parity-proof: the trichotomy
    ;; (n = 3k / succ 3k / succ^2 3k), residue-exclusivity (3x /= succ 3y), and the
    ;; linchpin nn-3-div-square (3|p*p => 3|p) -- plus nn-3-cancel / nn-lt-triple.
    ;; Feeds sqrt3-proof.  Needs nn-parity-proof + nn-integral (nn-mul-cancel).
    "theorem-library/nn-mod3-proof"
    ;; <= versus + on NN: a <= 0 => a = 0, a <= a+b, and additive monotonicity.
    ;; order-lemmas.scm relates <= to succ and never to +; the pairing is what
    ;; exposed the gap.  Own file, not the pairing file, so the next user can
    ;; find them.  Needs nn-parity-proof (nn-zero-or-succ).
    "theorem-library/nn-order-proof"
    ;; The Cantor pairing NN x NN -> NN (TRINUM by recursion, NNPAIR(i,j) =
    ;; TRINUM(i+j)+j) and its surjectivity, plus nn-succ-add (succ(a)+b) which
    ;; the base lacked.  The re-indexing mechanism that compact-metric-is-
    ;; separable, the Ascoli diagonal and countable unions are all blocked on.
    ;; Needs nn-parity-proof (nn-zero-or-succ) and ordinals (def-by-nn-recursion).
    "theorem-library/nn-pairing"
    ;; compact-metric-is-separable, PROVEN (was a `reference' support in
    ;; structure-library/separable.scm, retired there).  The gate on the Ascoli
    ;; arc.  Needs nn-pairing (nn-flatten, immediately above) plus dc-on-nn
    ;; (dc-on-nn-pred), separable (IS-SEPARABLE, tb-scale-dense-seq),
    ;; compactness, order-predicates (nn-recip-succ-*), order-lemmas
    ;; (rr-lt-trans) and fun-apply-type-proof -- all earlier.
    "theorem-library/compact-separable-proof"
    ;; The three BIJECTION projection lemmas (in-fun / injective / surjective),
    ;; PROVEN modulo 0 from bijection-membership-iff -- formerly asserted in
    ;; bijection.scm "for direct use" (phantom debt).
    "structure-library/bijection-derived"
    ;; CARD*, cardinality DEFINED (an IOTA over "least ordinal whose segment A
    ;; bijects onto") rather than axiomatised, with card*-segment PROVEN from
    ;; pigeonhole.  A COMPANION name on purpose: CARD cannot be both axiomatised
    ;; and defined, so the defined constant is built here and the swap is made
    ;; name by name as each theorem lands.  Needs pigeonhole-segments-gen, the
    ;; segment bridges, bijection-derived (just above) and bijection-identity.
    "theorem-library/card-defined"
    ;; The five metric laws (pos/self-zero/zero-eq/sym/triangle), PROVEN by
    ;; projecting the is-metric property folded into IS-METRIC-SPACE -- they
    ;; were redundant asserted axioms (a definition oversight).
    "structure-library/metric-laws"
    ;; A descending NN-indexed family is a chain -- was L2 of
    ;; diagonalization-lemmas, asserted well-known; proven 2026-08-03 by
    ;; NN-induction on j.  Needs nn-order-proof (nn-le-zero-is-zero) and
    ;; subset-lemmas (subset-trans), both above, and must precede its consumer.
    "theorem-library/nn-nested-subset-chain-proof"
    ;; Diagonalization: nested infinite subsets of NN -> a single strictly-
    ;; monotone sequence with tail in every member.  PROVEN to QED via
    ;; dc-on-nn-pred + diagonalization-lemmas' two remaining generic supports.  Runs
    ;; here (needs the interactive engine + proof-debt) and BEFORE
    ;; cauchy-subseq-proof, which cites it.
    "theorem-library/diagonalization"
    ;; The combinatorial nested block family: cover-block-step recursed down a
    ;; sequence of finite covers via dc-on-nn-pred.  PROVEN to QED (was asserted
    ;; 'reference).  Needs the interactive engine + cover-block-step / IS-FINITE-
    ;; COVER (block-family-combinatorial.scm) + dc-on-nn-pred + inf-subsets;
    ;; BEFORE cauchy-subseq-proof, which cites it.
    "theorem-library/block-family-combinatorial-proof"
    "theorem-library/cauchy-subseq-proof"
    ;; countable Tychonoff headline, PROVEN to QED modulo the diagonalization
    ;; keystone.  Needs seq-compact-product's supports + interactive/proof-debt.
    "theorem-library/tychonoff-proof"
    ;; ((DIST RR-MS) u v) == abs(u - v): the RR-MS distance on the surface.
    ;; Proved, modulo 0.  Needs RR-MS (numeric-instances) and the slot equation
    ;; RR-MS@DIST that declare-instance! mints with it.  Loads BEFORE the ascoli
    ;; files because generalising IS-EQUICONTINUOUS to (s t fam) put the accessor
    ;; detour -- d_t(...) where the RR-valued form had abs(...) -- on the path of
    ;; every proof in that arc.
    "theorem-library/rr-ms-dist"
    ;; rr-complete-proof -- IS-COMPLETE(RR-MS): RR is a complete metric space,
    ;; PROVEN from order completeness via SUP of the eventual lower bounds.
    ;; Retires the axiom that stood asserted in numeric-instances.
    ;;
    ;; PLACEMENT, the hard-won part.  It needs, all together: interactive/
    ;; proof-debt (sp/qed), driver-kit, `obtain' (sketch.scm, 449), and the
    ;; theorem `rr-ms-dist' (immediately above) -- the last is why it sits this
    ;; far down rather than beside the other elementary proofs.  It does NOT
    ;; need to precede ascoli-bridge's (rests-on ... '(rr-complete)): rests-on
    ;; only registers metadata, and the "dependencies name installed theorems"
    ;; audit runs at the END of the load.
    "theorem-library/rr-complete-proof"
    "theorem-library/ascoli-arzela-statement"
    "theorem-library/ascoli-bridge"
    ;; Functional-analysis statement seeds (stated 2026-07-22; proofs deferred).
    "theorem-library/order-zorn"
    ;; INJECTION(X,Y) => INJECTIVE*(f): the bridge between the set-function and
    ;; class-function spellings of injectivity.  Needs injection.scm (both) and
    ;; fun-domain-apply-def (theory).
    "theorem-library/injective-star"
    ;; No SET receives an injective class function from ORD -- the Burali-Forti
    ;; endgame, factored out.  Needs image-set/image-membership-iff (injection),
    ;; subclass-of-set-is-set (set-basics), burali-forti (ordinals), choice.
    "theorem-library/ord-no-injection"
    "theorem-library/zorn-proof"
    ;; ZORN'S LEMMA, proved: the strictly increasing transfinite tower ZUP and the
    ;; Burali-Forti contradiction.  Must come after ord-no-injection (its endgame)
    ;; and before seminorm-hahn-banach, whose `rests-on' names zorn-lemma.
    "theorem-library/zorn-route-two"
    "theorem-library/seminorm-hahn-banach"
    "theorem-library/baire-category"
    "theorem-library/frechet-open-mapping"
    ;; subseq-of-convergent: a subsequence of a convergent sequence converges to
    ;; the same limit.  A keystone brick.  Needs cauchy-subsequence + metric-
    ;; completeness supports + interactive.
    "theorem-library/subseq-convergence-proof"
    ;; coord-block-estimate: convergence ALONG a block transfers to a reindexing
    ;; whose tail lands in the block, PROVEN to QED.  The estimate brick of the
    ;; coordinatewise-diagonal-subseq keystone.  Needs seq-compact-product's
    ;; CONVERGES-ALONG def + order-lemmas + interactive.
    "theorem-library/coord-block-estimate-proof"
    ;; totally-bounded => every sequence has a Cauchy subsequence, PROVEN to QED
    ;; via the combinatorial block family.  Needs cauchy-subsequence (the cited
    ;; supports) + interactive/proof-debt (sp/di/mac/fact/qed).

    ;; 0.x = 0_V : first proven MODULE theorem; worked test of `fact' + the
    ;; MODULE-VECTOR-AG view.  Needs interactive tactics + the module bricks.
    "theorem-library/module-zero-act"
    ;; Well-ordering of NN, PROVEN from ord-well-ordered (ordinals.scm) via
    ;; the <=_ORD/<= bridge; exercises the new ai iff-elim.  Needs interactive
    ;; tactics + qed and the ordinal axioms.
    "theorem-library/nn-least-element"
    ;; sqrt(2) is irrational, on NN: forall p,q in NN. q/=0 => p*p /= 2*(q*q).
    ;; Infinite descent by minimize! (so loads after nn-least-element); every witness
    ;; named by `obtain', typing and algebra by have!/from-context!.  Asserts nothing
    ;; of its own (nn-mul-nonzero / nn-2-cancel are proven above).  Needs nn-even-square
    ;; (nn-parity-proof), nn-lt-double (nn-integral), sketch (obtain/sk--split!).
    "theorem-library/sqrt2-proof"
    ;; sqrt(3) irrational, on NN: forall p,q in NN. q/=0 => p*p /= 3*(q*q).  Port of
    ;; sqrt2-proof, 2 -> 3, nn-even-square -> nn-3-div-square (nn-mod3-proof).  Asserts
    ;; nothing of its own.  Needs nn-mod3-proof + nn-least-element (minimize!).
    "theorem-library/sqrt3-proof"
    ;; euclidean-ideal-has-generator, PROVEN by `minimize!' (formerly an asserted
    ;; support in structure-library/ideal.scm).  THE mathematical core of
    ;; "every Euclidean ring is a PID".  Needs nn-least-element (for minimize!),
    ;; ideal.scm, euclidean-ring.scm, mat-equiv.scm (nn-succ-le-antisym).
    "theorem-library/euclidean-ideal-generator-proof"
    ;; Bezout on ZZ: { x*a + y*b } is an ideal of ZZ-RING (surface-goal! puts the
    ;; ideal conditions in ZZ arithmetic, `crs' decides them), so the Euclidean
    ;; generator above is a common divisor that IS a combination.  Needs
    ;; euclidean-ideal-generator-proof, zz-divisibility, transport.
    "theorem-library/zz-bezout-proof"
    ;; Pointwise continuity algebra on RR (const/identity continuous; sum/product
    ;; of continuous-at-a is continuous-at-a) -- the supporting machinery the
    ;; differentiation rules are proved on top of.  Needs IS-CONTINUOUS-AT
    ;; (metric-continuity) + RR-MS (numeric-instances).
    "theorem-library/continuity-algebra"
    ;; Chapter 2 (Differentiation) of calculus.pdf: the Caratheodory/o(h)
    ;; derivative IS-DIFF-AT + DERIV, and the first results (uniqueness, Prop 2.4
    ;; diff=>continuous, sum/product rules, const/identity).  Needs IS-CONTINUOUS-
    ;; AT (metric-continuity) + RR-MS / RR arithmetic (numeric-instances).
    "theorem-library/differentiation"
    ;; Calculus Def 2.2: the n-th derivative NTH-DERIV(f,n) as a function, by
    ;; NN-recursion on DERIV (nth-deriv-zero / -succ).  Needs DERIV
    ;; (differentiation) + def-by-nn-recursion (ordinals).
    "theorem-library/higher-derivatives"
    ;; Calculus Section 2.2: the o/O calculus, limit-free (LITTLE-O-AT) -- the
    ;; eq-12 bridge to IS-DIFF-AT + o-algebra (sum, scalar).  Needs IS-DIFF-AT
    ;; + IS-CONTINUOUS-AT.
    "theorem-library/little-o"
    ;; Linear algebra: the two matrix-product entry-expansion lemmas
    ;; (triple-entry-left/right), PROVEN from the (B) finite-sum bricks; cited by
    ;; matmul-assoc-proof, so loads before it.
    "theorem-library/triple-entry-proof"
    ;; Linear algebra: matrix multiplication is associative, via finsum-fubini
    ;; (matrix-entry-extensionality + triple-entry expansion + order-of-summation
    ;; interchange).  Cited by mat-ring-proof, so loads before it.
    "theorem-library/matmul-assoc-proof"
    ;; Linear algebra: MAT(n,n,A) is a ring.  Assembly proof unfolding the
    ;; generated IS-RING iff and discharging each of its 14 conjuncts against
    ;; matrix.scm's read-offs + matrix-ring axioms.  Needs matrix.scm (loaded
    ;; above) + the tactic surface (interactive, loaded above).
    "theorem-library/mat-ring-proof"
    ;; Linear algebra: Lemma 3.3 (algebraic-numbers.pdf ch.3), the column-shift
    ;; formula (P.E[k,l])_{ic} = P_{ik} if c=l else 0 -- matmul-entry expansion +
    ;; finsum-single-support collapse + EM case-split.  Engine behind Prop 3.5.
    ;; Needs elementary-matrix.scm (matunit PSS) + matrix.scm read-offs.
    "theorem-library/matunit-shift-proof"
    ;; Linear algebra: Prop 3.5 (algebraic-numbers.pdf ch.3), the ACTION of the
    ;; elementary column matrices (currently elem-h-action; g/f to follow).  Same
    ;; finsum-collapse shape as matunit-shift-proof.  Needs elementary-matrix.scm.
    "theorem-library/elem-actions-proof"
    ;; Linear algebra: Cor 3.6 (algebraic-numbers.pdf ch.3), the elementary column
    ;; matrices are invertible with elementary inverses (F^-1=F[l,k], G[r]^-1=G[-r],
    ;; H[r]^-1=H[r^-1]).  matrix-entry-extensionality + the Prop 3.5 actions.
    "theorem-library/elem-inverses-proof"
    ;; Linear algebra Phase B: Prop 3.29 (row form), the ROW operations = the action
    ;; of the elementary matrices by LEFT-multiplication (F swaps rows, G adds a row
    ;; multiple, H scales a row).  Left-mult mirror of elem-actions-proof; prerequisite
    ;; for Smith/normal-form reduction (Prop 3.36).  Needs elementary-matrix.scm row
    ;; read-offs (elem-{f,g,h}-r*).
    "theorem-library/elem-row-actions-proof"
    ;; Linear algebra Phase B: division-with-remainder over a euclidean ring in
    ;; usable form (euclidean-division), the ring-theoretic core of the Smith/
    ;; normal-form reduction (Prop 3.36) -- what shrinks a pivot below the running
    ;; minimum.  From gauge-is-degree (euclidean-ring.scm) + HAS-DIV-REMAINDER unfold.
    "theorem-library/euclidean-division-proof"
    ;; Linear algebra Phase B: the column-reduction STEP of the Smith reduction --
    ;; one elem-g column op puts the euclidean remainder r in the (1,j) slot,
    ;; shrinking it below the pivot degree (euclidean-division + elem-g-action +
    ;; comm-ring arithmetic).  Needs elem-actions-proof + euclidean-division-proof.
    "theorem-library/pivot-col-reduce-proof"
    ;; Linear algebra Phase B: the ROW-reduction step (mirror of pivot-col-reduce
    ;; via elem-g-row-action) -- one row op puts the euclidean remainder in the
    ;; (i,1) slot, clearing the first column.  Needs elem-row-actions-proof +
    ;; euclidean-division-proof.
    "theorem-library/pivot-row-reduce-proof"
    ;; Linear algebra Phase B infrastructure: the basic laws of the matrix
    ;; equivalence relation ~ (mat-equiv.scm) -- reflexivity, mult by an invertible
    ;; preserves ~, and the elementary swap ELEM-F is invertible (Cor 3.6).  The
    ;; foundation for the Smith normal-form induction.  Needs mat-equiv.scm +
    ;; elem-inverses-proof + matrix.scm identities.
    "theorem-library/mat-equiv-proof"
    ;; min-degree-entry, PROVEN by `minimize!' (formerly an asserted support in
    ;; mat-equiv.scm).  Must precede smith-proof, which cites it in
    ;; place-min-pivot.  Needs nn-least-element (above) for minimize!.
    "theorem-library/min-degree-entry-proof"
    ;; Linear algebra Phase B: the Smith normal-form reduction (Prop 3.36) --
    ;; equiv-mul-both, swap-to-corner, ... built on the ~ equivalence laws.
    "theorem-library/smith-proof"
    ;; mat-equiv-target-is-mat + class-min-pivot, PROVEN by `minimize!' plus
    ;; swap-to-corner-gen (formerly an asserted support in mat-equiv.scm).  After
    ;; smith-proof (swap-to-corner-gen), before clear-pivot-cross (which cites it).
    "theorem-library/class-min-pivot-proof"
    ;; Linear algebra Phase B: the Smith DESCENT step -- pivot-clears-col, one
    ;; column op zeroes an off-pivot row-1 entry (euclidean remainder forced to
    ;; vanish by class-minimality).  Needs pivot-col-reduce + class-min hyp.
    "theorem-library/smith-clear-proof"
    ;; Linear algebra Phase B: clear the whole first row -- NN-induction iterating
    ;; pivot-clears-col over the columns (clear-row-upto), then at k=n
    ;; (clear-first-row).  Needs pivot-clears-col + the NN/interval read-offs.
    "theorem-library/clear-first-row-proof"
    ;; Linear algebra Phase B: clear the whole first column -- the row-op mirror
    ;; of clear-first-row (pivot-clears-row + clear-col-upto at k=m).
    "theorem-library/clear-first-col-proof"
    ;; i in [a,b], b <= c  =>  i in [a,c].  Wanted wherever a summand lambda of
    ;; domain [1,succ n] is applied at an index introduced from [1,n]; the beta
    ;; guard refuses that reduction until the index has been carried across.
    ;; Needs only order-lemmas' interval read-offs.
    "theorem-library/interval-widen"
    ;; Linear algebra Phase B: block-matrix multiplication BORDER(a,X).BORDER(c,Y)
    ;; = BORDER(ac, X.Y) -- the direct-sum law the Smith bordering rests on.
    "theorem-library/border-mult-proof"
    ;; Linear algebra Phase B: the border algebra -- border-identity /
    ;; border-is-diagonal / border-invertible (routine, on border-mult).
    "theorem-library/border-assembly-proof"
    ;; Linear algebra Phase B: bordered-eq-border -- a cross-cleared C equals
    ;; BORDER(C11, SUBMAT C); bridges clear-first-row/col to the BORDER block form.
    "theorem-library/bordered-eq-border-proof"
    ;; Linear algebra Phase B: clear-pivot-cross -- P (euclidean ring, nonzero entry)
    ;; ~ BORDER(b, C') block form; per-level Smith step (pivot + clear cross + border).
    "theorem-library/clear-pivot-cross-proof"
    ;; Linear algebra Phase B CAPSTONE: smith-diagonalization -- every matrix over a
    ;; euclidean ring is ~ to a diagonal matrix (ni on row dim + clear-pivot-cross +
    ;; bordering recursion).
    "theorem-library/smith-diagonalization-proof"
    ;; Phase C, toward Cor 3.46: smith-diagonalization with the strengthened
    ;; invariant -- the nonzero diagonal entries are recorded as an INITIAL
    ;; SEGMENT (SMITH-STAIRCASE A m n D k).  border-staircase + smith-staircase,
    ;; both trust:none.  Needs clear-pivot-cross + bordering + the border algebra.
    "theorem-library/smith-staircase-proof"
    ;; ---- spans-submodule-fg: bricks, the last-coefficient ideal, the descent.
    ;; Moved ahead of submodule-free / submodule-fg-proof so the descent (which
    ;; proves spans-submodule-fg) precedes the corollary that consumes it.
    ;; BRICKS 1-2: the coefficient row acts linearly (matact-row-add/-scale).
    "theorem-library/matact-row-linear-proof"
    ;; BRICK 3: SPAN(md,n,u) is a submodule and u spans it; module-act-neg-one,
    ;; matact-zerorow/-unitrow/-empty-vzero.
    "theorem-library/span-bricks-proof"
    ;; BRICKS 4-6: matact-row-peel / matact-snoc, submodule-intersection, the
    ;; zero-dimension MAT spaces are inhabited.
    "theorem-library/span-bricks2-proof"
    ;; The last-coefficient set is an IDEAL of SCAL md (the descent's engine), and
    ;; "last coefficient 0 => the element is in the truncated span".
    "theorem-library/lastcoeff-ideal-proof"
    ;; THE DESCENT: spans-submodule-fg by induction on n, from the bricks +
    ;; euclidean-ideal-has-generator.  Was asserted in submodule-free.
    "theorem-library/spans-submodule-fg-proof"
    ;; Phase C, Cor 3.46: a submodule of a free module over a euclidean ring is
    ;; free of rank <= n.  submodule-fg is the lemma linear-algebra.tex \iffalse'd
    ;; out (tex:1651) and cannot do without -- Smith CONSUMES a finite generating
    ;; set for the submodule, it cannot produce one.  Needs mod-seq, finite-
    ;; dimensional (IS-SUBMODULE), euclidean-ring, smith-staircase.
    "theorem-library/submodule-free"
    ;; submodule-fg, PROVEN as the bm := VEC md case of spans-submodule-fg.  The
    ;; old submodule-fg support could not be proved by the induction its own
    ;; warrant described: the step's IH would have to apply to a SUBMODULE, and
    ;; GENERATES asserts the whole module.  Needs submodule-free (the corrected
    ;; statement) + module.scm's closure axioms.
    "theorem-library/submodule-fg-proof"
    ;; Phase C, Remark 3.39: the matrix action on module-element sequences is
    ;; associative, (PQ).u = P.(Q.u).  Mirrors matmul-assoc via finsum-fubini.
    ;; (The spans-submodule-fg bricks + the descent moved UP, before submodule-
    ;; free: the descent PROVES spans-submodule-fg, which submodule-fg-proof then
    ;; consumes, so it must run first.)
    "theorem-library/matact-assoc-proof"
    ;; Phase C, Lemma 3.40: I.u = u, and invertible matrices preserve generating
    ;; and relation-free sequences.
    "theorem-library/mod-basis-proof"
    ;; The inverse of an invertible matrix is invertible.  Cor 3.46 transports
    ;; the free generating sequence backwards along Smith's right factor, so the
    ;; inverse must itself be invertible before the transports will accept it.
    "theorem-library/inverse-invertible-proof"
    ;; The SPANS-relativized generates-transport: an invertible matrix carries a
    ;; sequence spanning a SUBMODULE to another such.  Cor 3.46 needs it because
    ;; F is a submodule, not the whole module.
    "theorem-library/spans-transport-proof"
    ;; Phase C, Prop 3.41: an n-generated module bounds every relation-free
    ;; sequence by n -- so rank is well defined.  The payoff of the Smith arc.
    "theorem-library/rank-bound-proof"
    ;; The Binomial Theorem (SUM form): (x+y)^n = SUM_k COMB-KK(R,x,y,n)(k),
    ;; PROVEN by induction via sum-expansion (multiply-and-shift) + Pascal on the
    ;; recursive coefficient COMB-KK.  Needs binomial.scm (COMB-KK + bricks) +
    ;; sequences.scm (SUM).
    "theorem-library/binomial-proof"
    ;; POLY(A) is a ring when A is -- the monoid-algebra construction's first real
    ;; proof (one instantiation of monalg-is-ring at NN-ADD-MONOID).  Needs
    ;; polynomial.scm + monoid.scm (comm-monoid-is-monoid) + numeric-instances.
    "theorem-library/poly-is-ring-proof"
    ;; Calculus Ch 2.5: closed interval CCINT(a,b) + Extreme Value Theorem
    ;; (continuous on [a,b] attains max/min) -- the base of the MVT arc.  Needs
    ;; IS-CONTINUOUS-AT + RR order.
    "theorem-library/extreme-value"
    ;; Calculus Ch 2.4-2.5: interior-extremum => f'=0 (Prop 2.10) + Rolle's
    ;; lemma (2.12), toward the MVT.  Needs EVT + IS-DIFF-AT + strict <.
    "theorem-library/mean-value"
    ;; Prop 2.10 interior-max-deriv-zero: machine-proven (Caratheodory factor +
    ;; product-sign + continuity pinch + antisymmetry), using the (in-rr) typing
    ;; tactic.  Needs mean-value (continuity supports) + order-lemmas + in-rr.
    "theorem-library/interior-extremum-proof"
    ;; Rolle's theorem, machine-proven: EVT argmax/argmin + Fermat
    ;; (interior-max/min-deriv-zero) + constant-case midpoint.  Needs EVT
    ;; (extreme-value), the Fermat proofs above, and order helpers.
    "theorem-library/rolle-proof"
    ;; Mean Value Theorem, machine-proven: apply Rolle (via fact) to the
    ;; auxiliary h(z)=f(z)(b-a)-z(f(b)-f(a)), then derivative-unique.
    ;; Needs rolle-proof + derivative-unique + in-rr.
    "theorem-library/mvt-proof"
    ;; Cor 2.15: f'=0 on (a,b) => f constant on [a,b], machine-proven by
    ;; trichotomy on u,v + MVT on [min,max] + derivative-unique.  Needs
    ;; mvt-proof + ccint/order supports + in-rr.
    "theorem-library/deriv-constant-proof"
    ;; Cor 2.14: f'<=M on (a,b) => f(b)-f(a)<=M(b-a) (and the lower form),
    ;; machine-proven from MVT + derivative-unique + scale-by-nonneg.  Reuses
    ;; deriv-constant-proof's dc-* helpers, so loads after it.
    "theorem-library/mvt-bounds-proof"
    ;; Cauchy / generalized MVT (Thm 2.11), machine-proven by Rolle on the
    ;; two-function auxiliary h(x)=f(x)(g(b)-g(a))-g(x)(f(b)-f(a)).  Reuses
    ;; deriv-constant-proof's dc-* helpers; needs rolle + derivative-unique.
    "theorem-library/generalized-mvt-proof"
    ;; Increasing function theorem: f'>0 on (a,b) => f strictly increasing,
    ;; machine-proven from MVT on [u,v] (f(v)-f(u)=f'(theta)(v-u)>0).  Reuses
    ;; deriv-constant-proof's dc-* helpers.
    "theorem-library/deriv-monotone-proof"
    ;; Taylor's theorem with Lagrange remainder (Cauchy-MVT route): generalized-mvt
    ;; on G(t)=f(x)-TAYLOR-POLY(f,t,n,x), H(t)=(x-t)^(n+1).  Needs generalized-mvt,
    ;; higher-derivatives (NTH-DERIV), power-series (SERIES-PARTIAL-SUM), injection
    ;; (FACTORIAL), ring-power (power), and deriv-constant-proof's dc-* helpers.
    "theorem-library/taylor-proof"
    ;; Hahn-Banach one-dimension extension step (real normed vector space):
    ;; norm-preserving extension of a bounded functional to s + RR.v.  Modulo
    ;; warranted core (hb-gap, hb-extend-construct).  Reuses dc-* helpers.
    "theorem-library/hahn-banach-proof"
    ;; Noetherian maximal-element principle (ACC => maximal), PROVEN from the
    ;; IS-NOETHERIAN chain condition + dependent choice; plus the reachable-
    ;; subspace vocabulary (NPE/GOOD-SUB) and hb-good-has-maximal it discharges.
    "theorem-library/noetherian-maximal-proof"
    ;; FULL finite-dimensional Hahn-Banach: iterate the one-step extension to the
    ;; whole space (good-step + a maximal reachable subspace).  Modulo warranted
    ;; plumbing (noetherian-maximal, dual-norm, span/subset structure).
    "theorem-library/hahn-banach-full-proof"
    ;; norm-as-sup: ||x|| is the sup of |f(x)| over norm-<=1 bounded functionals.
    ;; The "attained" half is the Hahn-Banach payoff (seed on the line RR.x, extend);
    ;; the reduction target for the vector-valued Taylor remainder bound.
    "theorem-library/norm-as-sup-proof"
    ;; Vector-valued Taylor: the remainder-NORM bound, reduced to the scalar
    ;; case via a norm-attaining functional (consumes norm-attained/bounded +
    ;; scalar taylor-lagrange).  Linear-algebra commutation cores warranted.
    "theorem-library/vector-taylor-proof"
    "theorem-library/nvs-taylor-statement"
    ;; The constructions a functor is INVISIBLE to.  A functoid that reads its
    ;; structure argument only through slots the functor carries ON THE NOSE
    ;; (PREIMAGE reads only PTS; METRIC-TOP carries PTS) satisfies
    ;; F(G r, ...) == F(r, ...) for EVERY r.  Each such equation is PROVED here
    ;; (unfold the functoid, project the accessors, qrfl -- modulo 0) and becomes
    ;; a rewrite by name; a pair whose canned proof does not close is REPORTED,
    ;; never asserted.  Must load after every functor + functoid it should see and
    ;; the tactic layer, and BEFORE any proof that cites one of its equations
    ;; (metric-top-functorial-proof does).
    "structure-library/functor-invariance"
    ;; The metric opens form a topology (metric-top-is-top-space) and METRIC-TOP(md)
    ;; is a METRIZABLE-TOP-SPACE: METRIC-TOP's TYPING obligation (top-space.scm).
    "theorem-library/metric-top-proof"
    ;; ... and its FUNCTORIALITY: an isometry induces a continuous map, so
    ;; Met -> Metrizable-Top is a functor.  Both obligations discharged.  Needs
    ;; metric-top-proof (cites metric-top-is-metrizable-top-space).
    "theorem-library/metric-top-functorial-proof"
    ;; T1: metrizable <=> metrizable by a BOUNDED metric.  Needs metric-top-proof
    ;; (metric-top-is-metrizable-top-space) and the bounded-metric packagings
    ;; (metrizable-has-metric-top, bdd-metric-is-bounded-metric-space,
    ;; bdd-metric-preserves-metric-top).
    "theorem-library/metrizable-bounded-proof"
    ;; A ringoid's congruence (a ~ b iff a-b in the ideal) is an equivalence
    ;; relation, so RINGOID-SETOID is a setoid.  Needs structure-library/ringoid.
    "theorem-library/ringoid-setoid-proof"
    ;; LaTeX rendering of formulas (used by Emacs vnb-view-as-pdf).
    "tex-output"
    ;; Render a completed proof as a LaTeX step-trace ((proof-tex name) /
    ;; (view-proof-pdf name)).  Needs tex-output (expr->tex) + the replay
    ;; machinery in interactive.scm.
    "proof-tex"
    ;; Reader mode: a human-level collapse of a proof ((proof-reader name) /
    ;; (write-proof-reader name path) / (view-proof-reader-pdf name)).  Folds
    ;; di/ai runs into the opening and collapses typing/bookkeeping fact-runs;
    ;; shows only content steps with original step-number margins.  Needs proof-tex.
    "proof-reader"
    ;; Centre-extraction lemma (compact => totally bounded, calculus.pdf Prop 3.12):
    ;; chosen-centre-is-centre + finite-ball-subcover-r-net.  Needs compactness
    ;; (support lemmas) + proof-tex (fbsr-eig uses proof-tex--focus-asms to capture
    ;; eigenvars counter-independently).  In the suite so accessor/eigenvar drift is
    ;; caught -- it silently rotted while standalone (X->PTS + fresh-counter drift).
    "calculus/finite-ball-subcover-proof"
    ;; Assumption-pattern scanner for forward-move discovery
    ;; (used by Emacs vnb-suggest-forward-moves).
    "suggest"
    ;; The rr-ineq applier: (rr-ineq-scan) / (rr-ineq!) sweep the curated real-
    ;; inequality cluster (order-lemmas + scalar-inequalities) and the (ineq)
    ;; oracle at the focus, committing the lane that closes.  Needs suggest
    ;; (vnb--scratch-state), interactive (apply-recorded-cmd!), ineq-oracle.
    "structure-library/rr-ineq"
    ;; (prep 'ineq) -- the diagnosis table: run a tactic's OWN preconditions and
    ;; report which one fails and what repairs it, instead of the single #f every
    ;; unmet precondition collapses to.  Read-only; every probe is a scratch
    ;; clone.  Needs suggest (vnb--scratch-state), ineq-oracle, interactive.
    "prep"
    ;; Library hygiene diagnostics: (audit-unbounded) scans for the partial-
    ;; equality hazard (unbounded universals feeding partial terms under =).
    "audit"
    ;; English verbalization of a wff (companion to expr->str symbolic /
    ;; describe-structure).  Loads last: uses expr->str + the theorem table.
    "wff-english"
    ;; PSS partition: files every support under a category bucket (after all
    ;; supports + their -rev companions are installed).  Soft-nudge in load.scm.
    "theorem-library/pss-categories"
    ;; Self-describing registry of the interactive tactics: (tactics) prints
    ;; the menu, (write-tactics-md) emits reference/TACTICS.md for the browser
    ;; reference.  Pure display/string; no dependencies beyond *reference-dir*.
    "tactics-help"
    ;; Curated browser topic pages (Elementary calculus, Metric spaces): pure
    ;; reading-order organization of already-installed results.  Loads LAST so
    ;; every result it lists is installed; emits reference/<TOPIC>.md, which the
    ;; end-of-load build-reference-html.py turns into hub cards.
    "theorem-library/reference-topics"
    ;; The alphabetical glossary: (glossary), (glossary 'NAME), GLOSSARY.md.
    ;; Reads the constant registry, the operator table, the functoid registry,
    ;; the structure/instance/view tables, the theorem table and the tactic
    ;; registry, so it must load after all of them.
    "glossary"
    ;; LAST: every view is a functor, and this proves it.  It needs every view
    ;; declared (views.scm, normed-vector-space.scm) and the tactic layer, so it
    ;; goes at the end.  It asserts nothing -- each functoriality theorem is
    ;; proved, modulo 0.
    "structure-library/functoriality"))

;;; Files whose top-level axioms are part of the trusted VNB base (not
;;; definitional sugar, not asserted math).  Their loads run with
;;; *current-provenance* = 'primitive so install-theorem! stamps them.
;;; The make-vnb-base-theory core is marked primitive at its build site
;;; (theory.scm); this list covers the remaining foundational axiom files.
;;;
;;; `number-systems' JOINED THE LIST 2026-08-01, by the user's decision, as the
;;; last step of the arithmetic-base cleanup that gave NN/ZZ/QQ/RR/CC their
;;; generation axioms.  Until then its ~107 axioms -- Peano closure, the field
;;; and order axioms, abs -- were installed by bare `theory-add-axiom!', which
;;; defaults to `asserted' (macetes.scm:1441), and carried no `warrant!'.  A
;;; fact that is asserted with nothing claimed to justify it is exactly what
;;; `trust: none' means, so every arithmetic proof in the library billed the
;;; axioms of arithmetic as unjustified assumptions:
;;;
;;;   ;; qed diagonalization: proven modulo {nn-zero-in, nn-succ-closed, ...}
;;;                                                            [trust: none]
;;;
;;; Measured on the load immediately before the change: of 238 bills, 96 read
;;; `trust: none', and 81 of those 96 cited a number-systems axiom -- ALL 81.
;;; Five bills were nothing BUT number-systems axioms and now read `modulo 0'.
;;;
;;; This is the same move as the 28 ordinal axioms (2026-07-27) and `image-set'
;;; (07-28), and it is a foundational decision, not a bookkeeping one: it says
;;; these axioms are not debt at all, because they are what the number systems
;;; ARE.  Note what it does NOT cover -- `qq-dense-in-rr' lives in
;;; structure-library/order-predicates.scm (it needs `<' and `POS-RR', which do
;;; not exist this early) and so stays `asserted'.  That asymmetry is honest:
;;; density is a THEOREM of the base, not part of it.
(define *primitive-files* '("theorem-library/axioms" "number-systems"))

;; In recompile mode (VNB_RECOMPILE=1, set by the VNB-with-compile script) the
;; compile path loads the tree ONCE (this --load) instead of twice.  It is also
;; INCREMENTAL: a file whose .com is up-to-date is loaded from that fresh .com
;; (its proofs then run COMPILED -- fast), and only files whose .scm is newer
;; than their .com (the ones you actually edited) are source-loaded.  This keeps
;; VNB-with-compile at ~seconds for a small edit instead of re-running every
;; library proof interpreted (~minutes).  In normal mode the name is loaded with
;; no extension, so MIT picks the up-to-date .com when present -- unchanged.
(define *vnb-recompile-mode* (and (get-environment-variable "VNB_RECOMPILE") #t))
;; VNB_FULL_RECOMPILE=1 (VNB-with-compile --full) forces EVERY file source-loaded
;; and recompiled, ignoring .com freshness.  Use it after editing a cross-file
;; MACRO (define-syntax in a core file): the incremental path keys off .scm/.com
;; mtimes and cannot see that a dependent's baked-in macro expansion went stale.
(define *vnb-full-recompile* (and (get-environment-variable "VNB_FULL_RECOMPILE") #t))

;; #t iff `base'.com is usable as-is: it exists, is at least as new as `base'.scm,
;; and we are not in a forced full recompile.
(define (file-fresh-com? base)
  (and (not *vnb-full-recompile*)
       (let ((com (string-append base ".com"))
             (scm (string-append base ".scm")))
         (let ((ct (and (file-exists? com) (file-modification-time com)))
               (st (and (file-exists? scm) (file-modification-time scm))))
           (and ct st (>= ct st))))))

;; Stub: prover-load calls this after every file, but clobber-guard.scm -- which
;; supplies the real one -- is itself loaded by prover-load.  Redefining a
;; procedure with another procedure is exactly what the guard permits.
(define (clobber-guard-check! file) file)

;;; PROOF-FILE CONTAINMENT.
;;;
;;; The rule (driver-kit.scm): every proof-driving Scheme procedure is either
;;; defined in driver-kit.scm, loaded before any proof, or is local to the file
;;; that defines it.  The second half is enforced here -- once driver-kit has
;;; loaded, each theorem-library/ and calculus/ file gets a fresh
;;; `extend-top-level-environment'.
;;;
;;; What that buys, verified: a file's top-level `define's stay in its own frame
;;; and cannot be seen by the next file, while its `set!' of *ps* still reaches
;;; the real binding, and it still sees every tactic, every macro (`bc*') and
;;; everything driver-kit defines.  So `(define BC '(succ p))' in a driver can no
;;; longer take down four tests in another file -- it breaks only its own.
;;;
;;; The flag starts #f, so the theorem-library/ VOCABULARY files that load before
;;; interactive (axioms, finsum-additive, ...) are untouched: they legitimately
;;; share wff-building helpers such as `tf' and `finite'.
(define *contain-proof-files?* #f)

(define (proof-file? f)
  (and *contain-proof-files?*
       (or (string-prefix? "theorem-library/" f)
           (string-prefix? "calculus/" f))))

(define (prover-load f)
  (let* ((base (string-append *prover-dir* f))
         ;; ALWAYS prefer a fresh .com; fall back to .scm SOURCE when the .com is
         ;; stale (older than its .scm) or absent.  This holds in BOTH normal and
         ;; recompile mode, so a source/tarball update self-heals -- MIT's `load'
         ;; otherwise picks a .com over its .scm blindly, silently serving a stale
         ;; binary (the classic "edited .scm but old .com wins" footgun).
         (path (if (file-fresh-com? base) base (string-append base ".scm"))))
    (cond ((member f *primitive-files*)
           (fluid-let ((*current-provenance* 'primitive)) (load path)))
          ((proof-file? f)
           (load path (extend-top-level-environment *driver-kit-env*)))
          (else (load path)))
    ;; No-op until clobber-guard.scm has taken its snapshot.  Contained files can
    ;; no longer trip it; it still guards the engine and structure-library.
    (clobber-guard-check! f)))

;; Load every file -- but clear *vnb-loading* if a file errors mid-load, so a
;; broken file can't strand the flag at #t and leave every (show) suppressed
;; for the rest of the session (the reset at the end of this file is skipped
;; when loading aborts).  On error: clear the flag, escape, then RE-RAISE so
;; the error still surfaces in the REPL -- now with interactive output enabled
;; for debugging.  On a clean load the thunk returns #f and nothing re-raises.
(let ((err (call-with-current-continuation
             (lambda (k)
               (with-exception-handler
                 (lambda (exn) (set! *vnb-loading* #f) (k exn))
                 (lambda () (for-each prover-load *vnb-files*) #f))))))
  (if err (raise err)))

;;; Files (compile-vnb!) always skips, independent of contents.  test-suite is
;;; not even in *vnb-files*; it is listed here only for documentation.
;;;
;;; driver-kit and clobber-guard capture `(the-environment)' at top level, and
;;; the environment a compiled block reports is not the environment its `load'
;;; put its definitions in.  Compiling them would hand every proof file a bogus
;;; parent environment (driver-kit) and an empty watch set (clobber-guard),
;;; SILENTLY -- compile-file accepts the form without complaint.  They are two
;;; small files; interpret them.
(define *vnb-no-compile-files*
  '("test-suite" "driver-kit" "clobber-guard"))

;;; A file with a top-level (bc* ...) use must NOT be compiled.  bc* is a macro
;;; defined in interactive.scm; MIT's compile-file processes each file in a
;;; fresh syntactic environment that cannot see it, so it emits a bare variable
;;; reference to bc*.  Loading that .com then aborts with
;;;   ;Variable reference to a syntactic keyword: bc*
;;; which strands the rest of load.scm -- every file after the offender
;;; (suggest/scout, audit, ...) never loads.  We detect such files by source
;;; scan rather than a hand-maintained list, so a newly added proof script that
;;; uses bc* can never silently reintroduce the abort.  The definition site
;;; (interactive) is exempt; it compiles fine.  Over-detection (a file that
;;; only mentions "(bc* " in quoted data) is harmless: it just loads as source.
;;; The same trap, a second macro: `declare-structure' (structures.scm).  A
;;; compiled commutative-ring.scm cannot see it either, so `(declare-structure
;;; COMMUTATIVE-RING (same-shape-as RING) (law "..."))' compiles as an
;;; APPLICATION and the .com dies on load with
;;;   ;Unbound variable: law
;;; It went unnoticed because those files' .com were stale, so load.scm was
;;; reading their source anyway -- until someone compiled them fresh (2026-07-12)
;;; and the library stopped loading.  compile-vnb! would have done the same to
;;; anyone.  So the scan is per-MACRO, not per-file, and adding a macro to the
;;; list is the whole fix.  Over-detection (a file merely mentioning the form in
;;; quoted data) is harmless: it just loads as source.
(define *vnb-top-level-macros*
  '(("(bc* "               . "interactive")     ; macro . its definition site
    ("(declare-structure " . "structures")
    ("(vlet "              . "vlet")))

(define (vnb-file-uses-bc*-macro? f)
  (find-first
    (lambda (entry)
      (and (not (string=? f (cdr entry)))
           (call-with-input-file (string-append *prover-dir* f ".scm")
             (lambda (port)
               (let loop ()
                 (let ((line (read-line port)))
                   (cond ((eof-object? line) #f)
                         ((substring? (car entry) line) #t)
                         (else (loop)))))))))
    *vnb-top-level-macros*))

;;; Recompile every file (call manually after editing sources).
(define (compile-vnb!)
  (for-each (lambda (f)
              (unless (or (member f *vnb-no-compile-files*)
                          (vnb-file-uses-bc*-macro? f)
                          ;; incremental: skip a file whose .com is already fresh
                          (file-fresh-com? (string-append *prover-dir* f)))
                (compile-file (string-append *prover-dir* f ".scm"))))
            *vnb-files*))

;;; Force-load from .scm source (bypasses stale .com files) then recompile.
(define (recompile-vnb!)
  (for-each (lambda (f)
              (load (string-append *prover-dir* f ".scm")))
            *vnb-files*)
  (compile-vnb!))

(display "VNB proof checker loaded.  Theory: ")
(display (theory-name *current-theory*))
(newline)
(if (not (null? *inert-macetes*))
    (begin
      (display ";; ")
      (display (length *inert-macetes*))
      (display " axioms/theorems registered as named-only -- macete form unsound (S-10).")
      (newline)
      (display ";; Use (display-inert-macetes) to list them.")
      (newline)))

;; Certification stamps from the last VNB test (reference/certification.scm, a
;; list of (certify! 'name "date") forms).  Written by `vnb-test'; absent until
;; the test has run at least once.  Loaded here so (status) can report when each
;; proven theorem was last re-verified.  certify! is defined in proof-debt.scm.
(let ((cert (string-append *reference-dir* "certification.scm")))
  (if (file-exists? cert)
      (begin (load cert)
             (display ";; certifications: ")
             (display (hash-table/count *certifications*))
             (display " proven theorem(s) stamped by the last VNB test\n"))
      (display ";; certifications: none on file -- run ./vnb-test to stamp\n")))

;; Classification invariant: DEFINITIONS ARE NOT PSS MEMBERS.  The PSS is the
;; set of *theorems* we excuse from the vnb-test (trusted on a warrant, never
;; re-proved); a definition is true by construction, not a theorem, so it has
;; no place on that roster.  It KEEPS its right to fire as a rewrite -- macete
;; installation is a separate registry, untouched here -- so a defining
;; equation still simplifies goals; it just is not a "support theorem".
;; Enforced globally (order-independent) so any definitional-provenance entry
;; that was installed via `support' is dropped from the PSS here.  MUST run
;; before (catalog)/(write-pss-md) so the generated .md and HTML count it right.
(let* ((before *support-theorem-names*)
       (kept   (filter (lambda (n) (not (eq? (provenance-of n) 'definitional)))
                       before)))
  (set! *support-theorem-names* kept)
  (let ((dropped (- (length before) (length kept))))
    (when (> dropped 0)
      (display ";; classification: ") (display dropped)
      (display " definition(s) de-supported (not PSS; still fire as rewrites)\n"))))

;; Regenerate the theorem/axiom catalog (THEOREMS.md) so it never goes stale.
(catalog)

;; Regenerate PSS.md (the dedicated Proof Support Set page) from the SAME
;; *support-theorem-names* the catalog's "Proof Support Set" section uses, so
;; the two never diverge.  Previously only (catalog) ran here, so PSS.md (and
;; its PSS.html) fossilised while THEOREMS.md kept current -- the two PSS lists
;; drifted apart (144 vs ~320 entries).
(write-pss-md)

;; Regenerate the proof-debt ledger (PROOF-DEBT.md) from *proof-debt*, which qed
;; has just filled for every proof in the library.  It had never been wired in:
;; `proof-debt-ledger' was defined in proof-debt.scm and called from nowhere, so
;; the file on disk was a 2026-06-03 snapshot listing the ten `demo-*' road-test
;; fixtures while the library grew to 125 real proofs.  Exactly the fossilisation
;; PSS.md suffered above.  Must run after (catalog), which needs no debt data,
;; and after every theorem-library file has reached its qed.
(proof-debt-ledger)
(report-keystones)

;; Regenerate the interactive-tactics menu (TACTICS.md) from the registry.
(write-tactics-md)

;; Regenerate GLOSSARY.md: every NAME in the system -- structures, instances,
;; views, predicates, functoids, accessors, defined constants, kernel heads and
;; tactics -- in one alphabetical list.  Runs after every registry is populated
;; and after (catalog), whose *theorem-table* the usage counts read.
(write-glossary-md)

;; Regenerate emacs/vnb-commands.lisp (the command-completion catalog) from the
;; same registry, so the M-x/button surface can never drift from (tactics).
(write-vnb-commands)

;; Invariant guard (so weirdos announce themselves instead of being hunted):
;; a `proof' warrant claims a machine proof, so it should never sit on an
;; asserted, non-PSS fact -- that is the "Asserted yet warrant: proof" anomaly.
;; Such a fact should be either machine-proven (provenance proven) or promoted
;; to a PSS support.  Surface any at load.
(let ((bad (filter (lambda (n)
                     (let ((w (warrant-of n)))
                       (and w (eq? (car w) 'proof)
                            (eq? (provenance-of n) 'asserted)
                            (not (memq n *support-theorem-names*)))))
                   (hash-table-keys *provenance*))))
  (if (null? bad)
      (display ";; warrant-invariant: ok (no asserted/non-PSS fact claims a proof)\n")
      (begin
        (display ";; WARRANT-INVARIANT WARNING: ")
        (display (length bad))
        (display " asserted/non-PSS fact(s) carry a 'proof warrant -- prove or PSS-promote:\n   ")
        (write bad) (newline))))

;; The COMPLEMENT of the guard above: the same anomaly INSIDE the PSS, which
;; the guard deliberately excludes.  That exclusion is why nobody had counted
;; these -- a `proof' warrant on an asserted PSS support claims a machine proof
;; that no load re-checks.  Soft nudge (count only); (proof-warrants-unproven)
;; returns (named unnamed).  See macetes.scm for what the split means.
(let* ((pw (proof-warrants-unproven))
       (named (car pw)) (unnamed (cadr pw)))
  (if (and (null? named) (null? unnamed))
      (display ";; proof-warrant-audit: ok (every 'proof warrant sits on a proven fact)\n")
      (begin
        (display ";; proof-warrant-audit: ")
        (display (+ (length named) (length unnamed)))
        (display " asserted PSS fact(s) claim a machine proof -- ")
        (display (length named)) (display " name a file, ")
        (display (length unnamed))
        (display " recite the derivation instead.\n")
        (display ";;   file-named (auditable -- load the file and see if it still qeds): ")
        (write named) (newline)
        (display ";;   (proof-warrants-unproven) for the rest\n"))))

;; Soundness gate: a proven theorem must not depend -- transitively, through the
;; proof citation graph -- on ITSELF.  That is a circular proof with no real
;; grounding (assert X, prove Y from X, then "prove" X from Y: each step looks
;; fine, but together nothing is founded).  Walk the live citation graph.
(let ((cycles (proof-cycle-check)))
  (if (null? cycles)
      (display ";; proof-cycle-check: ok (no proven theorem depends on itself)\n")
      (begin
        (display ";; PROOF-CYCLE ERROR: ")
        (display (length cycles))
        (display " circular dependency cycle(s) among proven theorems:\n")
        (for-each (lambda (c)
                    (display ";;   ")
                    (let inner ((p c))
                      (cond ((null? (cdr p)) (display (car p)))
                            (else (display (car p)) (display " -> ") (inner (cdr p)))))
                    (newline))
                  cycles)
        ;; Hard gate: a genuine proof cycle is a soundness bug -- stop the world,
        ;; as the case-fold gate below does.  (Own-name and definitional-unfold
        ;; edges are already excluded in record-proof-debt!, so a surviving cycle
        ;; runs through real proven citations.)  If a legitimate mutual induction
        ;; ever trips this, the fix is to exclude that edge at record time, never
        ;; to soften the gate to a warning.
        (error "proof-cycle-check: circular proof dependency among proven theorems"
               cycles))))

;; rests-on typo nudge (soft): a (rests-on 'R '(A B)) dep that names no installed
;; theorem is silently a sink -- it weakens the DAG check without saying so.
;; Report them by (declaring . bad-dep) so they can be fixed; never a gate.
(let ((bad (rests-on-unknown-deps)))
  (if (null? bad)
      (when (pair? (rests-on-declared-names))
        (display ";; rests-on: ok (all declared dependencies name installed theorems)\n"))
      (begin
        (display ";; rests-on: ") (display (length bad))
        (display " declared dependenc(y/ies) naming no installed theorem:\n   ")
        (write bad) (newline))))

;; Soundness gate: the reader case-folds symbols, so a binder pair differing
;; only in case (FORALL N .. FORSOME n) collapses and silently changes meaning
;; (cluster-point, difference-membership, finsum-ring-*).  Post-read that is
;; ALWAYS a binder whose variable is already in scope; case-fold-audit walks
;; every installed formula with the kernel's full binder vocabulary, so zero
;; hits => zero case-fold collisions in the library.  Authoritative over the
;; source-level scan-case-fold.py (which cannot see tf-built / -rev formulas).
(let ((bad (case-fold-audit)))
  (if (null? bad)
      (display ";; case-fold-audit: ok (no binder shadows an in-scope variable)\n")
      (begin
        (display ";; CASE-FOLD WARNING: ") (display (length bad))
        (display " formula(s) have a shadowing binder (likely a case-fold collision):\n")
        (for-each (lambda (e)
                    (display ";;   ") (display (car e)) (display ": ") (write (cdr e)) (newline))
                  bad))))

;; Same collision class, one level deeper: case-fold-audit walks *theorem-table*
;; only, so a def-functoid BODY -- which lives in *functoid-registry* -- was never
;; checked.  A body binder that case-folds onto a PARAMETER captures it silently
;; (MONALG-MUL's `m' vs param M turned (OPR M) into OPR-of-the-point, clean load
;; and all; 2026-07-25).  functoid-binder-audit wraps each body in a FORALL per
;; parameter and reuses the shadowing walk.  HARD gate: the library is clean, so
;; a hit is a real capture (or a needless shadow -- rename the binder x_/y_).
(let ((bad (functoid-binder-audit)))
  (if (null? bad)
      (display ";; functoid-binder-audit: ok (no functoid body binder shadows a parameter)\n")
      (begin
        (display "\n;; functoid-binder-audit: ") (display (length bad))
        (display " functoid(s) have a body binder shadowing a parameter (case-fold capture):\n")
        (for-each (lambda (e)
                    (display ";;   ") (display (car e)) (display ": ") (write (cdr e)) (newline))
                  bad)
        (error "functoid-binder-audit: functoid body binder(s) collide with a parameter -- see above"))))

;; Soundness gate: a bound variable named like a registered constant (accessor /
;; operator / functoid / predicate / defined fn) is read as that CONSTANT in head
;; position, scope-blind, silently changing the formula's meaning.  This is the
;; accessor/variable collision class (distinct from the binder-over-binder one
;; above).  HARD gate, with a deliberately loud report -- accessors carry
;; distinctive names (CARR/PTS/DIST/IDEN/MUL/VEC/...) precisely so this never
;; happens; a hit means someone reused one as a bound variable.
(let ((bad (constant-binder-audit)))
  (if (null? bad)
      (display ";; constant-binder-audit: ok (no binder is named like a registered constant)\n")
      (begin (shout-constant-binders! bad)
             (error "constant-binder-audit: bound variable(s) collide with registered constants -- see above"))))

;; ONE NAME, ONE SLOT.  An accessor macete is global and keyed by NAME, so an
;; accessor claimed at two different slot indices cannot have a correct global
;; reduction.  def-structure now withdraws the reduction rather than install a
;; false one (structures.scm, register-accessor-index!) -- `mul' used to hold the
;; group family's slot 2, and (mac 'mul) on (MUL ZZ-RING) reduced the INTEGERS'
;; MULTIPLICATION to binplus, their addition, all the way to a qed.
;;
;; HARD gate, as of the 2026-07-12 renames: the three legacy ambiguities are
;; gone (the group family's operation is OPR, the field's inverse RECIP, the
;; normed field's norm FNRM), so an ambiguity is now unambiguously a bug.
(let* ((audit (kernel-rules-audit))
       (undoc (car audit))
       (unused (cadr audit)))
  (if (and (null? undoc) (null? unused))
      (display ";; kernel-rules-audit: ok (documented trusted base = rules actually stamped)\n")
      (begin
        (if (pair? undoc)
            (begin
              (display "\n;; kernel-rules-audit: ") (display (length undoc))
              (display " TRUSTED RULE TAG(S) STAMPED BUT NOT DOCUMENTED --\n")
              (display ";; add them to *kernel-rule-tags* (tactics-help.scm) and to\n")
              (display ";; reference/KERNEL-RULES.md; an undocumented tag is trusted surface\n")
              (display ";; nobody can audit:\n")
              (display ";;   ") (display undoc) (newline)))
        (if (pair? unused)
            (begin
              (display ";; kernel-rules-audit: ") (display (length unused))
              (display " documented tag(s) not exercised by this load")
              (display " (a rule no proof uses,\n")
              (display ";; or one no tactic can reach): ")
              (display unused) (newline))))))

(let ((bad (connective-arity-audit)))
  (if (null? bad)
      (display ";; connective-arity-audit: ok (every installed formula's connectives are binary)\n")
      (begin
        (display "\n;; connective-arity-audit: ") (display (length bad))
        (display " INSTALLED FORMULA(S) WITH A MALFORMED CONNECTIVE --\n")
        (display ";; make-wff rejects these; theory-add-axiom!/support install without\n")
        (display ";; validating, and the kernel reads AND/OR/IMPLIES/IFF with\n")
        (display ";; binary-left/right, so extra conjuncts are SILENTLY DROPPED and the\n")
        (display ";; formula does not say what it appears to say.  Restate with nested\n")
        (display ";; binary connectives, or as chained implications:\n")
        (for-each (lambda (e)
                    (display ";;   ") (display (car e))
                    (display "  ") (write (cdr e)) (newline))
                  bad)
        ;; FATAL since 2026-07-28, when the pre-existing backlog reached zero.  A
        ;; malformed connective means the trusted base does not say what it
        ;; appears to say; there is no safe way to carry one.
        (error "connective-arity-audit: installed formula(s) with a malformed connective -- see above"))))

;; Same door as the audit above -- support / theory-add-axiom! install a raw
;; S-expression without validating it -- but a different defect: a variable the
;; author forgot to bind.  The kernel reads a free name literally, so such a
;; fact means whatever that name denotes WHERE IT IS CITED, and it looks like it
;; works for exactly as long as the citing proof spells its own eigenvariable
;; the same way.  WARN-ONLY: unlike a dropped conjunct, a free variable is not
;; automatically wrong (see the whitelisted splice metavariables), so this
;; reports and lets the author judge.
(let ((fv (free-variable-audit)))
  (if (null? fv)
      (display ";; free-variable-audit: ok (no installed formula has a free variable)\n")
      (begin
        (display "\n;; free-variable-audit: ") (display (length fv))
        (display " installed formula(s) with a FREE VARIABLE --\n")
        (display ";; each means whatever that name denotes at the point of citation, so it\n")
        (display ";; changes meaning silently when a caller renames a binder.  Bind it\n")
        (display ";; (with a typing guard where there is one to give):\n")
        (for-each (lambda (e)
                    (display ";;   ") (display (car e))
                    (display "  free=") (write (cdr e)) (newline))
                  fv))))

;; Third gate on the same door, and the one that enumerates instead of waiting:
;; every applied head in every installed formula, checked against the constant
;; registry -- the table free-vars / subst-free actually consult.  An
;; unregistered head is read as an applied function VARIABLE, which is how
;; `bijection' came to be a free variable of well-ordering-principle and of the
;; whole inverse-bij family.  WARN-ONLY: a new head is a declaration that has
;; not been written yet, not a formula that says the wrong thing.
(report-head-registry)

;; ... and the gate on the door itself: every formula is graded by make-wff's
;; validator AS install-theorem! installs it (macetes.scm), instead of by an
;; audit written after the next defect.  Each failure already warned, in place,
;; naming the file; this is the count.
(let ((iv (install-validation-failures)))
  (if (null? iv)
      (display ";; install-grading: ok (every installed formula passes make-wff's grading)\n")
      (begin
        (display "\n;; install-grading: ") (display (length iv))
        (display " installed formula(s) MALFORMED (warned above, in place):\n")
        (for-each (lambda (e)
                    (display ";;   ") (display (car e))
                    (display "  [") (display (caddr e)) (display "]\n")
                    (display ";;     ") (display (cadr e)) (newline))
                  iv))))

;; Fifth gate, and the one bijection-identity taught (2026-08-05): a repaired
;; RULE does not repair the AXIOMS that assert what the rule refuses.  Every
;; installed formula is checked for a universally quantified class parameter
;; standing, unguarded, in a sethood-carrying position of a function membership
;; it ASSERTS.  WARN-ONLY; the exemptions and the coverage gaps are in audit.scm.
(let ((sh (sethood-audit)))
  (if (null? sh)
      (display ";; sethood-audit: ok (no asserted function membership over an unguarded class)\n")
      (begin
        (display "\n;; sethood-audit: ") (display (length sh))
        (display " asserted function membership(s) over an UNGUARDED class parameter --\n")
        (display ";; at X := ORD each claims a proper-class-domain function exists, which is\n")
        (display ";; what pi-lambda-type!'s (IN A SET) obligation refuses.  Guard the axiom:\n")
        (for-each (lambda (e)
                    (display ";;   ") (display (car e))
                    (display "  var=") (display (cadr e))
                    (display "  in=") (write (caddr e)) (newline))
                  sh))))

;; The oracle list in proof-debt.scm must stay in step with the trust taxonomy
;; in tactics-help.scm, which loads far too late for proof-debt to read it.
;; Same arrangement as kernel-rules-audit: keep two lists, and compare them here.
(let* ((declared (sort *pd-oracle-verbs* (lambda (a b) (string<? (symbol->string a) (symbol->string b)))))
       (tagged   (sort (tactics--of-kind 'oracle) (lambda (a b) (string<? (symbol->string a) (symbol->string b))))))
  (if (equal? declared tagged)
      (display ";; oracle-inventory: ok (proof-debt's oracle list = the `oracle' tactic kind)\n")
      (begin
        (display "\n;; ORACLE-INVENTORY DRIFT: *pd-oracle-verbs* (proof-debt.scm) and the\n")
        (display ";; `oracle' entries of *tactic-kind* (tactics-help.scm) disagree.  A bill\n")
        (display ";; can then under-report the trusted code a proof leans on.\n")
        (display ";;   proof-debt says: ") (write declared) (newline)
        (display ";;   tactic-kind says: ") (write tagged) (newline))))

(let ((amb (accessor-index-audit)))
  (if (null? amb)
      (display ";; accessor-index-audit: ok (every accessor name denotes one slot)\n")
      (begin
        (display "\n;; accessor-index-audit: ") (display (length amb))
        (display " AMBIGUOUS accessor(s) -- a name at two slot indices has NO correct\n")
        (display ";; global (NTH k) reduction, so none is installed.  Rename one side.\n")
        (for-each
          (lambda (entry)
            (display ";;   ") (display (car entry)) (display " : ")
            (for-each (lambda (hit)
                        (display (car hit)) (display "@") (display (cdr hit)) (display "  "))
                      (cdr entry))
            (newline))
          amb)
        (error "accessor-index-audit: accessor name(s) claimed at two slot indices -- see above"))))

;; The other half: an accessor applied to a structure that HAS no such slot.
;; Well-formed, silent, and means something else -- (MUL ag) where ag is an
;; abelian group whose operation is OPR.  This is what drove the OPR/RECIP/FNRM
;; renames to completion; nothing else would have found `nf-metric-distance',
;; which took NRM of a normed field and failed no proof.
(let ((bad (accessor-type-audit)))
  (if (null? bad)
      (display ";; accessor-type-audit: ok (every accessor names a slot of its structure)\n")
      (begin
        (display "\n;; accessor-type-audit: accessor applied to the wrong structure:\n")
        (for-each
          (lambda (entry)
            (for-each
              (lambda (hit)
                (display ";;   in `") (display (car entry)) (display "': (")
                (display (car hit)) (display " ") (display (cadr hit))
                (display ") -- but ") (display (cadr hit)) (display " : ")
                (display (caddr hit)) (display ", which has no such slot.\n"))
              (cdr entry)))
          bad)
        (error "accessor-type-audit: accessor(s) applied to a structure lacking that slot -- see above"))))

;; A FUNCTOR YOU HAVE NOT PROVED IS A FUNCTOR YOU DO NOT HAVE.
;; def-functor (an accessor correspondence) gets its typing and functoriality by
;; construction -- functoriality.scm PROVES the latter, modulo 0.  A
;; def-constructed-functor, whose object map is a built term (the metric of a
;; normed field; the topology of a metric space), gets NOTHING for free: its two
;; theorems have content.  So the constructor records them as OBLIGATIONS and
;; asserts nothing, and they are listed here until discharged.  SOFT: an open
;; obligation is honest work outstanding, not a bug.
(let ((owed (functor-obligation-audit)))
  (if (null? owed)
      (display ";; functor obligations: none outstanding\n")
      (begin
        (display ";; functor obligations OUTSTANDING (the functor is not yet a functor):\n")
        (for-each (lambda (ob)
                    (display ";;   ") (display (car ob))
                    (display "  -- (functor-obligation '") (display (car ob))
                    (display ") for the goal\n"))
                  owed))))

;; Categorisation nudge (soft -- a discipline, not a soundness gate): every PSS
;; support should be filed under a *pss-category-order* bucket via category!.
;; Report how many are not yet filed; never fails the build.
(let ((un (uncategorized-pss-names)))
  (if (null? un)
      (display ";; pss-categories: ok (all support entries filed)\n")
      (begin
        (display ";; pss-categories: ") (display (length un))
        (display " uncategorized PSS entr(y/ies) -- file with (category! 'name 'cat):\n   ")
        (write un) (newline))))

;; Gloss nudge (soft, count only -- a discipline going forward, not a gate and
;; not a march-order over the legacy backlog): reference-warranted entries want
;; a gloss! so the base is searchable by content.  Report a bare count; the
;; names are available via (reference-warrants-without-gloss) when wanted.
(let ((n (length (reference-warrants-without-gloss))))
  (if (zero? n)
      (display ";; reference-glosses: ok (every reference-warranted entry glossed)\n")
      (begin
        (display ";; reference-glosses: ") (display n)
        (display " reference-warranted entr(y/ies) without a gloss")
        (display " -- (reference-warrants-without-gloss) to list\n"))))

;; Rebuild the browser reference (the reference.html hub + one page per doc)
;; from the just-refreshed .md files.  The .md regenerate on every load but the
;; HTML did NOT -- it was a
;; manual step, so the page the browser actually renders could fossilise (e.g.
;; show a now-proven theorem under "Asserted -- accepted without proof").
;;
;; This runs at the END of every load, INCLUDING when the prover is launched as
;; an Emacs subprocess (the GUI launcher).  A synchronous child that inherits
;; Emacs's pty can deadlock on terminal I/O -- which wedges the whole load, so
;; the prover never reaches its prompt: the launcher then sits with no Emacs
;; workspace and a blank browser.  So make the rebuild strictly best-effort and
;; un-wedgeable: detach the child from the terminal (stdin from /dev/null,
;; output discarded) and guard it (a missing/failing/blocking python3 just
;; leaves the previous HTML in place).
(load-option 'synchronous-subprocess)
(ignore-errors
  (run-shell-command
    (string-append "python3 " *prover-dir*
                   "reference/build-reference-html.py < /dev/null > /dev/null 2>&1 &")))

;; Clean slate.  The theorem-library / calculus proof scripts loaded above each
;; run an interactive (sp ...) ... (qed ...) and leave their finished proof
;; sitting in the global *ps* (qed does not null it).  Without this reset a
;; freshly started prover boots holding the LAST script's proof, so the first
;; (show) dumps a foreign "Proof complete" tree instead of "No current proof"
;; -- and worse, if a subsequent (sp ...) fails to actually evaluate, the stale
;; *ps* gets repainted and looks like sp printed someone else's proof.  A new
;; session must start with no current proof.
(set! *ps* #f)
(set! *proof-script* '())
(set! *current-goal* #f)

;; Load done: re-enable interactive show output.  (Held #t since the top of
;; this file to suppress the per-tactic flood from the library proof scripts.)
(set! *vnb-loading* #f)

;; Load done: from now on, make-wff REJECTS a formula whose binder is named like
;; a registered constant -- the interactive counterpart of the
;; constant-binder-audit gate.  Off during the load above so the library's own
;; (clean) wff construction stays silent.
(set! *reject-constant-binders?* #t)
