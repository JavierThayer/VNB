;;; load.scm -- load the proof checker in dependency order
;;;
;;; File names are passed without extension so MIT Scheme picks the
;;; compiled .com file when present, falling back to the .scm source.
;;; Recompile with (compile-vnb!) below or via the Makefile.

(define *prover-dir*
  (directory-namestring (current-load-pathname)))

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
    "wff"
    "sequents"
    "parser"
    "deduction-graphs"
    "primitive-inferences"
    "arith-eval"
    "macetes"
    "theory"
    "structures"
    ;; Named operation properties — referenced by structure declarations.
    "structure-library/operation-properties"
    ;; Theorem library (axioms not yet derivable from kernel)
    "theorem-library/axioms"
    "theorem-library/well-ordering"
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
    ;; Compactness + the four-way characterization (calculus.pdf Prop 3.12):
    ;; IS-COMPACT / IS-OPEN-COVER / CLUSTER-POINT / HAS-FIP + the equivalences.
    ;; Needs IS-OPEN/IS-CLOSED (above), TOTALLY-BOUNDED/BALL (metric-topology),
    ;; IS-COMPLETE (metric-completeness).
    "structure-library/compactness"
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
    ;; def-view-as can refer to any of them.
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
    ;; The bounded metric d/(1+d) of a metric space + its topological
    ;; equivalence to d (identity bicontinuous); the RR-BOUNDED-MS instance.
    ;; Needs IS-CONTINUOUS (metric-continuity), RR-MS (numeric-instances above)
    ;; and the f(t)=t/(1+t) family (scalar-inequalities).
    "structure-library/bounded-metric"
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
    ;; Needs FINSUM + the additive layer above + RR-RING (numeric-instances).
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
    ;; instances (RR-RING/RR-MS), number-systems (power), metric-completeness.
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
    ;; Warrant / proof-debt ledger: records each qed proof's bill of asserted
    ;; facts it rests on (loads right after interactive so qed can call it).
    "proof-debt"
    ;; minimize! -- "choose v with MEASURE(v) least".  A composite tactic over
    ;; the cmd-* layer (no kernel rule); its one mathematical appeal is
    ;; nn-least-element, resolved by NAME at call time, so it may load here,
    ;; long before theorem-library/nn-least-element.
    "minimize"
    ;; Snapshot every procedure binding, then let prover-load check after each
    ;; later file that none was rebound to a non-procedure -- the case-fold trap
    ;; ((define BC ...) clobbering the `bc' tactic) that no other gate catches.
    "clobber-guard"
    ;; The trivial subtype-subsumption laws ("every X is a Y"), PROVEN via
    ;; mac-h instead of asserted -- formerly phantom debt leaves.  Needs the
    ;; interactive tactics + qed/proof-debt, so loads here.
    "structure-library/subtype-laws"
    ;; The three BIJECTION projection lemmas (in-fun / injective / surjective),
    ;; PROVEN modulo 0 from bijection-membership-iff -- formerly asserted in
    ;; bijection.scm "for direct use" (phantom debt).
    "structure-library/bijection-derived"
    ;; The five metric laws (pos/self-zero/zero-eq/sym/triangle), PROVEN by
    ;; projecting the is-metric property folded into IS-METRIC-SPACE -- they
    ;; were redundant asserted axioms (a definition oversight).
    "structure-library/metric-laws"
    ;; Diagonalization: nested infinite subsets of NN -> a single strictly-
    ;; monotone sequence with tail in every member.  PROVEN to QED via
    ;; dc-on-nn-pred + diagonalization-lemmas' three generic supports.  Runs
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
    ;; euclidean-ideal-has-generator, PROVEN by `minimize!' (formerly an asserted
    ;; support in structure-library/ideal.scm).  THE mathematical core of
    ;; "every Euclidean ring is a PID".  Needs nn-least-element (for minimize!),
    ;; ideal.scm, euclidean-ring.scm, mat-equiv.scm (nn-succ-le-antisym).
    "theorem-library/euclidean-ideal-generator-proof"
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
    ;; Phase C, Cor 3.46: a submodule of a free module over a euclidean ring is
    ;; free of rank <= n.  submodule-fg is the lemma linear-algebra.tex \iffalse'd
    ;; out (tex:1651) and cannot do without -- Smith CONSUMES a finite generating
    ;; set for the submodule, it cannot produce one.  Needs mod-seq, finite-
    ;; dimensional (IS-SUBMODULE), euclidean-ring, smith-staircase.
    "theorem-library/submodule-free"
    ;; Phase C, Remark 3.39: the matrix action on module-element sequences is
    ;; associative, (PQ).u = P.(Q.u).  Mirrors matmul-assoc via finsum-fubini.
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
    "theorem-library/reference-topics"))

;;; Files whose top-level axioms are part of the trusted VNB base (not
;;; definitional sugar, not asserted math).  Their loads run with
;;; *current-provenance* = 'primitive so install-theorem! stamps them.
;;; The make-vnb-base-theory core is marked primitive at its build site
;;; (theory.scm); this list covers the remaining foundational axiom file.
(define *primitive-files* '("theorem-library/axioms"))

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

(define (prover-load f)
  (let* ((base (string-append *prover-dir* f))
         ;; ALWAYS prefer a fresh .com; fall back to .scm SOURCE when the .com is
         ;; stale (older than its .scm) or absent.  This holds in BOTH normal and
         ;; recompile mode, so a source/tarball update self-heals -- MIT's `load'
         ;; otherwise picks a .com over its .scm blindly, silently serving a stale
         ;; binary (the classic "edited .scm but old .com wins" footgun).
         (path (if (file-fresh-com? base) base (string-append base ".scm"))))
    (if (member f *primitive-files*)
        (fluid-let ((*current-provenance* 'primitive)) (load path))
        (load path))
    ;; No-op until clobber-guard.scm has taken its snapshot.
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
(define *vnb-no-compile-files*
  '("test-suite"))

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
(define (vnb-file-uses-bc*-macro? f)
  (and (not (string=? f "interactive"))
       (call-with-input-file (string-append *prover-dir* f ".scm")
         (lambda (port)
           (let loop ()
             (let ((line (read-line port)))
               (cond ((eof-object? line) #f)
                     ((substring? "(bc* " line) #t)
                     (else (loop)))))))))

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

;; Regenerate the interactive-tactics menu (TACTICS.md) from the registry.
(write-tactics-md)

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

;; Soundness gate: a proven theorem must not depend -- transitively, through the
;; proof citation graph -- on ITSELF.  That is a circular proof with no real
;; grounding (assert X, prove Y from X, then "prove" X from Y: each step looks
;; fine, but together nothing is founded).  Walk the live citation graph.
(let ((cycles (proof-cycle-check)))
  (if (null? cycles)
      (display ";; proof-cycle-check: ok (no proven theorem depends on itself)\n")
      (begin
        (display ";; PROOF-CYCLE WARNING: ")
        (display (length cycles))
        (display " circular dependency cycle(s) among proven theorems:\n")
        (for-each (lambda (c)
                    (display ";;   ")
                    (let inner ((p c))
                      (cond ((null? (cdr p)) (display (car p)))
                            (else (display (car p)) (display " -> ") (inner (cdr p)))))
                    (newline))
                  cycles))))

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

;; Load done: from now on, make-wff warns (loudly) if a user builds a formula
;; whose binder is named like a registered constant -- the interactive
;; counterpart of the constant-binder-audit gate.  Off during the load above so
;; the library's own (clean) wff construction stays silent.
(set! *warn-constant-binders?* #t)
