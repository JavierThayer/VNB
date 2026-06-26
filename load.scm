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
    "structure-library/euclidean-ring"
    ;; Ideals, principal ideals, and principal-ideal domains over a commutative
    ;; ring (IS-IDEAL / PRINCIPAL-IDEAL / IS-PID), plus the well-ordering of NN
    ;; (nn-least-element).  Vocabulary for the Euclidean-ring => PID proof.
    "structure-library/ideal"
    "structure-library/normed-field"
    ;; Normed abelian group: AG subtype (slots A MUL E INV) + norm NRM at
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
    "theorem-library/diagonalization"
    ;; Totally bounded => every sequence has a Cauchy subsequence.  Assembles
    ;; pigeonhole + diagonalization + ball-2r-triangle; supplies the SUBSEQ /
    ;; STRICTLY-MONO-NN / IS-SUBSEQUENCE vocabulary.  Needs TOTALLY-BOUNDED/BALL
    ;; (metric-topology), IS-CAUCHY-SEQ (metric-completeness), INF-SUBSETS.
    "theorem-library/cauchy-subsequence"
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
    ;; product metric D_w = SUM w(n) d_n/(1+d_n), coordinatewise convergence,
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
    ;; LaTeX rendering of formulas (used by Emacs vnb-view-as-pdf).
    "tex-output"
    ;; Render a completed proof as a LaTeX step-trace ((proof-tex name) /
    ;; (view-proof-pdf name)).  Needs tex-output (expr->tex) + the replay
    ;; machinery in interactive.scm.
    "proof-tex"
    ;; Assumption-pattern scanner for forward-move discovery
    ;; (used by Emacs vnb-suggest-forward-moves).
    "suggest"
    ;; Library hygiene diagnostics: (audit-unbounded) scans for the partial-
    ;; equality hazard (unbounded universals feeding partial terms under =).
    "audit"
    ;; English verbalization of a wff (companion to expr->str symbolic /
    ;; describe-structure).  Loads last: uses expr->str + the theorem table.
    "wff-english"
    ;; Self-describing registry of the interactive tactics: (tactics) prints
    ;; the menu, (write-tactics-md) emits reference/TACTICS.md for the browser
    ;; reference.  Pure display/string; no dependencies beyond *reference-dir*.
    "tactics-help"))

;;; Files whose top-level axioms are part of the trusted VNB base (not
;;; definitional sugar, not asserted math).  Their loads run with
;;; *current-provenance* = 'primitive so install-theorem! stamps them.
;;; The make-vnb-base-theory core is marked primitive at its build site
;;; (theory.scm); this list covers the remaining foundational axiom file.
(define *primitive-files* '("theorem-library/axioms"))

(define (prover-load f)
  (if (member f *primitive-files*)
      (fluid-let ((*current-provenance* 'primitive))
        (load (string-append *prover-dir* f)))
      (load (string-append *prover-dir* f))))

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

;;; Files skipped by (compile-vnb!): they use macros (e.g. `bc*' from
;;; interactive.scm) that MIT Scheme's compile-file doesn't see, because
;;; each compile-file call starts with a fresh syntactic environment.
;;; They load fast enough as source.
(define *vnb-no-compile-files*
  '("test-suite"))

;;; Recompile every file (call manually after editing sources).
(define (compile-vnb!)
  (for-each (lambda (f)
              (unless (member f *vnb-no-compile-files*)
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
