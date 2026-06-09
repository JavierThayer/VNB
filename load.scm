;;; load.scm -- load the proof checker in dependency order
;;;
;;; File names are passed without extension so MIT Scheme picks the
;;; compiled .com file when present, falling back to the .scm source.
;;; Recompile with (compile-vnb!) below or via the Makefile.

(define *prover-dir*
  (directory-namestring (current-load-pathname)))

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
    "structure-library/metric-topology"
    "structure-library/ring-simplify"
    ;; Commutative-ring identity decision procedure (multiset monomials);
    ;; reuses ring-simplify's poly plumbing, so loads right after it.
    "structure-library/comm-ring-simplify"
    "number-systems"
    "structure-library/order-predicates"
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
    ;; Restrictive ring/field structures (genuine IS-X predicates; need NN/RR
    ;; from number-systems, used by numeric-instances below).
    "structure-library/commutative-ring"
    "structure-library/integral-domain"
    "structure-library/field"
    "structure-library/euclidean-ring"
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
    "theorem-library/subsequence-capture"
    "theorem-library/diagonalization"
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
    ;; Context and proof commands
    "contexts"
    "proof-commands"
    "interactive"
    ;; Warrant / proof-debt ledger: records each qed proof's bill of asserted
    ;; facts it rests on (loads right after interactive so qed can call it).
    "proof-debt"
    ;; The trivial subtype-subsumption laws ("every X is a Y"), PROVEN via
    ;; mac-h instead of asserted -- formerly phantom debt leaves.  Needs the
    ;; interactive tactics + qed/proof-debt, so loads here.
    "structure-library/subtype-laws"
    ;; The five metric laws (pos/self-zero/zero-eq/sym/triangle), PROVEN by
    ;; projecting the is-metric property folded into IS-METRIC-SPACE -- they
    ;; were redundant asserted axioms (a definition oversight).
    "structure-library/metric-laws"
    ;; LaTeX rendering of formulas (used by Emacs vnb-view-as-pdf).
    "tex-output"
    ;; Assumption-pattern scanner for forward-move discovery
    ;; (used by Emacs vnb-suggest-forward-moves).
    "suggest"))

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

(for-each prover-load *vnb-files*)

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

;; Regenerate the theorem/axiom catalog (THEOREMS.md) so it never goes stale.
(catalog)
