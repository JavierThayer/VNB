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

;;; -----------------------------------------------------------------------
;;; RE-ROOT ON RESTORE.  `*prover-dir*' above is computed at LOAD time and then
;;; frozen into the band by `disk-save'.  The band travels: the user's
;;; nquick-load.sh rsyncs it from the build machine precisely so a start costs
;;; 0.1 s instead of a full load.  On the receiving machine every path derived
;;; from it -- reference/, printouts/ -- then named a directory belonging to the
;;; OTHER machine, and the failures were silent or misdirected: a reference
;;; writer aimed at a directory that does not exist, and `view-proof-pdf'
;;; reported "Permission denied" about the sender's home (2026-09-05, treated at
;;; the time as a permissions problem; it was this).
;;;
;;; The launcher knows the truth -- it computes PROVER_DIR from its own location
;;; -- and exports it as VNB_PROVER_DIR.  Re-read it whenever the image is
;;; restored, and say so if the frozen value is wrong and nothing tells us
;;; better, because a wrong root is worth a line of noise at startup.
(define (vnb-reroot!)
  (let ((env (get-environment-variable "VNB_PROVER_DIR")))
    (cond ((and env (not (string-null? env)))
           (let ((root (if (string-suffix? "/" env) env (string-append env "/"))))
             (if (not (string=? root *prover-dir*))
                 (begin
                   (set! *prover-dir* root)
                   (set! *reference-dir* (string-append root "reference/"))
                   (set! *printouts-dir* (string-append root "printouts/"))))))
          ((not (file-directory? *prover-dir*))
           (display ";VNB warning: the image was built under ")
           (display *prover-dir*)
           (display ", which does not exist here, and VNB_PROVER_DIR is unset.")
           (newline)
           (display ";             Generated files (reference/, printouts/) will not be written.")
           (newline)))))

(add-event-receiver! event:after-restore vnb-reroot!)


;;; PROOF CERTIFICATES (certificates.scm, 2026-09-24).  #t while the file loop
;;; below runs, and only then: a proof file is loaded from its certificate
;;; (VNB_CERTIFIED=on|strict) or proved with its certificate written
;;; (VNB_CERTIFIED=off) only as part of a load of the tree.  The store is
;;; written unless VNB_WRITE_CERTS=0.  Defined here, not in certificates.scm,
;;; because that file loads inside the loop.
(define *cert-in-load-list* #f)
(define *vnb-write-certs*
  (let ((v (get-environment-variable "VNB_WRITE_CERTS")))
    (not (and v (string=? v "0")))))

(define *vnb-files*
  '(;; FIRST, so that every later file is checked.  It snapshots every name
    ;; currently bound to a procedure -- which at this point is MIT Scheme's own
    ;; (`append', `list', `cons', `length' ...), exactly the ones a proof file's
    ;; (define APPEND '(...)) would clobber -- and grows the set after each file.
    ;; It used to load half way down, leaving 126 library files unguarded.
    "clobber-guard"
    ;; Core kernel
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
    ;; THE INFERENCE CHECKERS (batch 10, 2026-09-20).  One file per kind of
    ;; kernel operation; each registers a checker per rule tag, and the loader
    ;; arms *dg-check-inferences?* after the last of them -- so every inference
    ;; the library records from here on is verified against the rule it names.
    ;; The logic file also holds the shared helpers the other three use, so it
    ;; must come first.  See *rule-checker-groups* below and
    ;; docs/rule-checkers-2026-09-20.md.
    "rule-checkers-logic"
    "rule-checkers-schema"
    "rule-checkers-rewrite"
    "rule-checkers-oracle"
    ;; Book registry — sources a `reference' warrant may cite by key.  Must
    ;; precede every structure-library / theorem-library file that cites one.
    "structure-library/references"
    ;; Named operation properties — referenced by structure declarations.
    "structure-library/operation-properties"
    ;; Theorem library (axioms not yet derivable from kernel)
    "theorem-library/axioms"
    ;; theorem-library/well-ordering RETIRED 2026-09-20 (batch 9-B).  Its one entry,
    ;; `well-ordering-principle', was an ASSERTED PSS member stated with the
    ;; then-axiomatised CARD.  CARD is now DEFINED and the statement is PROVEN, character
    ;; for character, in theorem-library/rake-ord-pigeonhole (it was card-star-well-ordering
    ;; there).  The file is archive/2026-09-20-card-defined/well-ordering.scm.
    ;; The NBG facts about SET the kernel rules do not give -- chiefly that a
    ;; class included in a set is a set.  Foundational: loaded with them.
    "structure-library/set-basics"
    ;; DIFFERENCE and SINGLETON: two set constructors that structure-library/field.scm
    ;; writes into IS-FIELD's defining IFF.  HOISTED here 2026-09-20 (batch 12-A) out of
    ;; prod-of-sums (~454) and theorem-library/field-ring-view (~1142), where they stood far
    ;; BELOW their first use.  Definitions only; the membership laws keep their homes.
    "structure-library/set-vocabulary"
    ;; INTERSECTION-OF(c), the intersection of the members of a family c: a DEFINED constructor
    ;; ({x in BIG-UNION(c) | forall u in c. x in u}; the empty family gives EMPTY-SET), no binder and no kernel
    ;; rule.  2026-09-20, decision of the user; it replaces the uninterpreted head BIG-INTERSECTION that HAS-FIP
    ;; and compact-iff-fip (compactness.scm) had been written with.  Laws: theorem-library/intersection-of-laws.
    "structure-library/intersection-of"
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
    ;; CONS and the generation principle for TUPLES -- the recursive
    ;; characterization of LENGTH that theory.scm:637 recorded as pending.
    ;; Placed here, not with the other foundations: its axioms mention succ,
    ;; NN and <=, so it must follow number-systems, which registers them.
    "structure-library/list-recursion"
    ;; SQN(a) = FUN(NN, a) -- "the sequences in a", the infinite counterpart of
    ;; TUPLES(a).  A notation with a membership IFF beside it, because a
    ;; `def-functoid' installs only a rewrite macete and `mac-h' cannot unfold
    ;; one in an ASSUMPTION, which is how every sequence hypothesis is read.
    ;; Needs only FUN and NN (base theory); placed beside list-recursion, whose
    ;; TUPLES(a) it is the companion of.
    ;;
    ;; The file is `sqn.scm' and NOT `sequences.scm', which is taken:
    ;; structure-library/sequences.scm (line 311 below) is PROD-ORD / SUM /
    ;; SUM-AG, the finite products and sums over initial NN-segments.  Naming
    ;; this one `sequences.scm' overwrote that file on 2026-08-20 and took the
    ;; whole finite-sum family down with it -- sum-ag-*, sum-set-*, prod-ord-*,
    ;; prod-set-*, ring-prod-n-*, and with them sum-expansion and
    ;; binomial-theorem, which fail to install and say only "proof is not
    ;; complete".  Nothing else reports it: no load error, no gate.
    "structure-library/sqn"
    ;; ZZ is GENERATED by NN (every integer is n or -n).  number-systems.scm
    ;; axiomatizes ZZ as a commutative ring containing NN -- of which QQ is a
    ;; model, so `2k /= 1' and the parity dichotomy are FALSE in a model of the
    ;; theory without this.  Asserted, warranted `reference'; parity is proved
    ;; from it in theorem-library/parity.
    "structure-library/zz-arith"
    "structure-library/order-predicates"
    ;; NN-MINUS (monus), an explicit definition over number-systems.  HOISTED here
    ;; 2026-09-20 (batch 12-A) out of theorem-library/finsum-additive (~459), which is
    ;; BELOW structure-library/mat-equiv (~412) -- a file that states its recursion with
    ;; the head.  Definition only.
    "structure-library/nn-minus"
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
    ;; The metric induced by the norm: NVS-METRIC-SPACE(m) = [VEC(m), (x,y) |-> ||x (-) y||].
    ;; HOISTED 2026-09-20 (batch 12-A) out of theorem-library/vector-taylor-proof, where the
    ;; def-functoid sat inside a proof file and kept every theorem stated with it -- the four
    ;; metric laws of a normed vector space among them -- from loading above it.  Vocabulary only.
    "structure-library/nvs-metric"
    ;; Bounded linear functionals + dual norm on a normed vector space
    ;; (vocabulary): IS-LINEAR-FUNCTIONAL, IS-BOUNDED-LINEAR-FUNCTIONAL,
    ;; DUAL-NORM (IOTA least-upper-bound).  Loads after normed-vector-space.
    "structure-library/linear-functional"
    ;; THE DUAL as an OBJECT: DUAL-VEC(m) (the bounded functionals) and the
    ;; NORMED-VECTOR-SPACE 7-tuple DUAL(m) over it, with DUAL-NORM in the norm
    ;; slot.  Vocabulary only; reuses linear-functional.scm's predicates rather
    ;; than restating them.  Loads after linear-functional (DUAL-NORM) and
    ;; normed-vector-space (the 7-slot shape).
    "structure-library/dual-space"
    "structure-library/complex"
    ;; REDUCE + FAM-OF-LIST: kiddie n-ary <-> adult finite-fold bridge.
    ;; Consumed by numeric-instances (nary-plus-N-list axioms) and by
    ;; sequences (sum-ag-as-reduce); kernel-only deps (LIST/NTH/LENGTH/NN).
    "structure-library/reduce"
    "structure-library/numeric-instances"
    ;; 2026-09-20 (batch 12): SUBSPACE-MS / RESTRICT, and IS-DIFF-ON / DERIV-ON / HOLOMORPHIC-ON
    ;; (the derivative over a normed field on an OPEN set; docs/diff-on-open-sets-2026-09-20.md).
    "structure-library/metric-subspace"
    "structure-library/diff-on"
    ;; ---- THE CALCULUS VOCABULARY (hoisted 2026-09-20, batch 12-A) ----------------
    ;; Three definition files that used to sit inside proof files far below, each one
    ;; STATED in theorems of many other files.  They need only IS-CONTINUOUS-AT
    ;; (metric-continuity), RR-MS (numeric-instances) and the RR order, all above.
    ;; CCINT(a,b) = the closed interval, a SEP over RR (was theorem-library/extreme-value,
    ;; load position ~406 of 546; 43 files are stated with it).
    "structure-library/extreme-value"
    ;; IS-DIFF-AT (the Caratheodory derivative) and DERIV (was
    ;; theorem-library/differentiation:37, ~358; 34 files are stated with them).  The four
    ;; PROOFS of differentiation.scm stay where they are.
    "structure-library/derivative"
    ;; 2026-09-21 (batch 14-A): CC-COORDS, CC-OF-PAIR, IS-CC-DIFF-AT (docs/paths-and-line-integrals-2026-09-21.md, 3.1).
    "structure-library/cc-coords"
    ;; IS-ANTIDERIVATIVE / IS-ANTIDERIVABLE, Def 4.6 (was theorem-library/antiderivative:116,
    ;; ~514 of 546, which jammed all twelve files stated with them into the last thirty slots).
    ;; The eleven PROOFS of antiderivative.scm stay where they are.
    "structure-library/antiderivative"
    ;; COMPLEX-INNER-PRODUCT-SPACE: slots 1-6 are MODULE's (one name, one slot),
    ;; slot 7 the sesquilinear form IP : VEC x VEC -> CC; scalars pinned to CC
    ;; THROUGH the ring view of CC-NORMED-FIELD.  Plus the induced norm IP-NORM
    ;; and the NORMED-AG it builds.  Needs module + views
    ;; (NORMED-FIELD-AS-COMMUTATIVE-RING) + numeric-instances (CC-NORMED-FIELD)
    ;; + normed-ag + real-powers (SQRT).
    "structure-library/complex-inner-product"
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
    ;; The TRUNCATED metric d'(x,y) = min(1, d(x,y)) of a metric space, as an
    ;; ENDOFUNCTOR of METRIC-SPACE (def-constructed-functor: the distance is
    ;; BUILT from DIST, so no accessor correspondence expresses it).  Asserts
    ;; nothing; its typing obligation is discharged in
    ;; theorem-library/trunc-metric-proof.scm, where d and d' are also proven
    ;; UNIFORMLY equivalent -- which is what min(1,.) buys over BDD-METRIC's
    ;; merely topological claim.  Needs metric-space (PTS/DIST) and `min'.
    "structure-library/trunc-metric"
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
    ;; RR-POS-STAR = [0,+inf]: nonnegative extended reals, order-complete via ESUP.
    ;; Needs extended-reals (RR-STAR, POS-INF) + set primitives (SUBSET).
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
    ;; MOVED to structure-library/ 2026-09-20 (batch 12-A): vocabulary only -- no proof in it.
    "structure-library/block-family-combinatorial"
    ;; MOVED to structure-library/ 2026-09-20 (batch 12-A): vocabulary only -- no proof in it.
    "structure-library/subsequence-capture"
    ;; Totally bounded => every sequence has a Cauchy subsequence.  Assembles
    ;; pigeonhole + diagonalization + ball-2r-triangle; supplies the SUBSEQ /
    ;; STRICTLY-MONO-NN / IS-SUBSEQUENCE vocabulary.  Needs TOTALLY-BOUNDED/BALL
    ;; (metric-topology), IS-CAUCHY-SEQ (metric-completeness), INF-SUBSETS.
    ;; MOVED to structure-library/ 2026-09-20 (batch 12-A): vocabulary only -- no proof in it.
    "structure-library/cauchy-subsequence"
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
    ;; theorem-library/sum-set-left-scalar and -right-scalar (two support-only files) RETIRED
    ;; 2026-09-18 to archive/retired-2026-09-18/: both proven in theorem-library/rake-sum-set-scalar.
    "theorem-library/finsum-fubini"
    "structure-library/matrix"
    ;; 2026-09-25 (batch 32, the user's decision): TRANSPOSE(A, m, n), defined by its entries (d_ij = a_ji);
    ;; the matrix transpose only -- the adjoint of Hilbert-space operators is defined invariantly, later, elsewhere.
    "structure-library/transpose"
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
    "theorem-library/ord-segment-zero-no-members"
    "theorem-library/ord-segment-trans"
    "theorem-library/ord-segment-self"
    "theorem-library/fin-enum-is-bijection"
    "theorem-library/finsum-well-defined"
    "theorem-library/union-empty-left"
    "theorem-library/finsum-empty"
    "theorem-library/finsum-singleton"
    ;; Finite sums over a commutative monoid (closure / permutation-invariance
    ;; / enumeration-independence): the IS-COMM-MONOID generalizations of the
    ;; abelian-group finsum lemmas, reusing the same FINSUM functoid.  Needed
    ;; for the unordered RR-POS-STAR sum (RR-POS-STAR-ADD-MONOID has no inverses).
    "theorem-library/finsum-comm-monoid"
    ;; Product-of-sums expansion (warranted PSS tower): set-difference axioms,
    ;; powerset finiteness + insert-split, the finite-product recurrence
    ;; (finsum-insert) and PROD-RING's laws, capped by prod-of-sums-expansion.
    ;; Needs finprod, injection (IMAGE), cardinality, comm-monoid view.
    ;; MOVED to structure-library/ 2026-09-20 (batch 12-A): vocabulary only -- no proof in it.
    "structure-library/prod-of-sums"
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
    ;; MOVED to structure-library/ 2026-09-20 (batch 12-A): vocabulary only -- no proof in it.
    "structure-library/binomial"
    ;; ESUM: the unordered RR-POS-STAR sum = sup of finite partial sums over RR-POS-STAR-
    ;; ADD-MONOID.  Every RR-POS-STAR-valued f is summable; value is +inf unless the
    ;; partial sums are bounded by a real.  Needs finsum-comm-monoid + RR-POS-STAR.
    ;; MOVED to structure-library/ 2026-09-20 (batch 12-A): vocabulary only -- no proof in it.
    "structure-library/extended-sum"
    ;; ---- the measure-theory arc (Lebesgue via Caratheodory) ----
    ;; The rest of the [0,+inf] arithmetic and order vocabulary: etimes (with
    ;; the 0 * inf = 0 convention), EINF, ETAIL, ELIMINF/ELIMSUP and
    ;; ECONVERGES-TO.  Belongs beside extended-reals-pos conceptually; loaded
    ;; here because ETAIL is built from IMAGE (injection.scm, which loads after
    ;; extended-reals-pos) and because only the measure files consume it.
    "structure-library/extended-arith"
    ;; Outer measures, Caratheodory measurability and measures:
    ;; IS-OUTER-MEASURE / IS-CARATHEODORY-MEASURABLE / CARATHEODORY-SETS /
    ;; IS-MEASURE / IS-MEASURABLE-MAP / SIGMA-GENERATED, plus the Caratheodory
    ;; theorem and the elementary properties of a measure as warranted
    ;; supports.  Needs sigma-algebra (IS-SIGMA-ALGEBRA), extended-arith
    ;; (EINF), extended-sum (ESUM) and prod-of-sums (DIFFERENCE).
    "structure-library/measure"
    ;; MEASURABLE-SPACE (the pair (X,A), notes Def. 1.7) and MEASURE-SPACE (the
    ;; triple (X,A,mu), Def. 1.16) as declared STRUCTURES, per the standing rule
    ;; that a mathematical structure must be a structure in VNB rather than the
    ;; argument list of a predicate.  An ADDITION, not a migration: each law
    ;; clause CITES the existing predicate, so IS-SIGMA-ALGEBRA(PTS(s),SIGMA(s))
    ;; is a literal conjunct and every definition and support in measure.scm
    ;; applies verbatim at (PTS m, SIGMA m, MEAS m) with nothing to rewrite.
    ;; Needs measure (IS-MEASURE) and sigma-algebra (IS-SIGMA-ALGEBRA) above.
    "structure-library/measurable-space"
    ;; Measurable and simple functions, the [0,+inf]-valued INTEGRAL
    ;; characterised by Thayer's Thm. 2.7, and monotone convergence / Fatou /
    ;; dominated convergence.  Needs measure + extended-arith + cardinality
    ;; (CARD) + injection (IMAGE).
    "structure-library/integral"
    ;; Unconditional summability of a normed-AG-valued function (SUMS-TO,
    ;; IS-SUMMABLE, sums-to-unique).  Needs FINSUM + the NORMED-AG view.
    ;; MOVED to structure-library/ 2026-09-20 (batch 12-A): vocabulary only -- no proof in it.
    "structure-library/summability"
    ;; Real power series  Sum coef(n) x^n  (PS-PARTIAL-SUM via SUM-AG over
    ;; RR's additive group; PS-CONVERGES-(TO-)AT via CONVERGES on RR-MS).
    ;; Needs sequences (SUM-AG), views (NORMED-FIELD-ADDITIVE-AG), numeric-
    ;; instances (RR-NORMED-FIELD/RR-MS), number-systems (power), metric-completeness.
    ;; MOVED to structure-library/ 2026-09-20 (batch 12-A): vocabulary only -- no proof in it.
    "structure-library/power-series"
    ;; HISTORY ONLY since 2026-08-22: every entry it once held has been proven
    ;; and moved (monotone-convergence-proof, comparison-test-proof,
    ;; series-cauchy-proof); what is left is the record of where each went.
    ;; Installs nothing.  Needs power-series.
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
    ;; C-METRIC-SPACE: a set carrying a COUNTABLE FAMILY OF PSEUDOMETRICS that
    ;; separates points, and the CANONICAL METRIC it induces,
    ;;     D(a,b) = SUM_k 2^-(k+1) min(1, d_k(a,b)).
    ;; The declared-structure form of what pseudometric.scm can only say as the
    ;; argument list IS-COUNTABLE-PSEUDOMETRIC-FAMILY(fam, ground); the sum metric
    ;; is the construction metrizable-iff-gauge-countable's warrant DESCRIBES and
    ;; nothing in the tree had built.  Needs product-metric (SUMMABLE-WEIGHT),
    ;; power-series (SERIES-CONVERGES-TO), pseudometric (PSEUDOMETRIC-SPACE) and
    ;; number-systems (min).
    "structure-library/c-metric-space"
    ;; Countable Tychonoff for compact metric spaces (a countable product of
    ;; compact metric spaces is compact), via sequential compactness + the
    ;; coordinate diagonalization keystone.  Needs product-metric (PRODUCT-METRIC
    ;; + product-convergence-coordinatewise), compactness (IS-COMPACT),
    ;; cauchy-subsequence (STRICTLY-MONO-NN/SUBSEQ), metric-completeness
    ;; (CONVERGES-TO).
    ;; MOVED to structure-library/ 2026-09-20 (batch 12-A): vocabulary only -- no proof in it.
    "structure-library/seq-compact-product"
    ;; Retroactive warrants for founding PSS members admitted before warrants
    ;; were standard; loads after every result it warrants is installed.
    "theorem-library/founder-warrants"
    ;; Context and proof commands
    "contexts"
    "proof-commands"
    "interactive"
    ;; presentation -- THE RESOLUTION DIAL.  r0 kernel / r1 surface syntax (the
    ;; last invertible notch, where the round-trip gate lives) / r2 guards and
    ;; typings elided / r3 structures destructured and deep subterms elided,
    ;; plus the goal-driven auto-notch, which SUGGESTS a starting notch and then
    ;; stays put.  Changes nothing at r1: it installs *presentation-hook*
    ;; (sequents.scm), which returns #f there.  Loads after interactive because
    ;; `dial' calls `show'; after structures because r3 reads the slot names off
    ;; `lookup-structure'.
    "presentation"
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
    ;; certificates -- the proof-certificate store, the certified loader and the
    ;; switch VNB_CERTIFIED=on|off|strict (docs/certificates-2026-09-24.md).
    ;; Right after proof-debt (qed's record hook reads the ledger), before the
    ;; first contained proof file.
    "certificates"
    ;; extend-band -- `vnb-extend-band!', `retract-theorem!' and the band record
    ;; (docs/extend-band-2026-09-23.md).  After proof-debt (it reads the ledger),
    ;; before the first contained proof file: its position is the boundary before
    ;; which an extension refuses to reload anything.
    "extend-band"
    ;; minimize! -- "choose v with MEASURE(v) least".  A composite tactic over
    ;; the cmd-* layer (no kernel rule); its one mathematical appeal is
    ;; nn-least-element, resolved by NAME at call time, so it may load here,
    ;; long before theorem-library/nn-least-element.
    "minimize"
    ;; prop -- the propositional decision procedure.  Decides whether the focus
    ;; goal follows from the context by propositional logic, then DISCHARGES it
    ;; through the ordinary tactics (di/ai/oi/ass/pbc/use-em/have!/detach!), so
    ;; it adds no trust and no debt.  Needs interactive + driver-kit (use-em,
    ;; have!, dk-*), both directly above; nothing in the library depends on it,
    ;; so its position here is simply "with the other composite tactics".
    "prop"
    ;; (mp) -- close a goal that is an INSTANCE of a universal already in the
    ;; context, with no arguments: the term is DERIVED by matching the
    ;; universal's conclusion against the goal, and the guard is checked against
    ;; the context.  The syllogism.  Drives inst+ and ass, so it adds no rule
    ;; and no debt.  Needs interactive (inst+, ass) and prop's neighbours only.
    "mp"
    ;; (push-not-h k) -- push a NOT inward through one quantifier or implication
    ;; in an assumption, discharged through kernel rules so it adds no trust.
    ;; The move every "suppose it does NOT converge" argument opens with, and
    ;; the one VNB had no tactic for: `prop' treats a quantifier as an opaque
    ;; atom and `contra' is arithmetic.  Needs interactive + driver-kit (have!)
    ;; + prop.  Placed HERE, before the theorem library, deliberately: `contra'
    ;; sits at the far end of load.scm and no library proof can reach it.
    "push-not"
    ;; witness-tactics -- (obtain-at h t) instantiate-and-skolemize,
    ;; (use-at h t) the same where the conclusion is not an existential, and
    ;; (eps-part e k) "let h be e/k", and (choose ex w [prover]) "choose eps
    ;; such that FUBA(eps)" -- choose-pos is its pos-rr instance.  The moves an
    ;; eps-delta argument is made of, each of which was five hand steps with
    ;; four silent failure modes.  Composites over the ordinary tactics, so no new trust.  Needs
    ;; interactive + driver-kit (dk-have!, dk-split!, dk-landed); `eps-part'
    ;; cites rr-pos-halvable, which is proven far below, but only at CALL time.
    "witness-tactics"
    ;; counterexample -- (try-at t ...) / (try-small): PROBES that try to REFUTE the focus goal by
    ;; evaluating an instance (the user's notes-41, 2026-09-25: "attempting to prove falsehoods");
    ;; no inference, no recording; the what-now lane `counterexample' flags a dead path.
    "counterexample"
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
    ;; 2026-09-24 (batch 27-A follow-on): factorial-in-nn PROVEN by nn-induction (the axiom in injection.scm
    ;; retired); needs driver-kit for the induction helper, nothing cites it.
    "theorem-library/factorial-in-nn"
    ;; subseq-apply -- (SUBSEQ f phi)(k) == f(phi k) at a typed index, the VALUE equation that replaces
    ;; "unfold SUBSEQ under a binder, then lam-b" (CLAUDE.md).  One home since 2026-09-19 (it had been proven
    ;; three times, late).  SUBSEQ is defined in cauchy-subsequence, below the driver kit: this is the earliest slot.
    "theorem-library/subseq-apply"
    ;; rake-compose-typing -- the seven RAN/compose typing supports of
    ;; structure-library/compose-typing.scm, PROVEN 2026-09-17 (rake batch A).
    ;; Cites only base theory and injection.scm; sits here for the driver kit.
    "theorem-library/rake-compose-typing"
    "theorem-library/co-eq-lt-trans"
    ;; INTERVAL's read-offs, PROVEN by separation from its def-functoid:
    ;; interval-in-set (60 bills), interval-elt-in-nn, interval-lo, interval-hi,
    ;; plus the citable unfolding equation.  Were in order-lemmas / matrix.
    "theorem-library/interval-basics"
    "theorem-library/interval-mem-intro"
    "theorem-library/ord-segment-nn-succ-proof"
    "theorem-library/ord-segment-nn-subset-proof"
    "theorem-library/inf-subsets-is-set"
    "theorem-library/bdd-metric-carrier"
    ;; poly-membership -- SUPP / FINSUPP / POLY read-offs, PROVEN modulo 0 the
    ;; same way interval-basics and mat-basics prove theirs: the def-functoid
    ;; unfold as a citable `==', then mac-h it into the hypothesis and let the
    ;; kernel's sep-me read it apart.  A polynomial is always read OUT of a
    ;; context ("let f be a polynomial"), and until this file nothing could be
    ;; said about one -- mac-h cannot unfold a functoid.  Needs
    ;; structure-library/polynomial (SUPP/FINSUPP/POLY, :350), sqn
    ;; (sqn-membership, :144), numeric-instances (nn-add-monoid@carr, :250) and
    ;; driver-kit + prop, all above.
    "theorem-library/poly-membership"
    ;; normed-field-ring-view -- THE SCALAR BRIDGE, PROVEN modulo 0.  A normed
    ;; field is a 7-tuple and the ring predicates pin length 6, so a scalar slot
    ;; holds NORMED-FIELD-AS-COMMUTATIVE-RING(f) (views.scm:167) -- and
    ;; `def-functor' installs a functoid and a typing axiom, so until this file
    ;; NOTHING said what carr / add / mul / one OF that projection are.  Twelve
    ;; read-offs: six generic in the normed field, six at RR-NORMED-FIELD, each
    ;; the functoid unfold composed with an NTH projection.  Needs views +
    ;; numeric-instances (structure-library, far above) and interactive +
    ;; proof-debt; nothing in the library depends on it yet, so it sits with the
    ;; other def-functoid read-offs.
    "theorem-library/normed-field-ring-view"
    ;; The six RING-ADDITIVE-AG / MODULE-VECTOR-AG read-offs -- PROVEN modulo 0
    ;; (wave 6), RESTATED with an IS-RING / IS-MODULE guard.  The unguarded `='
    ;; supports they retire were UNPROVABLE: after the slot projection `rfl' owed
    ;; definedness of (NTH k A) for an arbitrary tuple.  The guard supplies it
    ;; through the IS-X typing conjunct, which is definitional and so free.
    ;; Cites no theorem-library theorem; must load before lam-fun-bricks.
    "theorem-library/ag-view-read-offs"
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
    ;; 2026-09-22: image-subset-codomain PROVEN (was an unwarranted axiom in structure-library/injection.scm).
    "theorem-library/image-subset-codomain"
    ;; rake batch 6 (2026-09-19): RECURSIVE CHOICE ON NN PROVEN.  dc-on-nn-pred by DC-ITER (a parametric
    ;; def-by-nn-recursion with a CHOICE step), then dc-on-nn from it.  Window [after fun-apply-type-proof,
    ;; diagonalization).
    "theorem-library/rake-dc-on-nn"
    ;; compose-apply -- (COMPOSE f g)(x) = f(g(x)), PROVEN modulo 0.  Was a
    ;; `support' in structure-library/compose.scm claiming the `proof' warrant
    ;; tier with the derivation written out in its warrant TEXT and never run,
    ;; and the text was wrong where it counted: the beta guard (2026-08-03)
    ;; licenses `lam-b' only on the lambda's OWN domain, which for COMPOSE is
    ;; DOM(g), not the A of (IN x A).  The bridge is fun-codomain-iff +
    ;; dom-fun-membership, both base axioms, so the bill stays zero.  Needs
    ;; compose (COMPOSE) and fun-apply-type-proof (fun-apply-type-c, just
    ;; above) plus interactive/proof-debt and driver-kit; must precede its
    ;; earliest consumer, theorem-library/continuity-compose.
    "theorem-library/compose-apply-proof"
    ;; pair-tuple-sethood -- pair-in-cartesian and pair-tuple-is-set, PROVEN
    ;; modulo 0.  Nothing in the library concluded sethood of a TUPLE: TUPLES
    ;; has no membership IFF, so `list-sethood' wants `L in TUPLES(A)' as a
    ;; hypothesis and a literal pair cannot supply it.  The route goes through
    ;; CARTESIAN (`ci' carries no sethood guard on the components) and back via
    ;; membership-implies-sethood.  See structure-notes/tuples-rung.md.  Needs
    ;; only base axioms + driver-kit, so it sits with the other plumbing.
    "theorem-library/pair-tuple-sethood"
    ;; rake-setoid -- class-is-set, quotient-is-set, proj-in-fun, descend-in-fun,
    ;; descend2-in-fun (setoid.scm), vec-is-set and vspace-vec-is-set (were add-to-pss
    ;; inside hahn-banach-full-proof / noetherian-maximal-proof): PROVEN 2026-09-17
    ;; (rake batch F).  Window [166, 442): pair-in-cartesian above, those two files below.
    "theorem-library/rake-setoid"
    ;; nn-order-ord -- the elementary NN order block, PROVEN modulo 0 from the
    ;; ORDINAL shelf (primitive since 2026-07-27).  Seven `well-known' supports
    ;; left structure-library/order-lemmas.scm for it: nn-one-in, nn-zero-le,
    ;; nn-le-succ, nn-le-imp-neq-succ, nn-succ-mono, nn-one-le-succ and
    ;; nn-le-succ-cases.  None of them is derivable from NN's own base
    ;; (nn-zero-in, nn-succ-closed, nn-induction) -- NN = {0} with succ 0 = 0
    ;; models all three -- so the route is nn-subset-ord + ord-succ-nn +
    ;; ord-le-nn-compat and back.  Must precede nn-order-basics, which cites
    ;; nn-le-succ and is the earliest citation of anything in the block.
    "theorem-library/nn-order-ord"
    "theorem-library/nn-not-le-succ-le"
    ;; nn-order-basics -- nn-le-refl, nn-le-add-right (m <= m+n by induction on
    ;; n) and nn-pair-upper-bound, PROVEN.  The first and third were supports in
    ;; order-lemmas claiming the `proof' warrant tier with no machine proof.
    ;; Needs interactive + driver-kit (use-induction); must precede
    ;; theorem-library/nn-order-proof and coord-block-estimate-proof.
    "theorem-library/nn-order-basics"
    ;; MAT's read-offs, PROVEN the same way interval-basics proves INTERVAL's:
    ;; the unfolding equation as a citable `==', then subst the goal back into
    ;; the separation.  `mat-rows-in-nn' is step one of defining CARD -- guarding
    ;; interval-card-in-nn needs the matrix dimensions typed NN, and the theorem
    ;; statements that cite it do not type them.
    ;; Moved here from after bdd-metric-carrier on 2026-09-16: the zero-row
    ;; lemmas (nil-in-mat) cite nn-in-rr and rr-le-trans, proven just above.
    ;; Nothing between the old and the new position cites mat-basics.
    "theorem-library/mat-basics"
    ;; nn-pos-of-nonzero -- PROVEN (wave 6), retiring the order-lemmas support.
    ;; Window: after nn-order-ord (nn-zero-le), before nn-integral.
    "theorem-library/nn-pos-of-nonzero"
    ;; interval-membership + one-in-interval-1 -- PROVEN (wave 6).  Needs
    ;; interval-mem-intro and nn-le-refl, both above; cited from matact-row-linear.
    "theorem-library/interval-membership"
    "theorem-library/nn-not-lt-le-proof"
    "theorem-library/entry-in-carrier"
    "theorem-library/bt-shims"
    ;; rr-order-basics -- the elementary RR order facts, PROVEN modulo 0.  Ten
    ;; were warranted supports in structure-library/order-lemmas.scm and three
    ;; more were declared with add-to-pss INSIDE calculus proof files
    ;; (rolle-proof, mvt-proof, taylor-proof); all thirteen are theorems here.
    ;; Eleven are one `ineq' call -- the oracle reads `<' natively and the
    ;; number-systems axioms behind it are primitive since 2026-08-01, so the
    ;; facts that were the oracle's SPECIFICATION are now its output.  Needs
    ;; order-predicates (`<'), the ineq oracle and driver-kit; must precede
    ;; rr-recip-order (rr-lt-trichotomy) and every calculus file below.
    "theorem-library/rr-order-basics"
    ;; The six calc-chain composition lemmas -- PROVEN modulo 0 (wave 7).  The four
    ;; order compositions are now GUARDED on RR (unguarded they asserted transitivity
    ;; of a GLOBAL relation); the two eq- links are unchanged and need no guard.
    ;; Before calc and before ord-segment-arith, the earliest proof-file citer.
    "theorem-library/co-order-trans-guarded"
    "theorem-library/pos-rr-bridges"
    ;; rr-abs-basics -- absolute value, PROVEN from its DEFINITION.  Until
    ;; 2026-08-17 number-systems.scm characterised `abs' by five norm-shaped
    ;; axioms (closed / nonneg / zero-iff / triangle / multiplicative) which do
    ;; not determine it -- x |-> sqrt(|x|) satisfies all five -- so x <= |x| and
    ;; the two-sided bound were INDEPENDENT of the theory and stood as asserted
    ;; supports in order-lemmas.scm.  That file now carries `rr-abs-def' (the
    ;; definition by cases on the sign), the five axioms are deleted, and all of
    ;; them plus the three supports are proven here `modulo 0'.  Needs
    ;; rr-order-basics (rr-lt-implies-le), binary-minus-laws (rr-sub-in-rr), the
    ;; ineq oracle and driver-kit; must precede every consumer of abs, the
    ;; earliest being rr-metric-space-proof.
    "theorem-library/rr-abs-basics"
    ;; MAX on RR: the usable facts (closure, "max is one of the two", the two
    ;; bounds, and the least-upper-bound property), all PROVEN from the single
    ;; defining equation rr-max-def in number-systems.scm.  Stating any of them
    ;; as an axiom instead would repeat the abs mistake the note beside
    ;; rr-abs-def records.  The whole proof is excluded middle on the guard the
    ;; definition splits on.  Needs rr-order-basics, prop and ineq.
    "theorem-library/rr-max-basics"
    ;; MIN on RR, the mirror of the file above and proven the same way from the
    ;; single defining equation rr-min-def -- plus the NN closure of BOTH max
    ;; and min, which is why it comes after rr-max-basics and after
    ;; nn-order-basics (nn-in-rr).  There is deliberately no NN-MAX operator:
    ;; NN is a subset of RR under the same order, so the RR operators take the
    ;; right values there and only closure is owed, one theorem each.  The
    ;; alternative -- a second head with its own laws -- is the per-system
    ;; proliferation the project has a standing rule against.
    "theorem-library/rr-min-basics"
    ;; cc-real-imag -- real-part / imag-part, DEFINED from conjugation and
    ;; proven real.  Both heads were registered (wff.scm) and advertised as
    ;; "CC -> RR" (interactive.scm) with no axiom whatever behind them, so a
    ;; symbolic real-part(z) was an uninterpreted application.  The definitions
    ;; are in number-systems.scm; this file proves the two typings and the
    ;; decomposition z = re(z) + i*im(z).  Needs the CC axioms, crs and
    ;; driver-kit.
    "theorem-library/cc-real-imag"
    ;; cc-magnitude MOVED 2026-08-17 to just after sqrt-defined (below): the
    ;; five SQRT facts it cites stopped being supports of real-powers.scm and
    ;; became theorems proved off the IVT, which lands them a thousand lines
    ;; further down the list.  Nothing between here and there cites a
    ;; cc-magnitude-* theorem, so the move is free.
    ;; rr-recip-order -- the L1 rung of the loose-ends ladder: a * 0 = 0,
    ;; 0 < 1, the product of positives is positive, and the one everything
    ;; analytic waits on, 0 < a => 0 < recip a.  Needs order-predicates (`<'),
    ;; order-lemmas (the rr-lt-* family), the ineq oracle and driver-kit.
    "theorem-library/rr-recip-order"
    ;; pos-rr-of-lt -- 0 < x IMPLIES POS-RR(x), the bridge the tree did not have:
    ;; `nn-recip-succ-pos' was the ONLY theorem in the library whose conclusion
    ;; was a POS-RR at all, and it was asserted.  Proving the general fact makes
    ;; that instance four lines, and it is retired from order-predicates here.
    ;; Its warrant had said "not mechanised: it needs recip-order lemmas the
    ;; tree does not have yet" -- rr-recip-order, immediately above, is them.
    ;; Must PRECEDE compact-separable-proof, the earliest citer.
    "theorem-library/pos-rr-of-lt"
    ;; rr-halving -- rr-pos-halvable, PROVEN modulo 0: every positive real is
    ;; d + d for a positive d, witness eps * recip(1+1).  Retires the
    ;; `well-known' support that stood in structure-library/order-predicates.
    ;; Needs rr-recip-order (rr-mul-pos, rr-recip-pos) immediately above,
    ;; rr-order-basics (rr-pos-ne-zero) and equality-basics (neq-sym); must
    ;; precede its citers, cauchy-subseq-proof and rr-complete-proof.
    "theorem-library/rr-halving"
    "theorem-library/rr-order-bundle"
    ;; rr-le-all-pos -- rr-le-all-pos-nonpos, PROVEN modulo 0: a real that is
    ;; <= every positive real is <= 0.  Retires the `well-known' support that
    ;; stood in structure-library/order-predicates, and it was the SOLE asserted
    ;; leaf of 20 bills.  Needs rr-halving (rr-pos-halvable) immediately above,
    ;; equality-basics (neq-sym), `prop' and the ineq oracle; must precede its
    ;; citers, the earliest being dominated-convergence.
    "theorem-library/rr-le-all-pos"
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
    ;;; =====================================================================
    ;;; THE CARD BLOCK (2026-09-20, batch 9-B: CARD := CARD-STAR).
    ;;; CARD is DEFINED in structure-library/cardinality.scm (the least ordinal whose
    ;;; segment the set bijects onto) and the eight facts that were `primitive' axioms
    ;;; -- seven there and card-image-injection in injection.scm -- are THEOREMS.  Their
    ;;; proofs are the nineteen files below, which used to be scattered between
    ;;; positions 192 and 337 and had to come above the axioms' earliest citers.  The
    ;;; whole block is CARD-free until theorem-library/card-laws.scm; the analysis (the
    ;;; citation cone, the three files that had to be split, the floors) is
    ;;; docs/card-defined-2026-09-20.md.  It cannot go higher than here: it uses
    ;;; `obtain' (sketch) and `vlet', immediately above.
    ;; The four inclusion facts, PROVEN rather than asserted: subset-mem-fwd /
    ;; subset-mem / subset-trans off subset-def, and subclass-of-set-is-set off
    ;; class-extensionality + separation.
    "theorem-library/subset-lemmas"
    ;; rake-analysis2 -- fun-domain-in-set, bijection-compose (was an informal axiom),
    ;; subseq-is-fun, metric-hom-is-continuous, le-bound-mono, centre-set-contains-choice.
    "theorem-library/rake-analysis2"
    ;; rake-inverse-bij -- the four INVERSE-BIJ axioms of bijection.scm (were unwarranted)
    ;; and ord-segment-self.  fin-enum-is-bijection was SPLIT OFF (it rests on
    ;; card-finite-bij) into theorem-library/rake-fin-enum, below the CARD laws.
    "theorem-library/rake-inverse-bij"
    ;; Parity on NN, the predecessor PRED (an IOTA), the segment/arithmetic bridges and
    ;; the finite-surgery kit (COLLAPSE-AT) -- everything finite pigeonhole needs.
    "theorem-library/nn-parity-proof"
    "theorem-library/nn-pred"
    "theorem-library/ord-segment-arith"
    "theorem-library/finite-surgery"
    ;; pigeonhole-segments -- finite pigeonhole, the theorem the DEFINITION of CARD needs.
    "theorem-library/pigeonhole-segments"
    ;; enum-append-is-bijection ("EXTEND-BY"), split out of theorem-library/finsum-insert,
    ;; which rests on the CARD laws and so stays below them.
    "theorem-library/enum-append"
    ;; union-empty-right / union-assoc, split out of theorem-library/fin-subsets for the
    ;; same reason.  Two unguarded set identities; they mention no CARD.
    "theorem-library/union-laws"
    ;; The three BIJECTION projection lemmas (in-fun / injective / surjective), PROVEN
    ;; modulo 0 from bijection-membership-iff, and bijection-identity.
    "structure-library/bijection-derived"
    "theorem-library/bijection-identity-proof"
    ;; card-defined -- the uniqueness of the description and card-segment, PROVEN from
    ;; finite pigeonhole; card-finite -- card-from-body, card-bij, card-empty.
    "theorem-library/card-defined"
    "theorem-library/card-finite"
    ;; Zermelo L1: no SET receives an injective class function from ORD; ZEN, the
    ;; choice-enumeration of a set, and its exhaustion; zermelo-bijection; then
    ;; card-zermelo and well-ordering-principle.
    "theorem-library/ord-no-injection"
    "theorem-library/zen-step"
    "theorem-library/rake-zermelo"
    "theorem-library/rake-ord-pigeonhole"
    ;; The finite CARD laws: card-insert-curried, card-union-disjoint-curried,
    ;; finite-set-induction, card-image-injection-curried and the peel under them.
    "theorem-library/rake-card-star-laws"
    ;; card-laws -- the five former axioms whose counterpart has a different SHAPE
    ;; (card-in-ord, card-insert, card-finite-bij, card-union-disjoint,
    ;; card-image-injection), restated character for character as the axioms stood so
    ;; that no citer changes.  After this file nothing about CARD is asserted.
    "theorem-library/card-laws"
    ;; The two halves that had to wait for the CARD laws.
    "theorem-library/card-singleton-proof"
    "theorem-library/rake-fin-enum"
    ;;; ===================== end of the CARD block =========================
    ;; difference-laws -- difference-membership / difference-set, PROVEN.  They
    ;; were asserted supports in prod-of-sums (395), and were the ENTIRE residue
    ;; of four bills.  DIFFERENCE is now a def-functoid for COMPLEMENT-IN, whose
    ;; two laws are kernel axioms, so each proof is an unfold and a citation.
    ;; Here and not in prod-of-sums because `sp'/`qed' need interactive (485).
    "theorem-library/difference-laws"
    ;; The laws of INTERSECTION-OF (unfold, membership, subset of each member, the empty family, sethood,
    ;; antitonicity) and De Morgan for COMPLEMENT-IN over BIG-UNION and INTERSECTION-OF.  All modulo 0.
    ;; Floor: subset-lemmas (which the CARD surgery of 2026-09-20 moved up into the block after transport).
    "theorem-library/intersection-of-laws"
    ;; complement-in-double (Y \ (Y \ A) = A for A subset Y; rake-open-sets carries a private copy) and
    ;; family-of-subsets-is-set.  2026-09-20, batch 11-E.  Floor: subset-lemmas.
    "theorem-library/rake-complement-laws"
    ;; rake batch 6 (2026-09-19): fun-codomain-superset (FUN codomain widening, from fun-codomain-iff);
    ;; rr-prod-pos (= rr-mul-pos) and rr-lt-from-diff-pos.  rake-rr-order-leaves needs rr-recip-order (above).
    "theorem-library/rake-fun-codomain"
    "theorem-library/rake-rr-order-leaves"
    ;; rake batch 5c (2026-09-18): RR-POS-STAR carrier facts; EPLUS and ETIMES DEFINED, their laws proven.
    ;; Window ends at rake-extended-order, which cites eplus-real-defined.
    ;; The five derivable infinity axioms of extended-reals.scm, proven (2026-09-19).
    ;; Window [142, rake-rr-pos-star): lo is `prop', hi cites pos-inf-neq-neg-inf.
    "theorem-library/rake-infinity-points"
    "theorem-library/rake-rr-pos-star"
    "theorem-library/rake-eplus-defined"
    "theorem-library/rake-etimes-defined"
    "theorem-library/rr-sup-approx"
    "theorem-library/nn-unbounded-in-rr"
    "theorem-library/nn-recip-succ-small"
    ;; discrete-space -- DISCRETE-SPACE(a) = (a, POWER(a)), the first witness of
    ;; MEASURABLE-SPACE and the first OUTRIGHT inhabitant of TOP-SPACE.  One
    ;; tuple, two structures: both have carrier PTS at slot 1 and a `constant'
    ;; slot typed into POWER(POWER(PTS)) at slot 2, so the OPENS and SIGMA
    ;; accessor macetes reduce to the same (NTH 2 s).  Carries the power-set
    ;; lemma family it needed -- the tree had NO theorem about POWER before it,
    ;; only the two base axioms -- plus a named `subset-refl'.  Loads here for
    ;; subclass-of-set-is-set, one line above; everything else it cites
    ;; (top-space, measurable-space, sigma-algebra, nn-is-set, prop) is earlier.
    "theorem-library/discrete-space"
    ;; rake batch 5 (2026-09-18): sigma-algebra / measurable-map projections, window [199, end)
    "theorem-library/rake-measure"
    ;; rake batch 5b (2026-09-18): measurable-fn-indicator + the set-level sigma-algebra bricks
    "theorem-library/rake-measure2"
    ;; The trivial subtype-subsumption laws ("every X is a Y"), PROVEN via
    ;; mac-h instead of asserted -- formerly phantom debt leaves.  Needs the
    ;; interactive tactics + qed/proof-debt, so loads here.
    "structure-library/subtype-laws"
    ;; op-typing -- the codomain typing of a structure operation in APPLIED
    ;; form, PROVEN modulo 0, seven at once from one driver: ring-add-closed,
    ;; ring-carrier-closed-mul, ring-neg-in-carr, bt-add-in-carr,
    ;; metric-dist-real, vnrm-real, nvs-vadd-in-vec.  Retires seven supports
    ;; whose warrants each recited the same derivation (IS-X unfold + the FUN
    ;; conjunct + apply-tupling).  Needs fun-apply-type-proof (fun-apply-type-c)
    ;; and pair-tuple-sethood (pair-in-cartesian), and subtype-laws
    ;; (commutative-ring-is-ring, which bt-add-in-carr descends through) -- the
    ;; last of these is why the file sits here and not beside pair-tuple-sethood.
    ;; Must precede the earliest citer, compact-separable-proof.
    "theorem-library/op-typing"
    ;; sum-ag-type (an axiom with NO warrant), enum-fam-in-fun, finsum-type and
    ;; finsum-all-id -- all PROVEN modulo 0 (wave 6).  MUST load BEFORE cancellation:
    ;; that file runs the unrestricted (view-as-auto-specialize! RING-ADDITIVE-AG),
    ;; which is what mints finsum-type-ring-additive-ag, cited by name in
    ;; mat-typing-bundle.  Installed after that call, the companion is never built.
    "theorem-library/finsum-type-proof"
    ;; finsum-single-support -- PROVEN 2026-09-17 (was a well-known support in
    ;; structure-library/matrix.scm, the sole leaf of ten bills).  Window [199, 286):
    ;; cites sum-ag-all-id-ind (finsum-type-proof, just above); the earliest citer
    ;; is finsum-fiber.
    "theorem-library/finsum-single-support"
    ;; integral-domain-cancel-zero, PROVEN by unfolding is-integral-domain-def
    ;; (the no-zero-divisor conjunct, instantiated and OR-eliminated against
    ;; b /= 0).  The file was WRITTEN and never wired in -- it sat on disk,
    ;; unloaded and therefore unrun, while integral-domain.scm went on asserting
    ;; the same fact unwarranted into seven bills; found 2026-08-10.  Same
    ;; position and the same reasons as subtype-laws above: needs the
    ;; interactive tactics + qed/proof-debt, and must precede its consumers
    ;; (nn-integral, submodule-free).
    "structure-library/integral-domain-laws"
    ;; IS-RING(ZZ-RING), PROVED -- formerly the asserted axiom `zz-is-ring', which
    ;; every theorem reaching the integers through their ring structure was billed
    ;; for.  Unfold the IFF, push the accessors to the surface (surface-goal!),
    ;; and the conjuncts are the arithmetic axioms.  Must load BEFORE cancellation
    ;; (which transports through it).  Needs transport + crs + numeric-instances.
    ;; The application read-offs for lambda-valued operation slots.  MUST come
    ;; before zz-ring-is-ring: surface-goal! uses them to take (ADD ZZ-RING)(u,v)
    ;; down to u + v, which is what `crs' needs to see for the ring laws.  They
    ;; replace the second half of the old two-step bridge, whose first half was
    ;; the shared constant `binplus' -- the inconsistency (numeric-instances.scm).
    "theorem-library/lambda-slot-apply"
    "theorem-library/zz-ring-is-ring"
    "theorem-library/rr-is-normed-field"
    ;; RR as a one-dimensional real normed vector space -- the FIRST witness of
    ;; NORMED-VECTOR-SPACE, which was satisfiable-but-unexemplified since the
    ;; 2026-08-23 repair.
    ;; MUST come after lambda-slot-apply, whose three read-offs are in
    ;; *surface-bridge-theorems* -- without them `surface-goal!' cannot take the
    ;; instance's accessors down to the surface, and it fails SILENTLY (the
    ;; driver wraps it in vnb-guard), leaving every goal still speaking of
    ;; scal(rr-nvs).  And after rr-abs-basics: the four norm laws are rr-abs-nonneg,
    ;; rr-abs-zero, rr-abs-mult and rr-abs-triangle, all proved there.  It also
    ;; needs normed-field-ring-view's scalar slot read-offs, which are earlier.
    "theorem-library/rr-nvs-exemplification"
    ;; IS-COMMUTATIVE-RING(ZZ-RING) and IS-INTEGRAL-DOMAIN(ZZ-RING), PROVED --
    ;; the storey above zz-ring-is-ring, and formerly two more asserted axioms of
    ;; numeric-instances.  The content is that ZZ has no zero divisors, which
    ;; nothing in number-systems states: it comes from QQ being a FIELD
    ;; (qq-recip-inverse) plus zz-subset-qq.  Needs zz-ring-is-ring above,
    ;; driver-kit (have!/use-em) and surface-goal!; must precede
    ;; theorem-library/nn-integral, which transports through it.
    "theorem-library/zz-integral-domain"
    ;; IS-COMM-MONOID(NN-ADD-MONOID), PROVED -- the last numeric-instance
    ;; assertion with a dependent.  Same shape as zz-ring-is-ring, except the
    ;; three law conjuncts are closed by CITING the NN axioms rather than by
    ;; `crs': NN is not a ring, and a commutative-ring oracle would have closed
    ;; them anyway.  Must precede theorem-library/poly-is-ring-proof.
    "theorem-library/nn-add-monoid"
    ;; Cancellation, proved ONCE in GROUP and then carried: -> ABELIAN-GROUP ->
    ;; [RING-ADDITIVE-AG view] -> RING -> [transport!] -> ZZ/QQ in the SURFACE
    ;; language -> NN by restriction.  The worked example of the transport chain,
    ;; and the retraction of an induction proof that never needed induction.
    ;; Needs subtype-laws (abelian-group-opr-comm), views, numeric-instances,
    ;; transport.
    "theorem-library/cancellation"
    "theorem-library/ring-zero-one-power"
    ;; theorem-library/rake-sum-set-scalar MOVED 2026-09-18 below rake-sum-set-defined: SUM-SET is
    ;; defined now and the scalar laws cite the PROVEN sum-set laws.
    ;; The NN arithmetic support layer: cancellation, no-zero-divisors, and the
    ;; order fact k<2k, all DERIVED (not asserted) from ZZ being an ordered
    ;; integral domain via NN<=ZZ -- the integral-domain law is TRANSPORTED to
    ;; the surface (zz-mul-cancel-zero), then restricted.  Retires the reference
    ;; assertions number-theory proofs kept re-making.  Needs transport,
    ;; zz-is-integral-domain, nn-subset-zz, order-lemmas.
    "theorem-library/nn-integral"
    ;; The six COMB-KK / binomial-transform laws -- PROVEN modulo 0 (wave 7),
    ;; reachable at last because COMB-KK is now ZZ-indexed (binomial.scm), which
    ;; is what its own header always said it was.  bt-succ-minus-1 is proved
    ;; GUARDED on (IN n NN): the ZZ form is NOT a theorem of this tree, since
    ;; `succ' has no characterisation off NN -- all three citers supply NN.
    ;; After nn-parity-proof (nn-succ-plus-one), before binomial-proof.
    "theorem-library/comb-kk-laws"
    ;; mod-3 arithmetic on NN, the mirror of nn-parity-proof: the trichotomy
    ;; (n = 3k / succ 3k / succ^2 3k), residue-exclusivity (3x /= succ 3y), and the
    ;; linchpin nn-3-div-square (3|p*p => 3|p) -- plus nn-3-cancel / nn-lt-triple.
    ;; Feeds sqrt3-proof.  Needs nn-parity-proof + nn-integral (nn-mul-cancel).
    "theorem-library/nn-mod3-proof"
    ;; nn-order-via-rr -- elementary NN order facts proven by taking the
    ;; contradiction in RR: nn-not-le-zero-pos (was the TOP of the
    ;; greedy what-if at TEN bills cleared.  Goes through RR: NN has no order
    ;; axioms beyond the succ family, and the obvious NN route is circular --
    ;; nn-order-proof just below proves nn-le-zero-is-zero BY CITING THIS.
    ;; Retires the support from order-lemmas.  Needs rr-order-basics
    ;; (rr-pos-ne-zero), rr-recip-order (rr-zero-lt-one), nn-order-basics
    ;; (nn-in-rr); `contra' would have done it in one line and loads 1600
    ;; entries too late.
    "theorem-library/nn-order-via-rr"
    ;; rake-intervals -- nn-succ-le-cancel, nn-minus-succ-1, one-in-interval, succ-not-one,
    ;; nn-minus-1-inj, and succ-in-interval / pred-in-interval GUARDED on the bound in NN:
    ;; PROVEN 2026-09-17 (rake batch K).  Window [220, 350): nn-order-via-rr above,
    ;; border-mult-proof below.
    "theorem-library/rake-intervals"
    ;; zz-order -- the integers' own order facts, PROVEN modulo 0 (2026-09-16):
    ;; abs(a) in NN, the sign cases, trichotomy, discreteness (0 < a => 1 <= a),
    ;; a < b => a + 1 <= b, 0 <= a => a in NN.  Everything ZZ number theory
    ;; (zz-division, gcd, Euclid) needs and RR's order does not give.  Needs
    ;; nn-parity-proof (nn-nonzero-is-succ), rr-abs-basics, rr-order-basics.
    "theorem-library/zz-order"
    ;; zz-division -- nn-division, zz-division and zz-is-euclidean-ring, PROVEN
    ;; 2026-09-17 modulo 0 (the axiom was structure-library/numeric-instances.scm's).
    ;; Window: after zz-order (zz-abs-in-nn, zz-abs-cases, zz-lt-succ-le), before
    ;; zz-bezout-proof, which cites zz-is-euclidean-ring.
    "theorem-library/zz-division"
    ;; zz-parity-proof -- EVEN/ODD on ZZ and their laws, nine theorems modulo 0.
    ;; On disk since 2026-07-15 and never in this list (the integral-domain-laws
    ;; species, CLAUDE.md); first loaded 2026-09-16.  Needs nn-parity-proof.
    "theorem-library/zz-parity-proof"
    ;; nn-pos-is-succ -- PROVEN (wave 6).  Needs nn-not-le-zero-pos, just above.
    "theorem-library/nn-pos-is-succ"
    ;; <= versus + on NN: a <= 0 => a = 0, a <= a+b, and additive monotonicity.
    ;; order-lemmas.scm relates <= to succ and never to +; the pairing is what
    ;; exposed the gap.  Own file, not the pairing file, so the next user can
    ;; find them.  Needs nn-parity-proof (nn-zero-or-succ).
    "theorem-library/nn-order-proof"
    ;; rake-algebra -- ring-carr-in-set, ideal-elt-in-carrier, principal-ideal-in-ideal,
    ;; diagonal-off-entry, ring-add-right-id (zz-bezout's last leaf), span-add-one-
    ;; membership, strictly-mono-ge-id: PROVEN 2026-09-17 (rake batch D).  Window
    ;; [215, 284): finite-surgery (nn-lt-succ-le) above, subseq-convergence-proof below.
    "theorem-library/rake-algebra"
    ;; rake-algebra2 -- abelian-group-assoc/-right-id/-inverse-unique, ring-add-right-inv,
    ;; ring-neg-neg, ring-neg-mul-left, and the four unwarranted axioms matrix-sethood,
    ;; monoid-identity-in, monoid-carrier-closed-opr, mpow-type: PROVEN 2026-09-17 (rake
    ;; batch I).  Window [226, 241): rake-algebra (ring-add-right-id) above,
    ;; rake-mat-typing (cites mpow-type) below.  Rebuilds the three cited view companions.
    "theorem-library/rake-algebra2"
    ;; rake batch 5c (2026-09-18): monoid-assoc / -left-id / -right-id as projections of IS-MONOID
    "theorem-library/rake-monoid-laws"
    ;; rake batch 6 (2026-09-19): ZZ-ACT DEFINED (zz-action.scm); its two equations, the five billed laws,
    ;; mpow-one, mpow-add and four abelian-group inverse laws proven.  Window [rake-monoid-laws, rake-finsum-core).
    "theorem-library/rake-zz-act"
    ;; rake batch 5b (2026-09-18): the ringoid additive group; ringoid-neg-diff, ringoid-diff-telescope.
    ;; Window [pair-tuple-sethood, ringoid-setoid-proof): the setoid proof cites the two.
    "theorem-library/rake-ringoid-additive"
    ;; rake-finsum-typing -- finsum-comm-monoid-type, prod-ring-type, ring-power-type,
    ;; submodule-finsum-closed, funcomp-succ-type (guarded q in NN): PROVEN 2026-09-17
    ;; (rake batch G).  Window (nn-order-proof, spans-transport-proof).
    "theorem-library/rake-finsum-typing"
    ;; rake-finsum-welldef -- sum-ag-permutation-invariance, finsum-well-defined and the
    ;; two comm-monoid twins: the FINSUM FLOOR, PROVEN 2026-09-17 modulo 0 (rake batch N,
    ;; part 2).  Window [230, 243): rake-finsum-typing above, rake-finsum-laws below.
    "theorem-library/rake-finsum-welldef"
    ;; finsum-insert -- MOVED here 2026-09-17 from position 155: it cites the two
    ;; well-definedness facts, proven just above; its ord-segment-self /
    ;; fin-enum-is-bijection / sum-ag-segment-congruence blocks are cut (proven above).
    "theorem-library/finsum-insert"
    ;; rake batch 5b (2026-09-18): order and eplus laws on RR-POS-STAR (pos-inf-above-reals), esum-finite-iff-bounded
    "theorem-library/rake-extended-order"
    ;; rake batch 6 (2026-09-19): ESUP DEFINED (extended-reals-pos.scm); esup-in/-upper/-least/-empty proven.
    "theorem-library/rake-esup-defined"
    ;; rake batch 6: IS-COMM-MONOID(RR-POS-STAR-ADD-MONOID) PROVEN (was asserted in extended-reals-pos).
    "theorem-library/rake-rr-pos-star-monoid"
    ;; Every field is a FIELD-RING -- the bridge that WITNESSES the predicate
    ;; VECTOR-SPACE's scalar law was rewritten to use on 2026-08-23.  Also
    ;; defines SINGLETON (it had no membership characterisation at all) and
    ;; proves the FIELD-AS-INTEGRAL-DOMAIN slot read-offs.
    ;;
    ;; MUST come after nn-order-proof (where nn-le-antisym is proved): singleton-membership's forward direction
    ;; needs nn-le-antisym to pin the index to 1.  Placed beside the other view
    ;; read-offs at first, where that theorem does not exist yet -- the band has
    ;; the whole library, so a probe against it cannot see a load-order error.
    "theorem-library/field-ring-view"
    ;; QQ as a one-dimensional vector space over itself -- the FIRST witness of
    ;; VECTOR-SPACE, and of MODULE directly rather than through a view.  After
    ;; field-ring-view (field-is-field-ring discharges the scalar law, and the
    ;; FIELD-AS-INTEGRAL-DOMAIN slot read-offs live there) and after
    ;; lambda-slot-apply, whose read-offs surface-goal! needs.
    ;; qq-field-is-field -- IS-FIELD(QQ-FIELD), PROVED, retiring the bare axiom
    ;; that stood in numeric-instances.scm.  It was the SOLE unwarranted leaf of
    ;; qq-line-is-module and qq-line-is-vector-space, so those read `trust: none'
    ;; for it alone.  Loads HERE and not earlier for two reasons: the proof needs
    ;; the interactive tactics, and its MUL-INV conjunct needs SINGLETON's
    ;; membership law, which field-ring-view (just above) is what builds.
    "theorem-library/qq-field-is-field"
    "theorem-library/qq-vs-exemplification"
    ;; Reading membership out of a literal brace set: {a,b} is sugar for
    ;; MAKE-SET(LIST a b), whose membership law is an existential over INDICES.
    ;; makeset2-membership turns it into a disjunction, once.  Needs
    ;; nn-order-proof (nn-le-antisym), just above.
    "theorem-library/makeset-basics"
    ;; The two BACKWARD rungs for "this set is empty, so its cardinal is 0":
    ;; card-empty-le (X = {} => card(X) <= 0) and makeset-of-empty-tuple
    ;; (L = [] => make-set(L) = {}).  Both one `subst' off card-empty /
    ;; make-set-empty, both `modulo 0'.  They exist because the backchain lane
    ;; had nothing to offer on a list-induction base case: no installed fact
    ;; concluded `card(_) <= 0' or `make-set(_) = EMPTY-SET'.  Needs
    ;; structure-library/cardinality (card-empty), loaded far above.
    "theorem-library/empty-cardinality"
    ;; List induction, DERIVED from the generation axioms of
    ;; structure-library/list-recursion by induction on the length -- so the
    ;; tree gets list induction without an asserted induction schema.  Class
    ;; form, like nn-induction and finite-set-induction.  Placed after
    ;; makeset-basics because it is what retires that file's per-arity ladder.
    "theorem-library/tuples-induction"
    "theorem-library/tuple-extensionality"
    ;; The LIST TABULATION primitive and what it builds: tuple-tabulation (for every
    ;; n and f there is a tuple whose i-th entry is f(i)), its row and matrix
    ;; versions, and then mat-tabulation-exists / matof-exists-image /
    ;; entry-of-matof-guarded -- the GUARDED forms of what matrix.scm asserts.
    ;; Nine theorems, all modulo 0 (wave 8).  matrix.scm has promised this file since
    ;; its header was written ("dischargeable via a general list-tabulation
    ;; primitive").  Tabulation PREPENDS, CONS being the only tuple constructor the
    ;; theory has, so every step shifts the index by one and the shift is carried in
    ;; the arithmetic (an explicit offset k) rather than in the function -- VNB has no
    ;; term-former for "f shifted by one" that beta-reduces under an applied variable,
    ;; and application is not curried.
    ;; After tuple-extensionality (entry-unfold, matrix-entry-extensionality).
    "theorem-library/tuple-tabulation"
    ;; rake batch 5b (2026-09-18): border-entry-block(2); window ends at border-mult-proof, which cites block2
    "theorem-library/rake-border-entry"
    ;; rake batch 6 (2026-09-19): border-entry-11/-1j/-i1, succ-nn-minus-1.  Window [after rake-border-entry, border-mult-proof).
    "theorem-library/rake-border-siblings"
    "theorem-library/matof-in-mat"
    ;; A tuple of length n has at most n distinct entries:
    ;; CARD(MAKE-SET(l)) <= LENGTH(l), by the same length-induction as
    ;; tuples-induction, strengthened to carry sethood and finiteness of the
    ;; entry set (neither is available from outside -- make-set-sethood wants
    ;; `a in SET' and the statement leaves `a' an arbitrary class).  Brings with
    ;; it union-comm, union-singleton-absorb and the insertion bound
    ;; card-union-singleton-bound, which the library had for a DISJOINT union
    ;; (card-union-disjoint) and for a FRESH element (card-insert) and for
    ;; neither of the two cases an entry set presents.  Needs
    ;; structure-library/list-recursion (makeset-cons, the generation axioms),
    ;; structure-library/cardinality (card-empty, card-insert),
    ;; order-lemmas (nn-le-succ, nn-succ-mono) and nn-order-basics
    ;; (nn-le-refl, nn-le-trans-guarded) -- all above.
    "theorem-library/makeset-card-bound"
    "theorem-library/card-subset-nn"
    "theorem-library/card-image-finite"
    "theorem-library/interval-card-in-nn"
    ;; rake-finsum-laws (two files; part 1 first, part 2 cites its bricks) --
    ;; finsum-congruence (== form; the = form was false), finsum-two-support, finsum-add-ag,
    ;; finsum-interval-peel, finsum-act-distrib-gen, finsum-ring-distrib-left/right-gen,
    ;; finsum-fubini-c: PROVEN 2026-09-17 (rake batch J).  Window [240, 296):
    ;; interval-card-in-nn above, finsum-fiber below.
    "theorem-library/rake-finsum-laws"
    "theorem-library/rake-finsum-laws2"
    ;; rake-finsum-core -- finsum-fubini, finsum-act-collect-gen, ord-segment-insert,
    ;; finsum-singleton, finsum-add, finsum-ring-distrib-left/-right, finsum-ord-peel,
    ;; finsum-ring-scalar-zz, comm-monoid-opr-comm: PROVEN 2026-09-17 (rake batch M).
    ;; Window [245, 370): rake-finsum-laws2 above, matact-assoc-proof below.
    "theorem-library/rake-finsum-core"
    ;; rake batch 5c (2026-09-18): finsum-comm-monoid-type-ptwise
    "theorem-library/rake-finsum-cm-ptwise"
    ;; rake batch 6 (2026-09-19): ESUM DEFINED (extended-sum.scm); esum-in/-upper/-least proven.  Needs
    ;; rake-esup-defined, rake-rr-pos-star-monoid and rake-finsum-cm-ptwise.  Then the finiteness dichotomy,
    ;; split out of rake-extended-order because it cites the three.
    "theorem-library/rake-esum-defined"
    "theorem-library/rake-esum-finite"
    ;; rake-finsum-fubini-c -- finsum-fubini-c, moved out of rake-finsum-laws (it cites
    ;; finsum-fubini, proven just above); before finsum-fiber.
    "theorem-library/rake-finsum-fubini-c"
    "theorem-library/mat-typing-bundle"
    ;; rake-mat-typing -- block/snoc-col/snoc-row/matadd/matscale/matneg-type, mat-is-set,
    ;; submat-type, border-type, minor-type, det-in-carrier: PROVEN 2026-09-17 (rake batch
    ;; E).  Window [239, 328): mat-typing-bundle (mat-colcount-transfer) above,
    ;; mat-ring-proof below.
    "theorem-library/rake-mat-typing"
    ;; rake batch 5b (2026-09-18): interval-1-1, det-1x1/2x2/identity, mat-ring-one; window ends at mat-ring-proof
    "theorem-library/rake-det-small"
    ;; rake batch 6 (2026-09-19): the seven remaining MAT-RING read-offs.  Window [rake-mat-typing, mat-ring-proof).
    "theorem-library/rake-mat-ring-readoffs"
    ;; matmul-entry -- the product's entry law, PROVEN modulo 0 (2026-09-16):
    ;; unfold MATMUL, read the dimensions off SIZE (mat-basics), entry-of-matof
    ;; (its definedness hypothesis is matmul-type's inner block), lam-b.  Was the
    ;; most-cited asserted leaf (44 bills).  Needs interval-card-in-nn.
    "theorem-library/matmul-entry-proof"
    ;; matunit-type and matact-type -- PROVEN (wave 6), down to the matof-in-mat
    ;; tuple-shelf residue.  After interval-card-in-nn and finsum-type-proof.
    "theorem-library/matunit-matact-type"
    "theorem-library/nn-finite-subset-bounded"
    ;; The two missing CARD inequalities -- card-subset-mono (A subset B and B
    ;; finite => CARD A <= CARD B) and card-union-bound (subadditivity,
    ;; CARD(A u B) <= CARD A + CARD B), the monotonicity and subadditivity laws
    ;; a CARD-normed monoid of finite sets needs.  Neither existed; the nearest
    ;; thing, card-subset-nn, states only that the subset is FINITE and its own
    ;; warrant says "bounded by the superset's" without stating the bound.
    ;; (Proved in 2026-08 for the then-axiomatised CARD; since 2026-09-20 CARD is
    ;; DEFINED and card-union-disjoint is a theorem, so the note that used to stand
    ;; here -- "blocked on the unbuilt EXTEND-BY" -- is spent.)  Four
    ;; set-algebra lemmas about COMPLEMENT-IN come with them, all modulo 0,
    ;; plus card-union-nn (the union of two finite sets is finite), which is NOT
    ;; a corollary of the bound -- `<=' does not put its left side in NN -- and
    ;; is what a monoid of finite sets needs to be closed under union at all.
    ;; Needs structure-library/cardinality (card-union-disjoint),
    ;; theorem-library/prod-of-sums (card-subset-nn), subset-lemmas
    ;; (subset-mem-fwd, subclass-of-set-is-set) and nn-order-proof (nn-le-add,
    ;; nn-add-le-mono) -- all above -- plus prop/driver-kit.
    "theorem-library/card-inequalities"
    ;; rake-combinatorics -- ring-power-one/-succ/-add/-mult, prod-ring-empty/-singleton/
    ;; -insert, choose-n-0, choose-0-succ, card-power-nn, power-insert-cover/-disjoint,
    ;; power-zero-base, union-empty-left, succ-nn-ord, ord-segment-trans, bt-mul-comm:
    ;; PROVEN 2026-09-17 (rake batch P).  Window [251, 375): card-inequalities
    ;; (card-union-nn) above, binomial-proof (ring-power-succ) below.
    "theorem-library/rake-combinatorics"
    ;; rake batch 5 (2026-09-18): interval-card, choose-in-nn, permutations-zero, pigeonhole-infinite
    "theorem-library/rake-combinatorics2"
    ;; rake batch 5b (2026-09-18): choose-succ (Pascal)
    "theorem-library/rake-choose-succ"
    "theorem-library/nn-infinite"
    ;; FIN-SUBSETS(a) = { t in POWER(a) : CARD(t) in NN }, the finite subsets,
    ;; with the set-algebra laws that make it a commutative monoid under union:
    ;; the membership characterisation, sethood of the carrier, union-assoc,
    ;; union-empty-right, {} in FIN-SUBSETS(a), and closure under union (the
    ;; one law that needs card-union-nn).  NOTE the membership law is PROVEN
    ;; modulo 0, not asserted `definitional' as the other SEP-bodied functoids'
    ;; are: `mac' unfolds a functoid on the GOAL side and the SEP layer is
    ;; reached by kernel rules, so the iff is a theorem rather than an axiom.
    ;; Needs card-inequalities (card-union-nn) immediately above, cardinality
    ;; (card-empty) and the POWER/SEP/UNION base axioms.
    "theorem-library/fin-subsets"
    ;; rake batch 5c (2026-09-18): finsum-union-disjoint, finsum-embed (window ends at finsum-fiber, which
    ;; cites finsum-embed); its comm-monoid mirror; SUM-SET defined as FINSUM and its laws; the scalar laws.
    "theorem-library/rake-finsum-union"
    "theorem-library/rake-finsum-cm-union"
    "theorem-library/rake-sum-set-defined"
    ;; PROD-SET DEFINED as FINSUM (finprod.scm); its four laws proven (2026-09-19).  Window [271, end).
    "theorem-library/rake-prod-set-defined"
    "theorem-library/rake-sum-set-scalar"
    ;; FIN-SUBSET-MONOID(a) = (FIN-SUBSETS(a), union, {}) and the theorem that
    ;; it IS a commutative monoid for a a set.  A parametric structure, so it is
    ;; a def-functoid over the slot LIST plus a guarded IS-X theorem, the
    ;; MAT-RING pattern (matrix.scm:296 / mat-ring-proof.scm:94) -- NOT
    ;; declare-instance!, which mints a constant and cannot carry the parameter.
    ;; The three slot read-offs are PROVEN here (accessor macete + nth-r +
    ;; qrfl), where MAT-RING's six are asserted `reference' supports.
    ;; Needs fin-subsets immediately above, monoid (COMM-MONOID),
    ;; operation-properties, and makeset-card-bound (union-comm).
    "theorem-library/fin-subset-monoid"
    ;; The Cantor pairing NN x NN -> NN (TRINUM by recursion, NNPAIR(i,j) =
    ;; TRINUM(i+j)+j) and its surjectivity, plus nn-succ-add (succ(a)+b) which
    ;; the base lacked.  The re-indexing mechanism that compact-metric-is-
    ;; separable, the Ascoli diagonal and countable unions are all blocked on.
    ;; Needs nn-parity-proof (nn-zero-or-succ) and ordinals (def-by-nn-recursion).
    "theorem-library/nn-pairing"
    ;; compact => totally bounded (calculus.pdf Prop 3.12, the (1)=>(4) half):
    ;; unfold IS-COMPACT in the hypothesis, instantiate it at the r-ball cover,
    ;; and backchain finite-ball-subcover-r-net.  Installs the theorem under the
    ;; name compact-implies-totally-bounded, which compactness.scm used to
    ;; ASSERT as a support -- the file had no load.scm entry, so the proof never
    ;; ran while the support went on billing.  Needs compactness (BALL-COVER,
    ;; the two ball-cover lemmas) + interactive/proof-debt.
    "theorem-library/ball-cover-lemmas"
    "calculus/finite-ball-subcover-proof"
    ;; calculus/compact-tb-proof MOVED 2026-09-18 below theorem-library/rake-metric-constructions:
    ;; it cites ball-cover-is-open-cover, proven there (it had been an asserted support).
    ;; calculus/compact-complete-proof MOVED 2026-09-19 below structure-library/metric-laws: two of its three
    ;; leaves are proven in rake-compact-complete, which cites metric-triangle (the window was empty here).
    ;; compact-metric-is-separable, PROVEN (was a `reference' support in
    ;; structure-library/separable.scm, retired there).  The gate on the Ascoli
    ;; arc.  Needs nn-pairing (nn-flatten, immediately above) plus dc-on-nn
    ;; (dc-on-nn-pred), separable (IS-SEPARABLE, tb-scale-dense-seq),
    ;; compactness, order-predicates (nn-recip-succ-*), order-lemmas
    ;; (rr-lt-trans) and fun-apply-type-proof -- all earlier.
    ;; theorem-library/compact-separable-proof MOVED 2026-09-18 with compact-tb-proof (it cites
    ;; compact-implies-totally-bounded); nothing cites compact-metric-is-separable.
    ;; rake batch 5 (2026-09-18): card-bijection-eq, finsum-reindex(-ag), qq-nonneg-is-fraction
    "theorem-library/rake-algebra3"
    ;; The five metric laws (pos/self-zero/zero-eq/sym/triangle), PROVEN by
    ;; projecting the is-metric property folded into IS-METRIC-SPACE -- they
    ;; were redundant asserted axioms (a definition oversight).
    "structure-library/metric-laws"
    ;; rake batch 6 (2026-09-19): cauchy-seq-is-fun, cauchy-cluster-converges PROVEN; then their one citer.
    ;; The one open-set constructor of the tree; latest citation metric-triangle (metric-laws).  Moved here
    ;; from the Ascoli block on 2026-09-19 so that rake-compact-cluster can cite it.
    "theorem-library/ball-is-open"
    "theorem-library/rake-compact-complete"
    ;; rake batch 7 (2026-09-19): compact-seq-has-cluster PROVEN (cover by the open sets the sequence abandons;
    ;; no pair-valued choice).  Was the single leaf of compact-implies-complete.  Uses bc*: loads from source.
    "theorem-library/rake-compact-cluster"
    ;; compact => complete (the other half of Prop 3.12 (1)=>(4)): a Cauchy
    ;; sequence in a compact space has a cluster point, and a Cauchy sequence
    ;; with a cluster point converges.  Installs compact-implies-complete, also
    ;; formerly an asserted support here.  Needs compactness (compact-seq-has-
    ;; cluster, cauchy-cluster-converges) + metric-completeness (cauchy-seq-is-fun).
    "calculus/compact-complete-proof"
    ;; rake-balls -- ball-unfold, ball-membership, ball-is-set, ball-center-in,
    ;; ball-2r-triangle (were `proof'-warranted supports in metric-topology.scm) and
    ;; cauchy-block-estimate (was a support inside cauchy-subsequence.scm), PROVEN
    ;; 2026-09-17 (rake batch B).  Window [255, 261): metric-laws above,
    ;; cauchy-subseq-proof (cites cauchy-block-estimate) below.
    "theorem-library/rake-balls"
    ;; 2026-09-20 (batch 12-B): the metric subspace, RESTRICT, closed subset of a compact space.
    "theorem-library/metric-subspace-laws"
    "theorem-library/compact-subspace"
    ;; rake-analysis-typing -- embed-in-fun and five helpers (was a support in
    ;; metric-completion.scm), PROVEN 2026-09-17 (rake batch H).  Window [257, end):
    ;; metric-laws (metric-self-zero) above; no citer.
    "theorem-library/rake-analysis-typing"
    ;; rake-cont-preimage -- continuous-implies-open-preimage, PROVEN 2026-09-17 (rake
    ;; batch L): the last support of metric-open-sets.scm.  Window [262, 279):
    ;; rake-balls above, rake-open-sets below.
    "theorem-library/rake-cont-preimage"
    ;; The four PSEUDOMETRIC laws (self-zero/pos/sym/triangle), PROVEN by
    ;; projecting `is-pseudometric' -- the same move metric-laws just made for
    ;; `is-metric', but stated about a bare distance FUNCTION and a carrier,
    ;; which is the form a member of a pseudometric FAMILY arrives in.  The tree
    ;; had no projection of is-pseudometric at all.
    "theorem-library/pseudometric-laws"
    "theorem-library/bdd-metric-distance"
    ;; The whole bdd-fn-* family plus bdd-metric-bounded and
    ;; bdd-metric-is-metric-space -- PROVEN modulo 0 (wave 6).
    ;; Before bdd-metric-convergence, the earliest citer.
    "theorem-library/bdd-metric-basics"
    ;; rake batch 6 (2026-09-19): nn-step-strictly-mono, subsequence-capture (from dc-on-nn-pred), null-rr-seq-exists.
    ;; Window [nn-infinite, diagonalization).
    "theorem-library/rake-subseq-leaves"
    ;; batch 8 (2026-09-19): cauchy-rapid-subsequence PROVEN modulo 0 (dc-on-nn-pred over NN, the step set spelled
    ;; with IS-CAUCHY-SEQ's own binders so the skolemized hypothesis IS the invariant).  Floor: nn-step-mono-ptwise.
    "theorem-library/rake-dc-consumers"
    ;; rake batch 7 (2026-09-19): cluster-point-has-convergent-subseq and compact-implies-seq-compact (the forward
    ;; half of compact-iff-seq-compact; the support stays until the converse is proven: tychonoff-proof uses both).
    "theorem-library/rake-compact-iff-seq-compact"
    ;; rake batch 7 (2026-09-19): seq-compact-implies-totally-bounded PROVEN modulo 0 (dc-on-nn-pred over the
    ;; carrier FIN-SUBSETS(PTS s): the step state is the whole finite set, so no card layer).  Floor: metric-laws.
    "theorem-library/rake-seq-compact-tb"
    ;; rake batch 7 (2026-09-19): the LEBESGUE NUMBER lemma, seq-compact-implies-compact, and compact-iff-seq-compact
    ;; itself (Prop 3.12 (1)<=>(3)), all modulo 0.  Uses bc*: loads from SOURCE, never compile it.
    "theorem-library/rake-lebesgue-number"
    ;; rake batch 7 (2026-09-19): nn-enum-spec PROVEN (choose! with the subsequence-capture witness), and two
    ;; bricks: strictly-mono-image-infinite, strictly-mono-le-reflect.  Floor: rake-subseq-leaves.
    "theorem-library/rake-nn-enum"
    ;; rake batch 6 (2026-09-19): cover-block-step (pigeonhole-infinite), dist-le-implies-in-carrier.
    ;; Window [nn-infinite, block-family-combinatorial-proof).
    "theorem-library/rake-tb-leaves"
    ;; rake batch 6 (2026-09-19): tb-scale-dense-seq, tb-rad-ball-cover -- provable since IS-R-NET says
    ;; F subseteq A (the user's decision).  Window [rake-balls, cauchy-subseq-proof).
    "theorem-library/rake-tb-leaves-2"
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
    ;; rr-metric-space-proof -- IS-METRIC-SPACE(RR-MS), PROVEN modulo 0.  It was
    ;; a bare theory-add-axiom! in numeric-instances.scm with no warrant at all,
    ;; hence `trust: none', and it was the SOLE unwarranted leaf of rr-complete
    ;; (immediately below).  Waiting on the MULTI-BINDER case of pi-lambda-type!,
    ;; which arrived 2026-08-14 naming this theorem as the thing it unblocked.
    ;; Needs rr-order-basics (rr-abs-sub-sym) and the lam-t / lam-b rules.
    "theorem-library/rr-metric-space-proof"
    ;; trunc-metric-proof -- the TRUNCATED metric min(1,d): a metric (the
    ;; def-constructed-functor's typing obligation, discharged), bounded by 1,
    ;; and UNIFORMLY equivalent to d in both directions.  Needs
    ;; structure-library/trunc-metric, metric-laws (the five projected laws),
    ;; metric-continuity (IS-UNIFORMLY-CONTINUOUS), rr-min-basics
    ;; (rr-min-closed/-cases/-le-left/-le-right, rr-le-min,
    ;; rr-min-one-subadditive), rr-halving (rr-pos-halvable), rr-order-basics
    ;; (rr-min-pos), rr-recip-order (rr-zero-lt-one) and `obtain'.
    "theorem-library/trunc-metric-proof"
    ;; cc-metric-space-proof MOVED 2026-08-17, with cc-magnitude, to just after
    ;; sqrt-defined (below).  It cites cc-magnitude and must follow it.
    "theorem-library/rr-complete-proof"
    ;; metric-limit-unique -- A SEQUENCE IN A METRIC SPACE HAS AT MOST ONE
    ;; LIMIT, proven once for an arbitrary metric space, with rr-limit-unique
    ;; and cc-limit-unique as three-line instances.  rr-limit-unique WAS proved
    ;; inside dominated-convergence (L8), sixty lines of rr-abs-* bookkeeping
    ;; reaching a fact that is not about the reals; the abstract proof is
    ;; shorter because no absolute value appears in it.  The statement
    ;; re-installed here is byte-identical to the retired one.  Needs
    ;; metric-laws (the five laws), op-typing (metric-dist-real), rr-halving
    ;; (rr-pos-halvable), rr-le-all-pos-nonpos, rr-max-basics (nn-max-closed,
    ;; rr-le-max-left/right) and complex (CC-MS).  MUST precede
    ;; dominated-convergence, which cites rr-limit-unique and no longer proves
    ;; it.  MOVED UP HERE from just above dominated-convergence on 2026-09-14:
    ;; seq-limit-core (next) cites rr-limit-unique and has to precede
    ;; ascoli-bridge; everything this file needs was already above this line.
    "theorem-library/metric-limit-unique"
    ;; THE LIMIT OF A REAL SEQUENCE AS A TERM: SEQ-LIMIT (totalised by an IF so
    ;; that seq-limit-in-rr is UNCONDITIONAL and the term may sit in the body of
    ;; a VNB-LAMBDA over all of RR), seq-limit-converges-to, seq-limit-value,
    ;; the TAIL bound rr-limit-tail-abs-le, and rr-cauchy-converges
    ;; (completeness in the abs/eps language rather than in (DIST RR-MS)).
    ;; SPLIT OUT of theorem-library/seq-limit (far below) on 2026-09-14: the
    ;; limit LAWS rr-limit-scale / rr-limit-sub stayed there, since they cite
    ;; limit-arithmetic and rr-null-scale, which load after ascoli-bridge;
    ;; these five cite nothing later than rr-complete-proof and
    ;; metric-limit-unique (rr-limit-unique) just above, and
    ;; unif-cauchy-limit (below) builds unif-cauchy-has-uniform-limit from them
    ;; and must precede ascoli-bridge.  Also needs rr-metric-space-proof,
    ;; rr-ms-dist, rr-abs-basics, rr-le-all-pos, rr-max-basics, rr-min-basics,
    ;; nn-order-basics, binary-minus-laws, fun-apply-type-proof and
    ;; metric-completeness (complete-cauchy-converges).
    "theorem-library/seq-limit-core"
    ;; MOVED to structure-library/ 2026-09-20 (batch 12-A): vocabulary only -- no proof in it.
    "structure-library/ascoli-arzela-statement"
    ;; The analytic core of the dense bridge, PROVEN: equicontinuity + pointwise
    ;; convergence on a dense sequence => Cauchy at every point (the user's notes,
    ;; Lemma 3.36), and CORE A assembled from it plus the one compactness rung.
    ;; Carries the vocabulary IS-DENSE-SEQ / CONVERGES-ON / IS-UNIF-CAUCHY that
    ;; ascoli-bridge used to define, so it must load BEFORE ascoli-bridge.
    "theorem-library/ascoli-analytic-cores"
    ;; ball-is-open MOVED UP on 2026-09-19 to just after structure-library/metric-laws (its window is
    ;; [metric-laws, ptwise-cauchy-unif)): an open-cover proof in the metric block needs it.
    ;; rake-open-sets -- the eight open-set / preimage supports of
    ;; structure-library/metric-open-sets.scm, PROVEN 2026-09-17 (rake batch C).
    ;; Window [272, 464): ball-is-open above, metric-top-proof below.
    "theorem-library/rake-open-sets"
    "theorem-library/ptwise-cauchy-unif"
    "theorem-library/ascoli-assembly"
    ;; CORE B1 of the dense bridge, PROVEN (2026-09-14): a uniformly Cauchy
    ;; sequence fam : NN -> (PTS(s) -> RR) has a uniform limit.  The limit is
    ;; VNB-LAMBDA x in PTS(s). SEQ-LIMIT(VNB-LAMBDA k in NN. fam(k)(x)); it is
    ;; a function by seq-limit-in-rr (unconditional), it is the pointwise limit
    ;; by rr-cauchy-converges + seq-limit-converges-to, and the uniform
    ;; estimate is rr-limit-tail-abs-le at the uniform-Cauchy threshold for
    ;; eps/2.  Retires the `reference' support of that name that ascoli-bridge
    ;; carried.  Needs seq-limit-core and metric-limit-unique (above),
    ;; ascoli-analytic-cores (IS-UNIF-CAUCHY) and ascoli-arzela-statement
    ;; (CONVERGES-UNIFORMLY) just above, rr-halving, rr-order-basics,
    ;; pos-rr-bridges, rr-abs-basics, binary-minus-laws and
    ;; fun-apply-type-proof.  MUST precede ascoli-bridge, which cites it.
    "theorem-library/unif-cauchy-limit"
    "theorem-library/ascoli-bridge"
    ;; Functional-analysis statement seeds (stated 2026-07-22; proofs deferred).
    ;; MOVED to structure-library/ 2026-09-20 (batch 12-A): vocabulary only -- no proof in it.
    "structure-library/order-zorn"
    ;; INJECTION(X,Y) => INJECTIVE-STAR(f): the bridge between the set-function and
    ;; class-function spellings of injectivity.  Needs injection.scm (both) and
    ;; fun-domain-apply-def (theory).
    "theorem-library/injective-star"
    "theorem-library/zorn-proof"
    ;; ZORN'S LEMMA, proved: the strictly increasing transfinite tower ZUP and the
    ;; Burali-Forti contradiction.  Must come after ord-no-injection (its endgame)
    ;; and before seminorm-hahn-banach, whose `rests-on' names zorn-lemma.
    "theorem-library/zorn-route-two"
    ;; MOVED to structure-library/ 2026-09-20 (batch 12-A): vocabulary only -- no proof in it.
    "structure-library/seminorm-hahn-banach"
    ;; MOVED to structure-library/ 2026-09-20 (batch 12-A): vocabulary only -- no proof in it.
    "structure-library/baire-category"
    ;; 2026-09-20 (batch 12-F): closure, interior, closed balls; the Baire step.
    "theorem-library/metric-closure-laws"
    "theorem-library/rake-baire"
    ;; MOVED to structure-library/ 2026-09-20 (batch 12-A): vocabulary only -- no proof in it.
    "structure-library/frechet-open-mapping"
    ;; subseq-of-convergent: a subsequence of a convergent sequence converges to
    ;; the same limit.  A keystone brick.  Needs cauchy-subsequence + metric-
    ;; completeness supports + interactive.
    "theorem-library/subseq-convergence-proof"
    ;; subsequence-principle: the CONVERSE direction -- if every subsequence of f
    ;; has a further subsequence converging to L, then f converges to L.  PROVEN
    ;; modulo {nn-finite-subset-bounded, subsequence-capture}.  Also installs
    ;; fun-codomain-subset (PROVEN modulo 0: widening a codomain along a subset
    ;; inclusion) and asserts nn-finite-subset-bounded, the converse of
    ;; diagonalization-lemmas' inf-subset-nn-unbounded.  Needs cauchy-subsequence
    ;; (STRICTLY-MONO-NN/SUBSEQ), subsequence-capture, inf-subsets,
    ;; metric-completeness, fun-apply-type-proof, nn-order-basics (nn-le-refl)
    ;; and driver-kit (have!/use-em/the dk- kit).
    ;; SUBSQN(y,f) -- "y is a subsequence of f", the space-free relation, and
    ;; its bridge to IS-SUBSEQUENCE (which is that relation plus a typing).  The
    ;; def-predicate itself is in cauchy-subsequence.scm, which loads before
    ;; `interactive' and so cannot carry a proof.
    "theorem-library/subsqn-basics"
    "theorem-library/subsequence-principle"
    ;; batch 8 (2026-09-19): tb-block-step (cover-block-step at one radius, by the constant-sequence device),
    ;; tb-has-eps-cauchy-subseq, block-family (block-family-combinatorial at tb-rad-ball-cover's covers): all
    ;; modulo 0; they were asserted in cauchy-subsequence.scm.  Uses bc*: loads from SOURCE, never compile it.
    "theorem-library/rake-offbill-combinatorial"
    ;; poly-tail-zero -- "a polynomial is a sequence that is eventually zero",
    ;; the bridge between the tree's definition (a finitely-supported function
    ;; NN -> CARR(A)) and the usual reading.  Both directions PROVEN; the halves
    ;; are separate theorems because their bills differ (forward pays only
    ;; nn-finite-subset-bounded, backward only card-subset-nn + the four
    ;; seg-mem-succ-le leaves).  Needs subsequence-principle
    ;; (nn-finite-subset-bounded, immediately above), poly-membership,
    ;; prod-of-sums (card-subset-nn), ord-segment-arith (seg-mem-succ-le),
    ;; rr-order-basics (rr-le-total) and nn-order-basics (nn-in-rr).
    "theorem-library/poly-tail-zero"
    ;; monalg-laws -- the monoid-algebra laws that need no reindexing.
    ;; `monalg-add-fun' is PROVEN here (retired from structure-library/
    ;; polynomial.scm, where it was a Bourbaki-warranted support), together with
    ;; two general bricks: `monoid-carrier-is-set' (the sethood conjunct of the
    ;; IS-MONOID definition -- every lam-t over a structure carrier needs it) and
    ;; `monalg-add-apply' (the pointwise value of the pointwise sum).  The file
    ;; ends with a survey of what the other five laws are missing.  Needs
    ;; poly-membership (finsupp-membership, supp-membership, supp-in-set),
    ;; card-inequalities (card-union-nn), prod-of-sums (card-subset-nn) and
    ;; fun-apply-type-proof (fun-apply-type-c), all above.
    ;; finsum-fiber -- FIBERED FUBINI, the dependent-index companion of
    ;; finsum-fubini: a finite sum grouped by the fibers of an arbitrary map.
    ;; PROVEN from finsum-fubini + finsum-single-support + finsum-embed +
    ;; finsum-congruence by the indicator-weighted summand on S x T; it is a
    ;; theorem of the rectangular Fubini, not a new assumption.  The mechanism
    ;; the convolution of A[M] (monalg-mul-assoc) needs.  Also proves the brick
    ;; `cartesian-nth' (the projections of a member of a product), which is what
    ;; every typing of a lambda on a CARTESIAN domain wants and what
    ;; matmul-assoc-summand-type (matrix.scm) asserts instead.  Needs
    ;; finsum-fubini, finsum-additive, matrix (finsum-single-support),
    ;; prod-of-sums (card-subset-nn), subtype-laws (group-identity-in) and
    ;; fun-apply-type-proof (fun-apply-type-c), all above.
    "theorem-library/finsum-fiber"
    ;; 2026-09-20 (batch 13-C): BAIRE CATEGORY THEOREM proven (nested closed balls by dc-on-nn-pred).
    "theorem-library/rake-baire-2"
    "theorem-library/lam-fun-bricks"
    ;; rake-identmat -- identmat-left-identity, identmat-right-identity, matact-entry:
    ;; PROVEN 2026-09-17 (rake batch K).  Window [298, 332): lam-fun-bricks above,
    ;; mat-ring-proof below.
    "theorem-library/rake-identmat"
    ;; rake batch 6 (2026-09-19): generates-coeff-matrix PROVEN.  Window [rake-identmat, rank-bound-proof).
    "theorem-library/rake-generates-coeff"
    "theorem-library/monalg-laws"
    ;; poly-zero -- the ZERO of a monoid algebra, pointwise, and the
    ;; EXTENSIONALITY BRIDGE for polynomials.  All six statements PROVEN
    ;; modulo 0.  `poly-zero-iff' says p = ZERO(POLY A) iff every coefficient
    ;; of p is ZERO(A); contraposed it turns "p is not the zero polynomial"
    ;; into "p has a nonzero coefficient", which is the hypothesis every
    ;; pointwise statement about polynomials consumes -- and which
    ;; poly-degree-laws could not state until this file existed.  The backward
    ;; direction cites `fun-domain-extensionality' (theory.scm, primitive)
    ;; directly; no per-operator congruence lemma is added.  Needs polynomial
    ;; (MONALG-ZERO/POLY), poly-membership, sqn, ring (ring-zero-in),
    ;; equality-basics and numeric-instances -- all above.  Must precede
    ;; theorem-library/poly-degree-laws.
    "theorem-library/poly-zero"
    "theorem-library/monalg-is-ring"
    ;; 2026-09-20 (batch 12-E): prod-of-sums-expansion PROVEN.
    "theorem-library/rake-prod-of-sums"
    ;; rake batch 6 (2026-09-19): finsum-interval-shift.  After rake-border-siblings (cites succ-nn-minus-1) and monalg-is-ring; before border-mult-proof.
    "theorem-library/rake-smith-leaves"
    ;; rake batch 5b (2026-09-18): monalg-comm, bijection-from-inverse, lambda-compose-value
    "theorem-library/rake-monalg-comm"
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
    ;; the ORD-LE/<= bridge; exercises the new ai iff-elim.  Needs interactive
    ;; tactics + qed and the ordinal axioms.
    "theorem-library/nn-least-element"
    ;; DEG / LEADCOEF / MONOMIAL for A[x].  The definitions (structure-library/
    ;; poly-degree) and their proofs (theorem-library/poly-degree-laws), split
    ;; the usual way.  DEG(A,p) is the LARGEST exponent with a nonzero
    ;; coefficient, spelled as the IOTA of the least support bound; its
    ;; well-definedness is a `minimize!' discharge, not an axiom, which is why
    ;; the pair loads HERE -- after nn-least-element, which minimize! resolves
    ;; by name at call time.  Nothing in either file is asserted.  Needs
    ;; polynomial.scm (POLY/SUPP/FINSUPP), poly-membership, poly-tail-zero
    ;; (poly-tail-zero-fwd/bwd), monalg-laws (monalg-add-fun/-apply),
    ;; nn-add-monoid + subtype-laws (IS-MONOID NN-ADD-MONOID), finite-surgery
    ;; (nn-not-lt-le, nn-lt-succ-le), nn-order-proof (nn-le-antisym) and
    ;; equality-basics -- all above.
    ;;
    ;; Registering DEG cost one rename, and the failure it caused is worth
    ;; recording: structure-library/euclidean-ring.scm bound a variable `deg'
    ;; (the Euclidean degree function) in is-euclidean-ring-def,
    ;; has-div-remainder and euclidean-ring-has-gauge.  The head registry is
    ;; SCOPE-BLIND, so from the moment DEG is registered an APPLIED `deg' inside
    ;; those formulas reads as the constant -- and euclidean-ideal-generator-
    ;; proof.scm's final `ai' then failed with `cannot decompose', aborting the
    ;; load and everything after it.  `constant-binder-audit' names exactly this
    ;; and is FATAL, but it runs at the END of the load, long after the damage.
    ;; The binder is now `dg', which is what the same file already called it in
    ;; EUCLIDEAN-GAUGES / gauges-mem-build / gauges-spec.
    "structure-library/poly-degree"
    "theorem-library/poly-degree-laws"
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
    "theorem-library/gauge-is-degree"
    "theorem-library/euclidean-ideal-generator-proof"
    ;; Bezout on ZZ: { x*a + y*b } is an ideal of ZZ-RING (surface-goal! puts the
    ;; ideal conditions in ZZ arithmetic, `crs' decides them), so the Euclidean
    ;; generator above is a common divisor that IS a combination.  Needs
    ;; euclidean-ideal-generator-proof, zz-divisibility, transport.
    "theorem-library/zz-bezout-proof"
    ;; The constant and identity maps are continuous, PROVEN, with their FUN
    ;; typings -- the first two of continuity-algebra's seven asserted supports,
    ;; retired there.  Cited by differentiation.scm (:130-132, :199, :215).
    ;; Needs rr-metric-space-proof, rr-ms-dist, rr-abs-basics, metric-continuity.
    "theorem-library/continuity-basics"
    ;; Negation preserves membership in FUN(RR,RR) and continuity, PROVEN --
    ;; the two lemmas that make the MIN form of EVT a corollary of the max form
    ;; rather than a second copy of its proof.  MOVED here 2026-08-18 from just
    ;; before evt-min-proof: continuity-sub (below) builds a DIFFERENCE out of
    ;; it, so it must now precede continuity-algebra.  Its own dependencies were
    ;; already met far earlier -- metric-continuity, rr-abs-basics
    ;; (rr-abs-bound), binary-minus-laws (rr-sub-in-rr), rr-ms-dist -- so only
    ;; the position moved.  The comment it used to carry, that citing the then
    ;; asserted sub-continuous-at would have put a fresh asserted leaf into the
    ;; eleven bills EVT had just been removed from, is now moot: sub-continuous-
    ;; at is proven, and proven from this file.
    "theorem-library/neg-continuous"
    ;; The pointwise SUM of two maps continuous at a is continuous at a, PROVEN
    ;; modulo 0, with its FUN typing (sum-lam-in-fun) -- the third of
    ;; continuity-algebra's seven asserted supports, retired there, and the first
    ;; of the two that carry content.  The eps/2 estimate is one citation of
    ;; rr-abs-sum-bound (rr-abs-basics) and "the min of the two deltas" is
    ;; rr-min-pos (rr-order-basics).  Needs continuity-basics's dependencies plus
    ;; rr-halving (rr-pos-halvable) and fun-apply-type-proof; must precede
    ;; continuity-algebra and differentiation.
    "theorem-library/continuity-sum"
    ;; The pointwise PRODUCT, PROVEN modulo 0, with its FUN typing
    ;; (prod-lam-in-fun) -- the fourth of continuity-algebra's seven asserted
    ;; supports and the last of them carrying content.  The estimate is
    ;; rr-abs-prod-bound (rr-abs-basics); unlike the sum it needs ONE of the four
    ;; values bounded, which costs a preliminary delta at eps = 1, and the delta
    ;; is a double rr-min-pos.  Needs continuity-sum's dependencies plus
    ;; rr-recip-order (rr-zero-lt-one, rr-mul-pos, rr-recip-pos); must precede
    ;; continuity-algebra and differentiation.
    "theorem-library/continuity-product"
    ;; The pointwise-equality TRANSFER, PROVEN modulo 0 -- the fifth of
    ;; continuity-algebra's seven asserted supports, and the one that stood
    ;; between diff-implies-continuous and `modulo 0'.  Continuity reads only
    ;; the values, so a map agreeing pointwise with a continuous map inherits
    ;; its delta unchanged: no eps/2 split, no estimate, no arithmetic.  Needs
    ;; only IS-CONTINUOUS-AT (metric-continuity) and RR-MS; must precede
    ;; continuity-algebra and differentiation.
    "theorem-library/continuity-transfer"
    ;; The pointwise DIFFERENCE, PROVEN modulo 0, with its FUN typing
    ;; (sub-lam-in-fun) -- the last of continuity-algebra's seven asserted
    ;; supports carrying content, and after continuity-transfer the SOLE
    ;; unwarranted leaf of diff-implies-continuous.  NO eps/delta: neg-
    ;; continuous-at then sum-continuous-at then cont-transfer-ptwise-eq, the
    ;; bridge between the difference lambda and the sum lambda being one `crs'.
    ;; Needs neg-continuous, continuity-sum and continuity-transfer above; must
    ;; precede continuity-algebra and differentiation.
    "theorem-library/continuity-sub"
    ;; The SCALAR MULTIPLE, PROVEN modulo 0, with its FUN typing
    ;; (scale-lam-in-fun) -- the one shape of the continuity/typing algebra the
    ;; tree did not carry, and the pair Prop 4.8's scalar half
    ;; (antiderivative.scm) stopped on.  NO eps/delta: const-continuous-at then
    ;; product-continuous-at then cont-transfer-ptwise-eq, the bridge between
    ;; x |-> c.f(x) and the product with the constant lambda being one `crs'.
    ;; The typing is NOT a corollary of deriv-scalar-mult, which types the term
    ;; only where f is differentiable.  Needs continuity-basics
    ;; (const-continuous-at), continuity-product, continuity-transfer and
    ;; fun-apply-type-proof, all above; must precede antiderivative.
    "theorem-library/continuity-scale"
    ;; COMPOSITION of continuous maps -- the LAST of continuity-algebra's seven
    ;; asserted supports carrying content, PROVEN 2026-08-23.  eps/delta, one
    ;; nesting of deltas: g's delta at f(a) for eps, then f's delta at a for
    ;; that.  No eps/2 split, no `min', no arithmetic -- the distance is never
    ;; opened into `abs'.  Bills {compose-type, compose-apply} (the two COMPOSE
    ;; laws of structure-library/compose, both `warrant: proof'), NOT zero.  The
    ;; sequential route through continuous-at-iff-sequential was tried first and
    ;; wants two lemmas the tree lacks: associativity of COMPOSE, and transfer
    ;; of CONVERGES-TO across pointwise equality of sequences.  Needs
    ;; metric-continuity, compose (COMPOSE, compose-type, compose-apply),
    ;; fun-apply-type-proof; must precede continuity-algebra (whose
    ;; compose-continuous-at support it retires) and chain-rule.
    "theorem-library/continuity-compose"
    ;; The RECIPROCAL of a nowhere-zero continuous map, PROVEN modulo 0, with
    ;; its FUN typing (recip-lam-in-fun) -- the EIGHTH member of the pointwise
    ;; continuity algebra and the first the tree had nothing of.  `recip' is
    ;; PARTIAL, so the statement is about the composite x |-> recip(h(x)) with
    ;; h nowhere zero, which is total by construction; a bare "recip is
    ;; continuous at c /= 0" is not statable.  The estimate never bounds a
    ;; reciprocal: the ring identity (1/c - 1/z)*(c*z) = z - c plus rr-abs-mult
    ;; turns the whole thing into D*K <= eps*K, and rr-nonneg-cancel-pos strips
    ;; K.  Needs rr-abs-basics (rr-abs-mult, rr-abs-reverse-triangle,
    ;; rr-abs-sub-sym, rr-abs-zero), rr-order-basics (rr-le-scale-nonneg,
    ;; rr-nonneg-cancel-pos, rr-min-pos), rr-recip-order (rr-mul-pos),
    ;; rr-halving (rr-pos-halvable), rr-ms-dist and metric-continuity; must
    ;; precede inverse-function.
    "theorem-library/continuity-recip"
    ;; Pointwise continuity algebra on RR -- the supporting machinery the
    ;; differentiation rules are proved on top of.  ONE support remains asserted
    ;; here (cont-agree-off-pt, which is not an algebra fact but the statement
    ;; that RR has no isolated points); const/identity moved to
    ;; continuity-basics, sum to continuity-sum, product to continuity-product,
    ;; the pointwise-equality transfer to continuity-transfer, the difference to
    ;; continuity-sub and the composite to continuity-compose, all above.
    ;; Needs IS-CONTINUOUS-AT (metric-continuity) + RR-MS (numeric-instances).
    "theorem-library/continuity-algebra"
    ;; cont-agree-off-pt -- PROVEN: two functions continuous at a point and
    ;; agreeing away from it agree at it.  Sixth of continuity-algebra's seven
    ;; supports to fall; only compose-continuous-at is left.  It was fourth in
    ;; the SOLE-leaf ranking (alone in 4 bills, named in 88).  Must precede
    ;; differentiation, the earliest citer.  Needs rr-halving, rr-order-basics
    ;; (rr-min-pos, rr-le-ne-lt, rr-le-all-pos-nonpos), rr-abs-basics, rr-ms-dist.
    "theorem-library/cont-agree-off-pt"
    "theorem-library/continuous-one-sided-sign"
    ;; Chapter 2 (Differentiation) of calculus.pdf: the Caratheodory/o(h)
    ;; derivative IS-DIFF-AT + DERIV, and the first results (uniqueness, Prop 2.4
    ;; diff=>continuous, sum/product rules, const/identity).  Needs IS-CONTINUOUS-
    ;; AT (metric-continuity) + RR-MS / RR arithmetic (numeric-instances).
    "theorem-library/differentiation"
    ;; Differentiability reads only the VALUES: a map agreeing pointwise with a
    ;; map differentiable at a is differentiable at a with the same derivative.
    ;; The mirror of cont-transfer-ptwise-eq one storey up, and the joint every
    ;; Caratheodory argument needs -- the rules conclude about the LITERAL
    ;; lambda they build, so without a transfer an induction cannot feed a
    ;; rule's conclusion into the next rung.  Same witness phi throughout; the
    ;; proof cites no continuity lemma and no arithmetic.  `modulo 0'.  Needs
    ;; differentiation; must precede deriv-power.
    "theorem-library/diff-transfer"
    ;; Calculus Prop 2.5 (SUM rule) and Prop 2.6 (PRODUCT rule), PROVEN, both
    ;; `modulo 0'.  Retires differentiation.scm's two `reference' supports,
    ;; whose warrant texts were the derivations written in prose and never run.
    ;; The witnesses are algebraic (phi_f+phi_g; phi_f.g + f(a).phi_g) and their
    ;; continuity is a citation from the continuity algebra, so there is no
    ;; eps-delta here at all.  The one step the warrants omit: the product
    ;; witness needs g CONTINUOUS at a (Prop 2.4), cited BEFORE `mac-h' eats the
    ;; IS-DIFF-AT hypothesis.  Needs differentiation, continuity-sum,
    ;; continuity-product, continuity-basics and fun-apply-type-proof.
    "theorem-library/deriv-sum-product"
    ;; Calculus Prop 2.8: the CHAIN RULE, PROVEN, plus its DERIV form
    ;; (equation 13) and the reader `deriv-of-is-diff-at' that gets from a
    ;; Caratheodory witness to DERIV.  The Caratheodory factor of g o f is
    ;; (phi_g o f).phi_f: two substitutions and one `crs', with the only
    ;; analytic step being product-continuous-at over compose-continuous-at.
    ;; Retires differentiation.scm's `deriv-chain' support.  Needs
    ;; differentiation (IS-DIFF-AT, DERIV, diff-implies-continuous,
    ;; derivative-unique), continuity-compose (compose-continuous-at),
    ;; continuity-product (product-continuous-at, prod-lam-in-fun) and compose.
    "theorem-library/chain-rule"
    ;; The INVERSE FUNCTION THEOREM on the line, Caratheodory form, PROVEN:
    ;; f differentiable at a with f'(a) /= 0, g a two-sided inverse of f and
    ;; continuous at f(a), gives g differentiable at f(a) with derivative
    ;; 1/f'(a).  The witness is recip o phi o g -- continuous at f(a) by
    ;; compose-continuous-at then recip-continuous-at -- and the only real work
    ;; is that phi never vanishes, which is where the inverse hypothesis is
    ;; used.  GLOBAL, not local: IS-DIFF-AT is total on RR, so "invertible near
    ;; a" is not statable (no metric subspace structure).  Bills
    ;; {compose-type, compose-apply}, inherited from compose-continuous-at.
    ;; Needs differentiation, continuity-compose, continuity-recip, compose.
    "theorem-library/inverse-function"
    ;; Calculus Def 2.2: the n-th derivative NTH-DERIV(f,n) as a function, by
    ;; NN-recursion on DERIV (nth-deriv-zero / -succ).  Needs DERIV
    ;; (differentiation) + def-by-nn-recursion (ordinals).
    "theorem-library/higher-derivatives"
    ;; Calculus Section 2.2: the o/O calculus, limit-free (LITTLE-O-AT) -- the
    ;; eq-12 bridge to IS-DIFF-AT + o-algebra (sum, scalar).  Needs IS-DIFF-AT
    ;; + IS-CONTINUOUS-AT.
    ;; MOVED to structure-library/ 2026-09-20 (batch 12-A): vocabulary only -- no proof in it.
    "structure-library/little-o"
    ;; Linear algebra: the two matrix-product entry-expansion lemmas
    ;; (triple-entry-left/right), PROVEN from the (B) finite-sum bricks; cited by
    ;; matmul-assoc-proof, so loads before it.
    "theorem-library/triple-entry-proof"
    ;; Linear algebra: matrix multiplication is associative, via finsum-fubini
    ;; (matrix-entry-extensionality + triple-entry expansion + order-of-summation
    ;; interchange).  Cited by mat-ring-proof, so loads before it.
    "theorem-library/matmul-assoc-proof"
    ;; theorem-library/mat-ring-proof MOVED 2026-09-19 one entry down, below elem-entry-readoffs: the eight
    ;; matrix-algebra laws it cites are proven in rake-matrix-laws, which needs matadd-entry / entry-of-zeromat.
    ;; Linear algebra: Lemma 3.3 (algebraic-numbers.pdf ch.3), the column-shift
    ;; formula (P.E[k,l])_{ic} = P_{ik} if c=l else 0 -- matmul-entry expansion +
    ;; finsum-single-support collapse + EM case-split.  Engine behind Prop 3.5.
    ;; Needs elementary-matrix.scm (matunit PSS) + matrix.scm read-offs.
    ;; The elementary-matrix ENTRY read-offs -- 23 supports PROVEN (wave 8) by ONE
    ;; generic lane, `eer-run!', with no per-theorem driver: decide each IF
    ;; condition against the context, if-true/if-false a decided one, use-em an
    ;; undecided one, recurse.  Nothing in the lane is about matrices; it is a
    ;; candidate for driver-kit as dk-if-close!.  Every bill is {entry-of-matof},
    ;; the single floor under this whole family.  Must load after
    ;; structure-library/elementary-matrix (the four functoids) AND after driver-kit /
    ;; prop / interactive, as any proof file must; before
    ;; theorem-library/matunit-shift-proof, the earliest citer.
    "theorem-library/elem-entry-readoffs"
    ;; rake batch 6 (2026-09-19): matadd-comm/-assoc/-zero-left/-zero-right/-neg-left/-neg-right and the two
    ;; GUARDED distributivity laws, one entrywise driver.  Window [elem-entry-readoffs, mat-ring-proof).
    "theorem-library/rake-matrix-laws"
    ;; Linear algebra: MAT(n,n,A) is a ring.  Assembly proof unfolding the
    ;; generated IS-RING iff and discharging each of its 14 conjuncts against
    ;; matrix.scm's read-offs + matrix-ring axioms.  Needs matrix.scm (loaded
    ;; above) + the tactic surface (interactive, loaded above).
    "theorem-library/mat-ring-proof"
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
    ;; 2026-09-24 (batch 25-C): THE DETERMINANT IS LINEAR IN EACH ROW AND ALTERNATING, from the first-row cofactor
    ;; definition (det-row-linear, det-swap-rows, det-alternating-rows -- a THEOREM now, its support retired), the
    ;; elementary row operations, expansion along ANY row (det-expand-row); det(EA) = det E det A for an elementary E.
    ;; det-multiplicative: PROVEN the same day (batch 26-B, after bordered-eq-border-proof).
    "theorem-library/det-rows"
    "theorem-library/det-mul"
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
    ;; matact-summand-type-le-guarded -- PROVEN modulo 0 (wave 7).  It replaces the
    ;; UNGUARDED support, which was false: the statement's whole content is
    ;; [1,k] subset [1,n], and that needs k in NN -- `k <= n' is the RR order and
    ;; types nothing.  After interval-widen (which it cites), before
    ;; span-bricks2-proof (its only citer).
    "theorem-library/matact-summand-type-le-proof"
    ;; Linear algebra Phase B: block-matrix multiplication BORDER(a,X).BORDER(c,Y)
    ;; = BORDER(ac, X.Y) -- the direct-sum law the Smith bordering rests on.
    "theorem-library/border-mult-proof"
    ;; Linear algebra Phase B: the border algebra -- border-identity /
    ;; border-is-diagonal / border-invertible (routine, on border-mult).
    "theorem-library/border-assembly-proof"
    ;; Linear algebra Phase B: bordered-eq-border -- a cross-cleared C equals
    ;; BORDER(C11, SUBMAT C); bridges clear-first-row/col to the BORDER block form.
    "theorem-library/bordered-eq-border-proof"
    ;; 2026-09-24 (batch 26-B): Hoffman-Kunze 5.3 Thm 2 -- a function of n x n matrices linear in each row and zero on
    ;; two equal rows is det(A) * D(I) (det-alternating-form; induction on n, no permutations, no signs) -- and
    ;; DET IS MULTIPLICATIVE over any commutative ring (det-multiplicative, a THEOREM now, its support retired);
    ;; the notes' 3.20 (det-mul-invertible).
    "theorem-library/det-alternating-form"
    "theorem-library/det-multiplicative"
    ;; 2026-09-25 (batch 32): det(A^t) = det A by the uniqueness theorem (det-alternating-form), the COLUMN
    ;; clauses of the notes' 3.18 (det-col-linear, det-swap-cols, det-equal-cols-zero), 3.19 for the elementary
    ;; column operations (det-elem-{f,g,h}-col, det-mul-elem-*-col) and 3.22 column expansion (det-expand-col).
    "theorem-library/det-transpose"
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
    ;; BRICKS 1-2: the coefficient row acts linearly (lincomb-row-add/-scale).
    "theorem-library/matact-row-linear-proof"
    ;; BRICK 3: SPAN(md,n,u) is a submodule and u spans it; module-act-neg-one,
    ;; lincomb-zerorow/-unitrow/-empty.
    "theorem-library/span-bricks-proof"
    ;; BRICKS 4-6: lincomb-row-peel / lincomb-snoc, submodule-intersection, the
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
    ;; (structure-library/extreme-value -- the CCINT def-functoid -- MOVED UP 2026-09-20,
    ;; batch 12-A, to the calculus-vocabulary block after numeric-instances: it is a SEP over
    ;; RR and has no floor, while 43 files are STATED with CCINT.)
    ;; ccint-membership, PROVEN modulo 0 from the separation that DEFINES
    ;; CCINT.  Retires the `add-to-pss' support that stood in extreme-value
    ;; (whose warrant text was the derivation, unrun).  Must precede every
    ;; citer: rolle-proof, interior-extremum-proof, deriv-constant-proof,
    ;; deriv-monotone-proof, ivt-proof.
    "theorem-library/ccint-basics"
    ;; The INTERMEDIATE VALUE THEOREM, PROVEN modulo 0 by Bolzano's sup
    ;; argument on S = { x in [a,b] : f(x) <= c }.  Needs extreme-value
    ;; (CCINT), ccint-basics (just above), rr-halving (rr-pos-halvable),
    ;; rr-ms-dist, rr-abs-basics (rr-abs-bound), rr-order-basics
    ;; (rr-lt-trichotomy, rr-sub-ne-zero), metric-continuity, and `obtain'.
    "theorem-library/ivt-proof"
    ;; MONOTONICITY VOCABULARY -- IS-STRICTLY-INCREASING-ON(f, s), which the
    ;; tree had no form of (deriv-monotone-proof writes it longhand) -- plus the
    ;; EXISTENCE HALF of the inverse function theorem on a closed interval, all
    ;; `modulo 0': ccint-subset-rr, strict-increase-injective,
    ;; monotone-ccint-inverse-exists (every y in [f(a),f(b)] is f(x) for a
    ;; UNIQUE x in [a,b] -- `ivt' for existence, injectivity for uniqueness) and
    ;; monotone-ccint-inverse-order.  The inverse is NOT packaged as a function:
    ;; continuity of it is not statable without relative continuity or a metric
    ;; subspace, and the file header says so.  Needs ivt-proof immediately
    ;; above, ccint-basics (ccint-membership), rr-order-basics
    ;; (rr-lt-trichotomy) and fun-apply-type-proof.
    "theorem-library/monotone-inverse"
    ;; sq-continuous -- z |-> z*z is in FUN(RR,RR) and is continuous at every
    ;; real point, PROVEN modulo 0.  Step one of DEFINING SQRT by the IVT, and
    ;; the step that is easy to miss: `ivt' applies to a CONTINUOUS f, and every
    ;; fact in theorem-library/continuity-algebra.scm is an asserted support, so
    ;; citing `product-continuous-at' here would relabel the debt rather than
    ;; clear it.  Needs rr-order-basics (rr-min-pos, rr-prod-le-prod,
    ;; rr-le-scale-nonneg), rr-abs-basics (rr-abs-mult, rr-abs-bound),
    ;; rr-recip-order, rr-metric-space-proof, rr-ms-dist and metric-continuity.
    "theorem-library/sq-continuous"
    ;; sqrt-defined -- SQRT DEFINED as IOTA x. x in RR and 0 <= x and x*x = a
    ;; (the description is in structure-library/real-powers.scm), and the five
    ;; supports that used to characterise it -- sqrt-nonneg, sqrt-sq,
    ;; sqrt-of-sq, sqrt-mono, sqrt-mul -- RETIRED as theorems, `modulo 0'.
    ;; Existence is `ivt' on the square over [0, 1+a]; uniqueness is the
    ;; difference of squares against rr-no-zero-divisors.  Needs ivt-proof and
    ;; sq-continuous immediately above, ccint-basics (ccint-membership),
    ;; rr-order-basics and rr-abs-basics.  Must PRECEDE cc-magnitude.
    "theorem-library/sqrt-defined"
    ;; cc-magnitude -- the complex modulus, PROVEN from the definition in
    ;; structure-library/complex.scm.  Replaces seven axioms of
    ;; number-systems.scm (closed / nonneg / zero-iff / neg / mul / triangle,
    ;; and rr-magnitude-is-abs).  MOVED HERE 2026-08-17 from just after
    ;; cc-real-imag: the five SQRT facts it cites are now theorems of
    ;; sqrt-defined above, not supports of real-powers.scm, and with that these
    ;; bills reach `modulo 0'.  Needs cc-real-imag (cc-re-im-of), rr-abs-basics
    ;; (rr-abs-of-nonneg), rr-order-basics (rr-sq-nonneg, rr-no-zero-divisors)
    ;; and equality-basics (eq-sym).
    "theorem-library/cc-magnitude"
    ;; 2026-09-20 (batch 13-B): cc-is-normed-field PROVEN (was an unwarranted asserted axiom).
    "theorem-library/cc-normed-field"
    ;; cc-metric-space-proof -- IS-METRIC-SPACE(CC-MS), the same axiom one system
    ;; up, PROVEN.  Also a bare theory-add-axiom! with no warrant (complex.scm),
    ;; so also `trust: none'.  It became available when `magnitude' stopped being
    ;; axiomatised and became DEFINED (cc-magnitude.scm, 2026-08-17): the three
    ;; laws with content are now cc-magnitude-zero-iff / -neg / -triangle.  Adds
    ;; cc-sub-in-cc and cc-sub-zero-eq, the two ring facts the RR proof got from
    ;; `ineq' and CC cannot, having no order.  Needs cc-magnitude, immediately
    ;; above; MOVED with it 2026-08-17.
    "theorem-library/cc-metric-space-proof"
    ;; complex-inner-product-laws -- the SECOND-argument laws of a sesquilinear
    ;; form (additivity, conjugate-homogeneity, vanishing at 0), got by
    ;; conjugating the first-argument laws, plus the two expansion identities
    ;; <x+y,x+y> and <a.x+b.y, a.x+b.y> that every inner-product inequality is
    ;; an instance of.  All PROVEN modulo 0.  Needs structure-library/
    ;; complex-inner-product (the cips-* projections) and the cc-conjugate-*
    ;; axioms (number-systems, primitive).
    "theorem-library/complex-inner-product-laws"
    ;; inner-product-inequalities -- CAUCHY-SCHWARZ and MINKOWSKI at the
    ;; inner-product level (no finite sums).  Needs complex-inner-product-laws
    ;; above, sqrt-defined (sqrt-nonneg/-sq/-of-sq/-mono/-mul), cc-real-imag
    ;; (cc-re-im-of, real-part-in-rr), rr-order-basics (rr-nonneg-cancel-pos,
    ;; rr-le-from-diff-nonneg, rr-le-cases, rr-sq-nonneg) and binary-minus-laws
    ;; (rr-sub-in-rr).
    "theorem-library/inner-product-inequalities"
    ;; rake batch 5b (2026-09-18): ip-normed-ag-is-normed-ag
    "theorem-library/rake-ip-normed-ag"
    ;; (rr-sup-approx MOVED 2026-09-14 up to just after subset-lemmas, so that
    ;; nn-unbounded-in-rr -- proven from it -- can sit below compact-separable-proof.)
    ;; The supremum APPROXIMATION lemma: nothing below SUP(S) is an upper bound,
    ;; i.e. for d > 0 some member of S exceeds SUP(S) - d.  The half of order
    ;; completeness rr-sup-in/-upper/-least do not give directly, and the step
    ;; every creeping argument needs.  Needs subset-lemmas (subset-mem-fwd),
    ;; rr-order-basics (rr-lt-trichotomy), binary-minus-laws (rr-sub-in-rr).
    ;; MONOTONE CONVERGENCE on RR: a nondecreasing real sequence bounded above
    ;; converges (to the supremum of its range), plus the monotone lift
    ;; nn-monotone-step-implies-le it needs -- retiring the asserted support of
    ;; the same name in series-order-lemmas.scm, which comparison-test names as
    ;; the lemma it was waiting on.  Needs rr-sup-approx just above,
    ;; order-lemmas (nn-zero-le, nn-le-succ-cases), nn-order-basics (nn-in-rr),
    ;; fun-apply-type-proof, rr-abs-basics (rr-abs-bound), binary-minus-laws
    ;; (rr-sub-in-rr), rr-ms-dist and rr-metric-space-proof.
    "theorem-library/monotone-convergence-proof"
    ;; THE COMPARISON TEST, PROVEN -- retiring the asserted support of that name
    ;; in power-series.scm and the two order supports it cited
    ;; (series-partial-sum-monotone-nonneg, series-partial-sum-le-termwise) in
    ;; series-order-lemmas.scm.  Brings the SUM-AG recurrence to the surface
    ;; (series-partial-sum-zero/-succ, off the RR additive-group readouts) and
    ;; proves the rung the warrant did not name: a convergent nondecreasing
    ;; sequence is bounded above.  Needs monotone-convergence-proof just above,
    ;; power-series, sequences, views, numeric-instances, metric-completeness,
    ;; rr-order-basics (rr-le-total), nn-order-basics (nn-le-refl),
    ;; rr-abs-basics, binary-minus-laws, rr-ms-dist, fun-apply-type-proof.
    "theorem-library/comparison-test-proof"
    ;; series-abs-triangle -- |Sum f(n)| <= Sum |f(n)|, PROVEN, with abs(0) = 0.
    ;; analysis-inequalities.scm describes this in a warrant and nothing proved
    ;; it: rr-abs-triangle is the two-term case, series-block-le compares two
    ;; NONNEGATIVE series.  It is the rung under ps-absolute-implies-convergent,
    ;; and so under the ratio test.  A transplant of cc-series.scm's
    ;; cc-series-partial-sum-magnitude-le with six names swapped.  Needs
    ;; comparison-test-proof immediately above and rr-abs-basics.
    "theorem-library/series-abs-triangle"
    ;; series-block-abs -- the BLOCK triangle inequality over m..k, plus the NN
    ;; gap lemma (m <= k => k = m + d) that the tree did not have and that is
    ;; the only bridge between the shape `use-induction' can prove (induct on
    ;; the gap) and the shape every eps/N argument wants (bnd <= m <= n).  The
    ;; rung directly under ps-absolute-implies-convergent.  Needs
    ;; series-abs-triangle immediately above, nn-order-proof (nn-le-succ-cases,
    ;; nn-le-zero-is-zero), nn-arith and driver-kit's `use-cases'.
    "theorem-library/series-block-abs"
    ;; rake-finsum-typing-nn -- nn-minus-in-nn, falling-in-nn: PROVEN 2026-09-17 (rake
    ;; batch G); both cite nn-le-gap (series-block-abs, just above).
    "theorem-library/rake-finsum-typing-nn"
    ;; LINEARITY OF THE REAL PARTIAL SUM, in POINTWISE / TRANSFER form: the
    ;; partial sums of a family typed only by `forall k in NN. f(k) in RR'
    ;; (which a ZZ-indexed family such as COMB-KK satisfies and FUN(NN,RR)
    ;; membership does not), with the summand given by a pointwise EQUATION
    ;; rather than as a literal lambda.  Three NN inductions off
    ;; series-partial-sum-succ, all `modulo 0'.  What the Bernstein moments
    ;; need, and what makes the unwarranted `sum-left-scalar' axiom
    ;; unnecessary on the RR surface.
    "theorem-library/series-linearity"
    ;; THE BERNSTEIN BASIS POLYNOMIALS and identity (75) of docs/calculus.pdf
    ;; Proposition 5.4 -- rung 2 of the integration arc.  B_{k,n}(x) is
    ;; COMB-KK (binomial.scm) at RR's ring view with y := 1-x, so the partition
    ;; of unity is `binomial-theorem' by citation once two bridges exist:
    ;; ONE^n = ONE in a commutative ring, and SERIES-PARTIAL-SUM = the ring SUM
    ;; over that view (both PROVEN here, `modulo 0').  The second is what puts
    ;; every later Bernstein estimate on the RR surface, where `crs' and `ineq'
    ;; can see it, instead of behind (ADD r) accessors.  Needs
    ;; comparison-test-proof just above (series-partial-sum-zero/-succ),
    ;; normed-field-ring-view, binomial-proof, finsum-additive (ring-power-succ).
    "theorem-library/bernstein-basis"
    ;; THE BERNSTEIN MOMENTS and identity (76) of Proposition 5.4 -- the half
    ;; of the proposition with combinatorial content.  The mechanism is
    ;; series-linearity's WEIGHTED multiply-and-shift expansion, of which
    ;; binomial-proof's `sum-expansion' is the weight-1 case; the three
    ;; moments are the weights 1, k and k(k-1).  Needs bernstein-basis just
    ;; above and series-linearity.
    "theorem-library/bernstein-moments"
    ;; THE CAUCHY CRITERION FOR REAL SERIES, PROVEN -- retiring the asserted
    ;; `well-known' support of that name in series-order-lemmas.scm (its LAST
    ;; live entry) and clearing the one genuinely ANALYTIC asserted leaf of
    ;; dominated-convergence.scm just below, which CITES the name.  Convergence
    ;; names a limit; each partial sum is within eps/2 of it (rr-pos-halvable);
    ;; the block is the difference.  No triangle inequality: `rr-abs-bound' on
    ;; the goal and rr-le-abs / rr-neg-abs-le on the hypotheses make everything
    ;; linear and `ineq' decides it.  Needs comparison-test-proof just above
    ;; (series-partial-sum-in-rr, series-partial-sum-seq-apply), rr-abs-basics,
    ;; rr-halving, rr-ms-dist, binary-minus-laws, nn-order-basics,
    ;; power-series and metric-completeness.
    "theorem-library/series-cauchy-proof"
    ;; DOMINATED CONVERGENCE, PROVEN, in two forms -- for real series (the
    ;; content) and in ELL-ONE (defined here) -- with the twenty lemmas they
    ;; are assembled from.  Four of those are library gaps rather than
    ;; bookkeeping: LIMIT UNIQUENESS on RR-MS (the tree had none, in any form),
    ;; which makes SERIES-LIMIT(f) = IOTA L. SERIES-CONVERGES-TO(f,L) a DEFINED
    ;; term -- the ell^1 norm, and the shape of product-metric's D_w;
    ;; LINEARITY of series convergence (nonnegative case), without which the
    ;; dominator a + a of the ell^1 argument could not be said to converge;
    ;; the CC-MS distance on the surface (the CC-MS twin of rr-ms-dist); and
    ;; the FINITE HEAD lemma, which is where a max over a finite family would
    ;; have been needed and is not -- induction on the head length reduces it
    ;; to the binary MAX.  Needs comparison-test-proof just above
    ;; (series-partial-sum-succ/-zero/-in-rr/-seq-in-fun, comparison-test,
    ;; monotone-convergent-bounded-above), monotone-convergence-rr,
    ;; rr-max-basics and rr-min-basics, series-cauchy-proof just above
    ;; (series-cauchy-criterion), rr-abs-basics, binary-minus-laws,
    ;; metric-limit-unique (rr-limit-unique -- the file loaded HERE until
    ;; 2026-09-14 and now sits beside rr-complete-proof, far above, because
    ;; seq-limit-core needs it there; its comment went with it),
    ;; nn-order-basics, order-lemmas, fun-apply-type-proof, rr-ms-dist,
    ;; cc-magnitude and sqn.
    "theorem-library/dominated-convergence"
    ;; cc-complete-proof -- IS-COMPLETE(CC-MS), the LAST of the three bare
    ;; `trust: none' metric-space axioms about CC (the other two,
    ;; cc-is-metric-space and the five magnitude laws, went on 2026-08-17).
    ;; Coordinatewise from rr-complete: the two projections of a Cauchy sequence
    ;; are Cauchy in RR because |Re w| <= |w|, they converge, and the complex
    ;; estimate comes back from |w| <= |Re w| + |Im w|.  None of those three
    ;; bounds was in the tree; nor was Re(z-w) = Re z - Re w.  All five are
    ;; proved here, `modulo 0', ahead of the theorem.  Sits after
    ;; dominated-convergence only for `cc-ms-dist'; everything else it cites --
    ;; cc-magnitude, cc-real-imag, cc-metric-space-proof, rr-complete-proof,
    ;; rr-ms-dist, rr-abs-basics, binary-minus-laws, sqrt-defined,
    ;; fun-apply-type-proof, nn-order-basics -- is far above.
    "theorem-library/cc-complete-proof"
    ;; series-abs-converges -- ABSOLUTE CONVERGENCE IMPLIES CONVERGENCE for real
    ;; series: the block estimate makes the partial sums Cauchy and RR is
    ;; complete.  Bills {nn-not-le-zero-pos} only, inherited through
    ;; series-abs-triangle-le -> nn-le-gap.  Sits here for `series-tail-small'
    ;; (dominated-convergence) and `rr-complete'.  NOT the same theorem as the
    ;; asserted `ps-absolute-implies-convergent', which is the power-series
    ;; specialisation and needs the three PS/series bridges, themselves asserted.
    "theorem-library/series-abs-converges"
    ;; cc-series -- THE COMPLEX SERIES LAYER: CC-SERIES-PARTIAL-SUM (SUM-AG over
    ;; the additive group of CC), CC-SERIES-CONVERGES-TO / -CONVERGES in CC-MS,
    ;; and the five results that make them usable (the two slot read-offs, the
    ;; empty sum, the CC typing by induction, the functoid unfold as a theorem,
    ;; and the recurrence).  NO COMPLEX SUM WAS FORMED ANYWHERE IN THE TREE
    ;; before this: SUM-AG was used over RR's additive group only, and ELL-ONE
    ;; is defined through the REAL series of magnitudes.  All seven `modulo 0',
    ;; citing neither cc-is-normed-field nor sum-ag-type -- the closure comes off
    ;; the instance slots and cc-add-closed, as comparison-test-proof does for
    ;; RR.  Needs complex (CC-MS), numeric-instances (CC-NORMED-FIELD), views
    ;; (NORMED-FIELD-ADDITIVE-AG), sequences (SUM-AG) and metric-completeness.
    "theorem-library/cc-series"
    ;; A TERM OF A NONDECREASING CONVERGENT SEQUENCE IS AT MOST ITS LIMIT
    ;; (rr-mono-le-limit) -- the sharp bound the tree did not have, and the rung
    ;; the retired warrant of `comparison-test' named and then did not need
    ;; (monotone-convergent-bounded-above takes eps = 1 and gets L + 1 instead).
    ;; With it, "a partial sum is at most the sum": the partial sums are
    ;; nonnegative (series-partial-sum-nonneg, a two-line induction) and a
    ;; nonnegative series whose sum is 0 has every term 0
    ;; (series-nonneg-zero-sum) -- which is the zero law of the countable
    ;; product metric.  Needs comparison-test-proof just above
    ;; (series-partial-sum-zero/-succ/-in-rr/-seq-apply/-seq-in-fun,
    ;; series-partial-sum-monotone-nonneg), monotone-convergence-proof
    ;; (nn-monotone-step-implies-le), dominated-convergence just above
    ;; (series-partial-sum-nonneg), rr-max-basics, rr-min-basics
    ;; (nn-max-closed), rr-abs-basics, binary-minus-laws, order-predicates
    ;; (rr-le-all-pos-nonpos), rr-ms-dist, fun-apply-type-proof.
    "theorem-library/mono-le-limit"
    ;; THE TWO LIMIT LAWS BOTH LANES WERE MISSING: `<=' carried across TWO
    ;; limits (rr-limit-le) and the limit of a pointwise SUM (rr-limit-add),
    ;; with the series readings of the second (series-converges-to-add,
    ;; series-limit-add).  The nearest facts in the tree all carry a CONSTANT
    ;; on one side -- rr-limit-abs-le a uniform bound, rr-mono-le-limit the
    ;; sequence's own limit, rr-null-sum the two zeros -- and
    ;; dominated-convergence's header records the second gap in as many words
    ;; ("The signed case wants lim(f+g) = lim f + lim g and is NOT here").
    ;; Neither needed a new mechanism: both are the eps/2 pattern of the two
    ;; files above, with rr-pos-halvable, the binary MAX and one `ineq'.
    ;; Needs mono-le-limit just above (its driver), dominated-convergence
    ;; (rr-limit-unique, series-limit-converges-to / -in-rr,
    ;; series-partial-sum-add), comparison-test-proof
    ;; (series-partial-sum-seq-apply / -seq-in-fun), rr-halving, rr-max-basics,
    ;; rr-min-basics, rr-abs-basics, binary-minus-laws, order-predicates,
    ;; rr-ms-dist and fun-apply-type-proof.
    "theorem-library/limit-arithmetic"
    ;; ell-two -- ELL-TWO, the square-summable complex sequences, with the
    ;; carrier's INHABITATION and its closure under the pointwise sum and
    ;; negation.  The first storey of the l^2(NN; CC) witness that would make
    ;; `cips-schwarz' and `cips-minkowski' (both PROVEN modulo 0,
    ;; inner-product-inequalities.scm) say something: COMPLEX-INNER-PRODUCT-
    ;; SPACE is one of the thirteen entries of structure-exemplification-
    ;; audit's UNWITNESSED list, so those two inequalities are currently true
    ;; and empty.  NO `declare-instance!' here, and the reason is a
    ;; measurement rather than a preference: the INNER PRODUCT
    ;; Sum_k x(k) conj(y(k)) is a COMPLEX series and the tree has none --
    ;; SERIES-PARTIAL-SUM is hard-wired to NORMED-FIELD-ADDITIVE-AG(RR-NORMED-
    ;; FIELD) (power-series.scm) and SERIES-CONVERGES to RR-MS.  The CARRIER
    ;; needs no complex series at all, |x(k)|^2 being real, which is why this
    ;; storey is reachable today; ELL-ONE (dominated-convergence.scm) rests on
    ;; the same observation.  Needs dominated-convergence just above
    ;; (series-converges-sum, comparison-test), monotone-convergence-proof,
    ;; cc-magnitude (cc-magnitude-closed/-nonneg/-neg/-triangle/-zero-iff),
    ;; rr-order-basics (rr-sq-nonneg, rr-prod-le-prod), sqn, real-powers.
    "theorem-library/ell-two"
    ;; THE CANONICAL PRODUCT-METRIC WEIGHTS 2^-(n+1) ARE SUMMABLE, proven --
    ;; retiring `product-metric-default-summable' (structure-library/
    ;; product-metric.scm) and, on the way, the never-cited `power-real-closed'
    ;; of power-series.scm.  The route is the closed-form partial sum
    ;; 1 - 2^-k by induction, which hands `monotone-convergence-rr' both its
    ;; hypotheses at once; the geometric series is not used and could not be
    ;; (it is asserted, and bridging a scalar multiple is not in the tree).
    ;; What the file is really about is that `crs' sees NEITHER `recip' NOR a
    ;; symbolic `power' -- it declines on the first and crashes on the second --
    ;; so every arithmetic step here is a generic RR identity over VARIABLES
    ;; (rr-scaled-inverse-unique, rr-halving-identity), proved by `crs' and then
    ;; INSTANTIATED at the recip/power term.  Needs comparison-test-proof and
    ;; monotone-convergence-proof above, rr-recip-order (rr-mul-pos,
    ;; rr-recip-pos), nn-parity-proof (nn-succ-plus-one), equality-basics,
    ;; `calc', and structure-library/product-metric (SUMMABLE-WEIGHT).
    "theorem-library/dyadic-weights"
    ;; rake batch 5 (2026-09-18): the scalar inequalities, rr-bernoulli, rr-pos-shrink, finsum inequalities
    "theorem-library/rake-inequalities"
    ;; The POWER RULE for the real monomial: n in NN =>
    ;;   IS-DIFF-AT(lambda x in RR. x^(succ n), a, succ(n).a^n).
    ;; Induction on n with the variable OUTERMOST (`ni' tests the goal's shape
    ;; literally); the step is deriv-product on identity x monomial, carried
    ;; onto the monomial itself by diff-transfer-ptwise-eq.  Stated with `succ n'
    ;; rather than n-1 so every exponent stays in NN and every `power' stays in
    ;; the unconditional part of its definition.  HERE, and not beside
    ;; differentiation.scm, because it cites `power-closed-at' -- proved in
    ;; dyadic-weights directly above; the alternative was a second copy of that
    ;; induction.  Bill {nn-add-succ}, from nn-succ-plus-one: the only debt in
    ;; the power rule is NN successor arithmetic, nothing analytic.  Needs
    ;; deriv-sum-product (deriv-product), diff-transfer, dyadic-weights
    ;; (power-closed-at), nn-parity-proof (nn-succ-plus-one), nn-order-basics.
    "theorem-library/deriv-power"
    ;; RUNG 1 OF THE INTEGRATION ARC: the DERIVATIVE OF A POLYNOMIAL, in the
    ;; coefficient-lambda representation
    ;;   lambda x in RR. SERIES-PARTIAL-SUM(lambda k in NN. a(k) x^k, succ n)
    ;; -- the same shape TAYLOR-POLY already has (taylor-proof.scm:19), and NOT
    ;; the formal polynomial ring POLY: the evaluation homomorphism is a
    ;; separate later bridge and the analysis does not wait on it.  Induction on
    ;; the degree with the variable OUTERMOST; the step is series-partial-sum-succ
    ;; on BOTH sums, joined by deriv-sum over the induction hypothesis and
    ;; deriv-coef-monomial, and carried onto the next rung's partial sum by
    ;; diff-transfer-ptwise-eq -- without which the induction cannot be written.
    ;; Carries the CONSTANT-MULTIPLE rule (deriv-scalar-mult), which the tree did
    ;; not have and which gmvt-aux-diff's warrant text already names.  Needs
    ;; deriv-power directly above, deriv-sum-product, diff-transfer,
    ;; differentiation (deriv-const), dyadic-weights (power-closed-at) and
    ;; comparison-test-proof (series-partial-sum-zero/-succ/-in-rr).
    "theorem-library/deriv-polynomial"
    ;; EXAMPLE 4.7 of the notes -- "every polynomial function is antiderivable",
    ;; with the antiderivative written out:
    ;;   d/dx sum_{k<=n} a_k x^(k+1)/(k+1) = sum_{k<=n} a_k x^k.
    ;; The rung the integration arc consumes: Cor 4.17 plus Theorem 5.2 turn it
    ;; into "every continuous function has an antiderivative", which DEFINES the
    ;; integral.  deriv-polynomial's driver one storey up and SHORTER than it --
    ;; both sums split at the same index succ n, since antiderivative and
    ;; derivative are indexed by the same k.  The one step with content is the
    ;; coefficient cancellation (succ k)(recip(succ k) a_k) = a_k, which `crs'
    ;; cannot do (recip is not a ring operation): it is rr-recip-inverse, whose
    ;; antecedent NOT (succ k = 0) is `nn-succ-nonzero' verbatim -- NN <= ZZ <=
    ;; QQ <= RR being inclusions of SETS, there is no separate "as a real" form.
    ;; Needs deriv-polynomial directly above (deriv-coef-monomial),
    ;; deriv-sum-product (deriv-sum), diff-transfer, dyadic-weights
    ;; (power-closed-at), comparison-test-proof (series-partial-sum-zero/-succ/
    ;; -in-rr), nn-parity-proof (nn-succ-nonzero) and nn-order-basics (nn-in-rr).
    "theorem-library/poly-antiderivative"
    ;; The series defining the weighted product metric CONVERGES, proven --
    ;; retiring the asserted product-weighted-summable and product-metric-carrier
    ;; of structure-library/product-metric.scm -- together with the functoid-unfold
    ;; readout of PRODUCT-CARRIER it needed, and the product metric's DISTANCE
    ;; FORMULA (D_w(x,y) is the sum of the coordinate series), which the tree
    ;; had for BDD-METRIC and for nothing else.  Needs comparison-test-proof
    ;; above, dominated-convergence (series-limit-converges-to),
    ;; structure-library/product-metric and bounded-metric.
    ;; (moved up from below tychonoff-proof on 2026-09-16: product-is-metric-space
    ;; needs it, and nothing between the two positions cites it.)
    "theorem-library/product-summable"
    ;; product-is-metric-space -- PROVEN modulo 0 (2026-09-16) with nine bricks,
    ;; the general one being series-limit-le (a termwise inequality passes to the
    ;; sums).  Retires the last unproven leaf of five bills.  Needs product-summable.
    "theorem-library/product-is-metric-space"
    ;; rake batch 7 (2026-09-19): convergence-block-tower PROVEN modulo 0 -- block-step-converges, ONE
    ;; dc-on-nn-pred over INF-SUBSETS(NN), the limit point a VNB-LAMBDA with a CHOICE body (no second dependent
    ;; choice).  It was the sole leaf of the diagonal facts, of compact-countable-product and of the Ascoli route.
    ;; Window [product-summable, rake-diagonal-subseq).
    "theorem-library/rake-block-tower"
    ;; countable Tychonoff headline, PROVEN to QED modulo the diagonalization
    ;; keystone.  Needs seq-compact-product's supports + interactive/proof-debt.
    ;; tychonoff-proof MOVED DOWN on 2026-09-19 to just after rake-diagonal-subseq (below product-convergence).
    ;; A nonnegative constant multiple of a null sequence is null -- the scalar
    ;; half of limit linearity, which the tree had nowhere (rr-null-sum adds two
    ;; null sequences and nothing scales one), plus the eps/delta lemma
    ;; rr-scale-eps that packages the reciprocal d = eps/(1+c).  Needs
    ;; dominated-convergence's neighbours: rr-ms-dist, fun-apply-type-proof,
    ;; rr-abs-basics, order-predicates and rr-recip-order.
    "theorem-library/rr-null-scale"
    ;; Convergence is the SAME in d and in the bounded metric d/(1+d) -- the
    ;; SEQUENTIAL form of the equivalence bounded-metric.scm asserts about open
    ;; sets, which no bridge in the tree connected to sequences.  Carries
    ;; bdd-fn-reflect, the missing converse of bdd-fn-mono.  Needs bounded-metric,
    ;; scalar-inequalities (bdd-fn-le-arg), rr-recip-order, rr-order-basics,
    ;; fun-apply-type-proof and `prop'.
    "theorem-library/bdd-metric-convergence"
    ;; rake batch 5 (2026-09-18): bounded metric, ball cover, product projection; then the two
    ;; compactness proofs moved down from the ball-cover-lemmas block (see the note there).
    "theorem-library/rake-metric-constructions"
    "theorem-library/rake-rr-bounded-ms"
    "calculus/compact-tb-proof"
    ;; batch 8 (2026-09-19): compact-iff-cluster-point and compact-iff-tb-complete (Prop 3.12 (1)<=>(3), (1)<=>(4))
    ;; PROVEN modulo 0 as assemblies.  Floor: compact-implies-totally-bounded, directly above.  No citer.
    "theorem-library/rake-compact-equivalences"
    ;; compact-iff-fip (Prop 3.12 (1)<=>(2)), modulo 0: compact-implies-fip, fip-implies-compact, by complements
    ;; at the ELEMENT level (bu-me / bu-mi), INTERSECTION-OF's De Morgan laws, card-image-finite.  With it all
    ;; four Prop 3.12 equivalences are theorems.  Uses bc*: loads from SOURCE, never compile it.
    "theorem-library/rake-compact-fip"
    "theorem-library/compact-separable-proof"
    ;; batch 8 (2026-09-19): equicont-subseq, and ascoli-sequential-from-diagonal -- Ascoli's conclusion from its
    ;; hypotheses + inhabitedness + ONE antecedent (a subsequence converging on a dense sequence).  That
    ;; antecedent is ascoli-pointwise-diagonal, proven in rake-ascoli-diagonal (below, after Bolzano-Weierstrass).
    "theorem-library/rake-ascoli"
    ;; CONVERGENCE IS A NULL SEQUENCE OF DISTANCES (converges-iff-dist-null):
    ;; CONVERGES-TO(t,f,L) iff the real sequence j |-> (DIST t)(f(j), L) is
    ;; null.  The bridge between the two languages the product and c-metric
    ;; lanes are written in -- everything provable about null sequences lives
    ;; in FUN(NN,RR), everything the product statements say is about
    ;; CONVERGES-TO -- and product-convergence-coordinatewise needs the
    ;; crossing in BOTH directions.  Both sides unfold to the same eps/N
    ;; clause; the content is (DIST RR-MS)(d,0) = abs(d) = d for d >= 0.
    ;; Carries `dist-seq-apply', whose left-hand side has a schema variable in
    ;; OPERATOR position and so cannot be applied with `mac' -- it is
    ;; instantiated by `fact' and used with `subst'.  Needs metric-space
    ;; (metric-pos, metric-dist-real), metric-completeness, rr-ms-dist,
    ;; rr-abs-basics, fun-apply-type-proof, `prop' and dk-lam-t!.
    "theorem-library/converges-dist-null"
    ;; THE SEQUENTIAL CHARACTERIZATION OF CONTINUITY, both directions proven:
    ;; f is continuous at a iff it carries every sequence converging to a to one
    ;; converging to f(a).  The bridge the product lane needs -- product-metric's
    ;; `product-weights-equivalent' is stated as BICONTINUITY while everything
    ;; provable about the product metric is about CONVERGENCE.  Carries three
    ;; lemmas the tree did not have: `not-continuous-witness' (the negation of
    ;; the eps/delta clause, as a theorem of pure logic -- push-not-h needs a
    ;; SMALL context, `prop' counting the atoms of the whole one),
    ;; `rr-recip-antitone' (recip reverses the order on the positives, named as
    ;; missing in the warrants of nn-recip-succ-pos/-small) and its NN reading
    ;; `nn-recip-succ-antitone'.  The (<=) construction is CHOICE of a SEP at
    ;; each scale 1/(k+1) -- the CENTRES idiom -- so it bills nothing beyond the
    ;; primitive choice-axiom.  Needs metric-continuity, metric-completeness,
    ;; compose, sqn, metric-laws (metric-sym), fun-apply-type-proof,
    ;; rr-recip-order, rr-order-basics, nn-order-basics, order-predicates,
    ;; push-not and `prop'.
    "theorem-library/sequential-continuity"
    ;; recip-succ-null -- 1/(n+1) -> 0 in RR-MS, the null sequence every eps/N
    ;; argument reaches for.  `nn-recip-succ-small' says a scale below eps
    ;; EXISTS; nothing said the scales CONVERGE.  Bills {nn-recip-succ-small},
    ;; the Archimedean property in its NN reading and now its only leaf.
    ;; POSITION, which took two loads to find and neither the band nor a probe
    ;; can tell you: the estimate cites `nn-recip-succ-antitone', which is
    ;; PROVEN in sequential-continuity immediately above (not asserted in
    ;; order-predicates, where its two siblings are), and the CONVERGES-TO goal
    ;; opens with IS-METRIC-SPACE(RR-MS), from rr-metric-space-proof.  Also
    ;; needs pos-rr-of-lt (nn-recip-succ-pos), rr-abs-basics (rr-abs-bound),
    ;; order-predicates (nn-recip-succ-small) and numeric-instances (rr-ms@pts,
    ;; rr-ms-dist).
    "theorem-library/recip-succ-null"
    ;; CONVERGENCE IN THE COUNTABLE PRODUCT IS EXACTLY COORDINATEWISE
    ;; CONVERGENCE, both directions PROVEN -- the defining property of the
    ;; PRODUCT TOPOLOGY, retiring the asserted `product-convergence-coordinatewise'
    ;; of structure-library/product-metric.scm.  The backward half, which the
    ;; retired warrant described as a weight-tail estimate plus a finite
    ;; intersection, is ONE citation of `dominated-null-series'; the forward
    ;; half is `series-term-le-sum' plus a SQUEEZE the tree did not have.
    ;; Carries two general lemmas, both `modulo 0': `rr-null-squeeze' (a
    ;; nonnegative sequence below a null one is null) and `converges-to-transfer'
    ;; (pointwise-equal sequences converge alike -- the metric lane's missing
    ;; transfer form, without which the beta-redex `(k |-> seq(k)(n))(j)' that
    ;; converges-dist-null-fwd builds cannot be reduced under its binder).
    ;; Needs product-summable just above, converges-dist-null,
    ;; bdd-metric-convergence, rr-null-scale, mono-le-limit (series-term-le-sum),
    ;; dominated-convergence (dominated-null-series) and `prop'.
    "theorem-library/product-convergence"
    ;; rake batch 7 (2026-09-19): seq-compact-countable-product and coordinatewise-diagonal-subseq PROVEN (through
    ;; the proven diagonalization + coord-block-estimate) from convergence-block-tower (rake-block-tower, proven).
    "theorem-library/rake-diagonal-subseq"
    ;; MOVED HERE 2026-08-22 from just after cauchy-subseq-proof: it cites
    ;; `product-metric-default-summable', which is no longer an axiom of
    ;; structure-library/product-metric.scm but a THEOREM of dyadic-weights.scm
    ;; directly above, and a theorem has to be proved before it can be cited.
    ;; Nothing loaded between the two positions cites compact-countable-product.
    "theorem-library/tychonoff-proof"
    ;; (moved again 2026-09-19: its leaf seq-compact-countable-product is proven in rake-diagonal-subseq, whose
    ;; floor is product-convergence.  Nothing between the old and the new position cites compact-countable-product.)
    ;; rake-setoid2 -- nine setoid facts (class-*, quotient-*, descend-computes,
    ;; quotient-universal, descend2-computes), cauchy-setoid-is-setoid, embed-isometry
    ;; (term restated to ((EMBED M) u)): PROVEN 2026-09-17 (rake batch O).  Window
    ;; [after product-convergence (rr-null-squeeze), end).
    "theorem-library/rake-setoid2"
    ;; rake batch 5c (2026-09-18): completion-is-metric-space
    "theorem-library/rake-completion-ms"
    ;; 2026-09-20 (batch 12-D): completion-is-complete PROVEN.
    "theorem-library/rake-completion-complete"
    ;; ANY TWO SUMMABLE WEIGHT SEQUENCES GIVE THE SAME TOPOLOGY on the
    ;; countable product, PROVEN -- retiring the asserted
    ;; `product-weights-equivalent' of structure-library/product-metric.scm and
    ;; with it the last asserted statement about the product's topology.  It is
    ;; the rung just above twice, crossed from CONVERGENCE to CONTINUITY by
    ;; `sequential-implies-continuous-at'; the identity is typed at all only
    ;; because PTS(PRODUCT-METRIC-W(ms,w)) == PRODUCT-CARRIER(ms) for every w.
    ;; Needs product-convergence just above, sequential-continuity,
    ;; product-summable (product-metric-carrier), compose and sqn.
    "theorem-library/product-weights"
    ;; The series defining the CANONICAL METRIC of a countably-metrised space
    ;; converges, proven, with the plumbing every later argument about C-METRIC
    ;; needs (the k-th distance is real -- which is the chain the asserted
    ;; `metric-dist-real' declines to run -- the termwise bound, the carrier and
    ;; distance readouts, and the canonical dyadic instance).  Mirror of
    ;; product-summable above.  Needs dyadic-weights
    ;; (product-metric-default-summable), comparison-test-proof,
    ;; dominated-convergence (series-limit-converges-to), pseudometric-laws,
    ;; rr-min-basics, pair-tuple-sethood and structure-library/c-metric-space.
    "theorem-library/c-metric-summable"
    ;; The CREEPING PRINCIPLE on [a,b]: a property holding at `a' that a local
    ;; step carries a little to the right of wherever it holds already, holds at
    ;; `b'.  The shared mechanism under boundedness-on-[a,b], the attainment
    ;; half of EVT, and (when it is written) Heine-Borel.  Needs rr-sup-approx
    ;; above and ccint-basics (ccint-membership).
    "theorem-library/ccint-creep"
    ;; A continuous function on [a,b] is BOUNDED ABOVE -- the first instance of
    ;; ccint-creep, and the half of EVT nothing in the tree had (without it
    ;; there is no supremum of the image for EVT to attain).  Needs ccint-creep,
    ;; rr-order-basics (rr-upper-of-two), rr-ms-dist, rr-abs-basics,
    ;; metric-continuity.
    "theorem-library/ccint-bounded"
    ;; A continuous function on [a,b] is UNIFORMLY continuous there, PROVEN
    ;; modulo 0 -- the SECOND instance of ccint-creep, and the analytic input
    ;; Bernstein density (Theorem 5.2, step (87)) needs.  Stated WITHOUT
    ;; IS-UNIFORMLY-CONTINUOUS, whose domain argument must be a metric SPACE:
    ;; [a,b] is not one until the tree has a metric SUBSPACE structure, the same
    ;; blocker Heine-Borel sits behind.  Needs ccint-creep, ccint-basics
    ;; (ccint-membership), rr-halving (rr-pos-halvable -- twice: eps/2 and then
    ;; delta/2, and the creep radius is the SECOND halving), rr-order-basics
    ;; (rr-min-pos, rr-le-ne-lt), rr-abs-basics (rr-abs-bound), rr-ms-dist,
    ;; metric-continuity.
    "theorem-library/uniform-continuity-ccint"
    ;; The EXTREME VALUE THEOREM (max form), PROVEN -- retiring the asserted
    ;; support of the same name in extreme-value.scm, which was the only
    ;; asserted mathematics in the Fermat -> Rolle -> MVT -> Taylor tower.
    ;; Boundedness (above) plus a second creep on { x : some k < SUP f([a,b])
    ;; bounds f on [a,x] }.  Needs ccint-bounded, ccint-creep, rr-halving,
    ;; rr-order-basics (rr-upper-of-two-below); must precede mean-value and
    ;; rolle-proof, which cite it.
    "theorem-library/evt-proof"
    ;; BABY HEINE-BOREL: a closed real interval has the finite-subcover
    ;; property, PROVEN modulo 0 -- the third instance of ccint-creep, and the
    ;; first that is not about a continuous function.  Stated WITHOUT
    ;; IS-COMPACT / IS-OPEN-COVER, which are predicates on a metric-space
    ;; STRUCTURE and would need a metric SUBSPACE constructor the tree does not
    ;; have.  Needs ccint-creep, ccint-basics (ccint-membership), rr-halving
    ;; (rr-pos-halvable -- BALL is OPEN, so the creep radius is the HALF of the
    ;; radius openness supplies), rr-order-basics (rr-le-lt-trans, rr-le-ne-lt),
    ;; rr-abs-basics, rr-ms-dist, subset-lemmas (subset-mem-fwd),
    ;; makeset-card-bound (union-comm, union-singleton-absorb),
    ;; structure-library/metric-open-sets (IS-OPEN) and cardinality.
    "theorem-library/heine-borel-baby"
    ;; EVT (min form), PROVEN: extreme-value-max at z |-> -f(z).  Retires the
    ;; last asserted support of theorem-library/extreme-value.scm.
    "theorem-library/evt-min-proof"
    ;; |f| BOUNDED ON A CLOSED INTERVAL, PROVEN modulo 0 -- the two-sided bound
    ;; the tree did not have.  Both EVTs are one-sided and
    ;; continuous-bounded-above-on-ccint is bounded ABOVE only; Bernstein's far
    ;; block wants 2M.  A MERGE, not an analytic argument: no supremum and no
    ;; creep.  Needs evt-proof and evt-min-proof (both attainment theorems),
    ;; ccint-basics (ccint-membership), rr-abs-basics (rr-abs-closed,
    ;; rr-abs-nonneg, rr-le-abs, rr-neg-abs-le, rr-abs-bound), rr-order-basics
    ;; (rr-upper-of-two) and fun-apply-type-proof (fun-apply-type-c).
    "theorem-library/ccint-abs-bounded"
    ;; THEOREM 5.2 of docs/calculus.pdf -- a continuous function on [0,1] is the
    ;; uniform limit of its Bernstein polynomials -- and the operator B_n f it
    ;; is about.  The last rung-2 file.  Not the notes' near/far split of the
    ;; sum (SERIES-PARTIAL-SUM has no predicate decomposition, so that route is
    ;; not expressible): ONE pointwise bound, uniform in the index, summed once
    ;; by the partition of unity (75) and the variance bound (76).  Needs
    ;; bernstein-moments, series-linearity, series-linearity
    ;; (series-partial-sum-le-termwise-ptwise and the three linearity laws),
    ;; uniform-continuity-ccint (87) and ccint-abs-bounded (M = sup|f|).
    "theorem-library/bernstein-density"
    ;; Calculus Ch 2.4-2.5: interior-extremum => f'=0 (Prop 2.10) + Rolle's
    ;; lemma (2.12), toward the MVT.  Needs EVT + IS-DIFF-AT + strict <.
    "theorem-library/mean-value"
    "theorem-library/mvt-cluster-readoffs"
    ;; 2026-09-21 (batch 14-C): deriv-difference.
    "theorem-library/deriv-difference"
    "theorem-library/mvt-aux-guarded"
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
    ;; The TWO-SIDED corollary: |f'| <= M on (a,b) => |f(b)-f(a)| <= M(b-a),
    ;; the upper and lower forms glued by rr-abs-bound.  Hypotheses stated in
    ;; Def 4.6's own shapes (CCINT-guarded continuity, conjunctive-antecedent
    ;; derivative clause) so that a citation off an IS-ANTIDERIVATIVE unfold is
    ;; a `fact' with no reshaping.  Needs mvt-bounds-proof directly above and
    ;; rr-abs-basics.
    "theorem-library/mvt-abs-bound"
    ;; CONTINUITY AT A POINT IS LOCAL: a map agreeing with a continuous map on
    ;; a BALL about the point is continuous there -- the local twin of
    ;; cont-transfer-ptwise-eq, which asks for agreement at EVERY real and so
    ;; cannot be cited about a function built on an interval.  Needs
    ;; metric-continuity, rr-ms-dist, rr-order-basics (rr-min-pos) and
    ;; rr-abs-basics.
    "theorem-library/continuity-local"
    ;; THE TOTALISED RECIPROCAL.  RECIP-STAR(u) = IF u = 0 THEN 0 ELSE recip(u),
    ;; the conditional total extension continuity-recip.scm's header names: the
    ;; bare map z |-> recip(z) is NOT in FUN(RR,RR) (lam-t would owe
    ;; (IN (recip 0) RR)), so the integrand of log(x) = C-INT(recip, 1, x) was
    ;; not a term the vocabulary could write -- IS-ANTIDERIVATIVE demands a
    ;; GLOBAL function.  Same device and same packaging discipline as SEQ-LIMIT:
    ;; recip-star-lam-in-fun is UNCONDITIONAL, and recip-star-value /
    ;; recip-star-zero / recip-star-inverse keep the IF out of every citer.
    ;; Continuity away from zero costs TWO LOCAL transfers (the global
    ;; cont-transfer-ptwise-eq cannot reach it: no nowhere-zero h has
    ;; recip(h(0)) = 0), both off continuous-at-local directly above.  Needs
    ;; continuity-recip (recip-continuous-at, recip-lam-in-fun),
    ;; continuity-basics (identity-continuous-at, ident-lam-in-fun),
    ;; rr-abs-basics, rr-order-basics, rr-halving and rr-recip-order.
    "theorem-library/recip-star"
    ;; CLAMP(a,b,x) = min(max(x,a),b), the retraction of the line onto [a,b],
    ;; and the mechanism that removes calculus.pdf Prop 4.16's ENDPOINT
    ;; problem: a function built as a limit on [a,b] is discontinuous at a and
    ;; b, and composing with CLAMP makes every hypothesis stated on the
    ;; interval speak at every real.  The lever is that CLAMP is 1-LIPSCHITZ,
    ;; so clamp-compose-continuous-at is an eps/delta with no cases.  Needs
    ;; rr-max-basics, rr-min-basics, rr-abs-basics, ccint-basics, rr-ms-dist,
    ;; metric-continuity and fun-apply-type-proof.
    "theorem-library/clamp"
    ;; THE LIMIT ARITHMETIC the tree lacked: rr-limit-scale and rr-limit-sub in
    ;; transfer form.  Until 2026-09-14 this file also DEFINED SEQ-LIMIT and
    ;; proved seq-limit-converges-to / seq-limit-in-rr / seq-limit-value /
    ;; rr-limit-tail-abs-le / rr-cauchy-converges; those are now
    ;; theorem-library/seq-limit-core, ~140 entries up beside rr-complete-proof,
    ;; because unif-cauchy-limit needs them before ascoli-bridge.  The two laws
    ;; could not go with them: they need rr-null-scale (rr-scale-eps) and
    ;; limit-arithmetic (rr-limit-add) above, plus rr-abs-basics, rr-ms-dist,
    ;; metric-completeness and fun-apply-type-proof.
    "theorem-library/seq-limit"
    ;; ---- docs/calculus.pdf CHAPTER 4 SECTION 1 -------------------------
    ;; The vocabulary Definition 4.1 is stated in: one-sided limits as
    ;; RELATIONS (the IS-DIFF-AT precedent), REGULATED, the finite partition
    ;; (58) as an NN-indexed family over INTERVAL(0,n), STEP-FN, PIECEWISE
    ;; CONTINUOUS, and uniform convergence ON [a,b].  Definitions only; needs
    ;; metric-continuity (IS-CONTINUOUS-AT), ccint-basics and INTERVAL.
    ;; MOVED to structure-library/ 2026-09-20 (batch 12-A): vocabulary only -- no proof in it.
    "structure-library/regulated"
    ;; Continuity at x gives both one-sided limits there, with value f(x) --
    ;; both `modulo 0'.  Needs regulated directly above, rr-ms-dist,
    ;; rr-abs-basics (rr-abs-bound, rr-abs-sub-sym), rr-order-basics
    ;; (rr-pos-ne-zero) and fun-apply-type-proof.
    "theorem-library/onesided-limits"
    ;; The EVENTUAL form of the Archimedean bound: for every d > 0 there is an
    ;; n past which every recip(m+1) <= d.  The tree ASSERTS only the pointwise
    ;; form (nn-recip-succ-small) and proves the null sequence from it; an
    ;; epsilon argument needs a threshold, and this derives one out of the
    ;; convergence theorem rather than by a second assertion.  Bills
    ;; `modulo {nn-recip-succ-small}'.  Needs recip-succ-null above.
    "theorem-library/recip-succ-small"
    ;; THE BRIDGE from Ch 4 Sec 1 to the finished Sec 2/3 arc: a function
    ;; continuous on [a,b] is REGULATED there, hence integrable in the notes'
    ;; sense.  Assembly over the two one-sided lemmas; the shape worth keeping
    ;; is that the shared typing work is landed BEFORE the conjunction splits,
    ;; since the two halves are independent nodes.  Needs onesided-limits and
    ;; regulated above, ccint-basics (ccint-membership) and fun-apply-type-proof.
    "theorem-library/continuous-is-regulated"
    ;; A CAUCHY CRITERION FOR ONE-SIDED LIMITS -- the sentence the notes end
    ;; Prop 4.5's sufficiency half with ("since epsilon is arbitrary, this
    ;; proves the left hand limits for g exist"), made a theorem.  The sample
    ;; sequence is x - recip(k+1) in CLOSED FORM, so no choice family is needed;
    ;; `seq-limit' names the limit as a term, so the witness is never
    ;; skolemized.  Bills {nn-recip-succ-small}, inherited through
    ;; recip-succ-small.  Needs recip-succ-small, regulated and onesided-limits
    ;; above, seq-limit-core (rr-cauchy-converges, seq-limit-converges-to),
    ;; rr-halving (rr-pos-halvable), rr-abs-basics and rr-ms-dist.
    "theorem-library/cauchy-criterion-left"
    ;; The RIGHT-hand mirror.  NOT a textual copy of the left one, which is
    ;; worth knowing: the interval conditions invert (x-delta <= s < x becomes
    ;; x < s <= x+delta), the two placement goals swap which premise proves
    ;; them, and the guard helper inside the Cauchy half places its sample
    ;; points the same way and moves with them.
    "theorem-library/cauchy-criterion-right"
    ;; A point of [a,b] lies in SOME piece of a partition of it -- the lemma
    ;; both remaining halves of Prop 4.5 need (`step-is-regulated' and the
    ;; necessity direction).  Induction on the number of pieces, and the reason
    ;; IS-PARTITION types its family TOTAL on NN: the step needs the same family
    ;; read as a partition with one piece fewer, which under a
    ;; FUN(INTERVAL(0,n),RR) typing is a different function and has to be built
    ;; as a VNB-LAMBDA.  Bills three NN-order facts.  Needs regulated above,
    ;; interval-basics, nn-order and ccint-basics.
    "theorem-library/partition-locates-point"
    ;; A UNIFORM LIMIT OF REGULATED FUNCTIONS IS REGULATED -- calculus.pdf
    ;; Prop 4.5, the sufficiency half, and the last open leaf of the
    ;; regulated-functions arc.  The 4-epsilon argument: the one-sided limit of
    ;; g is never CONSTRUCTED -- `cauchy-criterion-right'/`-left' reduce its
    ;; existence to a clustering statement -- and the estimate is closed by
    ;; `ineq' after `rr-abs-bound' opens the four absolute values, rather than
    ;; by three nested triangle inequalities.  Needs cauchy-criterion-left and
    ;; -right, regulated, ccint-basics, rr-order-basics (rr-min-pos),
    ;; rr-abs-basics (rr-abs-bound) and witness-tactics (obtain-at, use-at,
    ;; eps-part).
    "theorem-library/uniform-limit-regulated"
    ;; A UNIFORM LIMIT IS CONTINUOUS AT THE CENTRE OF A BALL on which the
    ;; convergence is uniform -- the pointwise, abs-written companion of
    ;; ascoli-analytic-cores' `uniform-limit-continuous', which concludes on all
    ;; of PTS(s) and demands a metric space.  Needs rr-order-basics (rr-min-pos),
    ;; rr-halving, rr-abs-basics, rr-ms-dist and metric-continuity.
    "theorem-library/uniform-limit-local"
    ;; DIFFERENTIABILITY IS LOCAL (diff-at-local: the Caratheodory identity on a
    ;; ball, plus continuity of the witness at the centre, gives IS-DIFF-AT --
    ;; the witness totalises by the difference quotient outside the ball), and
    ;; the Caratheodory core of calculus.pdf Prop 4.16 (diff-at-ptwise-limit).
    ;; Needs seq-limit just above (rr-limit-sub, rr-limit-scale), differentiation,
    ;; dominated-convergence (rr-limit-unique) and uniform-limit-local's
    ;; neighbours.
    "theorem-library/diff-at-local"
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
    ;; rake batch 6 (2026-09-19): nine Hahn-Banach leaves (typing, projections, two scalar inequalities).
    ;; Window [subset-lemmas, hahn-banach-full-proof).
    "theorem-library/rake-hb-leaves"
    ;; rake batch 7 (2026-09-19): the IOTA of DUAL-NORM-ON / DUAL-NORM DENOTES (dual-norm-on-spec, dual-norm-spec:
    ;; M = SUP of {0} u {|f x| * recip ||x||}), and the six corollaries in their GUARDED forms (-nvs).  The
    ;; unguarded supports are underdetermined (VNRM untyped without IS-NORMED-VECTOR-SPACE m).
    "theorem-library/rake-dual-norm-spec"
    ;; THE MODULE BRIDGE of a normed vector space: the six read-offs of
    ;; NORMED-VECTOR-SPACE-AS-MODULE and the submodule transfer, all PROVEN
    ;; modulo 0.  A normed vector space is a 7-tuple and every module predicate
    ;; (IS-MODULE, IS-VECTOR-SPACE, IS-NOETHERIAN, IS-FINITE-DIMENSIONAL) pins
    ;; length 6, so finite-dimensionality is said OF THE VIEW -- and nothing
    ;; said what the view's slots were until this file.  Needed by
    ;; noetherian-maximal-proof (hb-good-has-maximal) and, through it, by the
    ;; whole finite-dimensional Hahn-Banach arc.
    "theorem-library/nvs-module-view"
    ;; nvs-act-laws -- MOVED here 2026-09-17 (was after vector-taylor-proof): the
    ;; guarded vtaylor-poly-in-vec spliced into vector-taylor-proof cites nvs-act-in-vec.
    ;; Its own window is (nvs-module-view, directional-derivative).
    "theorem-library/nvs-act-laws"
    ;; rake batch 5 (2026-09-18): continuity, the norm metrics (ag-norm-metric-is-metric-space).
    ;; MOVED UP here 2026-09-20 (batch 12-A) from after vector-taylor-proof: its floor was forced
    ;; by the NVS-METRIC-SPACE def-functoid, which is now structure-library/nvs-metric, so the real
    ;; floor is abelian-group-opr-interchange (rake-finsum-laws, far above).  nvs-norm-laws below
    ;; cites nvs-metric-is-ms from it.
    "theorem-library/rake-norm-metrics"
    ;; nvs-norm-laws (2026-09-19, batch 8 consolidation): triangle, homogeneity (-c / RR forms) and ||0|| = 0 of
    ;; VNRM -- ONE home; they had been proven three times under hbg- / lfe- / nvs- prefixes.  The group and action
    ;; laws were gathered into nvs-act-laws the same day.  Suffixes: -c scalar in carr(scal m), -rr scalar in RR.
    "theorem-library/nvs-norm-laws"
    ;; rake batch 7 (2026-09-19): nvs-zero-act, nvs-neg-one-act and nine more NVS bricks; then line-is-submodule
    ;; and span-add-one-submodule by ONE parameterised driver.  Window [nvs-act-laws, hahn-banach-full-proof).
    "theorem-library/rake-hb-submodules"
    ;; The GUARDED forms span-add-one-superset-nvs / span-add-one-has-v-nvs (the unguarded supports are false:
    ;; docs/rake-batch6-2026-09-19.md 4.2).  Cites nvs-vzero-left from the file above.
    "theorem-library/rake-span-add-one-guarded"
    ;; Three more (good-sub-submodule, good-sub-in-power, line-has-v).  Wired 2026-09-19, once NPE / GOOD-SUB /
    ;; LINE had moved to structure-library/linear-functional.  Window [discrete-space, noetherian-maximal-proof).
    "theorem-library/rake-hb-leaves-2"
    ;; (rake-hb-leaves-2 sits HERE, not beside rake-hb-leaves: it cites nvs-scal-one / nvs-act-unital of nvs-act-laws;
    ;; the cold load of 2026-09-19 17:30 caught it.)
    ;; (The four entries above MOVED UP on 2026-09-19 from after hahn-banach-proof: rake-hb-gap needs the
    ;; nvs-act-* laws, and nothing in them depends on hahn-banach-proof.)
    ;; rake batch 7 (2026-09-19): hb-gap PROVEN (hb-gap-bound: the sup construction for an arbitrary bound c,
    ;; modulo 0; hb-gap one instantiation away).  Window [nvs-act-laws, hahn-banach-proof).
    "theorem-library/rake-hb-gap"
    ;; rake batch 7 (2026-09-19): hb-extend-construct PROVEN modulo 0 (uniqueness of y + r.v, the VALUE defined by
    ;; IOTA, one VNB-LAMBDA; vector-group cancellation proven on the way).  Then line-functional-exists, which
    ;; cites six hbx-* lemmas of the first file and 7-A's dual-norm-on-le-bound-nvs: KEEP THIS ORDER.
    "theorem-library/rake-hb-extend-construct"
    "theorem-library/rake-line-functional"
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
    ;; (theorem-library/rake-norm-metrics MOVED UP 2026-09-20 to just before nvs-norm-laws.)
    ;; rake batch 5b (2026-09-18): nf-norm-neg, nf-metric-space-is-metric-space
    "theorem-library/rake-nf-norm"
    ;; 2026-09-20 (batch 12-G): IS-DIFF-ON; the bridge to IS-DIFF-AT.
    "theorem-library/diff-on-laws"
    ;; 2026-09-20 (batch 13-A): the continuity algebra for generic metric spaces and normed fields;
    ;; then uniqueness, constants, identity, sum, product and CHAIN RULE for IS-DIFF-ON.
    "theorem-library/ms-continuity-algebra"
    "theorem-library/diff-on-laws-2"
    ;; 2026-09-20 (batch 13-B): NF-METRIC-SPACE(cc-normed-field) agrees with CC-MS; HOLOMORPHIC-ON read in CC-MS.
    "theorem-library/holomorphic-basics"
    ;; 2026-09-24 (batch 27-A follow-on): deriv-on-of-is-diff-on (DERIV-ON = L from IS-DIFF-ON, over a normed
    ;; field with small elements) and its CC corollary cc-deriv-on-of-is-diff-on.  Needs holomorphic-basics.
    "theorem-library/deriv-on-read-off"
    ;; 2026-09-21 (batch 14-C): end of section 2.1 of the notes: transfer along pointwise equality; constants, identity, sums, products and powers are holomorphic.
    "theorem-library/holomorphic-basics-2"
    ;; 2026-09-21 (batch 15-C): the reciprocal on CC: continuity, 1/z holomorphic off 0 with derivative -1/z^2,
    ;; the reciprocal and quotient rules for HOLOMORPHIC-ON.  Bills nothing asserted.
    "theorem-library/cc-reciprocal"
    ;; 2026-09-21 (batch 15-A): THE CALCULUS ON AN INTERVAL (docs/real-calculus-statements.tex): OOINT,
    ;; IS-CONTINUOUS-ON, the LOCAL derivative HAS-DERIV-AT, EXTEND-CONST (the clamped composite); Rolle, the
    ;; generalized MVT, the MVT and the three bounds for functions ON [a, b], as the user's notes state them.
    ;; The definitions file sits here, not with the vocabulary, because CLAMP is defined in
    ;; theorem-library/clamp.scm (a hoist candidate).
    "structure-library/interval-calculus"
    ;; 2026-09-23 (batch 20-D; the user's decision, docs/roads-regulated-primitives-2026-09-23.md): Dieudonne's
    ;; vocabulary for roads -- IS-COUNTABLE, the one-sided limits WITHIN a set, IS-REGULATED-ON (a function ON
    ;; [a, b] with one-sided limits everywhere), IS-PRIMITIVE (continuous, derivative = f off a COUNTABLE set).
    "structure-library/regulated-primitive"
    "theorem-library/interval-calculus-laws"
    "theorem-library/interval-mvt"
    ;; 2026-09-22 (batch 16-B/16-C): the notes' Def 2.9 / Prop 2.10 (LOCAL extremum, interior case) and the
    ;; vocabulary of Taylor's formula on [a, b] (IS-TAYLOR-FAMILY, TAYLOR-SUM / -AUX / -REM).
    "structure-library/interval-extremum"
    "theorem-library/interval-extremum"
    ;; 2026-09-22 (batch 16-D): ONE-SIDED DERIVATIVES as the notes define them (calculus 2.1, (5)-(6)):
    ;; HAS-DERIV-AT-WITHIN over an arbitrary window, HAS-RIGHT-DERIV-AT / HAS-LEFT-DERIV-AT on half-windows;
    ;; the notes' case (1) (differentiable iff both one-sided derivatives exist and agree); Prop 2.10's first
    ;; two sentences.
    "structure-library/one-sided-derivative"
    "theorem-library/one-sided-derivative-laws"
    "structure-library/interval-taylor"
    ;; calculus.pdf ch.2 s.8 Def 2.23 - Prop 2.27: the DIRECTIONAL derivative,
    ;; over an arbitrary real normed vector space.  Everything reduces to the
    ;; one-variable derivative of the segment curve f_{a,eta}(t) = f(a+t.eta),
    ;; so `mvt' proves 2.24 and `deriv-chain' proves 2.25 -- through ONE
    ;; mechanism, `dir-diff-reparam' (affine reparametrisation), plus the
    ;; IS-DIFF-AT pointwise transfer proved here.  Needs vector-taylor-proof
    ;; (NVS-METRIC-SPACE), mvt-proof, chain-rule, differentiation,
    ;; continuity-basics, compose, fun-apply-type-proof, equality-basics.
    "theorem-library/directional-derivative"
    ;; nvs-taylor-proof -- Taylor for a map between finite-dimensional real
    ;; NVSs, PROVED (it was a statement-only `support' warranted to Dieudonne).
    ;; The reduction is the curve theorem at f := the directional curve, a := 0,
    ;; x := 1.  Loads HERE, after directional-derivative, because that file is
    ;; what supplies nvs-act-one / nvs-act-in-vec / nvs-vadd-in-vec -- the old
    ;; statement file sat before it, which is fine for an assertion and not for
    ;; a proof.
    "theorem-library/nvs-taylor-proof"
    ;; calculus.pdf ch.4 s.2, Def 4.6 - Cor 4.11: the ANTIDERIVATIVE vocabulary
    ;; (IS-ANTIDERIVATIVE / IS-ANTIDERIVABLE), Prop 4.8 (the SUM half; the scalar half is handed off in
    ;; prove-scripts/drives/antiderivative-scale-drive.scm),
    ;; Prop 4.10 (two antiderivatives differ by a constant) and Cor 4.11
    ;; (f(b) - f(a) does not depend on the antiderivative -- the well-definedness
    ;; the definite integral is defined by).  Also `deriv-sub', which the tree
    ;; did not have.  Needs deriv-constant-proof (deriv-zero-implies-constant),
    ;; poly-antiderivative, continuity-sub, deriv-sum-product, deriv-polynomial,
    ;; diff-transfer and ccint-basics.
    "theorem-library/antiderivative"
    ;; The POINTWISE TRANSFER for Def 4.6 -- IS-ANTIDERIVATIVE reads only the
    ;; VALUES, in BOTH slots -- plus Prop 4.8's third case, the DIFFERENCE
    ;; (antiderivative-sub / antiderivable-sub), which is the sum half's driver
    ;; with sub-lam-in-fun / sub-continuous-at / deriv-sub in place of the sum
    ;; forms.  Needs antiderivative directly above, continuity-transfer,
    ;; diff-transfer and continuity-sub.
    "theorem-library/antiderivative-transfer"
    ;; THE WITNESS ESTIMATE of Prop 4.16: a bound on the INTEGRAND bounds the
    ;; CARATHEODORY WITNESS, on the whole interval and by the same constant.
    ;; Def 4.6's two clauses re-stated on a SUBINTERVAL (they have different
    ;; shapes, so each transfers its own way), `mvt-abs-bound' cited there, and
    ;; the factor |x - t| taken off the witness identity by
    ;; `rr-nonneg-cancel-pos'.  `trust: well-known', all of it inherited from the
    ;; MVT arc.  Carries with it Prop 4.16's own increment display
    ;; (antiderivative-pair-close): two antiderivatives AGREEING AT a whose
    ;; integrands are within M on [a,b] are within M.(b-a) on [a,b] -- the
    ;; difference by Prop 4.8, the Lipschitz bound based at a, and one product
    ;; monotonicity.  Needs antiderivative and antiderivative-transfer
    ;; (antiderivative-sub) directly above, mvt-abs-bound, ccint-basics,
    ;; rr-abs-basics, rr-order-basics (rr-lt-trichotomy, rr-nonneg-cancel-pos,
    ;; rr-le-scale-nonneg), equality-basics (eq-sym) and binary-minus-laws.
    "theorem-library/antiderivative-lipschitz"
    ;; The two families Prop 4.16 builds by CHOICE: the antiderivatives of a
    ;; sequence of antiderivable functions, and the Caratheodory witnesses of a
    ;; sequence of maps differentiable at one point.  Both hypotheses are a
    ;; universally quantified EXISTENTIAL and every consumer
    ;; (`uniform-limit-continuous-at', `diff-at-ptwise-limit') wants a FUNCTION
    ;; on NN; the bridge is `choose!' plus a VNB-LAMBDA.  Both `modulo 0', and
    ;; both conclude with a FORSOME so the CHOICE term never escapes.
    ;; Needs antiderivative + differentiation + metric-continuity and
    ;; driver-kit (choose!, in-sep!, dk-lam-t!).
    "theorem-library/witness-family-choice"
    ;; SHIFTING an antiderivative by a constant, and the NORMALISED
    ;; antiderivative family that follows.  Prop 4.16's second hypothesis --
    ;; "the sequence f_k(a) is convergent" -- is not implied by the other two
    ;; and Cor 4.17 has none to offer, so the constants are CHOSEN rather than
    ;; assumed: each antiderivative is normalised to vanish at a.  The shift
    ;; itself was missing from the tree (Prop 4.10 is its converse) and is
    ;; proved by Prop 4.8 against the constant map plus the two-slot pointwise
    ;; transfer.  Both `modulo 0'.  Needs antiderivative-transfer and
    ;; witness-family-choice above, continuity-basics (const-lam-in-fun,
    ;; const-continuous-at) and differentiation (deriv-const).
    "theorem-library/antiderivative-normalize"
    ;; docs/calculus.pdf PROP 4.16 and COR 4.17 -- THE ANTIDERIVABLE FUNCTIONS
    ;; ARE CLOSED UNDER UNIFORM LIMITS, which is rung 3 of the integration arc.
    ;; The mechanism is `uniform-cauchy-limit' (a uniformly Cauchy family of
    ;; maps has a uniform limit, on an ARBITRARY domain), used twice: for the
    ;; CLAMPED antiderivative family on all of RR -- the clamp is what makes the
    ;; limit continuous at the ENDPOINTS, where a limit built on [a,b] alone is
    ;; unconstrained -- and for the Caratheodory WITNESS family on [a,b], whose
    ;; uniform Cauchyness comes from `caratheodory-witness-pair-bound'.
    ;; `diff-at-local' is NOT cited: `diff-at-ptwise-limit' already absorbs it
    ;; once the clamped family is what it is fed.  `trust: well-known', all of
    ;; it inherited (the MVT arc, and rr-le-all-pos-nonpos through seq-limit-core).
    ;; Needs antiderivative-normalize directly above (antiderivable-family-
    ;; normalized), antiderivative-lipschitz (antiderivative-pair-close,
    ;; caratheodory-witness-bound), witness-family-choice, antiderivative-
    ;; transfer (antiderivative-sub), clamp, seq-limit and seq-limit-core,
    ;; uniform-limit-local,
    ;; diff-at-local, rr-null-scale (rr-scale-eps) and ccint-basics.
    "theorem-library/antiderivable-uniform-limit"
    ;; A FINITE SUM of antiderivable terms is antiderivable
    ;; (series-partial-sum-antiderivable): Prop 4.8's two-term closure lifted to
    ;; n terms by induction on the number of terms.  This is the theorem
    ;; `poly-is-antiderivable' should have been -- nothing in it is about
    ;; polynomials -- and it is what the Bernstein rung needs, BERNSTEIN-POLY
    ;; being a SERIES-PARTIAL-SUM already.  Carries with it the four pieces that
    ;; make such an induction writable: the projection
    ;; (antiderivable-fn-in-fun), the INTEGRAND transfer at both levels
    ;; (antiderivative-/antiderivable-integrand-transfer, the `==' form of the
    ;; f = g case of antiderivative-transfer-ptwise-eq just above), the
    ;; packaging of a global derivative (antiderivable-from-deriv) and the two
    ;; base cases (zero-is-antiderivable, power-antiderivable) -- plus Example 4.7
    ;; DERIVED from the finite-sum theorem (poly-fn-antiderivable), which is
    ;; there as evidence that section 5 is the general statement.  All `modulo 0'.
    ;; Needs antiderivative + antiderivative-transfer above,
    ;; comparison-test-proof (series-partial-sum-zero/-succ), series-linearity
    ;; (series-partial-sum-in-rr-ptwise), differentiation (deriv-const,
    ;; diff-implies-continuous), poly-antiderivative (deriv-anti-monomial),
    ;; ccint-basics (ccint-membership) and dyadic-weights (power-closed-at).
    "theorem-library/series-antiderivable"
    ;; calculus.pdf ch.4, equation (64): C-INT, the DEFINITE INTEGRAL of a
    ;; continuous function, DEFINED by definite description over the endpoint
    ;; difference of an antiderivative -- Cor 4.11 (antiderivative.scm) is
    ;; `iota-def''s uniqueness obligation verbatim.  Existence (rung 3: every
    ;; continuous function is antiderivable) is NOT needed to define it: the
    ;; IOTA is undefined where phi is not antiderivable, the tree's normal
    ;; treatment of a partial function.  Proves (64) itself (c-int-value), the
    ;; definedness (c-int-in-rr) and Props 4.12/4.13, linearity (c-int-add,
    ;; c-int-scale).  Bills exactly what Cor 4.11 bills and nothing more.
    ;; Needs antiderivative directly above, equality-basics and
    ;; fun-apply-type-proof.
    "theorem-library/c-int"
    ;; THE ORIENTED DEFINITE INTEGRAL, Remark 4.9, and ADDITIVITY IN THE BOUNDS.
    ;; IS-ANTIDERIVATIVE carries `a < b' deliberately (deriv-zero-implies-constant
    ;; and the two MVT bounds all want it), so C-INT(phi,a,b) cannot be written at
    ;; a = b or at b < a and int_a^a = 0, int_b^a = -int_a^b and
    ;; int_a^c = int_a^b + int_b^c cannot be STATED.  C-INT-OR is the wrapper:
    ;; SEQ-LIMIT's totalising IF, branching on IS-ANTIDERIVABLE (which already
    ;; entails a < b) rather than on the order, so the functoid is TOTAL -- which
    ;; is what lets it stand in a VNB-LAMBDA over all of RR, i.e. what LOG needs.
    ;; Nothing existing is touched: the bridge c-int-or-anti carries every c-int-*
    ;; result over by one `subst'.  Remark 4.9 (antiderivative-subinterval) is
    ;; free here -- both containments, closed and open, follow from a <= lo < hi <= b
    ;; -- and with it c-int-or-value gives f(b) - f(a) for ANY two points of the
    ;; ambient interval, so additivity is one `crs' with no ordering hypothesis.
    ;; Needs c-int directly above, antiderivative, ccint-basics, rr-order-basics
    ;; and fun-apply-type-proof.
    "theorem-library/c-int-oriented"
    ;; Theorem 5.2 transferred from [0,1] to [a,b] by the affine change of
    ;; variable, plus the five interval lemmas it needs.  Needs
    ;; bernstein-density, directional-derivative (deriv-affine, affine-lam-in-fun),
    ;; continuity-compose, compose-apply-proof and ccint-basics.
    "theorem-library/bernstein-ccint"
    ;; batch 8 (2026-09-19): rr-archimedean-multiple, and the eps-GRID finite cover of a closed interval
    ;; (ccint-eps-grid-cover-at by induction on the cell count -- no floor function --, ccint-eps-grid-cover,
    ;; ccint-grid-cover-seq: one cover per radius, the shape block-family-combinatorial consumes).  The floor of
    ;; Bolzano-Weierstrass; nothing in the tree built a finite cover of a bounded real set before.
    "theorem-library/rake-bolzano-weierstrass"
    ;; BOLZANO-WEIERSTRASS (2026-09-19): rr-interval-seq-has-convergent-subseq (codomain CCINT(lo,hi)),
    ;; rr-bolzano-weierstrass (the abs-bounded form to cite), bounded-block-converges (the block form the Ascoli
    ;; tower consumes).  Grid covers -> block-family-combinatorial -> diagonalization -> rr-cauchy-converges.
    "theorem-library/rake-bolzano-weierstrass-2"
    ;; ASCOLI-ARZELA (2026-09-20, batch 11-F): ascoli-pointwise-diagonal (from POINTWISE-BOUNDED and a dense
    ;; sequence alone: one dc-on-nn-pred whose totality is bounded-block-converges, then diagonalization +
    ;; coord-block-estimate), and ascoli-arzela-sequential itself, modulo 0, in two citations from
    ;; ascoli-sequential-from-diagonal (rake-ascoli).  The support of that name is retired.
    "theorem-library/rake-ascoli-diagonal"
    ;; EVERY BERNSTEIN APPROXIMANT IS ANTIDERIVABLE (rung 3(b)).  There is no
    ;; closed form for the Bernstein basis in this tree -- BERNSTEIN-BASIS is
    ;; COMB-KK, a Pascal recursion, and no C(n,k) exists anywhere -- so the
    ;; route is the RECURRENCE, under a hypothesis strong enough to survive the
    ;; multiplication by x that the recurrence performs:  x |-> x^j B_{k,n}(x)
    ;; is antiderivable, for every k and j at once.  Three instances of that per
    ;; step, combined by antiderivable-add / -sub and carried onto the goal by
    ;; the integrand transfer.  BERNSTEIN-POLY then follows from
    ;; series-partial-sum-antiderivable directly, that theorem being stated in
    ;; TRANSFER form: BERNSTEIN-POLY is a def-functoid and supplies the pointwise
    ;; equation from its own unfold.  Needs bernstein-basis, bernstein-moments
    ;; (bernstein-basis-succ/-null/-ptwise-in-rr), bernstein-density
    ;; (BERNSTEIN-POLY), series-antiderivable, antiderivative,
    ;; antiderivative-transfer, series-linearity and nn-parity-proof.
    "theorem-library/bernstein-antiderivable"
    ;; ANTIDERIVABILITY SURVIVES AN AFFINE CHANGE OF VARIABLE (rung 3(c)).
    ;; bernstein-uniform-approximation-ccint's approximant is
    ;; BERNSTEIN-POLY(f o A, n, U(x)) -- a Bernstein polynomial in the UNIT
    ;; coordinate -- while bernstein-poly-antiderivable is about
    ;; x |-> BERNSTEIN-POLY(g, n, x).  The bridge is the substitution lemma:
    ;; phi antiderivable and A affine with A' /= 0 give t |-> phi(A(t))
    ;; antiderivable, with antiderivative recip(lam).(Phi o A).  No analysis:
    ;; deriv-chain over deriv-affine, scaled by deriv-scalar-mult, and
    ;; compose-continuous-at over affine-continuous-at, scaled by
    ;; scale-continuous-at.  Four theorems -- the lam /= 0 engine, the 0 < lam
    ;; specialisation that computes the image interval, its TRANSFER form (which
    ;; is what avoids a redex under a binder; see the file header) and the rung.
    ;; Needs bernstein-antiderivable directly above, bernstein-ccint
    ;; (ccint-parts, affine-continuous-at), chain-rule, directional-derivative,
    ;; deriv-polynomial (deriv-scalar-mult), continuity-scale, continuity-compose,
    ;; compose-apply-proof, antiderivative and series-antiderivable.
    "theorem-library/antiderivable-affine-subst"
    ;; RUNG 3 and the integral that follows.  Corollary 4.17 (the antiderivable
    ;; functions are closed under uniform limits) applied to the approximating
    ;; sequence of Theorem 5.2 gives: every continuous function on [a,b] is
    ;; ANTIDERIVABLE there (continuous-is-antiderivable), and hence its definite
    ;; integral is defined (c-int-defined-for-continuous) and Props 4.12/4.13
    ;; hold with CONTINUITY, not antiderivability, as the caller's hypothesis
    ;; (c-int-add-continuous, c-int-scale-continuous).  No analysis: the family
    ;; is re-indexed off zero (the degree-0 approximant is excluded by
    ;; bernstein-poly-antiderivable's n /= 0) and the threshold shifts with it.
    ;; Needs antiderivable-affine-subst directly above
    ;; (bernstein-ccint-approximant-antiderivable), bernstein-ccint
    ;; (bernstein-uniform-approximation-ccint), antiderivable-uniform-limit
    ;; (Cor 4.17, antiderivable-fn-in-fun) and c-int.
    "theorem-library/continuous-antiderivable"
    ;; CHANGE OF VARIABLES for C-INT, increasing case:
    ;;   C-INT(t |-> phi(A(t)).A'(t), p, q) = C-INT(phi, A(p), A(q)).
    ;; Two citations: deriv-chain makes F o A an antiderivative of the left
    ;; integrand on [p,q], and c-int-value evaluates both sides to
    ;; F(A(q)) - F(A(p)).  Restricted to A(p) < A(q) because IS-ANTIDERIVATIVE
    ;; hard-codes a < b; the decreasing and degenerate cases belong to C-INT-OR.
    ;; The interval containment is handed in as TWO universals (closed into
    ;; closed, open into open), which is what keeps it sign-agnostic.  Needs
    ;; c-int (c-int-value), chain-rule (deriv-chain), continuity-compose,
    ;; compose-apply-proof, antiderivative, series-antiderivable
    ;; (antiderivative-integrand-transfer) and equality-basics.
    "theorem-library/c-int-change-of-variable"
    ;; THE LOGARITHM, defined as the oriented integral of the totalised
    ;; reciprocal from 1, and its basic laws.  Both halves of the definition are
    ;; TOTAL and both have to be: recip-star-lam-in-fun is unconditional (the
    ;; bare z |-> recip(z) is not in FUN(RR,RR)) and c-int-or-in-rr is
    ;; unconditional (an order-branching wrapper would leave the body undefined
    ;; at every x <= 0), so LOG is a member of FUN(RR,RR) on the nose.  The
    ;; functional equation log(x.y) = log x + log y is the change of variables
    ;; t = x.u: c-int-change-of-variable-transfer supplies the VALUE (the
    ;; antiderivable-affine-subst family concludes only that an antiderivative
    ;; EXISTS, which cannot reach an equation between integrals), the pointwise
    ;; equation it wants is recip*(lam.u).lam = recip*(u) -- true at EVERY real,
    ;; 0 included, which is the totalisation paying for itself -- and the
    ;; interval bookkeeping is antiderivable-affine-subst-pos's section 2
    ;; reproduced.  The orientation makes the rest free: c-int-or-value has no
    ;; ordering hypothesis, so nothing asks whether y is above or below 1.
    ;; Also the FTC (log' = recip*, through diff-at-local, IS-DIFF-AT being
    ;; GLOBAL where log agrees with an antiderivative only on an interval),
    ;; strict monotonicity (mvt-lower-bound over rr-recip-antitone) and
    ;; log(1/x) = -log(x).  Needs c-int-change-of-variable directly above,
    ;; continuous-antiderivable, c-int-oriented, recip-star, diff-at-local,
    ;; mvt-bounds-proof, bernstein-ccint (affine-continuous-at),
    ;; directional-derivative, continuity-basics (const-lam-in-fun),
    ;; sequential-continuity (rr-recip-antitone), rr-halving, rr-recip-order,
    ;; rr-abs-basics (rr-abs-bound), rr-order-basics and ccint-basics.
    "theorem-library/log"
    ;; THE REAL EXPONENTIAL, defined as the INVERSE of the logarithm:
    ;; R-EXP(y) == IOTA x. x in RR and 0 < x and LOG(x) = y.  The name is
    ;; R-EXP and not EXP so that the complex exponential can have the plain
    ;; name later, as C-INT does against the measure-theoretic INTEGRAL.
    ;; The description describes because LOG is SURJECTIVE onto RR, which
    ;; nothing in the tree said and which is the only real work in the file:
    ;; a DOUBLING INDUCTION (b := 1 at 0, b |-> 2b at the step, log(2b) =
    ;; log 2 + log b) makes log unbounded above WITHOUT the term 2^n and so
    ;; without `power' at all, log-recip mirrors it downwards, and `ivt'
    ;; fills in between -- log being continuous on [a,b] because it is
    ;; DIFFERENTIABLE there (log-deriv + diff-implies-continuous).
    ;; `deriv-inverse' (inverse-function.scm) CANNOT be cited: it asks for a
    ;; bijection of RR, and R-EXP(LOG(x)) = x is FALSE off the positives --
    ;; `r-exp-log-not-global' proves the negation, from the positivity of
    ;; R-EXP's values alone.  `deriv-right-inverse' here is `deriv-inverse'
    ;; with that global hypothesis weakened to the single equation
    ;; g(f(a)) = a, which is all its proof ever used; inverse-function.scm is
    ;; untouched.  `diff-at-local' is NOT needed -- log's Caratheodory
    ;; identity is global and is only ever instantiated at points R-EXP(z),
    ;; every one of them positive.  Continuity of R-EXP is pure monotonicity.
    ;; Needs log directly above, ivt-proof, inverse-function (rr-recip-solve),
    ;; continuity-compose, continuity-recip, recip-star, compose,
    ;; rr-metric-space-proof, rr-ms-dist, rr-abs-basics, rr-order-basics,
    ;; rr-halving and ccint-basics.
    "theorem-library/r-exp"
    ;; THE REAL POWER, DEFINED, with the base-zero conventions CARRIED:
    ;;   RPOW-STAR(x,s) == IF 0 < x then R-EXP(s . LOG x)
    ;;                     else IF 0 < s then 0 else 1
    ;; The user's definition (2026-08-26) in the shape they specified on the
    ;; 27th.  Name per the tree's convention for a DEFINED companion to an
    ;; AXIOMATISED operator (CARD/CARD-STAR, MUL-INV/RECIP-STAR);
    ;; structure-library/real-powers.scm is NOT touched, its RPOW keeping its
    ;; fourteen supports and its one customer (Hoelder).
    ;; WHY AN IF AND NOT A DESCRIPTION.  The instinct is that x^s is UNDEFINED
    ;; at x = 0.  In THIS tree it is not: **LOG is TOTAL** -- log-in-rr reads
    ;; `forall([x_], log(x_) in rr)' with no guard, because RECIP-STAR is the
    ;; totalised reciprocal and C-INT-OR's third branch returns 0 when the
    ;; integrand is antiderivable in NEITHER direction.  So R-EXP(s . LOG 0)
    ;; was already a defined POSITIVE real: there was never a hole at x = 0,
    ;; only junk.  The conventions are therefore ADOPTED, and the IF is the
    ;; house pattern for adopting one -- RECIP-STAR and C-INT-OR, the two
    ;; functoids LOG is built from, are both total-by-IF.
    ;; THE THIRD BRANCH IS A DON'T-CARE and no theorem mentions it: it fires at
    ;; 0^0, where it delivers the adopted 1, AND at 0^(-1), where 1 is not a
    ;; convention anyone holds.  So rpow-star-zero-zero is stated AT 0^0, not
    ;; as the else-branch, and 0^(-1) stays unspecified -- exactly as RPOW is
    ;; careful to say nothing about a negative exponent at base zero.
    ;; WHAT THE CONVENTIONS COST: the six laws that used to hold at EVERY real
    ;; base do not survive.  At x = 0, s = 1, t = -1: 0^(1+(-1)) = 0^0 = 1
    ;; while 0^1 . 0^(-1) = 0 . 1 = 0, so rpow-star-add is FALSE at base 0 and
    ;; every law now carries `0 < x'.  That is the arithmetic of the
    ;; conventions breaking the algebra at zero, which is why 0^0 is
    ;; contentious at all -- not a defect of the shape.
    ;; THREE BRANCH EQUATIONS (rpow-star-value, -zero-base, -zero-zero) are
    ;; proved once and the IF is never opened again -- c-int-oriented.scm's
    ;; discipline, and what keeps the conventions from leaking a case split
    ;; into every driver downstream.
    ;; Nothing is asserted.  The two conventions are `modulo 0'; everything
    ;; through the main branch inherits the 35-leaf `well-known' log/r-exp
    ;; residue unchanged and adds nothing.  Needs r-exp directly above, log,
    ;; recip-star, rr-order-basics (rr-lt-scale-pos, rr-mul-comm, rr-lt-irrefl)
    ;; and driver-kit.
    "theorem-library/rpow-star"
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
    ;; rake batch 6 (2026-09-19): the three leaves of metrizable-iff-bounded-metrizable.  After bdd-metric-convergence.
    "theorem-library/rake-bdd-metric"
    "theorem-library/metrizable-bounded-proof"
    ;; A ringoid's congruence (a ~ b iff a-b in the ideal) is an equivalence
    ;; relation, so RINGOID-SETOID is a setoid.  Needs structure-library/ringoid.
    "theorem-library/ringoid-setoid-proof"
    ;; rake batch 5b (2026-09-18): rq-add-computes
    "theorem-library/rake-ringoid"
    ;; rake batch 5c (2026-09-18): rq-mul/neg-computes, ringoid-quotient-is-ring
    "theorem-library/rake-ringoid-quotient"
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
    ;; Assumption-pattern scanner for forward-move discovery
    ;; (used by Emacs vnb-suggest-forward-moves).
    "suggest"
    ;; The MEASURED citation index: P(theorem cited | head in the goal's
    ;; statement), computed in one pass over the 464 scripts every `qed' files
    ;; in `*proof-script-table*'.  It is what the hand-written vocabulary filter
    ;; and the ubiquitous-head blacklist in `suggest' are crude guesses at, and
    ;; unlike them it is recomputed from the live tables, so it cannot drift.
    ;; Built LAZILY on first use: the library proofs load hundreds of lines
    ;; below this point, so there is nothing to count at load time.  Loads after
    ;; `suggest' because it reads `what-now--heads-of' rather than copying it.
    "cite-index"
    ;; The What Now lane that SUPPLIES the inequalities `ineq' cannot see.  The
    ;; oracle linearizes over + - * and treats max(a,b) and (dist(s))(x,y) as
    ;; opaque atoms, so it cannot know `a <= max(a,b)' or the triangle
    ;; inequality; this names the citations that land them -- with the `in rr'
    ;; certificate each atom needs, and the class bridge that turns
    ;; `m in metric-space' into `is-metric-space(m)' -- and then the `ineq' call
    ;; with its premises NAMED, which is the difference between closing the goal
    ;; and not.  Curated, not measured.  Needs `suggest' (vnb--scratch-state,
    ;; vnb--probing, what-now--subterms); the lemma names resolve at call time,
    ;; so the theorem files it cites load later.
    "ineq-supply"
    ;; (proof-map) -- a READ-ONLY view of the whole proof tree, closed branches
    ;; included.  Every other view -- (proof-leaves), the Focus panel, (show) --
    ;; shows only OPEN leaves, so a closed branch vanishes and "is the base case
    ;; actually finished?" had no direct answer.  Needs interactive (*ps*) and
    ;; deduction-graphs.
    "proof-map"
    ;; (contra) -- close a branch whose CONTEXT is arithmetically inconsistent,
    ;; the shape a case split or a membership unfold leaves behind.  Certifies
    ;; the inconsistency with the `ineq' oracle over ALL assumptions (it now
    ;; skips the non-arithmetic ones) and then discharges through have!/ai, so
    ;; it adds no trust beyond ineq's.  Probes on a scratch state before it
    ;; commits -- there is no undo -- which is why it must come after `suggest'
    ;; (vnb--scratch-state) and after driver-kit (have!).
    "contra"
    ;; geometric-series -- THE GEOMETRIC MAJORANT, PROVEN, with rr-abs-power,
    ;; rr-power-nonneg and the division-free partial-sum identity under it.
    ;; `geometric-partial-sum' is retired from power-series here.  The ratio
    ;; test's warrant claimed its chain was "assembled": comparison-test was,
    ;; the majorant was not -- both geometric lemmas were asserted, and the
    ;; value form waits on `r^k -> 0', which is still not in the tree.  What is
    ;; proven here is the half the ratio test consumes: CONVERGENCE of the
    ;; majorant, by monotone convergence, which needs no limit of r^k.
    ;; Needs monotone-convergence-proof, comparison-test-proof, dyadic-weights
    ;; (power-real-closed), rr-order-basics (rr-le-scale-nonneg), rr-recip-order
    ;; and `contra' immediately above; must PRECEDE pss-topics.
    "theorem-library/geometric-series"
    ;; 2026-09-24 (batch 25-A): the lim sup facts of the notes' Remark 2.6 (through ELIMSUP on [0, +inf]), EINF laws,
    ;; THE ROOT TEST (2.5) and THE RATIO TEST (2.15) for non-negative real series -- the divergence half with lim INF > 1,
    ;; the notes' lim sup form being false as printed.
    "theorem-library/limsup-tests"
    ;; ps-series-bridges -- the three PS/series bridges, PROVEN, plus the
    ;; CONVERGES twin of rr-limit-ptwise-eq that the third needs.  They are what
    ;; lets a theorem about bare series be USED about a power series.  Two are
    ;; the definitional one-liners their warrants described; the third is not,
    ;; because `mac' will not descend into a VNB-LAMBDA body -- the two sides
    ;; are related pointwise instead.  Needs geometric-series (rr-abs-power)
    ;; immediately above, comparison-test-proof and limit-arithmetic.
    "theorem-library/ps-series-bridges"
    ;; 2026-09-24 (batch 27-A): ratio-test-converges PROVEN literally from ratio-test-converges-limsup
    ;; (support in power-series.scm retired); elimsup-eventually-le.  Needs ps-series-bridges, limsup-tests.
    "theorem-library/ratio-test-proof"
    ;; rake batch 5 (2026-09-18): little-o, ps-absolute-implies-convergent, vtaylor-clear
    "theorem-library/rake-series"
    ;; rake batch 5c (2026-09-18): chain triangle inequality, summable-bound-implies-cauchy, r^k -> 0, geometric series
    "theorem-library/rake-series2"
    ;; 2026-09-20 (batch 12-B): Heine-Borel for a closed interval AS A SPACE.
    "theorem-library/heine-borel-interval"
    ;; 2026-09-21 (batch 14-A): CC and cartesian(rr, rr): bijections, coordinate laws, transfer of convergence, continuity, differentiability.
    "theorem-library/cc-coords-laws"
    ;; 2026-09-21 (batch 14-C): IS-CC-DIFF-AT: continuity, constants, complex multiples, difference, uniqueness, chain rule with a real inner map.
    "theorem-library/cc-diff-laws-2"
    ;; 2026-09-21 (batch 15-B): THE DEFINITIONS OF THE INTEGRAL ALONG A PATH, for functions ON [a, b]
    ;; (docs/paths-and-line-integrals-2026-09-21.md 3.2-3.4): IS-PW-CONTINUOUS-ON, PW-INT (over IS-PRIMITIVE since batch 20),
    ;; CC-INT (the notes' eq. 44), IS-PATH, IS-ROAD, TRACE, LINE-INT; witnesses (an affine primitive, the segment
    ;; as a road).  RESTATED 2026-09-22 (batch 16-A): the exceptional set is a finite SET (Dieudonne's D), not an
    ;; enumeration; PW-INT's uniqueness is PROVEN (`pw-zero-deriv-off-finite-set', by finite-set-induction) and
    ;; `pw-int-value' is unconditional.
    "structure-library/path-integral"
    ;; 2026-09-25 (batch 30, the user's decisions, docs/goursat-definitions-2026-09-25.md): the segment as a road on
    ;; [0,1] (SEG-PATH, SEG-DERIV, SEG-INT), the triangle integral as the sum of three segment integrals (TRI-INT),
    ;; CC-MID, the convex hull of three points CONV3 (a SEP over CC), IS-CONVEX. No diameter, no length.
    "structure-library/segments-triangles"
    ;; 2026-09-23 (batch 20-D): the laws of the vocabulary above -- countable sets (finite => countable, subset,
    ;; union, image), continuity gives both one-sided limits, uniqueness of a one-sided limit within an interval,
    ;; restriction, the read-offs of IS-PRIMITIVE, and the bridge pw-antiderivative-implies-primitive.
    "theorem-library/regulated-primitive-laws"
    ;; 2026-09-23 (batch 22-A): Dieudonne (7.6.1), NECESSITY -- a function regulated ON [a, b] is the uniform
    ;; limit on [a, b] of step functions (regulated-on-is-step-limit; the one-eps form regulated-on-step-approx),
    ;; by the creeping argument: every partition grows by one point at the right end, nothing is sorted.
    "theorem-library/regulated-step-approx"
    "theorem-library/has-deriv-at-more"
    ;; 2026-09-22 (batch 18-A): THE CHAIN RULE for the local derivative (calculus 2.3, Prop 2.8) and its affine corollary.
    "theorem-library/has-deriv-at-chain"
    ;; 2026-09-22 (batch 16-B/16-C): THEOREM 2.18 of the calculus notes (Taylor with a general G; both forms of
    ;; (20)) and 2.19 (Lagrange), for functions ON [a, b]; from `generalized-mvt-on-interval', as in the notes.
    "theorem-library/interval-taylor"
    ;; 2026-09-23 (batch 20-A): Dieudonne (8.5.2) / (8.5.3) and the remark after (8.6.1) with a COUNTABLE
    ;; exceptional set: the mean value inequality (mvi-off-countable, mvi-abs-off-countable), monotonicity
    ;; (neg-deriv-off-countable-nonincreasing), constancy (zero-deriv-off-countable, the drop-in for
    ;; pw-zero-deriv-off-finite-set, and -constant ON [a, b]); on the way, an open interval is not countable
    ;; (rr-interval-avoids-sequence, by nested intervals and dc-on-nn-pred, no 2^-n series).
    "theorem-library/zero-deriv-off-countable"
    ;; (loads AFTER zero-deriv-off-countable since 2026-09-23, batch 21: its uniqueness argument cites
    ;; `zero-deriv-off-countable'; `pw-lt-ne' moved the other way.)
    "theorem-library/pw-antiderivative-laws"
    "theorem-library/cc-int-laws"
    "theorem-library/road-laws"
    ;; 2026-09-22 (batch 17-A): the integral on [a, b]: scalar multiple (the notes' Prop 4.12 with the sum),
    ;; Prop 4.10 in full, Remark 4.9 (restriction to a subinterval), additivity over adjacent intervals;
    ;; CC-INT: eq. (44) as a value law, sum, real multiple.
    "theorem-library/pw-int-laws-2"
    ;; 2026-09-24 (batch 25-B): THE TAYLOR CLUSTER of the calculus notes -- 2.3 the k-th derivative of x^n (the notes'
    ;; (8) misprinted), 2.16 the interpolating polynomial (uniqueness on coefficients), 2.20 the sup bound for the
    ;; remainder, 2.21 the continuous remainder factor, 2.22 Taylor exact for a polynomial (either sign of h).
    "theorem-library/taylor-cluster"
    ;; 2026-09-23 (batch 22-C): primitives GLUE over adjacent intervals (primitive-glue: the pieces given by
    ;; agreement clauses, the joint into the countable exceptional set); a step function has a primitive on
    ;; [a, b] (step-fn-has-primitive, by induction over the partition, IS-PARTITION total on NN).
    "theorem-library/primitive-glue"
    ;; 2026-09-22 (batch 18-A): pw-antiderivative-linear (Prop 4.12 in one formula); CC-INT is linear over CC
    ;; (the sentence after (44)); CC-INT additivity over adjacent intervals.
    "theorem-library/pw-int-laws-3"
    ;; 2026-09-23 (batch 22-B): Dieudonne (8.6.4) on [a, b] with COUNTABLE exceptional sets -- a uniform limit
    ;; of primitives is a primitive (primitive-uniform-limit, normalised at g_k(a) = 0); on the way
    ;; countable-union-nn (an NN-indexed union of countable sets, by nn-flatten) and the Cauchy estimate
    ;; primitive-pair-lipschitz from the mean value inequality.
    "theorem-library/primitive-uniform-limit"
    ;; 2026-09-24 (batch 25-A): POWER SERIES IN CC -- the definitions (CPS-RADIUS as the sup of the r with sum |a_k| r^k
    ;; convergent, CC-SUP-NORM (29), IS-NORMALLY-CONVERGENT, CC-SERIES-LIMIT; structure-library/cc-power-series.scm, after
    ;; theorem-library/cc-series) and the laws: the radius formula 2.7, normal convergence inside the radius 2.8,
    ;; polynomial factors 2.9; 2.10 follows in cc-power-series-deriv (batch 26-A).
    "structure-library/cc-power-series"
    "theorem-library/cc-power-series-laws"
    ;; 2026-09-24 (batch 26-A): THE NOTES' 2.10 -- the sum function of a complex power series is holomorphic on
    ;; B(0, r) for every r < R, the derived series has the same radius, f' = sum (k+1) a_(k+1) u^k
    ;; (cps-holomorphic-ball, cps-radius-derived, cps-diff-on-ball); on the way domination from some index on
    ;; (series-domination.scm), the second-order power estimate, cc-series-limit-linear, cc-diff-on-quadratic.
    "theorem-library/series-domination"
    "theorem-library/cc-power-series-deriv"
    ;; 2026-09-24 (batch 27-A): the notes' 2.14 (cps-taylor-coefficients, cps-coefficient-formula) with f^(k)
    ;; read as the sum of the k-th derived series; the tree has no iterated derivative over CC.
    "theorem-library/cps-taylor-coefficients"
    ;; 2026-09-23 (batch 22-D): DIEUDONNE (8.7.2) -- every function regulated on [a, b] has a primitive
    ;; (regulated-on-has-primitive), assembled from 22-A, 22-C and 22-B; a primitive shifted by a constant is a
    ;; primitive (primitive-shift-const); one normalised primitive per index by CHOICE.
    "theorem-library/regulated-has-primitive"
    ;; 2026-09-22 (batch 18-C): THE OPPOSITE ROAD is a road, and Dieudonne (9.6.1): the integral along it is
    ;; minus the integral along the road; PW-INT and CC-INT under the reflection t |-> a + b - t.
    "theorem-library/road-laws-2"
    ;; 2026-09-23 (batch 19-B): the notes' Prop 3.2, THE FUNDAMENTAL THEOREM FOR LINE INTEGRALS: the integral of
    ;; f' along a road in the open set U where f is holomorphic is f(gamma(b)) - f(gamma(a)); before it, the MIXED
    ;; chain rule (holomorphic f composed with a road, coordinatewise, at the Caratheodory level: holomorphic-chain).
    ;; No primitive of the integrand is assumed: f o gamma IS the primitive.
    "theorem-library/line-int-fundamental"
    ;; 2026-09-25 (batch 29-B): the bricks of Goursat -- Cor 3.3 for a closed road (line-int-closed-road-of-derivative,
    ;; affine-closed-road-integral, affine-has-primitive-cc), the Caratheodory remainder bound (65) without phi
    ;; (caratheodory-remainder-small), the vertex-sequence lemma (cc-telescoping-limit-bound), quarter-step,
    ;; four-power-halving.
    "theorem-library/goursat-bricks"
    ;; 2026-09-23 (batch 23-A): THE INTEGRAL ALONG A ROAD EXISTS (Dieudonne IX.6 after (8.7.2)): the algebra of
    ;; regulated functions on [a, b] through one-sided limits within a set (sum, sub, mul, scalar, congruence), a
    ;; continuous function of a path is regulated, the road integrand is regulated (road-integrand-regulated),
    ;; and line-int-exists delivers the two primitives every cc-int / line-int law takes as antecedents; line-int-in-cc.
    "theorem-library/regulated-algebra"
    ;; 2026-09-22 (batch 18-B): calculus 3.19 (the continuous image of a compact set is compact) and the trace of
    ;; a path is compact; "derivative >= 0 off a finite set => nondecreasing", monotonicity of PW-INT,
    ;; |pw-int(phi)| <= pw-int(|phi|); the notes' estimate (45) for CC-INT.
    "theorem-library/compact-image"
    "theorem-library/pw-int-order"
    "theorem-library/cc-int-estimate"
    ;; 2026-09-23 (batch 24-A): the laws of the line integral for a ROAD and a CONTINUOUS f, no primitive in the
    ;; statement (line-int-sum, -scalar, -opposite-road (9.6.1), -adjacent, -abs-bound (54), -value); on the way
    ;; road-restrict, cc-int-congruence, and the modulus of a CC-valued regulated function is regulated.
    "theorem-library/line-int-laws"
    ;; 2026-09-25 (batch 29-A): the affine reparametrisation of PW-INT / CC-INT / LINE-INT (the notes' (48), affine
    ;; case: pw-int-affine-subst, cc-int-affine-subst, road-affine-reparam, line-int-affine-reparam), Lemma 3.4 in the
    ;; segment's shape (segment-int-split), the segment estimate (54) (segment-int-abs-bound), segment-int-reverse.
    "theorem-library/line-int-reparam"
    ;; 2026-09-25 (batch 30): CAUCHY-GOURSAT. Lemma 3.4 with the segment object (seg-int-split-at), Lemma 3.5
    ;; (tri-int-subdivision), Prop 3.6 for f holomorphic on U (goursat-triangle; the common point of the nested
    ;; triangles by the vertex sequence on the standard triangle, goursat-nest: no Cantor intersection, no compactness),
    ;; Cor 3.7 (cauchy-convex-segments), Prop 3.8 (cauchy-convex-primitive), Cor 3.9 (cauchy-convex-closed). The
    ;; heaviest file of the tree: ~15 min of proofs + ~8 min of page audit in an exam load; certified otherwise.
    "theorem-library/goursat"
    ;; 2026-09-25 (batch 31-A, the user's decision): exp, cos, sin on CC DEFINED BY THEIR POWER SERIES
    ;; (the notes' 2.3.1-2.3.2), then Lemma 2.16, exp' = exp, (33) exp(z+w) = exp z exp w by the zero-derivative
    ;; route along a segment, Prop 2.17 as its equations, conjugation, (34), (35) in its true form, the derivatives
    ;; of sin and cos, the addition formulas, cos^2 + sin^2 = 1.
    "structure-library/cc-elementary"
    "theorem-library/cc-exp"
    ;; 2026-09-25 (batch 31-B, the user's decision): PI is the positive real p with {z : exp z = 1} = ZZ (2 p i), i.e.
    ;; the upper-half-plane generator of the kernel divided by 2i (IOTA-bodied def-constant; existence and uniqueness
    ;; proven first); Lemma 2.18 (cc-exp-one-iff), the injectivity half of Prop 2.19 (cc-exp-injective-strip),
    ;; exp(i pi) = -1, cos(pi/2) = 0, sin(pi/2) = 1, the tail bound cc-series-ratio-tail.
    "structure-library/cc-pi"
    "theorem-library/cc-exp-kernel"
    ;; preamble -- a STRATEGY, executed: (preamble '(induct) '(unfold ...)
    ;; '(instantiate) '(close)) runs the clause list against every open leaf,
    ;; commits ordinary tactics that each record themselves, and RETURNS the
    ;; step list so it can be pasted into a proof file.  Drives prop, contra and
    ;; supply, so it loads after all three.  Nothing in structure-library or
    ;; theorem-library may cite it -- it is copilot machinery, and a library
    ;; theorem that depended on it would invert the dependency.
    "preamble"
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
    "theorem-library/pss-topics"
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
    ;; 2026-09-21: the list of MAJOR THEOREMS of the user's notes, as the library states them
    ;; (reads docs/major-theorems-table.sexp, writes reference/major-theorems.tex).  After every proof file:
    ;; it reads the stored scripts, the citation graph and the bills.
    "major-theorems"
    ;; LAST: every view is a functor, and this proves it.  It needs every view
    ;; declared (views.scm, normed-vector-space.scm) and the tactic layer, so it
    ;; goes at the end.  It asserts nothing -- each functoriality theorem is
    ;; proved, modulo 0.
    "structure-library/functoriality"
    ;; page-audit -- the gate on the PRINTED PAGE.  Reads *proof-script-table*
    ;; and emits each proof through `script--write-block', so it must come after
    ;; every proof file, after `interactive' (the emitter) and after
    ;; functoriality (which qeds 17 more).  It defines procedures only; the gate
    ;; line itself is printed with the other gates at the foot of this file.
    "page-audit"))

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

;;; PER-FILE LOAD TIMING, opt-in: VNB_TIME_LOAD=1 ./prover ...
;;;
;;; "The library takes too long to load" is not actionable; "these six files are
;;; 60% of it" is.  Nothing here runs unless the variable is set -- the timing
;;; branch is one `if' per file, and the accounting is a cons -- so a normal
;;; load pays nothing measurable.  `report-load-times' prints the slowest files
;;; plus the total, and is called at the end of this file under the same guard.
;;;
;;; What it CANNOT see: work done after the file list finishes (the reference
;;; generators, the audits, the structure graph) and the fixed cost of the
;;; Scheme image itself.  The total it prints is the sum over FILES; compare it
;;; with the wall clock to size the rest.
(define *vnb-time-load?* (and (get-environment-variable "VNB_TIME_LOAD") #t))
(define *vnb-load-times* '())              ; (file . milliseconds), newest first

(define (report-load-times #!optional n)
  (let* ((n     (if (default-object? n) 20 n))
         (rows  (sort *vnb-load-times* (lambda (a b) (> (cdr a) (cdr b)))))
         (total (fold-left + 0 (map cdr *vnb-load-times*))))
    (display ";; load timing: ") (display (length *vnb-load-times*))
    (display " files, ") (display (quotient total 1000)) (display "s in files\n")
    (let loop ((r rows) (i 0))
      (when (and (pair? r) (< i n))
        (display ";;   ") (display (cdar r)) (display " ms  ")
        (display (caar r)) (newline)
        (loop (cdr r) (+ i 1))))
    (display ";;   (VNB_TIME_LOAD=1 produced this; total is FILES only --\n")
    (display ";;    the reference generators and audits run after the list)\n")
    rows))

;; `runtime' (seconds, a flonum) -- MIT has no `real-time' in the global
;; environment, which is what the first cut of this reached for.
(define (prover-load--timed f)
  (if *vnb-time-load?*
      (let ((t0 (runtime)))
        (prover-load--do f)
        (set! *vnb-load-times*
              (cons (cons f (round->exact (* 1000 (- (runtime) t0))))
                    *vnb-load-times*)))
      (prover-load--do f)))

;;; -----------------------------------------------------------------------
;;; THE INFERENCE CHECKERS  (batch 10, 2026-09-20)
;;;
;;; Four core files, one per KIND of kernel operation, each registering a
;;; checker per tag with `register-rule-checker!' (deduction-graphs.scm).  They
;;; are listed in *vnb-files* above, after `structures' and before the tactic
;;; surface, so every one of them is in place before the first proof runs.
;;;
;;; A GROUP THAT IS NOT PRESENT IS NOT SILENTLY SKIPPED.  The heads it would
;;; have covered are collected here, registered as ACCEPTED ON TRUST by
;;; `dg-check-arm-with!' and LISTED at the load, so the switch can be on while
;;; a group is still being written and nobody can mistake an unchecked rule for
;;; a checked one.  The lists below are the `logic' / `schema' / `rewrite' /
;;; `oracle' partition of *kernel-rule-tags* (tactics-help.scm), which loads far
;;; too late to be read here; `kernel-rules-audit' checks that partition
;;; independently at the end of the load.
(define *rule-checker-groups*
  '(("rule-checkers-logic"
     and-intro or-intro-left or-intro-right implies-intro not-intro iff-intro
     forall-intro forsome-intro truth-intro and-elim or-elim not-elim iff-elim
     forsome-elim forall-elim assumption theorem-assumption cut weakening
     detach backchain proof-by-contradiction contraposition eq-subst
     reflexivity quasi-reflexivity if-true if-false cartesian-intro
     cartesian-elim tuples-intro tuples-elim union-intro union-elim
     intersection-intro intersection-elim nth-reduce length-reduce
     functoid-beta nn-induction transfinite-induction
     transfinite-induction-3cases)
    ("rule-checkers-schema"
     sep-sethood sep-mem-intro sep-mem-elim comp-mem-intro comp-mem-elim
     big-union-sethood big-union-mem-intro big-union-mem-elim iota-def
     iota-in-elim lambda-type lambda-beta lambda-beta-hyp)
    ("rule-checkers-rewrite"
     macete macete-hyp cartesian-decompose tuple-equality-decompose)
    ("rule-checkers-oracle"
     arith-ground arith-forsome arith-simplify ring-simplify comm-ring-simplify
     ineq sos)))

(define *rule-checker-untrusted* '())     ; heads of the groups that are absent

(define (rule-checker-group-last)
  (car (list-ref *rule-checker-groups* (- (length *rule-checker-groups*) 1))))

(define (prover-load f)
  (let ((grp (assoc f *rule-checker-groups*)))
    (if (and grp (not (file-exists? (string-append *prover-dir* f ".scm"))))
        (begin
          (set! *rule-checker-untrusted*
                (append *rule-checker-untrusted* (cdr grp)))
          (display ";VNB: ") (display f)
          (display " is absent -- its kernel operations are ACCEPTED ON TRUST.")
          (newline))
        (prover-load--timed f))
    ;; arm once, after the last group, and before any proof file.
    ;; VNB_NO_RULE_CHECK=1 leaves the switch off: it is the A/B control for
    ;; what the checking costs, the same binary with one flag different, and
    ;; it says so at the load rather than passing for a checked library.
    (if (and grp (string=? f (rule-checker-group-last)))
        (let ((off (get-environment-variable "VNB_NO_RULE_CHECK")))
          (if (and off (not (string=? off "")) (not (string=? off "0")))
              (begin
                (display ";VNB inference checking: OFF (VNB_NO_RULE_CHECK is set).")
                (newline))
              (dg-check-arm-with! *rule-checker-untrusted*))))))

;;; STALE-BINARY WARNING (2026-09-01).  A file whose .com is OLDER than its
;;; .scm loads from SOURCE -- correct, and the reason `file-fresh-com?' exists
;;; -- but INTERPRETED, and for a core file that is ruinous and silent.  Twice
;;; in one day an edit to sequents.scm and structures.scm (expr->str and the
;;; structure machinery, both in every inner loop) took the library load from
;;; 3m15 to 8m05 with nothing on screen to say why.  CLAUDE.md has warned about
;;; this since August; a warning nobody can forget to read is better than a
;;; warning in a file.  Recompile with (compile-vnb!) from a loaded REPL, or
;;; one file at a time with
;;;     mit-scheme --quiet --eval '(begin (compile-file "/abs/path.scm") (exit))'
;;; A file with NO .com at all is NOT reported: that is the normal state for
;;; the 31 files compile-vnb! deliberately skips.
(define *vnb-stale-com* '())

(define (report-stale-coms)
  (unless (null? *vnb-stale-com*)
    (display ";VNB warning: ") (display (length *vnb-stale-com*))
    (display " file(s) loaded from SOURCE because their .com is STALE --\n")
    (display ";             interpreted, which can cost MINUTES on a load:\n")
    (for-each (lambda (f) (display ";               ") (display f) (newline))
              (reverse *vnb-stale-com*))
    (display ";             recompile them: (compile-vnb!) from a loaded REPL.\n"))
  *vnb-stale-com*)

(define (prover-load--do f)
  (let* ((base (string-append *prover-dir* f))
         ;; ALWAYS prefer a fresh .com; fall back to .scm SOURCE when the .com is
         ;; stale (older than its .scm) or absent.  This holds in BOTH normal and
         ;; recompile mode, so a source/tarball update self-heals -- MIT's `load'
         ;; otherwise picks a .com over its .scm blindly, silently serving a stale
         ;; binary (the classic "edited .scm but old .com wins" footgun).
         (path (if (file-fresh-com? base) base (string-append base ".scm"))))
    (when (and (not (file-fresh-com? base))
               (file-exists? (string-append base ".com")))
      (set! *vnb-stale-com* (cons f *vnb-stale-com*)))
    (prover-load--file f path)))

;;; Load list entry F from PATH (its .com or its .scm), in the environment its
;;; kind calls for, then run the per-file gates.  Hoisted out of prover-load--do
;;; (2026-09-23) so that `vnb-extend-band!' (extend-band.scm) loads a file the
;;; way this load does, from an explicit .scm path.
(define (prover-load--file f path)
  (let ((base (string-append *prover-dir* f)))
    (cond ((member f *primitive-files*)
           (fluid-let ((*current-provenance* 'primitive)) (load path)))
          ;; a contained proof file: certificates.scm decides whether it is
          ;; loaded as today (VNB_CERTIFIED=off, or outside a load of the tree)
          ;; or from its certificate, form by form
          ((proof-file? f)
           (cert-load-proof-file! f path
                                  (lambda () (extend-top-level-environment *driver-kit-env*))))
          (else (load path)))
    ;; No-op until clobber-guard.scm has taken its snapshot.  Contained files can
    ;; no longer trip it; it still guards the engine and structure-library.
    (clobber-guard-check! f)
    ;; THE READ-TIME CASE-FOLD LINT (clobber-guard.scm, 2026-09-20): two
    ;; top-level defines in ONE file whose names fold to the same symbol.  It
    ;; reads the SOURCE text because nothing in the image can see the collision
    ;; -- the reader folded both spellings to one symbol before the file ran.
    ;; Warn-only; ~5 s over the whole tree.  clobber-guard.scm is the first file
    ;; loaded, so the procedure exists by the time this line first runs.
    (case-fold-define-lint! f (string-append base ".scm"))))

;; Load every file -- but clear *vnb-loading* if a file errors mid-load, so a
;; broken file can't strand the flag at #t and leave every (show) suppressed
;; for the rest of the session (the reset at the end of this file is skipped
;; when loading aborts).  On error: clear the flag, escape, then RE-RAISE so
;; the error still surfaces in the REPL -- now with interactive output enabled
;; for debugging.  On a clean load the thunk returns #f and nothing re-raises.
;;; KEEP-GOING MODE, opt-in: VNB_KEEP_GOING=1 ./prover ...
;;;
;;; A cold load stops at the first proof file that errors, so a change that
;;; breaks N files costs N loads to enumerate them.  With the variable set, an
;;; error inside a PROOF file (theorem-library/, calculus/) is recorded and the
;;; load goes on; the failures are listed at the end, in load order, with the
;;; condition text.  A file that fails leaves its later theorems uninstalled, so
;;; its citers fail too -- the list is a cascade, and its FIRST entries are the
;;; ones to read.  An error in an engine or structure-library file still stops
;;; the load: nothing after it can be trusted.
;;;
;;; This is a DEVELOPMENT mode.  A band built under it holds a library with
;;; holes in it, and the end of the load says so loudly.  (2026-09-16, the
;;; SIZE/MAT surgery: ~25 proof files to repair.)
(define *vnb-keep-going?*
  (let ((v (get-environment-variable "VNB_KEEP_GOING")))
    (and v (not (string=? v "")) (not (string=? v "0")))))
(define *vnb-load-failures* '())           ; (file . message), newest first

(define (prover-load--keep-going f)
  (if (not (and *vnb-keep-going?* (proof-file? f)))
      (prover-load f)
      (let ((err (call-with-current-continuation
                   (lambda (k)
                     (with-exception-handler
                       (lambda (exn) (k exn))
                       (lambda () (prover-load f) #f))))))
        (when err
          (let ((msg (call-with-output-string
                       (lambda (port)
                         (if (condition? err)
                             (write-condition-report err port)
                             (write err port))))))
            (set! *vnb-load-failures* (cons (cons f msg) *vnb-load-failures*))
            (display ";VNB KEEP-GOING: ") (display f) (display " FAILED: ")
            (display msg) (newline))))))

(define (report-load-failures)
  (when *vnb-keep-going?*
    (display ";; KEEP-GOING HOLES: ") (display (length *vnb-qed-holes*))
    (display " theorem(s) installed UNPROVEN (proof did not complete):\n")
    (for-each (lambda (h) (display ";;   ") (display (car h)) (newline))
              (reverse *vnb-qed-holes*))
    (display ";; ================================================================\n")
    (display ";; KEEP-GOING LOAD: ")
    (display (length *vnb-load-failures*))
    (display " proof file(s) FAILED -- this library has HOLES in it.\n")
    (for-each (lambda (r)
                (display ";;   ") (display (car r)) (newline)
                (display ";;       ") (display (cdr r)) (newline))
              (reverse *vnb-load-failures*))
    (display ";; ================================================================\n"))
  (reverse *vnb-load-failures*))

;;; VNB_LOAD_LIMIT=N (development, batch 28): load only the first N contained
;;; proof files, skip every later theorem-library/, calculus/ and
;;; structure-library/ entry, and still load the ROOT files of the tail (the
;;; tactics, the audits, the reference writers), so a development cycle of the
;;; load machinery costs minutes.  Never for a band anyone uses.
(define *vnb-load-limit*
  (let ((v (get-environment-variable "VNB_LOAD_LIMIT")))
    (and v (not (string-null? v)) (string->number v))))
(define *vnb-load-limit-count* 0)

(define (prover-load--limited f)
  (cond ((not *vnb-load-limit*) (prover-load--keep-going f))
        ((proof-file? f)
         (if (< *vnb-load-limit-count* *vnb-load-limit*)
             (begin (set! *vnb-load-limit-count* (+ *vnb-load-limit-count* 1))
                    (prover-load--keep-going f))))
        ((and (>= *vnb-load-limit-count* *vnb-load-limit*)
              (string-search-forward "/" f 0))
         'skipped)
        (#t (prover-load--keep-going f))))

(set! *cert-in-load-list* #t)
(let ((err (call-with-current-continuation
             (lambda (k)
               (with-exception-handler
                 (lambda (exn) (set! *vnb-loading* #f) (set! *cert-in-load-list* #f) (k exn))
                 (lambda () (for-each prover-load--limited *vnb-files*) #f))))))
  (if err (raise err)))
(set! *cert-in-load-list* #f)
(if *vnb-load-limit*
    (begin (display ";VNB: VNB_LOAD_LIMIT=") (display *vnb-load-limit*)
           (display " -- a CUT-DOWN load of the first ") (display *vnb-load-limit-count*)
           (display " proof file(s); not a library anyone should use.") (newline)))

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
;;;
;;; EXCEPT IN A COMMENT, where it was not harmless at all (found 2026-08-12).
;;; The scan used to read raw LINES, so a file that only DISCUSSES one of these
;;; macros was skipped: `macetes.scm' mentions "(bc* " at :134 and
;;; `interactive.scm' shows "(declare-structure " in a docstring at :2619, so
;;; compile-vnb! silently declined to compile TWO OF THE LARGEST CORE FILES.
;;; Nothing said so; the .com files in the tree were old ones, and the first
;;; time they were deleted the library load went from 50 s to over ten minutes
;;; with no diagnostic.  The scan now strips each line's comment first.  It
;;; still errs toward skipping -- a real use anywhere in the file, at top level
;;; or nested inside a lambda, must be caught, because compile-file cannot see a
;;; syntactic keyword at any depth -- but a mention in prose no longer counts.
(define *vnb-top-level-macros*
  '((bc*               . "interactive")         ; macro . its definition site
    (declare-structure . "structures")
    (vlet              . "vlet")))

;;; THIS CHECK IS DONE WITH THE READER, NOT BY SCANNING TEXT (2026-08-15), and
;;; the history of the two previous attempts is the argument for it.
;;;
;;; The scan began as a raw per-line `substring?' for "(bc* " and friends.  That
;;; matched COMMENTS, so macetes.scm (which mentions `(bc* ' at :134) and
;;; interactive.scm (a docstring at :2619) were silently never compiled; fixed
;;; 2026-08-12 by cutting each line at its first `;'.  But cutting at `;' does
;;; not help with the two shapes that remained, both of which are DATA:
;;;
;;;   suggest.scm:2733   (string-append "(bc* '" ...)      -- inside a STRING
;;;   suggest.scm:3851   (memq (car step) '(bc* fact ta))  -- QUOTED
;;;   tactics-help.scm   (bc* . "a library theorem's ...")  -- an ALIST KEY, and
;;;                      (bc* composite (backchain))        -- a table row
;;;
;;; so `suggest' and `tactics-help' -- the two copilot files, and the ones most
;;; likely to be edited -- were skipped by compile-vnb! forever.  A line-based
;;; scan cannot fix the last two at all: the quote that makes them data is on an
;;; enclosing line.  Found 2026-08-15 by the user, from a fresh unpack: 31 root
;;; .com files where this box had 33, and the two missing were exactly those.
;;;
;;; The failure is SILENT and it compounds: an uncompiled core file costs the
;;; whole library load (an interpreted wff.scm once took a 24 s load to over 14
;;; minutes), and nothing reports it.  So the check now READS the file and looks
;;; for the macro applied in CODE position.  The reader knows what a string is,
;;; what a comment is, and what `quote' is; a textual scan can only guess at all
;;; three.

;;; Is NAME applied anywhere inside FORM, outside quoted data?
(define (vnb--form-uses-macro? form name)
  (cond ((not (pair? form)) #f)
        ((eq? (car form) 'quote) #f)            ; '(bc* ...) is data, not a use
        ((eq? (car form) name) #t)
        (else (let loop ((l form))
                (cond ((not (pair? l)) #f)
                      ((vnb--form-uses-macro? (car l) name) #t)
                      (else (loop (cdr l))))))))

(define (vnb-file-uses-bc*-macro? f)
  (let ((macros (filter (lambda (e) (not (string=? f (cdr e))))
                        *vnb-top-level-macros*)))
    (and (pair? macros)
         (call-with-input-file (string-append *prover-dir* f ".scm")
           (lambda (port)
             (let loop ()
               (let ((form (read port)))
                 (cond
                   ((eof-object? form) #f)
                   ((find-first (lambda (e) (vnb--form-uses-macro? form (car e)))
                                macros)
                    #t)
                   (else (loop))))))))))

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

;;; Per-block timing of run-load-end! (2026-09-24), for the metrics ledger:
;;; Ignacio's step-1 measurement found the extension's tail (reference
;;; regeneration, the gates, the page audit) costing more than the reload
;;; itself, with no per-block number to blame.  *vnb-load-end-times* is an
;;; alist (key . seconds), summed across every call under the same key so a
;;; key split across two non-adjacent regions (the gates run before AND after
;;; the page audit) still reads as one total.  The shell wrapper that prints
;;; the `;;VNB-METRICS' line (prover --build-band / --extend-band) reads it
;;; and adds each entry as its own key=value.  `runtime' (seconds, a flonum),
;;; not `real-time' -- see the note on prover-load--timed above.
(define *vnb-load-end-times* '())
(define (vnb--time-block! key thunk)
  (let* ((t0 (runtime))
         (result (thunk))
         (secs (- (runtime) t0))
         (cell (assq key *vnb-load-end-times*)))
    (if cell
        (set-cdr! cell (+ (cdr cell) secs))
        (set! *vnb-load-end-times* (cons (cons key secs) *vnb-load-end-times*)))
    result))

;;; THE END-OF-LOAD BLOCK, as ONE procedure (2026-09-23): the catalog and
;;; reference writers, the gates, the page audit, the band record and the
;;; session reset.  `vnb-extend-band!' (extend-band.scm) calls the same
;;; procedure after it has reloaded its files, so an extension passes exactly
;;; the gates a cold load passes -- shared code, not a copy.
(define (run-load-end!)
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

  (vnb--time-block! 'reference_s (lambda ()
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

  ;; Regenerate DEBT-BUNDLE.md: the same debt data raked into heaps.  Two things
  ;; the flat ledger cannot say -- the GREEDY what-if ranking (which leaves, in
  ;; which order, actually clear bills; citation count is the wrong ranking and
  ;; `nary-neg-1' is the scar that proves it) and, for every bill of ten leaves or
  ;; more, the ENTRY ROUTE each leaf came in through, so a 115-leaf bill reads as
  ;; two or three named arcs.  Recomputed here, never stored, so it cannot drift.
  (report-stale-coms)
  (when *vnb-time-load?* (report-load-times))
  (report-load-failures)

  (let ((p (debt-bundle-md)))
    (display ";; debt-bundle: ") (display p) (newline))

  ;; Regenerate the interactive-tactics menu (TACTICS.md) from the registry.
  (write-tactics-md)

  ;; Regenerate GLOSSARY.md: every NAME in the system -- structures, instances,
  ;; views, predicates, functoids, accessors, defined constants, kernel heads and
  ;; tactics -- in one alphabetical list.  Runs after every registry is populated
  ;; and after (catalog), whose *theorem-table* the usage counts read.
  (write-glossary-md)
  ;; The major theorems of the notes against the library, in LaTeX (docs/major-theorems.tex is the wrapper;
  ;; `make major-theorems' in docs/).  A missing table is not an error.
  (write-major-theorems-tex! "docs/major-theorems-table.sexp" "reference/major-theorems.tex")

  ;; Regenerate emacs/vnb-commands.lisp (the command-completion catalog) from the
  ;; same registry, so the M-x/button surface can never drift from (tactics).
  (write-vnb-commands)
  ))

  (vnb--time-block! 'gates_s (lambda ()
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
          ;; the out-edges of every node named in a cycle -- without them the path
          ;; above says WHICH proofs are tangled but not WHICH citation tangles them
          (display ";; the cited names of each node on a cycle:\n")
          (for-each
           (lambda (n)
             (display ";;   ") (display n) (display "  [") (display (provenance-of n))
             (display "]  cites ") (write (proof-citations-of n)) (newline))
           (let loop ((cs cycles) (acc '()))
             (if (null? cs) (reverse acc)
                 (loop (cdr cs)
                       (let add ((p (car cs)) (a acc))
                         (cond ((null? p) a)
                               ((memq (car p) a) (add (cdr p) a))
                               (else (add (cdr p) (cons (car p) a)))))))))
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
  ;; gone (the group family's operation is OPR, the field's inverse MUL-INV, the
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

  ;;; THE INFERENCE-CHECKING REPORT (batch 10, 2026-09-20).
  ;;;
  ;;; What the switch did, in one line, at every load: how many inferences were
  ;;; verified, how many were REFUSED, and which rule heads were accepted on
  ;;; trust because their group's file was absent.  The count matters as much as
  ;;; the refusals: a switch that was never armed, or a checker table that
  ;;; accepts everything, reads exactly like a clean library otherwise.
  ;;;
  ;;; A refusal is a FINDING -- either the checker or the kernel operation is
  ;;; wrong -- so in a STRICT load it is fatal.  Under VNB_KEEP_GOING the load
  ;;; goes on and lists them, because the point of keep-going is to enumerate
  ;;; the damage in one run.  (A refusal also prints, unsuppressibly, where it
  ;;; happens: see dg-check-report-refusal! in deduction-graphs.scm.  A driver's
  ;;; `quietly' swallows the raise, so the line at the site is the only evidence
  ;;; that a silently no-opped tactic leaves behind.)
  (if (not *dg-check-inferences?*)
      (display ";; inference checking: OFF -- no inference of this load was verified\n")
      (let ((n (dg-check-refusal-count)))
        (display ";; inference checking: ")
        (display *dg-checked-count*)
        (display " inference(s) verified, ")
        (display n)
        (display " refusal(s)")
        (if (pair? *dg-trusted-rule-heads*)
            (begin
              (display "; ACCEPTED ON TRUST: ")
              (display *dg-trusted-rule-heads*)))
        (newline)
        (if (> n 0)
            (begin
              (for-each (lambda (r)
                          (display ";;   REFUSED ") (display (car r))
                          (display " -- ") (display (cdr r)) (newline))
                        (dg-check-refusals))
              (if (not *vnb-keep-going?*)
                  (error
                   "inference checking: this load recorded rule-checker REFUSALS; the library is NOT verified"))))))

  ;;; qed-failure gate (2026-09-20).  A `qed' that fails inside a proof file prints one
  ;;; line and returns; the load goes on, and when no later file cites the theorem
  ;;; nothing stops.  `qed' records every failure (interactive.scm,
  ;;; *vnb-qed-failures*); here the record is listed, and in a STRICT load it is
  ;;; fatal.  Under VNB_KEEP_GOING an incomplete proof is a HOLE, not a failure, and
  ;;; is listed with the holes; what remains here are the other ways a qed can fail.
  ;; PROOF CERTIFICATES: the two counts, apart (certificates.scm) -- the proofs
  ;; that ran in this image and the theorems installed from a certificate --
  ;; with the files that fell back to off mode, and the check that the kernel
  ;; hash covers every *kernel-caller-files* entry.
  (report-proof-counts)
  (let ((fails (reverse *vnb-qed-failures*)))
    (if (null? fails)
        (display ";; qed-failure gate: ok (every qed of this load installed its theorem)\n")
        (begin
          (display ";; qed-failure gate: ") (display (length fails))
          (display " qed(s) FAILED during this load -- the theorem was NOT installed:\n")
          (for-each (lambda (f)
                      (display ";;   ") (display (car f)) (display " -- ")
                      (display (cdr f)) (newline))
                    fails)
          (if (not *vnb-keep-going?*)
              (error "qed-failure gate: this load has proofs that did not reach qed; the library is NOT complete")))))

  ;; Not a question about the installed formulas, but about the CODE that walks
  ;; them: does every traversal agree with *binder-shapes* on which heads bind?
  ;; See binder-walker-audit in audit.scm for what a disagreement costs.
  (let ((bad (binder-walker-audit)))
    (if (null? bad)
        (begin
          (display ";; binder-walker-audit: ok (")
          (display (length *binder-shapes*))
          (display " binder head(s); free-vars, subst-free, alpha-equiv? and formula-hash agree; ")
          (display (length *binder-walkers*))
          (display " declared walker(s), ")
          (display (length (filter (lambda (w) (not (pair? (cdr w)))) *binder-walkers*)))
          (display " driven from the table)\n"))
        (begin
          (display "\n;; binder-walker-audit: ") (display (length bad))
          (display " WALKER DISAGREEMENT(S) WITH *binder-shapes* --\n")
          (for-each (lambda (e)
                      (display ";;   ") (display (car e))
                      (display " -- ") (display (cdr e)) (newline))
                    bad)
          (error "binder-walker-audit: a walker does not know a declared binder binds -- see above"))))

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
  ))

  ;; SIXTH GATE, and the one the user's standard of 2026-09-06 asks for: every
  ;; proof must have a re-runnable script -- a rendition that fits on paper and
  ;; that anybody able to use a keyboard can type back in to reproduce the proof.
  ;; This emits every stored proof through the same `script--write-block' the `W'
  ;; key uses and TYPES IT BACK IN, reporting how many reach a grounded graph.
  ;;
  ;; WARN-ONLY.  A proof whose page does not re-run is still a proof: the graph was
  ;; checked at `qed' and nothing here can unsay that.  What is missing is its
  ;; printed rendition, which is a different -- and, until this line existed,
  ;; completely invisible -- property.  Every violation is SILENT (the page loads,
  ;; nothing complains, the proof merely is not finished), which is the argument
  ;; for a load line rather than an instrument somebody remembers to run.
  ;;
  ;; COST, measured A/B on 2026-09-07, same binary, same tree:
  ;;      load with this line commented out   2m34.8s
  ;;      load with it in                     3m44.3s
  ;;      -> +69.5 s, +45%
  ;; The re-run is irreducible -- you cannot know whether a page reproduces a proof
  ;; without running it -- so the only lever is COVERAGE.  Exhaustive here is the
  ;; strong reading of the standard (it can name the one proof that broke today);
  ;; sampling here and keeping the exhaustive sweep in the suite is the cheap one
  ;; (it catches systematic breakage, not a single proof).  Left exhaustive, and
  ;; the number is written down so the trade can be revisited on evidence.
  (vnb--time-block! 'audit_s (lambda () (report-page-audit)))
  (vnb--time-block! 'gates_s (lambda ()
  ;; DEFINEDNESS AUDIT (2026-09-18, measurement): with VNB_DEF_AUDIT set, print how
  ;; many universal instantiations in this load were at a term nothing certifies
  ;; defined (see def-audit-note! in primitive-inferences.scm), by head.
  (let ((flag (get-environment-variable "VNB_DEF_AUDIT")))
    (when (and flag (not (string-null? flag)))
      (display ";; def-audit: ") (display *def-audit-total*)
      (display " instantiation(s), ") (display *def-audit-uncert*)
      (display " at a term with NO definedness certificate; by head:\n")
      (for-each (lambda (kv) (display ";;   ") (display (car kv)) (display " ")
                  (display (cdr kv)) (newline))
                (sort (hash-table->alist *def-audit-hits*)
                      (lambda (a b) (> (cdr a) (cdr b)))))
      (with-output-to-file "/home/ubuntu/def-audit-terms.txt"
        (lambda () (for-each (lambda (e) (write e) (newline)) (reverse *def-audit-terms*))))
      (display ";; def-audit: terms written to /home/ubuntu/def-audit-terms.txt\n")))

  ;;; install-duplicate-audit (2026-09-16) -- a theorem name installed twice during
  ;;; the load.  Either a proof re-proves a fact already proven, or a support was
  ;;; never retired when its proof landed, or -- the one that matters -- a fact is
  ;;; installed under a different provenance the second time, which silently
  ;;; changes every bill after it.  Warn-only until a clean load confirms zero.
  (let ((dups (reverse *install-duplicates*)))
    (if (null? dups)
        (display ";; install-duplicate-audit: ok (no theorem name installed twice)\n")
        (begin
          (display ";; install-duplicate-audit: ") (display (length dups))
          (display " name(s) installed twice during the load:\n")
          (for-each (lambda (n) (display ";;   ") (display n) (newline)) dups))))

  ;;; case-fold lint roll-up (2026-09-20, batch 12-C): the per-file loader runs
  ;;; `case-fold-define-lint!' on every proof file; this prints the total.  Warn-only until a
  ;;; cold load shows it at zero.
  (report-case-fold-defines)

  ;;; asserted-duplicate-audit (2026-09-19) -- an asserted statement alpha-equivalent to one
  ;;; settled under another name (proof-debt.scm).  Warn-only: each hit is one `fact' away
  ;;; from a proof, or one rename away from a retirement.
  (let ((hits (asserted-duplicate-audit)))
    (if (null? hits)
        (display ";; asserted-duplicate-audit: ok (no asserted statement repeats a settled one)\n")
        (begin
          (display ";; asserted-duplicate-audit: ") (display (length hits))
          (display " asserted statement(s) repeat a settled one under another name:\n")
          (for-each (lambda (h) (display ";;   ") (display (car h)) (display "  ==  ")
                                (display (cdr h)) (newline))
                    hits))))

  ;;; proven-duplicate-audit (2026-09-20, decision of the user) -- two or more PROVEN names with
  ;;; alpha-equivalent statements (proof-debt.scm).  Warn-only; the backlog on the day it was
  ;;; added is the list it prints.  Each group wants one name kept and the others renamed away
  ;;; with scratchpad/rename-sym.py.
  (let ((groups (proven-duplicate-audit)))
    (if (null? groups)
        (display ";; proven-duplicate-audit: ok (no statement is proven under two names)\n")
        (begin
          (display ";; proven-duplicate-audit: ") (display (length groups))
          (display " statement(s) are proven under more than one name:\n")
          (for-each (lambda (g)
                      (display ";;   ")
                      (let loop ((ns g))
                        (display (car ns))
                        (if (pair? (cdr ns)) (begin (display "  ==  ") (loop (cdr ns)))))
                      (newline))
                    groups))))

  ;; SEVENTH GATE (2026-09-12): who may write the deduction graph.
  ;;
  ;; `dg-apply-rule!' is the sole procedure that writes an inference into a
  ;; deduction graph.  (Until 2026-09-20 it validated NOTHING -- it recorded the tag it was handed.
  ;; Since that day it CHECKS every inference against the operation's checker before writing; this
  ;; gate is about WHO may ask it to write, which is a separate question and still needs an answer.)
  ;; So the trusted code base is exactly the set of procedures that call it, and
  ;; the kernel map measured that set (re-measured 2026-09-20): 69 call sites in 8 files, 0
  ;; uses of the name as a value, and -- over a re-run of the whole library --
  ;; 197,669 graph writes with 0 outside those call sites.  That was a measurement,
  ;; not an invariant: nothing stopped the 9th file from appearing tomorrow, and
  ;; the existing `kernel-rules-audit' cannot see it (it checks that the TAGS are
  ;; documented, never which procedures stamp them).
  ;;
  ;; FATAL, on the connective-arity precedent: a gate goes fatal once the
  ;; pre-existing backlog is zero, and this one's backlog IS zero.  A limit that
  ;; only warns is not a limit.  The remedy for an honest new kernel file is not
  ;; to weaken this -- it is to ADD the file to `*kernel-caller-files*' (audit.scm)
  ;; deliberately, which is the same one-explicit-decision-per-fact discipline the
  ;; primitive shelf runs on: enlarging the trusted base should cost a decision and
  ;; leave a record.
  ;;
  ;; COST, measured against the band: 7.4 s over 433 files, i.e. ~5% of a 2m35s
  ;; load.  Nearly all of it is opening the files, not parsing them -- a reader
  ;; pass over every file was 17.3 s, and the text pre-filter that skips the 422
  ;; files which cannot contain the call took it to 7.4 s.  That floor is the I/O.
  (let ((bad (kernel-callers-audit))
        (vals (kernel-callers-value-uses)))
    (if (and (null? bad) (null? vals))
        (let ((census (kernel-callers-census)))
          (display ";; kernel-callers-audit: ok (")
          (display (reduce + 0 (map cadr census)))
          (display " call site(s) to dg-apply-rule! in ")
          (display (length census))
          (display " file(s), all allowed; 0 value use(s))\n"))
        (begin
          (if (pair? bad)
              (begin
                (display "\n;; kernel-callers-audit: ") (display (length bad))
                (display " FILE(S) OUTSIDE THE KERNEL WRITE THE DEDUCTION GRAPH --\n")
                (display ";; each of these can ask dg-apply-rule! to record an inference, so each is trusted code\n")
                (display ";; that no one decided to trust.  Either route the step through an\n")
                (display ";; existing kernel entry point, or add the file to *kernel-caller-files*\n")
                (display ";; (audit.scm) as a deliberate enlargement of the trusted base:\n")
                (for-each (lambda (e)
                            (display ";;   ") (display (car e))
                            (display "  calls=") (display (cadr e))
                            (display "  value-uses=") (display (caddr e)) (newline))
                          bad)))
          (if (pair? vals)
              (begin
                (display "\n;; kernel-callers-audit: ") (display (length vals))
                (display " file(s) use dg-apply-rule! AS A VALUE --\n")
                (display ";; passing the graph writer to a caller moves the call site to wherever\n")
                (display ";; that caller lives, which is exactly what this gate cannot see:\n")
                (for-each (lambda (e)
                            (display ";;   ") (display (car e))
                            (display "  value-uses=") (display (caddr e)) (newline))
                          vals)))
          (error "kernel-callers-audit: the deduction graph is written from outside the kernel -- see above"))))

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
  ;; abelian group whose operation is OPR.  This is what drove the OPR/MUL-INV/FNRM
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

  ;; SIXTH GATE, and the first that asks about MEANING rather than shape: is a
  ;; structure predicate SATISFIABLE?  A shape structure's defining IFF opens with
  ;; (= (LENGTH s) n); a (substructure SLOT TYPE) clause and a law naming another
  ;; structure of that slot each pin a length too, and two pins with different
  ;; numbers make IS-X unsatisfiable -- whereupon every theorem carrying it as a
  ;; hypothesis is vacuously true and looks exactly like a good one.  That went
  ;; unnoticed for months in NORMED-VECTOR-SPACE (repaired 2026-08-23) and is why
  ;; this runs.  Syntactic, no proof search; see audit.scm.  WARN-ONLY: which
  ;; structure the slot is meant to hold is a decision, not a mechanical repair.
  (let ((bad (structure-satisfiability-audit)))
    (if (null? bad)
        (display ";; structure-satisfiability-audit: ok (no structure predicate pins one term's length twice)\n")
        (begin
          (display "\n;; structure-satisfiability-audit: ") (display (length bad))
          (display " structure predicate(s) UNSATISFIABLE --\n")
          (display ";; the hypothesis cannot be met, so every theorem carrying it is VACUOUS:\n")
          (for-each (lambda (e)
                      (display ";;   IS-") (display (car e))
                      (display " pins length(") (display (expression->string (cadr e)))
                      (display ") to ") (display (car (caddr e)))
                      (display " (via ") (display (cdr (caddr e)))
                      (display ") and to ") (display (car (cadddr e)))
                      (display " (via ") (display (cdr (cadddr e)))
                      (display ")\n"))
                    bad))))

  ;; SEVENTH GATE, and the blind spot of the sixth.  The audit above scans one
  ;; DECLARATION at a time, so it cannot see a clash ASSEMBLED by a theorem out of
  ;; two predicates that are each satisfiable alone: IS-NORMED-VECTOR-SPACE(m)
  ;; pins length(m) = 7 and IS-FINITE-DIMENSIONAL(m) pins it to 6 through
  ;; IS-VECTOR-SPACE, and five results conjoined the two on the same m.  Same
  ;; machinery, applied to the conjuncts of a HYPOTHESIS instead of the conjuncts
  ;; of a defining IFF, and following a def-predicate into its IFF (which is how
  ;; IS-FINITE-DIMENSIONAL's pin is reached at all).  Syntactic, no proof search;
  ;; see audit.scm.  WARN-ONLY: which structure each half is about is a decision.
  (let ((bad (statement-satisfiability-audit)))
    (if (null? bad)
        (display ";; statement-satisfiability-audit: ok (no statement's hypothesis pins one term's length twice)\n")
        (begin
          (display "\n;; statement-satisfiability-audit: ") (display (length bad))
          (display " statement(s) with an UNSATISFIABLE HYPOTHESIS --\n")
          (display ";; nothing can satisfy it, so each is VACUOUSLY true and says nothing:\n")
          (report-statement-satisfiability bad))))

  ;; EIGHTH GATE, and the blind spot of the seventh.  The two audits above read
  ;; one DECLARATION and one FORMULA's hypotheses respectively; neither can see a
  ;; contradiction assembled across FORMULAS by a shared constant.  `IN f (FUN A
  ;; ...)' pins DOM(f) = A EXACTLY (theory.scm:321; dom-of-fun, theory.scm:500),
  ;; so one object asserted into two function classes with different domains
  ;; proves those domains equal -- and for binneg (ZZ, QQ, RR, CC) that collapses
  ;; the numeric hierarchy and, through cc-i-squared, yields FALSITY.
  ;; WARN-ONLY: the findings are known, and their repair is a foundational
  ;; decision about how a numeric operation reaches a structure slot, not a
  ;; mechanical fix a gate should force at load time.
  (let ((bad (domain-clash-audit))
        (pop (domain-clash-population)))
    (if (null? bad)
        (begin
          (display ";; domain-clash-audit: ok (no object is asserted into two FUN classes with different domains; ")
          (display pop) (display " object(s) examined)\n"))
        (begin
          (display "\n;; domain-clash-audit: ") (display (length bad))
          (display " of ") (display pop)
          (display " object(s) carry CLASHING exact domains --\n")
          (display ";; each pair below PROVES those two domains equal:\n")
          (for-each
           (lambda (e)
             (display ";;   ") (display (expression->string (car e)))
             (display "  --  ") (display (length (cdr e))) (display " distinct domains:\n")
             (for-each (lambda (d)
                         (display ";;        ") (display (expression->string (car d)))
                         (display "   ") (write (cdr d)) (newline))
                       (cdr e)))
           bad))))

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
  ;; support should be filed under a *pss-topic-order* bucket via topic!.
  ;; Report how many are not yet filed; never fails the build.
  (let ((un (pss-names-without-topic)))
    (if (null? un)
        (display ";; pss-topics: ok (all support entries filed)\n")
        (begin
          (display ";; pss-topics: ") (display (length un))
          (display " PSS entr(y/ies) -- file with (topic! 'name 'cat):\n   ")
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
  ))

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

  ;; THE STRUCTURE GRAPH, rendered here too -- and the reason it was not is worth
  ;; recording, because it is the very rot the comment above `write-all-reference'
  ;; (interactive.scm) says it exists to stop.
  ;;
  ;; Every load REWRITES reference/structure-graph.dot.  Nothing rendered it: the
  ;; .html was refreshed only by `./VNB-with-compile' and by `M-x
  ;; vnb-structure-graph-html', and the standalone .svg only by the former.  So a
  ;; user who launches with `./VNB' -- or who opens the page from the browser hub
  ;; -- reads a render as old as their last recompile.  Found 2026-08-19 by the
  ;; user asking why `complex-inner-product-space' was not in the graph: it was in
  ;; the .dot, written that morning, and absent from a .html and .svg dated
  ;; 2026-07-23.  Four weeks of drift, and with it `measurable-space',
  ;; `measure-space' and five edges (the poly and dual self-loops among them).
  ;; Nothing said so; a stale render looks exactly like a correct one.
  ;;
  ;; The stated reason for leaving it out -- "rendering wants graphviz + python3,
  ;; which a headless library load must not depend on" -- is answered by the line
  ;; above, which already shells out to python3, detached and guarded, and by the
  ;; shell's own `command -v' test here: a box with neither tool simply skips and
  ;; keeps the previous render, exactly as before.  Measured cost: 0.42 s for the
  ;; sixteen dot layouts build-graph-html.py inlines, plus 0.04 s for the
  ;; standalone .svg -- and it is backgrounded, so it is off the load's path
  ;; entirely.
  (ignore-errors
    (run-shell-command
      (string-append
       "{ command -v dot >/dev/null 2>&1 && command -v python3 >/dev/null 2>&1 && "
       "cd " *prover-dir* "reference && "
       "python3 build-graph-html.py >/dev/null 2>&1 && "
       "dot -Tsvg structure-graph.dot > structure-graph.svg 2>/dev/null ; } "
       "< /dev/null > /dev/null 2>&1 &")))

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
  ;; ... and the UNDO STACK, for exactly the same reason: its marks name the last
  ;; library proof's state, and a (backup-one) at the fresh prompt would restore
  ;; *ps* to it.  (backup-one also refuses a stack that does not belong to the
  ;; current *ps*; this is the other half.)
  (vnb--undo-reset!)
  ;; Freeze the inert-command tally as the LOAD left it.  The live counter goes on
  ;; rising afterwards -- notably under `quietly', which suppresses the notice's
  ;; print but not its count -- so this is the number the suite asserts on.
  (set! *vnb-inert-at-load* *vnb-inert-count*)
  ;; ... and the SESSION LOG, for the same reason one level up.  `qed' appends to
  ;; it, and loading the library is ~300 qeds, so `dump-session' / `write-session'
  ;; -- documented as "every proof completed this session" -- opened with the
  ;; whole library and buried the user's own proof at the end of it.  "This
  ;; session" means the work done since the prompt appeared, not the library that
  ;; was loaded to make the prompt possible.
  (set! *session-log* '())

  ;; The band record (extend-band.scm): the strict marker and the content hash
  ;; of every file in *vnb-files*, which `vnb-extend-band!' compares against.
  (xb-mark-band!)

  ;; Load done: re-enable interactive show output.  (Held #t since the top of
  ;; this file to suppress the per-tactic flood from the library proof scripts.)
  (set! *vnb-loading* #f)

  ;; Load done: from now on, make-wff REJECTS a formula whose binder is named like
  ;; a registered constant -- the interactive counterpart of the
  ;; constant-binder-audit gate.  Off during the load above so the library's own
  ;; (clean) wff construction stays silent.
  (set! *reject-constant-binders?* #t)

  ;; VNB_CERTIFIED=strict: a gate, last.  Lists every theorem of the tree with no
  ;; valid certificate and exits 4; silent unless the mode is strict.
  (cert-strict-gate!))

(run-load-end!)
