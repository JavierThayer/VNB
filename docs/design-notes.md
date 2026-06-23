# VNB Design Notes

Informal record of design decisions and rationale, for eventual inclusion
in the manual or a separate design document.

---

## lambda / lambdoid and the Functoid concept

### Why two binders?

The original system had a single `vnb-lambda` binder.  We split it into
two forms that differ in what they promise about their domains:

- **`lambda([x₁ in A₁, ..., xₙ in Aₙ], body)`** — a *proper* anonymous
  function.  Every domain `Aᵢ` must belong to `SET` (verified in context
  by the wff validator).  The result is an element of `FUN(A₁ × ... × Aₙ, B)`
  when the typing condition `∀ xᵢ ∈ Aᵢ. body ∈ B` is proved.

- **`lambdoid([x₁ in A₁, ..., xₙ in Aₙ], body)`** — a *class-domain*
  anonymous function.  The domains may be arbitrary classes, including
  proper classes such as `ORD` or `SET` itself.  The result cannot in
  general be an element of any `FUN` class (since `FUN(A,B)` requires
  `A ∈ SET`), but it is still a meaningful computable object and
  supports β-reduction.

The name *lambdoid* is deliberately parallel to *functoid*: both signal
"function-like but not necessarily set-sized."

### Binding syntax

Each variable gets its **own independent domain**, exactly as in
quantification:

```
lambda([x in A, y in B, z in C], body)
```

This is more general than `lambda([x, y, z in A], body)` (which would
force a single shared domain) and mirrors the quantifier syntax
`forall([x in A, y in B], P)` already in the system.

### Why rename away from `vnb-lambda`?

The prefix `vnb-` was a workaround to avoid clashing with Scheme's
built-in `lambda` keyword.  MIT Scheme folds all symbols to lowercase,
so `LAMBDA` and `lambda` are the same symbol — which is Scheme's keyword.
The fix is simple: VNB data is always manipulated as **quoted** S-expressions
or Scheme record objects, never evaluated as Scheme code, so the symbol
`lambda` appearing in a VNB term is harmless.  The `vnb-` prefix was
unnecessary and cluttered the surface syntax.

---

## Functoids as meta-level tagged records

### What is a functoid?

A **functoid** is a Scheme `<functoid>` record with three fields:

| Field      | Content                          |
|------------|----------------------------------|
| `kind`     | `'lambda` or `'lambdoid`         |
| `bindings` | `((var . domain) ...)` alist     |
| `body`     | the raw VNB expression           |

Functoids are **not** VNB set-theoretic objects and **not** plain
S-expressions.  They are implementation-level structures that exist
alongside the VNB universe but have no standing within it (no class
contains all functoids; you cannot write `f ∈ FUNCTOID`).

### Why a record rather than an S-expression?

Every important structure in the system carries its own distinguishing
tag — deduction graphs, sequents, wffs, theories, macetes.  This
principle comes from the IMPS system (MIT/Mitre), where all structures
were first-class typed objects in the T language.  The payoff is that
the expression-traversal code — `free-vars`, `subst-free`,
`alpha-equiv?`, `rewrite-subexpressions` — can test `(functoid? e)`
before testing `(pair? e)`, and never accidentally processes a functoid
as an ordinary compound term.

Using a plain S-expression like `(LAMBDA (x A) body)` would work but
would require the traversal code to recognise yet another special head
symbol, and would make it trivial to confuse a functoid with a formula.
The record approach is safer and more explicit.

### `apply-functoid` internal representation

Applying a functoid to arguments produces the mixed structure:

```
(apply-functoid <record> v₁ v₂ ...)
```

The `car` is the symbol `apply-functoid`; the `cadr` is the actual
`<functoid>` record.  This is deliberately asymmetric: the car is a
symbol (so `(pair? e)` is true and `(car e)` gives the dispatch key)
while the cadr is a record (so it carries its own type and cannot be
confused with a variable or a numeric literal).

β-reduction (`pi-functoid-beta!` / `cmd-functoid-beta` / `(beta)`)
finds every `apply-functoid` sub-expression in the goal and replaces it
with `body[x₁ := v₁] ... [xₙ := vₙ]` via a left fold of
capture-avoiding substitutions.

### Surface syntax

Both function application and functoid application are written `f(x)` at
the surface level.  The parser emits `(apply-functoid <record> x)` only
when `f` is already tagged as a functoid at parse time; otherwise it emits
the ordinary S-expression `(f x)`.  Chained application `f(x)(y)` is
handled by `p-maybe-apply`, which loops until no opening parenthesis
follows.

---

## FUN vs. FUNCTOID — the ontological distinction

This distinction causes confusion but is important:

- **`FUN(A, B)`** is a VNB *set* (when `A, B ∈ SET`) — the class of all
  total functions from `A` to `B` in the set-theoretic sense.  Its
  members are sets of ordered pairs.  `FUN` itself is a class-level
  operator (a functoid at the meta level) applied as `apply-functoid(FUN, A, B)`.

- A **functoid** (Scheme record) is a meta-level computation object.
  It *can* represent an element of `FUN(A,B)` — a `lambda` with proved
  typing — but it need not.  A `lambdoid` whose domain is `ORD` is a
  perfectly valid functoid that corresponds to no element of any `FUN`
  class.

The analogy in classical mathematics: a function symbol in first-order
logic can denote a set-theoretic function, but the symbol itself is not
the set; it is a syntactic entity.  Functoids play the role of function
symbols in VNB's implementation.

---

## IMPS historical notes

The IMPS system (Farmer, Guttman, Thayer; JAR 1993) influenced several
VNB design choices:

- **Tagged structures everywhere**: IMPS was implemented in T (an
  object-oriented Lisp dialect), and every structure — inference rules,
  sequents, deduction graphs, theories — had its own type.  VNB
  carries this forward with Scheme `define-record-type`.

- **`apply-operator` for function application**: Late in IMPS
  development, function application was changed from `(f x)` to
  `(apply-operator f x)`.  This required substantial rewriting but was
  correct in hindsight: it disambiguated function application from
  other compound expressions.  VNB uses `apply-functoid` for the same
  reason, applied from the start rather than retrofitted.

- **Local contexts in macetes** (Monk 1988): As a macete's rewriter
  descends into an expression, it accumulates the local hypotheses
  introduced by `IMPLIES` antecedents and `AND` left conjuncts.
  Conditional macetes check their side conditions against this
  accumulated context, not against the top-level sequent hypotheses.
  This is documented in L. G. Monk, "Inference rules using local
  contexts," JAR 4:445–462, 1988.

---

## Arithmetic evaluator — `vnb-do-arith` / `pi-arith!`

The ground arithmetic decision procedure (`arith-eval.scm`) evaluates
closed VNB arithmetic terms and formulas using Scheme's exact arithmetic
(integers and rationals).  Key design points:

- Returns `#t`, `#f`, or `'UNDEF` (not decidable / free variables present).
- Handles `+`, `*`, unary `-`, `recip`, `abs`, `succ`, `conjugate`,
  `power` on exact numbers.
- Short-circuit evaluation for `AND`, `OR`, `IMPLIES` allows
  `(AND #f UNDEF) = #f` without evaluating the second operand.
- The `functoid?` guard at the top of `arith-eval-term` ensures that
  functoid records (which are not arithmetic values) return `#f`
  immediately rather than falling through to the `(pair? e)` branch.

---

## `declare-structure` — syntax design

### Why not quote arguments?

The original `def-structure` required quoted S-expressions:
```scheme
(def-structure 'GROUP '(A) '((MUL (CARTESIAN A A) A) (E A) (INV A A)) '())
```
The new `declare-structure` macro eliminates all quoting:
```scheme
(declare-structure GROUP
  (carriers A)
  (op MUL (CARTESIAN A A) A)
  (constant E A)
  (op INV A A))
```
This is both easier to read and less error-prone (no mismatched quotes).

### Why `er-macro-transformer`, not `syntax-rules`?

MIT Scheme's `syntax-rules` does not properly substitute pattern variables
inside `quote` in template position.  Specifically,
```scheme
(syntax-rules () ((_ name clause ...) (f 'name '(clause ...))))
```
does not quote each `clause` datum — the `...` expansion does not work
inside `'()`.  The fix is `er-macro-transformer`, where `form` is the
raw S-expression after read-time lowercasing, so `(cddr form)` is a
plain Scheme list of clause datums that can be quasiquoted directly:
```scheme
(er-macro-transformer
  (lambda (form rename compare)
    `(def-structure-from-clauses ',(cadr form) ',(cddr form))))
```

### Why no `axioms` clause?

An `(axioms name1 name2 ...)` clause was considered but removed.  The
problem: MIT Scheme evaluates macro arguments before the macro body
runs, so `name1` is looked up as a variable and throws `Unbound variable`.
Characteristic axioms are always installed by separate `theory-add-axiom!`
calls immediately after the `declare-structure` form.

### Stale compiled binaries

MIT Scheme loads `.com` (compiled) files in preference to `.scm` source
files.  After editing `structures.scm`, `(compile-file "structures.scm")`
must be run to update `structures.com`; otherwise the old macro definition
(or its absence) silently takes effect.  The symptom of a stale `.com` is
that the macro appears to fail or be undefined even though the source is
correct.

---

## MIT Scheme evaluation order

MIT Scheme evaluates procedure arguments **right-to-left**.  This matters
whenever a stateful operation (like `dg-post!` which mutates a deduction
graph) appears in argument position alongside an expression that reads
state.  The fix is to `let`-bind the stateful car before constructing
the cons:

```scheme
; WRONG — in MIT Scheme, (cdr ...) evaluates before (car ...)
(cons (dg-post! dg node) (rest ...))

; CORRECT — bind first, then cons
(let ((node (dg-post! dg node)))
  (cons node (rest ...)))
```

---

## scout — speculative depth-bounded proof search (2026-06-23)

A copilot facility that goes beyond *suggesting* a move (`what-now`/`tt`,
`cheap-mac`) to actually *trying tactic sequences* and reporting which ones
close the focus.  Conceptually it is the speculative, backtracking **v2 of
`B+`** (`bplus`) — whose own comment defers exactly this — made cheap by two
pieces that already existed: `vnb--scout-state`/`vnb--scratch-state` (clone the
focus into an **independent deduction graph**) and `apply-recorded-cmd!` (map a
tactic *form* to its `cmd-*`).  A search branch is then just a list of forms
replayed on a fresh clone; backtracking is free — you discard the clone, you
do not undo a move.  The live `*ps*` is never touched.

### grind — the deterministic normalizer

`(grind)` saturates the **no-choice** moves at the focus: `di` (decompose the
goal connective — strip ∀/⇒/∧, introduce binders + hypotheses) and `mac-h*`
(break open the hypotheses — unfold defined predicates, split conjunctions),
looping until neither fires.  Neither move involves *choosing* a lemma, so a
search never has to reconsider them: `grind` just puts the focus into normal
form.  It collapses the whole `di … di mac-h*` prefix that bloats proofs (the
7-page `metric-triangle` PDF) into a **single recorded ply**, and adds no kernel
rule.  Standalone-useful: `(grind)` on `metric-sym` lands you at goal
`(d s)(x,y) = (d s)(y,x)` with the metric's defining properties unfolded in
context.  Implementation calls the `cmd-*` layer directly (bypassing the
recording wrappers) so it logs as one `(grind)`.

### scout / scout-show / scout-run

`(scout [d [b [nodes]]])` runs a breadth-first search whose **alphabet** is the
*choice* moves only — `grind`, the closers (`ass`/`rfl`/`crs`/`arith`), the
top-`b` rewrite-index `mac` rules, and the top-`b` parameterless `bc*` lemmas
(those with no undetermined schema vars, so they run bare).  `di`/`mac-h*` are
folded into the single `grind` ply, so the search never branches on
normalization.  Each frontier node is a *path* of forms, evaluated by replaying
it on a fresh clone under `vnb-guard` (a soft-failing tactic raises inside
`apply-recorded-cmd!` → guard catches → that branch is dead).  Duplicate /
looping states are pruned by a fingerprint of the open-goal set.

Every move is the **real, kernel-checked** tactic, so a reported *closing*
branch is a genuine proof (up to eigenvariable renaming) when adopted.  The
"el cheapo, 'mano" principle: scout does **not reason** about which move is
wise — it brute-forces a small tree and you eyeball the survivors; soundness is
recovered because the survivors actually closed through the kernel.

Bounds, all reported when hit (no silent truncation): depth `d` (default 4),
per-node fan-out `b` (default 3), total nodes (default 300).

`(scout …)` **returns data, does not print** — a nested list

```
(number-of-branches  (d b)  goal  best-partials  closing-branches)
```

where `best-partials` is `((open-count (form …)) …)` most-reduced first, and
`closing-branches` is `((form …) …)` shortest first; the forms are
paste-runnable / evaluable.  Example, on `compact ⇒ totally-bounded` after
`grind` (focus `totally-bounded(s)`):

```
(59 (4 3) (totally-bounded s)
    ((2 ((mac 'totally-bounded)))
     (2 ((mac 'totally-bounded) (mac 'totally-bounded-rev)))
     (3 ((mac 'totally-bounded) (mac 'bdd-metric-carrier-rev)))
     …)
    ())                       ; <- empty closing-branches: scout could not close it
```

`(scout-show …)` runs the same search and **prints** the readable REPL report
(examined count, goal, numbered closing branches or best partials with
goals-left), returning the same nested list.  `(scout-run k)` adopts closing
branch *k* onto the live proof — it evaluates the branch's forms through the
real tactics, so they record and display normally.  Both `scout` and
`scout-show` stash the closing branches in `*last-scout*` for `scout-run`.

### Robustness lesson (the gauge/euclidean-ring crash)

The first roadtest crashed: `(scout)` after `(grind)` on a gauge /
euclidean-ring goal died with *"object 0 passed to symbol->string."*  Root
cause: the BFS ran the fingerprint and candidate-expansion **outside** any
guard (only replay was guarded), so one pathological clone state crashed the
*whole* search.  The state is fine for the kernel, but some rewrite leaves the
goal with a non-symbol (`0`) in head position, and `expression->string` — the
*pretty*-printer, which calls `symbol->string` on operator heads — throws on
it.  The fingerprint used that printer for its dedup key.

Two fixes, both general: (1) the dedup key now uses `write` on the raw s-expr
(`vnb--scout-key`), which never throws on data; (2) the BFS guards the
fingerprint **and** the expansion — a node that throws is dropped as a leaf,
never killing the search — and the whole search runs under `quietly`.  Along
the way `quietly` was taught to bind a new `*vnb-guard-quiet*` flag so the
guard's auto one-line error print is suppressed; otherwise every *expected*
pruned branch sprayed a `;; VNB error:` line.  (There remains a latent,
pre-existing issue worth a separate look: some gauge/euclidean-ring macete
produces a goal `expression->string` cannot render.)

### What scout cannot do yet — the inst lane (planned)

scout's alphabet is entirely **parameterless**.  The first move that needs a
*chosen term* — `(inst <hyp> <witness>)`, instantiate a universally-quantified
hypothesis — is absent.  That is the wall every non-trivial goal hits: after
`grind`, `metric-sym`'s symmetry fact sits inside a hypothesis
`∀u∈X. (… ∧ ∀v∈X. (… ∧ d(u,v)=d(v,u) …))`, and nothing in the current alphabet
can reach it.  So the metric laws, the gauge goal, and `totally-bounded` all
show up as **best-partials, never closures**.

Planned design (build deferred to 2026-06-24):

1. **Candidate generation.**  Scan focus hypotheses for `(FORALL v body)` /
   domain-guarded `(FORALL v (IMPLIES (IN v DOM) body))`.  Witness terms:
   *primary* — the **domain-typed** ones (`t` with `(IN t DOM)` already a
   hypothesis; after `grind` that is `x, y` for `DOM = (X s)` — 1–3 candidates,
   and the inst's domain side-condition is then `ass`-dischargeable); *fallback*
   (untyped ∀) — atomic subterms of goal + hypotheses.  A **relevance filter**
   keeps a `(hyp, term)` pair only if the instantiated body shares symbols with
   the goal (fingerprint overlap), so scout does not instantiate the triangle
   hypothesis while proving symmetry.

2. **Detach companion (the forward-MP gap).**  VNB has no forward modus ponens.
   Instantiating `∀u∈X.body` at `x` yields an *implication* hypothesis
   `(IN x (X s)) ⇒ body[x]` the current alphabet cannot consume.  So the inst
   lane ships a compound **`(inst+ hyp term)`** = instantiate, then
   antecedent-inference (`ai`) to detach, discharging the `(IN x (X s))` guard
   by `ass` — one ply, to keep depth sane.

3. **Interleave + depth.**  The cycle is
   `inst+ (u:=x) → grind → inst+ (v:=y) → grind → close`, ≈ 5 plies; the
   inst-enabled default depth rises to ~6.

4. **Best-first search (the real cost lever).**  inst widens the tree enough
   that pure BFS wastes the node budget.  Order the frontier by open-goal-count
   (depth tiebreak) so scout *dives* toward closure rather than exploring
   breadth uniformly.  This is the single biggest win for landing proofs within
   the node cap.

5. **Soundness/termination.**  inst/ai are real kernel rules, so closing
   branches stay genuine proofs; the el-cheapo is only the witness *guess* (a
   wrong guess just dies on the clone).  The open-goal-set fingerprint blocks
   re-instantiating into an identical state; add per-`(hyp, term)` dedup per
   node and a tight inst fan-out cap.

After the build, re-stress the metric laws / gauge to confirm inst-scout now
**closes** them (today they are partials).

### Stress-test target (planned obstacle map)

*"X totally bounded ⟹ every sequence in X has a Cauchy subsequence"* — the
sequential characterization of total boundedness.  This is a **deep** theorem
(a diagonal / nested-subsequence argument: cover by finitely many 1/n-balls,
pass to a subsequence inside one ball, diagonalize over n).  It is **not** a
closure target for scout+inst — it is an **obstacle-mapping** target: inst-scout
should get *past* the first wall (unfold `totally-bounded`, instantiate the
finite cover at radius `1/n`) and then stall exactly at the diagonal
construction, with `best-partials` marking the boundary, telling us what
machinery to build next.

Prerequisites before it can even be *stated*: (a) an `IS-SUBSEQUENCE` /
reindexing predicate (we have φ : ℕ→ℕ as a strictly-increasing reindexing
*inside* the `cauchy-rapid-subsequence` support, but no standalone vocabulary);
(b) the statement form `∀ f:ℕ→X(s). ∃ φ strictly-increasing.
IS-CAUCHY-SEQ(s, k ↦ f(φ k))`.  `IS-CAUCHY-SEQ` and `CONVERGES-TO` already
exist.
