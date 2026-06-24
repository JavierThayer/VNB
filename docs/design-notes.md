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

### The inst lane — scout's witness-choosing move (BUILT 2026-06-24)

scout v1's alphabet was entirely **parameterless**, so the first move that needs
a *chosen term* was missing and every witness-needing goal stalled as a partial.
The inst lane closes that gap.  scout now **closes `metric-sym`** end to end
(`scout-run` drives the live deduction graph to QED, all kernel-checked).

1. **`inst+` — instantiate then detach.**  `(inst+ hyp term)` (`cmd-inst+`,
   proof-commands.scm) instantiates an in-context universal at `term`, then
   forward-detaches each guard whose antecedent is already in context, peeling a
   guarded `(IMPLIES (IN term DOM) P)` down to `P`.  It is the *hypothesis-side*
   analogue of `fact` (which assembles a THEOREM); `inst+` assembles an
   in-context UNIVERSAL.  **Design correction:** the planned detacher was `ai`
   (antecedent-inference), but `ai` only decomposes AND/OR/NOT/FORSOME/IFF
   assumptions — it has *no IMPLIES case*.  The right tool is `cmd-detach`
   (`pi-detach!`, forward modus ponens), which is what `inst+` uses.

2. **Candidate generation** (`vnb--scout-inst-candidates`, suggest.scm).  Scan
   focus hypotheses for `(FORALL v body)`.  Witness terms come from the
   **context-typed** pool: every `t` with an assumption `(IN t S)`.  A guarded
   `(FORALL v (IMPLIES (IN v DOM) …))` prefers witnesses with `S = DOM` (its
   guard is then `detach`-dischargeable); the rest are the fallback.  A
   **relevance filter** keeps `(hyp, term)` only if the instantiated body shares
   a non-connective symbol with the goal, and a per-node guard skips a
   `(hyp, term)` whose instance is already an assumption.  Ranked by overlap,
   capped at `*scout-inst-fanout*` (6).  Candidates are emitted **first** in the
   expansion so the dive tries witnesses before the doomed parameterless moves.

3. **Depth.**  The `metric-sym` closer is `grind / inst+ (u:=x) / grind /
   inst+ (v:=y) / grind / ass` — note the **interleaved `grind`s**: `is-metric`
   unfolds to a *single* `(FORALL u …)` whose body is the five laws AND-ed under
   the `u,v,w` quantifiers, so after each `inst+` a `grind` is needed to split
   the exposed conjunction and surface the next inner `(FORALL v …)` / the bare
   equality.  That is **5 plies** ⇒ default depth raised 4 → 6 (`*scout-depth*`),
   node budget 300 → 600.

4. **Best-first search (the real cost lever) + the open-goal-count bug.**  The
   frontier is ordered by open-subgoal count (deeper-first tiebreak, so scout
   *dives*).  **This forced a correctness fix.**  `proof-open-goals` =
   `dg-ungrounded-nodes` returns *every ungrounded node including ancestors*, so
   its count **grows with derivation length** — and since each `inst+` adds
   ancestor nodes, best-first read the inst chain as *regress* and fled it.  The
   genuine "how much is left" measure is the count of ungrounded **leaves**
   (nodes with null `in-arrows` — the actual obligations); `vnb--scout-open-leaves`
   computes it, and the fingerprint now keys on the leaf frontier too.

5. **The `-rev` cycle trap.**  A `-rev` round-trip `((mac 'foo)(mac 'foo-rev))`
   folds the goal back to an *identical* sequent; `dg-post!` dedups onto the
   earlier node, and the graph closes into a **cycle** where every node has an
   in-arrow — so open-leaves = 0 while the proof is **not** done.  Counting
   leaves naively reported this as a bogus "0 open" best-partial (and best-first
   would chase it).  Fix: a non-done clone with **no open leaf is a dead end** —
   prune it (don't record, don't expand).

6. **Soundness/termination.**  `inst+` is `cmd-instantiate` + `cmd-detach`, both
   real kernel rules, so a closing branch is a genuine proof; the only el-cheapo
   is the witness *guess* (a bad guess — e.g. instantiating the open-cover
   `∀c` at the carrier `(X s)` — just produces a useless hypothesis that dies on
   the clone).  Leaf-set fingerprint + per-`(hyp,term)` dedup + the fan-out cap
   bound the widening.

**What it still cannot do:** witnesses scout cannot *type* from the context — a
fresh existential, a constructed term like `1/n` — are out of reach; those goals
still surface as best-partials.  That is the next frontier (see the stress
target below).

### The ew lane — existential-GOAL introduction (BUILT 2026-06-24)

The dual of the inst lane.  `inst+` witnesses a universal **hypothesis**; the
Cauchy-subsequence stress test showed the matching gap on the other side —
scout's alphabet had **no move that witnesses an existential goal**, so the
`∃N` Cauchy threshold (and any `∃φ`, `∃L`) stalled as a partial even when the
witness was sitting in context.  `(ew TERM)` (`cmd-exists-witness`, a real
kernel rule) discharges a `FORSOME` goal by supplying the witness; this lane
chooses that term.

- **Candidate generation** (`vnb--scout-ew-candidates`, suggest.scm).  Fires
  only when the focus goal is `(FORSOME v body)`.  Witness pool is the **same**
  context-typed terms as the inst lane (`vnb--scout-typed-terms` — every `t`
  with an `(IN t S)` assumption).  Where a guarded universal reads
  `(FORALL v (IMPLIES (IN v DOM) …))`, the existential guard is an **AND**:
  `(FORSOME v (AND (IN v DOM) …))` — so the domain is `(car (binary-left body))`
  under `AND`, and witnesses with `S = DOM` are tried first.  Relevance score is
  the witnessed body's symbol overlap with the **assumptions** (the body becomes
  the new goal — prefer a witness the context can discharge), capped at
  `*scout-ew-fanout*` (6).
- **The numeric-`N` case falls out for free.**  Once a null/Cauchy threshold has
  been skolemized into context as `(IN N0 NN)`, `N0` *is* a context-typed term,
  so on goal `(FORSOME N (AND (IN N NN) …))` the lane offers `(ew N0)` first
  (domain `NN` matches), and the `RR`-typed `eps` is correctly excluded.  The
  witness scout *"never offered"* per the stress-test write-up is now proposed by
  the structural dual — no special numeric extraction needed.
- **Integration.**  Emitted **first** in `vnb--scout-expand` alongside the inst
  candidates (witness moves are the productive dive on stuck goals).  `ew` fires
  only on a `FORSOME` focus and `inst+` only when a universal hypothesis is
  present, so the two never both apply at one node — no double fan-out.
  `what-now--show-ew` renders the same ranked candidates as `(ew term)` for the
  single-move copilot, so search and what-now agree on the witness.
- **Soundness.**  `cmd-exists-witness` *warns* (soft-fails) on a non-existential
  goal or an ill-typed witness, so a bad guess dies on the clone under
  `vnb-guard`; a closing branch is a genuine kernel proof.

**Still open (the next dual):** scout has no `ai` — it cannot *skolemize* an
existential **hypothesis** to GET the threshold `N0` into context in the first
place (the forward step the by-hand Cauchy assembly does with `ai`).  The ew
lane consumes a context that an `ai` lane would have to produce.  That
`ai`-suggester is the remaining gap between the by-hand assembly and a fully
automated `totally-bounded ⇒ Cauchy-subseq` close.

### The citation guard (2026-06-24)

A closing branch that discharges the goal by citing a library theorem
*alpha-equal to the goal itself* is `P proved by P` — kernel-valid but vacuous:
it only shows the goal is already a (often merely **asserted**) theorem, not
that scout found a proof.  This surfaced when `(scout)` on
`∀s. is-compact(s) ⇒ is-complete(s)` produced `… (bc* 'compact-implies-complete)
…` — and `compact-implies-complete` *is* that statement, an asserted PSS
citation whose real proof lives offline.  Circular.

`vnb--scout-cites-names` scans a path's goal-discharging steps (`bc*`/`bc`/
`fact`/`ta`; their first arg is the theorem name) and flags a cited theorem `T`
that is circular **directly or transitively** (`vnb--circular-citation?`):
*direct* — `T`'s statement is `alpha-equiv?` to the goal (`P by P`); *transitive*
— a name alpha-equal to the goal is in `debt-of(T)`, i.e. `T` was itself proven
*using* the goal (proof-debt.scm's transitive asserted-fact closure).  The
transitive case is the **`compact⇒complete` by `compact⇒bongo` + `bongo⇒complete`**
trap: neither lemma *is* the goal, but if `bongo⇒complete`'s proof leaned on
`compact⇒complete`, citing it is circular.  The goal's theorem name(s) are
resolved once per `scout` call by `vnb--goal-theorem-names` (reverse lookup over
the theorem table) and reused per closer.  `vnb--scout-collect` partitions the
closers: genuine ones become `closing-branches` (and `*last-scout*`, so
`scout-run` can never adopt a circular closure); the suppressed theorem names
go to `*scout-citations*` and the report prints *"the goal is already theorem
X — citing it would be circular."*

**Honest limit of the transitive check.**  `debt-of` of an *asserted* fact is
just itself (a leaf) — no live dependency edges run between assertions.  A loop
built entirely from independent asserted PSS citations therefore has nothing for
the guard to detect; composing them is valid-but-redundant, and any real
circularity lives in their *offline* proofs.  That layer is warrant/debt hygiene
(proof-debt trust levels + the warrant audit), not scout's to police.  The
transitive guard closes the loop precisely for chains through **proven** lemmas,
whose debt the live system actually tracks.  (Note also: in the base load *every*
proven theorem is modulo 0, so there is no natural transitive-circular pair yet
— the test synthesises one.)

Note this is what makes `inst+`-style
*definitional* proofs the honest kind: `metric-sym` posed in full still closes
genuinely (unfold the `is-metric` definition, instantiate) — it does **not**
cite the `metric-sym` theorem — whereas a goal scout cannot re-derive
(`equality-symmetry`, which needs `subst`) has only the circular closure, and is
correctly left open with the citation noted.

The deeper lesson for stress targets: a goal that is **already an asserted
theorem** (`compact⇒complete`, `compact⇒totally-bounded`, …) is a bad scout
demo — citing it proves nothing.  Point scout at goals *not* already in the
library.

### Stress-test: totally bounded ⟹ has Cauchy subsequence (2026-06-24, BUILT)

*"X totally bounded ⟹ every sequence in X has a Cauchy subsequence"* — the
sequential characterization of total boundedness, a diagonal/nested-subsequence
argument.  Now **stated and decomposed** in `theorem-library/cauchy-subsequence.scm`,
with a runnable obstacle-map probe in `calculus/totally-bounded-cauchy-subseq.scm`.

**Vocabulary added** (was the stated prerequisite): `STRICTLY-MONO-NN` (φ:ℕ→ℕ
strictly increasing — factored out of the three inline copies in
subsequence-capture / nn-enum-spec / cauchy-rapid-subsequence); `SUBSEQ(f,φ)` =
`k ↦ f(φ k)`; `IS-SUBSEQUENCE`; `NULL-RR-SEQ` (positive + → 0, elementary eps/N
form).  Case-fold trap dodged: the block family variable is `blk`, **not** `S`,
because the reader folds `S`≡`s` and the space `s` is in scope.

**Decomposition** — every leaf already existed; this theorem was the *intended*
consumer named in `pigeonhole.scm` / `diagonalization.scm`:
- `block-family` (new, warranted): TB + null `rad` ⟹ a nested family
  `blk : ℕ→INF-SUBSETS(ℕ)`, each `blk(k)` pinning `f` into one `rad(k)`-ball.
  The pigeonhole recursion — the one genuinely new construction.
- `diagonalization` (existing): nested infinite blocks ⟹ strictly-mono φ with
  tail past `k` inside `blk(k)`.
- `ball-2r-triangle` (existing): two points in one `r`-ball are `< 2r` apart.
- `null-rr-seq-exists` + the rad-parametrised / parameter-free headlines.

**What the probe established (the actual stress-test result):**
1. The **forward assembly is fully driveable by hand** through the kernel.
   `fact` cites a PSS universal, instantiates it, and auto-detaches in-context
   antecedents; `ai` skolemizes the resulting existential; `ew` witnesses an
   existential *goal*.  block-family's `∃ blk` skolemizes to `blk_2`,
   diagonalization's `∃ (diagonal)` to `f_3`, and `(ew f_3)` splits the goal into
   `strictly-mono-nn(f_3)` and `is-cauchy-seq(s, subseq(f,f_3))`.
2. The **`STRICTLY-MONO-NN` half closes to grounded** by `(mac)(di)(ass-all)` —
   both conjuncts are literally diagonalization's output in context.  (Verified
   via the ungrounded-LEAF frontier: `(strictly-mono-nn is-cauchy-seq)` → `(is-cauchy-seq)`.)
3. **Scout cannot drive the rest**, and this is the headline finding.  On
   `is-cauchy-seq` scout returns `closing=()` (genuine non-closure — `*scout-citations*`
   empty, not a suppressed circular citation).  Its `best-partials` are only
   `mac`/`grind` unfolds and `inst+` on universal *hypotheses*.  **Scout's
   alphabet has no existential-GOAL introduction.**  Proving `is-cauchy-seq`
   needs `∃ N` (the Cauchy threshold) witnessed from `NULL-RR-SEQ` at `eps/2`;
   `inst+` chooses witnesses for ∀-hypotheses, but nothing offers a witness for a
   `FORSOME` goal.

**Next machinery (recommended):** an **`ew`-suggester lane** — the dual of
`vnb--scout-inst-candidates` — that proposes context-typed terms (and, for
numeric thresholds, the `N` extracted from a null/Cauchy hypothesis) as
existential-goal witnesses, for both `what-now` and scout's alphabet.  This is
the single gap between the by-hand assembly and an automated close.  The maths
beyond it (the eps/2 + ball-2r-triangle estimate) is then ordinary ∀-instantiation
+ arithmetic, which the inst lane already handles.
