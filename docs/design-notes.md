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
  (op MUL (A A) A)
  (constant E A)
  (op INV (A) A))
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
