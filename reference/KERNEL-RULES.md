# VNB kernel inference rules — the trusted base beyond the axiom table

The catalog (`THEOREMS.md`) lists the **axioms** of VNB set theory — the
first-order formulas installed by `make-vnb-base-theory` (`theory.scm`) and the
`theorem-library` axiom files, stamped `primitive`. That list is **not the whole
trusted base.** A second group of trusted principles lives in the proof checker
itself, as **primitive inference rules** (`primitive-inferences.scm`, the
`pi-*!` procedures, dispatched through `apply-recorded-cmd!` in
`interactive.scm`). They are checked by hand-written Scheme, not derived from any
axiom, so anyone auditing what VNB *assumes* must read them too. This file
documents them.

Why some principles are rules rather than axioms: a few set-theoretic
constructors carry a **schema** in their body — a metavariable ranging over
*formulas* — that cannot be written as a clean first-order axiom without
higher-order quantification. Separation `{x ∈ A | p}`, comprehension `{x | p}`
and the indexed union `⋃_{z∈A} body` are the central cases. Rather than admit a
formula variable, VNB characterises these constructors at the kernel level, one
rule per elimination/introduction direction. (`theorem.scm`'s axiom prose
already flags this: *"Fixed, though not finite (separation/replacement are
schemas)."* The schemas themselves are below.)

This is the honest statement of the trusted base:

> **trusted base = the `primitive` axioms in THEOREMS.md + the kernel rules below.**

---

## Set- & class-formation schemas (the set-existence content)

These are the rules that *make sets exist*. Everything here is in
`primitive-inferences.scm`, the "D-7" block (`SEP`/`COMP`/`BIG-UNION`), with
sethood and membership directions. `⊢ G ⇐ ⊢ S₁ … ⊢ Sₙ` reads "to prove goal
`G`, prove subgoals `S₁ … Sₙ`"; `[x:=y]` is capture-avoiding substitution.

### SEPARATION — `SEP(x, A, p)` = `{ x ∈ A | p }`

A subclass of `A` cut out by a formula `p` (with `x` bound in `p`). A separation
over a **set** is a set.

| rule (`pi-…!`) | tactic | shape |
|---|---|---|
| `sep-sethood`   | `sep-set` | `⊢ SEP(x,A,p) ∈ SET  ⇐  ⊢ A ∈ SET` |
| `sep-mem-intro` | `sep-mi`  | `⊢ y ∈ SEP(x,A,p)  ⇐  ⊢ y ∈ A   and   ⊢ p[x:=y]` |
| `sep-mem-elim`  | `sep-me`  | assumption `y ∈ SEP(x,A,p)`  ⤳  context gains `y ∈ A` and `p[x:=y]` (the membership assumption is consumed) |

### COMPREHENSION — `COMP(x, p)` = `{ x | p }`  (class formation)

The class of all **sets** `x` satisfying `p`. Generally a *proper* class; its
members are sets (`membership-implies-sethood`), which is why intro/elim carry
the `∈ SET` side condition rather than a domain.

| rule (`pi-…!`) | tactic | shape |
|---|---|---|
| `comp-mem-intro` | `comp-mi` | `⊢ y ∈ COMP(x,p)  ⇐  ⊢ y ∈ SET   and   ⊢ p[x:=y]` |
| `comp-mem-elim`  | `comp-me` | assumption `y ∈ COMP(x,p)`  ⤳  context gains `y ∈ SET` and `p[x:=y]` |

(There is no `comp-sethood`: a comprehension is a class, a set only when
separately shown bounded by a set.)

### BIG-UNION — `BIG-UNION(z, A, body)` = `⋃_{z ∈ A} body`

The indexed/dependent union — VNB's replacement-style binder (the ZF
`⋃a` is the special case `BIG-UNION(s, S, s)`). The `body` is a class **schema**
in `z`. A big-union of a set-indexed family of sets is a set.

| rule (`pi-…!`) | tactic | shape |
|---|---|---|
| `big-union-sethood`   | `bu-set` | `⊢ BIG-UNION(z,A,body) ∈ SET  ⇐  ⊢ A ∈ SET   and   ⊢ ∀z. z ∈ A ⇒ body ∈ SET` |
| `big-union-mem-intro` | `bu-mi`  | with witness `w`: `⊢ x ∈ BIG-UNION(z,A,body)  ⇐  ⊢ w ∈ A   and   ⊢ x ∈ body[z:=w]` |
| `big-union-mem-elim`  | `bu-me`  | assumption `x ∈ BIG-UNION(z,A,body)`  ⤳  fresh eigenvariable `e`; context gains `e ∈ A` and `x ∈ body[z:=e]` |

### Related term-formers (same "schema in the body" reason)

- **`IOTA(x, p)`** — definite description "the `x` such that `p`" (`pi-iota-def!`,
  tactic `iota-d`). Characterised by its defining property under a uniqueness
  side condition.
- **`VNB-LAMBDA([x…], body)`** — the function-builder (`pi-lambda-type!` /
  `pi-lambda-beta!`, tactics `lam-t` / `lam-b`): typing into `FUN` and
  β-reduction `(VNB-LAMBDA([x], body))(a) = body[x:=a]`. The carrier of every
  `def-functoid` whose body is a `VNB-LAMBDA` (e.g. `BDD-METRIC`).

---

## The remaining logical rules (standard logic, equality, structure)

These add **no set-existence strength** — they are the ordinary natural-deduction
and congruence rules plus the structure/number eliminators. Trusted, but they
prove nothing the underlying logic + the axioms/schemas above don't already
license. All are `pi-*!` in `primitive-inferences.scm`.

Note that a single tactic often stamps several tags: `di` emits whichever of
`and-intro`, `or-intro-*`, `implies-intro`, `not-intro`, `iff-intro`,
`forall-intro` the goal calls for, and `ai` emits whichever of `and-elim`,
`or-elim`, `not-elim`, `iff-elim`, `forsome-elim` the cited assumption calls for.
The **tag** is the unit of trust, not the tactic.

| tag | tactic | note |
|---|---|---|
| `and-intro` `or-intro-left` `or-intro-right` `implies-intro` `not-intro` `iff-intro` `forall-intro` | `di`, `oi-l`, `oi-r` | goal-side introduction |
| `and-elim` `or-elim` `not-elim` `iff-elim` `forsome-elim` | `ai` | assumption-side elimination. `not-elim` fires only when the positive is **already** in context |
| `forsome-intro` | `ew` | supply a witness |
| `forall-elim` | `inst`, `inst+`, `fact` | instantiate a universal |
| `assumption` `theorem-assumption` | `ass`, `ta`, `fact` | close from context / cite an installed theorem |
| `cut` `weakening` `detach` `backchain` | `cut`, `have!`, `wk`, `detach!`, `bc`, `bc*` | |
| `proof-by-contradiction` | `pbc` | |
| `truth-intro` `contraposition` | — | **unreachable**: `pi-truth!` and `pi-contraposit!` are implemented and called from nowhere |
| `eq-subst` | `subst` | Leibniz; fires on `=` **or** `==`. Reaches argument positions only, never operator position |
| `reflexivity` | `rfl` | `t = t`, and only with `t` **defined** |
| `quasi-reflexivity` | `qrfl` | `t == t`, unconditionally |
| `if-true` `if-false` | `if-true`, `if-false` | |
| `cartesian-intro` `cartesian-elim` | `ci`, `ce` | |
| `tuples-intro` `tuples-elim` | `ti`, `te` | |
| `union-intro` `union-elim` | `ui`, `ue` | |
| `intersection-intro` `intersection-elim` | `ii`, `ie` | |
| `nth-reduce` `length-reduce` | `nth-r`, `len-r` | `NTH` / `LENGTH` of a literal `LIST` |
| `functoid-beta` | `beta` | |
| `nn-induction` | `ni` | induction on `NN` |
| `transfinite-induction` | `tfi` | **strong** transfinite induction on `ORD`. (Not "tuple-function image", which is what this file said until 2026-07-28.) Distinct from, and not to be confused with, the `transfinite-induction` **axiom** in `structure-library/ordinals.scm` — same name, two different trusted objects |
| `transfinite-induction-3cases` | `tfi3` | base / successor / limit |

---

## Rewriting is a kernel rule too

Macete application stamps its own tags, and they are trusted surface exactly like
the rules above. This section did not exist before 2026-07-28.

| tag | driven by | note |
|---|---|---|
| `macete` | `mac`, `macm` | rewrite the **goal** by an installed macete (`macetes.scm`) |
| `macete-hyp` | `mac-h`, `mac-h*` | rewrite an **assumption**. Replaces it |
| `cartesian-decompose` | `mac` | procedural macete (`theory.scm`): `x ∈ CARTESIAN(A₁…Aₙ)` to its existential chain |
| `tuple-equality-decompose` | `mac` | procedural macete (`theory.scm`): `LIST(a…) = LIST(b…)` to the conjunction of components |

The tag carries the source and replacement patterns as arguments; those are
per-application data, not part of the trusted surface.

---

## Oracles — trusted decision procedures

A tactic of kind `oracle` (`*tactic-kind*`, `tactics-help.scm`) closes a goal by
running a decision procedure and stamping a single tag. It is sound and complete
on its domain, but it is **trusted rather than mechanised through the axioms**:
nothing reduces it to the rules above. Three of the four live in
`structure-library/`, not in the kernel, which does not make them less trusted.

| tag | tactic | source |
|---|---|---|
| `arith-ground` | `arith` | `arith-eval.scm` — decide a closed arithmetic sentence |
| `arith-forsome` | `arith` | `arith-eval.scm` — witness a ground existential |
| `arith-simplify` | `arith` | `arith-eval.scm` — substitute ground context equations, then decide |
| `ring-simplify` | `rs`, `simp` | `structure-library/ring-simplify.scm` |
| `comm-ring-simplify` | `crs` | `structure-library/comm-ring-simplify.scm` |
| `ineq` | `ineq` | `structure-library/ineq-oracle.scm` — the `RR` order calculus |
| `sos` | `sos` | `structure-library/sos-oracle.scm` — sum-of-squares nonnegativity |

So the honest statement of the trusted base, refined:

> **trusted base = the `primitive` axioms in THEOREMS.md + every
> `dg-apply-rule!` tag: the schemas, the logical rules, the two rewrite tags, and
> the seven oracle tags.**

---

*This file is **checked**, not merely hand-maintained. `dg-apply-rule!`
(`deduction-graphs.scm`) records every tag it stamps; `*kernel-rule-tags*`
(`tactics-help.scm`) is the documented list; `kernel-rules-audit` compares the
two at the end of every load and reports both directions — a tag stamped but not
documented (trusted surface nobody wrote down) and a tag documented but not
exercised (a rule no proof uses, or one no tactic can reach). If you add a
`pi-*!` rule or an oracle, add its tag to `*kernel-rule-tags*` and describe it
here; the audit will tell you if you forget the first, and only a reader will
notice if you forget the second.*
