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

## The remaining kernel rules (standard logic, equality, structure)

These add **no set-existence strength** — they are the ordinary natural-deduction
and congruence rules plus the structure/number eliminators. Trusted, but they
prove nothing the underlying logic + the axioms/schemas above don't already
license. Listed by name (all `pi-*!` in `primitive-inferences.scm`):

- **Propositional / quantifier:** `direct-inference` (di), `antecedent-inference`
  (ai), `exists-witness` (ew), `instantiate` (inst), `weaken` (wk), `cut`,
  `assumption` (ass), `or-intro-left/right` (oi-l/oi-r), `truth`, `backchain`
  (bc/bc*), `detach`, `contraposit`, `proof-by-contradiction` (pbc),
  `theorem-assumption` (ta).
- **Equality (partial / quasi):** `eq-subst` (subst — fires on `=` **or** `==`),
  `reflexivity` (rfl — `t = t` only with `t` defined), `quasi-reflexivity` (qrfl
  — `t == t` unconditionally). See `=` vs `==` in the partial-equality note.
- **Conditionals:** `if-true` / `if-false`.
- **Structure / tuples / numbers:** `cartesian-intro/elim` (ci/ce),
  `tuples-intro/elim` (ti/te), `nth-reduce` (nth-r), `functoid-beta` (beta),
  `union-intro/elim` (ui/ue), `intersection-intro/elim` (ii/ie), `tfi` / `tfi3`
  (tuple-function image), `nn-induction` (ni).

---

*Hand-maintained. Source of truth: `primitive-inferences.scm` (the `pi-*!`
procedures) and the replay dispatch in `interactive.scm` (`apply-recorded-cmd!`).
If you add or change a `pi-*!` rule that carries set-existence or logical
content, update this file — it is the only place the kernel's trusted surface is
written down in prose.*
