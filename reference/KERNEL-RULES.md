# VNB kernel inference rules — the trusted base beyond the axiom table

The catalog (`THEOREMS.md`) lists the **axioms** of VNB set theory — the
first-order formulas installed by `make-vnb-base-theory` (`theory.scm`) and the
`theorem-library` axiom files, stamped `primitive`. That list is **not the whole
trusted base.** A second group of trusted principles lives in the proof checker
itself, as **primitive inference rules** (`primitive-inferences.scm`, the
`pi-*!` procedures). They are implemented in Scheme rather than derived from any
axiom, so anyone establishing what VNB *assumes* must read them alongside the
axioms. This page states them.

Why some principles are rules rather than axioms: a few set-theoretic
constructors carry a **schema** in their body — a metavariable ranging over
*formulas* — that cannot be written as a clean first-order axiom without
higher-order quantification. Separation `{x ∈ A | p}`, comprehension `{x | p}`
and the indexed union `⋃_{z∈A} body` are the central cases. Rather than admit a
formula variable, VNB characterises these constructors at the kernel level, one
rule per elimination/introduction direction. The catalog says as much where it
lists the axioms — *"Fixed, though not finite (separation/replacement are
schemas)"* — and those schemas are stated below.

Throughout, each rule has a **name** — `sep-mem-elim`, `forall-intro`, `cut` —
which is recorded in the deduction graph with every inference it justifies. (The
source calls this recorded name a *tag*.) The name is the unit of trust, not the
command that produced it: one command may record any of several rules according
to the shape of the goal, and two commands may record the same rule.

Stated compactly:

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
  side condition. Its context-side twin `iota-in-elim` (`pi-iota-in-elim!`,
  tactic `iota-e`, added 2026-09-15) runs the other way: when the context
  already establishes that the description **denotes** — it carries
  `(IN (IOTA x p) X)`, or an equation naming the term — the defining property
  `p[x := IOTA(x,p)]` is granted with no obligation posted. Soundness rests on
  two things the kernel already commits to: atomic formulas are strict, so a
  true membership entails that its subject denotes (this is exactly
  `asm-establishes-defined?`, primitive-inferences.scm:627, which `rfl` uses to
  close `t = t`, and the rule calls that predicate rather than re-testing the
  assumption shape, so the two cannot drift); and a description that denotes
  denotes the unique satisfier of its property, which is the same semantics
  `iota-def` relies on when it grants the property after existence and
  uniqueness are proved. With no definedness witness in the context the rule
  declines rather than assuming denotation.
- **`VNB-LAMBDA([x…], body)`** — the function-builder (`pi-lambda-type!` /
  `pi-lambda-beta!` / `pi-lambda-beta-hyp!`, tactics `lam-t` / `lam-b` /
  `lam-b-h`): typing into `FUN` and β-reduction
  `(VNB-LAMBDA([x], body))(a) = body[x:=a]`, in the goal (`lambda-beta`) or in
  an assumption (`lambda-beta-hyp`, primitive-inferences.scm:1415, driven from
  interactive.scm). The carrier of every `def-functoid` whose body is a
  `VNB-LAMBDA` (e.g. `BDD-METRIC`).

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
The **rule name** is the unit of trust, not the tactic.

| rule | tactic | note |
|---|---|---|
| `and-intro` `or-intro-left` `or-intro-right` `implies-intro` `not-intro` `iff-intro` `forall-intro` | `di`, `oi-l`, `oi-r` | goal-side introduction |
| `and-elim` `or-elim` `not-elim` `iff-elim` `forsome-elim` | `ai` | assumption-side elimination. `not-elim` fires only when the positive is **already** in context |
| `forsome-intro` | `ew` | supply a witness |
| `forall-elim` | `inst`, `inst+`, `fact` | instantiate a universal at `t`; since 2026-09-18 owes the side sequent `t = t` unless `t` is certified defined (a variable, a class term on defined arguments, an accessor of a structure the context has, or a term the context types) -- LUTINS instantiation; see docs/definedness-instantiation-2026-09-18.md |
| `assumption` `theorem-assumption` | `ass`, `ta`, `fact` | close from context / cite an installed theorem |
| `cut` `weakening` `detach` `backchain` | `cut`, `have!`, `wk`, `detach!`, `bc`, `bc*` | |
| `proof-by-contradiction` | `pbc` | |
| `truth-intro` `contraposition` | — | implemented, but reachable from no proof command; no proof in the library records either |
| `eq-subst` | `subst` | Leibniz; fires on `=` **or** `==`, with the equation in the context in either orientation. Rewrites in operator position too (since 2026-09-16) |
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
| `transfinite-induction` | `tfi` | **strong** transfinite induction on `ORD`. Distinct from, and not to be confused with, the `transfinite-induction` **axiom** in `structure-library/ordinals.scm` — same name, two different trusted objects |
| `transfinite-induction-3cases` | `tfi3` | base / successor / limit |

---

## Rewriting is a kernel rule too

Rewriting records rules of its own, and they are trusted exactly like the rules
above.

| rule | driven by | note |
|---|---|---|
| `macete` | `mac`, `macm` | rewrite the **goal** by an installed macete (`macetes.scm`) |
| `macete-hyp` | `mac-h`, `mac-h*` | rewrite an **assumption**. Replaces it |
| `cartesian-decompose` | `mac` | procedural macete (`theory.scm`): `x ∈ CARTESIAN(A₁…Aₙ)` to its existential chain |
| `tuple-equality-decompose` | `mac` | procedural macete (`theory.scm`): `LIST(a…) = LIST(b…)` to the conjunction of components |

The recorded rule carries the source and replacement patterns as arguments;
those are per-application data, not part of the trusted base.

---

## Oracles — trusted decision procedures

A tactic of kind `oracle` closes a goal by running a decision procedure and
recording a single rule. Each is sound and complete on its own domain, but it is
**trusted rather than reduced to the axioms**: nothing derives it from the rules
above, so each one widens the trusted base and is listed here for that reason.
Four of the five procedures live in `structure-library/` rather than in the kernel
directory, which does not make them any less trusted.

| rule | tactic | source |
|---|---|---|
| `arith-ground` | `arith` | `arith-eval.scm` — decide a closed arithmetic sentence |
| `arith-forsome` | `arith` | `arith-eval.scm` — witness a ground existential |
| `arith-simplify` | `arith` | `arith-eval.scm` — substitute ground context equations, then decide |
| `ring-simplify` | `rs`, `simp` | `structure-library/ring-simplify.scm` |
| `comm-ring-simplify` | `crs` | `structure-library/comm-ring-simplify.scm` |
| `ineq` | `ineq` | `structure-library/ineq-oracle.scm` — the `RR` order calculus |
| `sos` | `sos` | `structure-library/sos-oracle.scm` — sum-of-squares nonnegativity |

So the statement of the trusted base, refined:

> **trusted base = the `primitive` axioms in THEOREMS.md + every rule recorded
> in a deduction graph: the 13 schemas, the 42 logical, equational and
> structural rules, the 4 rewriting rules, and the 7 decision procedures, 66
> rules in all.**

The page *The kernel* describes each of the 66 by its effect on the deduction graph and is
the fuller statement; the counts there are generated from the registry the startup check uses.

---

## This list is checked against the system, not maintained by hand

A document of this kind is only useful if it cannot quietly fall out of step
with the program it describes. Two checks run every time the system starts.

`kernel-rules-audit` compares the rules actually recorded during the load
against the documented list (`*kernel-rule-tags*`), in **both** directions, and
reports either kind of discrepancy: a rule recorded but not documented — trusted
code that nobody wrote down — and a rule documented but never exercised, which
is either a rule no proof needs or one no command can reach.

`kernel-callers-audit` checks the other half: that only the eight permitted
files record inferences at all. It reads every file of the system with the
Scheme reader, and halts the load naming any file outside that list which calls
`dg-apply-rule!`, or which passes it on as a value. The inventory of entry
points, and of which proof command reaches which, is `KERNEL-MAP.md`.
