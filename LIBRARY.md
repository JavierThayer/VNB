# VNB Library — Topical Index

A reader's map of what the system knows at startup. Organised by what
you'd reach for, not alphabetically. Each entry: the operator or
predicate, a one-line description, and the file where its axioms live.

Companion documents:

- `STRUCTURES.md` — the algebraic structure hierarchy (groups, rings, …).
- `THEOREMS.md` — full alphabetical catalog of all 367 axioms and
  proven theorems (currently 20 proven, 347 axioms); auto-regenerated
  by `(catalog)` on load.

This file is hand-curated. When you add a new top-level operator or
predicate, add it here too.

---

## 1. Number systems

The five basic numeric domains, in increasing order: **NN ⊆ ZZ ⊆ QQ ⊆ RR ⊆ CC**.
Polymorphic n-ary arithmetic: `+`, `*`, `-`, `recip`, `abs`, `conjugate`,
`succ`, `<=`. Numeric literals 0, 1, 2, … live in ZZ (non-negative in NN).
The `(arith)` tactic closes any ground numeric goal.

- `NN, ZZ, QQ, RR, CC` — classes; sethood + closure axioms.
  `number-systems.scm`.
- `binplus, bintimes, binneg` — binary versions of `+ * -`, typed
  separately for each domain; the bridge to ring/monoid structure.
  `structure-library/numeric-instances.scm`.
- `(arith)` — evaluator/decision procedure for ground arithmetic;
  closes `(succ 0) = 1`, `(= (+ 2 3) 5)`, …
  `arith-eval.scm`.
- `(rs)` (ring-simplify) — polynomial-normal-form decision procedure
  for ring identities; symbols not numerically reducible are treated as
  generators.  `structure-library/ring-simplify.scm`.

## 2. Sets, classes, finiteness

- `SET` — class of sets (no proper classes). Kernel.
- `EMPTY-SET, IN, SEP, COMP, IOTA` — kernel set-formation. `theory.scm` + `theorem-library/axioms.scm`.
- `POWER A` — power set of A; `POWER(A,B) = FUN(B,A)`. `theorem-library/axioms.scm` (power-exp).
- `FUN A B` — class of total functions A → B. Kernel.
- `TUPLES A` — tuples (lists) over A.  Kernel + axioms.
- `LIST a₁ … aₙ`, `LENGTH`, `NTH k x` — list constructors/projections.
  `(nth-r)` reduces `(NTH k (LIST …))`.  Kernel.
- `CARTESIAN A B` — Cartesian product.  Kernel.

## 3. Ordinals & cardinality

The transfinite backbone underneath sequences, cardinality, finsum.

- `ORD` — the proper class of ordinals (Burali-Forti axiomatised).
  `structure-library/ordinals.scm`.
- `<=_ORD, <_ORD` — total preorder on ORD.
- `succ_ORD α` — ordinal successor (extends `succ` on NN).
- `LIMIT-ORD λ` — limit-ordinal predicate.
- `ORD-SEGMENT α` — the set `{β : β <_ORD α}`. Used everywhere as
  the "first α ordinals" indexing set.
- `SUP-ORD A` — least upper bound of a set of ordinals.
- `transfinite-induction` — induction schema on ORD.
- `nn-induction` — class-form induction on NN; also exposed as the
  built-in tactic `(ni)`. `number-systems.scm`.

**Cardinality.** `structure-library/cardinality.scm`.
- `CARD A` — cardinality of A; an ordinal.
- Anchors: `card-empty` (`CARD(∅) = 0`), `card-insert` (`CARD(A ∪ {x}) = succ(CARD A)` if `x ∉ A`),
  `card-segment` (`CARD(ORD-SEGMENT n) = n` for `n ∈ NN`),
  `card-finite-bij` (a set is finite iff there's a bijection to some `ORD-SEGMENT n`).

## 4. Bijections

`structure-library/bijection.scm`.

- `BIJECTION X Y` — class of bijections X → Y.
- `INVERSE-BIJ φ X Y` — the inverse function (CHOICE-defined; OK
  because uniqueness on a bijection makes the choice immaterial).
- `DELETE-AT φ k n` — given a bijection `ORD-SEGMENT(succ n) → S`,
  the restriction-and-shift that gives a bijection `ORD-SEGMENT n → S \ {φ(k)}`.
  Used in `sum-ag-splice-out`.

## 5. Algebraic structures

The hierarchy (see `STRUCTURES.md` for the tree). Each structure
declares its accessors via `def-structure-from-clauses` and folds its
characteristic laws into `IS-X` via named property predicates from
`operation-properties.scm`. So `IS-X(s)` is a *real* predicate, not a
shape check.

**Slot encoding — declaration is grouped, instance is flat.**

The declaration syntax uses clause-grouping:

```
(carriers A)
(op ADD (CARTESIAN A A) A)
(op MUL (CARTESIAN A A) A)
(op NEG A A)
(constant ZERO A)
(constant ONE A)
```

But the **runtime instance is a single flat VNB list** of
`(num-carriers + num-ops + num-constants)` slots, filled in
declaration order: carriers first, then ops, then constants. So a
`RING` instance is a 6-tuple `(LIST A-val ADD-val MUL-val NEG-val
ZERO-val ONE-val)`; `(A r)` is sugar for `(NTH 1 r)`, `(ADD r)` for
`(NTH 2 r)`, etc.

The clause-grouping in `(carriers A B) (op …)` is **parsing sugar**.
It does *not* nest in the instance — a 2-carrier structure has the
two carriers in slots 1 and 2 at the top level, not in a `(LIST
carrier1 carrier2)` sub-list.  Building a structure by hand means
writing the slots flat in declaration order; bridges between
structures of different species are positional — see section 6
(RING → AG).

Bare structures (live as Scheme classes via `IS-X`):

- `SEMIGROUP` — carrier `A`, op `MUL` (associative).
  `structure-library/semigroup.scm`.
- `MONOID` — + identity `E`.  `monoid.scm`.
- `COMM-MONOID` — MONOID with commutative MUL. `monoid.scm`.
- `GROUP` — MONOID with inverse `INV`. `group.scm`.
- `ABELIAN-GROUP` — GROUP with commutative MUL. `abelian-group.scm`.
- `RING` — carriers `A`; ops `ADD MUL NEG`; constants `ZERO ONE`.
  `ring.scm`.
- `COMMUTATIVE-RING, INTEGRAL-DOMAIN, FIELD, EUCLIDEAN-RING, NORMED-FIELD` —
  restrictive predicates over the RING shape (genuine IFFs, not new shapes).
  Each in its own file under `structure-library/`.
- `METRIC-SPACE` — carrier `X`, distance `D : X×X → RR`. `metric-space.scm`.

**Named operation properties.** Reusable predicates; reference these
by name in `(property NAME ACC …)` clauses, not by re-stating laws.

- `is-associative op crr`
- `is-commutative op crr`
- `is-identity op unit crr`
- `has-inverses op unit invop crr`
- `is-distributive addop mulop crr`
- `is-metric dist crr`

`structure-library/operation-properties.scm`.

**Numeric instances** (`structure-library/numeric-instances.scm`):

| Instance | Memberships |
|---|---|
| `NN-ADD-MONOID` | COMM-MONOID |
| `ZZ-RING` | RING, COMMUTATIVE-RING, INTEGRAL-DOMAIN, EUCLIDEAN-RING |
| `QQ-RING` | RING, COMMUTATIVE-RING, INTEGRAL-DOMAIN, FIELD |
| `RR-RING` | … + NORMED-FIELD |
| `CC-RING` | … + NORMED-FIELD; `CC-MS` is a METRIC-SPACE |

Generic ring theorems transport to instances via `specialize-structure`
(bringing e.g. `ring-add-comm-zz-ring`).  `structure-library/numeric-instances.scm:25`.

## 6. Summation and product over indices

Three closely related operators; the indexing varies, the algebraic
target varies.  `structure-library/sequences.scm`, `structure-library/finsum.scm`.

| Operator | Indexing | Algebraic target | Value |
|---|---|---|---|
| `PROD-ORD m f n` | NN-segment 0..n-1 | MONOID `m` | `f(0)·…·f(n-1)` |
| `SUM r f n` | NN-segment 0..n-1 | RING `r` | `f(0)+…+f(n-1)` |
| `SUM-AG ag f n` | NN-segment 0..n-1 | ABELIAN-GROUP `ag` | `f(0)+…+f(n-1)` |
| `FINSUM ag f S` | finite set `S` | ABELIAN-GROUP `ag` | `Σ_{x∈S} f(x)` |
| `RING-PROD-N f n` | NN-segment | (RING-valued) | iterated ring product |

All NN-indexed operators are defined by `def-by-nn-recursion`, which
installs `<name>-zero` and `<name>-succ` macetes.

**Gap — no `RING → ABELIAN-GROUP` projector.**  To use `FINSUM` over a
ring `r`, you build the *additive* abelian group of `r` by hand and
discharge `IS-ABELIAN-GROUP` for it from `IS-RING(r)`.  Concretely, when
`r` is a ring,

```
(LIST (A r) (ADD r) (ZERO r) (NEG r))
```

is an abelian group.  This list slots into the 4-slot `ABELIAN-GROUP`
shape positionally:

| Position | AG slot | Built from `r` |
|---:|---|---|
| 1 | `A`   (carrier)        | `A(r)`    — same carrier |
| 2 | `MUL` (binary op)      | `ADD(r)`  — additive op |
| 3 | `E`   (identity const) | `ZERO(r)` — additive zero |
| 4 | `INV` (unary inverse)  | `NEG(r)`  — additive negation |

So `IS-ABELIAN-GROUP` reads `MUL = ADD`, `E = ZERO`, `INV = NEG`; the
ring's additive laws (`is-associative ADD`, `is-commutative ADD`,
`is-identity ADD ZERO`, `has-inverses ADD ZERO NEG`) are *exactly* what
`IS-ABELIAN-GROUP` requires.  A convenience bridge `ADD-AG(r)` returning
this list, plus a single axiom `ring-add-ag-is-ag`, would close the
gap.  On the wishlist.

The matching is **positional**: slot `k` of the LIST goes into slot
`k` of the target structure, and `IS-ABELIAN-GROUP` of the result is
the bridge's soundness check.  A misaligned LIST is simply refutable
in the class — no encoding-level checking is needed beyond the
predicate itself.  This generalises to multi-carrier targets
(`(carriers V F) (op …)` declarations are accepted today — the
machinery already handles them); their `IS-X` predicate carries
whatever extra constraints the slots must satisfy (e.g.
`IS-FIELD(F(s))`).

**Permutation invariance.** `sum-ag-permutation-invariance` (proven,
the milestone of the library phase) underpins `finsum-well-defined` —
the value of `FINSUM` does not depend on which enumeration `FIN-ENUM`
returns.

**Sum/prod over sets**.  `sum-set-*`, `prod-set-*` axioms in
`structure-library/sequences.scm` give disjoint-union/empty/singleton laws.

## 7. Sequences supporting infrastructure

`structure-library/finsum.scm`:

- `FIN-ENUM S` — a chosen bijection `ORD-SEGMENT(CARD S) → S`.
- `ENUM-FAM ag f phi n` — the family `SUM-AG` consumes: `f∘phi` on the
  segment, identity outside.
- `INSERT-LAST phi x n` — append-to-enumeration; sibling to `DELETE-AT`.

## 8. Matrices

`structure-library/matrix.scm`.

- `MATRIX S` — class of matrices over a set S: lists of equilong rows
  over S, i.e. elements of `TUPLES(TUPLES S)` with all rows the same length.
- `SIZE M` — `[LENGTH M, LENGTH(NTH 1 M)]` — `[rows, columns]`.

No multiplication or addition on matrices yet. (The matrix-as-class
machinery is in place; the matrix-as-algebra is a future extension.)

## 9. Metric and analysis

- `METRIC-SPACE` — structure; section 5.
- `CC-MS` — the metric space `[CC, λ(x,y).|x-y|]`. `structure-library/complex.scm`.
- `cc-complete` — completeness of CC (Cauchy ⇒ convergent), axiom.
- Normed-field laws (positivity, multiplicativity, triangle) live
  inside `IS-NORMED-FIELD` and the per-instance witnesses
  (`rr-abs-*`, `cc-magnitude-*` in `number-systems.scm`).

**Extended reals.** `structure-library/extended-reals.scm`: `RR*`,
`POS-INF`, `NEG-INF` with ordering only; no extended arithmetic.

## 10. Tactics — kernel inference rules

All tactics live in `interactive.scm` as short-form Scheme functions.
Use `(show)` to print the focused sequent.

**Structural / propositional.**
`(di)` direct inference (peel ∀/⇒/∧/¬…) · `(pbc)` proof-by-contradiction
· `(ass)` assumption · `(ass-all)` sweep all open goals · `(rfl)`
reflexivity · `(qrfl)` quasi-reflexivity · `(oi-l) (oi-r)` ∨-intro ·
`(ci)` cartesian-intro · `(ti)` tuples-intro · `(ii)` intersection-intro
· `(ue f)` ∃-elim · `(cut f)` cut.

**Term/equality.** `(subst (= s t))` Leibniz substitution from an
equality in context · `(beta)` apply-functoid β · `(lam-b)`
VNB-LAMBDA β · `(if-true t)`, `(if-false t)` conditional reduction ·
`(nth-r)` `(NTH k (LIST …))` reduction.

**Backchain & theorem use.**
`(ta name)` add theorem as assumption · `(inst f t)` instantiate ∀ ·
`(bc f)` backchain · `(bc* name)` matching-backchain, applies a
theorem whose conclusion matches the goal (used heavily; subsumes
`ta`+`inst`+`bc` for the common case).

**Macetes.** `(mac name)` apply a rewrite rule from the macete table
(every named axiom/theorem is installed as one unless rogue).

**Calculation.** `(arith)` ground arithmetic · `(rs)` ring-simplify
decision procedure.

**Schema-handling primitives.** `(sep-set) (sep-mi) (sep-me)` separation ·
`(comp-mi) (comp-me)` class comprehension · `(iota)` IOTA characterisation ·
`(lam-t) (lam-b)` lambda typing/beta · `(ni)` NN-induction · `(tfi)`
transfinite-induction · `(bu-set) (bu-mi) (bu-me)` big-union.

**Navigation.** `(focus k)`, `(show)`, `(pp w)`, `(calc t)`.

## 11. Discovery commands

- `(catalog)` — regenerate `THEOREMS.md` (full alphabetical catalog).
- `(display-definitions)` — list every defined constant in the current
  theory and its characteristic axioms.
- `(display-inert-macetes)` — list theorems whose macete form is
  unsound (S-10): named-only, not usable as `(mac name)`.
- `(lookup-theorem 'name)` — return a theorem's formula.

**Looking for something not listed here?** Search `THEOREMS.md` (flat,
367 entries) or grep `structure-library/`.  If a basic operator you
expect is missing, that's a real gap — flag it.
