# Method I outer measures, the extension of a measure, and the monotone class theorem (MEASURE-2, 2026-10-08)

The user's order of 2026-10-08: "start the next batch tomorrow; decide then the vocab". The notes
(Construction of Measures, Chapter 4 Section 2.1-2.2, Chapter 3 Section 1, Chapter 1 Section 2) on
top of MEASURE-1's Caratheodory construction. One agent, about 70 minutes of probing; 55 theorems,
every one `modulo 0`, oracles `arith` and `ineq`; files `structure-library/outer-measure-construction.scm`
and `theorem-library/outer-measure-construction.scm` (43 theorems), `structure-library/monotone-class.scm`
and `theorem-library/monotone-class.scm` (12), after `caratheodory` in load.scm, library measure. The
report is `scratchpad/triage/MEASURE-2-REPORT.md`.

## The vocabulary (decided by the integrator; confirmed by the user 2026-10-08)

* `IS-PREMEASURE(omega, cls, pm)` (Def. 4.6): `omega` a set, `cls` a subset of its power set holding the
  empty set, `pm` a function from `cls` into `[0, +inf]` with `pm(EMPTY-SET) = 0`.
* `COVER-SUMS(omega, cls, pm, es)`: the set of values `ESUM(k -> pm(s k))` over the sequences `s` in
  `FUN(NN, cls)` whose union covers `es`; `METHOD-I-OUTER(omega, cls, pm)` is the function on the power set
  taking `es` to `EINF(COVER-SUMS(...))` (Def. 4.8, eq. (78)); "+inf when no sequence covers" is EINF's
  own convention for the empty set.
* `IS-NULL-SET(omega, ca, mu, ns)` (Def. 3.1), `IS-COMPLETE-MEASURE(omega, ca, mu)` (every null set is in
  `ca`), `IS-SIGMA-FINITE(omega, ca, mu)` (Def. 3.6; finite measure is `mu(A) in RR`).
* `IS-MONOTONE-CLASS(omega, mc)` (Def. 1.12, with `omega in SET` added so that it matches `IS-ALGEBRA-OF-SETS`
  and `IS-SIGMA-ALGEBRA`) and `MONOTONE-CLASS-GENERATED(omega, cE)`, the intersection of the monotone
  classes over `omega` containing `cE`, built as `SIGMA-GENERATED` is.
* For Lebesgue outer measure: `CLOSED-INTERVALS`, a constant, the empty set with every `CCINT(a, b)` for
  real `a <= b`; `INTERVAL-LENGTH(s)`, the supremum in `[0, +inf]` of `{0} u {y - x : x <= y in s}`, the
  diameter read off the set itself, total on every set of reals, so the pre-measure
  `VNB-LAMBDA s CLOSED-INTERVALS (INTERVAL-LENGTH s)` carries no representation obligation;
  `interval-length-ccint` says it is `b - a` on `CCINT(a, b)`. The pre-measure and the outer measure are
  not named constants (a function-valued constant does not unfold in applied position, and a functoid
  cannot take zero parameters); the statements write the `METHOD-I-OUTER` term.

## What is proven

| the notes | theorem |
|---|---|
| Prop. 4.7 | `method-i-outer-is-outer-measure` (with `-empty`, `-mono`, `-subadditive`) |
| Remark 4.9 | `method-i-outer-of-measure` |
| Prop. 4.10 | `method-i-outer-extends`, `method-i-outer-measurable`, `method-i-outer-null-iff`, `method-i-outer-finite-approx` |
| Cor. 4.11 | `caratheodory-measure-complete` (for any outer measure), `method-i-outer-caratheodory-complete`, `method-i-outer-extends-completion` |
| Prop. 4.12 | `method-i-outer-sigma-finite-completion` |
| Prop. 1.11, Thm. 1.13 | `algebra-monotone-union-sigma-algebra`, `monotone-class-theorem` |
| Lebesgue outer measure | `lebesgue-premeasure`, `lebesgue-outer-measure`, `lebesgue-measure-complete`, `interval-length-ccint` |

Not in this batch: that intervals are Lebesgue measurable and the measure of an interval is its length
(the metric outer measures of Section 3, or a direct argument), the next measure batch.

## The notes' gaps, each closed by a proven lemma

* Prop. 4.7: the re-indexing of the double sum by one sequence (`esum-nn-flatten-le`), the countable choice
  of the covers and the `eps / 2^(i+1)` budget are all silent in the notes.
* Prop. 4.10: neither "without loss of generality non-increasing" nor Prop. 1.18 is needed; monotonicity
  gives `rho(inter A_n) <= rho(A_n)` directly (`method-i-outer-attained`).
* Prop. 4.12: the notes show `E subset F` with `F \ E` null; the `A u N` form needs the same applied to
  `X \ E`. The notes print `<` where `<=` is meant.
* Thm. 1.13: the binary intersection the algebra definition asks for comes by De Morgan, which the notes skip.

## Kit findings (the agent's)

The most frequent trap: `dk-have!`, `dk-project!`, `fact` or `subst` proving the focus goal in place, so the
next bare `ass` fires on a sibling (a `dk-then-ass!` proposed). `dk-pick` by symbol picked a link of an
instantiation chain once. A functoid (`NNFST`) cannot stand as a quantified function argument without a
lambda wrapper. `dk-abstract!` fails when the value's sethood is not evident from the index typing alone.
`prop` declines an ex falso inside an IFF. `+` and `binplus` do not rewrite into each other. A local Scheme
name like `ew` silently shadows the tactic (the clobber guard watches top-level defines only).
