# Metric outer measures and Lebesgue measure on the line (MEASURE-3, 2026-10-09)

The user's order of 2026-10-09: "start MEASURE-3". The notes (Construction of Measures, Chapter 4 Section 3,
Def. 4.25 to Prop. 4.26) on top of MEASURE-1 (the Caratheodory construction) and MEASURE-2 (Method I outer
measures, Lebesgue outer measure). Three agents: A (metric outer measures, worker-02, about 85 minutes including
a 25-minute stall caused by the integrator), B (the length of an interval, worker-03, about 85 minutes), C (the
join, worker-02, 10 minutes). 86 theorems, every one `modulo 0`, oracles `ineq`, `arith`, `crs`; no support,
warrant, stamp or new axiom. Checked on last night's exam band (kernel round 1); the final probe loaded the four
files in load order (290 s, 86 / 86 `;; qed`, no warnings, `*vnb-qed-failures*` empty). The reports are
`scratchpad/triage/MEASURE-3-{A,B,C}-REPORT.md`.

Files, in load order after `theorem-library/monotone-class`, library measure:
`theorem-library/lebesgue-interval-length.scm` (23 theorems), `structure-library/metric-outer-measure.scm`
(vocabulary), `theorem-library/metric-outer-measure.scm` (58), `theorem-library/lebesgue-measure-line.scm` (5).

## The vocabulary (decided by the integrator; for the user's confirmation)

For a metric space m:

* `PT-SET-DIST(m, x, es)`: the EINF of the set of values DIST(m)(x, z), z in es (the notes' d(x, F); +inf for
  the empty set, EINF's convention).
* `SET-DIST(m, aa, bb)`: the EINF of the values DIST(m)(x, y), x in aa, y in bb (Eq. (406)).
* `IS-METRIC-OUTER-MEASURE(m, mu)` (Def. 4.25): m a metric space, mu an outer measure on PTS(m), and
  mu(aa u bb) = mu(aa) + mu(bb) whenever NOT(SET-DIST(m, aa, bb) = 0).
* `BOREL-SETS(m)`: SIGMA-GENERATED of the open subsets of PTS(m).

Lebesgue outer measure lam* is MEASURE-2's term, METHOD-I-OUTER(RR, CLOSED-INTERVALS, s -> INTERVAL-LENGTH(s));
Lebesgue measure is its Caratheodory measure, written RES(lam*, CARATHEODORY-SETS(RR, lam*)). Neither is named.

## What is proven

| the notes / the result | theorem |
|---|---|
| Lemma 4.27, (93) and (92) | `metric-outer-measure-finite-separated`, `metric-outer-measure-separated-sum` |
| Lemma 4.28 | `metric-outer-layers-limit` (the E_n nondecreasing; mu*(A n (X \ F)) is the ESUP of mu*(A n E_n)) |
| Prop. 4.26 | `metric-outer-closed-measurable`, `metric-outer-open-measurable`, `borel-sets-caratheodory-measurable` |
| lam* is a metric outer measure | `lebesgue-metric-outer-measure` (via `metric-outer-of-separating-sets`) |
| Borel sets and intervals are measurable | `lebesgue-borel-measurable`, `lebesgue-intervals-measurable`, the four half-lines |
| lam*([a, b]) = b - a | `lebesgue-outer-ccint`, from `ccint-cover-sum-ge` |
| points, the empty set, the other intervals | `lebesgue-outer-point`, `-empty`, `-ooint`, `-coint`, `-ocint` (one lemma: `lebesgue-outer-between`) |
| translation invariance of lam* | `lebesgue-outer-translate` (the translate written {z in RR : z - c in es}) |
| the Lebesgue measure of an interval is its length | `lebesgue-measure-ccint`, `-ooint`, `-coint`, `-ocint`; `lebesgue-measure-point` |

## Two routes better than the brief's

* **lam* is metric (agent A; the user approved the change of route).** The brief cut every covering interval into
  pieces shorter than d(A, B) and re-indexed them. Instead: the half-lines are measurable directly (a cover cut
  at one point keeps its index and its total length); two separated sets are split by the union of the grid
  cells of width less than d(A, B) that meet the first set, which is measurable, contains A and misses B; and a
  general lemma, `metric-outer-of-separating-sets`, says an outer measure is metric whenever separated sets are
  always split by a measurable set. No re-indexing; the measurability of the intervals comes with it.
* **The lower bound for [a, b] (agent B).** No Heine-Borel and no finite subcover: one creeping argument along
  [a, b] widens each covering set to an open neighbourhood and tracks a prefix sum of the widened diameters.
  The covering endpoints are never read, so there is no countable choice, and the lemma holds for ANY countable
  cover of [a, b] by sets of reals: their total diameter is at least b - a.

## The notes' gaps, each closed by a proven lemma

* (93): the induction must carry that the union of the first n sets stays at positive distance from the later
  ones (`set-dist-union-pos`).
* d(S_2k, S_2l) > 0 needs 1/(j+1) - 1/(j+2) > 0 (`nn-recip-succ-gap`, `dist-layer-gap`).
* Case (1) uses that the tail of a finite series in [0, +inf] tends to 0 (`esum-nn-tail-small`).
* X \ F = E_n u U_{k >= n} S_k uses the least layer containing a point (`dist-layer-ring-cover`).
* ESUM f + ESUM g <= ESUM h when f + g <= h termwise (`esum-nn-superadditive`).
* The case split is on whether L = sup mu*(A n E_n) is finite, which removes the notes' second case.
* That lam* is metric, and the length of an interval, are not proven in the notes at all.

## Kit findings (the agents')

* `dk-project!` drifts as `dk-have!` once did: when the projection is the focus goal it proves it in place, the
  focus moves, and it errors "not in context". Repair: the `dk-have!` treatment.
* `dk-nn!` does not get k <= n from k < succ(n), and treats `succ(m + k)` as one atom.
* `dk-apply!` errors when a partial instance of the same universal is already in context.
* `dk-pick` by "contains" picked `esup-least` for `esup-upper`.
* `subst` of `closed-intervals-def` reaches only the goal: a hypothesis wants `dk-rewrite-h!` first.
* `ineq` will not certify a variable typed only in RR-POS-STAR, and is poisoned by `eplus` or POS-INF atoms.
* `rfl` refuses `INTERVAL-LENGTH(X) = INTERVAL-LENGTH(X)` (not certified defined).
* `di` on an IFF goal lands each direction's hypothesis itself, so a following `(di)` fails.

## Integration notes

`rps-prefix-mono` was proven in both proof files with two different statements; agent B's is renamed
`rps-prefix-mono-range` (`rename-sym.py`). 17 of A's 58 `sp` / `qed` pairs are generated by helpers, so a text
count of `(qed '` finds 41. The cold build is tonight's exam (2026-10-10 06:00Z).
