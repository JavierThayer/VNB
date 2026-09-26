# The basic facts the library still asserts

Measured from a full load on 2026-08-12: 311 proven theorems, 119 bills reading
`modulo 0`, 4 reading `trust: none`, and **1032 facts with `asserted`
provenance**, of which **359 are named by at least one bill**.  The remaining 673
are asserted but uncited -- they cost nothing today and are listed here only
where they block something.

The ranking below is by citation count (`debt-keystones`), but the ordering
within a cluster is by what the proof would actually take.  The standing warning
applies: **reclassifying or proving a leaf buys nothing until it is the LAST
unwarranted leaf of the bills that name it.**  Run the what-if before believing a
count.

---

## 0. The CARD layer -- IN PROGRESS, see `card-basics-worklist.md`

Split out; it is the current work.

---

## 1. The NN order layer -- the largest cluster, and the most elementary

Roughly 250 citations across ten facts, every one of them a consequence of the
Peano axioms in `number-systems.scm` (which are `primitive` since 2026-08-01) plus
`nn-induction`.

| fact | bills | warrant |
|---|---|---|
| `nn-add-succ` | 40 | reference |
| `nn-le-succ` | 40 | well-known |
| `nn-le-succ-cases` | 33 | well-known |
| `nn-not-le-zero-pos` | 29 | well-known |
| `nn-one-le-succ` | 27 | well-known |
| `nn-le-imp-neq-succ` | 23 | well-known |
| `nn-succ-le-antisym` | 22 | well-known |
| `nn-zero-le` | 21 | well-known |
| `nn-not-le-succ-le` | 18 | well-known |
| `nn-succ-mono` | 14 | well-known |
| `nn-mul-succ` | 10 | reference |
| `nn-one-in`, `nn-minus-1-inj`, `nn-minus-succ-1`, `nn-pos-of-nonzero`, `nn-pos-is-succ` | 3-9 | well-known |

`nn-add-succ` already carries a memory note ("awaits a call"): it is the
recursion equation for addition, so whether it is a theorem or part of what `+`
MEANS on NN is a foundational question, not a proof-effort question.  The rest
are theorems.

The shape of the work is one file, `theorem-library/nn-order-laws.scm`, proving
the order facts from `nn-induction` in dependency order (`nn-zero-le` first,
then `nn-le-succ`, then the case-split and antisymmetry facts).  Nothing else in
the tree has to move.

## 2. The ring shape projections -- the group.scm precedent applies verbatim

About 180 citations.  `group.scm`'s four projections were PROVEN on 2026-08-10 in
`structure-library/subtype-laws.scm` (`stl--project!`) rather than stamped
`definitional`; the same treatment is available here, and says more.

| fact | bills | warrant | note |
|---|---|---|---|
| `ring-carrier-closed-mul` | 36 | proof | warrant names a proof; check it still runs |
| `ring-mul-zero-left` | 30 | well-known | genuine derivation: `a*0 = a*(0+0)`, cancel |
| `ring-mul-zero-right` | 27 | well-known | mirror |
| `ring-neg-in-carr` | 21 | well-known | projection |
| `ring-one-in` | 21 | well-known | projection |
| `ring-add-right-inv` | 18 | well-known | one commutation from the left law |
| `ring-add-right-id` | 17 | well-known | one commutation from the left law |
| `ring-neg-neg` | 11 | well-known | cancellation |
| `ring-add-closed` | 4 | well-known | projection |
| `ring-neg-mul-left` | 5 | well-known | from `ring-mul-zero-left` |

Note `ring.scm:139` already sweeps eleven names to `definitional`; these are the
ones the sweep does not cover.

## 3. `entry-in-carrier` -- 63 bills, the top keystone

Has its own plan (guards plus a 63-site migration).  Not a proof problem: the
statement needs a hypothesis it does not carry, and every citation has to supply
it.  Same migration shape as `interval-card-in-nn` (34 sites, done 2026-08-12).

## 4. The finsum layer -- about 200 citations, and real work

`finsum-congruence` (40), `finsum-single-support` (37), `finsum-fubini-c` (22),
`finsum-ring-distrib-left-gen` / `-right-gen` (22 each), `finsum-two-support`
(16), `finsum-act-distrib-gen` (13), `finsum-type` (13, informal),
`finsum-all-id` (8), `finsum-add-ag` (7).

Each is an induction over finite support, so each needs `finite-set-induction` --
which is itself one of the CARD axioms (see the CARD worklist).  **This cluster is
downstream of the CARD layer**, which is one reason to do CARD first.

## 5. The matrix entry layer -- mostly `reference`

`matmul-entry` (44), `matmul-type` (39), `matrix-entry-extensionality` (35),
`identmat-type` (32), `matprod-summand-type` (31), `matact-entry` (24),
`entry-of-identmat` (22), `matmul-assoc-summand-type` (21), the `elem-*` family
(14-17 each), the `tel-*` / `ter-*` typing families (22 each).

Large, mechanical, and downstream of both finsum and `entry-in-carrier`.  Not
next.

## 6. The bijection / injection layer -- small, and it gates CARD

| fact | warrant | note |
|---|---|---|
| `bijection-identity` | informal | "deferred: needs VNB-LAMBDA typing + beta + exists-intro" |
| `bijection-compose` | informal | same, on the nested application |
| `bijection-set-iff` | informal | subclass of `FUN(X,Y)` by separation |
| `inverse-bij-in-fun`, `-left`, `-right`, `-is-bijection` | **none** | uses CHOICE; Track A avoids it |
| `injection-in-fun`, `-injective`, `-set-iff`, `-from-empty` | **none** | uncited today |
| `image-subset-codomain`, `delete-at-*` | **none** | uncited today |

`bijection-identity` is the worst leaf of `cd-seg-body` and hence of
`card-star-segment`, so proving it is the difference between `[trust: informal]` and
`modulo 0` for the whole CARD arc.  It and `bijection-compose` are the two that
matter.

## 7. The ordinal segment facts still `informal`

`ord-segment-nn-subset` (5), `ord-segment-nn-succ` (5), and the uncited
`ord-segment-self`, `ord-segment-trans`, `ord-segment-insert`.  Small; they sit
just under the CARD work.

## 8. The three remaining `trust: none` leaves

Each is the SOLE unwarranted leaf of its bills, so each is worth its full count:

* `zz-is-euclidean-ring` (1 bill: `zz-bezout`) -- needs the division algorithm on ZZ.
* `rr-is-metric-space` (1 bill: `rr-complete`).
* `inf-subsets-is-set` (2 bills: `totally-bounded-has-cauchy-subsequence`,
  `block-family-combinatorial`).

## 9. Housekeeping the load already reports

* **117 PSS entries with no `topic!`** -- the load prints the list.
* **178 `reference`-warranted entries with no gloss** -- `(reference-warrants-without-gloss)`.
* **1 outstanding functor obligation**: `nf-metric-space-functorial`.
* **14 kernel-rule tags unexercised** by the library load.
