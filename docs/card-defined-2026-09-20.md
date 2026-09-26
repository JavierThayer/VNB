# CARD := CARD-STAR -- the analysis, the plan, and the log

Batch 9, assignment 9-B (`cdf-`).  The user's decision of 2026-09-20: *"rename CARD-STAR to
CARD and drop the axioms."*  Work is done in the copy `~/prover-card`; the pristine fork base
is `~/prover-fork-base-0920`.

The whole difficulty is LOAD ORDER, so the analysis below was done first and is kept here as
the design note.  Every number in sections 1-4 was measured on worker-03 against the
2026-09-19 band, from `*proof-citation-graph*` (proof-debt.scm:152) -- the exact record of
what each proof cited -- not from a text scan.  The probes are
`scratchpad/card/cdf-analysis.scm`, `cdf-cone.scm`, `cdf-axsweep.scm`, `cdf-shapes.scm`.

---

## 1.  The shelf: EIGHT primitive facts about CARD, not seven

`structure-library/cardinality.scm` carries seven inside its `primitive` block; an eighth,
`card-image-injection`, sits in `structure-library/injection.scm:161` under its own
`fluid-let` and is marked in the source as "A CARD axiom, so `primitive` like the rest of
them".  The sweep over every installed formula that mentions the head `CARD`
(`cdf-axsweep.scm`) finds these eight and no others on the `primitive` shelf.

Positions below are 0-based indices over `load.scm`'s quoted file names (586 entries).
`structure-library/cardinality` is 82, `structure-library/injection` is 83.

| # | axiom | file | citers | earliest citer |
|---|-------|------|-------:|----------------|
| 1 | `card-in-ord` | cardinality.scm:33 | 3 | `rake-choose-succ` @278 |
| 2 | `card-empty` | cardinality.scm:41 | 14 | `card-singleton-proof` @154 |
| 3 | `card-insert` | cardinality.scm:75 | 10 | `card-singleton-proof` @154 |
| 4 | `card-segment` | cardinality.scm:89 | 6 | `interval-card-in-nn` @260 |
| 5 | `card-finite-bij` | cardinality.scm:101 | 1 | `rake-inverse-bij` @200 |
| 6 | `card-union-disjoint` | cardinality.scm:117 | 2 | `card-inequalities` @275 |
| 7 | `finite-set-induction` | cardinality.scm:130 | 9 | `card-subset-nn` @258 |
| 8 | `card-image-injection` | injection.scm:161 | 2 | `rake-choose-succ` @278 |

No `-rev` companion of any of the eight is cited anywhere.

How much of the library rests on each (transitive closure of the citation graph over the
2150 proven theorems):

    card-in-ord            5      card-union-disjoint    69
    card-empty           225      card-segment          124
    card-insert          224      card-finite-bij       173
    finite-set-induction 204

So the binding constraint is `card-empty` / `card-insert`, whose earliest citer is at
position **154**, and `card-finite-bij`, whose only citer is at position **200**.

## 2.  The inventory: axiom vs. CARD-STAR counterpart

Compared RAW with `alpha-equiv?` after rewriting the head `CARD-STAR` to `CARD`
(`cdf-shapes.scm`).  "same" means the citers need no change at all.

| axiom | counterpart (file) | same? | what is needed |
|-------|--------------------|-------|----------------|
| `card-empty` | `card-star-empty` (card-finite.scm) | **yes** | rename only |
| `card-segment` | `card-star-segment` (card-defined.scm) | **yes** | rename only |
| `finite-set-induction` | `card-star-finite-set-induction` (rake-card-star-laws.scm) | **yes** | rename only |
| `card-in-ord` | first conjunct of `card-star-zermelo` (rake-ord-pigeonhole.scm) | no | one `fact` + `dk-split!` |
| `card-insert` | `card-star-insert` (rake-card-star-laws.scm) | no -- counterpart CURRIES `x in SET` and `not(x in A)`; the axiom conjoins them | restate in the axiom's shape |
| `card-union-disjoint` | `card-star-union-disjoint` (rake-card-star-laws.scm) | no -- counterpart is fully curried | restate in the axiom's shape |
| `card-image-injection` | `card-star-image-injection` (rake-card-star-laws.scm) | no -- binder order `dm,cod,phi` vs `dm,(cod,ph)`, and curried | restate in the axiom's shape |
| `card-finite-bij` | `card-star-well-ordering` (rake-ord-pigeonhole.scm) | no -- the counterpart is **STRONGER**: it drops the finiteness guard | weaken (add the guard back) |

No axiom is FALSE of the defined CARD, and none needs a guard the counterpart lacks.
`card-insert`'s finiteness guard was already added on 2026-09-18 for exactly this reason.

`well-ordering-principle` (theorem-library/well-ordering.scm:10, `asserted`,
`warrant! 'well-known`) is, after the rename, **character for character**
`card-star-well-ordering`.  It is cited by nothing (only a `topic!` and a duplicate
`warrant!` in founder-warrants.scm), so it can simply take over as the NAME of that proof.

## 3.  Circularity: there is none

The question the brief asks -- does the CARD-STAR development rest, directly or through the
theorems it cites, on a CARD axiom? -- is answered exactly by a walk of
`*proof-citation-graph*`.  For all 30 theorems of `card-defined.scm`, `card-finite.scm`,
`rake-zermelo.scm`, `rake-ord-pigeonhole.scm` and `rake-card-star-laws.scm`, and for every
brick they cite:

    CARD-AXIOM-FREE   (all 30, and the whole 138-name transitive cone; CONE-DEP-COUNT 0)

So **no cycle exists at the level of theorems**, and no cut is needed.  The headers of
`rake-card-star-laws.scm` and `rake-ord-pigeonhole.scm` claimed this by grep; the citation
graph confirms it transitively.

The cycle is only at the level of FILES, because `load.scm` orders files, not theorems.
The 138-name cone lives in 31 files (plus the primitive core).  Of those 31, three files
also contain theorems that DO rest on a CARD axiom, and those three are what must be split:

| file | @ | what the cone needs from it | what must stay behind |
|------|---|------------------------------|-----------------------|
| `theorem-library/rake-inverse-bij` | 200 | `inverse-bij-{in-fun,is-bijection,left,right}`, `ord-segment-self` | `fin-enum-is-bijection` (rests on `card-finite-bij`) |
| `theorem-library/finsum-insert` | 242 | `enum-append-is-bijection` | `finsum-empty`, `finsum-insert`, `finsum-insert-ag` |
| `theorem-library/fin-subsets` | 280 | `union-empty-right`, `union-assoc` | `fin-subsets-has-empty`, `fin-subsets-union-closed` |

## 4.  The reordering

Twelve of the 31 cone files already sit below position 191 and do not move.  The other
nineteen must load before the CARD theorems, which must in turn load before position 242
(`finsum-insert`, the first citer of `card-empty`/`card-insert` once `card-singleton-proof`
is moved).  The insertion point is **immediately after `transport` (load.scm:818, position
190)**: the block uses `obtain` (`sketch`, 188) and `vlet` (189), so it cannot go earlier,
and every cone file moves UP from there, which can never break a citer.

Verified for each of the nineteen: its every citation outside the block comes from a file at
position <= 160 (`theorem-library/binary-minus-laws`), except the three split files, whose
late citations belong to the parts that stay behind.

New block, in this order (old position in brackets):

    subset-lemmas [192]          rake-analysis2 [199]        rake-inverse-bij [200, split]
    nn-parity-proof [221]        nn-pred [223]               ord-segment-arith [224]
    finite-surgery [225]         pigeonhole-segments [226]   enum-append [NEW, from 242]
    union-laws [NEW, from 280]   bijection-derived [290]     bijection-identity-proof [292]
    card-defined [293]           card-finite [294]           ord-no-injection [333]
    zen-step [334]               rake-zermelo [335]          rake-ord-pigeonhole [336]
    rake-card-star-laws [337]    card-laws [NEW]             card-singleton-proof [from 154]
    rake-fin-enum [NEW, from rake-inverse-bij]

Two files move DOWN, and both were checked:

* `card-singleton-proof` (154 -> after `card-laws`): its only theorem `card-singleton` is
  first cited by `makeset-basics` @249, well below.
* `fin-enum-is-bijection` (out of `rake-inverse-bij` @200 -> after `card-laws`): first cited
  by `finsum-type-proof` @209, which the insertion pushes to roughly 231.

## 5.  What CARD becomes

`def-functoid 'CARD '(a_)` with the IOTA body of `card-defined.scm` moves into
`structure-library/cardinality.scm` (position 82), which is immediately after
`structure-library/bijection` (81) and after `ordinals` (77) -- everything the body needs.
The `primitive` block of that file goes.  `card-defined.scm` keeps the proofs only.

Definedness is unaffected: `pi--defined?` (primitive-inferences.scm:990) tries
`asm-establishes-defined?` and `pi--strict-hyp-certifies?` BEFORE the functoid clause, and
`CARD` is not in `*total-term-heads*`, so `CARD(A)` is certified exactly as it is today --
by a typing in context.  The new functoid clause unfolds to an IOTA, which is never
certified, so it adds nothing and removes nothing.

## 6.  Names after the rename

    CARD-STAR                        -> CARD                      (the head)
    card-star-empty                  -> card-empty                (the axiom's name)
    card-star-segment                -> card-segment              (the axiom's name)
    card-star-finite-set-induction   -> finite-set-induction      (the axiom's name)
    card-star-well-ordering          -> well-ordering-principle   (the PSS entry's name)
    card-star-insert                 -> card-insert-curried
    card-star-union-disjoint         -> card-union-disjoint-curried
    card-star-image-injection        -> card-image-injection-curried
    card-star-bij                    -> card-bij
    card-star-from-body              -> card-from-body
    card-star-zermelo                -> card-zermelo
    card-star-body-exists            -> card-body-exists
    card-star-zero-is-empty          -> card-zero-is-empty
    card-star-seg-image              -> card-seg-image
    card-star-union-disjoint-ind     -> card-union-disjoint-ind
    card-star-finite-induction-aux   -> card-finite-induction-aux

The four `-curried` names keep the shape the CARD-STAR proofs produced; the new file
`theorem-library/card-laws.scm` proves `card-insert`, `card-union-disjoint`,
`card-image-injection`, `card-in-ord` and `card-finite-bij` in the AXIOMS' exact shapes from
them, so that no citer changes.

## 7.  Not part of this job, but worth the user's eye

Once CARD is defined, every `asserted` statement about CARD stops being part of an implicit
definition and becomes a claim.  The sweep finds these still asserted and now checkable:
`injection-count-falling`, `injection-extension-recurrence`, `permutation-recurrence`,
`cauchy-schwarz-finite`, `cauchy-schwarz-sqrt`, `holder-finite`, `minkowski-l2`,
`prod-of-sums-expansion`.  All are standard finite combinatorics or finite inequalities and
are true of the least-ordinal cardinal; none is on the primitive shelf, so each already
shows on the bills that use it.

---

## Log

* **2026-09-20 02:30 UTC** -- analysis above complete (sections 1-6).  No cycle; no axiom
  false of the defined CARD; no decision of the user needed.  Proceeding to the surgery.

* **2026-09-20 02:20 UTC, stage 1 (reorder + the three splits)** -- load `card-1.log`:
  25 proof files FAILED, all one cascade.  The head of it was
  `theorem-library/finsum-insert: Unbound variable: fsi-psi` -- the extraction of
  `enum-append-is-bijection` took with it the helper `fsi-psi`, which the two theorems
  left behind still build.  Restored in place (`enum-append.scm` has its own copy; each
  theorem-library file gets its own environment).  Nothing in the failure list was a
  load-ORDER error: no `lookup-theorem: unknown theorem`, and the gates
  (`install-duplicate-audit`, `asserted-duplicate-audit`, `constant-binder-audit`,
  `connective-arity-audit`, `head-registry-sweep`, `kernel-callers-audit`) all passed.
  The reordering itself is therefore sound; stage 2 was merged into the next load.
* **2026-09-20 02:45 UTC, stage 2** -- the swap itself, in one load (`card-2.log`):
  CARD defined in `cardinality.scm`, the seven axioms there and the eighth in
  `injection.scm` deleted, the sixteen `card-star-*` names renamed (section 6),
  `theorem-library/card-laws.scm` written and wired, `theorem-library/well-ordering.scm`
  retired to `archive/2026-09-20-card-defined/`, its `founder-warrants.scm` warrant
  removed, the suite's CARD block added, and the prose in CLAUDE.md,
  `structure-notes/card-basics-worklist.md` and the nine affected file headers brought
  up to date.
* **2026-09-20 03:10 UTC, load `card-2.log`** -- 0 proof files failed, 0 holes, every CARD
  theorem `modulo 0` (`card-in-ord`, `card-insert`, `card-finite-bij`,
  `card-union-disjoint`, `card-image-injection`, and the renamed `card-empty`,
  `card-segment`, `finite-set-induction`, `well-ordering-principle`), but
  `proof-cycle-check` -- FATAL, and rightly -- refused the load:

      finite-set-induction -> card-finite-induction-aux -> card-zero-is-empty
                           -> finite-set-induction

  THE CAUSE, and it is a species worth recording: **a rename can create a name
  COLLISION that turns a leaf into a cycle.**  `theorem-library/rake-combinatorics.scm`
  already proved a theorem called `card-zero-is-empty` -- the same statement, by
  `finite-set-induction` when that was a PRIMITIVE axiom.  Renaming
  `card-star-zero-is-empty` to `card-zero-is-empty` made two installs of one name; the
  later one overwrote the citation-graph entry with a proof that cites
  `finite-set-induction`, which is now itself proven FROM `card-zero-is-empty`.  The
  cycle gate saw it; `install-duplicate-audit`, which would also have seen it, runs
  AFTER the cycle gate and never got the chance.

  THE FIX: the rake-combinatorics block was REMOVED (archived to
  `archive/2026-09-20-card-defined/rake-combinatorics-before-cze-cut.scm`).  The
  surviving proof is the better one -- it loads ~70 slots earlier and uses no induction
  at all, reading the enumeration of a set of cardinal 0 off `well-ordering-principle` --
  and the statements are alpha-identical, so the `fact` of the name later in
  rake-combinatorics.scm is unchanged.  A diagnostic was added to `load.scm` beside the
  cycle gate: it now prints the CITED NAMES of every node on a reported cycle, which is
  what says which citation tangles the proofs rather than merely which proofs are
  tangled.
* **2026-09-20 03:35 UTC, load `card-3.log` -- CLEAN.**  `BUILD-EXIT 0`.
  0 proof files failed, 0 holes, **2154 proofs and 2154 `modulo 0`** (no proof carries a
  bill).  `proof-cycle-check: ok`.  `page-audit: ok (all 2154 proof(s) emit a re-runnable
  script)`.  `install-duplicate-audit: ok`, `asserted-duplicate-audit: ok`, and every
  fatal gate -- `connective-arity-audit`, `constant-binder-audit`, `functoid-binder-audit`,
  `kernel-callers-audit` -- ok.  `free-variable-audit`, `head-registry-sweep` and
  `install-grading` ok.
  Catalog, against the fork base:

    |                  | fork base 2026-09-20 | after |
    |------------------|---------------------:|------:|
    | proven           | 2150 | 2154 |
    | support (PSS)    |   71 |   70 |
    | axioms           |  205 |  197 |

  The eight axioms are exactly the eight CARD facts; the PSS loses
  `well-ordering-principle` to a proof; the four net new proofs are the five restatements
  in `card-laws.scm` less the `card-zero-is-empty` duplicate that was removed.
  `proven-duplicate-audit` (warn-only) reports 25, one more than the last complete count,
  and the extra pair is `bt-mul-comm == commutative-ring-mul-comm` -- pre-existing and
  unrelated to CARD.

---

## 8.  Every file changed (diff against `~/prover-fork-base-0920`)

NEW
    theorem-library/card-laws.scm          the five restated former axioms
    theorem-library/enum-append.scm        enum-append-is-bijection, out of finsum-insert
    theorem-library/union-laws.scm         union-empty-right / union-assoc, out of fin-subsets
    theorem-library/rake-fin-enum.scm      fin-enum-is-bijection, out of rake-inverse-bij
    docs/card-defined-2026-09-20.md        this note
    archive/2026-09-20-card-defined/       well-ordering.scm and the four pre-split originals

REMOVED
    theorem-library/well-ordering.scm      its one PSS entry is now proven

CHANGED
    load.scm                               the CARD block (19 files moved + 4 new + 2 moved
                                           down), well-ordering unwired, the cycle gate's
                                           new diagnostic, two stale notes struck
    structure-library/cardinality.scm      the seven axioms OUT, the def-functoid CARD IN
    structure-library/injection.scm        the eighth axiom (card-image-injection) OUT
    theorem-library/card-defined.scm       def-functoid moved out; renames; header
    theorem-library/card-finite.scm        renames; header
    theorem-library/rake-card-star-laws.scm  renames; header; the card-zero-is-empty gloss
    theorem-library/rake-ord-pigeonhole.scm  renames; header
    theorem-library/rake-zermelo.scm       header
    theorem-library/rake-combinatorics.scm the duplicate card-zero-is-empty block REMOVED
    theorem-library/finsum-insert.scm      enum-append-is-bijection cut (fsi-psi kept)
    theorem-library/fin-subsets.scm        the two union laws cut
    theorem-library/rake-inverse-bij.scm   fin-enum-is-bijection cut
    theorem-library/rake-finsum-welldef.scm  header
    theorem-library/card-inequalities.scm  header
    theorem-library/founder-warrants.scm   the well-ordering-principle warrant removed
    theorem-library/c-int.scm              one stale cross-reference
    theorem-library/rpow-star.scm          one stale cross-reference
    test-suite.scm                         the CARD block (12 checks); the two reader
                                           round-trip checks re-pinned on `rpow-star'
    CLAUDE.md                              the "CARD" paragraph rewritten
    structure-notes/card-basics-worklist.md   marked CLOSED
    structure-notes/unproven-basics.md     one stale name

## 9.  Left for the integrator

* `reference/` is GENERATED and was regenerated on worker-03 by the clean load; the copy in
  `~/prover-card/reference/` is stale (the push excludes it, by the standing rule).
* `wff.scm`'s `*wff-term-form-heads*` still lists `CARD`, with a comment saying that
  everything else in that arc "is a def-functoid or a def-predicate and registers itself".
  CARD is now a def-functoid too, so the entry is redundant -- harmless (the list only says
  which heads are refused in WFF position, which is still right) and not worth a recompile
  of a core file on its own.
* The file names `card-defined.scm`, `card-finite.scm` and `rake-card-star-laws.scm` were
  kept, so `rake-card-star-laws.scm` now contains no `CARD-STAR`.  Renaming them is churn
  across many headers and archive references; each carries a dated banner saying so.
* **2026-09-20 04:00 UTC, suite** -- `=== SUMMARY: 1302 passed, 0 failed ===` (the fork
  base's was 1290 / 0; the twelve new checks are the CARD block added to test-suite.scm).
  One check had to be written twice: `lookup-theorem` ERRORS on an unknown name rather
  than returning `#f`, so "the CARD-STAR companion names are gone" asks
  `*theorem-table*` directly.
* **2026-09-20 04:20 UTC, confirmation load `card-4.log`** -- the tree exactly as it now
  stands (the previous load ran before two comment-level edits and the test-suite fix):
  `BUILD-EXIT 0`, 0 files failed, 0 holes, 2154 proofs / 2154 `modulo 0`,
  `proof-cycle-check: ok`, `page-audit: ok (all 2154)`, `install-duplicate-audit: ok`,
  `asserted-duplicate-audit: ok`, catalog 2154 proven / 70 support / 197 axioms.
  **DONE.**
