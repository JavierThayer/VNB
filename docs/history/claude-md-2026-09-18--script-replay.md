<!-- VERBATIM copy of a section of CLAUDE.md as it stood on 2026-09-18, moved here when
CLAUDE.md was trimmed to its operational rules.  Nothing was edited.  The dated findings,
measurements and case histories behind each rule in CLAUDE.md are in this text. -->

## Script replay -- what a script is, and the five things that broke it

**The proof is the GRAPH.** `qed` -> `cmd-qed` (proof-commands.scm:443) refuses to install
unless `proof-done?` = `dg-proved?` on the root: every node grounded back to it. The
SCRIPT is a recording of the surface commands (`record-cmd!`, interactive.scm:36) -- the
INPUT, not the output. It carries nothing from the graph: no nodes, no arrows, no
inferences. Replaying it is a second experiment, not a check on the first.

And several recorded arguments are not references into the graph but indices into
ephemeral state, re-resolved at replay time: `(focus n)` is a 1-based POSITION in
`proof-open-leaves` (interactive.scm:4596); `ai`/`inst+`/`mac-h`/`wk` take an assumption
INDEX (`->raw-formula/idx`, interactive.scm:185); `ai`/`ew` witnesses are eigenvariable
NAMES minted from a monotonic global. So replay fidelity is ENGINEERED, not inherited --
which is the difference from IMPS, where a script replays to the graph by construction.
`proof-tex` does not depend on any of this: it prints from `*proof-live-trace*`
(interactive.scm:62-77), snapshotted as the proof RAN.

**Measured 2026-09-06** with `replay-audit.scm` -- `(ra-run!)` against the band,
all 1022 scripts, three outcomes where harvest.scm had two: **grounded** (replay ends
`proof-done?`), **incomplete** (every step ran, graph not grounded -- the silent one),
**error**. Start: **128 grounded (12.5%)**. After five repairs: **979 (95.8%)**, 33 error,
10 incomplete. The companion `scratchpad/ra-diverge.scm` diffs each replay against the
live trace step for step (`ra-diverge.scm`) and found **no silent-drift class at all**: every replay that
does not raise reproduces the live run's goal, assumption list and open-leaf count exactly.
A script either replays faithfully or dies loudly.

The five, and each is a rule:

* **A recorded argument shape must match `apply-recorded-cmd!`.** `fact` records its terms
  FLAT -- `(fact thm a b c)`, the form you would type (interactive.scm:1236, which says so)
  -- and the dispatcher read `(fact thm (a b c))`. `(fact thm)` with no terms (815 recorded
  steps) died on `(cadr '())`; `(fact thm a b)` handed `cmd-fact` the SYMBOL `a` where a
  list was wanted, so it instantiated NOTHING, landed the raw universal, and every later
  `ass`/`ai` in that script missed. **128 -> 514 from one `(cdr args)`.** `ineq-supply.scm`
  had built a workaround to the wrong shape; it and its suite check went too.
* **A surface command that records ITSELF needs a case in `apply-recorded-cmd!` too** --
  recording itself is half the fix. `slot` (288 steps), `detach!` (170), `prop` (90),
  `slot-h` (54), `lam-b-h` (15), `macm` (8), `minimize!` (6) all replayed as "unknown
  recorded command". `replay--surface!` (interactive.scm) runs the surface procedure and
  checks the DEDUCTION GRAPH moved -- the same predicate `vnb--run!` uses for its inert
  notice, because a surface procedure reports failure by returning #f, not by raising.
* **A replay harness must restore `*fresh-counter*`** from `*proof-start-counter*`, as
  proof-tex's replay does, or a recorded `ai`/`ew` witness names a variable the replay
  never minted. harvest.scm did not, and its "104 of 120 scripts do not replay" was partly
  its own omission. Fixed there too. Worth ~200 scripts.
* **`in-rr` moved focus without recording it, and the page-audit gate caught it** (2026-09-14).
  Its two helpers `in-rr--focus-goal!` / `in-rr--focus-asm!` were bare
  `set-proof-state-focus!`, so every proof that typed through `in-rr` emitted a page whose
  later positional `(focus n)` addressed the wrong leaf -- silently `incomplete`, never an
  error. The four mvt-aux-guarded proofs showed it (eight leaves open after the page,
  divergence exactly at the typing lane); mvt, rolle and interior-min-deriv-zero had been
  in the gate's residue for the same reason since it was built. They now record
  `focus-id` (node number, which reproduces) with an undo mark, as `ass-all` does. Verified
  on the band: all four pages type back in `grounded`.
* **`dk-focus!` on a node that is not an open leaf was silent and unrecorded**, and that one
  shape was FOUR of the five page-audit failures (2026-09-15: zz-bezout, makeset2-split,
  qq-line-is-module, rr-nvs-is-normed-vector-space): a driver loop over a SNAPSHOT of leaves,
  where `in-rr`'s trailing `ass-all` had grounded a later element before the loop reached it.
  `dk-focus!` now records `focus-id` for an ungrounded non-leaf and REFUSES a grounded one
  with a warning. The fifth (rolle) was `bc*` taking a page's witness alias (`w3`) literally in
  its BINDINGS; `bc*-run!` now resolves them through `witness-resolve`. Loop over
  `(proof-open-leaves *ps*)` freshly, or guard each focus with a liveness test.
* **A driver helper that repositions focus must go through `dk-focus!`** (driver-kit.scm:164),
  which records the move; a raw `set-proof-state-focus!` / `focus-on` does not, and the
  script then replays the following steps against an engine-chosen leaf. Six lines in
  `driver-kit.scm` (`dc-focus!`, `dc-grind!`, `dc-focus-case!`, `hbf-focus-open!`,
  `dk-lam-t!`) took **868 -> 919**; a sweep of ~106 more sites across ~55 files in
  `theorem-library/`, `calculus/` and `structure-library/` took it to **962**. The check is
  a grep: `set-proof-state-focus!` outside driver-kit.scm:169 must be EMPTY, and so must
  `focus-on *ps*` outside the kernel.
* **A driver helper must drive the SURFACE tactic, never `pi-*!` or `cmd-*` directly.**
  Only the surface goes through `vnb--run!`, and only `vnb--run!` records. `fnc--di-quiet`
  (structure-library/functoriality.scm) called `pi-direct-inference!`, so the ~6 peeling
  `di`s at the head of every functoriality proof were absent from the script and all
  **14** `*-functorial` scripts died at step 1. It is now `(quietly (lambda () (di)))`:
  **962 -> 979**.

The 43 that remain are `di` 19 / `ass` 9 / `ai` 2 / `ew` 1 / `mac-h` 1 / `bc*` 1, plus the
10 `incomplete` (mat-equiv-*, elem-*-invertible, rolle-neutral, ...), and they are the
calculus/matrix arc almost exclusively -- file-local helpers not yet run down.

Library unmoved through all five: **1022 proven**, catalog byte-identical, all 17
functoriality views still proved, **suite 1184/0**. `replay-audit.scm` and
`ra-diverge.scm` are at the root beside `harvest.scm` -- instruments, not library, and
not in load.scm.

### The PAGE is not the replay, and the difference is 272 proofs

`replay-audit.scm` measures a HARNESS: `apply-recorded-cmd!` with `*fresh-counter*`
restored from `*proof-start-counter*`. A person who types the printed page has no
harness. **`page-audit.scm` measures the page** -- it emits each stored proof through
`script--write-block` (the emitter behind `write-proof-script` and the `W` key) and
types the text back in. Measured 2026-09-07:

    the page, typed in                          707 / 1022
    the page + only the counter restored        983 / 1022
    the dispatcher path, counter restored       979 / 1022

So the counter is the ONLY difference between the two harnesses that changes an
outcome -- the surface path is if anything marginally better than the dispatcher path,
which retires four other candidate differences (surface tactics vs `cmd-*`, args
re-read from text vs passed raw, `*replaying?*` unbound, soft warning vs hard error).
**ZERO of the 315 shortfalls are errors; every one is `incomplete`** -- the page loads,
nothing complains, and the proof simply is not finished.

304 of the 315 are one cause: the page names counter-minted eigenvariables (`d_1787`)
as literals, and `*fresh-counter*` is a monotone global, so those names do not exist in
another session. The other **11** are a driver defect and are the same residue the
replay audit leaves (`mat-equiv-*`, `elem-f/g-invertible`, `identmat-invertible`,
`rolle-neutral`, `bernstein-moment-2`, `makeset2-split`, `norm-bounded-by-functionals`,
`series-partial-sum-weighted-expansion`).

**THE STANDARD, and it is the user's (2026-09-06): every proof must have a re-runnable
script.** A proof has resolution rungs as a formula does -- sketch at the top, script at
the bottom -- and the script is the proof dial's INVERTIBLE notch, the analogue of r1.
What makes r1 a notch rather than a hope is a load-time gate (print-parse-`equal?`), so
the proof analogue needs one too: `(report-page-audit)` is now the sixth gate on the
install door, printing

    ;; page-audit: 707/1022 proof(s) emit a re-runnable script -- 315 do NOT

**Its cost is real and the coverage is a policy call left open** -- A/B, same binary:
load **2m34.8s** without it, **3m44.3s** with, so **+69.5 s, +45%**. The re-run is
irreducible; the only lever is coverage. Exhaustive can name the one proof that broke
today; sampling here with the exhaustive sweep in the suite catches systematic breakage
only. Left exhaustive, with the measurement written at the call site.

**And the cost depends on the HEAP, which is the trap this box already has a rule
about.** The 61 s figure is under `--heap 120000` (`./prover`, and the band build).
The SUITE took MIT's default heap when this was measured (2026-09-07; it has carried
`--heap 200000` since 2026-09-15), and there the same sweep took **165 s**, 2.7x. So a gate that is affordable
interactively is not automatically affordable in the suite, and the suite is exactly
where the silent-death-under-memory-pressure failure lives. Suite after: **1189/0**
(1184 + 5).

### B IS DONE (2026-09-08): 707 -> **983**, the pre-registered number exactly

The page now NAMES each minted variable it uses, once, right after the step that
minted it, and reads as ordinary text thereafter:

    (ai (quote (forsome n_ ...)))
    (name-witness! 3 (quote w1))
    (cut (quote (forall k ... w1 ...)))

`w1` is the PAGE's name. `name-witness!` (interactive.scm) binds it to whatever this
session minted at recorded step 3, and `->raw-formula` -- which every surface tactic
already runs over its formula arguments -- substitutes it back out. Verified: **zero
pages carry a counter-minted name**, and `rr-limit-scale`, a page that was
`incomplete` that morning, types back in `grounded`.

**Nothing about what is RECORDED changed.** `*proof-script*` still holds the literal
names, so proof-tex, harvest and the replay audit are untouched; the aliases are
introduced by the EMITTER (`script--write-block`) and resolved when a page is typed
in. The mint record lives beside the script in `*proof-mints-table*`.

**One invariant to keep: one `*proof-mints*` entry per RECORDED step.** The capture is
in `record-cmd!`, not `vnb--run!`, precisely because `focus`, `focus-id`, `prop`,
`minimize!` and `dk-focus!` record themselves directly -- a step with no entry shifts
every later step's number, and that number is what `name-witness!` cites. It also does
the right thing for a composite that mints internally and records only itself: the
names are attributed to the composite, which is the step a reader would name.

**Three measurements decided the design, and two of them overturned a plan:**

* **The staging was wrong, and a pre-registered prediction caught it before the work.**
  The plan was role 1 first -- record an INDEX for arguments that merely SELECT an
  assumption (`ai`, `mac-h`, `inst+`, `wk`, `detach!`, `slot-h`, `sep-me`, `lam-b-h`),
  which `->raw-formula/idx` already accepts. That is 2080 of 5875 nested occurrences
  and sounded like a third of the problem. Predicted gate line after it: **709**. A
  page fails while ANY minted name survives, and **302 of the 315 failures have one in
  a `cut`/`subst`/`fact`/`ew` argument**, which role 1 does not touch. Counting
  OCCURRENCES when the gate counts PROOFS is the error; role 1 is legibility work, not
  the fix.
* **Inline `,(witness-of 3)` vs naming: 16 to 1.** 728 distinct (proof, variable) pairs
  account for **11623** occurrences -- median 9 uses each, max 228, only 117 used once
  or twice. Naming costs 728 lines; inlining would have cost 11623. (MIT's `write`
  prints `(quasiquote ...)` in full, but that was never the deciding objection -- the
  printer is ours and could emit `` ` `` and `,`.)
* **Every minted-variable use traces to exactly ONE minting step**: 637 uses, 0
  orphaned, 0 ambiguous (`mint-attribution.scm`). No heuristic -- `fresh-var` names
  `<hint>_<n>` with n the counter at mint time and the counter only rises, so the step
  during which it crossed n IS the minter, by arithmetic.

### `ass-all` RECORDS ITSELF (2026-09-08): 983 -> **1011**

`ass-all` (interactive.scm) sweeps the open goals closing whatever the context
already proves, and until now it did that by hand -- `set-proof-state-focus!` plus a
direct `cmd-assumption`, neither of which reaches `record-cmd!`. So a proof driven
with it emitted a page that replayed every recorded step faithfully and then STOPPED,
with exactly the leaves the sweep had closed still open. 116 call sites across 30
files; `mat-equiv-proof.scm` ends nearly every line with it.

The diagnosis is worth the shape as much as the result: three residue proofs, typed in
form by form against `*proof-live-trace*`, showed **no goal divergence at all** -- every
step matched the live run -- and simply ran out of steps with 1-2 leaves open. A page
that never goes wrong and merely stops is the signature of an unrecorded driver, not of
a bad step.

The fix records what the sweep DID and changes nothing about what it does: same nodes,
same kernel call, same order, `record-cmd!` added after each success (so a leaf the
sweep cannot discharge writes nothing -- most leaves in a sweep are not
assumption-closable and a focus step for each would bury the page). It records
`focus-id`, not `focus`, because it sweeps `dg-ungrounded-nodes`, which includes
non-leaves a positional index into `proof-open-leaves` cannot name -- and `focus-id`
had **no case in `apply-recorded-cmd!` at all**, the same hole `slot` and `prop` had
until 2026-09-06. Node numbers come from the per-proof counter, so they reproduce.

This was the June note in `project_proof_script_emitter` -- "Remaining gap: `(ass-all)`
still not step-recorded" -- known for three months and never connected to replay.

**The prediction missed, and by a useful amount: 1015 predicted, 1011 measured.** The
model was "the file calls `ass-all`, so that is its only gap", true for 28 of the 32
and false for 4. Residue is now **11**, and a DIFFERENT 11 -- the whole
`mat-equiv`/`elem-*-invertible`/`rolle-neutral` group cleared, and only 3 of what
remains has no minted name. `zz-bezout`, `qq-line-is-module` and
`rr-nvs-is-normed-vector-space` were in the replay audit's ERROR class rather than its
silent class, so they are a different defect again.

Residue before this: **39** -- 11 with no minted name at all, plus 28 broken for a
second reason. Driver work, not a rendition question.

### THE INDEX PASS WAS BUILT AND REVERTED (2026-09-08) -- keep the reason

Selector formulas (`ai`, `mac-h`, `inst+`, `wk`, `detach!`, `slot-h`, `sep-me`,
`lam-b-h`) are **31% of the page corpus**: 6319 arguments, 747540 of 2377736
characters. Emitting `(ai 3)` instead is a large legibility win and
`->raw-formula/idx` has accepted an integer all along.

It does not work computed from outside the page's own run, and the pre-registered
criterion caught it. The index is the formula's position in the context BEFORE the
step; `*proof-live-trace*` cannot supply it (no record for `focus`/`focus-id`, which
are exactly the steps that change which context is in view), so the emitter replayed
with `apply-recorded-cmd!` and the counter restored. **The page runs through the
SURFACE tactics with no counter, and those two paths are not the same execution** --
the first page measurement had them at 983 and 979. For SEVEN proofs the assumption
positions differ, the emitted index named the wrong hypothesis, and the gate went
**1011 -> 1004**: `card-pair`, `chosen-centre-is-centre`, `coord-block-estimate`,
`finite-ball-subcover-r-net`, `spans-fg-base`, `subseq-of-convergent`,
`totally-bounded-has-cauchy-subsequence`.

A first guess -- that the index replay's `(sp ...)` was clobbering `*proof-mints*` /
`*witness-aliases*` / `*fresh-mark-at-last-record*`, which the fluid-let did not
protect -- was tested and is NOT the cause: protecting them changes nothing.

Doing it properly means computing the index inside the page's own execution, a third
pass over every page, on a gate whose emit-and-replay had already gone 61 s -> ~150 s.
For legibility. Reverted; the argument is preserved in interactive.scm above
`script--write-block`. **The rule it teaches is general: a positional reference is only
as good as the execution that resolved it, so compute it in the run that will use it.**

**The repair chosen is B, not A** (the user's call, 2026-09-07). A is one line --
wrap the emitted block in `(fluid-let ((*fresh-counter* N)) ...)`, N from
`*proof-start-counter*`, as proof-tex's replay already does -- and it would take 707 to
983. It was declined because the page then works only by carrying a number about the
machine that printed it: a serialization with a side channel, not an invertible notch,
and an unreadable line at the one rung whose job is to be exact. B records a witness by
PROVENANCE ("the variable step 47 minted") instead of by name, so the page is
self-contained and the name is one the upper rungs can also use. B's target is
therefore **983**, and the 39 that fail even with the counter restored -- the 11 above
plus 28 that are broken for a second reason as well -- are separate driver work.

Five suite checks pin the MECHANISM, not the number (the number is expected to move).
The control is `scratchpad/gate-control.scm`, and its middle probe is the one that
justifies the gate existing: a page with its last step deleted comes back `incomplete`,
never `error`.

