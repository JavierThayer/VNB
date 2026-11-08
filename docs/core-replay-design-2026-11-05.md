# Core replay: a proof re-run in a closed command vocabulary (design, 2026-11-05)

Status: DESIGN ONLY. No code exists. Source: notes-69 item 2; outline accepted in
`~/notes/response-to-notes-69.txt` s.4; the user's decision that the oracles count as
core, one step each, because their certificates are checked.

Terms. A *page* is the emitted text of a recorded proof script
(`script--write-block`, interactive.scm:6135). An *entry point* is one of the 57
procedures that call `dg-apply-rule!` (reference/KERNEL-MAP.md). The *core* is the
closed list of commands defined in s.1. A *core page* is a proof written in core
commands only. *Core replay* is the act of re-creating a proof from its core page.

## 0. Findings that shape the design

F1. The page alphabet is already closed and small. A page holds exactly what
`record-cmd!` (interactive.scm:138) appended. Its callers are `vnb--run!` (61 distinct
command symbols in the tree) and seven direct recorders: `focus`, `focus-id`
(interactive.scm, driver-kit.scm:195/204), `bc*` (interactive.scm:2221), `prop`
(prop.scm:497), `mp` (mp.scm:166), `minimize!` (minimize.scm:314); `keep` and
`zero-it` go through `vnb--run!`. No `dk-` helper records itself: driver-kit.scm calls
`record-cmd!` only for `focus` / `focus-id`, so a kit helper's page is its surface
sub-steps. The preamble records no step of its own (preamble.scm:395); `dk-diff!`
drives surface tactics. The composites that record ONLY THEMSELVES, running their inner
steps with `*replaying?*` bound, are `prop`, `mp`, `minimize!`, `zero-it` and the `bc*`
handlers.

F2. A page is CODE, not data. `page--type-in` (page-audit.scm) `eval`s each form in
`user-initial-environment`; the `bc*` case evaluates the handler forms as source
(interactive.scm, `apply-recorded-cmd!` bc* branch); `replay--surface!` runs the
surface procedures `slot`, `slot-h`, `prop`, `mp`, `minimize!`, `zero-it`. A page that
re-runs therefore re-runs through the composite tactics and any Scheme it contains.

F3. The BILL is read off the SCRIPT, not off the graph. `record-proof-debt!`
(proof-debt.scm:176) takes `proof-citations` of `*proof-script*` plus
`*proof-hidden-citations*`. The certificate's `uses` field is the kernel's own list
(`*proof-used-defs*`, deduction-graphs.scm:405), but it holds macete names and
definitions read by checkers only; a `theorem-assumption` inference records the bare
tag `theorem-assumption` (primitive-inferences.scm:1466), with no name. No code
compares a bill with what the kernel actually cited. Both past ledger defects (the
`bc*` handler citations of 2026-09-18; the phantom leaves of `mac`'s NAME-def
fallback) were disagreements of exactly this kind.

F4. The deduction graph is not kept after a proof. It exists at `qed` (in `*ps*`) and
inside `page--type-in`'s AFTER thunk. In a certified (daytime) load no proof runs and
no graph exists; core replay is therefore an EXAM-only check.

F5. Rolled-back work leaves no inference node. Transactions (`dk--transaction`, the
preamble's commit rule), `undo` and probes (`vnb--probing`, scratch states) either
journal-roll-back or work on a copy. The FINAL graph, walked from the root, is the
proof; a call trace of the run is a superset of it.

F6. Current exam (last-exam.json, 2026-11-05, worker-05): wall 12212 s, GC 6195 s,
page audit 2250 s, 18359 theorems; page audit 9993 of 9998 pages replay.

## 1. The candidate core list

Each core command is DEFINED as one call of one entry point at one named node. The
surface tactic of the same name is that call plus focus handling; the core command
takes its node explicitly (s.3, `at-node`).

A. Kernel rules (TACTICS.md kind `rule`, 48). Entry point in brackets.

    di [pi-direct-inference!]        ai F [pi-antecedent-inference!]
    pbc [pi-proof-by-contradiction!] oi-l, oi-r [pi-or-intro-left!/-right!]
    ew T [pi-exists-witness!]        ci, ti [pi-cartesian-intro!, pi-tuples-intro!]
    ii [pi-intersection-intro!]      ui K [pi-union-intro!]
    ni, tfi, tfi3 [pi-nn-induction!, pi-tfi!, pi-tfi3!]
    ass [pi-assumption!]             ta NAME [pi-theorem-assumption!]
    inst F T [pi-instantiate!]       detach! F [pi-detach!]
    bc F [pi-backchain!]             cut F [pi-cut!]
    wk F [pi-weaken!]                ce, te, ie, ue [the four -elim! entry points]
    mac NAME, macm NAME [elementary macete via apply-macete!; macm = spawn fluid on]
    mac-h NAME F [apply-macete-to-assumption!]
    subst EQ [pi-eq-subst!]          rfl, qrfl [pi-reflexivity!, pi-quasi-reflexivity!]
    beta [pi-functoid-beta!]         lam-t, lam-b, lam-b-h [pi-lambda-*!]
    nth-r, len-r [pi-nth-reduce!, pi-length-reduce!]
    if-true F, if-false F [pi-if-true!, pi-if-false!]
    sep-set, sep-mi, sep-me F; comp-mi, comp-me F; iota-d T, iota-e T;
    bu-set, bu-mi T, bu-me F [the schema entry points]

B. Oracles (the user's decision, one step each; certificate-checked): `arith`
[pi-arith!], `crs` [pi-comm-ring-simplify!], `rs` [pi-ring-simplify!], `ineq`
[pi-ineq!, premises by FORMULA], `sos` [pi-sos!]. 5.

C. Structure: `sp`, `qed`, and one new command `at-node N` (focus the replay node that
corresponds to node N of the core page). 3. (`at` is avoided: the name is taken by the
pending transport proposal.)

Core size: **56** commands. `prop` is not among them: it is lowered (s.6 Q1, decided).

Entry points with no core command: `pi-spec!`, `pi-truth!`, `pi-contraposit!` (all
unexercised in the library, KERNEL-MAP.md), and the two decomposition closures
`<macete:cartesian-decompose>`, `<macete:tuple-equality-decompose>`, reached today only
through `arith`. The closures get `mac 'cartesian-decompose` /
`mac 'tuple-equality-decompose` if they are addressable by name in the macete table
(to confirm in step 2), else two core names. A core page needing an unexercised entry
point is refused, with the reason.

Documented tactics that are COMPOSITES and are lowered, not core: the 19 of TACTICS.md
kind `composite` (`type-term ew-poly expand zero-it preamble inst+ mp grind-and-mp fact
bc* mac-h* grind wbc calc scout-run minimize! obtain have! vlet`), `simp` (kind
`oracle` but a cut + crs + eq-subst composite), and the untagged `slot`, `slot-h`,
`keep`, `prep`, `supply`, `focus`, `focus-id`. `keep` is a run of `wk` and lowers to
it. `fact`, the commonest step of all, lowers to `ta`, one `inst` per peeled universal,
`detach!` per discharged antecedent, and the closing steps of any owed definedness
leaf.

## 2. What a page contains today that is not core

The alphabet (F1) has 68 recorded names plus the page-side `name-witness!`. Outside the
core: **16** names -- `fact inst+ keep slot slot-h mac-h* grind bc* mp minimize!
zero-it simp apply-thm focus focus-id name-witness!`, and `prop` (lowered; s.6 Q1).
`apply-thm` and `simp` have no `apply-recorded-cmd!` case: they replay only through the
surface (the page), not through `replay-audit.scm`.

No stored page corpus exists in the tree (pages are rendered to strings in memory by
`page-of` and discarded; certificates hold no script). As a PROXY, call sites in the
885 theorem-library files (comments and strings stripped; 132260 calls of alphabet
names in all):

    fact 43956  subst 26566  ass 19496  mac 6733  di 5514  crs 3925  rfl 3904
    ew 3434  mac-h 2536  ai 2437  prop 2055  qrfl 1444  sep-me 1234  inst+ 1206
    arith 1098  slot 731  detach! 627  lam-b 607  cut 396 ... keep 105  slot-h 71
    bc* 55  mp 32  focus 28  grind 10  minimize! 8  simp 2  apply-thm 1

Non-core share of call sites: about 46000 of 132260 (35%), `fact` alone 33%. A call
site inside a loop or a kit helper (driver-kit.scm: 590 more) records many steps, so
these are not page counts. Step 1 of s.5 writes the exact counts.

## 3. The lowering

Per-step trace (the outline) versus final graph. The outline read each step's kernel
trace. A raw trace includes inferences later rolled back (F5); the final graph does not,
but its inference nodes carry only the rule tag, not the entry point's arguments
(`theorem-assumption` carries no name; `ineq` carries premise IDS, not formulas). The
design uses both: CAPTURE the arguments of every entry-point call, keyed by the
inference nodes the call created, and keep only the records of inference nodes that
survive in the final graph.

Capture. While `VNB_CORE_REPLAY=on` (exam only), a new file `core-replay.scm` wraps
the 57 entry points plus `apply-macete!` and `apply-macete-to-assumption!` by
`environment-assign!`, as `kernel-map-trace.scm` does (that instrument observed 0
inferences recorded outside an entry point over 197669). Per call it records: entry
point, target node, the non-node arguments, the values of the dynamic variables the
kernel reads (s.5 R1; at least `*macete-spawn-conditions?*`, `*match-var-head*`,
`*rewrite-path-bvars*`), and the inference nodes added. Nested calls are attributed to
the innermost entry point. Positional arguments are converted at capture time to what
they denote: an assumption index to the formula at that node, an `ineq` premise index
to its premise formula. No core page carries an index.

Lowering (at `qed`, after the certificate record is written). Walk the grounded proof
tree from the root, choosing for each node one in-arrow whose hypotheses ground with a
smaller rank (well-founded; a hash-consed node is emitted once). Emit, depth first, one
`(at-node N CMD ARG ...)` per chosen inference, from its capture record. Node ids are
renumbered densely in emission order; minted eigenvariables are renamed `v1`, `v2`, ...
in order of first minting. The core page therefore holds no counter-minted literal and
no machine-dependent number (the page standard). An entry point that recorded several
inferences in one call (`di`'s chain of introductions, a `keep`) yields one command at
the first node; the later nodes of the chain are found already justified at replay.

Recovery fallback. Where capture is missing (an entry point the wrapper did not see),
the argument is recovered from the inference node by the relation its checker tests:
`cut` = the lemma branch's goal, `ew` / `inst` = the term found by matching, `subst` =
the context equation (either orientation) whose substitution yields the hypothesis,
`ta` = the installed theorem whose statement the context gained (ambiguous when two
names share a statement: the proven-duplicate backlog). Every recovered argument is
counted; the target is zero.

Where replay breaks today, and what replaces each device:

| ephemeral reference | page today | core page |
|---|---|---|
| `focus k` (position in open leaves) | recorded as is; shifts when leaf counts differ | `at-node N`, mapped by the replayer |
| `focus-id n` (per-proof node number) | reproduces only when the same nodes are made in the same order | not used |
| assumption index (`ai 3`) | never emitted: pages reprint the formula (reverted index pass, interactive.scm) | formula; index computed at replay |
| `ineq` premise indices | recorded as indices | premise formulas; indices computed at replay |
| minted eigenvariable | `name-witness! STEP ALIAS` per recorded step (`*proof-mints*`) | canonical `vK`; bijection learned at replay |
| `*fresh-counter*` | not restored on a page | irrelevant: names are mapped |

`name-witness!` ties a name to a RECORDED STEP; a lowered page has different steps, so
the mint record cannot be reused as it stands. The replayer instead learns the mapping
at each minting inference by comparing the produced hypothesis sequents with the
recorded ones; the map must stay a bijection.

## 4. What the core replay verifies, precisely

Already verified without it: (i) every inference, by an independent checker at
`dg-apply-rule!`, none on trust; (ii) the closed list of writers
(`kernel-callers-audit`); (iii) `qed` refuses an ungrounded graph; (iv) the page audit
re-derives a grounded graph from the recorded surface commands.

Added by the core replay:

1. An independent rebuild of the graph BOOKKEEPING. The checkers verify each inference
   as a relation; nothing independent verifies node sharing (`dg-post!` reuse), the
   grounding propagation (`dg-propagate-grounding!`) or the journal rollback. A fresh
   graph built from the surviving inferences alone, and grounded at its root, checks
   those.
2. A proof object that is DATA: a finite list of entry-point calls in a 56-name
   vocabulary, replayed by a dispatch table with no `eval`. It does not depend on the
   driver kit, the composite tactics, the preamble, the owed-leaf hook, `bc*` handler
   source, or any Scheme on a page (F2). It is the artifact an external re-checker
   (META's K3 option C) would read.
3. Per theorem, the KERNEL'S citation list: the names handed to
   `pi-theorem-assumption!` and the macete names of the surviving inferences, and the
   oracle heads. Composed transitively over earlier theorems' kernel lists, it gives a
   second bill, computed without the ledger (F3), compared with the recorded bill.

Not added: independence from the entry points' builders, the checkers, the theorem and
macete tables, the definitions, or the oracles' certificate checkers -- the replay runs
the same kernel on the same tables. Nothing for a theorem installed from a certificate
in a daytime load (F4). For theorems proved through companions or the view
specializer, which have no `sp` / `qed` proof, nothing: they are counted apart.

Verdict. Every inference the core replay re-creates was already checked by an
independent checker when the proof ran, so for the soundness of a single inference the
replay adds next to nothing. What it adds is an independent rebuild of the graph
bookkeeping that no checker covers, and a data-only, eval-free proof in a 56-command
vocabulary that does not depend on the kit or the composite tactics. For the claim
"modulo 0" the larger gain is the bill read off the kernel's own citations instead of
off the recorded script; it needs only the capture and the final graph, not the replay.
It is therefore built first (step 2).

## 5. Build plan

| step | content | files | days |
|---|---|---|---|
| 1 | Page corpus: under `VNB_CORE_REPLAY=on`, the page audit writes every page (gzipped text) outside the tree; a Python counter gives exact counts by name | page-audit.scm; scratchpad tool | 0.5 |
| 2 | Capture + KERNEL BILL: entry-point wrappers, the surviving-inference filter, per-theorem kernel citation list, transitive kernel bill; load line `;; kernel-bill: N agree, M differ` with the differing names | core-replay.scm (new); interactive.scm (one hook in `qed`, after `cert-make-record`); load.scm (load + end report) | 2.5 |
| 3 | Lowering: proof-tree walk, ranks, dense ids, canonical mints, emission; the dynamic-variable list from a static scan of the kernel files | core-replay.scm | 2 |
| 4 | Core replayer: dispatch table core name -> entry point; `at-node` with the node map; mint bijection; per-entry check that the produced hypothesis sequents equal the recorded ones up to alpha and the map, in order; a node already carrying a matching inference is accepted without running; verdict `core-replayed` or `refused at step k (command, reason)` | core-replay.scm | 3 |
| 5 | Exam wiring: `vnb-band --exam` and `vnb-nightly-exam` set the flag; load line `;; core-replay: core-replayed N of M`, refusals listed; a field in last-exam.json; TACTICS.md marks the core (tactics-help.scm) | vnb-band, vnb-nightly-exam, load.scm, tactics-help.scm | 1 |
| 6 | One exam on a worker at night with the flag on; measure; warn-only until the refusal backlog is zero, then fatal like the other gates | -- | 1 + one night |

Total about 10 working days.

Kernel hash: NO CHANGE. None of the files touched is in `*cert-kernel-files*`
(certificates.scm:220-238: primitive-inferences, macetes, library, arith-eval, the four
oracle files, deduction-graphs, expressions, sequents, the four checker files).
core-replay.scm calls entry points, never `dg-apply-rule!`, so
`*kernel-caller-files*` is unchanged. The `load.scm` edit makes the next integration a
cold load (extend-band refuses), which the exam is anyway. interactive.scm and load.scm
are wired files: claim and release them under the two-session rule with META.

Isolation inside the image. The replay runs inside `fluid-let` of `*ps*`, the four
recording globals, `*fresh-counter*` and `*fresh-log*` (so later proofs mint the same
names as without it), `*proof-used-defs*`, `*pi-owed-nodes*`, the journal, and the
inference-check counters (replay refusals are counted on their own line, not hidden).
Capture records are dropped after each `qed`: only the verdict and the kernel citation
list are kept, and nothing enters the band.

Suite checks (each accepted / refused pair is a control that fails on a broken
implementation):

1. A proof using `fact`, `bc*` with a handler, `keep` and a preamble firing is lowered
   to core names only and core-replayed; the same core page with one argument altered,
   one entry removed, or a non-core form inserted is refused at the right step.
2. Mints: core-replayed after the counter is advanced by 1000; refused when the map is
   forced non-injective.
3. Rollback: a proof whose driver rolled back a transaction and a rejected preamble
   rule: the core page omits those inferences and replays.
4. Sharing: a proof with a node grounded by hash-consing replays and emits it once.
5. Dynamic state: a `macm` proof replays; replayed with the spawn fluid not restored,
   it is refused.
6. `ineq`: replays with the context permuted (premises resolved by formula).
7. Kernel bill: a proof citing an asserted support inside a recording-suppressed step,
   with the hidden-citation list disabled for the check: kernel bill differs from
   ledger bill and is reported; an ordinary proof: equal.
8. Coverage gate: every entry point in reference/kernel-map-static.sexp has a dispatch
   entry or is on the refused-unexercised list.
9. With the flag off, every wrapped entry point is `eq?` to its original.

Exam-time cost (estimate; measured in step 6). The replay runs no tactic search, no
context scan of `fact`, no scratch probe, no preamble trial: entry points and checkers
only. On the 2026-11-05 exam (12212 s wall, 2250 s page audit, half the wall in GC),
the estimate is 600-1500 s for the replay, 3-5% for the capture wrappers, and more GC
from the per-proof records. Budget: +10-20% of exam wall.

Main risks.

- R1. Hidden dynamic state read by entry points (fluids set by `bc*`, `macm`, `mac-h`;
  global tables a driver mutates mid-file). Mitigation: static scan of the kernel files
  for free references to globals that are `fluid-let` or `set!` outside them, values
  captured per call; control 5.
- R2. False refusals from node identity: the replay builds fewer nodes and may share
  differently. Mitigation: nodes are matched by sequent through the node map, never by
  number; entries under a node already grounded by a different inference are skipped
  and counted.
- R3. Mint mapping errors; a name that occurs in a surviving formula but was minted in
  a rolled-back attempt. Mitigation: refusal with the name.
- R4. Cost and memory (GC is already half the wall). Mitigation: records dropped per
  proof; flag off by day.
- R5. The kernel keeps moving (META: row 57, K3). Every new or narrowed entry point
  needs a dispatch entry; check 8 enforces it.
- R6. Wrapping kernel entry points is an instrument on the trusted base. Mitigation:
  wrappers installed only under the flag, removed after, check 9; the wrapper calls the
  original and records nothing in the graph.
- R7. Proofs outside `sp` / `qed` (companions, specializer) are outside M; the count is
  reported, so "N of M" is not read as "every theorem".

## 5a. The Emacs surface (the user, 2026-11-06)

REQUIREMENT. The core page of a theorem is available from the Emacs interface,
mouse first (menu entry and right-click on a theorem name; no new toolbar icon
unless the user asks):

* "Show core proof": opens a read-only buffer with the theorem's core page, one
  core command per line, each line carrying its proof-tex step number, the
  focus goal before the step on demand (hover or a toggle), and the verdict line
  (core-replayed / refused at step k, command, reason).
* "Replay core proof": types the core page into the workspace, step by step
  (forward / back buttons, as for a recorded script), so the user can watch the
  proof in core commands only.
* Source of the page: the core page written at the last exam (s.6 Q2); for a
  certified theorem whose proof did not run in this image, the same route as
  display-proof (run the file through the certified loader with this theorem's
  record withheld), under vnb-long-command-budget.

Build step: after step 6 of s.5, in emacs/vnb-launch.el with its panel checks
(emacs --batch -l emacs/vnb-panel-check.el), one accepted and one refused page.

## 6. Open questions

Q1. DECIDED (the user, 2026-11-05): `prop` is LOWERED. It has no kernel rule and no
certificate; it decides by truth evaluation and then discharges through ordinary
checked logic inferences, so lowering expands it at no cost. Its listing among the
oracles on 2026-11-04 was an error. The oracles that stay single core steps are
`arith` (arith-ground, arith-forsome, arith-simplify), `crs` (comm-ring-simplify),
`rs` (ring-simplify), `ineq` and `sos`: seven kernel rules, each with a checker in
rule-checkers-oracle.scm.

Q2. Where the replay runs: in the exam image at each `qed` (cheap, in load order, same
tables) or in a fresh image from a written corpus of core pages (independent of image
state, needs a load-order check of its own). Recommendation: in the image first; write
the corpus as well, for the counts and for an external re-checker later.

Q3. When the kernel bill and the ledger bill differ, which is reported as the
theorem's bill? Recommendation: the WORSE of the two until the difference is
explained, and the difference listed as a ledger defect.
