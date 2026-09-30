# VNB proof checker -- working brief

VNB is a proof checker and more generally a math assistant to help
users discover proofs. It is written in MIT Scheme with a user interface in
GNU/Emacs. Much of the documentation is available using a web
interface. There is also a manual which needs periodic update.  The
logical framework is von Neumann-Bernays set theory but with copious
ready-made constructors. Its research state (what is proven, what is
next) lives in Claude's memory index, not here. This file holds the
operational facts that are expensive to rediscover.

**This file was trimmed on 2026-09-18** from 155 KB to its rules. The dated findings,
measurements and case histories behind each rule were moved, VERBATIM, to
`docs/history/claude-md-2026-09-18--<section>.md`; the untouched original is
`BACKUP-CLAUDE.md`. Each section below ends with a pointer to its history file. When a rule
here looks arbitrary, the history file has the incident that produced it.

## Where the project is going

The **prove-theorem stage is done** (2026-07-11): `spans-submodule-fg` -- and with it
`submodule-fg` -- is proven, and since 2026-09-17 it bills `modulo 0`. Its purpose was never
the theorems themselves: it was to exercise and stress the machinery. Two claims made about
it on the way were false and are the standing lesson: "no asserted step" was never
re-checked against the bill, and one asserted support (`matof-exists`, unquantified
dimensions) became UNSOUND when a lemma proven much later, for an unrelated reason, met it.
An assertion that is harmless when written can become unsound later; the bill ledger exists
to make that visible. The repair (total `SIZE`, `[]` as the 0-by-n matrix, `LINCOMB` as a
FINSUM, guarded product laws) is `docs/size-mat-surgery-2026-09-16.md`.

**The rake phase (2026-08-31 to 2026-09-19) and its exit criterion.** The user's criterion for
leaving it (2026-09-18): NO ATTEMPTED PROOF LEFT INCOMPLETE -- every theorem that reached
`qed` bills `modulo 0`. **MET on 2026-09-19** (cold load 18:23 UTC: 2153 proofs, 2153
`modulo 0`; suite 1272 / 0); the page is `docs/rake-batch7-2026-09-19.md`, the agents' reports
`scratchpad/triage/RAKE-BATCH7-REPORTS.md`. The evening's follow-ons and consolidation (2150 / 2150,
PSS 71, suite 1290 / 0; Bolzano-Weierstrass; one home for the NVS laws; the kit additions) are
`docs/batch8-2026-09-19.md`. 2026-09-20 (CARD defined, INTERSECTION-OF, the CHECKING kernel,
four trusted-base defects found and closed, Ascoli and all four Prop 3.12 equivalences proven):
`docs/batch9-11-2026-09-20.md`. The design for differentiation over a normed field, DECIDED by the
user 2026-09-20 (one `IS-DIFF-ON(K, U, f, a, L)`, `U` OPEN by definition, the real theory untouched behind a
bridge theorem): `docs/diff-on-open-sets-2026-09-20.md`. Batches 12 and 13 of the same day (the metric SUBSPACE, `IS-DIFF-ON` with all its laws and the bridge
to `IS-DIFF-AT`, `cc-is-normed-field`, Heine-Borel for an interval as a space, Baire, the hoist of
seventeen proof-free files, the qed-failure gate, the repair of the definedness certificate; 2340
proofs, all `modulo 0`, PSS 66, suite 1571 / 0): `docs/batch12-2026-09-20.md`,
`docs/batch13-2026-09-20.md`. 2026-09-21 (THE STATEMENTS FOLLOW THE USER'S NOTES: a function lives ON its interval or open set, never
`fun(rr, ...)` plus interval parameters -- he withdrew a decision over this; the list of MAJOR THEOREMS,
`docs/major-theorems.pdf`, generated at every load from `docs/major-theorems-table.sexp`; the calculus on an
interval with the local derivative `has-deriv-at`; the DEFINITIONS of the integral along a path; 2471 proofs,
suite 1573 / 0): `docs/batch14-15-2026-09-21.md`. The number to keep at zero is proofs minus
`modulo 0`: a new proof that bills a support re-opens the rake. The user's order of work from
here: (a) keep the leaves clear, (b) documentation cleanup, (c) the terrain for COMPLEX
ANALYSIS -- first the metric SUBSPACE structure (it blocks the local inverse function theorem,
the neighbourhood chain rule, the open-set hypotheses of calculus.pdf 2.23-2.29, Heine-Borel),
then R^n with the sup norm (Props 2.28 / 2.29).

The project's three standing goals:

1. **Print proofs and read proofs.** `proof-tex` (full trace) and `proof-reader` (sketch)
   are faithful but report the *official* level where a human wants the *content* level
   ("Since `a` is a Euclidean ring, `a` is a ring"). The ONE operator table is
   `operators.scm`, populated by `def-predicate` / `def-functoid` via `register-operator!`,
   with readings declared by `notation!`; `wff-english`, `describe-structure`,
   `OPERATORS.md` and `expr->tex` (through `operator-render-tex`) read it. Outstanding on
   the reader: collapse runs of subtype-subsumption citations; capture the goal BEFORE each
   step; render `IS-EUCLIDEAN-RING(a)` as "a is a Euclidean ring".
2. **A large database of theorems without proofs**, indexed and searchable; the PSS is the seed.
3. Revisiting the manual against all of it.

Do not treat "prove one more theorem" as the goal. The deliverable of a proof request is
usually the obstacles it exposes.

**Where a definition lives, and the trap under it.** `def-predicate` / `def-constant`
install a THEOREM (the defining iff or equation), so they appear in `DEFINITIONS.md`.
`def-functoid` installs only a rewrite MACETE. Consequences:

* `mac` unfolds a functoid in a GOAL; **`mac-h` cannot unfold one in an ASSUMPTION by the
  functoid's own name** -- it warns `unknown theorem/macete` and the driver continues with
  the hypothesis untouched. The cure is to PROVE the unfold equation, one line, `modulo 0`:
  `(sp (make-wff '(FORALL ... (== (F a_) <body>)))) (di) (mac 'F) (qrfl)`; the resulting
  THEOREM is what `mac-h` can name (`theorem-library/poly-membership.scm` has seven). A
  functoid whose VALUE is read out of a context wants both unfolds as theorems.
* A `same-shape-as` structure (`VECTOR-SPACE`) has the same hole one storey up: prove
  `is-vector-space-unfold` the same way.
* `def-functoid` REFUSES an empty parameter list (2026-09-18): `'()` used to install the
  dead macete `(NAME ())`, leaving the constant uninterpreted. A parameterless defined
  object is a `def-constant`.
* A function-valued constant that is ALREADY registered (`eplus`, `etimes`) is defined by a
  `definitional`-wrapped `add-axiom!` of a quasi-equation plus `declare-named-only!`,
  not by `def-constant`; and because no rewriter unfolds a registered constant head in
  APPLIED position, its laws go through `apply-congruence-2`.
* Name-shape trap: `zz-bezout` is a THEOREM; the thing defined is `ZZ-BEZOUT-SET`.

History: `docs/history/claude-md-2026-09-18--where-the-project-is-going.md`.

## Running it

    ./prover                  # interactive REPL
    ./prover file.scm         # load a proof script, exit
    ./prover -i file.scm      # load a script, then drop into the REPL
    ./VNB                     # launcher (cold boot re-proves the library)
    ./VNB-with-compile        # recompile sources, then launch

Full check suite (needs an explicit heap since 2026-09-15; ~11 minutes on a t3.medium):

    timeout 4000 mit-scheme --heap 200000 --quiet --load test-suite.scm < /dev/null

It prints `=== SUMMARY: N passed, M failed ===`. **Run it ALONE, in the FOREGROUND, and check
for that line: exit 0 does not mean it ran.** Under memory pressure, beside another prover,
or launched with `nohup ... &`, it dies silently mid-load with no SUMMARY, nothing on
stderr, and exit 0. `vnb-suite WORKER` runs it correctly on a worker. A suite that stops
with `;lookup-theorem: unknown theorem X` is a stale check naming something retired.

**NO PROOF CHECKS DURING THE DAY (the user, 2026-09-30).** A daytime integration is a
CERTIFIED build: `vnb-band WORKER --build` runs `prover --build-band` with `VNB_CERTIFIED=on`
(the default since 2026-09-30), installs every theorem whose certificate is valid without
running its proof, re-proves only the rest, saves the band. Measured 2026-09-30 on worker-02,
heap 200000: 205 s wall (GC 39 s, gates 52 s, reference 15 s, page audit 1 s; 3441 certified,
39 proven -- the generated projections and functorials, which have no certificate file), then
`vnb-suite WORKER --band --detach` from that band. THE EXAM -- `vnb-band WORKER --build --exam`,
`VNB_CERTIFIED=off`, every proof run, every page typed back, every certificate rewritten:
7300-7400 s on a t3.medium at heap 200000, a third of it GC, 1700 s of it the page audit -- runs
at NIGHT: `vnb-nightly-exam` (cron on the primary, 06:00 UTC; log
`~/mailbox/metrics/nightly-exam.log`, outcome `last-exam.json`) starts a worker, pushes the tree,
runs the exam and the suite, pulls band + `reference/` + `certificates/` back with
`vnb-band-pull WORKER`, stops the worker; it SKIPS when the tree is the one the last exam passed.
Four exams had run in the 48 hours before this rule, two hours each, for integrations of which
ONE had touched a certificate-key file; a key-file change re-proves everything under `on` anyway,
so the certified build IS the exam exactly when it has to be. What the certified build does not
exercise until the night: a driver-kit or tactic change under proofs whose statements did not
move (the certificate skips the driver's steps). Read the morning's `last-exam.json` before
integrating on top of a failed night.

**The integration runs ONE load, not two (the user's decision, 2026-09-23).** The build on
the worker saves the band (`prover --build-band`); `vnb-band WORKER --build`
(2026-09-24) runs it as a detached `capataz run` job through `vnb-metrics-run` (job
`build-band`, the row carries `certified: on|off`) and carries its ledger row back to the primary the way `vnb-suite`'s `--band
--detach` does. The suite then starts FROM that band: `vnb-suite WORKER --band --detach`
returns a job id at once, `vnb-suite WORKER --wait JOB` brings back the digest (124 = still
running); `vnb-band WORKER --wait JOB` is the same pattern for a build-band or extend-band
job. `--band` refuses a band older than any library `.scm`. Measured 2026-09-23: cold load
25m54s, suite from the band 4m05s (1573 / 0), against 28 min for the suite with its own load.

**PROOF CERTIFICATES (the user's decision 2026-09-24; built 2026-09-25, batch 28;
`docs/certificates-2026-09-24.md`, `docs/batch28-2026-09-25.md`).** The everyday load runs NO proof: each
theorem-library file has `certificates/<file>.cert`, one record per `qed` (statement hash, the cited names
and the definitions mentioned with their hashes, bill, oracles, kernel hash), and `sp` installs a theorem
whose record is valid with provenance `certified`, skipping the driver's steps. `VNB_CERTIFIED=on` (the
default of `./prover` and of a stale-band start: certified theorems installed, the rest re-proved and
certified; ~3 min for the whole tree) | `off` (THE EXAM: `prover --build-band`, `vnb-band --build`,
`vnb-test`: every proof runs, the store is rewritten; ~55 min at heap 200000) | `strict` (nothing
re-proved; an uncovered theorem lists and exits non-zero). A changed statement re-proves that theorem and
its citers; a changed kernel file (the `dg-apply-rule!` callers and the four checker files) re-proves
everything. The bill line reads `certified modulo {...}` (no date or host in a record since 2026-09-30: an exam that changes nothing rewrites nothing); the load summary counts `proven` and
`certified` apart; the word `proven` alone means the proof ran in this image. The page audit covers the
proofs that ran. A file the skipper cannot handle is retracted and reloaded in `off` mode with a warning
(none in the tree on 2026-09-25). NOT in the key: a functoid reduced by `beta` or an accessor read by `slot`
(the exam is the backstop; recording them is an open decision). `VNB_LOAD_LIMIT=N` loads the first N proof
files, for development. The store lives in the tree and travels in the tarball.

**EXTENDING THE BAND (built 2026-09-23 from Ignacio's plan; the user's decision: build it, and
keep a cold load after EVERY integration, compared -- option A).** An integration of
theorem-library changes no longer waits for the cold load: push the tree (excluding the band
and `reference/`), then `vnb-band WORKER --extend [--dry-run] [--retire NAME ...]`, which runs
`prover --extend-band` on the worker as a detached job through `vnb-metrics-run` (ledger job
`extend-band`) and carries its row back with `vnb-band WORKER --wait JOB`: it restores the band,
RETRACTS every retired name and every theorem sourced from the reload set
(`retract-theorem!`, extend-band.scm, over every per-name table -- the audit table is in
`docs/extend-band-2026-09-23.md`), reloads only the changed theorem-library files plus, by the
CLOSURE RULE over the bills, every unchanged file holding a theorem whose bill cites a name whose
statement, bill, oracles or provenance changed (the set grows during the run), loads each
reloaded file EXACTLY as the cold load does (the `.com` when fresh, else the `.scm`: the first compare
mismatch, 2026-09-24, was a driver binding two recording calls in one `let`, which compiled and interpreted
code evaluate in different orders -- never bind two recording calls in one `let` or argument list), runs the SAME
end-of-load block (`run-load-end!`, shared with load.scm), and saves to `vnb.band.new`, renamed
over `vnb.band` only on a clean exit. Then `vnb-suite WORKER --band --detach` as before. It
REFUSES, with the reason, when a cold load is needed: the band is not a STRICT build (a
keep-going band, holes, or one built before this code: the marker is `*vnb-band-strict?*`),
anything outside `theorem-library/` changed (kernel, structure-library, load.scm outside its
list, the launcher, driver-kit), a kept entry moved in the load list, a changed file sits
before the `extend-band` entry, a retired name is still stated by an unchanged file, or a
citer cannot be placed. Measured 2026-09-23: dry run 5 s; one changed file 12.7 min, of which
the page audit over ALL proofs 665 s and the reload 2 s (auditing only the reloaded proofs is
the open step-7 decision); the extended band matched the cold band. The ORDER CHECK wraps the
kernel checkers for `theorem-assumption`, `macete` and `macete-hyp`, so a use of a later
theorem through a macete is caught, not only a named cite. THE BACKSTOP: after every
integration a cold load still runs, detached, on a spare worker, and `vnb-band-compare WORKER
COLD EXTENDED` (band-dump.scm; one sorted line per name: statement hash, macete and -rev
hashes, provenance, source, citations, bill, oracles, script hash with counter-minted names
relabelled; the registries, counts and 21 gates re-run) must report ZERO content differences
(load-order facts -- binder owners, eigenvariable counters -- are history, reported only). On a
mismatch the cold band replaces the extended one on every worker and every probe since the
extended band went live is re-verified; the mismatch is a bug in the extension. What only a
cold load refreshes: a topic, warrant, gloss or rests-on REMOVED from a reloaded file survives
in the band until the next cold load. `docs/extend-band-2026-09-23.md`,
`docs/band-compare-2026-09-23.md`.

**A command that does not come back (the user's demo froze on `zero-it` and the preamble,
2026-09-30).** Every tactic the workspace sends is wrapped in `(vnb-with-budget SECONDS LABEL
THUNK)` (interactive.scm; `vnb-command-budget`, 90 s, in vnb.el): a timer event escapes the
command, prints `;; STOPPED after N s: LABEL` on the console and the report channel, and the
REPL is back; what the command printed stays. `(vnb-budget-exhausted?)` is the cooperative
test (the preamble's rule loop stops on it with its report). The `Stop` toolbar button / `M-x
vnb-interrupt` is the backstop: SIGINT returns MIT Scheme to its top level (`;Quit!`), under a
pipe and a pty. Suite: three `budget:` checks. A composite command escaped mid-way may have
taken some steps: `(show)`, then `(undo)`.

The Emacs surface has its own check; run it after ANY edit to `emacs/vnb-launch.el`:

    emacs --batch -l emacs/vnb-panel-check.el      # === PANEL CHECK: N passed, M failed ===

**Keep-going load: `VNB_KEEP_GOING=1 ./prover ...`.** An error in a theorem-library/ or
calculus/ file is recorded and the load continues; failures and unproven HOLES are listed at
the end, in load order (a cascade: read the first entries first). A band built this way is
for repair work only, never the band. An engine or structure-library error still stops it.

History: `docs/history/claude-md-2026-09-18--running-it.md`.

## COMPILE THE TREE FIRST

`.com`/`.bin` are gitignored and excluded from the tarball, so a fresh clone is INTERPRETED
and nothing says so (a library load is minutes instead of seconds). If a load is
inexplicably slow the question is "is THIS file compiled": `ls -la <file>.com`.

* After editing a `.scm`, the stale `.com` is ignored (mtime test) and the file loads from
  SOURCE: harmless for a leaf proof script, ruinous for a core file (`wff.scm` interpreted
  took a load from 24 s to 14 minutes). **Recompile what you edit, before you run anything:**

      mit-scheme --quiet --eval '(begin (compile-file "/abs/path/file.scm") (exit))'

  A compile is seconds and small; it may run on the primary. `(compile-vnb!)` does the whole
  tree incrementally but needs a loaded REPL.
* **Never `compile-file` a file that USES a top-level macro** (`bc*`, `declare-structure`,
  `vlet`): it compiles the form as an application and the `.com` dies on load. Such files
  load from source, which costs nothing measurable. `compile-vnb!` decides with the READER
  (`vnb--form-uses-macro?`), not a text scan; a by-hand sweep must at least grep for the
  three macro heads and delete the `.com` instead of compiling.
* Legitimately uncompiled at the root: `clobber-guard driver-kit load mutation-check
  proven-theorems tactic-uses-data test-suite-negative test-suite` (`tactic-uses-data.scm` is
  generated DATA that tactics-help.scm reads). Check with
  `for f in *.scm; do b="${f%.scm}"; [ -f "$b.com" ] || echo "  $b"; done`.
* **There is no skip-proofs mode** (`VNB_SKIP_PROOFS` was removed). Compiling is the honest speedup.

History: `docs/history/claude-md-2026-09-18--compile-the-tree.md`.

## This box, and the workers

This is the capataz `primary`: a t3.small, 1.9 GB RAM plus 2 GB swap. **No Scheme load, band
build or suite runs here** -- one library heap is all that fits and a second kills the
session. The primary holds the canonical tree, Claude and the agents; heavy runs go to
WORKERS (t3.medium, launched and stopped by Claude, never by agents; at most 10 instances
and about $20/day; idle workers stop themselves after 30 minutes once
`vnb-idle-stop-install` has armed them).

Bringing up a worker (no compile: `.com` files and the band are portable, MIT Scheme 12.1):

    capataz launch worker --yes --json --type t3.medium
    capataz run worker-NN --json 'apt-get install -y -q mit-scheme'
    capataz run worker-NN --json 'fallocate -l 2G /swapfile; chmod 600 /swapfile; mkswap /swapfile; swapon /swapfile'
    capataz push worker-NN --yes --rsync --src ~/prover --dest /home/ubuntu/prover \
        --exclude .git --exclude scratchpad/ --exclude scratch/
    capataz run worker-NN 'bash /home/ubuntu/prover/vnb-idle-stop-install 30'

The dest path must equal the source path (the band carries absolute paths). **Never silence
a push: verify `md5sum` of a changed file on the worker before starting a load** (a lost push
cost a 7-minute load on 2026-09-18). `push --rsync` overwrites the worker's generated
`reference/` and band: after a worker build, PULL them back first (tunnel + rsync with
`~/.ssh/vnb-secondary`; the key must be in the worker's `authorized_keys`), and exclude
`vnb.band` and `reference/` from a push that must not clobber them.

* `vnb-slot ARGS` -- `./prover ARGS` inside a memory slot; two probe slots per t3.medium.
* `vnb-probe WORKER file.scm` -- ships ONE file (gzipped, under ~90 KB) and runs it against
  the BAND; prints a digest (warnings, qed lines, errors, tail). **A failed `qed` is a `;; VNB error`
  line; the digest has flagged those only since 2026-09-20** (an agent reported 25 of 26 theorems
  and never saw the 26th): COUNT the `;; qed` lines against the file's `(qed` forms, and print
  `*vnb-qed-failures*` at the end of a probe. The full log stays at
  `/home/ubuntu/probes/<parent-dir>__<file>.log`. The band is only as fresh as the last
  build: a probe that needs today's unwired files loads them first through a WRAPPER
  (`(load "..." (extend-top-level-environment *driver-kit-env*))`), after shipping them.
* `vnb-suite WORKER` -- the suite, alone, foreground, SUMMARY and FAIL lines brought back.
* Every run through those is metered into `~/mailbox/metrics/runs.jsonl`.
* `scratchpad/surgery/mkprobe-slim.py` wraps a chain in `*vnb-loading*` (no `show` dumps):
  use it from the FIRST probe; the dumps are ~95% of a multi-lemma probe's wall time.

**How a proving wave runs.** The briefs are `scratchpad/triage/` (`PROOF-AGENT.md`, the
`RAKE-BATCH*.md` files). An agent gets a leaf or a bundle, writes ONE new theorem-library
file, probes it on its worker, and reports outcome, load window and the support sites to
retire; it edits no shared file (a REPAIR agent is the explicit exception, and owns its
files alone). The integrator retires supports with `scratchpad/retire.py` (string-aware;
`--note`, `--keep-doc`), renames symbols with `scratchpad/rename-sym.py` (token-aware; never
a regex over Scheme source), wires `load.scm` BY FILE NAME, recompiles, pushes, and runs a
COLD load and the suite on a worker. Only the cold load catches load order, a proof citing
the support it replaces, and `lookup-theorem` on a retired name. When a proof's window is
EMPTY (it cites and is cited inside one file) it is SPLICED into that file between marked
lines, the original archived.

Never `pkill -f` / `pgrep -f` a pattern that occurs in your own shell's command line (it
kills the shell, exit 144): match the executable (`pgrep -x mit-scheme`,
`ps -eo pid,comm | awk '$2=="session-manager"'`) or keep the pid.

History: `docs/history/claude-md-2026-09-18--this-box.md`.

## Case folding -- the trap that keeps biting

Both the VNB reader and MIT Scheme fold symbols to lowercase. `X` is `x`, `SP` is `sp`.

1. **Never name a top-level `define` in a proof file like a tactic or a registered
   constant.** `(define BC ...)` rebinds the `bc` TACTIC. Use the file's helper prefix.
   `clobber-guard.scm` is the gate (it cannot see macros, so `bc*` is never watched). The
   fold reaches a driver's own `let` names too: `LAMAL` and `LAMal` are one variable.
2. Structure accessors collide with obvious binder names (`CARR`, `PTS`, `DIST`, `IDEN` were
   renamed away from `X`, `D`, `ID`). Avoid single letters.
3. Inner binders that would collide take a trailing underscore: `i_`, `j_`, `n_`. Never
   distinguish two names by case (`bd-K` / `bd-k`, `q` / `Q` are ONE symbol; a statement with a
   set `A` and a point `a` has ONE variable, and the goal prints `a in a`). Two top-level
   `define`s in one file that differ only by case are one binding, the second silently rebinding
   the first: `case-fold-define-lint!` (clobber-guard.scm, 2026-09-20) reads the SOURCE text with
   folding off, per file, at load; five files had the collision, none had yet built a wrong term.
4. **A binder list scopes LEFT TO RIGHT**: `forall([s in CARR(r), r], ...)` leaves the
   guard's `r` FREE. `warn-forward-guard-reference!` (wff.scm) warns at expansion.
5. **A binder may not be spelled like a CLASS NAME** (2026-09-18): `rR` folds onto `RR`, and
   `(FORALL rR (IMPLIES (IN rR RR) ...))` reads `forall X. X in X => ...`. The fatal
   `constant-binder-audit` now also tests `*class-name-constants*` (macetes.scm: NN ZZ QQ RR
   CC ORD SET EMPTY-SET POS-INF NEG-INF RR-STAR RR-POS-STAR).

**`lambda` is gone; the binders are `vnb-lambda` and `lambdoid`.** `vnb-lambda` builds a set
of ordered pairs, an element of `FUN(A,B)`, typed by `lam-t` and reduced by `lam-b`; a
functoid record (`lambdoid`) has no typing rule and reduces by `beta`. `parser.scm` errors
on `lambda`. OPEN: the rename of `def-functoid` itself (docs/functoids-and-functions.md, s.8).

History: `docs/history/claude-md-2026-09-18--case-folding.md`.

## Vocabulary

BONGO refers to a bug, a "tournant dangereux", or an otherwise bad idea.
FUBA, GUBA, RUBA, BLAH etc are generic names.

RANDO MUBA and his sister RANDA MUBA are hypothetical VNB users, invoked when a
question is about the WORKFLOW rather than about the mathematics: "RANDO finishes a
proof and types `qed` -- then what?". Either party may raise them. The user uses them
to request a clarification; Claude uses them to give one. The answer they call for is
a concrete end-to-end walkthrough -- which command, on which surface, writing which
file, at which moment, and what it costs -- with the file and line the claim comes
from, not a description of the design intent. If the walkthrough cannot be given
without checking the code, check the code.

## Working with the user

Treats Claude as a colleague, and can be ill-tempered at times. Does
not appreciate Claude forgetting previously settled questions. Does
not appreciate gratuitous compliments. Avoid obvious narrative
statements such as: "Let me check BLAH before relying on memory". Just
say "Checking BLAH".

Register: The user's interaction with the assistant is on an informal
register, very much like the register coworkers would use to interact
in the course of a technical discussion. Use of metaphor, imagery,
analogies to current events etc. to animate the conversation and ease
the burden of finding a pedantic formulation of an idea. The assistant
is allowed to use the same register if the alternative is too
pedantic. However, in any form of documentation the register should be
formal and precise, even if pedantic.

**More interested in technique than in bulk.** One general mechanism that
dissolves a class of obligations beats N bespoke lemmas that discharge them one
at a time. When a proof needs a nasty step, ask first whether the step is an
instance of something the *machine* can do, and only then whether it is a lemma
the PSS should assert. A tactic is untrusted; a support is trusted surface.

When many agents run at once the volume outruns review. Stop launching, integrate in one
verified cold load, and give the user ONE page (state, what was proven, what was found
wrong, open decisions each with a one-line recommendation) rather than the scroll.

## Writing proof drivers

Proof scripts navigate a deduction graph by moving focus between open leaves.

**Navigation and naming**

* **Never navigate by goal shape alone**, and never name an ASSUMPTION by shape: sibling
  branches share goal heads, and a formula the driver RECONSTRUCTED (guessing eigenvariable
  names) matches nothing and silently no-ops. Use the `dk-` kit: run the tactic, DIFF the
  assumption list, keep what appeared (`dk-landed`, `dk-landed-1`, `dk-landed-find`,
  `dk-split!`, `dk-opened`). Read an existential off the axiom INSTANCE (`(caddr <the IFF>)`),
  never rebuild it; copy a constructor call, never its printed reading.
* **`fact`, `inst+`, `inst*!`, `dk-apply!`, `dk-fact!` land the whole instantiation chain**
  (the theorem, each partly-peeled form, the detached result): use `dk-fact!` /
  `dk-deepest`, never put them inside a `dk-landed-1` thunk, and do not let a shape-based
  finder pick a link of the chain. `fact` of a membership IFF lands both the instance and
  the universal (an `iff-for` helper names the instance by its left-hand side). `comp-me`
  lands two formulas.
* **Discriminate a hypothesis on its CONSEQUENT, not on a symbol it contains.**
* **Never rely on where `ass` or `cut` leave focus**; re-focus explicitly, through
  `dk-focus!` (which records the move). A focus helper that returns `#f` on a miss must
  ERROR instead. Loop over `(proof-open-leaves *ps*)` freshly, not over a snapshot.
* Read eigenvariables off the GOAL or off the guard the peel just landed, never off the
  context order and never by index-walking a goal.
* At the head of a structure-predicate theorem use `dk-peel!`, never a counted `di`.

**The tactics' real behaviour**

* `fact` peels leading universals and auto-detaches antecedents already in context; it will
  NOT split a CONJUNCTIVE antecedent. `have!` the whole `AND` first, or the citation lands
  the implication SILENTLY and the failure surfaces branches later (`ord-le-total`,
  `rr-leq-total`, `card-subset-nn`, `finsum-insert`, `descend-computes`, ...). Prefer
  CURRIED antecedents in new statements.
* **`di` is greedy on universals only** (`peel-foralls-raw`, primitive-inferences.scm:41): one
  call peels EVERY leading FORALL, and lands a guard in the same step only when the body is
  literally `(IMPLIES (IN y ...) rest)` for the variable `y` just peeled -- and it then CONTINUES
  into `rest`, so `forall m in NN. forall n_ in NN. body` lands BOTH typings in one call (a
  `dk-di-var!` sees one landing and the next call errors: use `dk-peel!`, read the goal). A universal guarded
  by a PREDICATE (`POS-RR(eps) implies ...`) or unguarded lands nothing on that call; the
  antecedent comes with the NEXT `di`, one plain `IMPLIES` per call; after that a `di` takes a
  `NOT` or SPLITS an `AND`. Loop on the LANDING, not on a count. Greediness costs INDUCTION: `ni` tests the
  literal shape `(FORALL n (IMPLIES (IN n NN) body))`, so state the induction variable
  FIRST (or prove a companion statement with it outermost plus one `fact`). `tfi3` wants
  the ordinal outermost too.
* `ai` on a `NOT` is NOT-ELIM: it fires only when the positive is ALREADY in context.
* `obtain` cannot skolemize an existential already in context; use `dk-skolem!`.
* `mac-h`, `slot-h`, `ai`, `dk-split!`, `dk-skolem!`, `sep-me` REPLACE or CONSUME the
  formula they open. To read a projection off a hypothesis that is needed again, work
  inside a `have!` LANE. Get `d in RR`, `0 < d` from `POS-RR d` by CITATION
  (`rr-pos-rr-in-rr`, `rr-lt-of-pos-rr`), never by `mac-h 'pos-rr`. A `def-functor` typing
  axiom must be cited BEFORE `mac-h` unfolds the structure predicate it is guarded on.
* **A GUARDED macete: `mac` refuses, `mac-h` spawns** the side condition. Type the arguments
  BEFORE the `mac`. `mac-h` of a guarded read-off rewrites UNDER a `VNB-LAMBDA` binder and
  posts unclosable side conditions; orient the rewrite so only top-level terms are opened.
  A macete rewrites EVERY occurrence: normalize both sides with the same macete.
* **`lam-b` needs the argument TYPED, BEFORE the reduction**: otherwise it owes `(IN u A)`,
  and under a still-unpeeled binder the owed leaf is UNPROVABLE (posted in the outer
  context where the variable is free). PEEL AND TYPE FIRST, THEN BETA -- a rule about the
  drive LOOP, not one step. `lam-b` reduces every licensed redex, including under a SEP
  binder; where the summand is a non-variable lambda use a value lemma with variable heads
  (`enum-fam-value`, `lambda-compose-value`, `finsum-fiber-value`). `lam-b` reaches only the
  goal: a redex in a HYPOTHESIS wants `lam-b-h`. `lam-b` reduces a destructuring
  `(VNB-LAMBDA (LIST x_ y_) D b)` applied as `(f a b)`, not as `(f (LIST a b))`, once `a`
  and `b` are typed; a bound `nxt` applied as `(nxt k u)` may be instantiated at one.
* **`lam-t` opens TWO leaves**: the pointwise typing and the SETHOOD of the domain
  (`fun-domain-in-set`, `rr-is-set`, `rr-pos-star-is-set`). `dk-lam-t!` diffs leaves
  GLOBALLY and can close a sibling's node when conjuncts are open: prefer `dk-opened`.
* **A set, IOTA or lambda term the DRIVER builds must use binders that nothing else binds**
  (2026-09-19, met twice in one day): if its binder is spelled like an eigenvariable `di` will
  mint or like a binder of the statement or of a predicate body (`x_`, `y_`, `r_`), the
  capture-avoiding `subst-free` RENAMES it, and every later `equal?` lookup or `subst` of the
  rebuilt term matches nothing, silently; the one symptom is `symbol x_ is both bound and
  free`. Use names no predicate body uses (`tv_`, `pv_`, `cv_`).
* **Never unfold a lambda-bodied functoid (`SUBSEQ`) under a binder and then `lam-b`**: the
  redex under the unfolded binder owes `(IN (phi k) NN)` with `k` free, unprovable, and the
  failure surfaces at the enclosing `have!` as "THUNK left the side goal open". Rewrite by
  the VALUE equation at a typed index (`subseq-apply`). `lam-b` posts the argument typing as
  a LEAF even when the typing is already in context: close it, or the parent never grounds.
* **`lam-b` is ONE bottom-up pass and does not re-normalise its result** (read 2026-09-20): a redex
  that a contraction CREATES survives the call, and a redex whose owed typing would name a
  variable bound where it sits is left standing. Loop (`dk-lam-b!`), do not count. The checker's
  relation is reachability by contractions, each licensed where it sits or owed, created redexes
  included; `dk-lam-b!` / `dk-lam-b-h!` ERROR when the inference is refused or changes nothing
  (they used to return as if beta had closed the branch).
* `have!` returns the main NODE, not the claim: keep the formula yourself. **A driver form closed
  one paren SHORT swallows the following top-level forms as extra ARGUMENTS** of `have!`, which
  ignores them, and MIT evaluates arguments right to left: the LAST form of the file runs first
  and the error surfaces far from its cause.
* `if-true` / `if-false` do NOT rewrite the goal: they hand over the equation as an
  assumption, which then wants a `subst`. There is no hypothesis-side `subst`.
* **`subst` rewrites in operator position** (since 2026-09-16), takes `==` as `=`, and
  rewrites in the direction of its ARGUMENT, `s -> t` for `(subst '(= s t))`. The context may
  hold the equation in EITHER orientation and under either head (`pi-eq-subst!`,
  primitive-inferences.scm:557), so using an equation backwards is `(subst '(= t s))`, with
  no `eq-sym` (corrected 2026-09-19; the old reading "left to right only" cost workarounds).
  Substituting `w = [NTH 1 w, NTH 2 w]` rewrites `w` inside its own projections.
* `detach!` takes the IMPLIES formula, not its antecedent. `minimize!` lands its guard as
  ONE conjunction. `dk-split!` takes one conjunction, `dk-split-all!` a LIST of landings
  (with no argument it splits everything in context).
* **`cut` / `have!` of a formula already in context (up to alpha), or equal to the focus
  goal, is a silent self-loop** with no main branch. Guard with `alpha-equiv?`; a helper
  wants both a goal-closer form and a `have!` form. `use-em` on a decided proposition
  ERRORS; on a DISJUNCTIVE proposition it silently drops a branch (`use-em--on` lacks the
  length check) -- split on membership cases instead.
* **`prop`** decides propositional consequence with opaque atoms and adds no trust. In a deep
  context its atom cap drops the relevant pair and it declines with an EMPTY countermodel:
  `dk-only!` down to the relevant formulas first. It is not alpha-aware (`ass` is); it does
  not `ai` a context conjunction before NOT-elim. It does do the excluded-middle split.
* **`ineq`** is a TRUSTED oracle. Premise indices are 1-BASED; bare `(ineq)` passes ZERO
  premises; it certifies an atom only from a STANDALONE `(IN t RR)`; one uncertifiable
  premise (a set equation, `succ(n) = n + 1`, `q = a * recip(b)`) poisons the call and the
  message blames the goal -- name premises by FORMULA after `dk-only!`. It cannot prove a
  `NOT` goal. A missing cancellation (`c > 0, c*a <= c*b => a <= b`) is the opposite case
  of `rr-leq-total` plus one call. `contra` lifts NN typings to RR and filters premises.
  **It had NO eigenvariable check until 2026-09-20** (it peels the goal's `forall v in RR`; with
  `x <= 0` in context it closed `forall x in RR. x <= 0`, and FALSITY followed -- found by the
  independent rule checker): it now declines when a peeled variable is free in the context,
  certifies `abs(t)` only when `t`'s atoms are certified, and certifies atoms that cancel.
  It also DROPS, silently, a premise that is not linear (a product of two non-constant terms,
  `|c| * ||v||`), and then blames the goal (2026-09-19): chain such estimates by citation
  (`rr-mul-le-right`, `rr-leq-transitive`, `rr-le-add`); a product of two atoms both certified
  in RR is treated as ONE opaque atom, which is often enough.
* **`crs`** decides commutative-RING identities: do not use it on NN (no negation); it DOES
  reach a structure's `(ADD R)` / `(MUL R)` / `(NEG R)` once `IS-COMMUTATIVE-RING` of that
  structure (or of the view, `NORMED-FIELD-AS-COMMUTATIVE-RING K`) is in context (corrected
  2026-09-20; `nf-sub-add-back`), and it declines anything containing
  `recip` (prove the identity with the coefficient QUANTIFIED, instantiate after). `sos`
  has no `/` case: `mac 'binary-divide-def` first.
* `quietly` silences `vnb-guard` too, so an ERROR inside it becomes a silent no-op; a
  composite wants `show` quiet and the guard loud. A command that changes nothing prints
  `nothing changed ... The step was NOT recorded`; fixed-count `nth-r`/`lam-b` calls leave
  inert steps -- loop on a redex test.
* `backup-one` (`undo`) rolls back the deduction GRAPH (journalled writes); it does not
  restore `*fresh-counter*`.
* `else` is shadowed in the per-file environment: write `(#t ...)`.
* **`keep F ...` (2026-09-23) keeps only the named assumptions and drops the rest as ONE recorded
  step** (a page of Prop 3.2 had 676 `wk` lines from ten `dk-only!` calls in a 100-formula context;
  now 3 `keep` lines). Arguments are resolved to FORMULAS at call time (never recorded as indices);
  matching is up to alpha. `dk-only!` is `keep`. `wk` remains for one formula. The proof-tex gloss of
  `wk` used to say what `ass` does; corrected.

**Definedness (the LUTINS rule, since 2026-09-18).** `forall-elim` posts the side sequent
`t = t` unless the certificate `pi--defined?` accepts `t`: a variable or atomic constant, a
ground number, a term typed or equated in context or occurring outside binders in a true
`IN`/`=`/`<=`/`<` hypothesis, a class term on defined arguments, `VNB-LAMBDA`/SEP/BIG-UNION
over a certified domain, arithmetic on number-typed arguments, an accessor of a structure in
context (a structure predicate such as `IS-METRIC-SPACE(t)` in context certifies `t`; an `==` on one
of its accessors does not), an applied structure operation on typed arguments, `f(a)` with `f in FUN(D,_)` and
`a in D`. NEVER: CHOICE, IOTA, an untyped application, ENTRY without range typing, the
IOTA-bodied matrix constructors, FINSUM. So **TYPE THE TERM BEFORE YOU INSTANTIATE AT IT.**
A predicate hypothesis certifies what the conjuncts of its defining IFF
certify, but only for the PARAMETERS: a witness of a stripped `FORSOME` is a fresh symbol, and the
IFF must be definitional, primitive or proven (2026-09-20: `odd(n)` in context had certified `2 * k`
for the context's own `k`, and an asserted IFF certified with nothing billed).
`rfl` uses the same test and says so since 2026-09-18 ("not certified DEFINED"); a fold
about to be closed by `rfl` wants its `FINSUM = SUM-AG` equation landed. An owed leaf has
the SAME context as its parent, so a context-based focus helper may pick it first; a typing
landed inside a `have!` lane does not reach the main branch. Citing a typing "to be safe"
costs a bill entry. `dk-discharge-owed!` closes the tagged leaves when the typing is one
citation away. Policy: `docs/definedness-instantiation-2026-09-18.md`.

**Statements: the species of FALSE or underdetermined support found so far.** Check for them
before proving, report with a counterexample, prove the guarded form, stop:

* a dimension, index bound or `succ` argument left UNTYPED (`succ` off NN is uninterpreted);
* a strict `=` whose terms are untyped, asserting definedness (`finsum-congruence`,
  `sum-set-singleton`); state with `==`, or add the POINTWISE typing as an antecedent;
* a missing FINITENESS guard, false once CARD is defined (`interval-card-in-nn`,
  `card-insert`, the old SUM-SET axioms);
* CHOICE of a possibly empty class;
* `F(M, u)` for a ONE-parameter functoid is `F` at the PAIR, not `F(M)(u)`;
* **an under-guarded strict equation beside `(IN <constant> (FUN A B))`** proves FALSITY
  (the old `eplus` and `etimes` axioms): a member of `FUN(A,B)` is defined EXACTLY on `A`;
* a binder that folds onto a class name (see Case folding).

**Finite sums and sets.** Type summands POINTWISE (`forall z in S. f z in CARR`): a
pointwise typing restricts to a subset for free, so the missing RESTRICT never matters; a
FUN typing is needed only inside one helper, supplied by `(VNB-LAMBDA w_ U (f w_))` + `lam-t`
and transported by the untyped `finsum-congruence-q`. The bricks: `enum-fam-value`,
`sum-ag-type-ptwise`, `finsum-type-ptwise` and its comm-monoid twin, `finsum-in-subset`
(takes a CLASS: "the sum stays in P" is a citation), `finsum-insert-ptwise`,
`finsum-union-disjoint` (+ `-cm-`), `finsum-reindex(-ag)`, `finsum-reindex-inverse-ptwise`,
`finsum-fiber-slice`, `finsum-singleton-ptwise`, `card-bijection-eq`,
`card-insert-converse`, `remove-restore`. The comm-monoid mirror of an abelian-group finsum
law is five citation substitutions. Finite-set arguments: `finite-set-induction` with the
class relativised to subsets of a FIXED superset; the step ADDS a point, so no set surgery.
"Max over a finite family" is `nn-finite-subset-bounded` over an IMAGE. A family of subsets that
must be FINITE is carved out of `POWER(PTS s)`, which makes it a SET -- what `card-image-finite`
and `card-subset-nn` demand -- so the given cover never has to be one (`compact-subspace.scm`). "The least ordinal
such that P": bound by `ORD-SEGMENT(succ_ORD al0)` for a known witness, separate,
`ord-well-ordered` (no COMP anywhere in the tree).

**Structures and views.** THE SLOT KINDS of `declare-structure` (structures.scm) are `carrier`, `op`,
`constant`, `derived`, `substructure`, `family` (a set of subsets of a carrier: a sigma-algebra, a topology),
`family-fun` (a function on such a family: a measure) and `relation` (a set of pairs of points of a carrier:
SETOID's `REL`, since batch 40, 2026-09-28; a setoid is ONE carrier). Each kind has ONE typing conjunct in
`IS-X` and ONE arrow clause in the generated `IS-HOM-X` (preservation for an op, pullback for a family,
transport for a family-fun, "related points go to related points" for a relation); `hom-kinds.scm` proves the
category laws for the family and relation kinds, `hom-laws.scm` for the rest. A structure's default arrows
are the generated ones; a named alternative is a `declare-category!` with three PROVEN obligations (fatal
gate). Tightening a slot's typing breaks every proof that CONSTRUCTS an instance by hand (two in batch 40).
`slot` on a `def-functor` view has no per-slot projection: use
`(slot 'X) (mac 'THE-VIEW) (nth-r)`, iterate to a fixpoint when target and source accessor
are the same symbol, and ASSERT the goal literally before `qrfl`. Never fire an accessor or
instance-value macete by name (the suite pins `slot` as the one door; use `slot` twice when
an instance value and a projection are both needed). `slot-h` has no accessor fallback.
Two `def-functor` views with the same slot list are quasi-equal in four lines. `qrfl` is
alpha-aware. **Proving a fact that used to be an axiom moves it past the view specializer**:
its companions vanish (up to 121 per law); check who cites them, and rebuild with the
RESTRICTED `(view-as-auto-specialize! 'VIEW 'theorem)`.

**Files.** A proof file states its theorem LITERALLY (never `lookup-theorem` of the support
it replaces). A TACTIC that loads late (`contra`, `prep`, `ineq-supply`, after `suggest`) is
unavailable to an early file, and the band cannot tell you; nor can it tell you a
load-order error. One convenience lemma cited from a late file can cost sixty load slots.
A slice probed on the band is loaded into `(extend-top-level-environment *driver-kit-env*)`.
Run probe scripts with `< /dev/null`. Debugging recipe: `head -N` the file into scratchpad
and append a dump of the open leaves with a distinguishing context formula each.

**The kit is in driver-kit.scm; stop copying it**: `dk-peel!`, `dk-split-all!`, `dk-pick`,
`dk-only!`, `dk-apply!`, `dk-di-var!`, `dk-conj-close!`, `dk-skolem!`, `dk-halve!` (types
the half, not `eps`), `dk-have!` -- the `have!` that declines a claim already in context,
listed as owed for a week and in the file since 2026-09-14. **Added 2026-09-19 (batch 8),
each replacing three to five verbatim copies, each with a suite check:**
`dk-open-leaves` (the LEAVES among the ungrounded nodes; `proof-open-goals` is EVERY
ungrounded node and reading it as the work list has cost two agents a run);
`dk-ineq!` (`ineq` with the premises named by FORMULA, indices resolved at call time,
erroring on one that is not there -- `ineq-on!` is the same procedure's older name and
still works); `dk-le-chain!` with `dk-le-trans!`, `dk-le-add!`, `dk-eq-le!` and `dk-real!`
(the `<=` chain by CITATION, landing the typings and building `rr-leq-transitive`'s
conjunctive antecedent -- what `ineq` cannot do once a premise is a product; an `=` rung's
`subst` is oriented by CONTAINMENT, since the side that contains the other is the one that
has to be rewritten away); `dk-lam-b!` / `dk-lam-b-h!` (beta to a fixpoint, looping on a
REDEX TEST, closing the owed argument typings the context already holds and erroring when
two survive rather than focusing the wrong leaf); `dk-each-leaf!` (run a branching tactic,
visit each opened leaf, ERROR when it opened none); `have-f!` (`have!` returning the CLAIM
as the context holds it, not the node); `choose-mem!` (`choose!` that LEAVES the
membership `(IN (CHOICE S) S)` instead of consuming it). **Fixed the same day:** `in-sep!`
tolerates a subgoal that hash-consing had already grounded -- it used to error "no domain
subgoal", i.e. report the obligation's discharge as a failure -- and takes a one-thunk
form; and `push-not-h` goes through a NESTED universal. That refusal was mostly a
mis-model of `di`: the kernel peels every leading FORALL and, for the variable just
peeled, an `(IN x _)` guard with it, and nothing else, so a PREDICATE guard stops it and
`NOT forall(eps, POS-RR(eps) => forall(m in nn, ...))` -- the shape of every negated
definition in analysis -- was being refused for nothing. The genuinely deep case (an
`(IN x _)` guard over a further universal, which `di` does peel past) is now proved by
assuming the inner universal on its own lane, instantiating it at the eigenvariables `di`
minted -- read off the goal by matching, never guessed -- and contradicting.
**Added 2026-09-20 (batch 11-D):** `dk-close-if!` -- run a thunk on the focus leaf, run the
CLOSER only if that leaf is still open AND still the focus, return whether it is grounded.
This is the cure for FOCUS DRIFT: a tactic that rewrites, weakens or simply closes its leaf
moves the focus to a SIBLING, and the driver's next `(ass)` -- written as the closer for the
leaf just worked on -- fires on the sibling, silently (reproduced in the suite as a control:
`rfl` on the first conjunct, then a bare `ass`, closes the second). Also `dk-close-all!`
(run a branching tactic and `ass` every leaf it opened), `dk-iff!` (split an IFF and drive
both directions, discriminated on the GOAL, erroring when the discriminator picks both or
neither), and `dk-head` / `dk-head-is?` / `dk-goal-head?` -- head tests that tolerate an
ATOM, which `(car (caddr goal))` does not (EMPTY-SET is an atom; `bu-mi` opens a leaf whose
class is a bare variable).
**Added 2026-09-20 (batch 13-D), each with a control that fails on the old code:**
`dk-project!` (open a hypothesis -- `mac-h`, `sep-me`, `ai` -- inside a `dk-have!` LANE and land
the projection, so the hypothesis SURVIVES: three batch-12 agents lost a guard to `mac-h` and
then a `fact` landed its implication silently); `dk-pos-parts!` (`e in RR`, `0 <= e`, `0 /= e`
AND keeps `0 < e` and `POS-RR e`: the five copies of `rko-pos-parts!` destroy the strict atom;
a file adopting it must `dk-have!` the same conjunction, since `have!` reports a hash-consed
side node as `no side goal`); `dk-read-off!` (a GUARDED value equation onto the goal: `fact`
the instance, `subst` the equation THAT LANDED); `detach-with!` (the conjunctive antecedent
read off the instantiation chain, proved on a lane, detached); `dk-close-all!` tolerates
leaves hash-consing already grounded; `(dk-ineq!)` with no premise is bare `(ineq)`; and
**`have!` ERRORS on a third argument or a second one that is not a procedure**. The kit's
header now carries the rule: CAPTURE THE FORMULA WHEN IT LANDS, AND CITE BEFORE YOU DESTROY.
**Added 2026-09-24 (batch 27-B, the kit pass: 15 items, 50 suite checks, 15 of them controls
that fail on the old code; the local copies each replaces are listed per item in
`scratchpad/triage/BATCH27-REPORTS.md` for the retirement pass):** `dk-fun-ext!` (function
extensionality at the point of use, the pointwise universal proved under a fresh binder occurring
in NEITHER side, since the `x` of `fun-domain-extensionality` is captured by every polynomial term);
`dk-crs-opaque!` (`crs` with `recip` and binder-holding subterms quantified over RR, proved on a
lane, instantiated back); `dk-nn!` (NN linear arithmetic by lifting: finds the NN atoms and `succ`
terms itself, then `dk-ineq!`); `dk-chain!` (run an implication chain, detaching what is in
context and proving the rest from `(PRED . THUNK)` provers; tolerates a chain `fact` already
detached to its consequent, where `detach-with!` errors); `dk-lane` / `dk-lane-open?` /
`dk-lane-if!` (a lane remembers the leaf it started on and closers are guarded by THAT leaf: the
cure for focus drift inside `have!` thunks); `dk-lam-type!` (the `lam-t` typing loop on the leaves
THIS `lam-t` opened, not a global leaf diff: the repair of `dk-lam-t!`'s known defect, which is
left as it was for its callers); `dk-absurd!` (FALSITY from contradictory linear premises via
`0 < 0` and `rr-lt-irrefl`, since `ineq` declines a FALSITY goal); `dk-abstract!` (skolemise a
lambda family into a function symbol with its value equation); `dk-name!` (2026-09-28, batch 40: name a
typed term as a fresh symbol, landing `v in C` and `v = t` and returning `v`, the cure for `ineq` dropping a
compound product; the term must be TYPED in context first, else it errors with the reason); `dk-have!` of a claim EQUAL TO THE
FOCUS GOAL now proves it in place instead of dying with `cut left no main branch`; `dk-cite!`
(`dk-fact!` that returns the instance whether it lands or is already in context; `dk-fact!` stays
strict); `dk-congr!` (f(a) = f(b) from a = b where `subst` cannot be used because one side contains
the other: the kernel has no congruence rule for `=`); `dk-lam-b!` and `dk-lam-b-h!` RETURN whether
the leaf they started on is grounded (no call site used the old values); `iff-for`;
`dk-if-branch!` / `dk-case-if!` (the IF-tower resolver). FIXED the same day: `from-context!` tries
`ass` before `arith` on `(IN <numeral> C)`; `use-em` ERRORS on a disjunctive proposition (the old
code ran two bodies on a three-way split and left a branch undriven); `dk-skolem!` takes a split
argument (`#t` / `'top` / `#f`). NOT A DEFECT: `fact`'s auto-detach IS alpha-aware (`asms-find`,
`alpha-equiv?`), pinned by an accepted / refused pair; the 26-B miss was a clause differing beyond
a binder rename. Also `case-fold-local-lint!` (clobber-guard.scm): `let` / `let*` / `lambda` names
within one form differing only by case, warn-only, ~20 s per load; backlog 2 on the day it was
added (`dd-diff-typ!` in directional-derivative.scm, a latent bug -- the lambda's `x` IS the
parameter `X`, so its "already in context" test never matches; `r5u-ff-step!` in
rake-combinatorics2.scm, harmless).
STILL OWED: a helper closing a structure predicate's TYPING conjunct from a property already proven
(batch 40, finding 3); the view slot read-off (`slot-close!` / `readoff!` / `dk-read-off!`), `dk-finite!`,
`dk-least-ordinal!`, a hypothesis-side rewrite, the quotient-of-a-structure driver (`rep!` /
`compute-down!` / `close!`), and the retirement of the local copies the 27-B report lists. KNOWN
DEFECTS not yet fixed: `arith` raising on the ground goal `2 = 2` (did not reproduce on the band,
2026-09-24; interactive.scm); `dk-lam-t!` (global leaf diff: superseded by `dk-lam-type!`, kept
for its callers). (`dk-only!` grounding the focus leaf: FIXED 2026-09-23 -- `dk-only!` is now the
surface command `keep`, ONE recorded step, which stops when the weakened sequent lands on an
already-proven node and errors on any other drift.)

**The preamble (batch 41, 2026-09-28; `docs/preambles-2026-09-28.md`).** `(preamble)` applies an EDITABLE RULE FILE
(`preambles/default.pre`, or `~/.vnb-preamble.pre`) to the focus leaf: `(rule NAME (goal P) (with P)* (guard ..)*
(do FORM) [(probe ..)] [(side ..)])`, raw-S-expression patterns with `?x` schema variables, each firing tried on a
scratch copy and kept only on progress, recorded AS ITSELF (the page needs no rule file). The report names what
fired, what was rejected and why, the OWED claims of a tentative cut, and where it stopped. `(preamble '(induct)
...)` with a clause list is the older strategy pipeline (`preamble-clauses`). `(type-term)` types `t in C` for ANY
class the planner has a route for (closure laws in a number class, an application `f(a)` from `f in FUN(A, C)`,
an inclusion); it declines with nothing changed when there is no plan. Trap met 2026-09-28: the tree's `any`
(sequents.scm) returns `#t`, not the value found.

**Open foundational items.** The tree cannot form a SEP over triples (CARTESIAN is binary;
no literal-LIST TUPLES read-off; no tuple extensionality), which blocks the injection
recurrences (a triple that is only a TERM inside a SEP condition is free).
Recursive choice is PROVEN: `dc-on-nn-pred` by `DC-ITER`, a PARAMETRIC
`def-by-nn-recursion` with a CHOICE step; `rake-dc-on-nn.scm` is the model for "build a
sequence by repeated choices". IOTA has `iota-d` and `iota-e`;
`rake-esup-defined.scm` models an IOTA-defined operator. No citable beta; no SEP congruence rule; no general `converges-implies-cauchy`.

History (every batch report, measurement and incident behind these rules):
`docs/history/claude-md-2026-09-18--writing-proof-drivers.md`.

## Script replay and the page

**The proof is the GRAPH.** `qed` refuses to install unless every node is grounded. The
SCRIPT is a recording of the surface commands -- the input, not the output -- and several
recorded arguments are indices into ephemeral state, so replay fidelity is ENGINEERED.
`proof-tex` prints from `*proof-live-trace*`, snapshotted as the proof ran.

**THE STANDARD (the user's, 2026-09-06): every proof must have a re-runnable script.**
`(report-page-audit)` is a load-time gate: it emits each stored proof as a PAGE
(`script--write-block`), types the text back in, and demands `grounded`. It has read
`all N proof(s)` since 2026-09-15 and costs about 45% of the load. The page NAMES each
minted eigenvariable once, by provenance (`(name-witness! 3 'w1)`), and never carries a
counter-minted literal or a number about the machine that printed it.

The rules that keep a page re-runnable:

* a recorded argument shape must match `apply-recorded-cmd!` (`fact` records its terms FLAT);
* a surface command that records ITSELF needs a case in `apply-recorded-cmd!`;
* one `*proof-mints*` entry per RECORDED step (the capture is in `record-cmd!`);
* a driver helper that moves focus goes through `dk-focus!`; a helper drives the SURFACE
  tactic, never `pi-*!` or `cmd-*` (only `vnb--run!` records). The grep checks:
  `set-proof-state-focus!` outside driver-kit.scm and `focus-on *ps*` outside the kernel
  must be empty;
* a probe (`what-now`, `scout`) binds `*replaying?*` as well as `*ps*` (`vnb--probing`);
* a positional reference is only as good as the execution that resolved it: compute it in
  the run that will use it (the index pass was built and reverted for this reason).

**The ledger reads citations off the script, and `bc*` handlers run with recording
suppressed**: since 2026-09-18 the steps taken inside a handler are kept in
`*proof-hidden-citations*` for `record-proof-debt!` alone (one bill had been wrong).

History: `docs/history/claude-md-2026-09-18--script-replay.md`.

## Where a driver helper lives

**Every proof-driving Scheme procedure is either in `driver-kit.scm` -- loaded before any
proof -- or is local to the file that defines it.** There is no third place.

`load.scm` enforces the second half: once `driver-kit` has loaded, each `theorem-library/`
and `calculus/` file is loaded into a fresh `extend-top-level-environment`. A driver's
top-level `define`s stay in its own frame; its `set!` of `*ps*` still reaches the real
binding, and it still sees every tactic, every macro (`bc*`) and everything `driver-kit`
defines. If exactly one file needs a helper, define it there with the file's prefix. If two
do, it belongs in `driver-kit.scm`.

History: `docs/history/claude-md-2026-09-18--where-a-driver-helper-lives.md`.

## Layout

    structure-library/   definitions, structures, vocabulary, warranted supports
    theorem-library/     proofs that reach (qed ...); loaded, gated, counted
    calculus/            probes and stress tests; MOSTLY not in load.scm (three files are)
    reference/           MIXED.  Most of it is GENERATED at load (PSS.md, THEOREMS.md,
                         DEFINITIONS.md, PROOF-DEBT.md, DEBT-BUNDLE.md, TACTICS.md, ...):
                         never hand-edit.  HAND-WRITTEN: LIBRARY.md, KERNEL.md,
                         KERNEL-RULES.md, REVIEW.md, USABILITY-REVIEW.md, VNB-TEST.md.
                         KERNEL-MAP.md is GENERATED from reference/kernel-map-{static,dynamic}.sexp
                         (kernel-map-static.scm / kernel-map-trace.scm, then scratchpad/km/gen-kernel-map.py).
                         A .md absent from build-reference-html.py's DOCS list is
                         reachable from nowhere.
    docs/                design notes, the manual; docs/history/ holds the case histories
    archive/             retired and spliced originals, by date
    scratchpad/          throwaway drivers and the triage briefs (untracked); also scratch/

**A file with no proof in it belongs in `structure-library/`** (2026-09-20): seventeen
vocabulary files (CCINT, SUBSEQ, the series and Ascoli predicates, CLOSURE / INTERIOR, ...) sat in
`theorem-library/` and pinned a load floor under every theorem stated with them; they were moved,
and `IS-DIFF-AT` / `DERIV`, `IS-ANTIDERIVATIVE`, `NVS-METRIC-SPACE`, `DIFFERENCE` / `SINGLETON`
and `NN-MINUS` were extracted from proof files into definition files of their own (the last three
had been used, uninterpreted, by structure-library files that loaded BEFORE their definitions).
A definition moves with its `notation!` and without any proof.

**Load order matters.** A file using `sp`/`qed`/`make-wff` must come after `interactive`
and `proof-debt`. **A `.scm` that load.scm does not name is invisible, and no gate counts
files**: two proof files sat unloaded for weeks while the fact they proved went on being
asserted. If you write a proof file, the entry in load.scm is half the work.

History: `docs/history/claude-md-2026-09-18--layout.md`.

## Library-build policy

New mathematical facts are added as **warranted supports** (`support` + `warrant!`), not as
kernel axioms. A `qed` prints its bill: `proven modulo {...} [trust: ...]`, the asserted
facts it leans on. `modulo 0` is the strongest thing a `qed` can say.

**Trust tiers**, worst to best: `none hand-wave well-known reference informal proof`. A bill
reports its WORST leaf. `trust: none` means some leaf has no `warrant!` at all. `informal`
(a rigorous paper proof exists) outranks `reference` and `well-known`.

**Provenance.** `primitive` and `definitional` both contribute {} to every bill;
`asserted` is debt; `proven` inherits its citations' debt.

* **The primitive shelf grows only by an explicit foundational decision of the user**, one
  fact at a time, recorded in the file: the ordinal axioms, `app-graph`, `image-set`, the
  arithmetic base (`number-systems.scm`), and `pos-inf-above-reals` (2026-09-18). A
  `warrant!` is a better tier of DEBT; `primitive` says it is not debt at all.
* **A stamp must record its claim**, and a `definitional` stamp is not free: it makes the
  fact invisible to the ledger. `nn-add-succ` carries such a note. **The scar
  (2026-09-18): the five `etimes` case equations were stamped `definitional` as "a
  definition by cases of a fresh symbol"; one of them was FALSE, the axiom set proved
  FALSITY, and no bill could show it.** Prefer, in this order: DEFINE the object and PROVE
  its laws; PROVE the fact from what exists; only then a stamp, by the user's decision.
  `nn-mul-succ` was left unstamped and turned out provable; SUM-SET, EPLUS, ETIMES and
  RR-BOUNDED-MS were axiomatised and are now defined.
* Shape projections (the conjuncts of an IS-X iff) are PROVEN by unfolding
  (`stl--project!`), not asserted; a comment that says "a conjunct of ..., surfaced as a
  citable theorem" is a proof written in prose and not run.
* **Three territories of debt**: the leaves on bills (`DEBT-BUNDLE.md` s.1-2), the PSS
  entries on no bill (s.3), and asserted names with NO warrant (s.4, generated since
  2026-09-19; 43 names).
  Supports proven elsewhere, stale "blocked" notes and warrants that blame `crs` are
  common: re-read a header that names a blocker by theorem name before believing it.

**Triage by BILL, not by citation count.** A leaf buys nothing until it is the LAST
unproven leaf of the bills that name it; shadowing has bitten five times. `debt-greedy-order`
and `debt-entry-routes` (proof-debt.scm) write the ranking and the arcs into
`reference/DEBT-BUNDLE.md` at every load. For an independent win, rank by the number of
bills in which a leaf is the SOLE remaining one.

**CARD is DEFINED** (2026-09-20, the user's decision; `docs/card-defined-2026-09-20.md`):
`CARD(A)` is the `def-functoid` of `structure-library/cardinality.scm` -- the least ordinal
whose segment `A` bijects onto, A-first. The symbol `CARD-STAR` is gone. The EIGHT facts
that stood on the primitive shelf -- seven in `cardinality.scm` plus `card-image-injection`
in `injection.scm` -- are THEOREMS under their old names and in their old SHAPES, so no
citation changed: `card-segment` (`card-defined.scm`), `card-empty` (`card-finite.scm`),
`finite-set-induction` (`rake-card-star-laws.scm`), and `card-in-ord`, `card-insert`,
`card-finite-bij`, `card-union-disjoint`, `card-image-injection` (`card-laws.scm`, which
restates each from the CURRIED form the CARD development proved). `well-ordering-principle`
is likewise proven (`rake-ord-pigeonhole.scm`) and is no longer a PSS entry. `card-insert`,
`card-union-disjoint` and `finite-set-induction` carry a FINITENESS guard and need it:
`CARD(omega u {omega}) = omega`, not `omega + 1`. Pigeonhole for ORDINAL segments is false
(omega + 1 injects into omega); the finite form is proven. **The load order paid for this**:
nineteen files (the CARD-free citation cone of the development) moved up to a single block
just after `transport`, and three files had to be SPLIT (`finsum-insert` ->
`enum-append.scm`, `fin-subsets` -> `union-laws.scm`, `rake-inverse-bij` ->
`rake-fin-enum.scm`), because each held both a theorem the cone needs and a theorem that
rests on a CARD law.

**Arithmetic facts worth knowing.** Binary `-` and `/` are DEFINED (`binary-minus-def`,
`binary-divide-def`; both are LIVE macetes fired BY NAME -- the `declare-named-only!` beside
each came AFTER the install and was a silent no-op, deleted 2026-09-20, and nothing needs it:
a constant head like `-` or `/` reaches differences and quotients only, unlike `app-graph`'s
bare `(f x)`. `declare-named-only!` must PRECEDE the install and now warns when it does not).
Numeric literals are exact rationals. The archimedean
property is derivable. The `nary-*-3/4/5` forms are deliberately asserted (they fix the
reading of the parser's flat n-ary node). `sqrt-unique` is the general nonneg-square
cancellation. Start real-sequence limits from `rr-converges-to-abs`.

When a proof turns into a grind, that is a finding, not a failure: record the obstacle and
the lemma that would dissolve it. Do not slog. Before adding a support, ask whether it is an
*instance* of something a tactic could do (`minimize!`, `prop`, `contra` are the worked
examples; none adds trust).

History (the five shelf decisions with their measurements, the `trust: none` countdown, the
rake's batches, the continuity algebra, `prop` / `contra` / `minimize!`):
`docs/history/claude-md-2026-09-18--library-build-policy.md`.

## The gates on the install door

`support` and `add-axiom!` install a raw S-expression. The end of `load.scm` runs
the gates; each catches a defect the others call well-formed.

* `qed-failure gate` (2026-09-20) -- FATAL in a strict load. A `qed` that fails inside a proof file
  prints one line and RETURNS; when no later file cites the theorem nothing stopped, and a strict
  load exited 0 with a theorem missing. `qed` records every failure in `*vnb-qed-failures*`; the
  end of the load lists them. Under keep-going an incomplete proof is a HOLE and prints as one.
* `connective-arity-audit` -- FATAL. A flat `(AND a b c)` silently drops conjuncts.
* `free-variable-audit` -- warn-only.
* `head-registry-sweep` -- warn-only. Every applied head against `*constant-registry*`, the
  table `free-vars` / `subst-free` consult. A new TERM constructor goes in
  `*wff-term-form-heads*`; a PREDICATE gets a bare `register-constant!`.
* `install-grading` -- warn-only, at install time; grades SHAPE only.
* `sethood-audit`; `report-page-audit` (above); `install-duplicate-audit` (names installed
  twice; keep it at zero -- a proof moved between files must be CUT from the old one).
* `asserted-duplicate-audit` (2026-09-19) -- warn-only: an ASSERTED statement alpha-equivalent
  to a settled one under another name (one `fact` from a proof).
* `proven-duplicate-audit` (2026-09-20) -- warn-only: two or more PROVEN names with
  alpha-equivalent statements (system-minted `-rev` and view companions excepted). Backlog on
  the day it was added: 25 groups. Keep one name, rename the others away with `rename-sym.py`.
* `constant-binder-audit` -- FATAL, deliberately loud: a binder named like a registered
  constant or a class name. `functoid-binder-audit` for functoid bodies.
* **`dg-apply-rule!` CHECKS every inference since 2026-09-20** (the user's decision): one
  CHECKER per kernel operation (`rule-checkers-{logic,schema,rewrite,oracle}.scm`, 66, none on
  trust) verifies the finished inference as a relation between conclusion and hypotheses,
  written independently of the `pi-*` builder; no checker or a refusal is an ERROR and nothing
  is written. A refusal prints even inside `quietly`; the load ends with `;; inference
  checking: N verified, M refusal(s)` and a strict load errors when M > 0.
  `VNB_NO_RULE_CHECK=1` is the A/B control (+30% load time with checking). A NEW kernel
  operation needs its checker AND its two suite controls (accepted / refused). Where the
  builder NORMALISES a term (beta), the checker's relation is stated on the normalised term.
  The macete record is `(macete NAME L R)`; `ineq` and `sos` record their certificates.
  Design note: `docs/rule-checkers-2026-09-20.md`.
* `kernel-callers-audit` -- FATAL. The code that may CALL `dg-apply-rule!` is a closed list: `*kernel-caller-files*` (8 files). Enlarging it is a
  deliberate entry, on the one-decision-per-fact discipline.
* `accessor-callsite-audit` (suite): no file fires an accessor macete by name.

A gate that passes everything reads exactly like a clean library: make it fail on purpose
before believing it (`scratchpad/gate-control.scm`). A gate goes fatal once its backlog is zero.

**Standing facts from gate work.** `COMP` is in all the expression walkers since 2026-08-15
(no installed formula contains one). **Nullary application is an error except `list()` and
`set_of()`**, at both doors; `set_of(l)` is `{l}`, the set of entries is `make-set(l)`.
**A printed term must re-parse to the term that was printed**: the printer brackets nested
same-head children and the reader no longer splices a parenthesised left operand; the
residue is the literal `-1`, which re-reads as `(- 1)`. Constants are never spelled with
operator characters (`ORD-LE`, `RR-STAR`, `CARD-STAR`, ...): `card*(a)` parses as a PRODUCT.

History: `docs/history/claude-md-2026-09-18--install-gates.md`.

## Shipping

`~/prover-src.tar.gz` is rebuilt by a Stop hook (`~/.claude/settings.json`): gzipped tar
of `prover/`, no `.git`, no `.com`/`.bin`/`.ext`. That is what "the tarball" means.
