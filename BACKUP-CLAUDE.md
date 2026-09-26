# VNB proof checker -- working brief

VNB is a proof checker and more generally a math assistant to help
users discover proofs. It is written in MIT Scheme with a user interface in
GNU/Emacs. Much of the documentation is available using a web
interface. There is also a manual which needs periodic update.  The
logical framework is von Neumann-Bernays set theory but with copious
ready-made constructors. Its research state (what is proven, what is
next) lives in Claude's memory index, not here. This file holds the
operational facts that are expensive to rediscover.

## Where the project is going

The **prove-theorem stage is done** (2026-07-11): `spans-submodule-fg` -- and with it
`submodule-fg` -- is proven. Its purpose was never the theorems themselves: it was to
exercise and stress the machinery, and it delivered, right at the end, the
simultaneous-substitution bug in the macete rewriter (below).

**Until 2026-09-16 this paragraph said "proven, with no asserted step". That was false
in two ways.** (1) The bill was never empty: on 2026-09-16 it named 32 asserted leaves,
all `well-known`. (2) One of them was unsound. `matof-exists`, an asserted support with
unquantified dimensions, proved FALSITY once instantiated at m := ORD (`mat-rows-in-nn`
reads `ORD in NN` off the matrix; burali-forti refutes it; probe
`scratchpad/mx/mx-probe3.scm`). And the n = 0 base case read the empty linear
combination as the (1,1) entry of a 1-by-0 product, `NTH(1, [])`, an unspecified value,
because a matrix with no rows had no determinate size.

Repaired 2026-09-16 (the user's decisions):
* `SIZE` is total, and `[]` is the unique 0-by-n matrix for each natural n; membership
  in `MAT` does not determine the column count of a matrix with no rows
  (structure-library/matrix.scm, header).
* The linear combination is `LINCOMB`, a FINSUM over [1,n], so the empty combination is
  VZERO by construction (structure-library/mod-seq.scm).
* A product whose middle dimension is 0 reads its column count off `[]`, so the product
  laws carry guards: entry laws `1 <= n`; typing laws `n = 0 => (m = 0 or k = 0)`;
  associativity the two-dimension pair G1/G2
  (docs/size-mat-surgery-2026-09-16.md, the design note; the repair specification the
  agents worked from is scratchpad/surgery/SPEC.md).
* `matof-exists`, `entry-of-matof` and `matof-in-mat` are THEOREMS guarded on
  `m, n in NN`. About thirty further matrix supports that assumed a natural dimension or
  a ring without saying so were guarded, and twenty of them proven.

After the repair, `spans-fg-base` bills `modulo 0`, and `submodule-fg` bills 16 leaves,
all `well-known`. Five of them are matrix typing supports (`block-type`, `matadd-type`,
`matscale-type`, `snoc-col-type`, `snoc-row-type`); the audit found all five true at
every dimension under the new definitions. The controls `mx-probe1`,
`mx-probe3` and `mx-probe4` no longer close. The lesson is the one the bill ledger exists
for: an assertion that was harmless when written became unsound when a lemma proved much
later, for an unrelated reason, met it; and "no asserted step" was a claim that nobody
re-checked against the bill.

Then the project **refocuses**, onto three things:

1. **Print proofs and read proofs.** `proof-tex` (full trace) and `proof-reader` (sketch)
   exist and are faithful, but they report the *official* level -- three lemma citations --
   where a human wants the *content* level: "Since `a` is a Euclidean ring, `a` is a ring."
   The table is BUILT (`operators.scm`, the ONE table keyed by head symbol; populated by
   `def-predicate` / `def-functoid` at definition time via `register-operator!`, and the
   reading declared next to the definition with `notation!`). It is read by `wff-english`
   (`operator-ref` / `operator-english`), `describe-structure` and `OPERATORS.md`.
   `expr->tex` reads it too, and the old entry here -- "expr->tex does NOT read it" --
   was half wrong: the hook (`operator-render-tex`, tex-output.scm) had been in the
   `expr->tex` cond all along, but BELOW tex-output's own binop/special tables and,
   more to the point, **no head in the tree declared a `tex` template** (195 `notation!`
   calls, 0 with a `'tex` key), so it never fired. Fixed 2026-08-10: the branch now sits
   ABOVE the two built-in tables (a declaration beats a default) and BELOW the
   arithmetic-prefix branch (a fluid MODE beats a declaration), and `==` declares
   `($1 \simeq $2)` -- the manual's own reading -- instead of falling through to
   `\operatorname{==}(...)`. `abs` got the CARD treatment (`\lvert x \rvert`) in
   tex-output's special table, where it belongs: it is a primitive with no operator entry.
   STILL OUTSTANDING on the reader: collapse a run of subtype-subsumption
   citations (`register-definitional-structure!` already records the parent chain); capture
   the goal BEFORE each step, not only after, so the reader can always name an existential's
   bound variable (see the `proof-reader--goal-before` comment); render `IS-EUCLIDEAN-RING(a)`
   as "a is a Euclidean ring".

**Where a definition lives, and the trap under it.** `def-predicate` / `def-constant`
install a THEOREM (the defining iff), so they land in `theory-definitions` and hence in
`reference/DEFINITIONS.md`. `def-functoid` installs only a rewrite MACETE -- no theorem --
so a functoid is in neither that registry nor `*theorem-table*`. Two consequences, and they
are the same fact seen from two sides:

* `mac` unfolds a functoid in a GOAL; **`mac-h` cannot unfold one in an ASSUMPTION by the
  functoid's own name.** It warns `unknown theorem/macete` and the driver continues with
  the hypothesis untouched. A constructor whose members get read out of the context
  therefore needs a membership `iff` beside it (`span-membership`,
  `principal-ideal-membership`, `zz-bezout-set-membership`, ...). That iff is a
  CONSEQUENCE of the definition -- the functoid unfold composed with the SEP separation
  schema -- not the definition.

  **But it does NOT have to be ASSERTED, and this entry said for weeks that it did.**
  The unfold equation is PROVABLE, one line per functoid, and the proof is `modulo 0`:

      (sp (make-wff '(FORALL a_ (FORALL m_ (== (FINSUPP a_ m_) (SEP f_ ...))))))
      (di) (mac 'FINSUPP) (qrfl)

  `mac` unfolds the functoid in the GOAL -- which is the half that works -- and `qrfl`
  closes the resulting `X == X`. The result is a THEOREM, and `mac-h` rebuilds its rule
  from the theorem table, so `(mac-h 'finsupp-unfold h)` rewrites the hypothesis into a
  literal SEP membership that `sep-me` reads apart. Demonstrated side by side in
  `scratchpad/pl-probe2.scm` (2026-08-20): `(mac-h 'FINSUPP 1)` warns and no-ops;
  `(mac-h 'finsupp-unfold 1)` rewrites, then `(sep-me)` `(ass)` closes. Seven such
  theorems for SUPP/FINSUPP/POLY are in `theorem-library/poly-membership.scm`, all
  `modulo 0`. `interval-basics.scm` and `mat-basics.scm` already did this the long way,
  via `have!` + `subst`; the `mac-h` route is one step and works in place.

  So every `definitional`-stamped constructor membership law in the tree is a candidate
  for PROOF instead of a stamp. NOT DONE for the existing ones: re-tiering moves every
  citing bill, so it is a separate measurement (triage by BILL).
* Until 2026-08-10 **DEFINITIONS.md carried no functoid at all**; all 113 were only in
  `FUNCTORS.md`. Looking up `zz-bezout-set` there found only its membership law, which
  reads exactly like a definition and is not one. `write-definitions-md` now emits an
  "Unfold-only constructors (functoids)" section from `*functoid-registry*`, filtered by
  `lookup-view-as` as FUNCTORS.md filters it, so the counts cannot drift (113 in both).

And a name-shape trap worth stating once: `zz-bezout` is a THEOREM; the thing defined is
`ZZ-BEZOUT-SET`. Searching the definition index for a theorem's name lands you on whatever
shares its prefix.

2. **A large database of theorems without proofs**, suitable as raw material for building new
   proofs. Statements, indexed and searchable; the PSS is the seed.

3. Revisiting the manual against all of it.

Do not treat "prove one more theorem" as the goal. The deliverable of a proof request is
usually the obstacles it exposes.

## Running it

    ./prover                  # interactive REPL
    ./prover file.scm         # load a proof script, exit
    ./prover -i file.scm      # load a script, then drop into the REPL
    ./VNB                     # launcher (cold boot re-proves the library: 24 s compiled)
    ./VNB-with-compile        # recompile sources, then launch

Full check suite (distinct from the launcher):

    timeout 900 mit-scheme --quiet --load test-suite.scm < /dev/null

It prints `=== SUMMARY: N passed, M failed ===`.

**Since 2026-09-15 the suite needs an explicit heap.** With 1243 proofs (monalg-is-ring.scm's
forty theorems were the straw) the library load inside the suite dies with
`;Aborting!: out of memory` under MIT's default heap -- no SUMMARY, exit 0, the silent
signature below, but this time for a reason a `--heap` fixes:

    timeout 4000 mit-scheme --heap 200000 --quiet --load test-suite.scm < /dev/null

With that heap it runs in **8m53s** on a t3.medium (1202/0); under the default heap the
same suite took 26-34 minutes before it started dying -- the slowdown WAS the heap, GC
thrash, and the tally in this file that put the suite at 6 minutes was measured at 1031
proofs. An SSM run timeout under the run's length cuts it off before the summary line.

The suite is SCHEME only, and that left the whole Emacs surface unchecked. The
panel check covers the other half:

    emacs --batch -l emacs/vnb-panel-check.el      # ~30 s, prints
                                                   # === PANEL CHECK: N passed, M failed ===

It starts a real prover off the band, begins a real proof, drives `di`/`ass`,
and inspects the panel Emacs actually painted -- one Keys block, the goal
shown, every advertised key bound, no line past 79 columns, the hover table
fetched. **Reach for it after ANY edit to `emacs/vnb-launch.el`.** Its reason
for existing is the 2026-09-13 defect below: the painter re-entered itself
through a prover round trip and every piece of it was correct in isolation, so
nothing short of driving the real pipeline could see it. Same rule as the
suite: exit status means nothing, look for the summary line -- the pre-fix
control dies at `max-lisp-eval-depth` and never prints one.

**Keep-going load (2026-09-16): `VNB_KEEP_GOING=1 ./prover ...`.** A cold load normally
stops at the first proof file that errors. With the variable set, an error in a
theorem-library/ or calculus/ file is recorded and the load continues; the failures are
listed at the end, in load order. One load then enumerates a whole ripple instead of one
failure per load. The list is a cascade, so read its first entries first. A band built this
way has holes and the load says so; use it only for repair work, never as the band. An
error in an engine or structure-library file still stops the load.

**RUN IT ALONE, and check for that line -- exit 0 does not mean it ran.** (Until
2026-09-15 the command here carried no `--heap`, and the suite ran on MIT's default heap;
the 33-minute runs and the silent deaths below were measured on it. `vnb-suite` runs the
`--heap 200000` form on a worker.)
Started alongside a `./prover` process (2026-08-10) it died partway through the library
load, ran zero checks, printed no `SUMMARY`, no `;Aborting!`, nothing on stderr, and
**exited 0** -- indistinguishable from a clean run except that the log stops early and
always at the same place. A `./prover script.scm` sharing the box failed the same silent
way. Under contention it also gets much slower (>20 min against the usual ~6) before it
dies, so a suite that is dragging is already the warning.

**It is not only contention** (2026-08-18). The same silent death -- 786 lines, stopping
mid-library-load, no `SUMMARY`, no `;Aborting!`, nothing on stderr, exit 0 -- happened
with `pgrep -x mit-scheme` reporting ZERO other processes beforehand. The one difference
from the clean run was the launch: `nohup ... &` in the background rather than in the
foreground. Re-run in the FOREGROUND, alone, it was 905/0 in 5m14s. So the rule stands
and gets one clause: run it alone, in the FOREGROUND, and check for the SUMMARY line.

## COMPILE THE TREE FIRST -- everything below depends on it

`.com`/`.bin` are in `.gitignore` AND excluded from the tarball, so a fresh clone or
unpacked tarball is **interpreted**, and nothing tells you. Compiled vs interpreted, on
this box:

    library load     24 s   vs  ~11 min
    full test suite   6 min vs  ~42 min

Compile once, after a clone/unpack (~10 min, includes one source load):

    ./VNB-with-compile          # or, from a REPL that has loaded load.scm:
    (compile-vnb!)              # incremental: skips files whose .com is fresh
    (recompile-vnb!)            # source-load everything, then compile

If you are ever tempted to conclude "this box is slow", check `ls *.com` first.
`compile-vnb!` skips `*vnb-no-compile-files*` (`test-suite`, `driver-kit`,
`clobber-guard`: the latter two capture `(the-environment)`, which compiles WITHOUT
COMPLAINT and then reports the wrong frame) and any file using a top-level macro
(the .com aborts on load).

After editing a `.scm`, delete BOTH the `.com` and the `.bin`, or Scheme silently
loads the stale binary. `load.scm` names files without extension and prefers `.com`.
(`file-fresh-com?` compares mtimes, so a plain re-save is usually enough.)

**Then RE-COMPILE the files you edited, before you run anything.** An edited file
loads from source; that is fine for a leaf proof script and ruinous for a core
file. Editing `wff.scm` (whose `subst-free`/`free-vars`/`validate-wff!` run in every
inner loop) took one library load from 24 s to **over 14 minutes**. Compiling the
edited files back is a couple of seconds and needs no loaded library:

    mit-scheme --quiet --eval '(begin (compile-file "/abs/path/wff.scm") (exit))'

`compile-vnb!` does the whole tree incrementally but wants a loaded REPL -- which is
the very load you just made slow. Compile first, load second.

**And check WHICH files it actually compiled.** `vnb-file-uses-bc*-macro?` (load.scm)
decides what `compile-vnb!` skips. It is now done **with the READER** (2026-08-15), and
the two failed textual attempts before it are the argument for that:

* It began as a raw per-line `substring?` for `(bc* ` / `(declare-structure ` / `(vlet `,
  which matched COMMENTS -- so `macetes.scm` (`(bc* ` at :134) and `interactive.scm` (a
  docstring at :2619) were silently never compiled. Fixed 2026-08-12 by cutting each line
  at its first `;`.
* Cutting at `;` does not help when the mention is DATA: a string (`suggest.scm:2733`,
  `(string-append "(bc* '" ...)`), a quoted list (`suggest.scm:3851`,
  `(memq (car step) '(bc* fact ta))`), or an alist key (`tactics-help.scm`,
  `(bc* . "a library theorem's ...")` and `(bc* composite (backchain))`). So **`suggest`
  and `tactics-help` -- the two copilot files, and the ones most likely to be edited --
  were skipped forever**, along with `proof-tex`. A line scan cannot fix the last two at
  all: the quote making them data is on an enclosing line.

The check now `read`s the file and looks for the macro applied in CODE position
(`vnb--form-uses-macro?`, which returns #f under `quote`). The reader knows what a
string, a comment and a quote are; a textual scan can only guess at all three. After the
change the skip list is 31 files, every one a genuine `declare-structure` structure or
`bc*` driver, and `*vnb-top-level-macros*` keys are SYMBOLS now, not strings.

**How it was found, and why it matters:** the user unpacked the tarball fresh, ran
`./VNB-with-compile --full`, and had **31** root `.com` files where this box had 33. The
one-liner that names the difference is worth keeping:

    cd ~/prover; for f in *.scm; do b="${f%.scm}"; [ -f "$b.com" ] || echo "  $b"; done

The legitimately-uncompiled root set is 8: `clobber-guard driver-kit load mutation-check
proof-tex proven-theorems test-suite-negative test-suite` -- and `proof-tex` left that
list with this fix, so it is 7. Anything else in that output is a file the scan is
wrongly skipping. Compiling the three recovered files took the **full suite from ~6
minutes to 3m12s**. The failure mode is silent and it compounds: an uncompiled core file
costs the whole library load (an interpreted `wff.scm` once took a 24 s load to over 14
minutes) and nothing reports it. If a load is inexplicably slow, the question is not
"is the tree compiled" but "is THIS file compiled": `ls -la <file>.com`.

**But never compile a file that USES a top-level macro that way.** `compile-file` from a
bare REPL cannot see `bc*` (interactive.scm), `declare-structure` (structures.scm) or
`vlet` (vlet.scm) -- the three entries of `*vnb-top-level-macros*` (load.scm:1236) -- so
it compiles the form as an APPLICATION: a fresh `structure-library/ring.com` then dies on
load with `;Unbound variable: carr`, stranding every file after it. `compile-vnb!` knows
this (`*vnb-top-level-macros*` in load.scm) and SKIPS such files -- they load from source,
which costs nothing measurable (their work is in the compiled procedures they call:
moving the whole structure-library to source-load changed a cold load by under a second,
36.8 s -> 36.9 s). So `(compile-vnb!)` from a loaded REPL is the safe recipe; the one-file
`--eval (compile-file ...)` is only for files with no macro use.

**There is no skip-proofs mode.** `VNB_SKIP_PROOFS` was removed (2026-07-09): it had
silently stopped working, and a mode that installs goals as theorems without running their
tactics would give you a library whose `qed` bills read `trust: none` about proofs nobody
checked. Compiling is the honest speedup. If you find the variable named in an old
comment, the comment is stale.

## This box

**Since 2026-09-14 this is the capataz `primary`: a t3.small, 1.9 GB RAM plus a 2 GB
swapfile.** (The 3.8 GB figure that stood here until then was the OLD box, now stopped.)
One library load requests `--heap 120000`, about 1 GB, and **one is all that fits**: a
second heap or the suite beside it is the silent exit-0 death described under "Running
it". So the primary holds the canonical tree, Claude and the agents; heavy VNB runs go
to WORKERS.

**Workers (measured 2026-09-14, re-measured 2026-09-17).** Until 2026-09-17 a band PROBE
ran on MIT's DEFAULT heap (~135 MB): `-b file.scm` passed no `--heap`, its peak RSS was
~290 MB, and a t3.medium (3.8 GB) held about nine of them. The user's son profiled the
workers with perf (2026-09-15) and found that on that heap a probe spends **60% of its
wall time in the stop-the-world copying GC** (the library nearly fills the heap, so a
full copy of the live set runs every 85-240 ms). `prover` now gives every `--band` start
a heap too (`BAND_HEAP`: 120000 blocks on a box with 3 GB or more, 40000 on the primary;
`VNB_BAND_HEAP=none` is the old behaviour, the A/B control). One 10-theorem driver on a
t3.medium: default heap 64.1 s (60% GC, 143 collections, 437 MB peak); `--heap 60000`
37.1 s (28%, 779 MB); `--heap 120000` **31.2 s (17%, 19 collections, 1248 MB)**. So a
probe is now a ~1.25 GB process and a t3.medium holds TWO of them, one per vCPU (three
at 60000 would have shared two cores). A cold compiled load on a t3.medium is 4m39s.

Bringing a worker up is about FIVE minutes and involves no compile: the `.com` files and
the band are portable between boxes running the same MIT/GNU Scheme 12.1, and the
worker's Ubuntu 24.04 package IS 12.1 (verified: the primary's band restores there
unchanged and proves the same theorem). The recipe, from the primary:

    capataz launch worker --yes --json --type t3.medium
    capataz run worker-NN --json 'apt-get install -y -q mit-scheme; fallocate -l 2G /swapfile; chmod 600 /swapfile; mkswap /swapfile; swapon /swapfile'
    capataz push worker-NN --yes --rsync --src ~/prover --dest /home/ubuntu/prover \
        --exclude .git --exclude scratchpad/ --exclude scratch/     # WITH .com and vnb.band: 195 MB, 80 s

(The dest must equal the source path: the band carries absolute paths. The swap step
sometimes gets SIGKILLed when run in the same SSM command as the apt install -- run it
again on its own.) From-scratch, `VNB-with-compile` on a worker was still in its
INTERPRETED load after 48 minutes; the library is 1031 theorems now, not the 300 the
"~11 min interpreted" figure above was measured on. Do not compile on a worker; push.

Two scripts in the tree wrap this, and every prover run on a worker goes through the
first:

* `vnb-slot ARGS` -- `./prover ARGS` inside a memory slot (`flock`), so N+1 provers can
  never stack on one box. Probes (`-b`) and loads are separate slot families,
  RAM/1700 MB (2 on a t3.medium; RAM/400 MB under `VNB_BAND_HEAP=none`) and
  RAM/1200 MB; a further run WAITS for a slot. Override with `VNB_SLOTS`.
* `vnb-probe WORKER file.scm` -- ships ONE file to the worker (base64 over `capataz
  run`) and runs it there with `vnb-slot -b`; prints the output and passes the exit
  status back. About 5 s of overhead per call. This is how an agent on the primary
  tests a proof without a prover of its own. The worker's band is the primary's band as
  pushed: after a library change, rebuild here and push again.
* `vnb-suite WORKER [--heap 200000] [--timeout 4000]` -- the full check suite on a
  worker, alone, in the foreground of one SSM command, with the SUMMARY and FAIL lines
  brought back.
* **Every run through those two is METERED (2026-09-17).** `vnb-metrics-run` (python,
  runs on the worker) wraps the command, sums MIT's per-GC notification lines and reads
  the `;;VNB-METRICS` line `prover` prints under `VNB_METRICS`, and emits one JSON line
  (wall, CPU, GC seconds and count, peak RSS, theorem-table size, qed/warning counts,
  outcome). The line rides back in the same SSM reply as the digest -- no extra copy --
  and is appended to `~/mailbox/metrics/runs.jsonl` (field meanings in the README
  beside it); the suite also logs a progress line every five minutes. That ledger is
  read from outside the tree, by the user's son, to spot trends; it is what turned the
  GC finding above into a number that can be re-checked.

**How a proving wave runs (2026-09-14, two waves, 14/14 agents succeeded, 42 leaves):**
the triage tables and the agent brief are `scratchpad/triage/` (`CONSOLIDATED.md`,
`RUBRIC.md`, `PROOF-AGENT.md`). An agent gets one leaf (or a bundle sharing mechanics),
writes ONE new theorem-library file, probes it with `vnb-probe worker-NN`, and reports the
outcome, the load window and the support site to retire; it edits no shared file. The
integrator retires the supports (`scratchpad/retire.py`, a string-aware form remover),
wires load.scm BY FILE NAME (every agent counts load positions differently), then pushes
and runs a COLD load and the suite on a worker. The band on the worker is the primary's,
so an agent's proof may cite the support it is proving under another name; the cold load
is what catches that, and load-order, and `lookup-theorem`.

Lifecycle: `capataz stop` keeps the disk (and the pushed tree) for about a dollar a month;
`capataz launch worker` cannot start from a snapshot (only `launch primary` can), so a
pool of STOPPED workers is the bake. Claude launches and stops workers; agents never do.

Never `pkill -f mit-scheme` from a shell command: the pattern matches the killing
command's own command line and takes down the shell (exit 144). A bracket class
(`pgrep -f "[m]it-scheme"`) only saves `pgrep` from matching *itself* -- if the surrounding
shell was launched as `... mit-scheme ...`, `-f` still matches it and you kill your own
shell. Match the executable, not the command line: **`pgrep -x mit-scheme`**.

## Case folding -- the trap that keeps biting

Both the VNB reader and MIT Scheme fold symbols to lowercase. `X` is `x`, `SP` is `sp`.
Three consequences, each of which has cost a debugging session:

1. **Never name a top-level `define` in a proof file like a tactic or a registered
   constant.** `(define BC ...)` rebinds the `bc` TACTIC to a term; the next
   `(bc 'thm)` dies with "The object (...) is not applicable". Real cases: `BC` in
   bordered-eq-border-proof.scm, `TT` in hahn-banach-full-proof.scm and
   nn-least-element.scm, `SP` in a Smith driver, `ID` in mat-equiv-proof.scm.
   Use the file's helper prefix (`ss-`, `bm-`, `cc-`, `hb-`, `me-`). Single/double
   capitals (`BC` `TT` `SP` `NI` `AI` `DI`) are the danger zone. `case-fold-audit` and
   `constant-binder-audit` both inspect WFF binders only, never Scheme defines --
   **`clobber-guard.scm` is the gate that does**: it snapshots every procedure binding
   after `minimize` loads and, after each later file, errors if any was rebound to a
   non-procedure, naming file and symbol. (It found `(define Tm ...)` in
   noetherian-maximal-proof.scm silently killing the `tm` surface helper.) Macros are
   invisible to it -- `environment-lookup` refuses a syntactic keyword, so `bc*` is
   never watched.

2. Structure accessors may inadvertently collide with obvious binder names, but a
   warning is issued (`constant-binder-audit`). `X` used to be a carrier accessor
   and is now `CARR` for algebraic structures, `PTS` for metric spaces (whose
   distance `D` is now `DIST`). Same story for `A`, and for `ID`, now `IDEN`.
   In general avoid single letters -- not a hard and fast rule.

3. Inner binders that would collide take a trailing underscore: `i_`, `j_`, `n_`, `r_`.
   The same fold makes **`bd-K` and `bd-k` ONE variable**, so a driver holding two
   eigenvariables apart by capitalisation holds one (found 2026-08-17 in
   ccint-bounded.scm: the merged bound overwrote the inherited one, and the finder for
   the inherited one's bounding universal then matched nothing, several steps later).
   `clobber-guard` cannot see this -- both bindings are non-procedures in the file's own
   frame -- so the rule is simply never to distinguish two names by case. They are now
   `bd-k` and `bd-merged`.

4. **A binder list scopes LEFT TO RIGHT, so a guard may mention only binders to its
   LEFT.** `forall([s in CARR(r), r], FUBA(s))` expands to
   `(FORALL s (IMPLIES (IN s (CARR r)) (FORALL r (FUBA s))))`: the guard's `r` is
   OUTSIDE the scope of the `forall r`, hence FREE, and the later binder binds a
   different variable of the same name. With a body that mentions `r` too, one formula
   carries two distinct variables both spelled `r`, and the printer round-trips it
   faithfully -- nothing on screen shows it. `validate-wff!` warned generically
   ("symbol r is both bound (in some binder) and free"); since 2026-08-15
   `warn-forward-guard-reference!` (wff.scm) fires at binding-list expansion -- so on
   TYPED input, not only on install -- and names both positions. It returns its findings
   (`binding-list-forward-refs`) as well as printing them. Warn-only: the form has a
   meaning, it is simply almost never the intended one. Nothing in the library trips it.

**`lambda` is gone; the binders are `vnb-lambda` and `lambdoid`** (2026-08-18, the user's
call). Surface `lambda([x in A], body)` built a functoid RECORD -- the set-domain sibling of
`lambdoid` -- and so was NOT `VNB-LAMBDA`, which builds a set of ordered pairs, an element
of `FUN(A,B)`. They carry different obligations and different rules: `vnb-lambda` is typed
by `lam-t` (which opens the `A in SET` leaf) and reduced by `lam-b`; a functoid has no
typing rule and reduces by `beta`. One unadorned word standing for the construct no library
proof uses, beside a hyphenated one standing for the construct every proof uses, is a
confusion with no upside. `parser.scm` now ERRORS on `lambda`, naming both replacements.

Three things were checked before removing it, and they are the reason it was safe:

* **Zero installed formulas contain a functoid record** (measured over `*theorem-table*`),
  and `functoid-beta` is in `kernel-rules-audit`'s "not exercised by this load" list. The
  whole functoid-record machinery is reachable only from a hand-typed `lambdoid`.
* **The `'lambda` functoid KIND was dead.** Every reader of `functoid-kind` either
  preserves it, compares two for equality, or prints it -- nothing branches on it, so the
  documented "domain must be a SET" was enforced nowhere. `make-functoid` now REFUSES
  `'lambda`: `expr->str` prints the kind verbatim, so such a record would have printed as
  `lambda(...)`, which no longer parses, and a round-trip that silently stops round-tripping
  is worse than an error.
* **`vnb-lambda` was never "waved through by the parser"**, which is what it looks like:
  `VNB-LAMBDA` appears nowhere in parser.scm, and `vnb-lambda(...)` reaches the generic
  application branch. The binder is built by `expand-destructuring-quantifiers`
  (wff.scm:306-338) -- the same desugarer that handles `forall([x in A], ...)` -- which
  collapses the single-binder case to the bare-symbol form, REJECTS a partly-typed binder
  list, and REJECTS the domainless form. Plus a dedicated `make-wff` branch and five suite
  checks. It is a design, not an accident.

Only two suite checks used the surface `lambda` (both converted to `lambdoid`); four new
checks pin the removal and the error text. Suite 909/0.

A related naming question is still OPEN and is the same species: `def-functoid` installs a
macete and nothing else, and `docs/functoids-and-functions.md` section 8 (adopted
2026-07-28) says its borrowing of the word "is what makes the manual's account of functoids
read as false". That rename has not been done.

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

## Writing proof drivers

Proof scripts navigate a deduction graph by moving focus between open leaves.

* **Never navigate by goal shape alone.** Sibling branches routinely share a goal head.
  `(forall k. IN k NN => IH => ...)` and a row conjunct `(forall i_. ... => ... => ...)`
  are both `FORALL/IMPLIES/IMPLIES`. Discriminate on the binder, or better, on a
  CONTEXT formula unique to the branch.
* **Never name an ASSUMPTION by shape either** -- same rule, one level down. An induction
  step's context holds the IH, the instantiated IH, and look-alike `SPANS`/`FORSOME`
  siblings; and a `mac-h`/`ai` fed a formula the driver RECONSTRUCTED (with its own guess
  at the eigenvariable names) matches nothing, silently no-ops, and every later command
  runs in the wrong branch. Use the `dk-` kit in `driver-kit.scm`: run the tactic, DIFF
  the assumption list, keep what appeared. `dk-landed` (errors if nothing landed --
  a silent no-op IS the bug), `dk-landed-1`, `dk-landed-find`, `dk-split!` (ai the landed
  conjunctions to exhaustion), `dk-opened` (leaves a branching tactic opened).
  **`fact` and `inst+` land their whole instantiation chain**, not one formula -- the
  theorem, each partly-peeled form, and the detached result -- so use `dk-fact!` /
  `dk-deepest`, which take the landing no other landing contains.
* **Never rely on where `ass` or `cut` leave focus.** `cut` opens a side goal plus the
  main branch; the `ass` that closes the side goal hands focus to an engine-chosen leaf.
  Re-focus explicitly afterwards.
* A focus helper that returns `#f` and leaves focus put on a miss will hide all of the
  above for weeks. Make it **error**.
* `fact` peels leading universals and auto-detaches each antecedent already in context;
  it will NOT split a conjunctive antecedent (use backward `bc*` for those). If a `fact`
  seems inert, dump the context and look for the one missing typing hypothesis.
  `ord-le-total`, `ord-le-antisymm`, `ord-le-trans` and `ord-succ-immediate` all have
  AND antecedents, so each wants a `(have! '(AND ...))` immediately before the `fact`.
  Without it the citation lands the *implication*, silently, and a following `use-cases`
  cuts the disjunction it was supposed to find in context -- leaving an exhaustiveness
  obligation open branches away.
* **`di` is greedy.** One call takes the whole leading FORALL/IMPLIES prefix, and the
  next call will take a `NOT` (assuming it, goal `FALSITY`) or SPLIT an `AND` goal into
  two leaves. Counting `di`s is therefore not a way to land on a chosen goal -- write a
  peel-until-the-head-changes helper and guard it on progress (`zb-peel!` in
  zz-bezout-proof.scm, `z2-peel!` in zorn-route-two.scm).
  **Greediness costs you INDUCTION, and there is no undo.** `ni`
  (`pi-nn-induction!`) tests the goal's SHAPE -- literally `(FORALL n (IMPLIES (IN n NN)
  body))` at the top -- so it also misses `forall([a, n in nn, ...], ...)`, where the
  mathematics is the same and only the binder ORDER differs. State an induction variable
  FIRST. If the `di` already happened, the induction is still recoverable without a
  restart: `cut` the generalization with the NN variable outermost, `ni` that, and close
  the leaf from it by instantiation. `what-now`'s **induction lane** (suggest.scm,
  2026-08-15) reports both cases and prints the `(cut "...")` built from the goal and the
  CONTEXT's typings; it stays silent when `ni` already fires, since the live-fire lane has
  that. It quantifies only eigenvariables that carry a typing assumption -- an untyped one
  (from an unrestricted `forall([a], ...)`) stays free, which is sound because it is fixed.
  Four suite checks, including that the emitted cut parses with the variable outermost.
* **A GUARDED universal goes whole under one `di`; an UNGUARDED one does not.**
  `(FORALL t (IMPLIES (IN t S) body))` -- what the surface writes `forall([t in S], ...)`
  -- lands `(IN t S)` in a single call. `(FORALL y (IMPLIES (AND ...) ...))`, the shape a
  hand-built hypothesis takes when its antecedent is a conjunction rather than a typing,
  peels the QUANTIFIER and lands NOTHING; the antecedent comes on the next call. A
  `dk-landed-1` around one `di` therefore errors on the second shape and succeeds on the
  first, which is indistinguishable from a driver bug until you print the goal. Loop on
  the LANDING, not on a `di` count: `bd-di-landed!` (ccint-bounded.scm) calls
  `dk-landed*` until something lands and errors if nothing ever does.
* `ai` on a `NOT` assumption is NOT-ELIM, not "reduce the goal to the positive": it fires
  only when the positive is ALREADY in context. Every contradiction is therefore
  `have!` the positive, then `ai` the negation -- never an `ai` you expect to leave the
  positive as your new goal.
* **`obtain` cannot skolemize an existential that is ALREADY in the context**, and it
  does not say so. It diffs the context around its own LANE (sketch.scm), so a `FORSOME`
  that `di` landed a moment earlier is invisible to it -- `(obtain (lambda () #t))`
  reports "no existential landed". Write the three-line local skolemizer instead:
  `ai` the formula, `dk-split!` whatever lands, and read the eigenvariable off by
  free-variable set difference (`bd-skolem!` in ccint-bounded.scm, `ev-skolem!` in
  evt-proof.scm). Worse, `obtain` runs its lane under `vnb-guard`, so an ERROR raised
  inside the lane -- a finder that matched nothing, say -- is swallowed and reported as
  "nothing obtained": the `quietly`-hides-errors trap, one level in.
* **Discriminate a hypothesis on its CONSEQUENT, not on a symbol it contains.** A finder
  reading "the FORALL that mentions `IS-CONTINUOUS-AT`" picks
  `continuous-bounded-above-on-ccint` once that theorem has been cited, because the
  continuity universal is its own ANTECEDENT and `fact` lands the whole instantiation
  chain nearer the top of the context than the hypothesis sits. The instantiation then
  goes to the wrong theorem, at the wrong argument, and lands something unusable rather
  than nothing. Both EVT drivers now test `(car (caddr body))`.
* **A GUARDED macete: `mac` refuses, `mac-h` spawns.** `rr-ms-dist` is
  `forall u,v in RR. (DIST RR-MS)(u,v) == abs(u-v)`. On an ASSUMPTION, `mac-h` applies it
  and posts the typing as a side-condition subgoal ("1 side-condition(s) spawned"). On a
  GOAL whose arguments are not already typed in context, `mac` does not apply it at all --
  it warns `apply-macete: macete not applicable` and leaves the goal untouched, and the
  driver sails on rewriting a formula that never changed. So type the arguments BEFORE the
  `mac`. (Corollary for the operator, not the tree: `;VNB warning:` lines carry this
  information and are easy to filter out of a log grep. Grep for them.)
* **`lam-t` opens TWO leaves, not one:** the pointwise typing of the body, and the
  SETHOOD of the domain. A `VNB-LAMBDA` is a set of pairs, so `(IN RR SET)` has to be
  discharged (`rr-is-set`) before the lambda is a function at all. A driver that expects
  one leaf leaves the other open and finds out at `qed`.
* **`prop` can DECLINE a one-step contradiction in a deep context** (2026-09-17,
  finsum-single-support): with ~20 assumptions its atom cap (12, then radius narrowing)
  drops the pair `P` / `NOT P` and it prints "does not follow propositionally" with an
  EMPTY countermodel. That message means "I did not look at the right atoms", not "this
  is not propositional". For a contradiction already in context use `(ai <the NOT>)`
  directly; where propositional reasoning is really needed, `dk-only!` the context down
  to the relevant formulas first and `prop` fires.
* **`if-true` does not rewrite the goal.** It opens the condition as one leaf and hands
  the other leaf the equation `IF(p,a,b) = a` as an ASSUMPTION; the goal still holds the
  `IF`, and needs an explicit `subst` of that equation. A driver written as if `if-true`
  had rewritten dies steps later with `reflexivity: goal is not (= a a)`.
* **Two things the tree does NOT have** (same file): a RESTRICTION of a set-function to a
  subset (no `RESTRICT`, no "f in FUN(S,Y) => f|X in FUN(X,Y)"), and the converse of
  `card-insert` (`CARD X in NN` from `CARD(X u {k}) in NN`; the only lemma of that shape
  is the asserted `card-subset-nn`). A finite-sum argument that wants to peel one index
  off a SET therefore goes through the enumeration instead (induct on the fold length,
  transfer along `FIN-ENUM`), as `sum-ag-single-ind` does.
* **Rake batch 1 findings (2026-09-17, 27 `proof`-warranted supports proven by four
  agents in one afternoon; every warrant was an accurate plan nobody had run):**
  `dk-apply!` / `dk-fact!` inside a `dk-landed-1` thunk land the whole instantiation chain
  and error, same as `inst*!`/`inst+`/`fact`. An alpha-variant pair of leaves (the support
  spells a binder `y_`, the functoid body `x_`) closes by `ass`, which is alpha-aware, and
  NOT by `prop`, which is not. `ineq` certifies an atom only from a STANDALONE `(IN t RR)`:
  with `POS-RR r` or the typing inside an unsplit conjunction the atom is uncertified and the
  message blames the goal (cite `rr-pos-rr-in-rr`). A shape-based premise finder ("every
  `< <= =`-headed assumption") hands `ineq` a SET equation like `U = BALL(s,c,r)` and
  poisons the call; name premises by formula. A `proof`-warranted induction stated with the
  induction variable NOT outermost (`strictly-mono-ge-id`: `phi` first) needs a companion
  statement with the NN binder outermost plus one `fact`, not just a driver. Lemmas the
  tree still lacks, each built inline twice: `complement-in-involutive`
  (`PTS \ (PTS \ X) = X` for `X subset PTS`, beside `complement-in-subset`) and
  ball-monotone-in-radius (`BALL(s,y,m) subset BALL(s,y,r)` for `m <= r`, beside
  `ball-is-open`). And `continuous-implies-open-preimage` (metric-open-sets.scm, `informal`)
  is now the ONLY support left in that file; its argument is the mirror of
  `open-preimage-implies-continuous` in rake-open-sets.scm, so it is one assignment away.
* **A `same-shape-as` structure has NO citable unfold** (2026-09-17, rake batch F).
  `VECTOR-SPACE` is declared `same-shape-as MODULE` plus a law, which installs the MACETE
  `is-vector-space` and no theorem, so `mac-h 'IS-VECTOR-SPACE` warns `unknown
  theorem/macete` and no-ops, while `mac-h 'IS-RING` and `mac-h 'IS-NORMED-VECTOR-SPACE`
  work. It is the def-functoid trap one storey up, in a predicate. The one-line cure is the
  same: `is-vector-space-unfold` (theorem-library/rake-setoid.scm, `(di) (mac ...) (qrfl)`),
  and every other `same-shape-as` structure has the same hole until its unfold is proven.
  Also from that batch: DESCEND's well-definedness on a quotient is exactly `iota-d`'s two
  obligations (existence: `a in [a]` by REL reflexivity through `sep-mi`; uniqueness:
  RESPECTS), so `quotient-rep` / `class-self` / `descend-computes` were not needed; and
  `forall-guarded` emits all binders first and then the implication chain, so a hand
  transcription of a RESPECTS2-style body is a DIFFERENT formula (copy the constructor
  call, never the reading).
* **Rake batch E (matrix typing, 2026-09-17): three cheap retirements it exposed, and one
  duplicate.** `matrix-sethood` (matrix.scm) is an UNWARRANTED axiom (`trust: none` to any
  citer) and is provable in four lines -- `MATRIX(X)` is a subclass of the set
  `TUPLES(TUPLES X)`, so `tuples-sethood` twice plus `subclass-of-set-is-set`; it is cited
  nowhere. `pred-in-interval` (order-lemmas.scm, `well-known`) is provable (inline as
  `rkm-pred-in-interval!`, ~45 lines). The tree has `nn-succ-mono` and NO converse
  (`succ a <= succ b => a <= b`), re-derived by a three-lemma contradiction every time; one
  line in nn-order-ord.scm. `mpow-type` (monoid-power.scm, `informal`) is the WHOLE bill of
  `det-in-carrier` and, one view up, of `ring-power-type`: an NN induction nobody ran; and
  no `mpow-type-ring-multiplicative-monoid` view companion exists, so the read-off goes
  through the new `rmm-carr` (rake-mat-typing.scm; belongs in ag-view-read-offs.scm). The
  IF-tower resolver (`mtb-if-branch!` / `mtb-close-if!` in mat-typing-bundle.scm) is now
  duplicated as `rkm-if-branch!` / `rkm-close-if!`: it belongs in driver-kit.scm. And the
  entrywise typings (MATADD/MATSCALE/MATNEG) are NOT one-liners after the SIZE/MAT repair:
  they tabulate at `NTH(2, SIZE P)`, which is not `n` at zero rows, so each goes through
  `mat-colcount-transfer` with its guard closed by `prop` -- that is what makes them true
  at m = 0 rather than merely unchecked there.
* **Rake batch G (finsum / NN typing, 2026-09-17).** THREE warrants ("induction on |S| via
  finsum-insert": submodule-finsum-closed, finsum-all-id, finsum-single-support) named a
  finite-SET induction the tree does not have and a restriction it cannot express; the
  fold-length induction plus FIN-ENUM transfer does the job every time, and the general
  lemma `finsum-in-subset` (rake-finsum-typing.scm: a finite sum stays in any
  IDEN-containing, OPR-closed subset of an abelian group) should retire the next such leaf
  for free. `funcomp-succ-type` was FALSE with `q` untyped (q = 3/2: INTERVAL(1, succ q)
  can be empty while INTERVAL(1, q) = {1}) and is installed guarded `(IN q NN)`.
  `choose-in-nn` bottoms out in the asserted `card-power-nn` (finiteness of the powerset)
  and stays. `monoid-identity-in` / `monoid-carrier-closed-opr` (monoid.scm) are UNWARRANTED
  axioms (`trust: none` to any citer) -- the batch proved COMM-MONOID versions instead;
  retiring the monoid ones needs the `view-as-auto-specialize!` care (their view companions
  go with them). `mpow-type` is redundant at a commutative monoid (`mpow-comm-monoid-type-ind`
  is its induction, run). `def-functor` views still need a hand read-off per slot
  (`crmcm-carr` here, `rmm-carr` in batch E, six in ag-view-read-offs.scm): a shared view
  read-off driver would pay for itself. series-block-abs.scm's header still says `nn-le-gap`
  bills `nn-not-le-zero-pos`; that leaf is proven and the bill is `modulo 0`.
* **Rake batch L (analysis and sets, 2026-09-17).** `fun-domain-in-set` (`f in FUN(A,B) =>
  A in SET`; rake-analysis2.scm) did not exist: a member of a class is a set, `fun-no-junk`
  says a function IS its graph, and the first-coordinate image of a set is a set by
  replacement -- so any `lam-t` sethood leaf over the domain of an already-typed function
  closes by citation now. `centre-set-contains-choice` was UNDERDETERMINED (CHOICE of an
  empty class; F = {EMPTY-SET}) and carries `forsome c. c in CENTRES(s,U,r)` since. Three
  leaves stay asserted with their routes written in that file's report: `card-power-nn`
  is `finite-set-induction` (primitive) with `C = {x | CARD(POWER x) in NN}`, the step
  needing only the INCLUSION `POWER(S u {x}) subset POWER S u IMAGE(T |-> T u {x}, POWER S)`
  plus `card-image-finite` and `card-union-nn` (both proven) -- a 150-250 line driver of
  card-subset-nn.scm's shape; `subsequence-capture` is `dc-on-nn-pred` at `X := S`,
  `nxt(k,u) = {y in S | u < y}` (totality is the PROVEN `inf-subset-nn-unbounded`) plus one
  NN induction, so it chains to `dc-on-nn`; and `dc-on-nn-pred` cannot be derived from
  `dc-on-nn` without a SEP over triples the tree cannot form (CARTESIAN is binary, no
  TUPLES-membership lemma for a literal LIST, no tuple-extensionality read-off) -- honest
  debt, and its warrant says exactly that.
* **`succ` off NN is an uninterpreted term, and statements that forget it are FALSE**
  (rake batch K, 2026-09-17). Every axiom and theorem about `succ` is NN-guarded, so a
  statement that puts `succ t` in an INTERVAL bound or an index without typing `t` asserts
  something a model may interpret freely: `succ-in-interval` (q = 3/2, succ(3/2) := 0) and
  `pred-in-interval` (p = 1/2, succ(1/2) := 100) were both refutable and are now guarded on
  the bound; `comb-kk-laws`' note on `bt-succ-minus-1` over ZZ is the same species. Worth a
  SWEEP of the remaining PSS for `succ` applied to an untyped variable; these two were found
  by trying to prove them, not by an audit. Also from that batch: the "`succ a <= succ b =>
  a <= b`" helper the earlier batches wanted already existed as the asserted
  `nn-succ-le-cancel` (now proven, rake-intervals.scm); `succ-nn-minus-1` (order-lemmas.scm)
  is one line from it; the two IDENTMAT identity laws needed NO guard (the middle dimension
  is one of the outer ones, so the product guard is propositionally trivial); and
  `elem-entry-readoffs` sits one slot above `mat-ring-proof`, an empty window for anything
  that wants both -- it can move anywhere in [235, 332).
* **Rake batch J (the finsum laws, 2026-09-17). `finsum-congruence` was FALSE as stated**:
  `f`, `g` untyped (deliberately, 2026-08-02, so back-peeled families fit) but the
  conclusion a strict `=`, which is definedness -- a constant map with a value outside
  `CARR(ag)` satisfies the hypothesis and the FINSUM does not denote; the literal statement
  drives down to `t = t` and `rfl` refuses. It is now stated with `==` (rake-finsum-laws.scm;
  `subst` takes `==` as `=`, and the 52 citers `fact` then rewrite), with the typed `=`
  form beside it as `finsum-congruence-guarded`. **`enum-fam-value`** (`(ENUM-FAM ag u phi
  n)(i) == u(phi i)` on the segment, `u`, `phi` VARIABLES so `lam-b` has one redex) is the
  brick the whole finsum arc had been re-doing inline; with it every law is a pointwise
  relation between two ENUM-FAMs plus the fold-length induction. `sum-ag-type-ptwise` is the
  matching typing (sum-ag-type wants `f in FUN(NN, ...)`, which a sliced family never is).
  `finsum-embed` stays asserted: `finite-set-induction` DOES exist (class form), and the
  restriction blocker is now dissolvable (`VNB-LAMBDA z u (f z)` typed by `lam-t`, transported
  by the untyped `finsum-congruence`), but the surgery `S = (S \ {x}) u {x}` still wants
  `difference-membership` and a converse of `card-insert`. Also new and previously missing:
  `abelian-group-opr-interchange` (`(a.b).(c.d) = (a.c).(b.d)`; there is no abelian-group
  normalizer, `crs` is rings only), `module-act-zero-vec` (`r . 0_V = 0_V`, the twin of
  `module-zero-act`), `interval-succ-insert`; `ord-segment-insert` (finsum-additive.scm, still
  asserted) is the ORD-SEGMENT twin of the last and the same driver closes it.
* **`F(M, u)` for a ONE-parameter functoid `F` is `F` applied to the pair `[M, u]`, not
  `F(M)(u)`** (rake batch O, 2026-09-17). `apply-tupling-2` makes an n-ary application an
  application to the TUPLE, so the support `embed-isometry` wrote `(EMBED M u)`, which is
  EMBED at `[M,u]` -- a function on `PTS([M,u])`, not a point of the completion -- and `mac
  'EMBED` declined on it. The statement is now `((EMBED M) u)`, the term `embed-in-fun`
  types, and is proven (rake-setoid2.scm). Any support that applies a def-functoid to MORE
  arguments than its parameter list has is the same misspelling; worth a sweep. Also from
  that batch: `rko2-quad` (the quadrilateral inequality `|d(a,b) - d(c,e)| <= d(a,c) +
  d(b,e)`) and `rko2-dist-converges` (the metric is continuous along sequences) did not exist
  and are what every representative-independence argument about a completion needs;
  `dk-split-all!` with NO argument splits every conjunction in context, including a `have!`
  just landed and the theorem's own AND antecedent -- pass it the landing.
* **UNIVERSAL INSTANTIATION OWES DEFINEDNESS since 2026-09-18** (the LUTINS rule; the
  entry below records how the hole was found). `forall-elim` posts the side sequent `t = t`
  unless the CERTIFICATE (`pi--defined?`, primitive-inferences.scm) accepts `t`: a variable; a
  ground number; a term the context types or equates; a term occurring OUTSIDE binders in a
  true `IN` / `=` / `<=` / `<` hypothesis, in any position, the operator included
  (strictness); a class term on defined arguments (SEP, COMP, FUN, TUPLES, POWER, IMAGE,
  INTERVAL, ORD-SEGMENT, BIJECTION, MATRIX, ... and any functoid whose body is one);
  `VNB-LAMBDA`/SEP/BIG-UNION over a certified domain; `NTH k` of a LIST; `LENGTH` of a term
  typed in a tuples class; arithmetic (`+ - * min max abs succ ^`) on number-typed arguments;
  an accessor of a structure the context has (`IS-RING s` or `s in RING`, through the
  definitional parent chain); an applied structure operation on arguments typed in its
  declared domain; `f(a)` with `f in FUN(D,_)` and `a in D`; a `def-predicate` hypothesis
  whose defining body's conjuncts certify (`IS-ANTIDERIVABLE(s(k),a,b)` types `s(k)`, to
  depth 3, existentials stripped). NEVER: CHOICE, IOTA, an untyped application, ENTRY without
  range typing, the IOTA-bodied matrix constructors, FINSUM. `rfl` uses the same test. The
  policy and the measurements are docs/definedness-instantiation-2026-09-18.md.
  **What the leaf costs a driver:** nothing when the term's typing is in context BEFORE the
  instantiation, or one citation away for a matrix constructor, FINSUM, LINCOMB, ENTRY or
  arithmetic -- `dk-discharge-owed!` (driver-kit.scm), called at the command boundary on the
  leaves the kernel TAGGED (`*pi-owed-nodes*`), cites the typing and closes by `rfl`,
  recording its steps. Anything else stays open and `qed` reports it. Under
  `VNB_KEEP_GOING` a proof that ends with open leaves installs as an ASSERTED HOLE and prints
  its goals (`*vnb-qed-holes*`), so one load lists every root. Three traps the repair wave
  hit: an owed leaf has the SAME context as its parent, so a "focus the leaf whose context
  holds X" helper picks the owed leaf first and the driver dies branches later with `cdr of
  #f`; `ai` / `dk-split!` / `dk-skolem!` REPLACE the formula they open, so exposing a typing
  conjunct as a certificate must be a `have!` lane; and `every` in this tree is 2-ary
  (deduction-graphs.scm) -- a two-list call raises, and an error inside a kernel rule aborts
  the whole `fact`. The audit hook stays: `VNB_DEF_AUDIT=1` prints the owed count by head at
  the end of a load and dumps the terms to /home/ubuntu/def-audit-terms.txt.
  **Two copilot lanes had to learn the rule too:** `what-now`'s typing lane now emits the
  forward typing BEFORE the backchain (suggest.scm; the closure law's `bc*` instantiates at
  the term, which owes definedness until the fact has typed it) and drops the owed leaf from
  the probe's subgoals; and `ineq-supply` no longer cites typings at atoms that sit UNDER a
  binder of the formula they came from (`f(n_)` inside the lambda of a partial sum: the
  variable is out of scope at the node, so the citation owed a leaf nothing could close, and
  `supply` refused the whole goal). The two suite `ni` proofs (`prod-ord-type`, `sum-type`)
  now rewrite along the recursion equation instead of instantiating at the recursion term.
  The hook is TRANSACTIONAL: an attempt that does not close the leaf is rolled back (graph,
  focus, script, trace, undo stack), so a failed closer leaves no half-cut leaf behind.
* **THE KERNEL PROVES THAT EVERY TERM DENOTES** (rake batch P, 2026-09-17; probe
  `scratchpad/rkp/defprobe.scm`). `term-self-defined?` (primitive-inferences.scm) grants every
  VARIABLE definedness, so `(FORALL a (= a a))` is provable `modulo 0` by `(di) (rfl)`; and
  `pi-instantiate!` substitutes an arbitrary TERM into a universal with no definedness side
  condition, so that theorem instantiated at `recip(0)` closes `recip(0) = recip(0)`. That
  collapses the partial-equality reading `(= t t)` is supposed to carry. It is a foundational
  decision, the user's, of the `iota-in-elim` kind: either instantiation owes a definedness
  obligation for the instantiating term, or `rfl` must not certify a bare variable. Until it
  is made, `mul-defined-factors` (order-lemmas.scm) is "provable" for the wrong reason and
  `recip-defined-nonzero` is unprovable (nothing relates recip's definedness to its argument;
  no strictness axiom, no elimination for definedness); both stay asserted. Also from that
  batch: `card-zero-is-empty` (`CARD A = 0 => A = EMPTY-SET`) did not exist (rake-
  combinatorics.scm has it, by finite-set-induction whose step never uses the IH);
  `card-power-nn` needs no disjointness (`card-union-nn` asks none); `fact` of a membership
  IFF lands BOTH the instance and the universal and `dk-deepest` cannot separate them;
  `pairing-membership`'s guard sits BETWEEN its binders, so `fact` stops at the detached
  `forall x` and the element must come from `inst*!`; `crs` does not reach a structure's
  `(MUL R)`, so ring regrouping is hand-chained (`ring-mul-interchange`); `choose-succ`
  (Pascal) is a ~150-line assignment on the CHOOSE-SET split plus `card-image-injection`.
* `dk-split!` begins by `ai`-ing the formula you hand it, so handing it an ATOM is an
  error (`dk-landed: the tactic landed no assumption`), not a no-op. It is for
  conjunctions only; for a single landed atom keep `dk-landed-1`.
* `detach!` takes the **IMPLIES** formula, not its antecedent. `(detach! <antecedent>)`
  is a silent no-op.
* **`lam-b` needs the argument TYPED, and needs it BEFORE the reduction.** A lambda
  carries its domain and is defined only there, so `((VNB-LAMBDA x A b) u)` reduces
  cleanly only when `(IN u A)` is evident -- in the context, or supplied by an
  enclosing guarded universal or by an enclosing `VNB-LAMBDA`/`SEP`/`BIG-UNION`
  binder (the walker threads all three). Otherwise the step still fires but **owes
  `(IN u A)` as an extra leaf**, and a driver that was not expecting it wanders.
  **And the owed leaf can be UNPROVABLE, not merely extra** (2026-08-17, the SQRT work).
  `pi-lambda-beta!` (primitive-inferences.scm:1404) licenses a redex against
  `(append scope asms)` -- it threads the enclosing binders -- but posts the obligation as
  `(make-sequent asms ...)`, the OUTER context alone. So a `lam-b` fired on a goal that is
  still `forall y in PTS(RR-MS). ... ((VNB-LAMBDA z RR ...) y) ...`, where the walker
  cannot see `PTS(RR-MS)` as `RR`, owes `(IN y RR)` at a node whose context predates `y`
  entirely: `y` is FREE there and nothing constrains it. That leaf cannot be closed by any
  later step, and nothing says so until `qed`. PEEL AND TYPE FIRST, THEN BETA.
  The fix is always the same and always one line: land the typing fact *above* the
  `lam-b`, not below it. `mat-ring-proof`'s `mr-close-conj` is the worked example
  (type -> `lam-b` -> cite -> `ass`), and it is why `mr-rops` no longer betas: at the
  point it used to, the binders whose typings were needed did not exist yet.
* `mac-h` **replaces** the assumption it unfolds. Unfolding `(IS-IDEAL s I)` to reach its
  closure conjuncts therefore deletes the hypothesis that `ideal-elt-in-carrier` (and
  every other `fact` guarded on `IS-IDEAL`) needs. Get the projection another way, or
  unfold last.
* `minimize!` lands `GUARD[v:=w]` as **one conjunction**, not as its conjuncts. `ai` it
  before detaching anything against it.
* **A multi-variable substitution is NOT single substitution iterated.** `subst-free*`
  (expressions.scm) is the only multi-binding substitution in the tree; a fold of
  `subst-free` exposes whatever each binding substitutes IN to every later binding.
  That fold WAS `apply-subst` (the macete rewriter) until 2026-07-11: unfolding `SPANS`
  -- parameters `(md n u sm)` -- at `SPANS(md,k,w, INTERSECTION(sm, SPAN(md,n,BLOCK(u,n,1))))`
  let the pending `n:=k`, `u:=w` bindings rewrite the caller's own `n` and `u` INSIDE the
  term matched to `sm`. No error, no warning: a different theorem. It is the case-fold
  disease (a name collision) one level down, and it bites precisely when a recursive
  construction is fed back into its own definition. Iterating `subst-free` is legitimate
  ONLY when peeling nested quantifiers one binder at a time (`cmd-fact`, `mz--type-at!`),
  where the remaining variables are still BOUND.
* **`subst` rewrites in OPERATOR position since 2026-09-16.** Until then the Leibniz walk
  (`replace-term`, primitive-inferences.scm) visited argument positions only. Substituting
  for a VARIABLE was never affected, because it goes through `subst-free`, which walks
  heads. A COMPOUND term, though, was invisible inside a head: `((VADD md) x y)`, an
  applied `VNB-LAMBDA`, `((f (g r)) r)`. And when the term occurred both in the head and
  in an argument, only the argument was rewritten, SILENTLY. The walk now visits the
  head; the binder cases still block capture. Probe with before/after logs:
  `scratchpad/mx/subst-head-probe.scm`; five suite checks. Old drivers that `mac` an
  equation to reach an operator (`mvag-op`, `ras-op`) still work, and `subst` is now an
  alternative there.
* A macete rewrites **every** occurrence. If `fact` lands `SUM(λz. (MUL ag) …) = (MUL ag) …`
  and you `mac-h` it, the operator changes in the summand lambda *and* at the top, while
  the goal's copy of that same summand does not. Normalize **both sides** with the same
  macete (`mac` the goal, `mac-h` the assumption), or `ass` silently fails to match.
* **`cut` of a formula already in context (up to ALPHA) is a silent self-loop.**
  `dg-post!` hash-conses sequent nodes by alpha-equivalence of the assertion plus
  equality of the context, and `context-add-assumption` is alpha-idempotent -- so the
  "main" child of the cut *is* the focus node. One leaf opens instead of two, the graph
  gains a cycle, and the failure surfaces branches later as a missing leaf. Guard with
  `alpha-equiv?` before cutting anything you did not just construct fresh. (This is what
  `minimize!` does; see `mz--cut!` in minimize.scm.)
* **`use-em` on a proposition the context already DECIDES is not a case split**, and
  since 2026-08-15 it ERRORS rather than doing it. If `P` is an assumption, the P-branch
  is hash-consed straight back onto the node it was split from (`context-add-assumption`
  is alpha-idempotent, sequents.scm:51) and the NOT-P branch has a contradictory context;
  the caller sees one new leaf that reads like a real obligation, is closable only by
  NOT-elim, and -- there being no undo in the tree -- cannot be taken back. The same holds
  mirrored when `NOT P` is the assumption. On a disjunctive goal whose disjunct is already
  in context the move is `(oi-l)` / `(oi-r)` then `(ass)`, and the error says so.
  `what-now`'s disjunction lane proposed the split unconditionally from the day it was
  written (2026-08-14) until the same date; it now checks both disjuncts against the
  context (`what-now--disjunct-in-context`, suggest.scm) and names the two-move close
  instead. Suite checks: five, beside the driver-kit containment block.
* **A PROBE MUST BIND `*replaying?*`, not just `*ps*`.** `what-now` / `scout` probe by
  running the REAL interactive tactic on a scratch state (`vnb-apply?` evals it by name),
  and every interactive tactic goes through `vnb--run!`, which calls `record-cmd!` and
  `vnb--capture-step!`. Those write to the GLOBAL `*proof-script*` and `*live-trace*` --
  which a `fluid-let` of `*ps*` does not protect. Until 2026-08-15 every FIRING probe
  therefore appended a step nobody took: to the script the emitter writes out and to the
  trace `proof-tex` prints from. Measured: one probed `(oi-l)` = +1 to each; a whole
  `what-now` = one per firing candidate. `*replaying?*` is the existing switch for exactly
  this (interactive.scm:25) and `vnb--scout-replay` already bound it; the what-now probes
  did not. All three now go through `vnb--probing` (suggest.scm), which binds `*ps*`,
  `*replaying?*` and `quietly` together. Library proofs were never affected -- they run
  from files and never call the copilot -- so this was an interactive-session defect only.
  Suite: two counter checks, plus `scratchpad/probe-pollution-demo.scm`, which fires the
  same tactic through the old and new wrappers and prints both deltas.
* `quietly` silences `vnb-guard` as well as `show`, so a tactic that *errors* inside it
  becomes a silent no-op and every later command runs in the wrong branch. A composite
  tactic wants `show` quiet and the guard loud (`mz--quietly`), plus a per-step
  "did this rule fire?" check -- every primitive inference gives its focus node an
  in-arrow, so `(null? (sequent-node-in-arrows n))` afterwards means it did not.
* **A command that changes nothing now SAYS so, and is not recorded** (2026-08-24).
  `vnb--run!` (interactive.scm) had three outcomes -- error, soft warning, success -- and
  a fourth hiding inside the third: a tactic that raised nothing, declined nothing, and
  returned the state it was handed fell to the success branch, was appended to
  `*proof-script*` and to the `*live-trace*` `proof-tex` prints from, and `show`ed the
  unchanged goal as though it had landed. The boundary now tests for it and prints
  `;VNB warning: <cmd>: nothing changed -- no rule fired and the focus did not move.
  The step was NOT recorded.`
  **What discriminates a real move is the deduction GRAPH plus the focus NODE** --
  a node posted, an inference recorded, an arrow written, something grounded; or else
  the focus moved. Not the goal formula (a `mac-h` lands a hypothesis and leaves the goal
  alone; a branching tactic can leave it alone too), not the assumption list (mirror
  image), not the open-leaf count (`ass` closes one and hands focus to another; a
  one-premise rule leaves the count put). And a pure focus move -- `focus`, `focus-id`,
  `dk-focus!` -- writes nothing into the graph and is nonetheless a real step, which is
  why the focus half is there.
  This is STRONGER than the in-arrow test this file names two bullets up
  (`(null? (sequent-node-in-arrows n))`): that one is right about one primitive on the
  focus node and wrong about everything else -- it calls a hypothesis-side rewrite inert
  (the rule fired on a node the focus is not) and calls a re-visited node a firing (the
  in-arrow was already there). Keep the in-arrow test for a per-step "did THIS rule fire"
  check inside a composite; the boundary uses the graph.
  **One surface tactic BYPASSES the boundary and had to be wired by hand**, and it is the
  one that found the only real instance in the tree. `to-binary` / `to-nary` drive `mac`
  in a saturation loop inside `quietly`, so the inner `mac` warnings are swallowed: a
  saturation with nothing to saturate was completely silent -- no warning, nothing
  recorded, an unchanged goal redisplayed. They now take the same mark and report through
  the same notice, and on the first run that reported **32 declines per library load, all
  of them from `in-rr`**, which opens with an unconditional `(to-binary)` as a speculative
  "push the arithmetic onto the structure surface first" step that most typing goals have
  no arithmetic for. That call is now `quietly`, which is what a speculative pre-step
  inside a composite should always have been: the notice is a soft warning, so `quietly`
  suppresses it exactly as it suppresses every other.
  **After that fix: zero inert notices over the whole library load**, so no script, no
  `*live-trace*` and no `qed` bill moved. `*vnb-inert-count*` is the tally and
  `*vnb-inert-at-load*` is it frozen at the end of load.scm -- the suite asserts THAT one,
  since the live counter goes on rising through the suite's own deliberate no-ops. It
  counts notices ISSUED, not inert calls detected, so it equals
  `grep -c "nothing changed"` over the log: a speculative pre-step that declines under
  `quietly` is not a dead step anyone took, and counting it would make the tally disagree
  with what the log shows. This is the SILENCE half, and it is not optional -- a notice
  that fires on every command is as useless as none.
  Note what the notice does NOT catch, because those cases are already loud: the dozen
  silent no-ops this file lists are all soft WARNINGS at the `cmd-*` layer (`subst` with
  nothing to rewrite returns #f from `pi-eq-subst!`, `mac-h` on a functoid name warns
  `unknown theorem/macete`, `detach!` on an antecedent warns). The tree had been guarding
  its known no-ops one tactic at a time -- `cmd-mac-h*` returns a warning rather than
  `ps0` "so the surface wrapper records no no-op", in its own words. What the boundary
  closes is the residual FOURTH outcome, which nothing else was watching and which every
  tactic written from here on gets for free.
* **`backup-one` (alias `undo`) is the undo, and a STATE STACK is not what it is.**
  There is exactly one `<proof-state>` object per proof: `start-proof` (proof-commands.scm)
  is its only constructor, every `cmd-*` mutates it through `set-proof-state-focus!` and
  returns THAT SAME OBJECT, and `vnb--run!`'s `(set! *ps* result)` therefore assigns `*ps*`
  the value it already had. Pushing the old `*ps*` on a stack pushes the object about to be
  mutated and restores nothing. (interactive.scm's own `to-binary--saturate` comment had
  half of this: "`(eq? *ps* ...)` never changes because tactics mutate `*ps*` in place --
  repeat/orelse rely on that identity and so silently run once, a separate latent bug".)
  The state lives in the deduction graph, so the rollback is there. `deduction-graphs.scm`
  now journals the only four writes there are -- `dg-add-sequent-node!`,
  `dg-add-inference-node!`, `dg-apply-rule!` (arrows), `dg-propagate-grounding!` -- and
  `dg-rollback!` undoes the journalled per-node writes newest-first, then restores the two
  node lists and the node counter. **That is what settles the orphan-leaf question**: the
  nodes posted since the mark are DROPPED from the graph, not orphaned, so
  `proof-open-leaves` cannot count a node from an abandoned branch and `qed` cannot be
  handed a phantom obligation. Checked both ways in the suite: after backing up over a
  branching `di` the leaf count is the pre-branch count, and a proof finished after two
  backups still `qed`s `modulo 0`.
  Cost: an A/B over a full library load, same binary, machinery off vs on, was
  1m52.868s vs 1m52.518s -- nothing. The mark holds the inference list (cons-built, a
  shared tail) and the node COUNTER rather than the node list (`append`-built, so a held
  pointer would pin a whole copy); `list-head` rebuilds the prefix at rollback time.
  Two things it does NOT do. It does not restore `*fresh-counter*`, so backing up over an
  `ai`/`ew` that minted `u_4` and re-running it mints `u_5`. And it is gated on
  `*replaying?*`: no mark is taken during a replay or a copilot probe, since a probe runs
  the real tactic on a SCRATCH proof state and a mark naming that state on the live stack
  would make the next `backup-one` set `*ps*` to it. The composites that record THEMSELVES
  rather than their expansion -- `prop`, `minimize!`, `bc*`, `dk-focus!` -- take their own
  mark outside their `fluid-let`, so one script entry is one undo.
* Debugging recipe that works: `head -N` the proof file into scratchpad, append a dump of
  `(proof-leaves)` with each leaf's goal head and a distinguishing context formula, run it.
* **The peel / split / pick kit is in driver-kit.scm (2026-09-14); stop copying it.** Measured
  that day: ~90 `<prefix>-peel!`, ~40 `<prefix>-skolem!`, ~10 `<prefix>-di-var!` and a dozen
  conjunction splitters in theorem-library/, verbatim or nearly. The shared ones are
  `dk-peel!`, `dk-split-all!`, `dk-pick`, `dk-only!`, `dk-apply!`, `dk-di-var!`,
  `dk-conj-close!`, `dk-skolem!` and `dk-halve!` (given `POS-RR eps` in context, lands
  `POS-RR d`, `d + d = eps`, `d in RR`, `0 < d` and returns `d`). A driver that defines one
  of these under its own prefix is duplicating.
* **Never put `inst*!`, `inst+` or `fact` inside a `dk-landed-1` thunk**: they land the whole
  instantiation chain, so the thunk lands several formulas and `dk-landed-1` errors. Wrap
  the `detach!` alone (`dk-apply!` does this).
* **Get `d in RR` and `0 < d` out of `POS-RR d` by CITATION** -- `rr-pos-rr-in-rr`,
  `rr-lt-of-pos-rr` (theorem-library/pos-rr-bridges.scm) -- never by `mac-h 'pos-rr`, which
  deletes the hypothesis the next `inst+` needs. Four drivers carried comments about
  sequencing the unfold after the instantiation; they were all this.
* **`slot` on a VIEW built by `def-functor` has no per-slot projection** (2026-09-14):
  `install-functor-projections!` runs only for `def-constructed-functor`, so `slot 'IDEN`
  on `IDEN(COMMUTATIVE-RING-MULTIPLICATIVE-CM R)` falls through to the global last-write-wins
  accessor index and produced `NTH(3, ...)`, not `ONE(R)`. The working pattern is
  `(slot 'IDEN) (mac 'commutative-ring-multiplicative-cm) (nth-r)` -- open the view's own
  functoid list -- and then ASSERT the goal is literally `(== (ONE R) (ONE R))` before
  `qrfl`, so a drifted index cannot close it with the wrong component.
* **`slot-h` has no accessor fallback; `slot` does.** Goal-side `slot 'DIST` rewrote every
  occurrence but the one under a `VNB-LAMBDA` binder, and `slot-h` refused the hypothesis
  outright (`mac-h: unknown theorem/macete: dist`). Bridge with a one-line `have!` lane
  (`nth(2,s)(x,y) == d(x,y)` by `(slot 'DIST)(qrfl)`) and one `subst`.
* **A proof file states its theorem LITERALLY.** `(sp (make-wff (lookup-theorem 'name)))`
  works against the band -- where the support is still installed -- and dies on the cold
  load, where it has been retired. Wave 1 lost a cold load to it.
* **`else` is shadowed in the per-file environment.** A `case`/`cond` with an `else` clause
  in a theorem-library file dies with "Special keyword can't be expanded"; write `(#t ...)`.
* **`seg-mem-succ-le` drags the UNGUARDED `co-le-trans` into every bill that cites it**
  (its backward half uses it). The five-line inline -- `seg-mem-lt`, `nn-le-succ`,
  `nn-le-trans-guarded`, `nn-le-imp-neq-succ` -- is `modulo 0`; interval-card-in-nn.scm
  does it, and poly-tail-zero / pigeonhole-segments / finite-surgery could.
* **A guard that keeps the binder list byte-identical beats the citer's own hypothesis.**
  The G-side Taylor facts (taylor-g-at-a/-at-x/-in-fun, taylor-poly-in-rr) needed only
  `DFUN(f,n)` -- every derivative up to order n is a total real function -- and
  TAYLOR-DIFFERENTIABLE implies it (`taylor-derivs-in-fun`, taylor-proof.scm). Guarding on
  TD itself would have forced a new binder `a` and an `a < x` antecedent into statements
  that never mention the interval. One `fact` of the bridge in the citer lands DFUN and
  every guarded fact then auto-detaches.
* **When a proof's window is INSIDE another proof file, splice it there.** The guarded
  Taylor facts cite taylor-proof.scm's lemma block and are cited by its taylor-lagrange;
  load.scm loads each theorem-library file into its own environment, so a split would
  strand the file-local helpers. Two marked blocks ("BEGIN spliced block") sit in
  taylor-proof.scm for that reason; the originals are in archive/spliced-2026-09-14/.
* **`vnb-probe` ships one file inside one SSM command, GZIPPED since 2026-09-17** (capataz
  refuses at 97 KB of command text, not 128; a 90 KB two-file chain is 28 KB gzipped) and
  refuses over 90 KB on the wire. Its `--timeout` bounds the PROVER inside the memory slot
  (`VNB_RUN_TIMEOUT` in vnb-slot), not the wait for a slot, which once killed a probe that
  had queued four minutes. And `scratchpad/surgery/mkprobe-slim.py` wraps a chain in
  `(fluid-let ((*vnb-loading* #t)) ...)`: the per-step `show` dumps go, warnings and qed lines
  stay, and a chain that was killed at 610 s verbose ran in 69 s. And
  the tree on a worker is only as fresh as the last push: an agent that `(load ...)`s a
  file "from the tree on the worker" gets whatever was pushed, not what the primary holds.
* **IOTA definedness has no elimination rule** (found 2026-09-14 on the vector Taylor arc).
  `iota-d` runs one way -- post exists-unique, then grant the property -- and nothing lets a
  proof pass from `(IN (IOTA x p) X)` to `p[x := (IOTA x p)]`. TAYLOR-DIFFERENTIABLE-V's
  continuity conjunct says every `NTH-DERIV-V m f k` is a total map into VEC(m), i.e. the
  IOTA `DERIV-V(m, f^(k-1), x)` DENOTES everywhere, which is semantically the
  differentiability the `gof-nth-deriv` induction needs -- and the kernel cannot use it.
  The missing principle is `iota-in-elim`: `(IN (IOTA x p) X) => p[(IOTA x p)]`, a kernel
  rule or base axiom; it is the user's call (it is a foundational decision about IOTA), and
  `gof-nth-deriv`, `g-of-remainder` and `gof-taylor-diff` wait on it. The other gap under
  them is a step lemma, "a bounded linear functional composed with a vector-differentiable
  map is differentiable with derivative g(L)", whose own bricks (BLF continuity in the norm
  metric, composition of continuity across DIFFERENT metric spaces, `g(VNEG v) = -g(v)`) do
  not exist. Exact statements in the spliced block of theorem-library/vector-taylor-proof.scm.
* **A slice of a proof file probed on the band must be loaded into
  `(extend-top-level-environment *driver-kit-env*)`**, as load.scm does: the band's top
  level is the library's own environment, and a slice's `(define SF ...)` rebinds the band
  PROCEDURE `sf` (case-folded). And check `(proof-done? *ps*)` before believing a missing
  `qed` line: a slice cut short of its own `qed` looks exactly like a divergence.
* **"Max over a finite family" is `nn-finite-subset-bounded` over an IMAGE** (2026-09-15, the
  last Ascoli rung): index the family by a finite set, map each index to its threshold by a
  CHOICE lambda, `card-image-finite` makes the image finite, and the bound of that image is
  the max. No `nn-finite-max` lemma is needed. And a cover whose members carry their own
  threshold as a SEP property (`{u | IS-OPEN u and forsome n. n serves u}`) needs no
  CENTRES/CHOICE-of-centre construction: `sep-me` reads the threshold off the member.
  `compact-seq-has-cluster` wants the same shape.
* **`sep-me` CONSUMES the membership it opens**, so a `lam-b` licensed by that membership must
  fire BEFORE it, or the beta owes a leaf nothing can close. And `have!` of a claim equal to
  the focus goal has no main branch (the cut is a self-loop; exhibit the witness with `ew`).
* **The finsum floor is enumeration-independence, and it is PROVEN (2026-09-17, rake batch
  N, rake-finsum-welldef.scm, `modulo 0`).** `sum-ag-permutation-invariance` did NOT need the
  archived splice-out argument (1200 lines, eight unwarranted `delete-at-*` / `inverse-bij-*`
  axioms): the content is ONE-ENTRY REPLACEMENT (`g = gp` off `k` => `SUM(g,n).gp(k) =
  SUM(gp,n).g(k)`, peeling the top index with `sum-ag-succ` and `(a.b).c = (a.c).b`) and the
  induced permutation of `OS(n)` is phi RE-ROUTED (`rho(i) = IF phi(i) = n THEN phi(n) ELSE
  phi(i)`), never compressed, so no index shifts and no inverse. Stated over the four LAWS
  (identity-in, closure, assoc, comm) as curried hypotheses, so the comm-monoid and
  abelian-group forms are fifteen lines each. `finsum-well-defined` and its comm-monoid twin
  follow, and `finsum-insert` / `finsum-insert-ag` (finsum-insert.scm, moved below them in
  load.scm) now bill `modulo 0`. `finsum-reindex` / `-ag` stay: they need `CARD S = CARD T`
  from a bijection, which the tree cannot conclude (`card-finite-bij` runs the other way;
  `card-star-bij` is about CARD-STAR) -- a card-layer lemma via `pigeonhole-segments-gen`
  both ways. Also from batch M: `finsum-fubini` is a DOUBLE FOLD with every family a VARIABLE
  (the rectangle curried), `ni` on the row count; two `def-functor` views with the same slot
  list are quasi-equal in four lines (`cra-is-rag`: `(di) (mac A) (mac B) (qrfl)`), which
  retires a same-shape support per three lines; `mac 'FINSUM` does not rewrite under a
  `VNB-LAMBDA` binder; a stray `'` before `)` reads as "Unbalanced close parenthesis".
  `finsum-embed` stays: it is the permutation floor in another hat (an INJECTION between index
  sets), closed by a `sum-ag-support-inj` lemma stated in rake-finsum-core.scm's header.
  `INSERT-LAST` (finsum.scm) is
  unusable for its purpose: its lambda has domain NN, so it can never be in a BIJECTION out
  of ORD-SEGMENT(succ n); the proof uses an inline lambda with the right domain.
* **Convolution associativity in the monoid algebra owes `finsum-reindex-inverse`**: a
  reindexing along a pair of mutually inverse maps (not a BIJECTION term, which
  `finsum-reindex-ag` demands). Exact statement in theorem-library/monalg-is-ring.scm's
  header; `monalg-mul-assoc` stays asserted until it exists.
* **Two of the bt- shims were character-for-character primitive axioms** (`bt-nn-in-zz` =
  `nn-subset-zz`, `bt-succ-in-nn` = `nn-succ-closed`) carrying 60+ bills each. The
  duplicate audit compares only against PROVEN theorems; it should compare against the
  primitive and definitional shelves too.

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

## Where a driver helper lives

**Every proof-driving Scheme procedure is either in `driver-kit.scm` -- loaded before any
proof -- or is local to the file that defines it.** There is no third place.

`load.scm` enforces the second half: once `driver-kit` has loaded, each `theorem-library/`
and `calculus/` file is loaded into a fresh `extend-top-level-environment`. A driver's
top-level `define`s stay in its own frame; its `set!` of `*ps*` still reaches the real
binding, and it still sees every tactic, every macro (`bc*`) and everything `driver-kit`
defines. So a stray `(define BC '(succ p))` now breaks only its own file.

Before this, both halves were false and nobody had said so: `proof-leaves` and `any-pred`
were defined *only* inside `theorem-library/nn-least-element.scm` -- a proof script -- and
used by `interactive.scm`, `macetes.scm` and eighteen drivers; `deriv-constant-proof.scm`
exported a thirteen-procedure `dc-` kit to nine drivers, under a comment calling it
"file-local". It worked only because Scheme resolves free variables at call time.

If exactly one file needs a helper, define it there with the file's prefix. If two do, it
belongs in `driver-kit.scm`.

## Layout

    structure-library/   definitions, structures, vocabulary, warranted supports
    theorem-library/     proofs that reach (qed ...); loaded, gated, counted
    calculus/            probes and stress tests; MOSTLY not in load.scm -- but
                         `calculus/finite-ball-subcover-proof` IS loaded (load.scm:787),
                         and load.scm's per-file environment containment covers
                         `calculus/` exactly because such files can be loaded
    reference/           MIXED, and the distinction matters.  Most of it is GENERATED
                         at load (PSS.md, THEOREMS.md, GLOSSARY.md, DEFINITIONS.md,
                         PROOF-DEBT.md, DEBT-BUNDLE.md, TACTICS.md, ...) -- never
                         hand-edit those, the next load overwrites them.  Five are
                         HAND-WRITTEN and always were: LIBRARY.md, KERNEL-RULES.md,
                         KERNEL-MAP.md, REVIEW.md, USABILITY-REVIEW.md, VNB-TEST.md.
                         `build-reference-html.py`'s DOCS list is what reaches the
                         browser, and a .md absent from it is on disk and reachable
                         from nowhere -- which is what KERNEL-RULES.md was for months.
    scratchpad/          throwaway drivers (untracked)

Also on disk, not described above: `prove-scripts/`, `stress-tests/`, `examples/`,
`structure-notes/`, `archive/`, `printouts/`, `emacs/`, `docs/`, and a SECOND
scratch directory `scratch/` alongside `scratchpad/` (both in use; no rule
distinguishes them).

**Load order matters.** A file using `sp`/`qed`/`make-wff` must come after `interactive`
and `proof-debt` in `load.scm`. Misplacing it gives "Unbound variable: make-wff".

## Library-build policy

New mathematical facts are added as **warranted supports** (`support` + `warrant!`),
not as kernel axioms. A `qed` prints its bill: `proven modulo {...} [trust: ...]`, the
set of asserted facts it leans on.

**The primitive shelf CAN grow, but only by an explicit foundational decision.**
`primitive` provenance (proof-debt.scm:12) is trusted base: it contributes {} to every
bill, exactly like the ~92 axioms of `make-vnb-base-theory`, which theory.scm:613 installs
inside `(fluid-let ((*current-provenance* 'primitive)) ...)`. This brief used to say the
~92 never grow. They grew, once, on 2026-07-27: the **28 ordinal axioms** of
structure-library/ordinals.scm (burali-forti, ord-le-*, ord-succ-*, limit-ord-iff,
ord-segment-*, sup-ord-*, transfinite-induction) are now wrapped the same way, by the
user's decision that the ordinals are foundational rather than owed an argument. They had
been billing as `asserted` only because `theory-add-axiom!` defaults to that
(macetes.scm:1405) and nobody had written the fluid-let. Note the distinction that makes
this NOT a loophole: a `warrant!` moves a fact from `none` to `well-known` -- a better tier
of DEBT; `primitive` says it is not debt at all. Use it only where a mathematician would
answer "because that is what ordinals are", and say so in the file.

They grew a second time on 2026-07-28, and this one is INSIDE
`make-vnb-base-theory`, so the count itself moved: **92 -> 93**. The new axiom is
`app-graph` (theory.scm, at the head of the function-space block):

    forall f, x.   (f x)  ==  IOTA y. (LIST x y) in f

"A functoid is a class; a function is a functoid that is a set." It DEFINES
application as the description over the graph, unguarded -- guarding it on `IS-FUN`
would restrict it to set-functions, which is the restriction it exists to remove.
Safe unguarded because `f` is a VARIABLE and an axiom is instantiated only at TERMS:
`UNION`, `POWER`, `FUN`, `CHOICE`, the accessors and every `def-functoid` head are
constant heads, and `CARR` alone is not a term. Operators are syntax, not objects.
The argument is `docs/functoids-and-functions.md`.

It is **named-only** and has to be: its left-hand side is a bare application with both
sides schema variables, so as a live macete it would rewrite every application in every
goal into an `IOTA`. `declare-named-only!` (macetes.scm) is the new facility that says
so -- distinct from S-10, which catches a rewrite that is UNSOUND; this catches one that
is sound and ruinous to fire automatically. It suppresses the `-rev` companion too.
Adding it moved nothing else: 219 proven, every bill unchanged, every gate still ok.

The shelf grew a THIRD time on 2026-07-28: **`image-set`** (replacement,
structure-library/injection.scm) is now wrapped `primitive` too, by the user's decision
that the image of a set under a class function being a set is what sets ARE. It was the
SOLE entry in the bills of `ord-no-injection-into-set` and, through it, **Zorn's lemma** --
both now read `modulo 0`. Catalog moved 94 -> 95 axioms and 263 -> 262 assertions, i.e. one
fact crossed columns and nothing else did.

The shelf grew a FOURTH time on 2026-08-01, and this one is much the largest: the
user's rebuild of the **arithmetic base**. `number-systems.scm` joined
`*primitive-files*` in load.scm -- the list `prover-load` wraps in
`(fluid-let ((*current-provenance* 'primitive)) (load path))`, alongside
`theorem-library/axioms` -- so its ~107 axioms (Peano closure, the ZZ/QQ/RR/CC field
and order axioms, abs) stopped billing as debt. They had been `asserted` with no
`warrant!` at all, which is exactly `trust: none`, so every arithmetic proof in the
library was billing the axioms of arithmetic as unjustified assumptions. Measured
across all 238 bills, before vs after: **81 shrank, 0 grew, 45 changed trust tier,
5 cleared to `modulo 0`**; `trust: none` bills went 96 -> 51, `modulo 0` 62 -> 67, and
the catalog columns moved 95 -> 212 axioms / 273 -> 156 assertions.

The same cleanup ADDED the axioms that say what each system IS, since the ring/field
axioms alone pinned down none of them (QQ is a model of ZZ; RR was any ordered field):
`zz-generated-by-nn` (moved in from zz-arith.scm), `qq-is-fraction`,
`rr-sup-in`/`rr-sup-upper`/`rr-sup-least` (order completeness, with `SUP` and the
predicates `RR-UPPER-BOUND` / `RR-BOUNDED-ABOVE`), and for CC `cc-i-in`,
`cc-i-squared`, `cc-generated-by-rr`, `cc-conjugate-fixes-rr`, `cc-conjugate-i`.
`qq-dense-in-rr` is the one that is NOT in the base: it needs `<` and `POS-RR`, which
do not exist until order-predicates.scm, so it lives there and stays `asserted` --
honest, since density is a theorem of the base rather than part of it.

A LATER FINDING of the same cleanup, 2026-08-01: **binary minus had no axiom at all.**
Every minus axiom was UNARY (`rr-neg-closed`, `rr-neg-inverse`, ...), while the parser
emits binary `(- x y)` for "x - y"; nothing said `u - v` was a difference. The only
statement about that head was `rr-sub-in-rr`, a `well-known` support that read like a
restatement of `rr-add-closed`. It mattered because **`ineq` -- a TRUSTED oracle --
"linearizes over + - *"**, so it was reading a meaning the theory declined to state.
number-systems.scm now carries `binary-minus-def` (`(- a b) == a + (- b)`), stamped
`definitional` and `declare-named-only!` -- as a live macete its left side matches every
difference in the library. `rr-sub-in-rr` is now PROVEN `modulo 0` in
theorem-library/binary-minus-laws.scm, and that alone shrank **ten** bills (the whole
differentiation/MVT/Taylor arc), because every one of them differences two reals.
The same question was open for `/` and is now CLOSED the same way (verified
2026-08-04): number-systems.scm:107 carries `binary-divide-def`,
`(/ a b) == a * recip(b)`, stamped `definitional` and `declare-named-only!`
(its left side matches every quotient in the library, so firing it live would
rewrite all arithmetic into recip form). The 14 quoted supports that carry a
literal `/` head -- `bdd-fn-*`, the `product-metric` weights, `young-inequality`,
`holder-finite`, `amgm-2-sqrt`, `sqrt-rpow` -- are therefore about the real
quotient now, not an uninterpreted binary operator. Writing `recip` directly is
still the better habit in new statements.

Two consequences worth keeping in view. **The archimedean property is now derivable**
(`nn-unbounded-in-rr` in order-predicates.scm was re-tiered `well-known` -> `informal`
on that basis; `rr-pos-halvable` was proven 2026-08-17 and `rr-le-all-pos-nonpos`
2026-08-31, leaving `rr-pos-shrink` as the last of the five still asserted). And **numeric literals are now exact rationals**: parser.scm's `p--exact-num`
reads every literal with the `#e` prefix, so `0.1` is `1/10` -- NOT
`(inexact->exact .1)`, the dyadic value of the double. arith-eval.scm's sound-arith
gate stays; its remaining job is rejecting inexactness arithmetic PRODUCED
(exp/sin/cos/magnitude), which is a different thing from a literal that was read.

The `card-*` axioms (cardinality.scm) were listed here as "still asserted, awaiting the
same call". That is STALE, and the truth is worse than either state: **the shelf is
SPLIT** (measured 2026-08-04). `primitive` -- so contributing {} to every bill --
are `card-empty`, `card-finite-bij`, `card-image-injection`, `card-in-ord`,
`card-insert`, `card-segment`, `card-union-disjoint`. Still `asserted/well-known`
are `card-singleton`, `card-subset-nn`, `card-power-nn`, `interval-card`,
`interval-card-in-nn`. So `card-insert` (add an element, the cardinal goes up) is
trusted base while `card-singleton` (a one-element set has cardinal 1) is debt.
No decision produced that split; it is the residue of two sessions.

It matters more than the tidiness suggests, and the reason is in cardinality.scm's
own header: **CARD is AXIOMATISED, not defined.** The intended meaning -- the least
ordinal in bijection with X -- is stated there in prose and declined in the code. So
`primitive` here does not say "this is what cardinality IS" the way it does for the
ordinals; it says "we are assuming the theory of cardinals", and no bill records it.
Either define CARD (the L1/L2 route in the Zermelo ladder makes that possible) or
demote the seven back to `asserted` + `warrant!` so the assumption is visible.

**One obstacle to defining CARD is now gone (2026-08-12): `interval-card-in-nn` is
GUARDED.** It read `forall a, b. CARD(INTERVAL(a,b)) in NN`, which a defined CARD makes
FALSE -- INTERVAL(1, b) for a non-natural b is all of NN, whose cardinal is omega -- so
the unguarded form blocked the definition outright. It now carries `(IN b NN)` on the
UPPER bound alone (matrix.scm), and the guard is not free: 34 `fact` citations across 13
proof files. 7 already had the typing from their own premises; 26 now land it with
`mat-rows-in-nn` (theorem-library/mat-basics.scm -- `IN Q (MAT m n X) => IN m NN`, which
is why that file exists) off a matrix already in context, and border-mult's `[1, succ q]`
citation lands it with `nn-succ-closed`. The matrix statements type no dimension
(matmul-assoc quantifies `m n k l` with premises only `IN P (MAT m n (CARR A))`), so the
typing has to come off the MATRIX; where the dimension is a data matrix's COLUMN count
the square elementary/unit matrix typed one line earlier (ELEM-F/G/H, MATUNIT: n-by-n)
supplies it, which is how the sites are reached without the column read-off mat-basics
deliberately declines to prove. Library after: 307 proven, every bill byte-identical,
suite 799/0. The failure mode here is LOUD, and that was checked rather than assumed:
delete the two `mat-rows-in-nn` lines from matmul-assoc-proof.scm and the load reports
`qed: proof is not complete; cannot install matmul-assoc` plus its cascade.

**`trust: none` is the WEAKEST tier.** `*pd-trust-order*` (proof-debt.scm) is
`(none hand-wave well-known reference informal proof)`, worst to best, and
`debt-trust-level` reports the worst leaf. It is literally
`(cons 'none *warrant-kinds*)`, so the ranking cannot drift from macetes.scm.
Note that `informal` OUTRANKS `reference` and `well-known`: `informal` means a
rigorous paper-proof exists (just not mechanized), which beats both a citation
nobody has checked and a textbook fact asserted with no argument at all.
`none` means *some leaf has no `warrant!`
at all* -- "scarier than a hand-wave: nothing was even claimed to justify it", as the
code says. The unconditional case prints `modulo 0` and no tier at all; **that** is
the strongest thing a `qed` can say. This brief claimed the reverse until 2026-07-10,
and the misreading is loose in old commit messages ("PROVEN to QED (trust:none)");
proof-debt.scm and the ledger's design notes always had it right. (The brief also
had `informal` and `well-known` swapped until 2026-07-23 -- the same swap that was
fixed in proof-debt.scm on 2026-07-10 and never propagated here.)

**The shape projections.** A structure declaration generates an IS-X IFF; each
operation-property conjunct of it, unfolded, IS one of the structure's laws. Stating
those laws separately as `theory-add-axiom!` and never warranting them is what used to
drag every algebra proof to `trust: none` -- the weakest report there is, for facts that
are literally part of the definition. Three different resolutions are now in the tree,
and the difference between them matters:

* module.scm wraps its projections in `(fluid-let ((*current-provenance* 'definitional))
  ...)` (module.scm:64) and pays nothing.
* ring.scm does the same thing by a different door: a `register-provenance! ...
  'definitional` sweep over the eleven names (ring.scm:139, with the reasoning in the
  comment above it). This brief said until 2026-08-10 that ring.scm "contains no
  provenance wrap at all" -- that check looked for `fluid-let` and missed the sweep.
* group.scm's four (`group-assoc`, `group-left-id`, `group-left-inv`,
  `group-identity-in`) are, since 2026-08-10, **PROVEN** `modulo 0` in
  structure-library/subtype-laws.scm (`stl--project!`), beside `abelian-group-opr-comm`,
  which was already done that way. Same work as a provenance stamp and it says more: the
  unfold is CHECKED, not asserted to exist. `ag-cancel-right` -- whose entire bill was
  those three, and which is the deck's worked example of a proof that still owes
  something -- now reports `modulo 0`.

`abelian-group-idempotent-is-id` was the fourth case and the different one: not a
projection but a genuinely DERIVED fact, and with 14 dependents the most-cited
unwarranted leaf in the library. It is **PROVEN** `modulo 0` (2026-08-10) in
theorem-library/cancellation.scm beside `group-cancel-left`, whose shape it borrows --
`a*a = a` and `a*e = a` give `a*a = a*e`, cancel `a` on the left. It became reachable the
same day *because* of the projections above: it needs the right identity (not a group
axiom -- group.scm states only left-id -- but one commutation away in an abelian group)
and `IDEN(s)` in the carrier, i.e. `group-identity-in`.

Measured after all five (2026-08-10): **293 proven, 105 `modulo 0`, 32 `trust: none`**
(was 288 / 97 / 54). Note `\Ntrustnone` is a TALLY, not a grep: PROOF-DEBT.md's own legend
contains the string `trust: none`, so `grep -c` reports one more than the truth.

**The `nary-*` bridge, and what "the weakest leaf" costs you.** `nary-plus-2`,
`nary-times-2` and `nary-neg-1` (numeric-instances.scm) are the CONVERSE, written out, of
`binplus-apply` / `bintimes-apply` / `binneg-apply`, which sit forty lines above them in
the same file stamped `definitional` as the defining equations of the bridge symbols; the
file's own comment says so ("Arity 2 is just binplus-apply / bintimes-apply reversed").
`==` is quasi-equality, hence symmetric, so the converse of a conservative definition
introduces nothing. On the user's call (2026-08-10) all three are now wrapped
`definitional` -- individually, since they are not contiguous, and as a WRAP rather than a
later `register-provenance!` so that `install-theorem!` stamps the auto-generated `-rev`
companion too.

**Stamping those three moved 27 leaf citations and ZERO bills.** The tier of a bill is its
WORST leaf, and every proof citing those three also cites `nary-minus-2`, which was left
`asserted` in the first pass. `trust: none` stayed at 32. `nary-minus-2` was then stamped
too, on a SEPARATE decision because the argument is a different one -- it is not a converse
but a COMPOSITION: `(- x y) == x + (- y)` is `binary-minus-def` (number-systems.scm), and
the two converses rewrite the right-hand side to `binplus x (binneg y)`. `==` is a
congruence, so the chain substitutes, and every step is definitional. That single stamp
took `trust: none` **32 -> 19** and left `modulo 0` at 105 -- so `nary-minus-2` was never
any bill's ONLY leaf, it was merely the worst one in thirteen of them.

The lesson outlives the arithmetic: **reclassifying or proving a leaf buys nothing until it
is the LAST unwarranted leaf of the bills that name it.** Triage by BILL, not by citation
count -- `debt-keystones` ranks by citations and misled exactly here, putting `nary-neg-1`
(14 dependents) at the top of the list when it was worth nothing on its own. The
measurement to run first is the what-if: drop a candidate leaf from every bill and recount
the tiers (`scratchpad/nary-what-if.scm`). It has been right every time.

It happened TWICE in one day. `integral-domain-cancel-zero` was then PROVEN
(below) -- and `trust: none` again did not move, because all seven of its bills also cited
`zz-is-integral-domain`. Proving THAT took 19 -> **11**. Two of the day's five repairs
moved nothing on their own; both were nonetheless necessary, because the shadowing leaf had
to go too.

**`integral-domain-cancel-zero` was already proved -- in a file nobody loaded.**
structure-library/integral-domain-laws.scm unfolds the no-zero-divisor conjunct of
`is-integral-domain-def` and closes it, and it had sat on disk for weeks WITHOUT AN ENTRY IN
`load.scm`, so the proof never ran while integral-domain.scm went on asserting the same fact
unwarranted into seven bills. Nothing catches this: a `.scm` in structure-library/ that
load.scm does not name is simply invisible, and no gate counts files. If you write a proof
file, the entry in load.scm is half the work.

**`zz-is-integral-domain` (7 bills, the last big one) is PROVEN**, in
theorem-library/zz-integral-domain.scm, together with `zz-is-commutative-ring`. Pattern:
zz-ring-is-ring.scm's, one storey up -- unfold the defining IFF, `surface-goal!` the
accessors down to integer arithmetic, and the conjuncts fall to `crs` / `arith` / a
citation. The one piece of real content is that **ZZ has no zero divisors**, which nothing
in number-systems.scm states (there is no ZZ zero-divisor axiom and no sign or trichotomy
machinery for the integers). It is proved where the fact comes from, one system up: QQ is a
FIELD, so `qq-recip-closed` / `qq-recip-inverse` invert any b /= 0, `zz-subset-qq`
(primitive) carries the integers in, and

    a = a.1 = a.(b.b^-1) = (a.b).b^-1 = 0.b^-1 = 0

is four rewrites. `zz-no-zero-divisors` bills `modulo 0`. No induction, no order, no
descent: the integers have no zero divisors because the rationals have inverses.

`integral-domain-nontrivial` went the same way (five lines beside its sibling): it is not
an INSTANCE of a conjunct of `is-integral-domain-def`, it IS one, verbatim. The axiom it
replaced carried the comment "a conjunct of is-integral-domain-def, surfaced as a citable
theorem" -- the proof, written in prose and then not run. Watch for that species of
comment; it is the same failure as the unloaded proof file, one line long.

Three more went the same afternoon, and the pair among them is the cleanest illustration
of the shadowing rule anywhere in the tree, because the what-if PREDICTED it:

* `qq-is-ring` -- PROVEN. `theorem-library/zz-ring-is-ring.scm` is now PARAMETERISED over
  the instance (carrier, defining equation, set-hood fact, three typing axioms) and called
  for ZZ-RING and QQ-RING, rather than copied. The file's name is historical; a third
  numeric ring is one more line of instance data.
* `comm-monoid-is-monoid` -- PROVEN, one line in subtype-laws.scm (`stl--prove-pred!`, the
  abelian-group-is-group shape).
* `nn-add-monoid-is-comm-monoid` -- PROVEN, theorem-library/nn-add-monoid.scm. Those two
  were the ONLY unwarranted leaves of ONE bill (`poly-is-ring`) and shadowed each other:
  measured in advance, either alone moved nothing and the two together moved one.

**`nn-add-monoid` is where NOT to use `crs`.** Its three law conjuncts are closed by
citing `nn-add-assoc` / `nn-add-comm` / `nn-add-zero`, not by the ring simplifier: `crs`
decides commutative-RING identities and **NN is not a ring** -- it has no negation. All
three identities are true of NN, so `crs` would have closed them and nothing would have
looked wrong, but the justification would have been "this holds in any commutative ring",
which is not a statement about NN. An oracle is sound where it applies; knowing that it
applies is the caller's job.

Two driver lessons from that file, both of which cost a run: read the eigenvariables off
the GOAL, never off the context (`dk-asms` order is not the peel order -- taking the
NN-typed hypotheses in context order gives `(w v u)` where the goal wants `(u v w)`, and
`fact` then builds an instance `ass` quietly refuses); and run probe scripts with
`< /dev/null`, because an `error` inside one drops into the `2 error>` REPL and waits on
stdin forever, which looks exactly like an infinite loop.

**`principal-ideal-membership` (5 bills, the largest single one left) is `definitional`**,
stamped at source in ideal.scm. This entry used to end "-- and it is the case where a
PROOF is not available and the stamp is the settled answer". **That was wrong**, and the
counter-example is above: the functoid's unfold equation is provable `modulo 0` by
`(di) (mac 'THE-FUNCTOID) (qrfl)`, and the resulting THEOREM is what `mac-h` needs. The
stamp is still what is IN the tree, and re-tiering moves every citing bill, so it stays
until that measurement is made -- but it is a stamp of convenience, not of necessity. `def-functoid` installs only a rewrite MACETE, not a
theorem, so `mac-h` cannot unfold `PRINCIPAL-IDEAL` in an ASSUMPTION: it warns "unknown
theorem/macete" and the driver sails on with the hypothesis untouched. That is why the
axiom exists at all -- it is the only way to read a member of (a) out of the context,
which is exactly what zz-bezout-proof and spans-submodule-fg-proof do with it. And it is
legitimately definitional: the functoid unfold composed with the SEP separation schema,
both trusted base, i.e. exactly the IFF `def-predicate' would have generated had
PRINCIPAL-IDEAL been a predicate. Same treatment and reasoning as `span-membership`
(mod-seq.scm, 2026-07-10) and the five constructor membership characterisations in
definitional-reclass.scm; this one had simply been missed. Any `SEP`-bodied `def-functoid`
whose members get read out of the context wants the same one-line wrap.

End of 2026-08-10: **301 proven, 109 `modulo 0`, 4 `trust: none`**, in ten repairs, THREE
of which moved nothing on their own. The four that remain have NO shadowing left -- each
is the SOLE unwarranted leaf of its bill, so each is worth its full count:
`zz-is-euclidean-ring` (zz-bezout; needs the division algorithm on ZZ, a different piece
of work), `rr-is-metric-space` (rr-complete), and `inf-subsets-is-set` (two bills:
totally-bounded-has-cauchy-subsequence, block-family-combinatorial).

**2026-09-17: `trust: none` is ZERO.** `zz-is-euclidean-ring` is PROVEN `modulo 0`
(theorem-library/zz-division.scm: `nn-division` by induction on the dividend with the
divisor fixed, `zz-division` reduced to it at `(|a|, |b|)` with four sign cases and a
SIGNED remainder -- the Euclidean law asks only for a size bound, so no correction step --
and the law itself with `VNB-LAMBDA a_ ZZ. abs(a_)` as the degree). The axiom in
numeric-instances.scm is retired. `finsum-single-support`, the sole leaf of ten bills, went
the same day (theorem-library/finsum-single-support.scm, induction on the fold length and a
transfer along `FIN-ENUM`; the set-minus route is blocked twice over, see the driver bullets).
Cold load after both: **1415 proven, 1310 `modulo 0`, 0 `trust: none`**, suite 1220/0. And
the shadowing rule struck once more: `zz-bezout` did not clear -- it now bills exactly
`ring-add-right-id`, `well-known`, which had been hidden behind the axiom the whole time.
(Proven that afternoon in rake batch D; `zz-bezout` is `modulo 0`.) The two rake batches
that followed the same day took the tree to **1501 proven, 1397 `modulo 0`, PSS 333 -> 275**,
suite 1220/0; `submodule-fg` bills 9 leaves, all `well-known` finsum/group facts. Batch 3 the
same evening: **1549 proven, 1467 `modulo 0`, PSS 247**; `submodule-fg` bills two --
`finsum-well-defined` and `finsum-congruence`, and the second was FALSE AS STATED (see the
batch-J driver bullet). **The user chose "shape 1"** (2026-09-17 evening): the `=` conclusion
with the POINTWISE typing `forall z in S. f z in CARR(ag)` as a second antecedent, after the
equality, so every citer's `fact` keeps its arguments. Proven `modulo 0` in
rake-finsum-laws.scm (from the `==` form plus the new `finsum-type-ptwise`). The 52 bills were
transitive: only SEVEN files cite it directly (19 sites), repaired by three agents in one
pass, every bill byte-identical -- the fix at each site is one `have!` of the pointwise
typing before the `fact`, closed by `fun-apply-type-c` off a FUN typing the driver already
held (plus `interval-widen` where the summand's lambda domain is `[1, succ n]` and the index
set `[1, n]`). Spell the `have!` binder `z_`, not the theorem's `z`: `asms-find` is
alpha-aware and `z` would shadow the summand lambda's own binder. Batch 4 the same night took
the finsum FLOOR (`sum-ag-permutation-invariance`, `finsum-well-defined`), `finsum-fubini`,
`card-power-nn`, the setoid facts and the ring powers: **1649 proven, 1601 `modulo 0`, PSS
205, and `submodule-fg` and `matmul-assoc` bill `modulo 0`** -- the theorem the project was
built to prove has, for the first time, no asserted step under it.

**The rake's universe is the BILLS, and that is two-thirds blind** (the user, 2026-09-17).
The PSS holds 333 asserted supports; only 131 are on any bill. The other 202 are cited by
nothing proven, so `debt-greedy-order` scores them zero and `DEBT-BUNDLE.md` never names
them -- among them two-line facts like `ball-is-set` (SEP sethood) and 27 entries warranted
`proof`, a tier that claims a machine-checked proof exists for a fact nobody checked. The
standing instruction is to rake ALL the leaves: the 27 first, then the sethood /
membership / typing shapes (~40, one recipe per shape), then the bill-carrying leaves in
greedy order, then the rest by area.

Also deliberately left `asserted`: the arity 3-5 forms (`nary-plus-3`, ...), which are not
converses of anything -- they FIX the reading of the parser's flat n-ary node as a left
fold, and nothing else in the theory states it. They have no dependents.

**The shelf grew a FIFTH time on 2026-08-24: `nn-add-succ`** (`a + succ b = succ(a+b)`,
structure-library/nn-arith.scm), stamped `definitional` by the user's decision that Peano
recursion for `+` is part of what NN IS. It was the largest single leaf left, and by the
ranking that matters rather than the obvious one: by CITATIONS it was only third (55,
behind `entry-in-carrier` 63 and `interval-card-in-nn` 60), but by SOLE-leaf count it was
first by half again -- **20**, against 13 for `rr-le-all-pos-nonpos` and 8 for
`metric-dist-real`, and neither of the two more-cited leaves is EVER a bill's only one.
Triage by BILL, again. Measured before/after over 719 proven results: `modulo 0`
**448 -> 468**, 35 further bills shortened, NO bill grew, `trust: none` unmoved at **3**
(block-family-combinatorial, totally-bounded-has-cauchy-subsequence, zz-bezout).
`cc-complete` and `rr-complete` clear together, being the same bill; every fact Example 4.7
(`prove-scripts/drives/poly-antiderivative-drive.scm`) must cite is now debt-free, so that
drive can reach `modulo 0`. The sole-leaf ranking was then headed by
`rr-le-all-pos-nonpos` at 13 -- **PROVEN 2026-08-31**, see the raking entry below. Wrapped as a `fluid-let` at the axiom site, not a later `register-provenance!` --
which is what stamped the auto-generated `nn-add-succ-rev` companion too (the load's
`classification:` line went 17 -> **19** de-supported, two names not one).

**And the stamp is NOT free, which is why the site carries a comment saying so.**
`definitional` contributes {} to every bill, so a stamp does not merely re-tier a fact --
it makes the fact invisible to the debt ledger. number-systems.scm axiomatises `+` by its
ALGEBRAIC laws (closure, assoc, comm, `a+0 = a`) and never by its recursion, so calling
the recursion equation "definitional" ALSO asserts that the algebraically-axiomatised `+`
SATISFIES Peano recursion. That is a claim, not a definition, and it is established
nowhere in this tree. The block above the axiom states it plainly and names the exit:
construct NN's `+` by recursion, derive the algebraic laws from it, prove the constructed
operation agrees with the posited one. **Standing rule, confirmed by the user the same
day: a stamp must record its claim.** The `warrant! 'reference` was removed rather than
reworded, on the ordinals precedent -- a warrant is a better tier of DEBT, and
`definitional` says there is no debt.

**`nn-mul-succ` was measured and deliberately NOT stamped -- and the restraint PAID,
because its argument was NOT identical.** The entry here used to say it was. It is
**PROVEN** `modulo 0` (2026-08-31, theorem-library/nn-parity-proof.scm): `succ(b) = b + 1`
is `nn-succ-plus-one`, already proven there, and then `nn-distributive` and `nn-one-mul`
-- both `primitive` -- give `a * succ(b) = a*(b+1) = a*b + a*1 = a*b + a` in four
rewrites. Addition's recursion has to be ASSUMED (nothing in the tree implies it;
`nn-succ-plus-one` is proved FROM it, so the reverse move is circular); multiplication's
does not. A stamp by analogy would have assumed what a proof establishes -- which is the
argument for the one-explicit-decision-per-fact rule, now with a scar to point at.
It sits in nn-parity-proof rather than a file of its own because `nn-succ-plus-one` is
produced there and consumed thirty lines later: no separate file fits between.

**THE RAKE, 2026-08-31: the greedy what-if is MECHANIZED, and the ranking is not the
obvious one.** This file already said triage by BILL, not by citation count, and named
`nary-neg-1` as the scar. That triage is now a procedure and a generated document:
`debt-greedy-order` (proof-debt.scm) repeatedly takes the leaf that would empty the most
bills OUTRIGHT, removes it from every bill and goes again; `debt-entry-routes` attributes
each leaf of a bill to the direct citation it entered through. Both are written to
`reference/DEBT-BUNDLE.md` at load, recomputed and never stored, so the ranking cannot go
stale the way `debt-keystones` misleads. Section 1 answers "prove these N, in this order,
and N bills reach `modulo 0`"; section 2 turns a 113-leaf bill into "87 via
smith-diagonalization, 41 via free-transport" -- the arcs, not a wall of symbols.
Routes OVERLAP by construction (a leaf reachable two ways is counted under both), so the
columns do not sum to the bill; that is stated in the file.

Measured over one session with it: **981 -> 990 proven, `modulo 0` 635 -> 680**, billed
results 346 -> 310, one-leaf bills 70 -> 38. Nine facts crossed from asserted to proven,
and the ordering mattered more than the count -- `rr-le-all-pos-nonpos` alone was 20
bills, and by CITATIONS it was nowhere near the top.

**Seven of those nine fell to ONE driver, and the derivation had been written down in May
and never run.** `theorem-library/op-typing.scm` proves the codomain typing of a structure
operation in APPLIED form -- `((MUL r) a b) in CARR(r)`, `((DIST s) x y) in RR` -- for
ring ADD/MUL/NEG, commutative-ring ADD, METRIC-SPACE DIST, NVS VNRM/VADD. Every one was a
separate support whose warrant recited the same four lines ("From (op MUL (CARTESIAN CARR
CARR) CARR) + fun-apply"). The driver is: peel, `mac-h` the IS-X unfold, split, and then
either `fun-apply-type-c` directly (unary) or bridge the TUPLING first -- a structure
operation eats one pair while the parser emits the curried `(f a b)`. Two mechanics make
it work and neither is obvious:

* **`apply-tupling-2` is stated with `==`, and `subst` takes a `==` as happily as a `=`**
  (pi-eq-subst!). So the bridge is one rewrite of the goal. It has to be `==`: both sides
  are undefined when `f` is not tuple-typed, and `=` is the definedness predicate.
* **`binary-apply-type` does not exist and is not needed.** The May note said these
  closure axioms "become derivable via IS-X unfold + the typing conjunct +
  binary-apply-type"; the two pieces that would have built it (`fun-apply-type-c`,
  proven; `pair-in-cartesian`, proven) do the job directly.

`nvs-act-in-vec` has the same shape and does NOT fall to it: ACT's domain in the NVS
declaration is the scalar ring's carrier, not `CARTESIAN(RR, VEC(m))`, so the pair does
not type without the normed-field view. Left asserted, deliberately.

**`ineq` premise indices are 1-BASED** (ineq-oracle.scm:206 -- `(>= i 1)`,
`(list-ref asms (- i 1))`). A 0-based finder is in range, names the neighbouring
formulas, and the oracle then reports "goal not a linear-RR consequence" -- blaming the
goal, exactly the misdirection the 2026-08-15 skip-a-non-arithmetic-premise comment
describes one line above the check.

**Proving a fact that used to be an axiom moves it past the view specializer.**
`view-as-auto-specialize!` runs inside `def-functor`, i.e. when views.scm loads
(load.scm:195) -- long before the interactive tactics exist, so a theorem proved in
theorem-library/ (load.scm 500+) is invisible to it and its view companions are never
built. `abelian-group-idempotent-is-id-module-vector-ag` is cited BY NAME in
theorem-library/module-zero-act, so the move would have silently deleted it.
cancellation.scm already re-ran the specializer for RING-ADDITIVE-AG for this exact
reason. The trap: the unrestricted re-run installed **67** companions -- every
abelian-group theorem proved since views.scm -- to deliver the one that was needed. So
`view-as-auto-specialize!` now takes an optional SECOND argument naming a single theorem
(structures.scm), and errors on an unknown name:

    (view-as-auto-specialize! 'MODULE-VECTOR-AG 'abelian-group-idempotent-is-id)   ; 1, not 67

Reach for the unrestricted form only when carrying a whole backlog across a view is what
you mean, as the RING-ADDITIVE-AG line does.

(The companion figure "438 of 1325 asserted facts carry no warrant" was measured
2026-07-23 and is stale: 117 facts left the asserted column on 2026-08-01. It wants
re-measuring, not adjusting.)

**The continuity algebra is six-sevenths proven, and the last two cost no estimate**
(2026-08-18). `cont-transfer-ptwise-eq` (theorem-library/continuity-transfer.scm) and
`sub-continuous-at` (theorem-library/continuity-sub.scm) are PROVEN `modulo 0`, and with
them **`diff-implies-continuous` bills `modulo 0`**. Only `compose-continuous-at` and
`cont-agree-off-pt` are still asserted in continuity-algebra.scm.

Neither needed an eps/delta argument, and that is the transferable part:

* The TRANSFER is what the algebra was missing. `sum-continuous-at` concludes about the
  LITERAL term it builds, not about "any map that happens to be the sum" -- so without a
  transfer the algebra can only ever conclude about lambdas it built itself. The proof is
  two instances of the pointwise hypothesis and two `subst`; the distance is never opened
  into `abs`, so nothing in it is about RR. (It is stated at RR-MS only because that is
  where continuity-algebra states it.)
* Given the transfer, the DIFFERENCE is a composition of three theorems already in the
  tree -- `neg-continuous-at`, `sum-continuous-at`, `cont-transfer-ptwise-eq` -- plus one
  `crs` to bridge `(- (g w) (h w))` and `(+ (g w) (- (h w)))`. The retired warrant
  proposed the eps/2 route ("a difference is the sum estimate with `-' throughout"), which
  is a second copy of continuity-sum's driver. It was not needed. `neg-continuous.scm`
  moved earlier in load.scm to make this available.

Two mechanics worth keeping. **`mac-h` is destructive, so read a typing off a hypothesis
inside a `have!` LANE**: `(have! '(IN g (FUN RR RR)) (lambda () (mac-h 'is-continuous-at ...)
(split) (slot-h 'PTS ...) (ass)))` unfolds on the side branch only, and the main branch
keeps `IS-CONTINUOUS-AT` intact for the next `fact`. Done in the main branch instead, the
following `fact` silently lands an implication. And `slot-h` is destructive the same way:
in continuity-transfer.scm `(IN b (PTS RR-MS))` is needed as itself (to detach g's
delta-universal) AND as `(IN b RR)` (to detach the pointwise hypothesis), so the `inst+`
must come BEFORE the `slot-h`. continuity-sum.scm meets the same trap and solves it the
other way, with a `have!` that puts the PTS form back.

When a proof turns into a grind, that is a finding, not a failure: add the obvious
lemma to the PSS and record the obstacle. Do not slog.

**`prop` (prop.scm, 2026-08-15) is the second worked example** of that principle, and the
cheapest one to reach for: it decides whether the focus goal follows from the context by
PROPOSITIONAL logic and closes it if so. It dissolves a whole class of leaves that were
each obvious and each wanted a different hand-picked dance -- `(oi-l)(ass)` when a disjunct
is in context, `(oi-r)` plus a conjunction split when it is not, `(ai)` on a negation when
the context is contradictory, `use-em` plus two bodies when the goal needs a case. Atoms
are opaque: `x in a`, an equation, a whole `forall(...)` -- so it will NOT instantiate a
quantifier or reason about equality, and it declines with a COUNTERMODEL naming which atom
must be true and which false, which is usually the missing hypothesis. It **adds no
trust**: it decides semantically (three-valued evaluation, pruned search), then discharges
through `di`/`ai`/`oi-l`/`oi-r`/`ass`/`use-em`/`have!`/`detach!`, so a `qed` over a
`prop`-closed proof bills `modulo 0` and the recorded script is the ordinary step-by-step
proof (verified: `scratchpad/prop-debt-probe.scm`). It is in `*what-now-fire-probes*`, so
the copilot now prints `(prop) => CLOSES the goal` on such a leaf.

Two traps it hit, both the alpha-self-loop above, reached through helpers: an opening
`pbc` put `not G` in the context and then `use-em`'s own `em-prove!` re-assumed it (fixed
by checking the GOAL against the assignment instead -- no pbc at all); and splitting on the
atom of a goal that IS `(OR p (not p))` cuts the goal itself (fixed by routing that shape
to `em-prove!`). Battery: `scratchpad/prop-battery.scm`, 19 cases including five that must
NOT close.

**`contra` (contra.scm, 2026-08-15) is the third**, and it came out of a leaf the user
was driving: unfolding `make-set-membership` in a list-induction base case leaves

    nth(i,l) = x,  i <= length(l),  1 <= i,  i in nn,
    x in set,  length(l) = 0,  l in tuples(a)   |-   x in empty-set

which is closable only because `1 <= i <= length(l) = 0` is absurd. The copilot said
nothing, and the reason was worth more than the leaf. `prop` cannot see it -- the three
order facts are opaque atoms to it, and it correctly reports a countermodel. `ineq` can
do the arithmetic, but **two input-handling traps kept it out of reach**, and both are
now fixed:

* A named premise that is NOT arithmetic used to make the whole call fail. `(ineq 1)`
  closed a goal that `(ineq 1 2)` refused, where 2 was a harmless `u in rr` typing -- and
  the message said "goal not a linear-RR consequence", blaming the goal. Such a premise
  is now SKIPPED; dropping a premise can only make Fourier-Motzkin prove less, so this is
  soundness-preserving by construction.
* `ineq-atom-rr-ok?` demands an `IN _ RR` certificate for every atom of every accepted
  premise. A combinatorial context types its terms in NN, so the oracle refuses. **The
  fix is NOT to weaken the oracle** -- it is trusted, and widening what it accepts widens
  the trusted surface. `contra` DISCHARGES the precondition instead: land the `IN t NN`
  facts the context already fires (found generically by the forward-citation scan, e.g.
  `length(l) in nn` from `l in tuples(a)`), then lift each to RR by `nn-in-rr` (proven,
  `modulo 0`).

The remaining trap is the sharp one: an `=` is arithmetic in SHAPE, so `nth(i,l) = x`
gets accepted and contributes the atoms `x` and `nth(i,l)`, which can never be certified
-- one irrelevant equation in the context poisons a call whose real premises were fine.
`contra--usable-indices` therefore filters premises by the oracle's own test before
naming any. It **probes on a scratch state before committing** (there is no undo: a
composite that cut first would strand two unprovable leaves), adds no trust beyond
`ineq`'s, and is in `*what-now-fire-probes*`, so the panel prints `(contra) => CLOSES the
goal`. Four suite checks; suite 880/0.

Before adding a support, ask whether it is an *instance* of something a tactic could do.
`minimize!` (minimize.scm) is the worked example: `(minimize! '(v ...) GUARD MEASURE)` =
"choose v satisfying GUARD with MEASURE as small as possible", leaving only the two
obligations any minimization owes -- MEASURE lands in NN, and GUARD is satisfiable. It
turned `min-degree-entry` and `class-min-pivot` from `'well-known` warrants into
theorems. It uses no choice: well-ordering returns a *member* of the value set, which is
a `SEP` set, so `sep-me` recovers the witness.

## The gates on the install door

`support` and `theory-add-axiom!` install a raw S-expression. The end of `load.scm` now
runs SEVEN numbered gates; the four below are the ones on THAT door, and they are
complementary -- each catches a defect the others call well-formed. (The other three
guard different doors: `sethood-audit` is the fifth, `report-page-audit` the sixth -- both
described in their own sections above -- and `kernel-callers-audit` the seventh, below.)

* `connective-arity-audit` (audit.scm) -- FATAL. A flat `(AND a b c)` is read with
  binary-left/right, so extra conjuncts are silently dropped.
* `free-variable-audit` -- warn-only. A free name means whatever the CALLER spells it.
* `head-registry-sweep` (audit.scm, added 2026-08-04) -- warn-only. Every applied head in
  every installed formula, checked against `*constant-registry*` (expressions.scm) --
  the table `free-vars` / `subst-free` actually consult. An unregistered head is read as
  an applied function VARIABLE. `unknown-head-audit` does NOT do this job: it accepts a
  head that is in `*operators*` or on its own allowlist, and reported 0 while 71 heads
  leaked. `register-operator!` now feeds the registry, so the two tables cannot drift.
  Register a new head in `*wff-term-form-heads*` (wff.scm) if it is a TERM constructor;
  a PREDICATE gets a bare `register-constant!` beside `LIMIT-ORD`, because a predicate in
  the term-form list makes `make-wff` reject every goal that mentions it.
* `install-grading` (`install--grade!`, macetes.scm) -- warn-only, and it fires at
  install time, naming the file. It runs `validate-wff!` -- the grading `make-wff`
  applies -- over every installed formula. It grades SHAPE only: arity, and
  wff-vs-term position. The four variadic macete schemas (RESTVAR/SPLICE) are exempt
  by shape.

An eighth, `install-duplicate-audit` (load.scm, 2026-09-16, warn-only), counts theorem
names installed twice during the load. The overwrite warning had printed on every load
for weeks without anyone acting on it. The first count was seven, of four kinds:
* a definitional fact re-added as an asserted PSS entry, which changes every later bill;
* a fact asserted twice;
* a fact proven twice;
* four supports never retired after their proofs landed.

All seven were repaired, and the count is now zero.

And the seventh gate is on a DIFFERENT door -- not what a formula says, but **who may
write the deduction graph**:

* `kernel-callers-audit` (audit.scm, added 2026-09-12) -- FATAL. `dg-apply-rule!`
  (deduction-graphs.scm:283) is the sole procedure that writes an inference into a
  deduction graph and it VALIDATES NOTHING: it records the tag it is handed. So the
  trusted code base is exactly the set of procedures that call it, and nothing bounded
  that set -- `kernel-rules-audit` checks that the TAGS are documented, never which
  procedures stamp them. This reads every loaded file and counts calls in code position
  **and uses of the name as a VALUE**, the second being the escape hatch the first
  misses: `(map dg-apply-rule! ...)` moves the call site to wherever the caller lives.
  The allowlist is `*kernel-caller-files*` (8 files: `primitive-inferences`, `macetes`,
  `theory`, `arith-eval`, and the four oracles). Enlarging the trusted base now costs a
  deliberate entry there, on the same one-explicit-decision-per-fact discipline as the
  primitive shelf. FATAL on the `connective-arity-audit` precedent -- a gate goes fatal
  once its backlog is zero, and this one's backlog is zero; a limit that only warns is
  not a limit. Load line: `68 call site(s) ... in 8 file(s), all allowed; 0 value use(s)`.

  Two things from building it. **A definition's formal list is spelled exactly like a
  call**: counting `(define (dg-apply-rule! dg rule hyps concl) ...)` reported 69 sites
  in 9 files, the extra being deduction-graphs.scm, where the writer LIVES and which is
  not a caller. With formals skipped this scan and the kernel map's independently written
  one agree exactly (68 / 8 / 0), which is the cross-check worth having. And the **cost is
  I/O, not parsing**: a reader pass over all 433 files was 17.3 s, and a text pre-filter
  skipping the 422 that cannot contain the call took it to 7.4 s -- about 4% of the load.
  That floor is why `duplicate-define-audit` stays out of the load and in the suite.

Controls for the last two: `scratchpad/gate-control.scm`. A gate that passes everything
reads exactly like a clean library, so make it fail on purpose before believing it. The
kernel-caller gate's control is in the suite instead (three checks, one of them the
definition/quote/value battery), for the same reason.

**`COMP` was in none of the expression walkers** (found and fixed 2026-08-15, while
testing the binder-scope diagnostic above -- its one false positive WAS this bug). The
string `COMP` did not occur in expressions.scm at all. `{x | p}` is `(COMP x p)`, which
binds `x` in `p` and has exactly the `FORALL`/`FORSOME`/`IOTA` shape, but it fell through
to the general compound branch, so `free-vars` called the bound variable FREE,
`subst-free` rewrote it (`r := zz` turned `{r | r in a}` into `{zz | zz in a}`) and
captured into it (`a := f(r)` gave `{r | r in f(r)}`, no rename), and `alpha-equiv?` said
two alpha-variants differed. The repair is one symbol at six case labels, all of shape
`(HEAD var body)`: `free-vars`, `subst-free`, `alpha-equiv-under?` (expressions.scm),
`match-expr`, `rewrite-expr` (macetes.scm), `replace-term` (primitive-inferences.scm),
plus `COMP` in the `term?` head list.

It was LATENT, and that is why it survived: **no installed formula in the tree contains a
COMP** (measured -- 0 of the theorem table), so nothing the library does was ever walked
wrong. It was reachable only by a user who TYPED `{x | p}`, which the parser has always
accepted and the manual documents. `validate-wff!` knew COMP was a binder the whole time
(wff.scm, "COMP bound var not symbol"), so the form graded clean -- a gate that checks
shape cannot see a walker that does not know the shape binds. 10 suite checks over the
two repairs; suite 870/0.

**Nullary application is an error except for `list()` and `set_of()`** (2026-08-15, the
user's call). `h()` used to be accepted everywhere: `p-parse-arglist` returns `'()` on an
immediate `)`, `p-maybe-apply` built `(h)`, `validate-wff!`'s generic application branch
had no arity floor, and `(f)` **printed as `f`** -- so `(= (f) f)` displayed as `f = f`
while `rfl` refused it, the two sides being different S-expressions. `cartesian()` and
`power()` went the same way; `union()` was rejected, but only by the `>= 2 args` floor the
binary case wanted, not by any decision about arity 0.

The rule is enforced at BOTH doors, because `support` / `theory-add-axiom!` install a raw
S-expression that never meets the parser: `p-check-nullary!` (parser.scm, list
`*p-nullary-ok*`) and an arity floor in `validate-wff!`'s generic term-application,
predicate-application and `CARTESIAN` branches (wff.scm). `LIST` keeps its own branch with
no floor -- `(LIST)` is `[]`, the empty TUPLE, which `empty-in-tuples` and `length-of-empty`
are about; `set_of()` is `{}` and never reaches the check, its branch in `p-parse-primary`
calling `expand-set-of` directly. The conventional nullary readings of the other
constructors (empty product, empty union, empty intersection) are deliberately declined:
nothing needs them and the last is a proper class. `expr->str` (sequents.scm) now prints a
nullary application as `f()`, so the arm can no longer hide one. 17 suite checks; the whole
suite is 856/0 and `install-grading` still reports ok, which is the evidence that no
installed formula in the tree ever had a nullary application but `(LIST)`.

Related, and the reason the question came up: `length([]) = 0` is the axiom
`length-of-empty` (theory.scm:648), inside `make-vnb-base-theory` and so `primitive`. It is
not derivable -- `length-cons` characterises `length` only on a `CONS`, and
`tuple-length-zero` runs the other way -- and it carries definedness for free, `=` being
partial. Note also that `set_of(l)` is NOT the set of entries of the tuple `l`:
`expand-set-of` wraps its arguments in a LIST literal, so `set_of(l)` is `{l}`, the
singleton. The set of entries is `make-set(l)`, which is writable on the surface like any
other registered head.

**A printed term must re-parse to the term that was printed** (2026-08-24, found while
proving Example 4.7). `expr->str` printed every same-head child of `+ * and or iff`
without parentheses, on the theory that those operators are associative. They are
associative in RR; they are not associative in the KERNEL, which holds S-expressions.
So the stored `(* (* (succ m) (* (recip (succ m)) c)) v)` -- the shape a chain of
`nary-times-2` rewrites leaves behind -- printed as `succ(m) * recip(succ(m)) * c * v`,
which the reader returns as the FLAT `(* (succ m) (recip (succ m)) c v)`: a different
S-expression, so not `equal?`, so `ass` declines a goal retyped from its own printed
form. Same species as `(f)` printing as `f`, and repaired the same way -- the PRINTER
was made honest, never the comparison lenient. Widening `alpha-equiv?`/`ass` to absorb
the difference was rejected outright: it enlarges what the kernel calls the same term.

The READER held the mirror half, and it is why parenthesising alone would have fixed
nothing. `p-parse-mul` / `p-parse-add` tested the SHAPE of the left operand
(`(eq? (car left) '*)`) instead of whether this loop had accumulated it, so `(a * b) * c`
was spliced into the flat `(* a b c)` -- the left-nested term was UNWRITABLE on the
surface -- while the mirror-image `a * (b * c)` built the nested node, the right operand
never being spliced. Both loops now carry a `mine?` flag. **Unparenthesised input reads
exactly as before**: `a + b + c` is still the flat node `nary-plus-3` fixes the meaning
of, and the `/` sugar branch is untouched, so every mixed `*` `/` chain reads as it did.
Making the parser LEFT-FOLD instead -- the other way to reconcile the two -- would have
retired the flat n-ary node the `nary-*-3/4/5` axioms exist to interpret, and rewritten
the statement of every arithmetic theorem in the tree. Not that.

The only two strings in the tree whose reading changed are in `theorem-library/ell-two.scm`
(`rr-sq-add-le`, `cc-magnitude-sq-add-le`), which write
`((u * u) + (u * u)) + ((v * v) + (v * v))` and MEANT the grouping: the `have!` three lines
below each writes that nested S-expression by hand, so author and parser now agree where
they used not to. Both still `qed`, no leaves. Blast radius of the defect: 48 installed
formulas held a nested `+`/`*` and 8 a left-nested `and`/`or`; 55 of them stopped
round-tripping, and now do. The 24 with a genuinely FLAT 3-or-more-ary node still print
unparenthesised -- a suite check pins that, so a later repair cannot buy honesty by
bracketing everything. The checks test the STORED FORM, print-then-parse-then-`equal?`;
a string check cannot tell the flat node from the left-nested one, which is the defect.

**The name half of that is now REPAIRED (2026-08-24): 108 of 3891 -> 3.** Seven constants
were spelled with characters the tokenizer reads as operators, and between them they cost
105 of the 108 remaining round-trip failures. They are gone, renamed to the spellings the
surrounding axiom names already used:

    <=_ORD -> ORD-LE            (ord-le-refl, ord-le-trans, ... already said so)
    <_ORD  -> ORD-LT            (ord-lt-iff)
    RR*    -> RR-STAR           (rr-star-membership, pos-inf-in-rr-star)
    RR+*   -> RR-POS-STAR       (rr-pos-star-membership); the monoid is
                                RR-POS-STAR-ADD-MONOID
    CARD*  -> CARD-STAR         the DEFINED cardinal, companion to axiomatised CARD
    INJECTIVE* -> INJECTIVE-STAR  the class-level injectivity, companion to INJECTION

Six of the seven errored out, which is annoying but honest. **`card*` did not**:
`read-ident` stops at the `*`, `read-op` takes it, and `card*(a)` parsed as the PRODUCT
`(* card a)` -- a different term, no error, no warning. That is the case that made this
worth doing. A suite check now pins BOTH readings (`card-star(a)` is an application;
`card*(a)` is still a product) so the reason cannot be forgotten. `succ_ORD` was NOT
renamed and does not need to be: a leading letter makes `_` an ordinary identifier
character, which is why the project's own `i_`/`r_` convention works.

No old spelling survives as an alias. `alias!` (macetes.scm:1354) records human search
names for THEOREMS -- it cannot give a constant a second spelling at all -- and an alias
that could would reinstate the one thing the rename removes, `card*` included.

The rename moved NO bill (732 proven, every debt set and trust tier byte-identical; five
proven theorem NAMES changed, `card*-segment` -> `card-star-segment` and siblings, and
none of them is any bill's leaf). It also let the doc round-trip gate drop its one
exemption: `IS-MEASURE-SPACE` was exempt because its MEAS slot's codomain was `RR+*`, and
`*doc-roundtrip-exempt*` is now `'()`.

**The 3 that remain are ONE defect, and it is not a name**: `cc-i-squared` (with its
`-rev`) and `rr-bernoulli` all hold the negative integer LITERAL `-1`, which prints as
`-1` and reads back as the unary application `(- 1)`. Same species as the `(f)`-prints-as-
`f` arm: a printed form that re-reads as a different S-expression. It wants its own
decision (print `0-1`, as the imaginary unit prints `0-i`, or make the reader fold a unary
minus over a literal), and it is the whole residue.

## Shipping

`~/prover-src.tar.gz` is rebuilt by a Stop hook (`~/.claude/settings.json`): gzipped tar
of `prover/`, no `.git`, no `.com`/`.bin`/`.ext`. That is what "the tarball" means.
