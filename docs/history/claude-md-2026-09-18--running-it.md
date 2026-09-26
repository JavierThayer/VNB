<!-- VERBATIM copy of a section of CLAUDE.md as it stood on 2026-09-18, moved here when
CLAUDE.md was trimmed to its operational rules.  Nothing was edited.  The dated findings,
measurements and case histories behind each rule in CLAUDE.md are in this text. -->

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

