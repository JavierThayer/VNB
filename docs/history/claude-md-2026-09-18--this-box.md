<!-- VERBATIM copy of a section of CLAUDE.md as it stood on 2026-09-18, moved here when
CLAUDE.md was trimmed to its operational rules.  Nothing was edited.  The dated findings,
measurements and case histories behind each rule in CLAUDE.md are in this text. -->

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

