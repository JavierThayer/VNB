# The sliced exam (design note, 2026-10-01)

## 1. The invariant

A sliced exam over K workers must leave on the primary EXACTLY the certificate store that one
serial exam (`VNB_CERTIFIED=off ./prover --build-band`) of the same tree leaves: the same
files, and in each file the same records (statement hash, cites, defs, uses, own-oracles,
bill, oracles, kernel hash), in the same order. The band built from that store must be the
band a certified build of the serial store gives, and the suite must pass from it. The
library's structure and load order are not touched: every worker loads the whole list in
order; only the set of files whose proofs RUN differs between workers.

Byte equality of the store is a meaningful test: since 2026-09-30 a record carries no date
and no host (certificates.scm:319-322), so an exam that changes nothing rewrites nothing.

How it is checked. On a validation night a fifth worker runs the serial exam of the same
tree. Then (a) `diff -r` of the serial store against the merged store must be empty;
(b) `vnb-band-compare` (docs/band-compare-2026-09-23.md) between the certified band built
from the serial store and the certified band built from the merged store must report zero
content differences. The serial exam's OWN band is not the comparand: band-dump records
provenance per name, and that band says `proven` where a certified band says `certified`.
(c) The suite runs from the merged band and prints `0 failed`.

## 2. The loader mode: `VNB_CERTIFIED=slice`, `VNB_EXAM_SLICE=<file>`

`<file>` lists load-list keys, one per line. `cert-mode` (certificates.scm:89-95) accepts
`slice`; `cert-load-proof-file!` (certificates.scm:798-807) dispatches:

* a key IN the slice: `cert--load-off!` (certificates.scm:810-822), exactly as `off` does --
  every proof runs, through `load` of the fresh `.com` or the `.scm`; the file's certificate is
  written, or deleted when the file installed nothing (certificates.scm:819-821);
* a key NOT in the slice: `cert--load-certified!` (certificates.scm:847) in `on` behaviour,
  with the write at certificates.scm:911-914 suppressed for that file.

The page audit needs no change: `page-audit!` walks `*proof-script-table*`
(page-audit.scm:108), which holds a script only for a proof that ran; a certified install
writes none (certificates.scm:418-427). Each slice therefore audits its own proofs, plus the
39 generated projections and functorials that have no certificate file and are proven on
every load.

An INVALID record outside the slice. In `on` behaviour `cert--on-sp-1!` proves the theorem
in place (certificates.scm:508-516), and a file whose certified pass fails is retracted and
reloaded in off mode (certificates.scm:925-930). Decision: the slice mode keeps both, PRINTS
`;VNB slice: re-proved outside the slice: NAME (reason)`, lists them at the end of the load,
carries the count in the ledger row (`outside_reproved`), and writes NOTHING for that file.
Reasons: (i) an error would lose the night to a condition the partitioner cannot see -- a
statement hash is computed by `sp` in a loaded image (certificates.scm:490-495), so no script
on the primary can predict which records are invalid; (ii) the duplicated proof is what `on`
mode already pays, bounded by the invalid set; (iii) not writing keeps the testable property
"a slice writes exactly its own files", and the owning slice proves the file in off mode
anyway. The brief's alternative ("the partitioner assigns every file whose certificate is
invalid to a slice") is vacuous -- every file is in exactly one slice -- and cannot keep other
workers from meeting the invalid record, since they load it as a predecessor.

A changed KERNEL key is the exception and is detectable offline: the kernel hash is the MD5
of the 17 key files' MD5s (certificates.scm:206-230) and every store file's header carries it
(certificates.scm:377-380). With a stale kernel hash every non-slice file goes to
`cert--load-off!` (certificates.scm:801-806) and every worker runs the whole exam. The slice
mode must REFUSE at load start in that case; what to do instead is decision D1.

## 3. The partitioner: `vnb-exam-slices K [--from LOG]`

Input: per-file seconds of the last exam. CONTRADICTION with the brief: `report-load-times`
prints only the 20 slowest files (load.scm:3683-3697, default n = 20), so the `load timing`
lines do not give a complete table. The change: under `VNB_TIME_LOAD=1` also write
`probes/load-times-<ts>.sexp` with every row of `*vnb-load-times*` (load.scm:3700-3707). Keys
outside `theorem-library/` and `calculus/` are dropped (they load on every worker); a key with
no measurement (a new file) gets the median.

Algorithm: LPT -- files by decreasing time, each to the currently lightest slice. Output: K
list files plus the predicted load of each. The lower bound is max(largest file, total/K).
With today's figures (proof files 3080 s: goursat 747, det-rows 376, det-alternating-form 230,
monalg-is-ring 161, goursat-exceptional 142, the rest 1424 s in small files):

    K   bound = max(747, 3080/K)   LPT result (small files fine-grained)
    2   1540                       ~1540
    3   1027                       ~1027
    4    770                       ~770: {goursat, ~23 s}; {det-rows, ~394 s};
                                   {det-alt, ~540 s}; {monalg, goursat-exc, ~467 s}
    5    747  (goursat binds)      ~747-760

K = 4 is the knee: K = 5 buys about 3% of proof time for a fifth worker. The weight should
be proof time PLUS that file's page-audit time; the audit is timed only as one block
(load.scm:4542), so per-file audit time is a second change (time `page--type-in` per name and
sum by `*theorem-source*`).

## 4. The driver: `vnb-exam-sliced K` (and `vnb-nightly-exam --sliced K`)

1. Refuse if the kernel hash differs from the store's (section 2, D1). Run the partitioner.
2. Start K workers; push the FULL tree to each, `certificates/` included (each worker installs
   the non-slice files from it), excluding `vnb.band` and `reference/` as today
   (vnb-nightly-exam:95); verify by md5, adding the slice list file. Record an md5 manifest of
   the primary's `certificates/`.
3. On each worker, one detached job `VNB_CERTIFIED=slice VNB_EXAM_SLICE=... ./prover
   --exam-slice` through `vnb-metrics-run`, ledger job `exam-slice`, row fields `slice`, `of`,
   `outside_reproved`, plus the `audit_s`/`gates_s`/`reference_s` keys `run-load-end!` already
   times. `--exam-slice` is `--build-band` (prover:156-230) WITHOUT the `disk-save`: a slice
   band is 595 MB that nobody uses.
4. Wait for all K (`vnb-band --wait`, as vnb-nightly-exam:106-109). Any failure fails the night.
5. MERGE on the primary. Refuse if the manifest of step 2 changed. From worker i pull only
   `certificates/<key>.cert` for keys in slice i (rsync `--files-from`; `vnb-band-pull`'s
   `--delete` of the whole directory, vnb-band-pull:47, must NOT be used); a slice key with
   no file on the worker is deleted on the primary; a file whose key is in no slice (a file
   retired from the list) is deleted, as the serial pull's `--delete` does. The store is one
   file per proof file and the slices are disjoint, so the merge is copies with no conflict.
6. On one of the K workers: push the merged store, a CERTIFIED build (`vnb-band --build`,
   205-256 s in the ledger) -- this produces THE band; none of the K slice images is the band,
   each holds a different mix of proven and certified theorems. Then the suite from it, then
   `vnb-band-pull`. Stop all workers.

THE BILL PROBLEM. A record's `bill` and `oracles` are DERIVED from its cites transitively.
In a slice, a cited non-slice theorem P is installed from its OLD record, its bill recomputed
from P's OLD cites (certificates.scm:428-446). If a tactic or kit change since the last exam
makes P's proof cite differently (statements unchanged: the case CLAUDE.md says only the
exam exercises), the serial exam writes T's bill from P's new cites and the slice from P's
old ones: the stores differ. The step-6 certified build sees it -- `install-from-certificate!`
prints `the exam's bill was ...` on a difference (certificates.scm:447-454) -- but writes
nothing for a valid record. Repair: step 6 runs with a REBILL flag that rewrites a record's
`bill` and `oracles` fields when the recomputation differs (they are not in the validity key,
certificates.scm:325-339); the cites, defs, uses and own-oracles come from a fresh run in
every case. Without it, invariant (a) fails whenever a proof's citations move.

Wall time, K = 4, today's figures. The ledger row of the serial exam (6987 s) attributes
3080 s to files, 1580 s to the page audit, 67 s to gates, 47 s to reference writers; about
2210 s is attributed to no key (untimed end-of-load blocks such as `proof-cycle-check`,
`sethood-audit`, load.scm:4214-4540, and the save of a 595 MB image). A certified build does
the whole non-proof load in 205-256 s, so most of that remainder follows the proofs.

    per slice (balanced)        optimistic            pessimistic
    certified base              205                   256
    proof files                 770                   830 (granularity)
    page audit (pro rata)       395                   500 (goursat-heavy audit)
    unattributed remainder      550 (pro rata)        2210 (fixed per slice)
    slice wall                  ~32 min               ~63 min
    + start/push ~6, merge ~3, certified build ~4, suite 7 min (ledger, 420 s)
    night                       ~52 min               ~83 min     (serial today: ~2 h 15)

GC (2314 s of the serial exam) is inside these figures; a slice heap holds about a quarter
of the proof graphs, so its GC share should fall. The pessimistic column is the one to trust
until a slice has been measured.

## 5. What a slice catches and what it does not

Load order: every worker loads the list in order, so a theorem of a later file is simply not
installed when an earlier slice proof runs -- in either mode. A certified install cannot mask
a forward citation: validity compares each cited name's hash in THIS image
(certificates.scm:325-339); an uninstalled name hashes `-` (certificates.scm:178-188), never
the recorded `T...`, so a record citing a later theorem is invalid and its proof runs. The
ORDER CHECK (extend-band.scm:508-597) is installed only by an extension (extend-band.scm:1005)
and is not needed here, as in a cold load.

Every proof runs in exactly one slice, under `off` loading, so a tactic or kit change that
breaks a proof is caught as in the serial exam. What differs is the IMAGE a proof runs in:
its predecessors were installed from certificates, as in every daytime build. Three
differences are known: the bill (section 4, repaired by REBILL); the eigenvariable counter
(`*fresh-counter*` advances less; records and pages relabel minted names, certificates.scm:20-23,
but a driver that tests a name's spelling could branch differently); provenance `certified`
where the serial image has `proven` (`*pi-provenance-of*` maps it back for definedness,
certificates.scm:598-601; any other provenance test in a tactic would see the difference).
The validation comparison of section 1 is what detects all three.

## 6. The nightly and the fleet

`vnb-nightly-exam` starts one worker (vnb-nightly-exam:80-88); `--sliced 4` starts four.
Worker-hours per night: serial ~2.3; sliced ~4 x (0.1 start + 0.55-1.05 slice) + 0.2 for
step 6 = ~2.8-4.6. At the on-demand t3.medium rate (about USD 0.04/h in us-east-1) that is
under USD 0.20 a night, within the USD 20/day cap; four instances at 06:00 UTC leave six of
the ten. A validation night adds a fifth worker for ~2.3 h. The script stops its workers
itself; the 30-minute idle stop remains the backstop.

## 7. Cost of building it

* certificates.scm: the `slice` mode, the per-file write suppression, the outside-slice list,
  the kernel refusal, REBILL -- ~3 h.
* load.scm: the full timing table to a file; per-name audit timing -- ~1 h.
* prover: `--exam-slice` (build without save; row fields) -- ~1 h.
* `vnb-exam-slices` (python) -- ~1 h. `vnb-exam-sliced` (start, push, K waits, partial pulls,
  merge, final build, suite, stop) -- ~3 h. `vnb-nightly-exam --sliced` -- ~1 h.
* test-suite checks, on the existing fixtures (`*cert-mode-override*`, `*cert-dir-override*`,
  `*cert-src-root-override*`, certificates.scm:87-112): a two-file slice build writes exactly
  those two certificates and no others; a non-slice file with an edited statement is re-proved,
  warned and not written; slices {A},{B} merged equal `off` over {A,B} byte for byte; a stale
  kernel hash is refused; REBILL rewrites a bill after a changed citation, with a control that
  fails without it -- ~2 h.
* One validation night (serial and sliced, section 1).

About 12 hours of work plus one night.

## 8. Open decisions

* D1. Kernel-key change: run the serial exam that night, or let slices install non-slice
  theorems from records whose ONLY defect is the kernel hash (scaffolding, never written)?
  Recommendation: serial for now; revisit if key changes become frequent.
* D2. REBILL in the post-merge certified build. Recommendation: yes; without it the
  invariant fails whenever a citation moves.
* D3. Validation cadence (serial alongside sliced). Recommendation: every night for the first
  week, then weekly and after any change to certificates.scm or the loader.
* D4. reference/: today the nightly pulls it from the EXAM (vnb-nightly-exam:128-131); sliced,
  it can only come from the certified build, whose pages say `certified`. Recommendation: take
  it from the certified build, and have the pages name the exam from last-exam.json.
* D5. K. Recommendation: 4; the floor (goursat, 747 s) makes a fifth worker worth ~3%.
* D6. A pre-pass certified build before slicing, so no worker re-proves outside its slice.
  Recommendation: no; report `outside_reproved` and add the pre-pass only if it is often large.
