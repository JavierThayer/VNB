# Comparing two bands: `vnb-band-compare` and `band-dump.scm` (2026-09-23)

Step 5 of the band-extension plan (`scratchpad/triage/extend-band-plan.txt`). The
extension of a band (`prover --extend-band`, docs/extend-band-2026-09-23.md) is accepted
only if a cold load of the same tree produces a band that says the same things. This note
describes the instrument that decides "the same things", what it compares, what it
deliberately does not compare, and the two controls run on 2026-09-23.

## 1. Invocation

    vnb-band-compare WORKER BAND_A BAND_B [--detach] [--heap BLOCKS] [--timeout SECONDS]
    vnb-band-compare WORKER --wait JOB
    vnb-band-compare --local BAND_A BAND_B            (run on the worker itself)

`BAND_A` and `BAND_B` are paths on the worker; a bare file name means
`/home/ubuntu/prover/NAME`. From the primary the script:

1. pushes `band-dump.scm` to the worker's `/home/ubuntu/prover/` and compares its MD5 on
   both sides; a mismatch stops the run (exit 2);
2. on the worker, takes both probe slots (the lock files of `vnb-slot` and `vnb-suite`),
   copies `band-dump.scm` to `/home/ubuntu/probes/band-compare/bc/` and compiles the copy
   there (the tree receives no `.com`); if the compile fails it runs the source and says so;
3. restores each band in turn,
   `mit-scheme --heap 200000 --band BAND --quiet --load .../bc/band-dump.com`, under
   `vnb-metrics-run --job band-dump` (one ledger row per band);
4. requires each dump to end with its `= end` line, diffs the two CONTENT dumps and the two
   HISTORY dumps, and prints the digest.

Exit status: 0 when the content dumps are identical (PASS), 1 when they differ (FAIL), 2
when a dump could not be produced, 124 from `--wait` while the job is still running. The
files remain on the worker in `/home/ubuntu/probes/band-compare/`: `a.content`,
`b.content`, `a.history`, `b.history`, `a.raw`, `b.raw`, `a.log`, `b.log`,
`content.diff`, `history.diff`.

The digest contains: the count lines of both bands, marked `!!` where they differ; the
names present in only one band and the names whose line changed, with the changed field
names; the registry, list and gate lines present in only one dump; the size of the
history diff and its session-counter lines; the first 60 lines of the content diff; the
wall time of the two dumps; the metrics lines; the verdict.

## 2. What the content dump records

`band-dump.scm` reads every table through a sorted key list and prints every value with
its own printer `bc-canon`, which never prints an address or a hash number:

* an uninterned symbol (a gensym; the schema variables of every elementary macete are
  gensyms) prints as `%gN`, N being its order of first occurrence within the value;
* a compiled procedure prints as its compiled-code file (relative to the prover root) and
  entry index, followed, to a bounded depth, by the variables and values of its closure
  frames up to the first top-level environment; an elementary macete therefore prints as
  its name, schema variables, conditions, source and replacement patterns;
* a record prints as its type name and fields; a hash table as its sorted entries; any
  other object by its kind only;
* hashes are the first 16 hexadecimal digits of the MD5 of the printed text.

Sections of `PREFIX.content`, in order:

| line | content |
|---|---|
| `C label value` | theorem, macete, proof, proven-name, bill, `modulo 0` and PSS counts; companion counts; theorems without a recorded source; the strict marker `*vnb-band-strict?*`, `*vnb-band-files*` and `*vnb-band-file-hashes*` (printed `absent` in a band built before E1's change); `*install-duplicates*`, `*vnb-qed-failures*`, `*vnb-qed-holes*`, `*vnb-load-failures*`, `*vnb-keep-going?*`; the rule-checker refusal count, `*dg-check-inferences?*`, `*dg-trusted-rule-heads*`; `*vnb-loading*` and whether a proof state is live |
| `G gate count hash` | the end-of-load audits that read only the band, re-run in the dump: asserted- and proven-duplicate, connective arity, free variable, sethood, case fold, install grading, proof cycle, rests-on, PSS topics, reference glosses, functoid binder, constant binder, accessor index, accessor type, structure and statement satisfiability, domain clash, functor obligations, binder walker, unproven proof warrants |
| `N name field=value ...` | one line per name (below) |
| `T table key hash` | `*functoid-registry*`, `*operators*`, `*constant-registry*`, `*installed-binder-names*`, the structure, accessor, instance, view and functor tables, `*books*`, `*notation-profiles*`, `*prep-methods*`, `*accessor-display*`, and the axiom list, theorem table, constant table and definition list of `*current-theory*` |
| `L list count hash` | `*proven-theorem-names*`, `*support-theorem-names*`, `*named-only-macetes*`, `*inert-macetes*`, `*named-only-late-declarations*`, `*install-intentional-redefinitions*`, `*install-validation-failures*`, `*case-fold-define-collisions*`, `*page-audit-results*` (as sets), and `*vnb-files*` (in order) |

The names are the union of the keys of the theorem, macete, provenance, bill,
citation-graph, oracle, script, warrant, topic, alias, gloss, anchor, rests-on,
certification and source tables and of the proven and PSS lists. A `-rev` companion
whose forward name is present is not given a line of its own: its complete line is hashed
into the forward's `rev=` field. The fields of a name line:

| field | source |
|---|---|
| `stmt` | the formula in `*theorem-table*` |
| `mac` | the procedure in `*macete-table*` |
| `rev` | the hash of the `-rev` companion's own complete line |
| `prov` | `*provenance*` (absent printed `-`, not the default `asserted`) |
| `src` | `*theorem-source*`, relative to the prover root, extension removed |
| `vsrc` | `*view-specialized-source*` |
| `cites` | `*proof-citation-graph*`, the immediate citations, sorted |
| `debt` | `*proof-debt*`, the bill, sorted (`{}` is `modulo 0`) |
| `oracles` | `*proof-oracles*`, sorted |
| `script` | the recorded script, with counter-minted names relabelled (below) |
| `warrant`, `topic`, `alias`, `gloss`, `anchor`, `restson`, `cert` | the per-name entries of `*warrants*`, `*pss-topics*`, `*theorem-aliases*`, `*glosses*`, `*reference-anchors*`, `*rests-on-graph*`, `*certifications*` |
| `flags` | membership in the proven list, the PSS, the named-only list, the inert list, the late named-only list |

A value absent from its table is printed `-`, so a table the retraction failed to clear
shows as a changed field.

## 3. What is not compared, and why: the history dump

Some state of a band is a function of the ORDER in which things were loaded, not of the
tree. It goes to `PREFIX.history`, which is diffed and reported and never decides the
verdict:

* per proof: the value of `*fresh-counter*` at its `sp` (`*proof-start-counter*`), the
  raw recorded script, the mint record `*proof-mints-table*`, the length of the live
  trace, the recorded extension of the source file (`.scm`, or none when the file was
  loaded by its stem and resolved to `.com` or `.scm`), and whether the fingerprint memo
  holds an entry;
* per session: `*fresh-counter*`, `*dg-checked-count*`, `*rules-applied*`,
  `*sp-counter-snapshot*`, `*session-log*`, `*vnb-load-times*`, `*vnb-stale-com*`, the
  inert counters, `*install-duplicates*`.

The recorded script of a proof contains the eigenvariables its steps minted, named from
the global counter (`b_6420`, and, when a minted name is minted from again, `x_6454_2`).
Every proof loaded after a point where the tree differs starts from a different counter
value, so its raw script differs although the proof is the same. The content dump
therefore hashes the script with every interned symbol that ends in one or more
`_<digits>` groups renamed to `BASE_#k`, k being the order of first occurrence in that
script. The renaming is injective within a script, so two scripts that differ in anything
but the counter values still differ.

The live trace is not printed: it holds every step's goal and context, and printing it
cost about 80 ms per proof. Only its length is recorded.

`kernel-callers-audit` is not re-run: it reads the source files on the worker's disk, not
the band.

## 4. Controls, 2026-09-23, worker-02

Band A in both controls is worker-02's `/home/ubuntu/prover/vnb.band` (strict cold build of
the batch-22 tree, 19:04 UTC, 2700 proofs). Band B of control 2 is worker-04's band
(strict cold build of the batch-22 tree without `theorem-library/regulated-has-primitive.scm`,
18:55 UTC, 2697 proofs, MD5 `e308d82a8b9757ff557ba94de41206cc`), copied to
`/home/ubuntu/probes/band-compare/bands/vnb-worker04.band` on worker-02 through the
primary (an SSM tunnel to worker-04 and `rsync`, then `capataz push`; MD5 verified at both
ends; worker-04 was only read).

**Control 1: the same band, two sessions.** `vnb-band-compare worker-02 vnb.band vnb.band`:
the two content dumps are byte-identical (MD5 `a146e39685dd5e96d21d03ddeca105d2` for both,
first run), and so are the two history dumps. Repeated after every change to the dump
file, including the final one, and once with `--local` on the worker: PASS each time.

**Negative control.** One restore of band A with three one-entry mutations applied before
the dump (one citation removed from `compact-image`'s citation list, `nn-add-comm`'s
macete replaced by an inert procedure, the owner of the binder `rhpc_` changed). The diff
against the unmutated dump is exactly three lines: `compact-image` (field `cites`),
`nn-add-comm` (field `mac`), and the `*installed-binder-names*` entry for `rhpc_`.

**Control 2: batch 22 against batch 22 without one file.** FAIL, as it must be, and the
difference is confined to the one file:

* names: exactly `primitive-family-normalised-choice`, `primitive-shift-const`,
  `regulated-on-has-primitive` are present only in A; no name is present only in B; no
  name common to both has a changed line;
* counts: theorems 5242 / 5239, macetes 5478 / 5475, proofs, proven names, bills and
  `modulo 0` 2700 / 2697, names 5484 / 5481;
* the three theorems' entries in the theory record's theorem table (count 2776 / 2773);
* the set hashes of `*proven-theorem-names*` and `*page-audit-results*` (2700 / 2697);
* `*vnb-files*` (653 / 652 entries): load.scm itself differs between the two trees;
* seven entries of `*installed-binder-names*` (`rhpc_`, `rhpf_`, `rhpff_`, `rhpg_`,
  `rhpgf_`, `rhpk_`, `rhpy_`), the binders the file's statements introduce, owned by its
  theorems.

Every gate line, every registry other than the binder owners, and the line of every other
name are identical. The history diff has 125 lines: 58 proofs loaded after the missing
file start from a lower counter (16 lower for `compact-image`) (in 28 of them the raw script and the mint record
differ as well, in one only the mint record), and `*fresh-counter*` (14264 / 14232),
`*sp-counter-snapshot*` and `*dg-checked-count*` (530995 / 530097) differ.

A first version of the dump relabelled only ONE trailing `_<digits>` group; control 2 then
also reported the scripts of `compact-image`, `reflect-image-countable`,
`reflect-image-finite` and `trace-opposite-subset` as changed. Each holds a doubly minted
name (`x_6454_2` against `x_6438_2`). The relabelling now strips every trailing group, and
those four lines are identical.

## 5. Cost

One dump, band restore included: 45 to 47 s wall on a t3.medium, peak RSS 2.28 GB, which is
why the two restores run one after the other and hold both probe slots. A compare from the
primary (push, MD5 check, compile, two dumps, diff, digest): 1 min 50 s. Content dump 1.4
MB, raw file 12.5 MB per band. Interpreted, the dump took about 7 minutes per band; the
cost was the printer run on proof scripts and live traces, and a quadratic string join.

## 6. What a band carries that is not a function of the tree

From the controls: the eigenvariable counter and everything named from it (the start
counter of each proof, the raw recorded scripts, the mint records), the inference count of
the rule checkers, the extension under which each theorem's source file was recorded, and
the absolute prover path in every recorded source. The dump normalises the path and the
extension and relabels the scripts; the rest goes to the history dump.

One table is a function of the load ORDER and is compared in content, deliberately:
`*installed-binder-names*` maps each binder name to the FIRST installed theorem that bound
it. A cold load assigns the owner by load order. An extension that deletes the entries
owned by a retracted theorem, and whose reloaded file no longer binds that name, leaves
the entry absent where a cold load would name the next theorem in load order that binds
it. The compare reports such a divergence as a changed `T *installed-binder-names*` line.
