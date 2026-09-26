# Proof certificates: a load that runs no proof (design, 2026-09-24)

The user's decision of 2026-09-24 (evening): the everyday load installs theorems from
CERTIFICATES written by a run that proved and checked them; the proofs run separately, in the
VNB test. The question that produced it: "I don't understand why a load has to include any
proofs. Isn't that the point of the VNB test that I thought was supposed to run separately?"
The answer at the time of the question: since `VNB_SKIP_PROOFS` was removed (2026-07-09) every
load re-runs every proof, because a `qed` is the only door to the theorem table and nothing on
disk holds a checked proof apart from the run; the band caches one whole load. The cold load
took 77 minutes on 2026-09-24 (2911 proofs, `docs/batch27-2026-09-24.md`).

## What a certificate is

One file per theorem-library file, `certificates/<path-of-the-file>.cert` (in the tree and in
the tarball, so the laptop receives them with the sources), one record per `qed` of the file,
in file order:

    (name STATEMENT-HASH STATEMENT
          (cites (NAME . STATEMENT-HASH) ...)     ; every name the ledger read off the script
          (bill ...) (oracles ...)                 ; what record-proof-debt! computed
          (kernel KERNEL-HASH) (date "...") (host "..."))

* STATEMENT is the S-expression `cmd-qed` installed (after `expand-destructuring-quantifiers`);
  STATEMENT-HASH is `bc-md5` of `bc-canon` of it (band-dump.scm: the canonical text of a formula,
  alpha-stable, counter-minted names relabelled).
* `cites` are the names `record-proof-debt!` read off the script (plus `*proof-hidden-citations*`),
  each with the hash of the statement that name had when the proof ran.
* KERNEL-HASH is `bc-md5` over the SOURCE text of the files that may call `dg-apply-rule!`
  (`*kernel-caller-files*`, audit.scm) and the four rule-checker files. The tactics, the kit and
  the drivers are NOT in the key: they are untrusted (every inference they produce is checked),
  so a kit change cannot invalidate a proof that was checked.
* The record is what `qed` knows at the moment it installs: nothing is recomputed from the
  graph, nothing is read from another file.

A certificate is VALID in a load when: the statement at `sp` hashes to STATEMENT-HASH; every
`(NAME . H)` in `cites` names a theorem already installed in this load with statement hash H
(load order guarantees the cited names come first); the kernel hash matches this tree's.

## The three positions of the switch: `VNB_CERTIFIED=on | off | strict`

* `on` (the default of `./prover`, `--band-if-fresh` when the band is stale, the laptop):
  a theorem whose certificate is valid is installed from it, its proof skipped; a theorem with
  no valid certificate is PROVED as today, and its certificate written when the load is of the
  canonical tree (`*vnb-write-certs*`; a probe on a worker writes none). This is the re-prove
  path: it runs only for what the certificates do not cover, and it heals the store.
* `off` (the VNB test; `prover --build-band`, the exam after an integration): every proof runs,
  every certificate is rewritten. The band it saves is the cache of THAT run.
* `strict` (a gate): certified theorems are installed, nothing is re-proved; a theorem without a
  valid certificate is listed and the load exits non-zero. It answers "do the certificates cover
  this tree?" without a single proof.

## How a proof is skipped

The unit of skipping is the proof, not the file, because 128 of 488 theorem-library files hold
their `sp` ... `qed` inside a larger form (a `define`, a `quietly`, a loop) and only 334 files
(1800 of 2911 theorems) have the two as consecutive top-level forms.

`prover-load--file` loads a proof file FORM BY FORM (read, then `eval` in the file's
environment), instead of one `load`. In `on` and `strict` modes:

1. `sp` hashes its statement and looks it up in the current file's certificate. On a valid
   record it installs the theorem (`theory-add-theorem!` under provenance `certified`, the bill
   and oracles from the record, then the same post-install steps `qed` runs from the statement:
   `register-proven-theorem!`, the `-rev` companion, view specialisation), sets the SKIP STATE
   to that record's name, and ESCAPES the current top-level form (a continuation the loader
   holds).
2. While the skip state is set, every top-level form that ERRORS is swallowed: the driver's
   tactic calls find no proof in progress and fail, a `define` whose value is a tactic result
   fails, and none of it matters. A form that succeeds (a `define` of a helper, a `notation!`, a
   `topic!`) takes effect as usual. `(qed 'NAME)` in skip state checks NAME against the record
   and clears the state; any other `qed`, or an `sp`, in skip state is an error of the loader.
3. At the end of the file the loader checks that every name of the file's certificate is
   installed. If one is missing (an `sp` never ran because the escape skipped the enclosing
   form, a helper defined between `sp` and `qed` was needed after it), the file is RETRACTED
   (`retract-theorem!` of each of its names, extend-band.scm) and RELOADED in `off` mode with a
   warning naming the file: the certified load is an optimisation with the exam as its fallback,
   never a different result.

`off` mode is the loader as it is today, one `load` per file.

## What the bill says

A theorem installed from a certificate has provenance `certified`, which the ledger treats as
`proven` for debt (its bill is the record's), and every report that counts proofs shows the
two counts apart: `N proven in this session, M certified (exam of DATE on HOST)`. A `qed` bill
line for a certified theorem prints `certified (exam 2026-09-24) modulo {...}`. The word
`proven` alone means the proof ran in this image.

## What moves

* The page audit runs over the proofs that RAN in this session (a certified theorem has no
  graph here); the exam audits all of them. This closes the extend-band step-7 question.
* `--band-if-fresh` with a stale band: a certified load (minutes) instead of a full load. The
  2026-09-24 opt-in `VNB_BAND_STALE_OK` is superseded once this lands.
* The closure rule of extend-band (reload every citer of a changed statement) is the `cites`
  check of a certificate, per theorem, done by the loader: a citer whose cited statement changed
  simply has no valid certificate and is re-proved.
* `vnb-test` is `VNB_CERTIFIED=off ./prover --build-band`: the header now says so.

## What it costs

Measured 2026-09-24 (worker-04, heap 120000): a cold load 4607 s, of which proofs ~2750 s, page
audit 1048 s, gates 55 s, reference 35 s. A certified load runs none of the first two: the
reading and `eval` of 488 files' non-proof forms (seconds each, 2 s per file measured on the
extension path), the gates and the reference writers, the certificate checks (a hash per
statement). Expected: 3 to 5 minutes, independent of how hard the proofs were to find.

## Controls (the suite)

Accepted / refused pairs for: a valid certificate skips the proof (no tactic runs: a counter);
a changed statement re-proves; a changed cited statement re-proves the citer and only the
citer; a changed kernel file invalidates everything; `strict` lists the uncovered theorem and
exits non-zero; the fallback retracts and reloads a file whose `sp` sits inside a `define`; a
probe on a worker writes no certificate; the two counts in the load summary; the bill line of a
certified theorem. And the exam itself: a cold load in `off` mode followed by a `strict` load of
the same tree installs the same theorem table (`vnb-band-compare` between the two bands: zero
content differences).
