# Extending the band instead of rebuilding it (2026-09-23)

This note documents steps 2 to 4 of the plan in
`scratchpad/triage/extend-band-plan.txt`: the per-name table audit and
`retract-theorem!`, the procedure `vnb-extend-band!`, and the launcher case
`prover --extend-band`. Step 5 (`vnb-band-compare`) is documented separately in
`docs/band-compare-2026-09-23.md`. The code is `extend-band.scm` (new), the
end-of-load block of `load.scm` (now the procedure `run-load-end!`), the
`--extend-band` case of `prover`, and the controls at the end of
`test-suite.scm`.

## 1. What an extension does

A band is a saved heap image produced by a cold load. An extension starts from
that image and produces the image a cold load of the current tree would have
produced, provided the tree changed only in `theorem-library/` files that load
after the containment boundary (section 4). It proceeds as follows.

1. It reads the load list `*vnb-files*` from `load.scm` with the Scheme reader
   and computes the MD5 of every listed `.scm` file.
2. It compares these against the **band record** (section 2) and computes the
   **plan** (section 4): the changed files, the refusals, the retired names and
   the files that must reload.
3. If the plan contains a refusal, it stops before changing anything. A cold
   load (`prover --build-band`) is then required.
4. It **retracts** (section 3) every retired name and every name stated by a
   file that will reload, before any file loads.
5. It loads the reload set from source (the explicit `.scm` path, never a paired
   `.com`), in load-list order, through `prover-load--file`, the same procedure
   the cold load uses for each entry (hoisted out of `prover-load--do` for this
   purpose). Proof files therefore load into a fresh environment extending
   `*driver-kit-env*`, exactly as in a cold load. While a file loads, the
   **order check** (section 5) is active.
6. After each file it compares every name that file stated in the band against
   a snapshot taken before the retraction (section 6). A changed name adds the
   files of its citers to the reload set.
7. It calls `run-load-end!`, the end-of-load block of `load.scm`, unchanged:
   the catalog and reference writers, every gate, the page audit over **all**
   stored proofs, the band record and the session reset.
8. It returns normally. The launcher then saves the image.

## 2. The band record

At the end of every load `run-load-end!` calls `xb-mark-band!`, which sets:

* `*vnb-band-strict?*` -- `#t` only when the load was not in keep-going mode,
  holds no keep-going hole (`*vnb-qed-holes*`), no failed proof file
  (`*vnb-load-failures*`), no failed `qed` (`*vnb-qed-failures*`), ran with
  inference checking on, recorded no rule-checker refusal, and recorded no
  order violation. `*xb-not-strict-reason*` holds the first defect found.
* `*vnb-band-files*` -- a copy of `*vnb-files*`.
* `*vnb-band-file-hashes*` -- `(KEY . MD5)` for every entry of the load list
  (the MD5 of its `.scm` text), for `"load.scm#rest"` (the MD5 of every
  top-level form of `load.scm` other than the `*vnb-files*` definition, as
  printed by `write`; comments therefore do not count), and for `"prover"`
  (the launcher).

Content is compared, not modification times: `capataz push --rsync` preserves
modification times and `touch` changes nothing. The hashes are computed at the
end of the load over the tree as it then stands (about one second for 653
files); an edit made to a file while the cold load that reads it is running is
not detected.

A band built before `extend-band.scm` existed has no record, and an extension
cannot start from it.

## 3. Retraction

### 3.1 The audit: every table that holds state per theorem name

The audit started from every `hash-table-set!` and `set!` of a global in the
files that load before the first proof and in the tactic files after it. The
table below lists every structure found to hold state keyed by, or listing, a
theorem name. "Full" is the retraction of a name that leaves the library;
"reload" is the retraction of a name whose file is about to load again.

| Table | Written by | Full | Reload |
|---|---|---|---|
| `*theorem-table*` | `install-theorem!` | removed | removed |
| `*macete-table*` | `install-theorem!` (also `def-functoid`, accessors: not theorem names) | removed | removed |
| `*theorem-source*` | `install-theorem!` | removed | removed |
| `*rev-companion-source*` | `install-theorem!` (the `-rev` companion) | removed | removed |
| `*view-specialized-source*` | `view-as-auto-specialize!` | removed | removed |
| `*provenance*` | `register-provenance!` | removed | removed |
| `*lemma-fingerprint-memo*` | `lemma-fingerprint` | removed | removed |
| `*proven-theorem-names*` (list) | `register-proven-theorem!` (`cmd-qed`) | removed | removed |
| `*support-theorem-names*` (list) | `register-support-theorem!` (`support`) | removed | removed |
| theorems and axioms of `*current-theory*` | `theory-add-theorem!`, `theory-add-axiom!`, `theory-add-support!` | removed | removed |
| `*proof-citation-graph*`, `*proof-debt*`, `*proof-oracles*` | `record-proof-debt!` | removed | removed |
| `*proof-script-table*`, `*proof-mints-table*` | `save-proof` | removed | removed |
| `*proof-live-trace*`, `*proof-start-counter*` | `qed--guarded` | removed | removed |
| `*certifications*` | `certify!` (re-read from `reference/certification.scm` by `run-load-end!`) | removed | removed |
| `*vnb-qed-holes*`, `*vnb-qed-failures*` | `cmd-qed` (hole mode), `qed` | removed | removed |
| `*install-duplicates*`, `*install-validation-failures*` | `install--warn-overwrite!`, `install--grade!` | removed | removed |
| `*inert-macetes*` | `theorem->elementary-macete` | removed | removed |
| `*installed-binder-names*` (binder -> first theorem using it) | `note-installed-binders!` | entries owned by the name removed (see below) | same |
| `*rkw--def-memo*` | the macete rule checker | removed | removed |
| `*pss-topics*` | `topic!` | removed | **kept** |
| `*glosses*` | `gloss!` | removed | **kept** |
| `*theorem-aliases*` | `alias!` (appends) | removed | removed, then restored in part (see below) |
| `*warrants*`, `*reference-anchors*` | `warrant!` | removed | **kept** |
| `*rests-on-graph*` (as key) | `rests-on` | removed | **kept** |
| `*named-only-macetes*` | `declare-named-only!` | **kept** | **kept** |

`*installed-binder-names*` records load-order state: each binder is owned by
the first theorem, in load order, that bound it. When a retraction removes an
owner and the reloaded file no longer binds that name, a cold load would give
the binder to the next theorem that binds it. After the reload the extension
therefore re-owns every such binder (`xb-reown-binders!`) to the theorem of the
earliest file that binds it. The order of theorems within one file is not
recorded, so ties within a file are broken by name; the table only words a
warning. (Reported by the band comparison, 2026-09-23.)

Metadata is kept in a reload retraction because the form that wrote it may sit
in a file that does not reload (`pss-topics.scm`, `reference-topics.scm`,
`founder-warrants.scm`); the reloaded file overwrites what it writes itself.
Aliases are the exception: `alias!` appends to the name's list rather than
overwriting it, so a kept list gains a second copy of every string the
reloaded file writes again. (The band comparison found exactly this on the
first extension: `rr-limit-scale` and `rr-limit-sub` carried their alias twice,
and three times after a second extension.) A reload retraction therefore
removes the alias list and saves it; after the reload, `xb-restore-aliases!`
gives back each saved string that is missing and appears literally in the
source of a load-list file that did not reload (a cold load would have it); a
string found nowhere else was dropped from the reloaded file and stays
dropped. A
named-only declaration is never removed, because it must precede the install
it suppresses and it may sit in another file.

Caches derived from the theorem table are dropped (they are rebuilt lazily):
`*chk-theorem-index*` (the rule checker's statement index, which is rebuilt
only when the table's size changes and would otherwise survive a retraction
followed by a re-installation of the same number of names),
`*what-now-head-index*`, `*what-now-membership-index*`,
`*witness-producer-index*`, `*op-fun-typing-index*`, the cite index
(`cite-index-reset!`) and `*page-audit-results*` (which `report-page-audit`
would otherwise return from cache without re-auditing).

State that is not per theorem is untouched: `*operators*`,
`*functoid-registry*`, `*constant-registry*`, `*books*`, the structure tables,
the rule-checker counters. `*session-log*` is reset by `run-load-end!`.
`*case-fold-define-collisions*` is per file: the entries of the files about to
reload (and of files removed from the list) are dropped, and the lint re-adds
what it finds.

### 3.2 The procedures

`(retract-theorem! NAME)` removes `NAME`, its `-rev` companion and the view
companions minted from it (transitively) from every table above, metadata
included, and returns an association list `((TABLE NAME ...) ...)` of what was
present and removed. When installed proofs outside the retracted set cite a
removed name, their bills now name a theorem that is no longer installed; the
procedure prints a warning naming them and appends `(citers NAME ...)` to the
result. `(retract-theorem! NAME 'reload)` keeps the metadata.

`(xb-retract-names! NAMES MODE)` is the batch form the extension uses; it
returns `(REMOVED . CITERS)`.

`retract-theorem!` lives in `extend-band.scm`, not in `macetes.scm`: no core
file changed for it, and it adds no caller of `dg-apply-rule!`.

## 4. The plan

`(xb-plan OLD-FILES NEW-FILES OLD-HASHES NEW-HASHES RETIRE STRICT VIEW)` is
pure: it reads only its arguments. `VIEW` is a pair of tables, name -> the
load-list key of the file that states it, and name -> the names whose proofs
cite it. The citers of a name are read from `*proof-citation-graph*` united
with a re-reading of each saved script (the graph drops definitional
citations; a changed definition unfold is a change). A citation of a `-rev`
companion or of a view companion is filed under the forward name as well.

### 4.1 Refusals

The plan refuses, and the extension changes nothing, when any of the following
holds.

* The band is not strict (section 2), or `VNB_KEEP_GOING` is set for the
  extension.
* `load.scm` changed outside the `*vnb-files*` list, or the launcher changed.
* A file outside `theorem-library/` changed, was added to the list or was
  removed from it. This covers the kernel, the rule checkers,
  `structure-library/`, `calculus/`, and every root file in the list, among
  them `driver-kit.scm`, `proof-debt.scm` and `extend-band.scm` itself.
* A file retained in the list moved (the relative order of the retained files
  differs).
* A changed or added file sits at or before the position of `"extend-band"` in
  the list. The theorem-library files before that position are vocabulary
  files loaded into the global environment before the proof machinery, and
  kernel files follow them; they cannot be reloaded in isolation.
* A retired name has no recorded source, or is still stated by a file that did
  not change (a cold load would install it again).
* A citer of a retired name has no recorded source or lives outside
  `theorem-library/`.
* An installed theorem has no recorded source at all (it would survive every
  extension whatever happened to its file). On the batch-22 band this count is
  zero.

### 4.2 The reload set

The certain reload set is the changed and added theorem-library files plus the
files of the citers of every retired name (a name given with `--retire`, or
stated by a file removed from the list). The plan also reports an upper bound:
the files that may join during the run, obtained by closing over the citers of
every name of every reloading file. That bound is what a purely static rule
would reload; the run reloads only the part of it that section 6 requires.

## 5. The order check

A cold load cannot use a theorem stated by a file that loads later. A band
holds everything, so an extension checks this. Every inference that brings an
installed theorem into a proof reaches the kernel's `dg-check-inference!` under
one of three rule tags: `theorem-assumption` (the statement enters the
context; the name is recovered from the statement with the checker's own
`chk-installed-theorem-name`), `macete` and `macete-hyp` (the name is in the
tag). While the extension loads file `F` at position `i`, the checkers of these
three tags are wrapped (`xb-with-order-check`): the wrapper refuses a use of a
theorem whose file sits at a position greater than `i`, before delegating to
the original checker. A statement held under two names is accepted when either
name is early enough. The refusal is an ordinary rule-checker refusal (printed,
counted, raised) and is also recorded in `*xb-order-violations*`; the extension
stops after the file. The originals are restored by `dynamic-wind` however the
load exits. Nothing in `extend-band.scm` calls `dg-apply-rule!`; the
kernel-callers gate is unchanged.

A theorem used by name without an inference (for instance a driver that reads
a statement with `lookup-theorem` in order to state a lemma) is not a use in
this sense and is not checked. A defined functoid's unfold carries no source
and is not checked.

## 6. The after-file rule (restatement by statement)

Before the retraction, every installed name is fingerprinted: statement,
provenance, bill (`debt-of`, sorted) and oracle set (`oracles-of`, sorted).
After file `F` loads, each name `F` stated in the band is compared with its
fingerprint:

* `vanished` -- no longer installed: retracted in full (its view companions
  with it), and its citers reload;
* `restated` -- the statement is not alpha-equivalent to the old one;
* `provenance`, `bill`, `oracles` -- the statement is unchanged but what a
  citer's stored bill or oracle set was computed from changed.

For every changed name, the files of its citers, and the file of every view
companion that another file minted from it, join the reload set; they load
later in the same pass, since a citer always sits after what it cites. A citer
in a file that is not a theorem-library file, that has no recorded source, or
that sits before `F` stops the run with a refusal.

A name that is new (absent from the band) has no citers. It can nevertheless
matter to a later file that specializes every theorem of a structure through a
view (an unrestricted `view-as-auto-specialize!` or a `def-functor`): a cold
load would mint a companion of it there. `xb-specializers` finds these files by
reading the sources after the boundary (on the batch-22 tree:
`theorem-library/cancellation.scm`, view `RING-ADDITIVE-AG`); when a new name
matches the view's target structure, the specializing file joins the reload set
(or the run stops, if it is not a theorem-library file).

The rule follows the lesson of `pw-antiderivative-exceptional-set`, whose
statement changed under an unchanged name on 2026-09-23: a restatement is
detected by comparing statements, never by comparing names.

## 7. The launcher

    prover --extend-band [--dry-run] [--retire NAME ...]

* `--dry-run` restores the band, prints the plan and exits without loading or
  saving: status 0 when the plan is accepted, 3 when it is refused.
* Without `--dry-run` the launcher checks that the volume holds a second band
  (the band's size plus ten percent), restores the band with the heap of a cold
  load (`VNB_EXTEND_HEAP` overrides), calls `(vnb-extend-band! RETIRE #f)`,
  turns the GC notification off and disk-saves to `vnb.band.new`. It renames
  `vnb.band.new` over `vnb.band` only when the Scheme process exited 0, the new
  file is non-empty and the log carries the line `;;VNB-EXTEND-SAVED`; on any
  other exit, and on an interrupt, `vnb.band.new` is deleted.
* The run goes through `vnb-metrics-run` with `job: extend-band`; the log is
  `$VNB_EXTEND_LOG` (default `~/probes/extend-band-<UTC stamp>.log`). The
  ledger row is `vnb-metrics-run`'s row with the fields of the Scheme side's
  `;;VNB-EXTEND` line merged in (`reload_files`, `retracted`,
  `install_duplicates`, `order_violations`, `files_s`, `total_s`, `strict`) and
  `band_replaced`; it is printed as `;;RUNS {...}` and appended to
  `~/probes/runs.jsonl`, where `vnb-suite` and `vnb-probe` keep theirs.
  (`vnb-metrics-run` itself copies only a fixed set of fields, so the merge is
  done by the launcher; `vnb-metrics-run` was not changed.)

## 8. What is tested where

The suite runs from a band and cannot build one. Its controls (the block
headed "EXTEND THE BAND" at the end of `test-suite.scm`) exercise the parts
that do not need a load; each fails on the code before `extend-band.scm`
(every new procedure is called under a guard that turns the unbound-variable
error into a failed check):

* `retract-theorem!`: lookup fails, the macete and the `-rev` companion are
  gone, the alias is gone, the name is off the PSS roster and out of its topic
  bucket, the result lists what was removed, re-installing prints no duplicate
  warning and counts none; a retraction with a live citer reports the citer.
* The plan on synthetic input: an unchanged tree reloads nothing; a retired
  name pulls in the unchanged file that cites it; a retired name whose file did
  not change is refused; a kernel change, a structure-library change, a change
  to `load.scm` outside the list, a keep-going band and a moved file are
  refused.
* The after-file rule: a same-name, new-statement re-installation reads as
  `restated` and pulls its citer's file in; an identical re-installation is no
  change.
* A dry run returns its plan and changes no table.
* The order check: a macete from a later file is refused by the kernel checker,
  the same macete from an earlier file passes, a named citation
  (`theorem-assumption`) from a later file is refused, and the checkers are
  restored afterwards.

That every control fails on the earlier code was checked on worker-04 by
running the block in an environment where each procedure and variable of
`extend-band.scm` it uses is shadowed by an unbound (raising or unassigned)
binding: 0 passed, 22 failed. From the final cold band the whole suite reads
1597 passed, 0 failed.

Only a worker run covers: reading and hashing the real tree, the retraction of
real files' names followed by their reload through `prover-load--file`, the
page audit and the gates of `run-load-end!` on an extended image, the save and
the rename by the launcher, the ledger row, and the restored band's contents.
Section 9 records those runs.

## 9. Measurements (worker-04, t3.medium, batch-22 tree plus 22-A/B/C, 2697 proofs)

| Run | Wall | Notes |
|---|---|---|
| cold load + save (`VNB_TIME_LOAD=1`), first build | 1963 s | 781 s in files; the rest is `run-load-end!` and the save |
| cold load + save, final build | 1974 s | 787 s in files; band record strict, 655 hashes |
| dry run, unchanged tree | 5 s | reload set empty, plan accepted |
| extension, one comment changed in `theorem-library/seq-limit` | 763 s | reload set 1 file, 2 names retracted, 2 qeds; GC 171 s (22.5 %) |
| the same, final code, twice (comment added, comment removed) | 765 s, 759 s | `files_s` 15 (the specializer scan included) |
| extension refused (structure-library change) | 7 s | exit 14, band untouched |
| extension failing in a pulled-in citer (a cited theorem removed) | 11 s | exit 14, band untouched |
| suite from the final cold band | 247 s | 1597 passed, 0 failed |

Inside the 763 s extension (timestamps of the GC notification lines): band
restore and plan 5 s, the reload 2 s, the catalog and reference writers 34 s,
**the page audit over all 2697 proofs 665 s**, the remaining gates 48 s, the
save about 10 s. The page audit is 87 % of an extension. An extension that
audited only the pages of the reloaded proofs would take on the order of two
minutes; whether that is sound (a page replays against the current theorem
table, so a restatement elsewhere can break an unchanged proof's page, but
every such proof's file is reloaded by section 6) is a decision for step 7 of
the plan, not taken here.

Comparisons of the extended band with the cold band of the same tree: the
E1 dump (name, statement hash, provenance, bill, citations, source, macete
presence for all 5239 names) found no difference after each extension. The E2
comparison (`vnb-band-compare`), run after two successive extensions (the
comment added, then removed, so that the tree equals the cold band's), found
the alias duplication of section 3.1 and nothing else. With the correction
(loaded into the session over the same cold band, the band's own copy of
`extend-band.scm` being the earlier one), two successive extensions of 761 s
and 764 s gave a band whose content comparison with the cold band is
identical (`PASS`); only the session counters differ (`*fresh-counter*`,
`*dg-checked-count*`, `*sp-counter-snapshot*`), which the comparison reports
as history.

## 10. Limits and hazards beyond the plan's table

* **Eigenvariable counter.** Reloaded proofs run with `*fresh-counter*`
  continuing from the band's final value, not from the value a cold load would
  have at that file. Statements, bills and pages are unaffected (pages carry no
  counter-minted literal), but minted names inside deduction graphs, live
  traces and `*proof-start-counter*` differ from a cold load's.
* **Automated search sees the whole band.** A tactic that searches the theorem
  table (backchain candidates, the what-now indices, the witness index) sees,
  in a reloaded file, theorems that a cold load would not have installed yet.
  A proof that ends up using one is stopped by the order check; a search that
  merely considers one and uses an earlier theorem is not detected, and could
  in principle behave differently in a cold load.
* **New names and unchanged later files.** A new theorem in a reloaded file is
  visible to searches in unchanged later files only in a cold load. The
  extension does not reload those files (except the view specializers of
  section 6), so a later proof whose search would now find the new theorem is
  not re-run.
* **Metadata removed from a reloaded file.** A `topic!`, `warrant!`, `gloss!`
  or `rests-on` removed from a reloaded file, for a name that stays or
  vanishes, survives in the extended band (section 3.1). The cold load of the
  integration corrects it. (Aliases are handled, section 3.1; an alias string
  that a reloaded file dropped but that also appears, for any reason, in the
  text of a file that did not reload is given back.)
* **Interleaved load list.** The load list is not a block of kernel files, a
  block of structure-library files and a block of theorem-library files:
  structure-library and root files are interleaved with theorem-library files
  up to the last entries (`structure-library/functoriality`, which proves 17
  theorems, and `page-audit`). The extension does not reload an unchanged
  non-theorem-library file after a changed theorem-library file. This is sound
  only if no such file reads per-theorem state at load time. The audit found
  every `def-functor` before the boundary, the only unrestricted
  `view-as-auto-specialize!` after it in a theorem-library file, and the
  functoriality proofs covered by the citation graph (a changed name they cite
  refuses). A future structure-library file after the boundary that walks the
  theorem table at load time would break this silently; the band comparison is
  the backstop.
* **Source paths.** `*theorem-source*` holds absolute paths, recorded either
  with the `.scm` extension or as the extensionless stem the cold load passes
  to `load` (on the batch-22 band, 1005 and 2586 entries respectively).
  Reloaded files record the explicit `.scm` path. `xb-rel-source` normalises
  both the prover-root prefix and the extension; a comparison of sources must
  do the same. Recording a normalised relative path at install time would
  remove the question, but that is a change to `install-theorem!`
  (`macetes.scm`), outside this work.
* **Order-sensitive lists.** Lists that accumulate in load order
  (`*case-fold-define-collisions*`, `*proven-theorem-names*`,
  `*support-theorem-names*`) receive the entries of a reloaded file at their
  head, not at the file's position. Their contents agree with a cold load's;
  their order does not.


## Addendum (2026-09-24): the first compare mismatch, and the loader

The third extension (a one-file repair of the batch-25 tree) matched its cold band in every
column but one: the recorded script of `taylor-coef-from-derivs` held the same steps with two of
them in the other order. The driver bound two recording calls in one `let`, and MIT Scheme
evaluates a `let`'s initialisers in one order in compiled code and in the other in interpreted
code; the extension loaded the reloaded file from source unconditionally (hazard 6 above), where
the cold load had run the fresh `.com`. Both proofs are the same proof and both pages replay
grounded; the compare's script column caught the difference, as designed, and the cold band
replaced the extended one.

The extension now loads a reloaded file exactly as the cold load does: the `.com` when it is
fresh, the `.scm` otherwise (`file-fresh-com?`, the rule of load.scm's loop; a stale `.com` is
therefore never served by either path). Hazard 8, for the table: a reloaded file running as
interpreted code where the cold load ran it compiled; any evaluation-order-dependent side effect
in a driver then records a different script. The driver in question was made sequential
(`let*`); a lint for two recording calls in one binding form is a kit item.
