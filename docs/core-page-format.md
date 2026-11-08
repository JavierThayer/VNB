# The core page format (specification, 2026-11-07)

Status: the contract between the lowering (`core-capture.scm`, which writes core pages at the
exam) and the replayer (`core-replay.scm`, which reads them). Design:
`docs/core-replay-design-2026-11-05.md`. This document fixes the syntax, the meaning of each
field, and the checks the replayer makes. Fields not defined here may appear in a page and are
ignored by the replayer.

## 1. Grammar

A core page is one datum read by the Scheme reader (symbols fold to lower case). Comment lines
(`;`) may precede it.

    page      ::= (core-page NAME field*)
    field     ::= (statement WFF)
                | (kernel-hash STRING)
                | (mints MINT*)
                | step
                | other-field                       ; ignored
    step      ::= (step K (at-node N) COMMAND step-field*)
    step-field::= SEQUENT                           ; the step's sequent
                | (hyps SEQUENT*)
                | other-field                       ; ignored
    SEQUENT   ::= (sequent (WFF*) WFF)              ; full
                | (sequent-ref J)                   ; shared (s.1a)
                | (sequent-delta J (drop I*) (add WFF*) [WFF])   ; a difference (s.1a)
    COMMAND   ::= (CMD ARG*)

* `NAME` is a symbol: the theorem's name (a fixture is named `core-fixture-...`).
* `WFF` is a raw formula or term in the kernel's S-expression form, the form `wff-formula`
  returns. Records (functoid records) cannot be written and do not occur.
* `MINT` is a symbol: a page name for an eigenvariable minted during the proof (`v1`, `v2`, ...
  in order of first minting).
* `K` and `N` are positive integers.
* `CMD` is a symbol. `ARG` is a formula, a term, a symbol (a theorem or macete name) or a
  nonnegative integer, never an index into a context or a list of open leaves.

Each of `statement`, `kernel-hash`, `mints` occurs at most once; the first occurrence is read.
The steps are read in the order they occur.

A page is stored as `NAME.core` (text) or `NAME.core.gz` (the same text, gzip-compressed); the
exam compresses its pages at load end (s.8).

## 1a. Shared and difference-written sequents

Every SEQUENT form of a page -- the sequent field of a step and each element of its `hyps`, in
reading order (within a step: the sequent field, then the hypotheses in order) -- is NUMBERED
`1, 2, ...`. A form of either compact kind is numbered like a full one.

* `(sequent-ref J)` denotes sequent number J, which occurs earlier on the page.
* `(sequent-delta J (drop I ...) (add A ...) [G])` denotes the sequent whose assumption list is
  `A ...` followed by the assumption list of sequent J with the 0-based positions `I ...`
  removed (the positions strictly increasing and each less than that list's length), and whose
  goal is `G`, or the goal of sequent J when `G` is absent.

The EXPANSION of a page replaces every compact form by the full `(sequent ASMS GOAL)` it
denotes; two references to one number expand to the same form. Expansion is exact: the
assumption list, ORDER INCLUDED, is the one the writer had. A compact form that does not
resolve (a number not yet written, a position out of range, a malformed form) expands to
`(sequent-invalid FORM)`, and the step holding it is refused (s.4). Every check of s.4 is made
on the expanded page; a page with full forms only is its own expansion.

The writer (`core-capture.scm`) writes a step's sequent as `sequent-ref` when the same node was
written before (in the lowering a step's node is always a hypothesis of an earlier step, except
the root), and each hypothesis as `sequent-delta` against the step's own sequent when the
difference reproduces the assumption list exactly (the kernel adds an assumption at the FRONT,
`context-add-assumption`), else in full. It prints each formula object once per page and reuses
the text.

## 2. Meaning of the fields

* `(statement WFF)`: the proposition proved. The replay starts from the root sequent with no
  assumptions and goal `WFF`. The root is page node 1.
* `(kernel-hash STRING)`: `(cert-kernel-hash)` of the image that wrote the page. The string `"*"`
  marks a hand-written page (the suite's fixtures), whose hash is not compared.
* `(mints MINT ...)`: every page name that stands for a minted eigenvariable. Every other
  free symbol of the page denotes itself.
* `(step K (at-node N) (CMD ARG ...) (sequent ASMS GOAL) (hyps SEQUENT ...))`: the K-th
  inference call of the proof. It is one call of the kernel entry point of `CMD` (s.3) at the
  page node `N`, whose sequent is `ASMS |- GOAL`; `hyps` lists, in order, the hypothesis
  sequents of the inferences that call recorded (for every entry point but one, the hypotheses
  of its single inference; `pi-spec!` is not a core command). An empty `(hyps)` is a closing
  step. The command is the form IMMEDIATELY after `(at-node N)`; the remaining fields are read
  by their head.
* Steps are numbered `1, 2, ...` without gaps. Page node ids are positive integers, dense in
  order of first use; node 1 is the root. A node is named by id only in `at-node`: the
  hypotheses of a step carry no id. The replayer identifies a page node with a replay node by
  its SEQUENT (s.4).

## 3. The core commands

56 names (design s.1). 53 are step commands, each one call of one entry point:

| CMD | arguments | entry point |
|---|---|---|
| di, pbc, oi-l, oi-r, ci, ti, ii, ni, tfi, tfi3, ass, rfl, qrfl, beta, lam-t, lam-b, nth-r, len-r, sep-set, sep-mi, comp-mi, bu-set | none | the `pi-` rule of the same row in design s.1 |
| ai F, detach! F, bc F, cut F, wk F, ue F, subst EQ, lam-b-h F, sep-me F, comp-me F, bu-me F | a formula | idem |
| ew T, if-true T, if-false T, iota-d T, iota-e T, bu-mi T | a term | idem |
| inst F T | a formula, a term | pi-instantiate! |
| ui K | an integer | pi-union-intro! |
| ce F K, te F K, ie F K | a formula, an integer | pi-cartesian-elim!, pi-tuples-elim!, pi-intersection-elim! |
| ta NAME | a theorem name | pi-theorem-assumption! |
| mac NAME | a macete name | apply-macete! (also the procedural macetes cartesian-decompose and tuple-equality-decompose) |
| macm NAME | a macete name | apply-macete! with `*macete-spawn-conditions?*` bound to #t |
| mac-h NAME F | a macete name, a formula | apply-macete-to-assumption! |
| arith, crs, rs | none | pi-arith!, pi-comm-ring-simplify!, pi-ring-simplify! |
| ineq F ... | premise FORMULAS | pi-ineq!, the premises resolved to 1-based indices of the node's context at replay |
| sos T ... | the certificate terms | pi-sos! |

The 3 structural names `sp`, `qed`, `at-node` are not step commands: `sp` is the `statement`
field, `qed` the final check, `at-node` the node field. The entry points `pi-spec!`, `pi-truth!`
and `pi-contraposit!` (unexercised in the library) have no command; a step naming anything that
is not a step command is refused. The table in the source is `*core-dispatch*`; suite check 8
compares it with `reference/kernel-map-static.sexp`.

## 4. What the replayer checks

`(core-replay-page PAGE)` returns `(core-replayed N)`, N the number of steps, or
`(refused K CMD REASON)`: K the step refused (0 for the header, N+1 with CMD `qed` for the
final check), REASON a string. The replay runs on a fresh proof state inside a `fluid-let` of
`*ps*`, the recording globals, `*fresh-counter*`, `*fresh-log*`, `*proof-used-defs*`,
`*pi-owed-nodes*`, the undo journal, the inference-check counters and the definedness audit
counters; it installs nothing. Checker refusals met during a replay are counted apart in
`*core-replay-kernel-refusals*`.

Header (step 0): the datum is a `(core-page NAME ...)` form; it has a statement; it has a
kernel hash, equal to the image's unless `"*"`; the mints are symbols; the statement is a
well-formed formula.

Each step K, in order:

1. the step number is K; `(at-node N)` is present with N a positive integer; the command is a
   form `(CMD ARG ...)`; CMD is a step command of s.3; no sequent form of the step is
   `sequent-invalid` (s.1a); the step has `sequent` and `hyps` fields;
2. the step's sequent mentions no page mint that is not yet mapped (the MINT MAP, s.5); with the
   mint map applied, it is the sequent of the replay node page node N maps to (the NODE MAP), or,
   when N is not yet mapped, of some node of the replay graph, which N is then mapped to (the
   node first tried is the one an earlier step's recorded hypothesis -- the same expanded form
   -- was matched to; the graph is searched only when that node's sequent differs).
   Sequents compare as the kernel compares them: goal up to alpha-equivalence, context as a set
   up to alpha-equivalence;
3. if that node already carries an inference whose hypotheses equal the recorded ones (in
   order, up to alpha and the mint map), the step is accepted WITHOUT RUNNING (a node shared by
   hash-consing, or a later link of a chain); otherwise, if it is already grounded, the step is
   accepted, not run, and counted as skipped;
4. otherwise the arguments are converted (the arity checked, the mint map applied to formulas
   and terms, an argument that mentions an unmapped page mint refused, `ineq` premises resolved
   to indices) and the entry point is called once on the node. It must return a true value, must
   not raise, and must record at least one inference, the first at that node;
5. the hypotheses of the inferences it recorded, in creation order, must equal the recorded
   `hyps`, in order, up to alpha and the mint map (s.5).

Final check (step N+1, `qed`): the root is grounded.

Accepted-without-running and skipped steps are counted in `*core-replay-last-stats*`,
`(ran shared skipped)`.

## 5. The mint map

The mint map sends each page mint to the name this session minted for it. It starts empty. At a
step whose recorded hypotheses mention an unmapped page mint, the replayer LEARNS it: the
candidates are the symbols free in the produced hypotheses and not free in the node the step ran
at; the first injective assignment of the unmapped mints to candidates under which the
hypotheses agree is taken. The extended map must be a bijection: two page mints may not denote
one name, and no mint may denote a symbol the page uses as itself (a free symbol of the page
outside the mint list). A step at which no assignment makes the hypotheses agree is refused.
The fresh counter is not consulted: a page replays at any counter value (suite check 2).

## 6. The Emacs API

* `(core-page-text 'NAME)` returns a string: for each step the line `goal K: TEXT` (the goal of
  the step's sequent -- the focus goal before the step -- printed as the workspace prints a
  formula, with the page's mint names) and the line `step K: (CMD ARG ...)    ; node N`, then the
  verdict line, `verdict: core-replayed N` or `verdict: refused at step K (CMD): REASON`. The
  page is read from `<tree>/core-pages/NAME.core` or `NAME.core.gz`, else from
  `<tree>/test-core-pages/`; when none exists the string is `no core page for NAME`. A `/` in
  NAME is written `%2F` in the file name.
* `(core-replay-begin 'NAME)` opens the statement in the workspace proof state with `sp` and
  returns the step count (#f, with a warning, when there is no page).
* `(core-replay-next)` runs the next step on the workspace proof state with the checks of s.4,
  pushes an undo mark with entry `(core-step K)`, focuses the node of the following step when it
  is known (else the first open leaf), prints the state, and returns K. After the last step it
  makes the final check, prints the verdict line and returns `done`. A refused step leaves the
  graph as it was, prints the verdict line as a warning and returns `(refused K COMMAND REASON)`.
* `(core-replay-back)` undoes the last core step by `backup-one` (the journal route), focuses the
  node of the step now next, prints the state, and returns the number of the last step still
  applied. It refuses when the last workspace step is not a core step.

Nothing the workspace replay does is recorded in `*proof-script*`; a `qed` after it is not
supported.

## 7. Fixtures

`test-core-pages/` holds six pages written by `test-core-pages/make-fixtures.scm` from core-only
scripts (`./prover -b test-core-pages/make-fixtures.scm` regenerates them): `core-fixture-and-comm`
(di, ai, ass), `core-fixture-mint` (a minted witness: ai on FORSOME, ew), `core-fixture-ineq`,
`core-fixture-cite` (ta, inst, detach!), `core-fixture-share` (two conjuncts that are one node),
`core-fixture-arith`. The suite's refused pages are these, altered in memory
(`core-replay-checks.scm`).

## 8. The replay in the exam image

Under `VNB_CORE_REPLAY=on` (set by `vnb-band WORKER --build --exam`, and so by
`vnb-nightly-exam`), at every `qed` of the load, after the certificate record:

1. the surviving inferences are lowered to a page (`core-capture.scm`) and the kernel bill is
   computed;
2. the page is written to `<tree>/core-pages/NAME.core` (the directory is emptied when the load
   starts);
3. the page is READ BACK from that file, expanded (s.1a) and replayed by `core-replay-page`, with
   the capture wrappers passed through; there is no time budget (the workspace command budget of
   `vnb.el` bounds the interactive commands);
4. the verdict is counted. Nothing is installed and no recorded bill is changed: the replay is
   warn-only.

At load end the pages are gzipped (one `gzip` process) and the summary is printed and written to
`<tree>/core-pages/SUMMARY.txt`:

    ;; kernel-bill: N agree, M differ
    ;; kernel-oracles: K differ
    ;; core-lowering: ... sequents written F full, S shared, D as differences; ...
    ;; core-replay: core-replayed N of M (R refused, E raised; replay T s wall)
    ;;   core-replay refused: NAME at step K (CMD): REASON
    ;;   core-replay raised: NAME -- MESSAGE
    ;;   core-replay slowest: NAME SECONDS ...

M counts the pages lowered (proofs that ran through `sp` / `qed` in this load); proofs outside
`sp` / `qed` (companions, the specializer) are not in M. `vnb-nightly-exam` copies the head lines
and the refusals into `last-exam.json` (`core_replay`, `kernel_bill`, `kernel_oracles`,
`core_lowering`, `core_replay_refusals`) and into `~/notes/exam-report.txt`; `vnb-band-pull`
brings `core-pages/` back to the primary, where the Emacs "Show core proof" reads it.
