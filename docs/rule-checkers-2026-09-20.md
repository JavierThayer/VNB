# The kernel checks what it records (batch 10, 2026-09-20)

## The decision

`dg-apply-rule!` (deduction-graphs.scm) is the one write point of the deduction
graph. Until today it recorded the rule name it was handed and checked nothing,
so the trusted code base was exactly the set of its callers -- eight files,
pinned by the fatal `kernel-callers-audit`. The user's decision of 2026-09-20:
`dg-apply-rule!` shall CHECK that the hypotheses it is handed are the ones the
named operation prescribes, behind a switch.

## The design

In `deduction-graphs.scm`:

    (define *dg-check-inferences?* #f)            ; the switch
    (define *rule-checkers* (make-strong-eqv-hash-table))
    (define (register-rule-checker! name proc) ...)   ; NAME = (rule-tag-head rule)

A checker is `(lambda (rule hyps concl) ...)`, where `rule` is the full tag as
handed to `dg-apply-rule!` (a symbol, or a list such as `(union-intro 2)`),
`hyps` the hypothesis sequents in the order handed over, and `concl` the
conclusion sequent. It returns `#t` to accept, and `#f` or a string (the
reason) to refuse.

With the switch ON, `dg-apply-rule!` looks the checker up by the tag's head
before anything is written: no checker is an ERROR, a refusal is an ERROR
naming the rule, the reason and both sequents, and in either case nothing
reaches the graph -- the check runs before `dg-post!` of the hypotheses. With
the switch OFF the procedure behaves exactly as it did before.

A checker VERIFIES a finished inference; it does not rebuild it. It is written
independently of the `pi-*` procedure that built the hypotheses: it neither
calls nor copies it, and uses only the expression layer (`alpha-equiv?`,
`free-vars`, `subst-free`, the sequent accessors) plus the one-way matcher in
`rule-checkers-logic.scm`, which is what FINDS a term the rule leaves implicit
(the `t` of `forall-elim`, the witness of `forsome-intro`, the eigenvariables
of `forall-intro`).

Three conventions, binding on all four checker files:

1. Assumption lists are compared as SETS, up to alpha-equivalence. Order and
   multiplicity carry no meaning: `context-add-assumption` already refuses a
   duplicate and `context-remove-assumption` drops every alpha-copy.
2. A rule that ADDS a formula is checked as a set UNION, never as "the
   hypothesis has one more formula" -- when the added formula was already in
   the context, the builder adds nothing and the union says the same thing.
3. Refusal is a string that names what failed. A refusal during a load is a
   finding to be read, never something to silence.

### What is deliberately NOT checked

* **The definedness certificate.** `forall-elim` owes the side sequent
  `(= t t)` exactly when `pi--defined?` declines to certify `t`
  (`docs/definedness-instantiation-2026-09-18.md`). That certificate is a
  POLICY about when an obligation may be skipped, not a rule of logic:
  instantiating a universal at a term is sound in LUTINS as soon as the term
  denotes. The checker therefore accepts the side sequent present or absent
  and re-derives nothing about which it was. The same holds for `reflexivity`.
* **Trust.** A checker says the inference has the shape the rule licenses. The
  trust tier of the theorems cited is the ledger's business (`proof-debt.scm`).

### The files

    rule-checkers-logic.scm     (10-A)  the 42 `logic' operations + the shared helpers
    rule-checkers-schema.scm    (10-B)  the 13 `schema' operations
    rule-checkers-rewrite.scm   (10-C)  the 4 `rewrite' operations
    rule-checkers-oracle.scm    (10-D)  the 7 `oracle' operations

They are core files, loaded by `load.scm` after `structures` and before
`interactive`, so before the first proof. `load.scm` then calls
`dg-check-arm-with!`, which registers an ACCEPT-ON-TRUST checker for every head
of a group whose file is not present, LISTS those heads at load, and turns the
switch on. A silent acceptance would be worse than no check at all.

`scratchpad/chk/dg-check-shim.scm` is the same framework, written to be loaded
over a WORKER'S BAND (which was built before any of this existed), so a probe
can re-run library proof files with the switch on before the tree is rebuilt.
It is a copy and dies the day the band is rebuilt.

## The relation each `logic' checker enforces

`Gamma => G` is the conclusion sequent.

| rule | relation |
| --- | --- |
| `and-intro` | `G = (AND p q)`; two hypotheses, same context, goals `p` and `q` |
| `or-intro-left` | `G = (OR p q)`; one hypothesis, same context, goal `p` |
| `or-intro-right` | `G = (OR p q)`; one hypothesis, same context, goal `q` |
| `implies-intro` | `G = (IMPLIES p q)`; context gains `p`, goal becomes `q` |
| `not-intro` | `G = (NOT p)`; context gains `p`, goal becomes `FALSITY` |
| `iff-intro` | `G = (IFF p q)`; hypotheses `Gamma, p => q` and `Gamma, q => p` |
| `forall-intro` | the hypothesis is the body of `G`'s universal chain at eigenvariables `y_i`, each a symbol free neither in `Gamma`, nor in the formula still being generalised at that step, nor in a guard already collected; the context gains exactly the guards the chain carried. The `y_i` are FOUND by matching, never minted |
| `forsome-intro` | `G = (FORSOME x p)`; same context, hypothesis goal is `p[x := t]` for some `t` (found by matching) |
| `truth-intro` | `G = TRUTH`; no hypotheses |
| `and-elim` | some `(AND p q)` of the context is replaced by `p` and `q`; goal unchanged |
| `or-elim` | some `(OR p q)` of the context is replaced, in two branches, by `p` and by `q`; goal unchanged |
| `not-elim` | the context holds both `p` and `(NOT p)`; no hypotheses |
| `iff-elim` | some `(IFF p q)` of the context is replaced by its two implications |
| `forsome-elim` | some `(FORSOME x p)` of the context is replaced by `p[x := y]` for a symbol `y` free neither in the rest of the context, nor in `G`, nor in the existential |
| `forall-elim` | some `(FORALL x p)` of the context yields `p[x := t]`, which the context gains; goal unchanged; the owed `Gamma => (= t t)` may be present or absent |
| `assumption` | `G` is `TRUTH` or is in the context; no hypotheses |
| `theorem-assumption` | the context gains the installed statement of SOME theorem (searched for in `*theorem-table*` by statement); goal unchanged |
| `cut` | `Gamma => L` and `Gamma, L => G` |
| `weakening` | the hypothesis context is included in `Gamma`; goal unchanged |
| `detach` | the context holds `(IMPLIES p q)` and `p`, and gains `q` |
| `backchain` | the context holds `(IMPLIES p G)`; the goal becomes `p` |
| `proof-by-contradiction` | the context gains `(NOT G)`; the goal becomes `FALSITY` |
| `contraposition` | `G = (NOT p)`, the context holds `(IMPLIES p q)`, the goal becomes `(NOT q)` |
| `eq-subst` | the context holds `s = t` or `s == t` (either orientation, either head) and the new goal is `G` with SOME occurrences of `s` replaced by `t`, and differs from `G` |
| `reflexivity` | `G` is `TRUTH` or `(= u v)` with `u` and `v` the same term; no hypotheses |
| `quasi-reflexivity` | `G = (== u v)` with `u` and `v` the same term; no hypotheses |
| `if-true` | branch 1 proves the condition `p`; branch 2 keeps the goal and gains `(= (IF p a b) a)` |
| `if-false` | branch 1 proves `(NOT p)`; branch 2 keeps the goal and gains `(= (IF p a b) b)` |
| `cartesian-intro` | `G = (IN [e1..en] (CARTESIAN A1..An))`, equal lengths; one hypothesis `(IN e_i A_i)` per component |
| `cartesian-elim k` | the context holds such a membership and gains `(IN e_k A_k)` |
| `tuples-intro` | `G = (IN [e1..en] (TUPLES A))`; one hypothesis `(IN e_i A)` per component |
| `tuples-elim k` | the context holds such a membership and gains `(IN e_k A)` |
| `union-intro k` | `G = (IN x (UNION S1..Sn))`; one hypothesis `(IN x S_k)` |
| `union-elim` | the context's `(IN x (UNION S1..Sn))` is replaced, one branch per set, by `(IN x S_i)` |
| `intersection-intro` | `G = (IN x (INTERSECTION S1..Sn))`; one hypothesis `(IN x S_i)` per set |
| `intersection-elim k` | the context holds such a membership and gains `(IN x S_k)` |
| `nth-reduce` | the new goal is the old one with some `(NTH k [a1..an])` contracted to `a_k`, and differs from it |
| `length-reduce` | likewise for `(LENGTH [a1..an])` contracted to `n` |
| `functoid-beta` | likewise for `(apply-functoid <lambdoid> v1..vn)` contracted by parallel substitution |
| `nn-induction` | `G = forall n in NN. body` with `n` outermost; the two hypotheses ARE `body[n := 0]` and the step |
| `transfinite-induction` | `G = forall var in ORD. P`; the hypothesis IS the strong-induction step, its induction variable read off the hypothesis and required to be fresh for `P` and the context |
| `transfinite-induction-3cases` | the same, with the base, successor and limit cases |

The three reduction rules are checked by CONTRACTING INDEPENDENTLY: the
contraction is three lines in the checker file, and the relation tested --
"the new goal is the old one with SOME licensed redexes contracted" -- is
weaker than "the normal form was reached", hence sound.

## Log

* **2026-09-20, milestone 1 (10-A).** Framework in `deduction-graphs.scm`
  (switch, table, `register-rule-checker!`, the checking `dg-apply-rule!`);
  `scratchpad/chk/dg-check-shim.scm` for probing over a band; the shared
  helpers and all 42 `logic` checkers in `rule-checkers-logic.scm`. Both files
  compile.
* **2026-09-20, milestone 2 (10-A).** Positive control over the band
  (`scratchpad/chk/probe2.scm`, worker-01): 37 theorem-library files re-run
  with the switch ON and the other three groups accepted on trust -- 132 `qed`
  lines, **no refusal**. An earlier eight-file probe verified 211 inferences,
  likewise with no refusal.
* **2026-09-20, milestone 3 (10-A).** Negative controls appended to
  `test-suite.scm` under the banner "rule checkers: logic": one ACCEPTED case
  and one REFUSED case per rule, driven straight at `dg-apply-rule!`, plus
  three checks that the switch is on after the load, that it verified more
  than a thousand inferences (a switch that is a no-op would pass every other
  check), and that no `logic` head is accepted on trust. An unregistered tag
  is checked to be refused outright.
* **2026-09-20, milestone 4 (10-A).** `load.scm` wires the four files in after
  `structures`, arms the switch after the last of them, and accepts on trust
  (by name, at the load) the heads of any group whose file is absent.
  `VNB_NO_RULE_CHECK=1` leaves the switch off: it is the A/B control for what
  the checking costs, the same binary with one flag different.
* **2026-09-20, milestone 5 (10-A).** First integrated cold load on worker-01,
  `VNB_NO_RULE_CHECK=1` (the A/B control): 2162 proofs, page audit ok for all
  2162, KEEP-GOING 0 failures and 0 holes, every gate as before. So the four
  files are wired in and cost nothing when the switch is off. Wall 943 s.
  `kernel-rules-audit` reports 8 of the 66 documented tags UNEXERCISED by the
  load -- `truth-intro`, `contraposition`, `tuples-intro`, `tuples-elim`,
  `functoid-beta`, `tuple-equality-decompose`, `arith-forsome`,
  `ring-simplify`. Those eight checkers therefore have NO positive control
  from the library, and their negative controls in the suite are all the
  evidence there is for them.
* **2026-09-20, milestone 6 (10-A).** First cold load with the switch ON. THE
  42 `logic` CHECKERS REFUSED NOTHING. The `lambda-beta` checker
  (rule-checkers-schema.scm, 10-B) refused licensed reductions and failed
  several proof files; the finding, with the two sequents and the kernel lines
  that settle it, is `scratchpad/chk/FINDING-10-A-to-10-B.md`: the kernel
  contracts a redex's ARGUMENTS FIRST and judges the licence on the contracted
  arguments, and the checker was judging it on the argument as written in the
  conclusion, which is still a redex. The kernel is right; the checker is
  wrong. Worth recording separately: a refusal inside a driver's `quietly'
  does not print -- `vnb-guard' swallows it and the tactic no-ops -- so
  `rr-nvs-exemplification' failed with no refusal in the log at all. When the
  switch is on, a proof that "did not close" for no visible reason is the
  shape a silenced refusal takes.
* **2026-09-20, milestone 7 (10-A), on the integrator's instruction.** A
  refusal is now UNSUPPRESSIBLE. `dg-check-report-refusal!`
  (deduction-graphs.scm) displays `;VNB RULE CHECKER REFUSED <rule> -- <reason>`
  and records the refusal in `*dg-check-refusals*` BEFORE `dg-apply-rule!`
  raises, so a driver's `quietly` can no longer hide it. At the end of the
  load, `load.scm` prints
  `;; inference checking: N inference(s) verified, M refusal(s)` together with
  the accepted-on-trust list, lists each refusal, and ERRORS when M > 0 in a
  strict (non-keep-going) load. The suite checks that the ledger really fills.
* **2026-09-20, second finding (10-C).** The `macete` checker's matcher lacks
  the NUMERAL <-> SUCC bridge of `match-expr` (macetes.scm:108-118), by which
  a pattern `(succ P)` matches a positive integer literal `m` against `m - 1`
  -- which is what lets `nth-deriv-succ`, `mpow-succ` and `power-succ` fire on
  1, 2, 3 rather than only on syntactic succ-towers. Write-up:
  `scratchpad/chk/FINDING-10-A-to-10-C.md`. The kernel is right.
* **2026-09-20, the first switch-ON load in full.** 2127 of 2162 proofs; 31
  `lambda-beta` refusals and 1 `macete` refusal, all from the two checker bugs
  above; **nothing refused by the 42 `logic` checkers and nothing by the 7
  oracle checkers**; 10 proof files failed and 5 theorems were installed as
  holes (`fin-subset-monoid-is-comm-monoid`, `nth-deriv-one`,
  `mat-ring-is-ring`, `border-mult`, `poly-is-ring`). Both checkers were fixed
  by their owners and the load re-run.
* **2026-09-20, milestone 8: THE LOAD IS CLEAN WITH THE SWITCH ON.**
  worker-01, `/home/ubuntu/loads/chk-on2.log`, BUILD-EXIT 0:

      2162 proofs, 2162 `proven modulo 0`
      ;VNB inference checking: ON, 66 rule(s) checked, none accepted on trust
      ;; inference checking: 197677 inference(s) verified, 0 refusal(s)
      ;; page-audit: ok (all 2162 proof(s) emit a re-runnable script)
      KEEP-GOING: 0 proof file(s) failed, 0 holes
      every gate ok; kernel-callers-audit ok (69 call sites, 8 files)

  **What it costs.** Same tree, same binary, one flag different:

      switch OFF (VNB_NO_RULE_CHECK=1)   902 s
      switch ON                         1173 s
      overhead                          +271 s, +30 %

  That is 271 s for 197,677 verified inferences, about 1.4 ms each. The
  checkers compare assumption lists as sets, which is quadratic in the
  context; `dg-post!` already scans every node of the graph per posting, so
  the checking is of the same order as what the graph cost before it.
* **2026-09-20, milestone 9: the suite.** The first run was
  `1470 passed, 22 failed`, and all 22 failures were in 10-A's own TEST DATA,
  not in a checker: the cases were written as quoted nests and had one paren
  level too many in every hypothesis whose context was non-empty, so the
  checkers were handed a context whose "formula" was a list of formulas and
  duly refused it -- the right answer to the wrong question. Three more cases
  (`assumption`, `reflexivity`, `quasi-reflexivity`) passed the SAME empty
  hypothesis list as both the right and the wrong inference. The block was
  rewritten around a constructor, `(rcl--h <assumptions> <goal>)`, which
  cannot be mis-nested, and the three rules with no hypotheses now get an
  explicit accept case and an explicit refuse case with different
  CONCLUSIONS. No other agent's block failed.
* **2026-09-20, milestone 10: the suite.** `./vnb-suite worker-01`:

      === SUMMARY: 1489 passed, 0 failed ===

  (against 1307 before batch 10; the 182 new checks are the four groups'
  negative controls plus the integrator's oracle-repair checks). 10-A's block
  contributes 90 of them: one ACCEPTED and one REFUSED case for each of the 42
  logic rules, plus the switch-is-on check, the switch-is-not-a-no-op check,
  the none-on-trust check, the refusal-ledger check, and the check that an
  unregistered tag is refused outright.

## What the four files add to the trusted base

`kernel-callers-audit` is unchanged at 69 call sites in 8 files: the checker
files call `dg-apply-rule!` from nowhere, so `*kernel-caller-files*` did not
grow. But they are TRUSTED CODE in the ordinary sense -- a checker that
accepts an unsound inference is as bad as a kernel that records one -- and
`reference/KERNEL-MAP.md` counts the trusted code base at 318 procedures over
15 files. That inventory should now count `rule-checkers-logic`,
`rule-checkers-schema`, `rule-checkers-rewrite` and `rule-checkers-oracle`.
REPORTED, not edited: KERNEL-MAP.md is hand-written and belongs to 10-M.

## The eight rules the library never exercises

`kernel-rules-audit` reports, at every load, eight documented tags that no
proof in the library uses: `truth-intro`, `contraposition`, `tuples-intro`,
`tuples-elim`, `functoid-beta`, `tuple-equality-decompose`, `arith-forsome`,
`ring-simplify`. Two of them (`truth-intro`, `contraposition`) are
unreachable: no tactic calls `pi-truth!` or `pi-contraposit!`. For all eight,
the positive control is EMPTY -- the cold load says nothing about their
checkers -- and the suite's negative controls are the only evidence there is.
