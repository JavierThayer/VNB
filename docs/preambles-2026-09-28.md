# Preambles and postambles: rule-based drivers a human can edit (notes-45, 2026-09-28)

The note asks for human-editable, rule-based drivers for interactive use: a PREAMBLE is an ordered list
of rules "if the sequent has the form BLAH then do FUBA", applied repeatedly to the focus goal, with a
default one shipped and alternates made by editing it; a POSTAMBLE is a preamble shaped by an existing
proof, obtained by re-running a successful proof and keeping the rules that made progress. The note
observes that the driver kit already does this in Scheme, and that what is missing is a DESCRIPTION
LANGUAGE for BLAH and FUBA. This page says what the tree has, what the language should be, how the two
objects are built from it, and what the user must decide.

## 1. What the tree already has

Four pieces of the machine exist; none is the machine.

* **User rules in the copilot** (`suggest.scm:2378`, 2026-08-20): `*what-now-goal-rules*` and
  `*what-now-assumption-rules*` are lists of Scheme procedures read from a user file
  (`M-x vnb-edit-filter`), each returning a move form or calling `wn-add!`; the lane runs first, every
  suggestion is probed on a scratch copy, a non-firing move is still shown. This is "if BLAH then FUBA"
  exactly, but it SUGGESTS: nothing acts, nothing repeats, and BLAH is a Scheme predicate.
* **`prep`** (`prep.scm`): per-tactic diagnosis procedures, keyed in `*prep-methods*`, that say WHY a
  tactic will not fire and search the library for the fact that repairs it; the plan is run on a clone
  before it is shown. It is a preamble at the scale of one tactic, read-only.
* **`sketch`** (`sketch.scm`): `step CLAIM` cuts a claim and tries to discharge it by a fixed lane list
  (`sk--auto`: `ass rfl qrfl crs arith`, NN typing, the order closer, a bounded `scout`); an undischarged
  claim is granted to the main branch and reported as owed. `sk--discharge` already evaluates a tactic FORM
  when the lane is a pair, a hook nothing has exercised. This is the note's "tentative cut" with its two
  outcomes, minus the rule table.
* **The recording.** Every surface command is recorded (`*proof-script*`, replayed by
  `apply-recorded-cmd!`), the page audit re-runs every proof at every load, and the live trace
  (`*proof-live-trace*`) snapshots each proof as it ran. A postamble reads exactly this.

Also present and reusable: the LCF tacticals `repeat` and `orelse` (`interactive.scm:920`), the bounded
search `scout`, the dispatcher `use`, and the first-order matcher of the rewriter, `match-expr`
(`macetes.scm:98`), which matches a pattern with schema variables against an expression.

## 2. The description language

The recommendation is to take the language the tree already trusts for rewriting, a macete's pattern
with schema variables, and lift it from a formula to a SEQUENT and from a rewrite to a tactic call.

**BLAH: a sequent pattern.** A rule's condition is a goal pattern and zero or more assumption
patterns, in the library's concrete syntax, with schema variables written `?p`, `?t`:

    goal   forall([?x in ?C], ?body)
    goal   ?a <= ?b            with   ?a in rr, ?b in rr
    goal   ?t in fun(?A, ?B)   with   is-metric-space(?s)
    goal   ?P and ?Q

An assumption pattern binds against ANY assumption of the sequent (the first match in context order,
all matches when the action is per-assumption); a schema variable bound in the goal keeps its value in
the assumption patterns, so "the goal is `?a <= ?b` and `?a in rr` is in context" is one rule. The
matcher is `match-expr` as it stands, plus the sequent loop and a small set of guards a pattern can
name: `typed(?t, ?C)` (the context types the term, through the definedness certificate `pi--defined?`),
`head(?t, F)`, `closed(?t)`, `not-in-context(?f)`. These are the predicates the kit uses today
(`dk-head-is?`, `dk-asm?`, `dk-pick`), given names a pattern can carry.

**FUBA: a tactic form with the schema variables substituted.** `(di)`, `(fact 'rr-leq-transitive ?a ?b
?c)`, `(dk-ineq! (:= ?a ?b))`, `(use '?head)`, `(cut F)`. The forms are the recorded surface commands,
so a preamble's steps go through `vnb--run!` and are recorded like any other; a rule adds no trust and
appears on the page as the steps it took. A FUBA may also be a PREAMBLE name: rules compose.

**A rule file.** One S-expression per rule, name first, then the patterns, then the action, then an
optional `probe` clause saying what counts as progress (grounded, fewer leaves, a landed assumption):

    (rule peel-guarded-universal
      (goal  (forall (?x in ?C) ?body))
      (do    (di)))
    (rule close-by-context
      (goal  ?g) (with ?g)
      (do    (ass)))
    (rule real-order-by-ineq
      (goal  (<= ?a ?b)) (with (in ?a rr) (in ?b rr))
      (do    (dk-ineq!))
      (probe grounded))
    (rule tentative-cut-then-pss
      (goal  ?g) (with (forall (?y in ?C) (implies ?h ?g)))
      (do    (cut ?h))
      (side  preamble-or-owed))

This is the "giant COND" of the note, as data: readable, diffable, editable in Emacs, and loadable by
`read`, with no Scheme required of the user who edits it.

## 3. The preamble

`(preamble)` applies the current rule list to the FOCUS leaf: the first rule whose patterns match is
FIRED ON A SCRATCH COPY (`vnb--scratch-state`, as `what-now` and `prep` do), and is committed only if its
probe clause is satisfied (by default: the leaf is grounded or the number of open leaves did not grow
and something changed); then the loop restarts on the new focus, until no rule fires or a cap is
reached. Each committed step is one recorded surface command; a rule that fired and was rejected leaves
nothing. The report block (the channel `zero-it` uses) lists, in order, the rules that fired and what each
did, and at the end the rules that matched but were rejected by their probe, so a preamble that stops
short says WHERE it stopped and why. The default preamble is a shipped file (`preambles/default.pre`),
the user's alternate is `~/.vnb-preamble.pre` or a file named on the command; the Emacs surface gets a
button beside `what-now` and a chooser for the file.

**The tentative cut.** A rule whose action is a `cut` has a `side` clause. `preamble-or-owed` runs the
preamble on the side leaf; if that grounds it the cut is a lemma proven in place, and if it does not the
side leaf is left open and REPORTED BY NAME as an owed claim, exactly as `sketch`'s outcome 2. Putting it
in the PSS is then one surface command on that leaf (`support` + `warrant!` with the claim as written),
the user's decision, never the rule's: a rule may propose a support, the ledger records who took it.

**Why this is not the shape-navigation trap.** CLAUDE.md forbids navigating a DRIVER by goal shape
because sibling branches share goal heads and a rule fires on the wrong one. A preamble acts on the focus
leaf only, one step at a time, with a probe before commit, and its patterns may name the marker
assumptions that distinguish the siblings (the frame tactics' discipline). What it must not do is choose
WHICH leaf to work on by shape; the loop follows the focus.

## 4. The postamble

A postamble is a preamble derived from a finished proof. The construction has three inputs, all
present: the proof's recorded script, the sequent before each step (the page audit replays every proof
and can snapshot it; the live trace has the goal after each step), and a starting preamble.

1. **Replay with attribution.** Re-run the proof step by step. Before each recorded step, match every
   rule of the starting preamble against the sequent. A rule whose action equals the recorded step (up to
   the schema substitution) is CONFIRMED at that sequent. A rule that matches but whose action is not the
   step is a CANDIDATE; fire it on a scratch copy and record whether it would have made progress.
2. **Prune and order.** Rules never confirmed and never progressing are dropped; the rest are ordered by
   the position at which they first fired.
3. **Learn the missing rules.** A recorded step that no rule proposes becomes a new rule by
   generalisation: the sequent is abstracted to a pattern by replacing every eigenvariable and every term
   that occurs as an argument of the step by a schema variable, keeping the heads; the assumptions the
   step consumed or cited are kept as `with` patterns, the rest dropped; the step, with the same
   substitution, is the action. This is explanation-based generalisation as the 1980s rule systems did
   it, one proof at a time, and it costs a replay, not a search.

The output is a rule file, `postambles/<theorem>.pre`, written for the user to read and edit, never
installed as the default by the machine. Over the library the confirmation counts per rule are a
statistic worth printing: a rule confirmed in three hundred proofs belongs in the default; one confirmed
once is that proof's own. Merging postambles into the default is an editing decision.

What a postamble cannot learn from one proof: a rule whose condition depends on a fact NOT in the
sequent (the reason a lemma was cut). Those remain the user's rules, or `sketch` steps.

## 5. Cost and order

* Phase 1, the preamble: the rule reader, the sequent matcher over `match-expr` with the four guards,
  the loop with probe-before-commit, the report, the default file with about fifteen rules (peel, split
  a conjunction, close by context or reflexivity or arithmetic, type by citation when the typing is one
  citation away, `use` the goal head, `dk-ineq!` and `crs` on arithmetic atoms, the tentative cut, and the
  user's clause of 2026-09-28: a goal `t in C` with `C` a number class and `t` an arithmetic term is closed by
  `(type-term)`, which is bottom-up over the closure laws, so the recursion the note asks for is inside the
  action, not in the rule), the
  Emacs button and chooser, suite checks with controls (a rule rejected by its probe leaves no step; the
  loop stops on a cap; a raising rule is named). One agent-day.
* Phase 2, the postamble: the attributing replay over the page audit's re-run, the pruner, the
  generaliser, the per-theorem file and the library statistic. One agent-day after phase 1, plus one
  load to gather the statistic.
* Phase 3: retire `sk--auto` in favour of the default preamble (`sketch`'s `step` then takes a preamble
  name as its lane), and let `what-now` show "what the preamble would do" as a lane.

## 6. Decisions asked of the user

1. **The language** (section 2): macete patterns lifted to sequents, in the concrete syntax, with four
   named guards. Recommended: yes. The alternative is Scheme predicates, which the copilot rules already
   are and which the note calls the missing piece.
2. **Commit policy**: fire on a scratch copy, commit only on progress, one recorded step per rule
   firing, the loop on the focus leaf only. Recommended: yes.
3. **The tentative cut's second outcome**: the side leaf reported as owed, the PSS entry a separate user
   command on that leaf. Recommended: yes; a rule that installs a support would put trust on a pattern.
4. **The postamble's product**: a rule file per theorem for the user to edit, plus the confirmation
   statistic over the library; the default preamble is edited by hand from those. Recommended: yes.
5. **Order**: phase 1 now, phase 2 after the user has driven a preamble on his own goals for a day.

## 7. Built (phase 1, batch 41, 2026-09-28)

Decisions 1 to 3 of section 6 were taken as recommended. The engine is in `preamble.scm` (helper prefix
`pa-`); the shipped rule file is `preambles/default.pre`. The typing gate of `type-term` was lifted in the
same batch (section 7.8).

### 7.1 An existing command of the same name

Section 1 omits a `preamble` that the tree already had: the clause pipeline of 2026-08-21
(`(preamble '(induct) '(unfold ...) '(close))`, `preamble.scm`, loaded after `contra` and `ineq-supply`).
It has no suite check, no help entry and no caller. It is kept, unchanged, under the name
`preamble-clauses`. The command `preamble` dispatches on its argument: a clause list goes to the pipeline;
no argument, a symbol or a string goes to the rule engine.

### 7.2 The file format

A rule file is a sequence of S-expressions read by `read`, so symbols fold to lower case exactly as in the
rest of the tree. Each form is

    (rule NAME
      (goal  PATTERN)          ; required
      (with  PATTERN)          ; zero or more
      (guard GUARD ...)        ; zero or more
      (do    FORM)             ; required
      (probe WHAT)             ; optional: grounded | progress (default) | changed | (lands F)
      (side  HOW))             ; only with (do (cut F)): preamble-or-owed (default) | owed

Patterns are written in ONE syntax, the raw S-expression form that `(dk-goal)` returns; the concrete string
syntax is not accepted. A schema variable is a symbol beginning with `?`. An example from the default file,
verbatim:

    ;; h => g and h are both in context: detach, landing g (close-by-context then closes).
    (rule modus-ponens
      (goal  ?g)
      (with  (implies ?h ?g))
      (with  ?h)
      (do    (detach! '(implies ?h ?g)))
      (probe (lands ?g)))

**Matching.** The goal pattern is matched first, then each `with` pattern against the assumptions in
context order. Bindings are shared: a variable bound by the goal must match the same term, up to alpha
equivalence, in an assumption. The `with` patterns are matched with backtracking, and the guards are tested
on the complete binding. The matcher is `match-expr` (macetes.scm) applied position by position, except at
a binder whose bound variable is a schema variable: `(forall ?x ...)`, `(sep ?v ?a ?p)`,
`(vnb-lambda ?v ?d ?b)`. There the schema variable binds the NAME of the goal's bound variable, and its
occurrences in the body must then be that name. `match-expr` refuses a schema variable in binder position,
because a rewrite would carry the bound variable out of its scope. A rule only selects a tactic to run on
the matched goal, so the binding is harmless here. A literal bound variable in a pattern matches up to
alpha equivalence.

**Guards.** Each argument is a pattern term with its schema variables substituted.

| guard | holds when |
|---|---|
| `(typed T C)` | `(in T C)` is an assumption up to alpha, or `(in T K)` is, with K below C on in-rr's inclusion table (NN ZZ QQ RR CC, CCINT to RR, INTERVAL to NN). It reads the context, not the definedness certificate `pi--defined?`. |
| `(head T SYM)` | T is an application headed SYM, or the atom SYM |
| `(closed T)` | every free symbol of T is a registered constant or a class name |
| `(not-in-context F)` | F is not an assumption, up to alpha |
| `(one-of T S1 S2 ...)` | T is one of the symbols |
| `(occurs PAT T)` | some subterm of T matches PAT; binds PAT's variables |
| `(unfolds T ?M)` | the head of T has a definitional macete (`NAME` or `NAME-def`); binds ?M to it |

`one-of`, `occurs` and `unfolds` go beyond the four guards of section 2. Without them the rule language
cannot say "a number class", "a beta redex somewhere in the goal" or "a head with a definition".

**The action.** The `do` form is evaluated with its schema variables substituted. In an evaluated position
`?x` becomes `(quote VALUE)`; inside a quoted datum it becomes `VALUE`. Thus `(fact 'thm ?t)` and
`(cut '(in ?t zz))` both read as written. The form is evaluated in `user-initial-environment`, where every
tactic is bound. `(preamble NAME)` as an action runs another rule file on the focus, as one firing.

### 7.3 The loop and its commit rule

On the focus leaf L, the rules are tried in file order. A rule is TRIED when its patterns and guards match.
It is first run on a scratch copy of L's sequent (`vnb--scratch-state` under `vnb--probing`). If its probe
holds there, it is run on the proof inside `dk--transaction` and the probe is tested again on the live
outcome. The firing is COMMITTED only when the probe holds both times. Otherwise every effect of the live
run is rolled back: the graph, the focus, the script, the mint record, the live trace and the undo stack.
The probe is evaluated on L:

- `grounded`: L is grounded.
- `changed`: L is grounded, or L is no longer an open leaf, or new leaves appeared. The one exception is
  churn: a single resulting focus with L's goal and L's assumptions.
- `progress`: `grounded`, or `changed` and the number of open leaves did not increase.
- `(lands F)`: `changed`, and F (with bindings substituted) is an assumption of the resulting focus.

`changed` is an addition to section 3. Splitting a conjunction increases the number of leaves, so under
`progress` alone it could never be committed.

The first rule that commits ends the step. A rule that matched and failed its probe is REJECTED: it is
reported and nothing of it is kept. After a commit the loop restarts on the new focus. It works only on
leaves that did not exist when it began, so a leaf already open elsewhere in the proof is never touched,
and owed leaves are left alone. It stops in one of these ways:

- the proof, or the subtree of the starting leaf, is done: status `done`, or `owed` when only owed claims
  remain;
- no rule commits on the focus: `stalled`;
- `*preamble-cap*` (40) firings have been committed: `cap`;
- the rule file cannot be read, or there is no open goal: `error`, and nothing is done.

A rule whose matching or action raises an error (including an action that names an unbound schema
variable) is reported by name and skipped. A malformed rule is left out, and the report names it.

**Recording.** Each committed firing is recorded as the surface commands it ran. The preamble records no
step of its own, so the page of a proof it drove replays without any rule file present. The suite checks
this on four proofs: a typing, a conjunction, a tentative cut proven in place, and a real comparison. All
four pages type back in `grounded`.

**The tentative cut.** A rule with the action `(cut F)` makes the cut. Under `preamble-or-owed`, it then
runs the same rule list on the side leaf F, inside a transaction, without the cut rules (depth one). If
this grounds F, the steps are kept. If not, they are rolled back: F is left open and reported as OWED, and
the rolled-back firings are listed as rejected. Under `owed`, the attempt is skipped. The focus returns to
the main branch. No support is installed. The default file uses the cut for a plain implication `h => g`
in context. The universal form `forall y. h(y) => g` is not supported: the instance to cut is not
determined by the match. It remains a phase-2 question.

### 7.4 The report and the value

The report is printed once, at the end, between `;;VNB-REPORT-BEGIN` and `;;VNB-REPORT-END`, the markers
`zero-it` uses. It is also written to the report channel (`vnb-report!`). It lists:

1. the source file;
2. any malformed rules;
3. each rule that fired, with its instantiated form and what it did;
4. each rule that matched and was rejected, with the goal and the reason;
5. any rule that raised;
6. the owed claims;
7. the status and why the loop stopped.

When an action returns a verdict with a `report` field (as `zero-it` does), that text is appended to the
line. The user's FALSE goal, verbatim:

    ;; preamble: rules from /home/ubuntu/prover/preambles/default.pre (20 rule(s))
    ;;   fired     peel-universal: (di) -- goal now x + 1 = x -- landed x in rr
    ;;   rejected  ring-equation: (zero-it) on x + 1 = x -- no change [zero-it: x + 1 - x  normalises to  1 | zero-it: the goal is FALSE over rr: it reduces to 1 = 0.  This path is dead; no inference was made.]
    ;; preamble: stalled after 1 firing(s) -- every rule that matched was rejected on x + 1 = x

The value is an association list with the fields `status`, `steps`, `fired`, `rejected`, `raised`, `owed`,
`stop`, `file` and `report`. The accessors are `preamble-status`, `preamble-steps`, `preamble-fired`,
`preamble-rejected`, `preamble-raised`, `preamble-owed` and `preamble-report`.

### 7.5 The default rules (`preambles/default.pre`, in order)

| rule | matches | does | probe |
|---|---|---|---|
| peel-universal | `(forall ?x ?body)` | `(di)` | progress |
| peel-implication | `(implies ?a ?b)` | `(di)` | progress |
| split-conjunction | `(and ?p ?q)` | `(di)` | changed |
| close-by-context | goal `?g` with `?g` in context | `(ass)` | grounded |
| reflexivity | `(= ?a ?a)` | `(rfl)` | grounded |
| quasi-reflexivity | `(== ?a ?a)` | `(qrfl)` | grounded |
| ground-arithmetic | a `closed` goal | `(arith)` | grounded |
| type-arithmetic-term (the user's clause) | `(in ?t ?c)`, `?c` one of nn zz qq rr cc | `(type-term)` | grounded |
| type-by-context | `(in ?t ?c)` | `(type-term)` (any class, 7.8) | grounded |
| type-by-in-rr | `(in ?t ?c)` | `(in-rr)` | grounded |
| modus-ponens | `?g`, with `(implies ?h ?g)` and `?h` | `(detach! '(implies ?h ?g))` | `(lands ?g)` |
| instance-of-universal | `?g`, with `(forall ?y ?b)` | `(mp)` | grounded |
| ring-equation | `(= ?p ?q)` | `(zero-it)` | progress |
| real-order-le / -lt | `(<= ?a ?b)` / `(< ?a ?b)` | `(pa-ineq!)` | grounded |
| beta-redex | a goal with `((vnb-lambda ?v ?d ?body) ?arg)` inside | `(dk-lam-b!)` | progress |
| sep-membership | `(in ?t (sep ?v ?a ?p))` | `(sep-mi)` | changed |
| unfold-goal-head | a goal whose head `unfolds` | `(mac '?m)` | progress |
| unfold-class-head | `(in ?t ?c)`, `?c`'s head `unfolds` | `(mac '?m)` | progress |
| cut-antecedent | `?g`, with `(implies ?h ?g)`, `?h` not in context | `(cut ?h)`, side preamble-or-owed | (7.3) |

Three rules differ from section 2 and the brief:

- **The real comparison uses `pa-ineq!`**, not bare `ineq` and not `supply`. Bare `(ineq)` passes no
  premise. `supply` runs its steps through `apply-recorded-cmd!`, which records nothing, so a proof it
  closes has a page that does not replay (finding, 7.10). `pa-ineq!` does what `contra` does before its own
  call: it lands the NN typings the context fires, lifts them to RR, and calls `ineq` on the premises that
  contra's filter accepts. Every step is recorded.
- **The unfold uses `mac`, not `use`.** `use` ends with `use--sweep!` over every open leaf, and a rule acts
  on the focus only.
- **The tentative cut is last**, and is limited to plain implications (7.3).

### 7.6 What the user edits, and where

The user does not edit `preambles/default.pre`. To change the rules, the user copies it and edits the copy.
There are three ways to choose which rule file runs:

- `~/.vnb-preamble.pre`: when this file exists, `(preamble)` reads it instead of the default. The path is
  held in `*preamble-user-file*`.
- `preambles/NAME.pre`: `(preamble 'NAME)` reads it.
- Any other file: `(preamble "path.pre")` reads it.

A missing or unreadable file is reported and nothing is done; the default is not substituted. Every report
begins with the file that was read. The Emacs button and file chooser are the integrator's (section 3).

### 7.7 RANDO's walkthrough

RANDO pastes `forall([x in zz, y in zz], 4 * x^3 + 6 * x^2 * y + 4 * x * y^2 + y^3 in zz)` and types
`(preamble)`.

1. `~/.vnb-preamble.pre` does not exist, so `pa--source` returns `preambles/default.pre`. It holds 20 rules
   and none is malformed.
2. **peel-universal fires.** The goal is `(forall x (implies (in x zz) ...))`, and the first rule
   `(forall ?x ?body)` matches it, binding `?x` to `x`. `(di)` runs on a scratch copy: the goal changes to
   the polynomial typing, lands `x in zz, y in zz`, and one leaf remains, so `progress` holds. `(di)` then
   runs on the proof in a transaction, and the probe holds again. It is committed and recorded as `(di)`.
3. **type-arithmetic-term fires.** On the new focus `4 * x^3 + ... in zz`, rules 1 to 7 do not match: it is
   not a universal, an implication or a conjunction; it is not in context; it is not an equation; and it
   is not closed, since `x` and `y` are free. Rule 8, type-arithmetic-term, matches (`?c` = `zz` is one of
   the number classes). `(type-term)` closes the goal on the scratch copy and again on the proof.
4. **What is recorded.** `type-term` records its own steps: `cut`, `focus`, `arith`, `fact 'zz-mul-closed`,
   `crs`, `subst`, `ass`: 220 of them for this polynomial, 221 steps in all.
5. **Where it stops.** No open leaf remains, so status is `done` after 2 firings. The report block is
   printed:

       ;; preamble: rules from /home/ubuntu/prover/preambles/default.pre (20 rule(s))
       ;;   fired     peel-universal: (di) -- goal now 4 * x ^ 3 + 6 * x ^ 2 * y + 4 * x * y ^ 2 + y ^ 3 in zz -- landed x in zz, y in zz
       ;;   fired     type-arithmetic-term: (type-term) -- closed the goal
       ;; preamble: done after 2 firing(s) -- done: the goal is proved

6. **The page.** RANDO types `(qed 'my-typing)`, which bills `proven modulo 0 [oracles: arith crs]`. The page
   is `(di)` followed by `type-term`'s steps. It contains no `(preamble)` line, and it types back in
   grounded with no rule file present.
7. **The panel.** Before RANDO ran it, `what-now` showed one line naming the rules that match, without
   running them:
   `PREAMBLE -- the rules that match, in the order (preamble) tries them: peel-universal (di), ground-arithmetic`.
   ground-arithmetic matches because the whole sentence is closed; it would have been rejected.

### 7.8 type-term on any class

`(type-term)` used to refuse a class outside NN ZZ QQ RR CC before consulting its planner, although the
planner has a route for any class. That route is:

- the context, through an inclusion from a subclass typing; or
- an application `f(a)` with `f in fun(A, C)` in context and `a` typable in A. The argument is planned
  recursively.

The gate is removed from both the command (`driver-kit.scm`) and what-now's TYPE-TERM lane (`suggest.scm`).
The command now declines only when there is no plan, and the decline message says which kind of class it
was. The lane stays silent when the plan for a non-number class is only "the typing is in context", since
`ass` covers that case. The suite checks:

- `f in fun(zz, bb), x in zz |- f(3 * x + 1) in bb` closes;
- without `x in zz`, it declines and nothing changes;
- the lane offers the command on the first goal and is silent on the second.

On the old code the first check and the lane check fail.

### 7.9 What phase 2 needs from phase 1

The attribution replay must match rules against a recorded sequent without running anything. The entry
points exist, are pure (they do not read `*ps*`), and are checked in the suite:

- `(preamble-propose RULES GOAL ASMS)` returns `(name bindings instantiated-form)` for every rule that
  matches, in file order.
- `(preamble-attribute RULES GOAL ASMS STEP)` returns `(confirmed candidates)`. A rule is confirmed when its
  instantiated action equals the recorded STEP, compared as the script records it, with quoted arguments
  unquoted. The other rules that matched are candidates.
- `pa-match-rule` and `pa-read-rule-file` are the underlying matcher and reader.

The page audit's replay supplies the sequent before each step. The generaliser (section 4, step 3) writes
rules in the format above.

### 7.10 Findings

1. **`supply` does not record its steps.** `supply--attempt!` drives `lam-b`, `fact` and `ineq` through
   `apply-recorded-cmd!`, and that path records nothing. A proof closed by `(supply)` therefore has a script
   without the closing step, and its page reads `incomplete`. This was reproduced in a probe: the script
   was `((di) (di))` and the page `incomplete`. The fix belongs in `ineq-supply.scm`: record each step, or
   record `(supply)` with a case in `apply-recorded-cmd!`.
2. **The language cannot choose an instance.** A rule cannot say "the instance of this universal whose
   conclusion is the goal". `mp` does this as an action. The tentative cut of a universal hypothesis needs
   a term chosen by matching the conclusion, which the language could offer as a guard binding the
   instance, for example `(instance ?u ?g ?inst)`.
3. **`type-term`'s pages are long.** A degree-3 polynomial in two variables costs 220 recorded steps, which
   is `type-term`'s own granularity. A preamble that calls it inherits the length.
4. **The tree's `any` returns #t, not the value** (`sequents.scm:462`, shadowing SRFI-1). A walker written
   with `(any f xs)` to find a binding receives `#t`. The engine's `occurs` guard walks by hand for this
   reason.
