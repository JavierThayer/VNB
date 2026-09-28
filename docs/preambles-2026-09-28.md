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
  citation away, `use` the goal head, `dk-ineq!` and `crs` on arithmetic atoms, the tentative cut), the
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
