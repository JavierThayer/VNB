# The first postamble: rules extracted from a proof driver (2026-10-02)

The user's item for the day: "for some test cases, look at the proof drivers (e.g. bernstein-moments.scm)
and attempt to extract a sequence of preamble-type rules", with the new rule kind "ask the user for
advice" (notes-50: the rules need not give the whole proof; they give the user an idea how to go about
it). This page records what was built, what the rule file does on the driver's own statements, and what
the attempt found. The design of preambles is `docs/preambles-2026-09-28.md`; the rule file is
`postambles/bernstein-moments.pre`; the probe is `scratchpad/postamble-bernstein-probe.scm`.

## 1. The driver, counted

`theorem-library/bernstein-moments.scm`: 699 lines, 8 theorems (the basis is real; the Pascal recurrence;
two vanishing laws; the weighted step; the first and second moments by induction; the variance identity;
the variance bound). Its surface steps, by kind:

| kind | count | what it is |
|---|---|---|
| `fact` / `dk-fact!` | 125 | a hypothesis landed forward, almost all typings (`k in ZZ`, `1 in RR`, a basis value in RR) |
| `have!` / `dk-have!` | 52 | a claim with an inner proof: 44 pointwise typings or pointwise equations, each `(di) (type the atoms) (lam-b ...) (crs)` |
| `subst` | 35 | a rewrite by a cited equation (the weighted step, the linearity laws, the earlier moments) |
| `di` | 37 | peeling |
| `crs` | 27 | the closing ring identity |
| `ass` | 24 | close by context |
| `mac` / `mac-h` | 17 | unfold the basis; the Pascal law of COMB-KK; the ring view's operations read as the reals' |
| `use-induction` | 2 | the moments |
| `sos` | 1 | the variance bound |

Three in five steps land a typing. One in five is a rewrite by a lemma AT A WITNESS the author chose: the
weight, the three families of the weighted step, the induction variable. The rest is navigation.

## 2. What was built

**The rule kind `(ask TEXT)`** (preamble.scm, parser, loop, report; two suite checks). A rule carries
`(ask TEXT)` in place of `(do FORM)`. When it matches, nothing is run: the loop stops with status `ask`,
the rules fired before it stay committed, the report carries `ASK NAME: TEXT -- on GOAL`, and
`(preamble-asked v)` returns the `(name text goal)` list. The patterns and guards say WHEN the advice
applies.

**The rule file** `postambles/bernstein-moments.pre`, 29 rules in six groups, in the order the driver
meets them: (0) the induction ask, before peeling, guarded on a sum to `succ(n)` in the body;
(1) navigation; (2) the ring context -- RR is a normed field, its ring view is a commutative ring, `1`,
`1 - x` real, `x` and `1 - x` in the view's carrier (two tentative cuts, each closed by one rewrite);
(3) typings landed forward -- an NN index in ZZ, `1 in ZZ`, the shifted index, `succ(n) in NN`, a basis
value real; (4) one basis value -- the typings brought to COMB-KK form, the unfold, the two vanishing
laws by citation with the ring's zero read as 0, the Pascal law, the read-offs of the ring operations,
the slot-op saturation, beta, the closing `crs`; (5) the sum ask; (6) the default preamble as a fallback.

**Two defects of the engine met on the way, fixed:** the `(lands F)` probe accepted a step that re-landed
a formula already in context (a `fact`'s chain lands its intermediate forms again, so the graph
"changes"), and the loop reported `done` when the leaf list was empty although the proof was not
grounded. The probe now requires F to be new; the loop reports that state as `broken`.

## 3. What the rule file does on the driver's statements (worker-02, against today's band)

| statement | result |
|---|---|
| `bernstein-basis-null` (the basis vanishes below the range) | PROVEN, 18 firings, no user input |
| `bernstein-basis-succ` (the Pascal recurrence) | 26 firings, stalled: the basis value at index `k` never gets its realness (section 4, finding 2); the goal is the ring identity with one atom untyped |
| `bernstein-moment-1` (the first moment) | the induction ask, before any step |
| `bernstein-variance-bound` | the induction ask, before any step (the advice says what to do when the identity follows by linearity, as here) |

The vanishing law's 18 firings read, in the report, exactly as the driver's 11 lines do: peel, the five
context facts, the typing of the basis value, the unfold, the typing brought to COMB-KK form, the
citation, the ring's zero. The report IS the digestible presentation the note asked for, for that
theorem.

## 4. Findings

1. **A `fact` of an instance already in context is a silent self-loop.** Reproduced minimally: after
   `(fact 'nn-subset-zz 'k_)` twice, the proof has 0 open leaves, `proof-done?` is false, 5 ungrounded
   nodes. CLAUDE.md records this for `cut` and `have!`; `fact` has the same hole, since its chain is
   landed by the same cut. The user sees "0 open goals" and `qed` refuses. RECOMMENDED: refuse, at
   `dg-apply-rule!`, an inference whose conclusion sequent is one of its own hypothesis sequents
   (a trivial cycle; no stored proof can contain one, since such a node never grounds), with the
   accepted / refused suite pair the gate rules require. A kernel-file change: the nightly exam
   re-proves everything. The user's decision.
2. **Guards do not backtrack.** `(with (in ?k zz))` binds `?k` to the first assumption that lets the
   later guards hold, but `(occurs PAT ?g)` returns its FIRST match, so a goal with two basis values
   (`(succ n, x)` at `k`, `(n, x)` at `k`) lets the rule type one of them and never the other. The
   Pascal lane stalls on exactly this. Making `occurs` enumerate its matches (the `with` loop already
   backtracks) is a contained change to `pa--guard` / `pa-match-rule`.
3. **The matcher refuses a destructuring binder in a pattern.** The ring's `add` and `mul` read off as
   `vnb-lambda([x_, y_], cartesian(rr, rr), x_ + y_)`; `(vnb-lambda (list ?p ?q) ?d ?body)` does not
   match. The rule file works around it with `(occurs (cartesian rr rr) ...)`.
4. **`type-term` has no route for `succ`:** the tentative cut of `succ(n_) in nn` with `n_ in nn` in
   context was left owed by the default preamble. The driver cites `bt-succ-in-nn` (a binomial shim)
   and the tree has `nn-succ-closed`; the rule file cites the latter. `type-term` should know it.
5. **Forward typing is the language's weak half.** Every typing the driver lands is a rule of the shape
   `(goal ?g) (guard (occurs T ?g) (not-in-context (in T C))) (do (fact LAW ...)) (probe (lands (in T C)))`,
   one per law. What the driver really does is "type every atom of the goal before `crs`", which is
   one tactic (`dk-saturate-slot-ops!` is its ring-operation half). A rule kind `(type-atoms C)` --
   land `t in C` for every maximal non-arithmetic subterm `t` of the goal that `type-term` can reach,
   as one firing -- would replace sections 2-3 of the rule file and most of the 125 facts.
6. **What is a step, at the content level.** For this file: the content steps are the five asks' worth
   -- induct or not; the weight; the three families; which linearity law; the earlier moment to cite --
   plus the two citations of COMB-KK laws. Everything else (typings, read-offs, beta, crs) is
   machinery a rule can take. The reader (`proof-reader`) should show exactly the content steps; the
   postamble shows which steps those are, by being unable to take them.
7. **Per theorem or per file.** The rule file is per FILE and it works: the eight theorems share the
   ring context, the typing laws and the unfold; only the asks are per theorem, and they are
   distinguished by the goal's shape (a sum or not; a vanishing law or the recurrence).

## 5. Not done

The postamble is hand-extracted. The design page's section 4 (replay with attribution, prune, learn the
missing rules by generalisation) is the mechanical version; `preamble-attribute` exists for its first
step. The sum theorems are asks all the way down: a rule that fires `bernstein-weighted-step` needs the
weight and the three families as terms, which only the author's `have!` claims carry.
