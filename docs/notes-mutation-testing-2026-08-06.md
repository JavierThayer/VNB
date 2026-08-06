# Mutation testing the must-not-prove corpus

2026-08-06.  Written to substantiate a claim made in passing, namely: *"here is the
record of deliberately breaking five guards to prove the list isn't decorative --
including the two occasions that caught the tests themselves being vacuous."*  The
claim is roughly right and loosely stated; section 5 corrects it.

## 1. Why a passing negative test says nothing on its own

A positive test that passes is informative: the machine did the thing.  A negative test
that passes is not, because *every way of failing to prove something looks identical
from outside the test*.  When `test-suite-negative.scm` reports

    PASS  must NOT prove: lam x in NN. x  is in FUN(EMPTY-SET, EMPTY-SET)

the observation is only that the proof state was still open when the attack stopped.
That is consistent with all of:

* the system soundly refused (what the entry means to assert);
* the goal was misspelled, so the attack was aimed at a formula nobody cares about;
* a tactic raised an error inside `quietly`, which silences `vnb-guard`, and the
  remaining commands ran against a state they were not written for;
* the attack ran correctly but on the wrong node -- the rule branched and the script
  attacked one leaf while the other stayed open for free;
* the attack was too weak to close a goal the real system closes in one line.

The last three are not hypothetical; two of them occurred here, on the first pass.  The
defect is the same one a load-time gate has when it accepts everything: an instrument
that cannot report a fault is indistinguishable from an instrument reporting no fault.

## 2. The standard answer

Mutation testing (DeMillo, Lipton and Sayward, 1978).  Inject, on purpose, exactly the
fault the test claims to detect.  If the test still passes, the test does not detect
that fault, whatever its name says.  The test suite is being tested, with the injected
fault as the known-positive control.

Applied to a soundness corpus the correspondence is unusually direct.  Each entry exists
because of a specific repair; the mutation is the *un-repair*.  "This entry guards the
2026-08-02 sethood obligation" becomes a checkable statement: delete the obligation,
and the entry must go red.

## 3. Why it is cheap here

Two facts make the loop seconds rather than minutes.

* A band restart brings the fully loaded library up in about 0.4 s
  (`vnb.band`, 56 MB; see the band note).
* MIT Scheme's compiled code reaches top-level bindings through linkage that respects
  redefinition, so `(set! pi-lambda-type! <mutant>)` in the restarted image is seen by
  the compiled `cmd-lambda-type` that calls it.  No recompilation, no rebuild.

So one mutation run is: restart the band, `set!` one procedure, load the corpus, compare
the PASS/FAIL lines against the prediction.  The runner is
`scratchpad/mnp-mutate.scm`, selecting the mutant from the environment variable
`MNP_MUT`.

## 4. The five mutations

Each row is a prediction made before running: *this guard is what that entry is
watching, so deleting it must turn that entry, and nothing else, red.*

| mutant | what is deleted | predicted red | observed |
|---|---|---|---|
| `no-sethood` | `pi-lambda-type!`'s `(IN A SET)` subgoal | the ORD entry | as predicted |
| `no-domain-match` | `pi-lambda-type!`'s `alpha-equiv?` check that the term's declared domain is the `FUN`'s | the `FUN(EMPTY-SET, EMPTY-SET)` entry | **nothing** -- see 5 |
| `no-definedness` | `pi-reflexivity!`'s definedness guard (`term-self-defined?` := always true) | `pred(0)`, `recip(0)` | as predicted |
| `credulous-arith` | `arith-eval-formula`'s verdict (every decidable sentence true) | `0 = 1`, `2 + 2 = 5` | as predicted, plus `pred(0)` |
| `credulous-ineq` | `fm-prove`'s search (Fourier-Motzkin always reports infeasibility) | the false `ineq` goal | as predicted |

Two observations worth keeping.

`credulous-arith` reddened a third entry, `pred(0) = pred(0)`, which was not predicted.
That is correct behaviour and not a defect: a credulous `arith` will close a reflexivity
goal about an undefined term, so `pred(0)` is genuinely guarded by two independent
mechanisms.  An unpredicted red is information; an unpredicted green is a bug in the
test.

`credulous-ineq` did *not* redden `0 <= a |- 0 <= a*a`, and that is also correct.
That entry does not guard Fourier-Motzkin.  `formula->lin+rel` refuses the nonlinear
goal before `fm-prove` is ever called, so the entry guards the *linearizer* -- the
component that decides what `ineq` is allowed to look at.  Naming the component
correctly matters: the entry would survive an unsound `fm-prove` and must not be cited
as evidence against one.

## 5. The vacuity findings, accurately accounted

The loose sentence said "two occasions that caught the tests themselves being vacuous",
which runs together two things of different kinds.  Precisely:

**Found by a mutation.**  One mutant, `no-domain-match`, turned nothing red, twice over,
for two independent reasons.

1. *The entry attacked only the focus leaf.*  With the domain match deleted,
   `pi-lambda-type!` fires on the false goal and produces two subgoals.  The attack
   closed the one it was looking at; the sibling stayed open; `mnp-closed?` reported
   "still open"; the entry passed.  A branching tactic was buying a refusal for free.
   Repaired by `mnp-attack-leaves!`, which attacks every open leaf to exhaustion.
2. *The attack could not prove `(IN EMPTY-SET SET)`.*  With (1) fixed, the surviving
   leaf was a sethood goal that the real system discharges in one line and the blunt
   attack -- grind, arith, crs, ass, rfl -- could not touch at all.  The entry was
   therefore reporting the weakness of its attacker as a property of the system.
   Repaired by giving the attacker `dk-set-close!`, the library's own sethood closer.
   It returns `#f` on `ORD`, which is the honest boundary (Burali-Forti) rather than a
   remaining gap.

After both repairs the mutant reddens the entry as predicted.

**Not found by a mutation.**  While writing a new entry for the 2026-07-11
simultaneous-substitution bug, two *positive*-suite checks turned out to be incapable of
failing: `test-suite.scm:4363` and `:4372`.  Both listed the binding `sm` last in the
substitution's alist.  With that order the naive fold -- the very defect the checks were
written against -- consumes `n` and `u` before `sm` introduces the term containing them,
so the fold and `subst-free*` return the identical answer.  Verified by computing both
on both fixtures.  Reordering `sm` first makes the distinction observable; the expected
values do not change, because a simultaneous substitution is order-blind.

This was found by hand, by asking "what would the old code have returned here?" -- which
is the same question a mutation asks, applied by inspection rather than by execution.
It is the same *method*, not the same *record*.

So the accurate statement is: **one of five mutations exposed the corpus as vacuous,
twice over; and separately, a hand-check while writing a new entry exposed two
long-standing positive-suite checks as incapable of failing.**

## 6. What the exercise licenses, and what it does not

Licensed: *for each of five named guards, the corpus detects its removal.*  That is a
statement about five specific procedures, verified by execution, on 2026-08-06.

Not licensed, and each of these is a way the sentence could be over-read:

* **Not "the corpus detects soundness bugs."**  It detects the removal of five guards it
  was built around.  A sixth guard nobody has mutated is in the position all five were
  in before this session.
* **Not "these mutations are realistic."**  Each replaces one procedure wholesale.  A
  real defect is usually a subtler edit -- an off-by-one in an index, a missing case in
  a `cond`, a walker that skips one position (which is exactly what the `NTH` bug was).
  An entry that catches the crude mutation may well miss the subtle one.
* **Not "the entries not mentioned are verified."**  Two entries are consistency
  canaries rather than fix-regressions, and no single-guard mutation reddens them:
  `0 in EMPTY-SET` (reaching it needs a two-domain derivation through
  `fun-domain-apply-def`, which the blunt attack does not construct) and
  `f in INJECTION(S(1), S(0))` (paired with the theorem that nothing is; if both ever
  pass, the library is inconsistent, which is what they are watching for).
* **Not a standing guarantee.**  `mnp-mutate.scm` lives in the scratchpad: it is not in
  the tree, not in the suite, and not re-run by anything.  The table in section 4 is a
  measurement taken once, and it decays the moment any of the five guards is edited.

## 7. Consequent worklist

1. **Move the mutation runner into the tree** and give it a target, so "the corpus still
   detects these five faults" is reproducible by a command rather than by trusting a
   comment.  This is the difference between a record and a check.
2. **Mutate the remaining entries' guards**, and where no mutation can be written, say so
   in the entry -- an entry no mutation reddens is an entry whose attack may be too weak.
3. **Replace the blunt attacker with a `scout` search**, so an entry means "no route the
   system's own search finds" rather than "this fixed script did not find one".
4. **Try one subtle mutation** -- an off-by-one rather than a wholesale replacement -- to
   find out whether the corpus has any resolution below "guard entirely absent".
