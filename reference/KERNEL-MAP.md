# The VNB kernel: which code the system trusts

A theorem VNB reports as proven is a claim about a deduction graph, and such a
claim is worth exactly as much as the code permitted to write into that graph.
This page is the inventory of that code. It addresses two questions, both of
which bear directly on the soundness of the system:

- **(a)** which procedures may record an inference, the decision procedures
  included; and
- **(b)** which of those each proof command can reach.

## The boundary

An inference is recorded in a deduction graph by exactly one procedure,
`dg-apply-rule!` (`deduction-graphs.scm`). It records the name of the rule it is
handed — the name that appears in the inference node — posts the premise
sequents, and writes the arrows. Before it writes anything it verifies the
inference: the rule name selects a **checker**, and the checker states the rule
as a relation between the conclusion sequent and the hypothesis sequents and
tests that the relation holds. A rule with no checker, and a checker that
refuses, are both errors, and in either case nothing is written. The checkers
are written independently of the procedures that build the inferences: a checker
never re-runs the builder, it restates the rule and tests it.

The procedures that ask for an inference are the **kernel entry points**. There
are **57**: 54 named procedures and 3 rewriting closures held in the macete table,
at **69 call sites in 8 files**. They are listed in full below, each with the
rules it may record. The **trusted code base** is what is reachable from them,
together with what the write point runs to verify an inference: 678 procedures.

The 8 files are named in a list in the source (`*kernel-caller-files*`), and
the restriction is enforced rather than merely stated. Every time the system
starts it reads all of its own source with the Scheme reader and counts, per
file, the calls to `dg-apply-rule!` and any use of that procedure as a value —
the second being how a file could otherwise pass the capability to code outside
the list. If a file not on the list records inferences, the system names it and
refuses to finish starting. On a clean tree the check prints one line:

    ;; kernel-callers-audit: ok (69 call site(s) to dg-apply-rule!
    ;;   in 8 file(s), all allowed; 0 value use(s))

Widening this base is a legitimate thing to want — a new decision procedure is
the usual reason — but it cannot happen quietly: a file must be added to the
list by hand, which is a deliberate act that leaves a record.

## How the figures below were obtained

The inventory is produced by two independent methods, and they agree.

1. **By reading the source.** All 593 loaded files are read with MIT Scheme's
   reader and each definition walked with scope tracking, so that a mention in a
   comment, a string or quoted data is never mistaken for a call. The two tables
   the kernel reaches indirectly are modelled explicitly: the rewriting closures
   in the macete table, reachable only through `lookup-macete`, whose sole caller
   is `apply-macete!`; and the 66 checkers, reachable only through the write
   point's own verification step.
2. **By running the library.** Every entry point, every proof command and
   `dg-apply-rule!` itself are instrumented, and the entire library — the 453
   files that carry proofs — is re-proved in load order, recording for each
   inference its rule, the entry point that recorded it, and the commands active
   at the time.

The second is what turns the inventory from a claim about code into a claim
about behaviour: **197,669** inferences were recorded over the whole library;
**0** were recorded outside an entry point, and **0** carried a rule the reading
of the source does not attribute to the entry point that recorded it. Each was
verified before it was written, and none was refused. 49 of the 57 entry points
were exercised; the rest are listed below with a dash, which means the library
contains no proof that needs them, not that they are unchecked.

## (a) The entry points

### Logic

| Entry point | File | Rules | Fired |
|---|---|---|---:|
| `pi-direct-inference!` | `primitive-inferences` | `forall-intro` `not-intro` `iff-intro` `implies-intro` `and-intro` | 17781 |
| `pi-antecedent-inference!` | `primitive-inferences` | `iff-elim` `forsome-elim` `not-elim` `or-elim` `and-elim` | 15100 |
| `pi-weaken!` | `primitive-inferences` | `weakening` | 12779 |
| `pi-cut!` | `primitive-inferences` | `cut` | 13686 |
| `pi-instantiate!` | `primitive-inferences` | `forall-elim` | 44753 |
| `pi-spec!` | `primitive-inferences` | `forall-elim` `theorem-assumption` | — |
| `pi-exists-witness!` | `primitive-inferences` | `forsome-intro` | 760 |
| `pi-assumption!` | `primitive-inferences` | `assumption` | 17015 |
| `pi-or-intro-left!` | `primitive-inferences` | `or-intro-left` | 1600 |
| `pi-or-intro-right!` | `primitive-inferences` | `or-intro-right` | 1574 |
| `pi-truth!` | `primitive-inferences` | `truth-intro` | — |
| `pi-backchain!` | `primitive-inferences` | `backchain` | 166 |
| `pi-detach!` | `primitive-inferences` | `detach` | 36874 |
| `pi-contraposit!` | `primitive-inferences` | `contraposition` | — |
| `pi-proof-by-contradiction!` | `primitive-inferences` | `proof-by-contradiction` | 1334 |
| `pi-theorem-assumption!` | `primitive-inferences` | `theorem-assumption` | 18218 |

### Equality and conditionals

| Entry point | File | Rules | Fired |
|---|---|---|---:|
| `pi-eq-subst!` | `primitive-inferences` | `eq-subst` | 4388 |
| `pi-reflexivity!` | `primitive-inferences` | `reflexivity` | 815 |
| `pi-quasi-reflexivity!` | `primitive-inferences` | `quasi-reflexivity` | 290 |
| `pi-if-true!` | `primitive-inferences` | `if-true` | 253 |
| `pi-if-false!` | `primitive-inferences` | `if-false` | 243 |

### Induction

| Entry point | File | Rules | Fired |
|---|---|---|---:|
| `pi-nn-induction!` | `primitive-inferences` | `nn-induction` | 128 |
| `pi-tfi!` | `primitive-inferences` | `transfinite-induction` | 1 |
| `pi-tfi3!` | `primitive-inferences` | `transfinite-induction-3cases` | 4 |

### Sets and schemas

| Entry point | File | Rules | Fired |
|---|---|---|---:|
| `pi-sep-sethood!` | `primitive-inferences` | `sep-sethood` | 73 |
| `pi-sep-mem-intro!` | `primitive-inferences` | `sep-mem-intro` | 199 |
| `pi-sep-mem-elim!` | `primitive-inferences` | `sep-mem-elim` | 378 |
| `pi-comp-mem-intro!` | `primitive-inferences` | `comp-mem-intro` | 22 |
| `pi-comp-mem-elim!` | `primitive-inferences` | `comp-mem-elim` | 22 |
| `pi-big-union-sethood!` | `primitive-inferences` | `big-union-sethood` | 6 |
| `pi-big-union-mem-intro!` | `primitive-inferences` | `big-union-mem-intro` | 19 |
| `pi-big-union-mem-elim!` | `primitive-inferences` | `big-union-mem-elim` | 24 |
| `pi-union-intro!` | `primitive-inferences` | `union-intro` | 2 |
| `pi-union-elim!` | `primitive-inferences` | `union-elim` | 4 |
| `pi-intersection-intro!` | `primitive-inferences` | `intersection-intro` | 5 |
| `pi-intersection-elim!` | `primitive-inferences` | `intersection-elim` | 12 |
| `pi-iota-def!` | `primitive-inferences` | `iota-def` | 27 |
| `pi-iota-in-elim!` | `primitive-inferences` | `iota-in-elim` | 1 |

### Functions and tuples

| Entry point | File | Rules | Fired |
|---|---|---|---:|
| `pi-cartesian-intro!` | `primitive-inferences` | `cartesian-intro` | 31 |
| `pi-cartesian-elim!` | `primitive-inferences` | `cartesian-elim` | 1 |
| `pi-tuples-intro!` | `primitive-inferences` | `tuples-intro` | — |
| `pi-tuples-elim!` | `primitive-inferences` | `tuples-elim` | — |
| `pi-nth-reduce!` | `primitive-inferences` | `nth-reduce` | 264 |
| `pi-length-reduce!` | `primitive-inferences` | `length-reduce` | 29 |
| `pi-functoid-beta!` | `primitive-inferences` | `functoid-beta` | — |
| `pi-lambda-type!` | `primitive-inferences` | `lambda-type` | 361 |
| `pi-lambda-beta!` | `primitive-inferences` | `lambda-beta` | 864 |
| `pi-lambda-beta-hyp!` | `primitive-inferences` | `lambda-beta-hyp` | 128 |

### Rewriting (macete table)

| Entry point | File | Rules | Fired |
|---|---|---|---:|
| `<elementary-macete>` | `macetes` | `macete` | 3365 |
| `<macete:cartesian-decompose>` | `theory` | `cartesian-decompose` | 6 |
| `<macete:tuple-equality-decompose>` | `theory` | `tuple-equality-decompose` | — |
| `apply-macete-to-assumption!` | `macetes` | `macete-hyp` | 2150 |

### Oracles

| Entry point | File | Rules | Fired |
|---|---|---|---:|
| `pi-arith!` | `arith-eval` | `arith-simplify` `arith-forsome` `arith-ground` | 512 |
| `pi-comm-ring-simplify!` | `structure-library/comm-ring-simplify` | `comm-ring-simplify` | 643 |
| `pi-ineq!` | `structure-library/ineq-oracle` | `ineq` | 754 |
| `pi-ring-simplify!` | `structure-library/ring-simplify` | `ring-simplify` | — |
| `pi-sos!` | `structure-library/sos-oracle` | `sos` | 5 |

The trusted code base comprises **678** procedures: `primitive-inferences` 97, `rule-checkers-logic` 90, `rule-checkers-oracle` 81, `rule-checkers-schema` 64, `rule-checkers-rewrite` 51, `deduction-graphs` 46, `macetes` 34, `expressions` 29, `sequents` 27, `wff` 26, `structure-library/ineq-oracle` 24, `presentation` 22, `structure-library/linear-arith` 20, `structure-library/ring-simplify` 15, `structure-library/comm-ring-simplify` 13, `structure-library/sos-arith` 10, `structures` 9, `arith-eval` 9, `theory` 8, `structure-library/sos-oracle` 3.

Four of those files hold the checkers rather than the inferences:
`rule-checkers-logic` verifies the introduction and elimination rules of the
connectives and quantifiers together with cut, weakening, detachment,
substitution of equals and the two reflexivity rules; `rule-checkers-schema`
the separation, comprehension, big-union, description and lambda rules;
`rule-checkers-rewrite` the two macete rules and the two decomposition
closures, re-deriving from the installed theorem, functoid or accessor what the
rewrite was licensed to do; and `rule-checkers-oracle` the arithmetic, ring,
inequality and sum-of-squares certificates. 66 rules are checked, and none is
accepted on trust.

## (b) What each proof command can reach

The table below gives, for each of the 105 proof commands, the entry points it
can reach, and so the rules it can cause to be recorded. This is the bound on
what a command can do. Some of them are substantial — `prop` decides a whole
class of goal, `minimize!` carries out a construction several steps deep — but
each is confined to the entry points listed against it, and every entry point
records a rule from the fixed list.

**Static** is every entry point reachable from the command's own code: the
bound, whether or not the library happens to exercise it. **Observed** is what
was recorded beneath that command while the library was re-proved. A dash under
Observed beside a non-zero call count means the command ran and recorded
nothing — which is the correct behaviour for navigation and session commands
such as `focus`, `show` and `save-proof`.

One set of entry points is common to every command and is left out of the
column rather than repeated 105 times. When a command instantiates a universal
at a term whose definedness the system has not certified, the instantiation
posts a side sequent asking for it, and a hook run after any command that
changed the proof (`*owed-leaf-hook*`) closes such sequents by citing the typing
the context already holds. The hook reaches these 20 entry points:

> `<elementary-macete>` `<macete:cartesian-decompose>` `<macete:tuple-equality-decompose>` `pi-antecedent-inference!` `pi-arith!` `pi-assumption!` `pi-cartesian-intro!` `pi-cut!` `pi-detach!` `pi-direct-inference!` `pi-eq-subst!` `pi-instantiate!` `pi-lambda-beta!` `pi-lambda-type!` `pi-nth-reduce!` `pi-or-intro-left!` `pi-or-intro-right!` `pi-proof-by-contradiction!` `pi-reflexivity!` `pi-theorem-assumption!`

so every row of the table below is to be read as the command's own reach
together with those. The hook proves nothing a proof command could not have
proved by hand; it spares the driver the citation.

For 59 of the 77 commands the library exercises, the two columns agree exactly.
Two commands, `have!` and `use-em`, reach past their static bound, for a reason
their definitions make plain: each runs a procedure supplied by its caller, so
what it reaches depends on what it is handed. Neither adds a rule of its own.

| Command | Kind | Calls | Static | Observed |
|---|---|---:|---|---|
| `ai` | `rule` | 15097 | `pi-antecedent-inference!` | `pi-antecedent-inference!` |
| `apply-thm` | *rule (proposed)* | — | `pi-spec!` | — |
| `arith` | `oracle` | 459 | `<elementary-macete>` `<macete:cartesian-decompose>` `<macete:tuple-equality-decompose>` `pi-arith!` `pi-eq-subst!` | `<elementary-macete>` `pi-arith!` |
| `arith--decide` | *oracle (proposed)* | 459 | `pi-arith!` | `pi-arith!` |
| `ass` | `rule` | 16415 | `pi-assumption!` | `pi-assumption!` |
| `ass-all` | *rule (proposed)* | 605 | `pi-assumption!` | `pi-assumption!` |
| `backup-one` | `meta` | — | — | — |
| `bc` | `rule` | 16 | `pi-backchain!` | `pi-backchain!` |
| `bc*` | `composite` | 76 | `pi-assumption!` `pi-backchain!` `pi-cut!` `pi-instantiate!` `pi-theorem-assumption!` | `pi-assumption!` `pi-backchain!` `pi-cut!` `pi-instantiate!` `pi-theorem-assumption!` |
| `bc*--attempt` | *composite (proposed)* | 76 | `pi-assumption!` `pi-backchain!` `pi-cut!` `pi-instantiate!` `pi-theorem-assumption!` | `pi-assumption!` `pi-backchain!` `pi-cut!` `pi-instantiate!` `pi-theorem-assumption!` |
| `beta` | `rule` | — | `pi-functoid-beta!` | — |
| `bu-me` | `rule` | 24 | `pi-big-union-mem-elim!` | `pi-big-union-mem-elim!` |
| `bu-mi` | `rule` | 19 | `pi-big-union-mem-intro!` | `pi-big-union-mem-intro!` |
| `bu-set` | `rule` | 6 | `pi-big-union-sethood!` | `pi-big-union-sethood!` |
| `calc` | `composite` | 3 | `<elementary-macete>` `<macete:cartesian-decompose>` `<macete:tuple-equality-decompose>` `apply-macete-to-assumption!` `pi-antecedent-inference!` `pi-arith!` `pi-assumption!` `pi-backchain!` `pi-big-union-mem-elim!` `pi-big-union-mem-intro!` `pi-big-union-sethood!` `pi-cartesian-elim!` `pi-cartesian-intro!` `pi-comm-ring-simplify!` `pi-comp-mem-elim!` `pi-comp-mem-intro!` `pi-cut!` `pi-detach!` `pi-direct-inference!` `pi-eq-subst!` `pi-exists-witness!` `pi-functoid-beta!` `pi-if-false!` `pi-if-true!` `pi-ineq!` `pi-instantiate!` `pi-intersection-elim!` `pi-intersection-intro!` `pi-iota-def!` `pi-iota-in-elim!` `pi-lambda-beta!` `pi-lambda-beta-hyp!` `pi-lambda-type!` `pi-length-reduce!` `pi-nn-induction!` `pi-nth-reduce!` `pi-or-intro-left!` `pi-or-intro-right!` `pi-proof-by-contradiction!` `pi-quasi-reflexivity!` `pi-reflexivity!` `pi-ring-simplify!` `pi-sep-mem-elim!` `pi-sep-mem-intro!` `pi-sep-sethood!` `pi-sos!` `pi-tfi!` `pi-tfi3!` `pi-theorem-assumption!` `pi-tuples-elim!` `pi-tuples-intro!` `pi-union-elim!` `pi-union-intro!` `pi-weaken!` | `pi-assumption!` `pi-comm-ring-simplify!` `pi-cut!` `pi-detach!` `pi-eq-subst!` `pi-ineq!` `pi-instantiate!` `pi-theorem-assumption!` |
| `ce` | `rule` | 1 | `pi-cartesian-elim!` | `pi-cartesian-elim!` |
| `choose` | *composite (proposed)* | — | `<elementary-macete>` `<macete:cartesian-decompose>` `<macete:tuple-equality-decompose>` `pi-antecedent-inference!` `pi-arith!` `pi-assumption!` `pi-cut!` `pi-detach!` `pi-direct-inference!` `pi-eq-subst!` `pi-exists-witness!` `pi-instantiate!` `pi-theorem-assumption!` | — |
| `choose-pos` | *composite (proposed)* | — | `<elementary-macete>` `<macete:cartesian-decompose>` `<macete:tuple-equality-decompose>` `pi-antecedent-inference!` `pi-arith!` `pi-assumption!` `pi-cut!` `pi-detach!` `pi-direct-inference!` `pi-eq-subst!` `pi-exists-witness!` `pi-instantiate!` `pi-theorem-assumption!` | — |
| `ci` | `rule` | 31 | `pi-cartesian-intro!` | `pi-cartesian-intro!` |
| `comp-me` | `rule` | 22 | `pi-comp-mem-elim!` | `pi-comp-mem-elim!` |
| `comp-mi` | `rule` | 22 | `pi-comp-mem-intro!` | `pi-comp-mem-intro!` |
| `contra` | *composite (proposed)* | 1 | `<elementary-macete>` `<macete:cartesian-decompose>` `<macete:tuple-equality-decompose>` `pi-antecedent-inference!` `pi-arith!` `pi-assumption!` `pi-cut!` `pi-detach!` `pi-direct-inference!` `pi-eq-subst!` `pi-ineq!` `pi-instantiate!` `pi-theorem-assumption!` | `pi-antecedent-inference!` `pi-arith!` `pi-cut!` `pi-ineq!` |
| `crs` | `oracle` | 643 | `pi-comm-ring-simplify!` | `pi-comm-ring-simplify!` |
| `cut` | `rule` | 13483 | `pi-cut!` | `pi-cut!` |
| `detach!` | `rule` | 962 | `pi-detach!` | `pi-detach!` |
| `di` | `rule` | 18035 | `pi-direct-inference!` | `pi-direct-inference!` |
| `dial` | *meta (proposed)* | — | — | — |
| `dial-wff` | *meta (proposed)* | — | — | — |
| `dk-focus!` | *meta (proposed)* | 44310 | — | — |
| `eps-part` | *composite (proposed)* | 2 | `<elementary-macete>` `<macete:cartesian-decompose>` `<macete:tuple-equality-decompose>` `pi-antecedent-inference!` `pi-arith!` `pi-assumption!` `pi-cut!` `pi-detach!` `pi-direct-inference!` `pi-eq-subst!` `pi-instantiate!` `pi-theorem-assumption!` | `pi-antecedent-inference!` `pi-assumption!` `pi-cut!` `pi-detach!` `pi-eq-subst!` `pi-instantiate!` `pi-theorem-assumption!` |
| `ew` | `rule` | 760 | `pi-exists-witness!` | `pi-exists-witness!` |
| `fact` | `composite` | 18124 | `pi-arith!` `pi-cut!` `pi-detach!` `pi-instantiate!` `pi-theorem-assumption!` | `pi-arith!` `pi-cut!` `pi-detach!` `pi-instantiate!` `pi-theorem-assumption!` |
| `focus` | *meta (proposed)* | 25 | — | — |
| `focus-id` | *meta (proposed)* | — | — | — |
| `goal-status` | *meta (proposed)* | — | — | — |
| `grind` | `composite` | 10 | `apply-macete-to-assumption!` `pi-antecedent-inference!` `pi-direct-inference!` | `pi-antecedent-inference!` `pi-direct-inference!` |
| `grind-and-mp` | `composite` | — | `apply-macete-to-assumption!` `pi-antecedent-inference!` `pi-arith!` `pi-assumption!` `pi-cut!` `pi-detach!` `pi-direct-inference!` `pi-instantiate!` | — |
| `have!` | `composite` | 10358 | `<elementary-macete>` `<macete:cartesian-decompose>` `<macete:tuple-equality-decompose>` `pi-arith!` `pi-assumption!` `pi-cut!` `pi-detach!` `pi-direct-inference!` `pi-eq-subst!` `pi-instantiate!` `pi-theorem-assumption!` | `<elementary-macete>` `<macete:cartesian-decompose>` `apply-macete-to-assumption!` `pi-antecedent-inference!` `pi-arith!` `pi-assumption!` `pi-backchain!` `pi-big-union-mem-elim!` `pi-big-union-mem-intro!` `pi-big-union-sethood!` `pi-cartesian-elim!` `pi-comm-ring-simplify!` `pi-comp-mem-elim!` `pi-comp-mem-intro!` `pi-cut!` `pi-detach!` `pi-direct-inference!` `pi-eq-subst!` `pi-exists-witness!` `pi-if-false!` `pi-if-true!` `pi-ineq!` `pi-instantiate!` `pi-lambda-beta!` `pi-lambda-beta-hyp!` `pi-lambda-type!` `pi-length-reduce!` `pi-nn-induction!` `pi-nth-reduce!` `pi-or-intro-left!` `pi-or-intro-right!` `pi-proof-by-contradiction!` `pi-quasi-reflexivity!` `pi-reflexivity!` `pi-sep-mem-elim!` `pi-sep-mem-intro!` `pi-sep-sethood!` `pi-tfi!` `pi-theorem-assumption!` `pi-weaken!` |
| `ie` | `rule` | 12 | `pi-intersection-elim!` | `pi-intersection-elim!` |
| `if-false` | `rule` | 243 | `pi-if-false!` | `pi-if-false!` |
| `if-true` | `rule` | 253 | `pi-if-true!` | `pi-if-true!` |
| `ii` | `rule` | 5 | `pi-intersection-intro!` | `pi-intersection-intro!` |
| `in-rr` | *composite (proposed)* | 173 | `<elementary-macete>` `<macete:cartesian-decompose>` `<macete:tuple-equality-decompose>` `pi-arith!` `pi-assumption!` `pi-cartesian-intro!` `pi-cut!` `pi-detach!` `pi-direct-inference!` `pi-eq-subst!` `pi-instantiate!` `pi-theorem-assumption!` | `pi-arith!` `pi-assumption!` `pi-cut!` `pi-detach!` `pi-direct-inference!` `pi-instantiate!` `pi-theorem-assumption!` |
| `in-rr--refocus!` | *meta (proposed)* | 306 | — | — |
| `ineq` | `oracle` | 756 | `pi-ineq!` | `pi-ineq!` |
| `inst` | `rule` | 64 | `pi-instantiate!` | `pi-instantiate!` |
| `inst+` | `composite` | 2118 | `pi-arith!` `pi-cut!` `pi-detach!` `pi-instantiate!` | `pi-detach!` `pi-instantiate!` |
| `iota-d` | `rule` | 27 | `pi-iota-def!` | `pi-iota-def!` |
| `iota-e` | `rule` | 1 | `pi-iota-in-elim!` | `pi-iota-in-elim!` |
| `lam-b` | `rule` | 1099 | `pi-lambda-beta!` | `pi-lambda-beta!` |
| `lam-b-h` | `rule` | 128 | `pi-lambda-beta-hyp!` | `pi-lambda-beta-hyp!` |
| `lam-t` | `rule` | 361 | `pi-lambda-type!` | `pi-lambda-type!` |
| `len-r` | `rule` | 29 | `pi-length-reduce!` | `pi-length-reduce!` |
| `mac` | `rule` | 3491 | `<elementary-macete>` `<macete:cartesian-decompose>` `<macete:tuple-equality-decompose>` | `<elementary-macete>` `<macete:cartesian-decompose>` |
| `mac-h` | `rule` | 2076 | `apply-macete-to-assumption!` | `apply-macete-to-assumption!` |
| `mac-h*` | `composite` | — | `apply-macete-to-assumption!` `pi-antecedent-inference!` | — |
| `macm` | `rule` | 9 | `<elementary-macete>` `<macete:cartesian-decompose>` `<macete:tuple-equality-decompose>` | `<elementary-macete>` |
| `minimize!` | `composite` | 6 | `<elementary-macete>` `<macete:cartesian-decompose>` `<macete:tuple-equality-decompose>` `pi-antecedent-inference!` `pi-arith!` `pi-assumption!` `pi-cut!` `pi-detach!` `pi-direct-inference!` `pi-eq-subst!` `pi-exists-witness!` `pi-instantiate!` `pi-reflexivity!` `pi-sep-mem-elim!` `pi-sep-mem-intro!` `pi-theorem-assumption!` | `<elementary-macete>` `pi-antecedent-inference!` `pi-assumption!` `pi-cut!` `pi-detach!` `pi-direct-inference!` `pi-eq-subst!` `pi-exists-witness!` `pi-instantiate!` `pi-reflexivity!` `pi-sep-mem-elim!` `pi-sep-mem-intro!` `pi-theorem-assumption!` |
| `mp` | `composite` | — | `pi-arith!` `pi-assumption!` `pi-cut!` `pi-detach!` `pi-instantiate!` | — |
| `ni` | `rule` | 128 | `pi-nn-induction!` | `pi-nn-induction!` |
| `nth-r` | `rule` | 1731 | `pi-nth-reduce!` | `pi-nth-reduce!` |
| `obtain` | `composite` | 45 | `<elementary-macete>` `<macete:cartesian-decompose>` `<macete:tuple-equality-decompose>` `apply-macete-to-assumption!` `pi-antecedent-inference!` `pi-arith!` `pi-assumption!` `pi-backchain!` `pi-big-union-mem-elim!` `pi-big-union-mem-intro!` `pi-big-union-sethood!` `pi-cartesian-elim!` `pi-cartesian-intro!` `pi-comm-ring-simplify!` `pi-comp-mem-elim!` `pi-comp-mem-intro!` `pi-cut!` `pi-detach!` `pi-direct-inference!` `pi-eq-subst!` `pi-exists-witness!` `pi-functoid-beta!` `pi-if-false!` `pi-if-true!` `pi-ineq!` `pi-instantiate!` `pi-intersection-elim!` `pi-intersection-intro!` `pi-iota-def!` `pi-iota-in-elim!` `pi-lambda-beta!` `pi-lambda-beta-hyp!` `pi-lambda-type!` `pi-length-reduce!` `pi-nn-induction!` `pi-nth-reduce!` `pi-or-intro-left!` `pi-or-intro-right!` `pi-proof-by-contradiction!` `pi-quasi-reflexivity!` `pi-reflexivity!` `pi-ring-simplify!` `pi-sep-mem-elim!` `pi-sep-mem-intro!` `pi-sep-sethood!` `pi-sos!` `pi-tfi!` `pi-tfi3!` `pi-theorem-assumption!` `pi-tuples-elim!` `pi-tuples-intro!` `pi-union-elim!` `pi-union-intro!` `pi-weaken!` | `pi-antecedent-inference!` `pi-detach!` `pi-instantiate!` `pi-sep-mem-elim!` `pi-theorem-assumption!` |
| `obtain-at` | *composite (proposed)* | 12 | `<elementary-macete>` `<macete:cartesian-decompose>` `<macete:tuple-equality-decompose>` `pi-antecedent-inference!` `pi-arith!` `pi-assumption!` `pi-cut!` `pi-detach!` `pi-direct-inference!` `pi-eq-subst!` `pi-instantiate!` `pi-theorem-assumption!` | `pi-antecedent-inference!` `pi-detach!` `pi-instantiate!` `pi-theorem-assumption!` |
| `oi-l` | `rule` | 1600 | `pi-or-intro-left!` | `pi-or-intro-left!` |
| `oi-r` | `rule` | 1574 | `pi-or-intro-right!` | `pi-or-intro-right!` |
| `orelse` | *meta (proposed)* | — | — | — |
| `pbc` | `rule` | 1334 | `pi-proof-by-contradiction!` | `pi-proof-by-contradiction!` |
| `prep` | *meta (proposed)* | — | — | — |
| `prop` | *composite (proposed)* | 727 | `<elementary-macete>` `<macete:cartesian-decompose>` `<macete:tuple-equality-decompose>` `pi-antecedent-inference!` `pi-arith!` `pi-assumption!` `pi-cut!` `pi-detach!` `pi-direct-inference!` `pi-eq-subst!` `pi-instantiate!` `pi-or-intro-left!` `pi-or-intro-right!` `pi-proof-by-contradiction!` `pi-theorem-assumption!` | `pi-antecedent-inference!` `pi-assumption!` `pi-cut!` `pi-detach!` `pi-direct-inference!` `pi-or-intro-left!` `pi-or-intro-right!` `pi-proof-by-contradiction!` |
| `push-not-h` | *composite (proposed)* | 10 | `<elementary-macete>` `<macete:cartesian-decompose>` `<macete:tuple-equality-decompose>` `pi-antecedent-inference!` `pi-arith!` `pi-assumption!` `pi-cut!` `pi-detach!` `pi-direct-inference!` `pi-eq-subst!` `pi-exists-witness!` `pi-instantiate!` `pi-or-intro-left!` `pi-or-intro-right!` `pi-proof-by-contradiction!` `pi-theorem-assumption!` | `pi-antecedent-inference!` `pi-assumption!` `pi-cut!` `pi-direct-inference!` `pi-exists-witness!` `pi-or-intro-left!` `pi-or-intro-right!` `pi-proof-by-contradiction!` |
| `qed` | `meta` | 2160 | — | — |
| `qrfl` | `rule` | 290 | `pi-quasi-reflexivity!` | `pi-quasi-reflexivity!` |
| `quietly` | *meta (proposed)* | — | — | — |
| `repeat` | *meta (proposed)* | — | — | — |
| `replay-proof` | `meta` | — | `<elementary-macete>` `<macete:cartesian-decompose>` `<macete:tuple-equality-decompose>` `apply-macete-to-assumption!` `pi-antecedent-inference!` `pi-arith!` `pi-assumption!` `pi-backchain!` `pi-big-union-mem-elim!` `pi-big-union-mem-intro!` `pi-big-union-sethood!` `pi-cartesian-elim!` `pi-cartesian-intro!` `pi-comm-ring-simplify!` `pi-comp-mem-elim!` `pi-comp-mem-intro!` `pi-cut!` `pi-detach!` `pi-direct-inference!` `pi-eq-subst!` `pi-exists-witness!` `pi-functoid-beta!` `pi-if-false!` `pi-if-true!` `pi-ineq!` `pi-instantiate!` `pi-intersection-elim!` `pi-intersection-intro!` `pi-iota-def!` `pi-iota-in-elim!` `pi-lambda-beta!` `pi-lambda-beta-hyp!` `pi-lambda-type!` `pi-length-reduce!` `pi-nn-induction!` `pi-nth-reduce!` `pi-or-intro-left!` `pi-or-intro-right!` `pi-proof-by-contradiction!` `pi-quasi-reflexivity!` `pi-reflexivity!` `pi-ring-simplify!` `pi-sep-mem-elim!` `pi-sep-mem-intro!` `pi-sep-sethood!` `pi-sos!` `pi-tfi!` `pi-tfi3!` `pi-theorem-assumption!` `pi-tuples-elim!` `pi-tuples-intro!` `pi-union-elim!` `pi-union-intro!` `pi-weaken!` | — |
| `rfl` | `rule` | 816 | `pi-reflexivity!` | `pi-reflexivity!` |
| `rs` | `oracle` | — | `pi-ring-simplify!` | — |
| `save-proof` | `meta` | 2160 | — | — |
| `scout` | `meta` | — | `<elementary-macete>` `<macete:cartesian-decompose>` `<macete:tuple-equality-decompose>` `apply-macete-to-assumption!` `pi-antecedent-inference!` `pi-arith!` `pi-assumption!` `pi-backchain!` `pi-big-union-mem-elim!` `pi-big-union-mem-intro!` `pi-big-union-sethood!` `pi-cartesian-elim!` `pi-cartesian-intro!` `pi-comm-ring-simplify!` `pi-comp-mem-elim!` `pi-comp-mem-intro!` `pi-cut!` `pi-detach!` `pi-direct-inference!` `pi-eq-subst!` `pi-exists-witness!` `pi-functoid-beta!` `pi-if-false!` `pi-if-true!` `pi-ineq!` `pi-instantiate!` `pi-intersection-elim!` `pi-intersection-intro!` `pi-iota-def!` `pi-iota-in-elim!` `pi-lambda-beta!` `pi-lambda-beta-hyp!` `pi-lambda-type!` `pi-length-reduce!` `pi-nn-induction!` `pi-nth-reduce!` `pi-or-intro-left!` `pi-or-intro-right!` `pi-proof-by-contradiction!` `pi-quasi-reflexivity!` `pi-reflexivity!` `pi-ring-simplify!` `pi-sep-mem-elim!` `pi-sep-mem-intro!` `pi-sep-sethood!` `pi-sos!` `pi-tfi!` `pi-tfi3!` `pi-theorem-assumption!` `pi-tuples-elim!` `pi-tuples-intro!` `pi-union-elim!` `pi-union-intro!` `pi-weaken!` | — |
| `scout-run` | `composite` | — | — | — |
| `scout-show` | `meta` | — | `<elementary-macete>` `<macete:cartesian-decompose>` `<macete:tuple-equality-decompose>` `apply-macete-to-assumption!` `pi-antecedent-inference!` `pi-arith!` `pi-assumption!` `pi-backchain!` `pi-big-union-mem-elim!` `pi-big-union-mem-intro!` `pi-big-union-sethood!` `pi-cartesian-elim!` `pi-cartesian-intro!` `pi-comm-ring-simplify!` `pi-comp-mem-elim!` `pi-comp-mem-intro!` `pi-cut!` `pi-detach!` `pi-direct-inference!` `pi-eq-subst!` `pi-exists-witness!` `pi-functoid-beta!` `pi-if-false!` `pi-if-true!` `pi-ineq!` `pi-instantiate!` `pi-intersection-elim!` `pi-intersection-intro!` `pi-iota-def!` `pi-iota-in-elim!` `pi-lambda-beta!` `pi-lambda-beta-hyp!` `pi-lambda-type!` `pi-length-reduce!` `pi-nn-induction!` `pi-nth-reduce!` `pi-or-intro-left!` `pi-or-intro-right!` `pi-proof-by-contradiction!` `pi-quasi-reflexivity!` `pi-reflexivity!` `pi-ring-simplify!` `pi-sep-mem-elim!` `pi-sep-mem-intro!` `pi-sep-sethood!` `pi-sos!` `pi-tfi!` `pi-tfi3!` `pi-theorem-assumption!` `pi-tuples-elim!` `pi-tuples-intro!` `pi-union-elim!` `pi-union-intro!` `pi-weaken!` | — |
| `sep-me` | `rule` | 378 | `pi-sep-mem-elim!` | `pi-sep-mem-elim!` |
| `sep-mi` | `rule` | 199 | `pi-sep-mem-intro!` | `pi-sep-mem-intro!` |
| `sep-set` | `rule` | 73 | `pi-sep-sethood!` | `pi-sep-sethood!` |
| `show` | *meta (proposed)* | 120958 | — | — |
| `simp` | `oracle` | — | `pi-comm-ring-simplify!` `pi-cut!` `pi-eq-subst!` | — |
| `slot` | *composite (proposed)* | 694 | `<elementary-macete>` `<macete:cartesian-decompose>` `<macete:tuple-equality-decompose>` | `<elementary-macete>` |
| `slot-h` | *rule (proposed)* | 74 | `apply-macete-to-assumption!` | `apply-macete-to-assumption!` |
| `sos` | `oracle` | 5 | `pi-sos!` | `pi-sos!` |
| `sp` | `meta` | 2160 | — | — |
| `subst` | `rule` | 4391 | `pi-eq-subst!` | `pi-eq-subst!` |
| `supply` | *composite (proposed)* | — | `<elementary-macete>` `<macete:cartesian-decompose>` `<macete:tuple-equality-decompose>` `apply-macete-to-assumption!` `pi-antecedent-inference!` `pi-arith!` `pi-assumption!` `pi-backchain!` `pi-big-union-mem-elim!` `pi-big-union-mem-intro!` `pi-big-union-sethood!` `pi-cartesian-elim!` `pi-cartesian-intro!` `pi-comm-ring-simplify!` `pi-comp-mem-elim!` `pi-comp-mem-intro!` `pi-cut!` `pi-detach!` `pi-direct-inference!` `pi-eq-subst!` `pi-exists-witness!` `pi-functoid-beta!` `pi-if-false!` `pi-if-true!` `pi-ineq!` `pi-instantiate!` `pi-intersection-elim!` `pi-intersection-intro!` `pi-iota-def!` `pi-iota-in-elim!` `pi-lambda-beta!` `pi-lambda-beta-hyp!` `pi-lambda-type!` `pi-length-reduce!` `pi-nn-induction!` `pi-nth-reduce!` `pi-or-intro-left!` `pi-or-intro-right!` `pi-proof-by-contradiction!` `pi-quasi-reflexivity!` `pi-reflexivity!` `pi-ring-simplify!` `pi-sep-mem-elim!` `pi-sep-mem-intro!` `pi-sep-sethood!` `pi-sos!` `pi-tfi!` `pi-tfi3!` `pi-theorem-assumption!` `pi-tuples-elim!` `pi-tuples-intro!` `pi-union-elim!` `pi-union-intro!` `pi-weaken!` | — |
| `ta` | `rule` | 29 | `pi-theorem-assumption!` | `pi-theorem-assumption!` |
| `te` | `rule` | — | `pi-tuples-elim!` | — |
| `tfi` | `rule` | 1 | `pi-tfi!` | `pi-tfi!` |
| `tfi3` | `rule` | 4 | `pi-tfi3!` | `pi-tfi3!` |
| `ti` | `rule` | — | `pi-tuples-intro!` | — |
| `ue` | `rule` | 4 | `pi-union-elim!` | `pi-union-elim!` |
| `ui` | `rule` | 2 | `pi-union-intro!` | `pi-union-intro!` |
| `undo` | `meta` | — | — | — |
| `use-at` | *composite (proposed)* | 20 | `<elementary-macete>` `<macete:cartesian-decompose>` `<macete:tuple-equality-decompose>` `pi-arith!` `pi-assumption!` `pi-cut!` `pi-detach!` `pi-direct-inference!` `pi-eq-subst!` `pi-instantiate!` `pi-theorem-assumption!` | `pi-assumption!` `pi-cut!` `pi-detach!` `pi-direct-inference!` `pi-instantiate!` `pi-theorem-assumption!` |
| `use-em` | *composite (proposed)* | 1222 | `<elementary-macete>` `<macete:cartesian-decompose>` `<macete:tuple-equality-decompose>` `pi-antecedent-inference!` `pi-arith!` `pi-assumption!` `pi-cut!` `pi-detach!` `pi-direct-inference!` `pi-eq-subst!` `pi-instantiate!` `pi-or-intro-left!` `pi-or-intro-right!` `pi-proof-by-contradiction!` `pi-theorem-assumption!` | `<elementary-macete>` `apply-macete-to-assumption!` `pi-antecedent-inference!` `pi-arith!` `pi-assumption!` `pi-backchain!` `pi-big-union-mem-elim!` `pi-big-union-mem-intro!` `pi-comm-ring-simplify!` `pi-cut!` `pi-detach!` `pi-direct-inference!` `pi-eq-subst!` `pi-exists-witness!` `pi-if-false!` `pi-if-true!` `pi-ineq!` `pi-instantiate!` `pi-lambda-beta!` `pi-lambda-beta-hyp!` `pi-lambda-type!` `pi-nn-induction!` `pi-nth-reduce!` `pi-or-intro-left!` `pi-or-intro-right!` `pi-proof-by-contradiction!` `pi-quasi-reflexivity!` `pi-reflexivity!` `pi-sep-mem-elim!` `pi-sep-mem-intro!` `pi-sep-sethood!` `pi-theorem-assumption!` `pi-union-intro!` `pi-weaken!` |
| `vlet` | `composite` | — | `pi-antecedent-inference!` `pi-cut!` | — |
| `wbc` | `composite` | — | `pi-antecedent-inference!` `pi-arith!` `pi-cut!` `pi-detach!` `pi-instantiate!` `pi-theorem-assumption!` | — |
| `wk` | `rule` | 12793 | `pi-weaken!` | `pi-weaken!` |

## What this inventory does not settle

Three qualifications, so that the figures above are not read for more than they
say.

**Coverage of the run.** The re-proof exercised 2160 of the 2162 results the
build proves. The two it did not were skipped by the driver that produces them,
which declines to re-prove a result already present. The rules they use are
covered by the reading of the source, which does not depend on any proof being
run.

**Commands selected by name.** Several places in the system choose a proof
command at run time from a name rather than calling it directly. Reading the
source cannot follow those edges; running the library does. This is the main
reason both methods are used, rather than either on its own.

**Rules with no route to them.** Two operations are implemented but reachable from
no proof command, so no proof records them: `contraposition`, `truth-intro`.
They remain listed in `KERNEL-RULES.md`, checked like the rest, and counted in
the trusted base: code that exists is code a future command could reach, so the
count is of what is present, not of what is currently used.
