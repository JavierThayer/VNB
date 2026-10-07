# The Caratheodory construction, proven (MEASURE-1, 2026-10-07)

The user, reading the book of theorems by library (reference/library-book.tex, part VI, Measure),
noticed that the Caratheodory construction was the one thing in the measure files that was not
proven: five asserted supports in `structure-library/measure.scm`, each with a `reference` warrant to
his notes (Construction of Measures, Chapter 4 Section 1: Def. 4.1, Def. 4.2, Remark 4.3, Prop. 4.4).
The rake had tried them on 2026-09-17 and stopped at a wall it named precisely -- the extended
nonnegative reals had no order theory and `eplus` no laws (the inventory at the foot of
`theorem-library/rake-measure.scm`). That wall was torn down by the batches that followed, M-1
(`measure-laws.scm`) in particular, so the five were provable, and one agent proved them in twenty
minutes: `theorem-library/caratheodory.scm`, 16 theorems, every one `modulo 0`, oracles `ineq` and
`arith` only, statements unchanged.

| statement | the notes |
|---|---|
| `outer-measure-binary-subadditive` | Def. 4.1(3), the binary instance |
| `caratheodory-null-measurable` | Remark 4.3 |
| `caratheodory-superadditive-suffices` | eq. (75) after Def. 4.2 |
| `caratheodory-measurable-sigma-algebra` | Prop. 4.4, first half |
| `caratheodory-measure` | Prop. 4.4, second half |

**The proof's one deviation from the notes.** The notes prove Prop. 4.4 in three steps: binary
unions, then finite families (Lemma 4.5), then a limit. The file goes through one lemma instead,
`caratheodory-prefix-split`: for any sequence of measurable sets `f` and every test set `A`,
`mu(A) = sum_{k<n} mu(A n D_k) + mu(A \ U_n)`, where `U_n = f_0 u ... u f_{n-1}` and `D_k = f_k \ U_k`.
Each induction step uses only that `f_n` is measurable, so "the measurable sets form an algebra" is
never needed. The sigma-algebra half then goes through (75), with `esup-eplus-le` moving the supremum
past `+` and countable subadditivity bounding `mu(A n U)`; the measure half takes `A` to be the union
itself, each `f_k` lying inside `U n D_k` when the `f` are disjoint.

**Integration.** The five supports retired from measure.scm (their glosses carried into the proof
file; the warrants are history), measure.scm's header and rake-measure.scm's inventory marked as
such, the file wired after `integral-convergence` (it cites `esup-eplus-le` from there), library
measure. Nothing in the tree cited the five.

**Kit findings from the agent.** A hand-rebuilt universal clause captured the binder `a_` when the
eigenvariable had the same name (a `dk-clause!` reading the clause off the unfolded predicate would
remove the trap); `mac` with the membership iffs applies outermost-first, so a nested pattern wants a
loop (`dk-unfold-sets!` candidate); seven of measure-laws.scm's local helpers were copied under the
`cth-` prefix and are candidates for the kit pass; three parenthesis slips cost the most probes, and a
per-form balance check before shipping a probe would catch them. The report is
`scratchpad/triage/MEASURE-1-REPORT.md`.
