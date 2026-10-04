# Readability examples (notes-58, 2026-10-04)

Current printouts, for the user to judge before the printer is changed.

* `examples-2026-10-04-reader.pdf` -- READER MODE (`proof-reader`, the sketch: the `di` / `ai`
  bookkeeping collapsed, content steps as bullets with their step ranges) for five proofs across
  topics: `binomial-theorem` (rings), `rr-ms-dist` (the metric of RR), `recip-succ-small` (real
  analysis), `interval-widen` (intervals), `card-singleton` (cardinality). Six pages. Its TeX source
  is beside it.
* `binomial-theorem-2026-10-04-full-trace.pdf` -- the FULL TRACE (`proof-tex`) of the same binomial
  theorem, every tactic a numbered sequent: 51 pages, for comparison.

Produced on worker-01 from the band of 2026-10-04 19:19Z by re-running the five proof files
(scratchpad/readability/examples1.scm) and typeset with pdflatex on the primary.

## Round 2 (the user's remarks of 2026-10-04 evening)

`examples-2026-10-04-reader-v2.pdf`: the same five proofs after the first changes to the reader
(proof-reader.scm) and to the row-breaking rule (tex-output.scm):

* a run of steps that establish only trivial facts (typings, structure specialisations such as
  `is-ring(r)` from `commutative-ring-is-ring`, ordering facts) is ONE line: "Clearly 0 in N,
  is-ring(r) and one(r) in carr(r)."; steps 2 to 7 of the binomial theorem are that line;
* a substitution names its equation and the goal it leaves: "Substituting comb-kk(r, x, y, 0)(0) =
  one(r), reduce to ...";
* an equation stays on one line when it fits; the ruler is the plain printed width of the formula,
  not the length of its TeX source (`\operatorname{comb\text{-}kk}` is 29 characters for 7 glyphs);
* the eigenvariables and hypotheses a `di` introduces inside a proof read "Suppose ...", what an `ai`
  unpacks reads "Hence ...", the proposition's own suppositions are not repeated in a branch, and a
  long hypothesis in an induction is "the induction hypothesis";
* `slot`, `mac-h` and `lam-b-h` have prose ("Read off the component dist of the structure",
  "Unfolding converges-to in the hypothesis", "beta-reducing the hypothesis").
