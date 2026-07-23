# Reject-and-rebuild: swapping a proof approach without touching the engine

A recurring situation, once the library starts tracking the literature: a user
(call him RANDO) accepts VNB's trusted machinery -- foundational axioms,
inference rules, tactics -- but rejects the *mathematical development* the library
happens to have chosen for some corner, and wants a different, usually more
down-to-earth, one. He should not have to fork the prover, and he should be able
to *prove* his rebuilt development is free of the thing he rejected.

The warrant ledger is what makes this a mechanical operation rather than an act of
faith. Worked example on disk: `calculus/rando-dieudonne-mvineq.scm` (a probe,
run with `./prover calculus/rando-dieudonne-mvineq.scm`).

## The example

VNB builds the Mean Value Theorem classically:

    mvt  <-  rolle  <-  interior-extremum  <-  extreme-value-max

`extreme-value-max` -- "a continuous function on a compact interval attains its
sup" -- is asserted (warrant `reference`) and is the non-constructive node.
Dieudonne (*Foundations of Modern Analysis*, 8.5) instead proves the mean value
INEQUALITY by an l.u.b./connectedness argument that attains no maximum and never
invokes the extreme value theorem. RANDO prefers Dieudonne.

## The four moves

1. **Audit via the ledger, don't trust.** `mvt` is *proven*, but "proven" is not
   "acceptable to RANDO": a proof resting on an asserted support he rejects is
   tainted for him, and the `proven modulo {...}` bill exposes exactly that. He
   reads the chain down to `extreme-value-max`, provenance `asserted`.

2. **The substrate cut.** Keep `*vnb-files*` THROUGH
   `theorem-library/differentiation` (the reals, their completeness, continuity,
   the derivative and its rules -- everything he accepts) and DROP from
   `theorem-library/extreme-value` down (EVT, Rolle, MVT, Taylor). This is sound
   because the substrate is upstream of the EVT tower and cites none of it
   (verified: differentiation at load.scm line ~526, extreme-value at ~688;
   differentiation.scm references none of extreme-value/rolle/mvt). NB: there is
   no named load target for this yet -- it is a hand-cut of `*vnb-files*`, the
   same tier-seam gap as the "kernel-only" load. See the memory index
   (`presentation_ladder`, the load-seam discussion) for the tiering.

3. **Assert the replacement primitive with chapter and verse.** RANDO adds
   `(support 'mvineq-dieudonne ...)` -- the same statement VNB derives as
   `mvt-upper-bound`, but asserted -- warranted `'(dieudonne "8.5.1 ..." 178)`.
   Dieudonne is on disk (`references.scm`), so the page anchor resolves.

4. **The guarantee is the bill.** The probe runs in the FULL prover, so
   `extreme-value-max` is loaded and available, and STILL the corollary's bill is
   `modulo {mvineq-dieudonne}` -- EVT absent. That is the stronger claim: the
   proof provably does not touch the rejected node, certified by the ledger, not
   by its absence.

## Why this matters beyond one theorem

There are many ways to prove the basic facts of analysis and algebra, and they
sit at very different altitudes -- an elementary estimate vs. a compactness
argument vs. a category-theoretic universal property. VNB does not force a single
one: each theorem's bill names exactly the asserted facts it leans on, so a user
can keep the machinery, swap the primitives, and mechanically demonstrate which
approach his development actually rests on. Preferring the down-to-earth proof is
then a checkable property of the bill, not a matter of taste that hides in prose.
