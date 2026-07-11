# Design note: an intermediate proof language (2026-07-10)

Verbatim exchange, saved for the upcoming proof-print / proof-read phase.
A distilled version lives in Claude's memory (project_intermediate_proof_language).

---

## User

Pause. But before I leave I'd [like] to register a few thoughts related to the
upcoming next phase regarding proof printouts and eventually and hopefully proof
READING.

Ideally there should be an (maybe more than one) intermediate layer(s) between the
conceptual proof you'd find in a paper and the detailed proof script in an .scm
file. What would that language look like? At this point I have no idea.

---

## Claude

Good place to stop. And this is the right question to chew on now, because I just
spent this whole session writing the layer-N artifact (the `.scm` driver) against a
layer-0 artifact (the warrant text) for the *same* theorem, so I have both in front
of me and can say concretely what sits between them.

Start with the observation that the warrant text for `spans-submodule-fg` already
*is* the paper proof, and it's good -- "S is an ideal, euclidean so principal with
generator b, subtract q.x0, apply IH, snoc." What the `.scm` adds on top of that is
almost entirely one of four things, and none of them is mathematics:

- focus navigation -- `sd-branch!`, snapshot the leaves, find the one whose goal is
  an `=`, don't grab a leftover from another branch;
- rewrite direction and plumbing -- `subst` this way not that, `eq-sym` first,
  normalize both sides so `ass` matches;
- definedness discharge -- before `rfl` on `t = t`, type `t` (the `(ADD a b)`, the
  `(VADD ...)`), because `=` is partial here;
- antecedent staging -- fact `nn-succ-closed` *before* `nn-le-refl (succ n)` so the
  guard is present when the next `fact` wants to detach it.

That split is the whole design brief. The intermediate language keeps the signal and
lets an elaborator regenerate the noise, because the noise is bookkeeping, not search.

Concretely, the layer I'd want reads like the warrant but with a justification welded
onto every step:

    step n = succ p:
      let u' = BLOCK u p 1,  bm' = SPAN u',  sm' = sm meet bm'
      have  IS-SUBMODULE md bm'                     by span-is-submodule
      have  IS-IDEAL (SCAL md) S                    by lastcoeff-set-is-ideal
      obtain b   with  b in S,  S <= (b)            by euclidean-ideal-has-generator
      obtain c0, x0   with  x0 = c0.u in sm, last c0 = b
      fix x  with  x in sm
        obtain c   with  x = c.u                    by SPANS, subset
        obtain q   with  last c = q*b               by principal-ideal, S <= (b)
        obtain y   with  y in bm',  x = y + q.x0    by descent-remainder
        have  y in sm'                              by submodule-intersection
        obtain e, w', k'   with  y = e.w', k' <= p  by IH at (u', bm', sm')
        have  x = (e,q).(w',x0)                      by matact-snoc
      conclude  k = succ k',  w = SNOC-COL w' x0

Every `have ... by L` compiles to "fact L, navigate to the resulting subgoal,
subst/ass" -- the elaborator owns the navigation and the direction. `obtain ... by`
is `ew`/`ai`/`inst+`. `fix ... with` is `di`. It's declarative-with-explicit-instances,
which is exactly the register I was already writing in -- I never asked the prover to
*guess* an instantiation, I always wrote `(fact 'matadd-entry '(SCAL md) 1 '(succ n)
...)`. So the elaborator doesn't need to be a prover; it needs to be a good
bookkeeper. That's the difference between this being feasible and being a research
project.

There's a second sub-language hiding in the same proofs, and it's worth calling out
separately: half of what I wrote was equational rewrite chains, and those want to
render as a `calc` block, not as `have`s:

    c.u = sum_{j=1..succ n} c_{1j}.u_j              [matact-entry]
        = (sum_{j=1..n} ...) + c_{1,succ n}.u       [finsum-interval-peel]
        = (BLOCK c 1 n).(BLOCK u n 1) + ...         [finsum-congruence, entry-of-block]

That maps one-to-one onto a `subst` run. So your "maybe more than one layer" instinct
resolves, I think, not into a stack of two languages but into two *constructs* in one
language -- an assertional skeleton (`have`/`obtain`/`fix`) with `calc` chains inside
the leaves.

Now the part that I think actually matters most for where you're headed. You framed
this as a *writing* aid, but the same artifact is the *reading* output. Proof-reading
a `have`/`obtain` skeleton is just... reading it -- that's what a mathematician reads.
The current `proof-reader` reports the tactic level (or, per your notes, the "official"
three-citation level); the thing above is precisely the "content level" you said you
wanted. So the write-language and the read-rendering are the same object approached
from two ends: you can *author* it top-down and elaborate to `.scm`, or you can
*extract* it bottom-up from an existing `.scm` plus its live trace -- segment the trace
at each `fact`/`mac`/`ew`, label the segment "since <cited fact in English>, <resulting
goal in English>." Extraction is the nearer target and it leans on machinery you
already have: the proof-debt ledger knows the citations, the trace has the order. The
head-symbol table you sketched (`head -> arity, TeX, English, ...`) is orthogonal to
all of this -- it renders the individual formulas; this layer supplies the *structure*
the formulas hang on. They compose cleanly.

Three things I'd want to pin down before committing to a shape, because they're where
it gets subtle:

1. **Granularity is a tree, not a level.** "S is an ideal by lastcoeff-set-is-ideal"
   hides a 100-line proof; sometimes you want it hidden, sometimes you want to zoom
   into the six ideal axioms. So the layer should be collapsible the way the reader
   already collapses `di`/`ai` runs -- a proof you can open one node at a time. That's
   probably *the* central design decision.

2. **Definedness may be real content, not noise.** In a partial-`=`/NBG setting, "type
   the term before `rfl`" is sometimes a genuine proof obligation, not plumbing. The
   clean move is a typing oracle the elaborator calls silently, and the reader elides
   -- but you have to decide deliberately that "well-defined" is a step the reader is
   allowed to skip, and be able to un-skip it.

3. **Extraction vs authoring will disagree, and that's information.** If I extract the
   skeleton from my `.scm` and it doesn't match the warrant text, one of them is wrong
   or one is at the wrong altitude -- which is a useful check on both the proof and the
   renderer.

Touchstones (prior art, not to copy): Isar (Isabelle), Mizar, Lean's `have`/`obtain`/
`calc`, TLAPS. The declarative-vs-procedural tension is the whole game.
