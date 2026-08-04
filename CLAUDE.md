# VNB proof checker -- working brief

VNB is a proof checker and more generally a math assistant to help
users discover proofs. It is written in MIT Scheme with a user interface in
GNU/Emacs. Much of the documentation is available using a web
interface. There is also a manual which needs periodic update.  The
logical framework is von Neumann-Bernays set theory but with copious
ready-made constructors. Its research state (what is proven, what is
next) lives in Claude's memory index, not here. This file holds the
operational facts that are expensive to rediscover.

## Where the project is going

The **prove-theorem stage is done** (2026-07-11): `spans-submodule-fg` -- and with it
`submodule-fg` -- is proven, with no asserted step. Its purpose was never the theorems
themselves: it was to exercise and stress the machinery, and it delivered, right at the
end, the simultaneous-substitution bug in the macete rewriter (below).

Then the project **refocuses**, onto three things:

1. **Print proofs and read proofs.** `proof-tex` (full trace) and `proof-reader` (sketch)
   exist and are faithful, but they report the *official* level -- three lemma citations --
   where a human wants the *content* level: "Since `a` is a Euclidean ring, `a` is a ring."
   The table is BUILT (`operators.scm`, the ONE table keyed by head symbol; populated by
   `def-predicate` / `def-functoid` at definition time via `register-operator!`, and the
   reading declared next to the definition with `notation!`). It is read by `wff-english`
   (`operator-ref` / `operator-english`), `describe-structure` and `OPERATORS.md`.
   STILL OUTSTANDING: `expr->tex` does NOT read it -- tex-output.scm keeps its own
   per-operator render rules, so TeX and English can disagree. Known first entries: collapse a run of subtype-subsumption
   citations (`register-definitional-structure!` already records the parent chain); capture
   the goal BEFORE each step, not only after, so the reader can always name an existential's
   bound variable (see the `proof-reader--goal-before` comment); render `IS-EUCLIDEAN-RING(a)`
   as "a is a Euclidean ring".

2. **A large database of theorems without proofs**, suitable as raw material for building new
   proofs. Statements, indexed and searchable; the PSS is the seed.

3. Revisiting the manual against all of it.

Do not treat "prove one more theorem" as the goal. The deliverable of a proof request is
usually the obstacles it exposes.

## Running it

    ./prover                  # interactive REPL
    ./prover file.scm         # load a proof script, exit
    ./prover -i file.scm      # load a script, then drop into the REPL
    ./VNB                     # launcher (cold boot re-proves the library: 24 s compiled)
    ./VNB-with-compile        # recompile sources, then launch

Full check suite (distinct from the launcher):

    timeout 900 mit-scheme --quiet --load test-suite.scm < /dev/null

It prints `=== SUMMARY: N passed, M failed ===`.

## COMPILE THE TREE FIRST -- everything below depends on it

`.com`/`.bin` are in `.gitignore` AND excluded from the tarball, so a fresh clone or
unpacked tarball is **interpreted**, and nothing tells you. Compiled vs interpreted, on
this box:

    library load     24 s   vs  ~11 min
    full test suite   6 min vs  ~42 min

Compile once, after a clone/unpack (~10 min, includes one source load):

    ./VNB-with-compile          # or, from a REPL that has loaded load.scm:
    (compile-vnb!)              # incremental: skips files whose .com is fresh
    (recompile-vnb!)            # source-load everything, then compile

If you are ever tempted to conclude "this box is slow", check `ls *.com` first.
`compile-vnb!` skips `*vnb-no-compile-files*` (`test-suite`, `driver-kit`,
`clobber-guard`: the latter two capture `(the-environment)`, which compiles WITHOUT
COMPLAINT and then reports the wrong frame) and any file using a top-level macro
(the .com aborts on load).

After editing a `.scm`, delete BOTH the `.com` and the `.bin`, or Scheme silently
loads the stale binary. `load.scm` names files without extension and prefers `.com`.
(`file-fresh-com?` compares mtimes, so a plain re-save is usually enough.)

**Then RE-COMPILE the files you edited, before you run anything.** An edited file
loads from source; that is fine for a leaf proof script and ruinous for a core
file. Editing `wff.scm` (whose `subst-free`/`free-vars`/`validate-wff!` run in every
inner loop) took one library load from 24 s to **over 14 minutes**. Compiling the
edited files back is a couple of seconds and needs no loaded library:

    mit-scheme --quiet --eval '(begin (compile-file "/abs/path/wff.scm") (exit))'

`compile-vnb!` does the whole tree incrementally but wants a loaded REPL -- which is
the very load you just made slow. Compile first, load second.

**But never compile a file that USES a top-level macro that way.** `compile-file` from a
bare REPL cannot see `bc*` (interactive.scm), `declare-structure` (structures.scm) or
`vlet` (vlet.scm) -- the three entries of `*vnb-top-level-macros*` (load.scm:950) -- so
it compiles the form as an APPLICATION: a fresh `structure-library/ring.com` then dies on
load with `;Unbound variable: carr`, stranding every file after it. `compile-vnb!` knows
this (`*vnb-top-level-macros*` in load.scm) and SKIPS such files -- they load from source,
which costs nothing measurable (their work is in the compiled procedures they call:
moving the whole structure-library to source-load changed a cold load by under a second,
36.8 s -> 36.9 s). So `(compile-vnb!)` from a loaded REPL is the safe recipe; the one-file
`--eval (compile-file ...)` is only for files with no macro use.

**There is no skip-proofs mode.** `VNB_SKIP_PROOFS` was removed (2026-07-09): it had
silently stopped working, and a mode that installs goals as theorems without running their
tactics would give you a library whose `qed` bills read `trust: none` about proofs nobody
checked. Compiling is the honest speedup. If you find the variable named in an old
comment, the comment is stale.

## This box

~3.8 GB RAM (resized 2026-07-08 from 1.9 GB), plus a 2 GB swapfile. One prover run
requests `--heap 120000`, about 1 GB. **Two concurrent provers fit; three do not.**

Never `pkill -f mit-scheme` from a shell command: the pattern matches the killing
command's own command line and takes down the shell (exit 144). A bracket class
(`pgrep -f "[m]it-scheme"`) only saves `pgrep` from matching *itself* -- if the surrounding
shell was launched as `... mit-scheme ...`, `-f` still matches it and you kill your own
shell. Match the executable, not the command line: **`pgrep -x mit-scheme`**.

## Case folding -- the trap that keeps biting

Both the VNB reader and MIT Scheme fold symbols to lowercase. `X` is `x`, `SP` is `sp`.
Three consequences, each of which has cost a debugging session:

1. **Never name a top-level `define` in a proof file like a tactic or a registered
   constant.** `(define BC ...)` rebinds the `bc` TACTIC to a term; the next
   `(bc 'thm)` dies with "The object (...) is not applicable". Real cases: `BC` in
   bordered-eq-border-proof.scm, `TT` in hahn-banach-full-proof.scm and
   nn-least-element.scm, `SP` in a Smith driver, `ID` in mat-equiv-proof.scm.
   Use the file's helper prefix (`ss-`, `bm-`, `cc-`, `hb-`, `me-`). Single/double
   capitals (`BC` `TT` `SP` `NI` `AI` `DI`) are the danger zone. `case-fold-audit` and
   `constant-binder-audit` both inspect WFF binders only, never Scheme defines --
   **`clobber-guard.scm` is the gate that does**: it snapshots every procedure binding
   after `minimize` loads and, after each later file, errors if any was rebound to a
   non-procedure, naming file and symbol. (It found `(define Tm ...)` in
   noetherian-maximal-proof.scm silently killing the `tm` surface helper.) Macros are
   invisible to it -- `environment-lookup` refuses a syntactic keyword, so `bc*` is
   never watched.

2. Structure accessors may inadvertently collide with obvious binder names, but a
   warning is issued (`constant-binder-audit`). `X` used to be a carrier accessor
   and is now `CARR` for algebraic structures, `PTS` for metric spaces (whose
   distance `D` is now `DIST`). Same story for `A`, and for `ID`, now `IDEN`.
   In general avoid single letters -- not a hard and fast rule.

3. Inner binders that would collide take a trailing underscore: `i_`, `j_`, `n_`, `r_`.

## Vocabulary

BONGO refers to a bug, a "tournant dangereux", or an otherwise bad idea.
FUBA, GUBA, RUBA, BLAH etc are generic names.

RANDO MUBA and his sister RANDA MUBA are hypothetical VNB users, invoked when a
question is about the WORKFLOW rather than about the mathematics: "RANDO finishes a
proof and types `qed` -- then what?". Either party may raise them. The user uses them
to request a clarification; Claude uses them to give one. The answer they call for is
a concrete end-to-end walkthrough -- which command, on which surface, writing which
file, at which moment, and what it costs -- with the file and line the claim comes
from, not a description of the design intent. If the walkthrough cannot be given
without checking the code, check the code.

## Working with the user

Treats Claude as a colleague, and can be ill-tempered at times. Does
not appreciate Claude forgetting previously settled questions. Does
not appreciate gratuitous compliments. Avoid obvious narrative
statements such as: "Let me check BLAH before relying on memory". Just
say "Checking BLAH".

Register: The user's interaction with the assistant is on an informal
register, very much like the register coworkers would use to interact
in the course of a technical discussion. Use of metaphor, imagery,
analogies to current events etc. to animate the conversation and ease
the burden of finding a pedantic formulation of an idea. The assistant
is allowed to use the same register if the alternative is too
pedantic. However, in any form of documentation the register should be
formal and precise, even if pedantic.

**More interested in technique than in bulk.** One general mechanism that
dissolves a class of obligations beats N bespoke lemmas that discharge them one
at a time. When a proof needs a nasty step, ask first whether the step is an
instance of something the *machine* can do, and only then whether it is a lemma
the PSS should assert. A tactic is untrusted; a support is trusted surface.

## Writing proof drivers

Proof scripts navigate a deduction graph by moving focus between open leaves.

* **Never navigate by goal shape alone.** Sibling branches routinely share a goal head.
  `(forall k. IN k NN => IH => ...)` and a row conjunct `(forall i_. ... => ... => ...)`
  are both `FORALL/IMPLIES/IMPLIES`. Discriminate on the binder, or better, on a
  CONTEXT formula unique to the branch.
* **Never name an ASSUMPTION by shape either** -- same rule, one level down. An induction
  step's context holds the IH, the instantiated IH, and look-alike `SPANS`/`FORSOME`
  siblings; and a `mac-h`/`ai` fed a formula the driver RECONSTRUCTED (with its own guess
  at the eigenvariable names) matches nothing, silently no-ops, and every later command
  runs in the wrong branch. Use the `dk-` kit in `driver-kit.scm`: run the tactic, DIFF
  the assumption list, keep what appeared. `dk-landed` (errors if nothing landed --
  a silent no-op IS the bug), `dk-landed-1`, `dk-landed-find`, `dk-split!` (ai the landed
  conjunctions to exhaustion), `dk-opened` (leaves a branching tactic opened).
  **`fact` and `inst+` land their whole instantiation chain**, not one formula -- the
  theorem, each partly-peeled form, and the detached result -- so use `dk-fact!` /
  `dk-deepest`, which take the landing no other landing contains.
* **Never rely on where `ass` or `cut` leave focus.** `cut` opens a side goal plus the
  main branch; the `ass` that closes the side goal hands focus to an engine-chosen leaf.
  Re-focus explicitly afterwards.
* A focus helper that returns `#f` and leaves focus put on a miss will hide all of the
  above for weeks. Make it **error**.
* `fact` peels leading universals and auto-detaches each antecedent already in context;
  it will NOT split a conjunctive antecedent (use backward `bc*` for those). If a `fact`
  seems inert, dump the context and look for the one missing typing hypothesis.
  `ord-le-total`, `ord-le-antisymm`, `ord-le-trans` and `ord-succ-immediate` all have
  AND antecedents, so each wants a `(have! '(AND ...))` immediately before the `fact`.
  Without it the citation lands the *implication*, silently, and a following `use-cases`
  cuts the disjunction it was supposed to find in context -- leaving an exhaustiveness
  obligation open branches away.
* **`di` is greedy.** One call takes the whole leading FORALL/IMPLIES prefix, and the
  next call will take a `NOT` (assuming it, goal `FALSITY`) or SPLIT an `AND` goal into
  two leaves. Counting `di`s is therefore not a way to land on a chosen goal -- write a
  peel-until-the-head-changes helper and guard it on progress (`zb-peel!` in
  zz-bezout-proof.scm, `z2-peel!` in zorn-route-two.scm).
* `ai` on a `NOT` assumption is NOT-ELIM, not "reduce the goal to the positive": it fires
  only when the positive is ALREADY in context. Every contradiction is therefore
  `have!` the positive, then `ai` the negation -- never an `ai` you expect to leave the
  positive as your new goal.
* `dk-split!` begins by `ai`-ing the formula you hand it, so handing it an ATOM is an
  error (`dk-landed: the tactic landed no assumption`), not a no-op. It is for
  conjunctions only; for a single landed atom keep `dk-landed-1`.
* `detach!` takes the **IMPLIES** formula, not its antecedent. `(detach! <antecedent>)`
  is a silent no-op.
* **`lam-b` needs the argument TYPED, and needs it BEFORE the reduction.** A lambda
  carries its domain and is defined only there, so `((VNB-LAMBDA x A b) u)` reduces
  cleanly only when `(IN u A)` is evident -- in the context, or supplied by an
  enclosing guarded universal or by an enclosing `VNB-LAMBDA`/`SEP`/`BIG-UNION`
  binder (the walker threads all three). Otherwise the step still fires but **owes
  `(IN u A)` as an extra leaf**, and a driver that was not expecting it wanders.
  The fix is always the same and always one line: land the typing fact *above* the
  `lam-b`, not below it. `mat-ring-proof`'s `mr-close-conj` is the worked example
  (type -> `lam-b` -> cite -> `ass`), and it is why `mr-rops` no longer betas: at the
  point it used to, the binders whose typings were needed did not exist yet.
* `mac-h` **replaces** the assumption it unfolds. Unfolding `(IS-IDEAL s I)` to reach its
  closure conjuncts therefore deletes the hypothesis that `ideal-elt-in-carrier` (and
  every other `fact` guarded on `IS-IDEAL`) needs. Get the projection another way, or
  unfold last.
* `minimize!` lands `GUARD[v:=w]` as **one conjunction**, not as its conjuncts. `ai` it
  before detaching anything against it.
* **A multi-variable substitution is NOT single substitution iterated.** `subst-free*`
  (expressions.scm) is the only multi-binding substitution in the tree; a fold of
  `subst-free` exposes whatever each binding substitutes IN to every later binding.
  That fold WAS `apply-subst` (the macete rewriter) until 2026-07-11: unfolding `SPANS`
  -- parameters `(md n u sm)` -- at `SPANS(md,k,w, INTERSECTION(sm, SPAN(md,n,BLOCK(u,n,1))))`
  let the pending `n:=k`, `u:=w` bindings rewrite the caller's own `n` and `u` INSIDE the
  term matched to `sm`. No error, no warning: a different theorem. It is the case-fold
  disease (a name collision) one level down, and it bites precisely when a recursive
  construction is fed back into its own definition. Iterating `subst-free` is legitimate
  ONLY when peeling nested quantifiers one binder at a time (`cmd-fact`, `mz--type-at!`),
  where the remaining variables are still BOUND.
* **`subst` cannot rewrite a term in OPERATOR position.** Its Leibniz walk reaches
  argument positions only, so `(subst '(= (VADD md) (MUL (MODULE-VECTOR-AG md))))` is a
  silent no-op on the goal `((VADD md) x y)` -- whose head *is* the term you meant to
  replace. Structure accessors (`VADD`, `MUL`, `ADD`, `ACT`) are almost always in operator
  position. Use the equation as a **macete**: `mac` on the goal, `mac-h` on an assumption.
  Any unconditional equation (e.g. `mvag-op`) is one.
* A macete rewrites **every** occurrence. If `fact` lands `SUM(λz. (MUL ag) …) = (MUL ag) …`
  and you `mac-h` it, the operator changes in the summand lambda *and* at the top, while
  the goal's copy of that same summand does not. Normalize **both sides** with the same
  macete (`mac` the goal, `mac-h` the assumption), or `ass` silently fails to match.
* **`cut` of a formula already in context (up to ALPHA) is a silent self-loop.**
  `dg-post!` hash-conses sequent nodes by alpha-equivalence of the assertion plus
  equality of the context, and `context-add-assumption` is alpha-idempotent -- so the
  "main" child of the cut *is* the focus node. One leaf opens instead of two, the graph
  gains a cycle, and the failure surfaces branches later as a missing leaf. Guard with
  `alpha-equiv?` before cutting anything you did not just construct fresh. (This is what
  `minimize!` does; see `mz--cut!` in minimize.scm.)
* `quietly` silences `vnb-guard` as well as `show`, so a tactic that *errors* inside it
  becomes a silent no-op and every later command runs in the wrong branch. A composite
  tactic wants `show` quiet and the guard loud (`mz--quietly`), plus a per-step
  "did this rule fire?" check -- every primitive inference gives its focus node an
  in-arrow, so `(null? (sequent-node-in-arrows n))` afterwards means it did not.
* Debugging recipe that works: `head -N` the proof file into scratchpad, append a dump of
  `(proof-leaves)` with each leaf's goal head and a distinguishing context formula, run it.

## Where a driver helper lives

**Every proof-driving Scheme procedure is either in `driver-kit.scm` -- loaded before any
proof -- or is local to the file that defines it.** There is no third place.

`load.scm` enforces the second half: once `driver-kit` has loaded, each `theorem-library/`
and `calculus/` file is loaded into a fresh `extend-top-level-environment`. A driver's
top-level `define`s stay in its own frame; its `set!` of `*ps*` still reaches the real
binding, and it still sees every tactic, every macro (`bc*`) and everything `driver-kit`
defines. So a stray `(define BC '(succ p))` now breaks only its own file.

Before this, both halves were false and nobody had said so: `proof-leaves` and `any-pred`
were defined *only* inside `theorem-library/nn-least-element.scm` -- a proof script -- and
used by `interactive.scm`, `macetes.scm` and eighteen drivers; `deriv-constant-proof.scm`
exported a thirteen-procedure `dc-` kit to nine drivers, under a comment calling it
"file-local". It worked only because Scheme resolves free variables at call time.

If exactly one file needs a helper, define it there with the file's prefix. If two do, it
belongs in `driver-kit.scm`.

## Layout

    structure-library/   definitions, structures, vocabulary, warranted supports
    theorem-library/     proofs that reach (qed ...); loaded, gated, counted
    calculus/            probes and stress tests; MOSTLY not in load.scm -- but
                         `calculus/finite-ball-subcover-proof` IS loaded (load.scm:787),
                         and load.scm's per-file environment containment covers
                         `calculus/` exactly because such files can be loaded
    reference/           GENERATED (PSS.md, THEOREMS.md, GLOSSARY.md, ...) -- never hand-edit
    scratchpad/          throwaway drivers (untracked)

Also on disk, not described above: `prove-scripts/`, `stress-tests/`, `examples/`,
`structure-notes/`, `archive/`, `printouts/`, `emacs/`, `docs/`, and a SECOND
scratch directory `scratch/` alongside `scratchpad/` (both in use; no rule
distinguishes them).

**Load order matters.** A file using `sp`/`qed`/`make-wff` must come after `interactive`
and `proof-debt` in `load.scm`. Misplacing it gives "Unbound variable: make-wff".

## Library-build policy

New mathematical facts are added as **warranted supports** (`support` + `warrant!`),
not as kernel axioms. A `qed` prints its bill: `proven modulo {...} [trust: ...]`, the
set of asserted facts it leans on.

**The primitive shelf CAN grow, but only by an explicit foundational decision.**
`primitive` provenance (proof-debt.scm:12) is trusted base: it contributes {} to every
bill, exactly like the ~92 axioms of `make-vnb-base-theory`, which theory.scm:613 installs
inside `(fluid-let ((*current-provenance* 'primitive)) ...)`. This brief used to say the
~92 never grow. They grew, once, on 2026-07-27: the **28 ordinal axioms** of
structure-library/ordinals.scm (burali-forti, ord-le-*, ord-succ-*, limit-ord-iff,
ord-segment-*, sup-ord-*, transfinite-induction) are now wrapped the same way, by the
user's decision that the ordinals are foundational rather than owed an argument. They had
been billing as `asserted` only because `theory-add-axiom!` defaults to that
(macetes.scm:1405) and nobody had written the fluid-let. Note the distinction that makes
this NOT a loophole: a `warrant!` moves a fact from `none` to `well-known` -- a better tier
of DEBT; `primitive` says it is not debt at all. Use it only where a mathematician would
answer "because that is what ordinals are", and say so in the file.

They grew a second time on 2026-07-28, and this one is INSIDE
`make-vnb-base-theory`, so the count itself moved: **92 -> 93**. The new axiom is
`app-graph` (theory.scm, at the head of the function-space block):

    forall f, x.   (f x)  ==  IOTA y. (LIST x y) in f

"A functoid is a class; a function is a functoid that is a set." It DEFINES
application as the description over the graph, unguarded -- guarding it on `IS-FUN`
would restrict it to set-functions, which is the restriction it exists to remove.
Safe unguarded because `f` is a VARIABLE and an axiom is instantiated only at TERMS:
`UNION`, `POWER`, `FUN`, `CHOICE`, the accessors and every `def-functoid` head are
constant heads, and `CARR` alone is not a term. Operators are syntax, not objects.
The argument is `docs/functoids-and-functions.md`.

It is **named-only** and has to be: its left-hand side is a bare application with both
sides schema variables, so as a live macete it would rewrite every application in every
goal into an `IOTA`. `declare-named-only!` (macetes.scm) is the new facility that says
so -- distinct from S-10, which catches a rewrite that is UNSOUND; this catches one that
is sound and ruinous to fire automatically. It suppresses the `-rev` companion too.
Adding it moved nothing else: 219 proven, every bill unchanged, every gate still ok.

The shelf grew a THIRD time on 2026-07-28: **`image-set`** (replacement,
structure-library/injection.scm) is now wrapped `primitive` too, by the user's decision
that the image of a set under a class function being a set is what sets ARE. It was the
SOLE entry in the bills of `ord-no-injection-into-set` and, through it, **Zorn's lemma** --
both now read `modulo 0`. Catalog moved 94 -> 95 axioms and 263 -> 262 assertions, i.e. one
fact crossed columns and nothing else did.

The shelf grew a FOURTH time on 2026-08-01, and this one is much the largest: the
user's rebuild of the **arithmetic base**. `number-systems.scm` joined
`*primitive-files*` in load.scm -- the list `prover-load` wraps in
`(fluid-let ((*current-provenance* 'primitive)) (load path))`, alongside
`theorem-library/axioms` -- so its ~107 axioms (Peano closure, the ZZ/QQ/RR/CC field
and order axioms, abs) stopped billing as debt. They had been `asserted` with no
`warrant!` at all, which is exactly `trust: none`, so every arithmetic proof in the
library was billing the axioms of arithmetic as unjustified assumptions. Measured
across all 238 bills, before vs after: **81 shrank, 0 grew, 45 changed trust tier,
5 cleared to `modulo 0`**; `trust: none` bills went 96 -> 51, `modulo 0` 62 -> 67, and
the catalog columns moved 95 -> 212 axioms / 273 -> 156 assertions.

The same cleanup ADDED the axioms that say what each system IS, since the ring/field
axioms alone pinned down none of them (QQ is a model of ZZ; RR was any ordered field):
`zz-generated-by-nn` (moved in from zz-arith.scm), `qq-is-fraction`,
`rr-sup-in`/`rr-sup-upper`/`rr-sup-least` (order completeness, with `SUP` and the
predicates `RR-UPPER-BOUND` / `RR-BOUNDED-ABOVE`), and for CC `cc-i-in`,
`cc-i-squared`, `cc-generated-by-rr`, `cc-conjugate-fixes-rr`, `cc-conjugate-i`.
`qq-dense-in-rr` is the one that is NOT in the base: it needs `<` and `POS-RR`, which
do not exist until order-predicates.scm, so it lives there and stays `asserted` --
honest, since density is a theorem of the base rather than part of it.

A LATER FINDING of the same cleanup, 2026-08-01: **binary minus had no axiom at all.**
Every minus axiom was UNARY (`rr-neg-closed`, `rr-neg-inverse`, ...), while the parser
emits binary `(- x y)` for "x - y"; nothing said `u - v` was a difference. The only
statement about that head was `rr-sub-in-rr`, a `well-known` support that read like a
restatement of `rr-add-closed`. It mattered because **`ineq` -- a TRUSTED oracle --
"linearizes over + - *"**, so it was reading a meaning the theory declined to state.
number-systems.scm now carries `binary-minus-def` (`(- a b) == a + (- b)`), stamped
`definitional` and `declare-named-only!` -- as a live macete its left side matches every
difference in the library. `rr-sub-in-rr` is now PROVEN `modulo 0` in
theorem-library/binary-minus-laws.scm, and that alone shrank **ten** bills (the whole
differentiation/MVT/Taylor arc), because every one of them differences two reals.
The same question was open for `/` and is now CLOSED the same way (verified
2026-08-04): number-systems.scm:107 carries `binary-divide-def`,
`(/ a b) == a * recip(b)`, stamped `definitional` and `declare-named-only!`
(its left side matches every quotient in the library, so firing it live would
rewrite all arithmetic into recip form). The 14 quoted supports that carry a
literal `/` head -- `bdd-fn-*`, the `product-metric` weights, `young-inequality`,
`holder-finite`, `amgm-2-sqrt`, `sqrt-rpow` -- are therefore about the real
quotient now, not an uninterpreted binary operator. Writing `recip` directly is
still the better habit in new statements.

Two consequences worth keeping in view. **The archimedean property is now derivable**
(`nn-unbounded-in-rr` in order-predicates.scm was re-tiered `well-known` -> `informal`
on that basis, and `rr-le-all-pos-nonpos` / `rr-pos-halvable` / `rr-pos-shrink` are in
the same position but were deliberately left alone -- re-tiering moves every citing
bill). And **numeric literals are now exact rationals**: parser.scm's `p--exact-num`
reads every literal with the `#e` prefix, so `0.1` is `1/10` -- NOT
`(inexact->exact .1)`, the dyadic value of the double. arith-eval.scm's sound-arith
gate stays; its remaining job is rejecting inexactness arithmetic PRODUCED
(exp/sin/cos/magnitude), which is a different thing from a literal that was read.

Still `asserted` and arguably in the same class, awaiting the same call: the `card-*`
axioms (cardinality.scm).

**`trust: none` is the WEAKEST tier.** `*pd-trust-order*` (proof-debt.scm) is
`(none hand-wave well-known reference informal proof)`, worst to best, and
`debt-trust-level` reports the worst leaf. It is literally
`(cons 'none *warrant-kinds*)`, so the ranking cannot drift from macetes.scm.
Note that `informal` OUTRANKS `reference` and `well-known`: `informal` means a
rigorous paper-proof exists (just not mechanized), which beats both a citation
nobody has checked and a textbook fact asserted with no argument at all.
`none` means *some leaf has no `warrant!`
at all* -- "scarier than a hand-wave: nothing was even claimed to justify it", as the
code says. The unconditional case prints `modulo 0` and no tier at all; **that** is
the strongest thing a `qed` can say. This brief claimed the reverse until 2026-07-10,
and the misreading is loose in old commit messages ("PROVEN to QED (trust:none)");
proof-debt.scm and the ledger's design notes always had it right. (The brief also
had `informal` and `well-known` swapped until 2026-07-23 -- the same swap that was
fixed in proof-debt.scm on 2026-07-10 and never propagated here.)

What drives the `trust: none` bills -- 51 of the 171 bills that carry any debt, out of
238 proven theorems, 67 of which are unconditional (`modulo 0`); recounted 2026-08-01,
after the arithmetic base went `primitive`, which is what took this from 96 to 51 --
is that **ring.scm / group.scm / abelian-group.scm stamp their projected laws
`asserted` and never warrant them** (`ring-mul-assoc`, `ring-add-left-id`,
`group-assoc`, `group-left-inv`, `abelian-group-idempotent-is-id`, ...), whereas
module.scm wraps the same kind of projection in
`(fluid-let ((*current-provenance* 'definitional)) ...)` (module.scm:64) and so pays
nothing. Re-verified 2026-08-01: those three files contain no provenance wrap at all,
and each name above carries no `warrant!` -- except `ring-mul-zero-left`, which this
list used to include and which IS warranted `well-known`. (The companion figure "438 of
1325 asserted facts carry no warrant" was measured 2026-07-23 and is stale: 117 facts
left the asserted column on 2026-08-01. It wants re-measuring, not adjusting.)
Open triage: the shape projections are projections of the
`def-structure-from-clauses` IFF, exactly like `module-act-unital`, and want
`definitional`; the genuinely derived ones (`abelian-group-idempotent-is-id`) want to
become warranted supports. With arithmetic out of the picture, this is now the largest
single source of `trust: none` in the library.

When a proof turns into a grind, that is a finding, not a failure: add the obvious
lemma to the PSS and record the obstacle. Do not slog.

Before adding a support, ask whether it is an *instance* of something a tactic could do.
`minimize!` (minimize.scm) is the worked example: `(minimize! '(v ...) GUARD MEASURE)` =
"choose v satisfying GUARD with MEASURE as small as possible", leaving only the two
obligations any minimization owes -- MEASURE lands in NN, and GUARD is satisfiable. It
turned `min-degree-entry` and `class-min-pivot` from `'well-known` warrants into
theorems. It uses no choice: well-ordering returns a *member* of the value set, which is
a `SEP` set, so `sep-me` recovers the witness.

## The gates on the install door

`support` and `theory-add-axiom!` install a raw S-expression. Four load-time gates now
grade what comes through, and they are complementary -- each catches a defect the others
call well-formed:

* `connective-arity-audit` (audit.scm) -- FATAL. A flat `(AND a b c)` is read with
  binary-left/right, so extra conjuncts are silently dropped.
* `free-variable-audit` -- warn-only. A free name means whatever the CALLER spells it.
* `head-registry-sweep` (audit.scm, added 2026-08-04) -- warn-only. Every applied head in
  every installed formula, checked against `*constant-registry*` (expressions.scm) --
  the table `free-vars` / `subst-free` actually consult. An unregistered head is read as
  an applied function VARIABLE. `unknown-head-audit` does NOT do this job: it accepts a
  head that is in `*operators*` or on its own allowlist, and reported 0 while 71 heads
  leaked. `register-operator!` now feeds the registry, so the two tables cannot drift.
  Register a new head in `*wff-term-form-heads*` (wff.scm) if it is a TERM constructor;
  a PREDICATE gets a bare `register-constant!` beside `LIMIT-ORD`, because a predicate in
  the term-form list makes `make-wff` reject every goal that mentions it.
* `install-grading` (`install--grade!`, macetes.scm) -- warn-only, and it fires at
  install time, naming the file. It runs `validate-wff!` -- the grading `make-wff`
  applies -- over every installed formula. It grades SHAPE only: arity, and
  wff-vs-term position. The four variadic macete schemas (RESTVAR/SPLICE) are exempt
  by shape.

Controls for the last two: `scratchpad/gate-control.scm`. A gate that passes everything
reads exactly like a clean library, so make it fail on purpose before believing it.

## Shipping

`~/prover-src.tar.gz` is rebuilt by a Stop hook (`~/.claude/settings.json`): gzipped tar
of `prover/`, no `.git`, no `.com`/`.bin`/`.ext`. That is what "the tarball" means.
