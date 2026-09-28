# `zero-it`: algebraic simplification of an equation goal (design, 2026-09-26)

The user's notes-42 (2026-09-26): "my biggest gripe is the inability to simplify algebraic expressions in
formulas". Asked for: a tactic `zero-it` that takes the goal

    x in rr  ==>  P(x) = Q(x)

reduces `P(x) - Q(x)` to a normal form `R(x)` and returns

    x in rr,  [the eliminated terms all defined]  ==>  R(x) = 0

and the same over a ring: `x in carr(a) ==> P(x) = Q(x)`. The stated purpose is as much to SHOW a dead path
("if in the end it means I have to prove 1 = 2, I can see I've been barking up the wrong tree") as to close
a goal: the tactic must print its normal form even when it cannot close anything.

## What exists (the parts; no kernel change is needed)

* `crs` (`structure-library/comm-ring-simplify.scm`, `pi-comm-ring-simplify!`): the trusted oracle for
  identities of commutative rings, over the number surface (`+ - * ^` and numerals on NN/ZZ/QQ/RR/CC) and
  over an abstract ring (`(ADD a)`, `(MUL a)`, `(NEG a)`, `(ZERO a)`, `(ONE a)` with
  `IS-COMMUTATIVE-RING(a)` in context). Its calculator: `cring-normal-form` (concrete) and
  `cring-generic-normal-form` (abstract) return the canonical sum of monomials as a TERM; a maximal
  non-arithmetic subterm (`f(x)`, `recip(x)`, `sqrt(x)`, a lambda application, an IOTA) is a GENERATOR. The
  oracle demands every generator certified in the ring (`cring-vars-ok?`), which is where the definedness
  of the eliminated terms enters.
* `simp` (`cmd-cring-simp`): rewrites ONE commutative-ring subterm of the goal to its normal form in place.
* `dk-crs-opaque!` (driver-kit.scm): `crs` with `recip` and binder-holding subterms quantified over RR on a
  lane and instantiated back, each typed first. Over RR only.
* `arith` (ground evaluation), `try-at` / `try-small` (counterexample.scm: refute at a value, no inference).
* The equation-to-zero laws: `rr-diff-zero-eq` (RR), `cc-sub-zero-eq` (CC), `nf-sub-zero-eq` (a normed
  field); over an abstract ring the group law `x - y = 0 iff x = y` under its ring name (to be located; if
  the tree lacks it in the ring vocabulary it is one theorem).
* The one-recorded-step mechanism: `keep` (interactive.scm) records ONE step and replays by name through
  `apply-recorded-cmd!`; a `bc*` handler runs inner surface steps with recording suppressed and keeps their
  citations in `*proof-hidden-citations*` for the bill (`record-cmd!`, interactive.scm:135).

## The behaviour

`(zero-it)` on a focus goal `P = Q` (or `P == Q`; on any other goal it prints why it declines and does
nothing):

1. THE RING. From the atoms of `P - Q` and the context typings decide the ring: RR, CC, QQ, ZZ (every
   generator typed there, or a subset -- NN typings lift to RR as `contra` does); or an abstract `a` with
   `IS-COMMUTATIVE-RING(a)` in context and the atoms in `CARR(a)`. NN alone is refused with the reason
   ("NN is not a ring: no subtraction"); mixed or missing typings are reported by atom.
2. THE NORMAL FORM. `R` := the calculator's normal form of `P - Q` (concrete or generic), computed on the
   term, not by inference. Print it in the library's printed syntax:
       ;; zero-it: P - Q  normalises to  R
   and RETURN `R` (data, not only print). Three cases:
   * `R` is the numeral 0: the identity holds in every commutative ring; close the goal by `crs` (one recorded
     step: the oracle), print "closed".
   * `R` is a non-zero NUMERAL: print "the goal is FALSE in every ring where 1 /= 0: it reduces to R = 0"
     and STOP without an inference (the dead-path signal; the what-now lane repeats it beside the
     counterexample lane).
   * otherwise: steps 3-5.
3. THE DEFINEDNESS. For each generator `g` of `R` and of `P - Q` (the "eliminated terms" are generators of
   `P - Q` absent from `R`): land `(IN g D)` from the context, by `dk-real!` / the ring's typing citations
   (`rr-recip-closed` for a `recip` whose non-vanishing is in context, the structure's operation typings);
   what cannot be landed becomes an OPEN SIDE LEAF `(IN g D)`, listed by name in the printout ("owed: g in
   rr"). These leaves are the notes' "[eliminated terms all defined]": visible, and the user closes them.
4. THE IDENTITY. On a lane, `P - Q = R` by `crs`, with `recip` and opaque generators generalised the way
   `dk-crs-opaque!` does (over RR) or handled as generators directly (the generic path accepts opaque
   generators once typed). This is the only trusted step and it is the existing oracle.
5. THE NEW GOAL. `cut` `R = 0`: the branch `R = 0 |- P = Q` is closed by the tactic (from `P - Q = R` and
   `R = 0`, `P - Q = 0`, then the ring's `sub-zero-eq` law); the branch `|- R = 0` is left OPEN and becomes
   the focus, with the side leaves of step 3 beside it. The user's picture is exactly the notes':
       x in rr, [owed typings]  ==>  R = 0

Recording: `zero-it` is ONE recorded step (`(zero-it)`, no arguments: the normal form is recomputed at
replay from the same goal, so the page needs no term), replayed through `apply-recorded-cmd!` like `keep`;
its inner steps run with recording suppressed on the `bc*`-handler path, so their citations reach the bill
through `*proof-hidden-citations*` and `crs` is recorded among the proof's oracles (verify: `*proof-oracles*`
must see an oracle fired inside a suppressed run; if it does not, that is a defect to fix first, since it
would also affect `bc*`). The proof-tex gloss: "simplifying, the goal is R = 0".

Trust: none beyond `crs`. The printed `R` comes from the same calculator the oracle uses, so the lane of
step 4 cannot disagree with the printout; the only way step 4 fails is an uncertified generator, which
step 3 has already posted as an owed leaf -- in that case the lane is not attempted, the owed leaves and
the printout stand, and the goal is left as it was (the tactic reports "P - Q normalises to R; cannot
rewrite until g in rr").

## Out of scope (follow-ups, each one line)

* `P <= Q` and `P < Q` (to `0 <= R`): the same steps with `rr-le-sub` in place of the sub-zero law.
* Simplifying a HYPOTHESIS (`zero-it-h`): the tree has no hypothesis-side rewrite yet (CLAUDE.md, owed).
* A normal form that respects `recip` algebra (rational functions): `crs` does not; `dk-crs-opaque!`'s
  generalisation is what we have.
* A toolbar button on the Emacs panel (mouse-first): after the tactic lands; `emacs/vnb-launch.el` with the
  panel check.

## Checks (test-suite.scm)

(1) RR: `forall x in rr, (x + 1)^2 = x^2 + 2 x + 1` closes, printout "normalises to 0". (2) RR: `x + 1 = x`
prints FALSE, reduces to 1 = 0, no step recorded. (3) RR: `x + x = x` leaves the goal `x = 0` open (the
notes' own example) with no owed leaf. (4) RR with `recip(y)`, `not(y = 0)` in context: the owed typing is
landed, the goal rewritten. (5) RR with `recip(y)` and NO non-vanishing: an owed leaf `recip(y) in rr` (or
the tactic's stated substitute) is open and listed. (6) CC: an identity with `1i`. (7) Abstract ring
`IS-COMMUTATIVE-RING(a)`: `(ADD a) x y = (ADD a) y x` closes. (8) NN goal: refused with the reason. (9) A
proof using `zero-it` page-audits `grounded` and its bill lists `crs` among the oracles. (10) CONTROL: the
replay of a recorded `(zero-it)` reproduces the same open goal.

## Built (2026-09-26)

Files: `zero-it.scm` (new, root; to be loaded right after `"counterexample"` in `load.scm`), one
`apply-recorded-cmd!` case in `interactive.scm` (5340-5341), the what-now lane call in `suggest.scm`
(5005-5011), the registry entries in `tactics-help.scm` (147-148 help, 360 when-to-use, 445 kind
`composite`), twelve checks in `test-suite.scm` (the block headed "ZERO-IT (notes-42"). Line numbers
below are `zero-it.scm` unless another file is named.

### RANDO's walkthrough

**The identity.** RANDO has the goal `forall([x in rr], (x + 1)^2 = x^2 + 2*x + 1)` in the Focus
Workspace and types `(zero-it)` at the prover prompt (or presses RET on the `(zero-it)` line of the
what-now workspace, where the lane offers it: `what-now--show-zero-it`, 536; called from
`suggest.scm`:5010).

1. `zero-it` (467) reads the focus goal and context and calls the pure analysis `zi--analyse` (218).
   `zi--peel` (84) strips the typed universal `x in rr`; the core is an equation; no `(ADD a)` head,
   so the concrete path `zi--analyse-concrete` (267): both sides go through crs's own calculator
   (`cvnb-expand-pow`, `cvnb->poly`, structure-library/comm-ring-simplify.scm), the ring is the
   largest class an atom is typed in (RR, from the binder), and the poly of P - Q is empty.
2. It prints (441)

       ;; zero-it: (x + 1) ^ 2 - (x ^ 2 + 2 * x + 1)  normalises to  0

3. Status `zero`; `zi--crs-direct?` (352) is true (every atom typed, the only binder in a number class,
   an `=` goal), so `zero-it` calls the surface `(crs)` (487), which records itself. Printout:
   `;; zero-it: an identity of commutative rings; closed by crs`. The value is `0`.
4. The page (`script--write-block`, interactive.scm) shows one line, `(crs)`: the recorded step IS the
   oracle.

**The false goal.** On `forall([x in rr], x + 1 = x)` the poly of P - Q is the constant 1
(`zi--poly-const`, 143), status `false` (`zi--finish`, 233). `zero-it` prints (479-482)

    ;; zero-it: x + 1 - x  normalises to  1
    ;; zero-it: the goal is FALSE in every ring where 1 /= 0: it reduces to 1 = 0.  This path is dead; no inference was made.

and returns `1`. No `vnb--run!` is entered, so nothing is recorded, the graph and the focus are
untouched, and the page does not change. what-now repeats the verdict in its ZERO-IT lane, which
offers no move on a false goal.

**The rewrite, with an owed typing.** On `forall([x in rr, y in rr], (x + recip(y)) * y = x * y + 1)`:

1. The analysis finds R = `y * recip(y) - 1` (printed by `zi--poly->term`, 130: crs's poly, highest
   degree first, expand's monomial shape) and status `rewrite`; the atom `recip(y)` is untyped.
2. `zi--run-step!` (499) runs ONE `vnb--run!` named `zero-it` with no arguments (503). Inside it the
   inner steps run with `*replaying?*` and `*in-bc*-handler?*` bound (505-506) -- the path the `bc*`
   handlers use (interactive.scm:128-146) -- so none of them is recorded as a step and their citations
   go to `*proof-hidden-citations*` for the bill; and inside `dk--transaction` (driver-kit.scm:3390),
   so any failure restores graph, focus, script, mints, trace, undo stack and hidden citations.
3. `zi--drive!` (412): `(di)` peels the universals (inside the same step) and the analysis is re-made
   on the sequent; `zi--land-typings!` (403) types what it can (`type-term--plan`, driver-kit.scm:3510,
   or `recip(t)` by `D-recip-closed` when `not(t = 0)` is in context: `zi--recip-plan`, 183) and CUTS
   each remaining typing as an owed side leaf (`zi--cut!`, 363). Here there is no `not(y = 0)`, so
   `recip(y) in rr` is cut and left open.
4. `R = 0` is cut (426); on the branch `R = 0 |- P = Q`, `zi--close-branch!` (384): `P = Q + R` by crs
   on a lane, `subst` P -> Q + R, `subst` R -> 0, and `zi--close-identity!` (372) closes `Q' + 0 = Q'`
   by crs. The focus goes to the `R = 0` leaf.
5. Printout:

       ;; zero-it: (x + recip(y)) * y - (x * y + 1)  normalises to  y * recip(y) - 1
       ;; zero-it: the goal is now  y * recip(y) - 1 = 0
       ;;   owed: recip(y) in rr

   and the proof state shows two open leaves: `recip(y) in rr, x in rr, y in rr => y * recip(y) - 1 = 0`
   (focus) and `x in rr, y in rr => recip(y) in rr` (owed). The value is the term R.
6. The page carries the single line `(zero-it)`. When it is typed back in, the surface command recomputes
   the same normal form from the same goal; `replay-proof` reaches it through the `zero-it` case of
   `apply-recorded-cmd!` (interactive.scm:5341), which calls the surface command (`replay--surface!`).
   `(backup-one)` takes the whole step back (one undo mark, taken by the outer `vnb--run!`).

### Deviations from the design, and findings

* **The closing branch uses no sub-zero law.** The design closes `R = 0 |- P = Q` through `P - Q = R`
  and `rr-diff-zero-eq` / `cc-sub-zero-eq` / the ring's law. Those laws are guarded by `P in RR`,
  `Q in RR`, which for compound P, Q is a typing proof per side (and has no generic-ring counterpart in
  the vocabulary crs reads). The built branch is `P = Q + R` (crs), `subst` P -> Q + R, `subst`
  R -> 0, crs on `Q' + 0 = Q'`: the same on both surfaces, no typing of P or Q, crs the only oracle.
  Its side conditions: P must not occur inside Q, and R must not occur inside an ATOM of Q (f(R) would
  become the untyped f(0)); otherwise the mirror orientation (Q -> P - R) is used; when both fail
  (`f(x) + x = f(x)`: R = x sits inside the atom f(x) of both sides) `zero-it` declines, prints the
  normal form and the reason, and changes nothing.
* **The owed typings are CUT, before `R = 0` is cut.** The design's last paragraph has the lane "not
  attempted" when a generator is uncertified; with the typings cut first, the main branch HAS every
  typing as a hypothesis, the lane always runs, and the new goal reads exactly as in the notes:
  `x in rr, [owed typings] ==> R = 0`. The "cannot rewrite until g in rr" message is therefore never
  printed; a failed lane (rolled back) prints "the rewriting steps did not go through" with the reason.
* **R = 0 records `(crs)`** when crs can close the goal as it stands; `(zero-it)` otherwise (typings to
  land, a `==` goal, a universal crs does not peel, e.g. over `CARR(a)`).
* **NN** is refused for the rewrite only; an identity over NN is closed and a FALSE verdict over NN is
  printed (both are true statements about the embedding NN in RR, and neither states a subtraction).
* **A non-zero constant over an abstract ring** is FALSE "in every ring where 1 /= 0" only when it is
  +-1; `c * 1 = 0` for |c| >= 2 is printed as "FALSE unless the characteristic of the ring divides c".
* **Complex coefficients.** A mixed coefficient a + b i is written `(a + b * 1i)` in R (Scheme would
  print the number as `-1+i`).
* **The ring when no atom is typed in a number class**: the smallest class type-term can type an atom in
  (`f(x)` with `f in FUN(RR, RR)` gives RR); under universals whose guards are not number classes, this
  is decided after the `di`.
* **DEFECT, not fixed here (outside this build's files): an oracle fired inside a suppressed run is NOT
  recorded among the proof's oracles.** `record-proof-debt!` computes `*proof-oracles*` from
  `(script-oracles *proof-script*)` (proof-debt.scm:206) and the certificate's `own-oracles` the same way
  (certificates.scm:311); neither reads `*proof-hidden-citations*`. Measured: a proof whose only oracle
  use is the crs inside `(zero-it)` qeds `proven modulo 0` with NO `[oracles: crs]`; with the scan
  reading the hidden steps it reads `[oracles: crs]`. The same hole affects every `bc*` handler that
  runs `crs`, `ineq`, `arith`, `sos`. The fix is the same argument at both call sites:
  `(script-oracles (append *proof-script* (reverse *proof-hidden-citations*)))`. Suite check (9b)
  fails until it is applied.
* The proof-tex gloss ("simplifying, the goal is R = 0") is not written: `*proof-tex-tactic-doc*` is in
  proof-tex.scm, outside this build's files; the live trace captures the step with the goal after it.
* `reference/TACTICS.md` picks the entry up from `tactics-help.scm`; `tactic-uses-data.scm` (GENERATED
  by docs/gen-tactic-uses.py from the kernel map) has no `zero-it` row until the kernel-map instruments
  are re-run, so the entry carries no `Uses` line meanwhile.


## The value (2026-09-28, the user)

"Even if it fails, the return VALUE should include a string with the same information; this might be
processed by a calling procedure which is attempting to find the correct statement of a theorem." So
`(zero-it)` returns a VERDICT, an association list with accessors `zero-it-status` (`closed`, `false`,
`rewrite` or `declined`), `zero-it-normal-form` (the term R, or `#f` when the goal was not an equation),
`zero-it-report` (every printed line, newline-joined), `zero-it-owed` (the typings posted as open leaves)
and `zero-it-reason` (a decline's reason). The printout is unchanged: printed once at the end as a
`;;VNB-REPORT-BEGIN` / `-END` block (echoed in the Emacs minibuffer), or handed to the Scratch Workspace
through the report channel when the surface evaluates under the quiet flag.

## Built (2): the existential case (2026-09-28)

The user's goal `forall([x, y in nn], forsome([a in nn], (x + y)^4 = x^4 + a * y))` was declined twice
over: the core under the universals is an existential, which the peel did not take, and NN is not a
ring. The second refusal stands (NN has no subtraction). For the first the user proposed, "rather than
changing the kernel, use `cut` with the reduced formula", and that is what was built. On
`forsome([a in C], P = Q)` under typed universals, the witness `a` is an atom typed by its binder; `R`
is computed and printed as before; and the one recorded step cuts the reduced existential
`forsome([a in C], R = 0)`, which is left to the user, and closes the main branch
`forsome([a in C], R = 0) |- forsome([a in C], P = Q)` by skolemising the assumption (`dk-skolem!`: a
fresh `w` with `w in C` and `R[w] = 0`), `ew w`, `di` to split the typing off, `ass` on it, and the
closing branch of section "Built" on `P[w] = Q[w]`. On the example over ZZ the goal becomes

    forsome([a in zz], 4 * x^3 * y + 6 * x^2 * y^2 + 4 * x * y^3 + y^4 - a * y = 0)

which is the display the notes asked for: it says what `a` has to be. When `R` is identically 0
nothing is cut (every `w in C` is a witness; the report says so and suggests `ew`); when `R` is a
non-zero constant the goal is FALSE for every witness. One existential binder is handled; nested ones
and an atom left untyped under the existential decline with the reason. Suite checks (E1) to (E6):
the ZZ example, the NN control, the FALSE case, the two declines, the replay through
`apply-recorded-cmd!`. No kernel file is touched.
