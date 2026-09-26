<!-- VERBATIM copy of a section of CLAUDE.md as it stood on 2026-09-18, moved here when
CLAUDE.md was trimmed to its operational rules.  Nothing was edited.  The dated findings,
measurements and case histories behind each rule in CLAUDE.md are in this text. -->

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
on that basis; `rr-pos-halvable` was proven 2026-08-17 and `rr-le-all-pos-nonpos`
2026-08-31, leaving `rr-pos-shrink` as the last of the five still asserted). And **numeric literals are now exact rationals**: parser.scm's `p--exact-num`
reads every literal with the `#e` prefix, so `0.1` is `1/10` -- NOT
`(inexact->exact .1)`, the dyadic value of the double. arith-eval.scm's sound-arith
gate stays; its remaining job is rejecting inexactness arithmetic PRODUCED
(exp/sin/cos/magnitude), which is a different thing from a literal that was read.

The `card-*` axioms (cardinality.scm) were listed here as "still asserted, awaiting the
same call". That is STALE, and the truth is worse than either state: **the shelf is
SPLIT** (measured 2026-08-04). `primitive` -- so contributing {} to every bill --
are `card-empty`, `card-finite-bij`, `card-image-injection`, `card-in-ord`,
`card-insert`, `card-segment`, `card-union-disjoint`. Still `asserted/well-known`
are `card-singleton`, `card-subset-nn`, `card-power-nn`, `interval-card`,
`interval-card-in-nn`. So `card-insert` (add an element, the cardinal goes up) is
trusted base while `card-singleton` (a one-element set has cardinal 1) is debt.
No decision produced that split; it is the residue of two sessions.

It matters more than the tidiness suggests, and the reason is in cardinality.scm's
own header: **CARD is AXIOMATISED, not defined.** The intended meaning -- the least
ordinal in bijection with X -- is stated there in prose and declined in the code. So
`primitive` here does not say "this is what cardinality IS" the way it does for the
ordinals; it says "we are assuming the theory of cardinals", and no bill records it.
Either define CARD (the L1/L2 route in the Zermelo ladder makes that possible) or
demote the seven back to `asserted` + `warrant!` so the assumption is visible.

**One obstacle to defining CARD is now gone (2026-08-12): `interval-card-in-nn` is
GUARDED.** It read `forall a, b. CARD(INTERVAL(a,b)) in NN`, which a defined CARD makes
FALSE -- INTERVAL(1, b) for a non-natural b is all of NN, whose cardinal is omega -- so
the unguarded form blocked the definition outright. It now carries `(IN b NN)` on the
UPPER bound alone (matrix.scm), and the guard is not free: 34 `fact` citations across 13
proof files. 7 already had the typing from their own premises; 26 now land it with
`mat-rows-in-nn` (theorem-library/mat-basics.scm -- `IN Q (MAT m n X) => IN m NN`, which
is why that file exists) off a matrix already in context, and border-mult's `[1, succ q]`
citation lands it with `nn-succ-closed`. The matrix statements type no dimension
(matmul-assoc quantifies `m n k l` with premises only `IN P (MAT m n (CARR A))`), so the
typing has to come off the MATRIX; where the dimension is a data matrix's COLUMN count
the square elementary/unit matrix typed one line earlier (ELEM-F/G/H, MATUNIT: n-by-n)
supplies it, which is how the sites are reached without the column read-off mat-basics
deliberately declines to prove. Library after: 307 proven, every bill byte-identical,
suite 799/0. The failure mode here is LOUD, and that was checked rather than assumed:
delete the two `mat-rows-in-nn` lines from matmul-assoc-proof.scm and the load reports
`qed: proof is not complete; cannot install matmul-assoc` plus its cascade.

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

**The shape projections.** A structure declaration generates an IS-X IFF; each
operation-property conjunct of it, unfolded, IS one of the structure's laws. Stating
those laws separately as `theory-add-axiom!` and never warranting them is what used to
drag every algebra proof to `trust: none` -- the weakest report there is, for facts that
are literally part of the definition. Three different resolutions are now in the tree,
and the difference between them matters:

* module.scm wraps its projections in `(fluid-let ((*current-provenance* 'definitional))
  ...)` (module.scm:64) and pays nothing.
* ring.scm does the same thing by a different door: a `register-provenance! ...
  'definitional` sweep over the eleven names (ring.scm:139, with the reasoning in the
  comment above it). This brief said until 2026-08-10 that ring.scm "contains no
  provenance wrap at all" -- that check looked for `fluid-let` and missed the sweep.
* group.scm's four (`group-assoc`, `group-left-id`, `group-left-inv`,
  `group-identity-in`) are, since 2026-08-10, **PROVEN** `modulo 0` in
  structure-library/subtype-laws.scm (`stl--project!`), beside `abelian-group-opr-comm`,
  which was already done that way. Same work as a provenance stamp and it says more: the
  unfold is CHECKED, not asserted to exist. `ag-cancel-right` -- whose entire bill was
  those three, and which is the deck's worked example of a proof that still owes
  something -- now reports `modulo 0`.

`abelian-group-idempotent-is-id` was the fourth case and the different one: not a
projection but a genuinely DERIVED fact, and with 14 dependents the most-cited
unwarranted leaf in the library. It is **PROVEN** `modulo 0` (2026-08-10) in
theorem-library/cancellation.scm beside `group-cancel-left`, whose shape it borrows --
`a*a = a` and `a*e = a` give `a*a = a*e`, cancel `a` on the left. It became reachable the
same day *because* of the projections above: it needs the right identity (not a group
axiom -- group.scm states only left-id -- but one commutation away in an abelian group)
and `IDEN(s)` in the carrier, i.e. `group-identity-in`.

Measured after all five (2026-08-10): **293 proven, 105 `modulo 0`, 32 `trust: none`**
(was 288 / 97 / 54). Note `\Ntrustnone` is a TALLY, not a grep: PROOF-DEBT.md's own legend
contains the string `trust: none`, so `grep -c` reports one more than the truth.

**The `nary-*` bridge, and what "the weakest leaf" costs you.** `nary-plus-2`,
`nary-times-2` and `nary-neg-1` (numeric-instances.scm) are the CONVERSE, written out, of
`binplus-apply` / `bintimes-apply` / `binneg-apply`, which sit forty lines above them in
the same file stamped `definitional` as the defining equations of the bridge symbols; the
file's own comment says so ("Arity 2 is just binplus-apply / bintimes-apply reversed").
`==` is quasi-equality, hence symmetric, so the converse of a conservative definition
introduces nothing. On the user's call (2026-08-10) all three are now wrapped
`definitional` -- individually, since they are not contiguous, and as a WRAP rather than a
later `register-provenance!` so that `install-theorem!` stamps the auto-generated `-rev`
companion too.

**Stamping those three moved 27 leaf citations and ZERO bills.** The tier of a bill is its
WORST leaf, and every proof citing those three also cites `nary-minus-2`, which was left
`asserted` in the first pass. `trust: none` stayed at 32. `nary-minus-2` was then stamped
too, on a SEPARATE decision because the argument is a different one -- it is not a converse
but a COMPOSITION: `(- x y) == x + (- y)` is `binary-minus-def` (number-systems.scm), and
the two converses rewrite the right-hand side to `binplus x (binneg y)`. `==` is a
congruence, so the chain substitutes, and every step is definitional. That single stamp
took `trust: none` **32 -> 19** and left `modulo 0` at 105 -- so `nary-minus-2` was never
any bill's ONLY leaf, it was merely the worst one in thirteen of them.

The lesson outlives the arithmetic: **reclassifying or proving a leaf buys nothing until it
is the LAST unwarranted leaf of the bills that name it.** Triage by BILL, not by citation
count -- `debt-keystones` ranks by citations and misled exactly here, putting `nary-neg-1`
(14 dependents) at the top of the list when it was worth nothing on its own. The
measurement to run first is the what-if: drop a candidate leaf from every bill and recount
the tiers (`scratchpad/nary-what-if.scm`). It has been right every time.

It happened TWICE in one day. `integral-domain-cancel-zero` was then PROVEN
(below) -- and `trust: none` again did not move, because all seven of its bills also cited
`zz-is-integral-domain`. Proving THAT took 19 -> **11**. Two of the day's five repairs
moved nothing on their own; both were nonetheless necessary, because the shadowing leaf had
to go too.

**`integral-domain-cancel-zero` was already proved -- in a file nobody loaded.**
structure-library/integral-domain-laws.scm unfolds the no-zero-divisor conjunct of
`is-integral-domain-def` and closes it, and it had sat on disk for weeks WITHOUT AN ENTRY IN
`load.scm`, so the proof never ran while integral-domain.scm went on asserting the same fact
unwarranted into seven bills. Nothing catches this: a `.scm` in structure-library/ that
load.scm does not name is simply invisible, and no gate counts files. If you write a proof
file, the entry in load.scm is half the work.

**`zz-is-integral-domain` (7 bills, the last big one) is PROVEN**, in
theorem-library/zz-integral-domain.scm, together with `zz-is-commutative-ring`. Pattern:
zz-ring-is-ring.scm's, one storey up -- unfold the defining IFF, `surface-goal!` the
accessors down to integer arithmetic, and the conjuncts fall to `crs` / `arith` / a
citation. The one piece of real content is that **ZZ has no zero divisors**, which nothing
in number-systems.scm states (there is no ZZ zero-divisor axiom and no sign or trichotomy
machinery for the integers). It is proved where the fact comes from, one system up: QQ is a
FIELD, so `qq-recip-closed` / `qq-recip-inverse` invert any b /= 0, `zz-subset-qq`
(primitive) carries the integers in, and

    a = a.1 = a.(b.b^-1) = (a.b).b^-1 = 0.b^-1 = 0

is four rewrites. `zz-no-zero-divisors` bills `modulo 0`. No induction, no order, no
descent: the integers have no zero divisors because the rationals have inverses.

`integral-domain-nontrivial` went the same way (five lines beside its sibling): it is not
an INSTANCE of a conjunct of `is-integral-domain-def`, it IS one, verbatim. The axiom it
replaced carried the comment "a conjunct of is-integral-domain-def, surfaced as a citable
theorem" -- the proof, written in prose and then not run. Watch for that species of
comment; it is the same failure as the unloaded proof file, one line long.

Three more went the same afternoon, and the pair among them is the cleanest illustration
of the shadowing rule anywhere in the tree, because the what-if PREDICTED it:

* `qq-is-ring` -- PROVEN. `theorem-library/zz-ring-is-ring.scm` is now PARAMETERISED over
  the instance (carrier, defining equation, set-hood fact, three typing axioms) and called
  for ZZ-RING and QQ-RING, rather than copied. The file's name is historical; a third
  numeric ring is one more line of instance data.
* `comm-monoid-is-monoid` -- PROVEN, one line in subtype-laws.scm (`stl--prove-pred!`, the
  abelian-group-is-group shape).
* `nn-add-monoid-is-comm-monoid` -- PROVEN, theorem-library/nn-add-monoid.scm. Those two
  were the ONLY unwarranted leaves of ONE bill (`poly-is-ring`) and shadowed each other:
  measured in advance, either alone moved nothing and the two together moved one.

**`nn-add-monoid` is where NOT to use `crs`.** Its three law conjuncts are closed by
citing `nn-add-assoc` / `nn-add-comm` / `nn-add-zero`, not by the ring simplifier: `crs`
decides commutative-RING identities and **NN is not a ring** -- it has no negation. All
three identities are true of NN, so `crs` would have closed them and nothing would have
looked wrong, but the justification would have been "this holds in any commutative ring",
which is not a statement about NN. An oracle is sound where it applies; knowing that it
applies is the caller's job.

Two driver lessons from that file, both of which cost a run: read the eigenvariables off
the GOAL, never off the context (`dk-asms` order is not the peel order -- taking the
NN-typed hypotheses in context order gives `(w v u)` where the goal wants `(u v w)`, and
`fact` then builds an instance `ass` quietly refuses); and run probe scripts with
`< /dev/null`, because an `error` inside one drops into the `2 error>` REPL and waits on
stdin forever, which looks exactly like an infinite loop.

**`principal-ideal-membership` (5 bills, the largest single one left) is `definitional`**,
stamped at source in ideal.scm. This entry used to end "-- and it is the case where a
PROOF is not available and the stamp is the settled answer". **That was wrong**, and the
counter-example is above: the functoid's unfold equation is provable `modulo 0` by
`(di) (mac 'THE-FUNCTOID) (qrfl)`, and the resulting THEOREM is what `mac-h` needs. The
stamp is still what is IN the tree, and re-tiering moves every citing bill, so it stays
until that measurement is made -- but it is a stamp of convenience, not of necessity. `def-functoid` installs only a rewrite MACETE, not a
theorem, so `mac-h` cannot unfold `PRINCIPAL-IDEAL` in an ASSUMPTION: it warns "unknown
theorem/macete" and the driver sails on with the hypothesis untouched. That is why the
axiom exists at all -- it is the only way to read a member of (a) out of the context,
which is exactly what zz-bezout-proof and spans-submodule-fg-proof do with it. And it is
legitimately definitional: the functoid unfold composed with the SEP separation schema,
both trusted base, i.e. exactly the IFF `def-predicate' would have generated had
PRINCIPAL-IDEAL been a predicate. Same treatment and reasoning as `span-membership`
(mod-seq.scm, 2026-07-10) and the five constructor membership characterisations in
definitional-reclass.scm; this one had simply been missed. Any `SEP`-bodied `def-functoid`
whose members get read out of the context wants the same one-line wrap.

End of 2026-08-10: **301 proven, 109 `modulo 0`, 4 `trust: none`**, in ten repairs, THREE
of which moved nothing on their own. The four that remain have NO shadowing left -- each
is the SOLE unwarranted leaf of its bill, so each is worth its full count:
`zz-is-euclidean-ring` (zz-bezout; needs the division algorithm on ZZ, a different piece
of work), `rr-is-metric-space` (rr-complete), and `inf-subsets-is-set` (two bills:
totally-bounded-has-cauchy-subsequence, block-family-combinatorial).

**2026-09-17: `trust: none` is ZERO.** `zz-is-euclidean-ring` is PROVEN `modulo 0`
(theorem-library/zz-division.scm: `nn-division` by induction on the dividend with the
divisor fixed, `zz-division` reduced to it at `(|a|, |b|)` with four sign cases and a
SIGNED remainder -- the Euclidean law asks only for a size bound, so no correction step --
and the law itself with `VNB-LAMBDA a_ ZZ. abs(a_)` as the degree). The axiom in
numeric-instances.scm is retired. `finsum-single-support`, the sole leaf of ten bills, went
the same day (theorem-library/finsum-single-support.scm, induction on the fold length and a
transfer along `FIN-ENUM`; the set-minus route is blocked twice over, see the driver bullets).
Cold load after both: **1415 proven, 1310 `modulo 0`, 0 `trust: none`**, suite 1220/0. And
the shadowing rule struck once more: `zz-bezout` did not clear -- it now bills exactly
`ring-add-right-id`, `well-known`, which had been hidden behind the axiom the whole time.
(Proven that afternoon in rake batch D; `zz-bezout` is `modulo 0`.) The two rake batches
that followed the same day took the tree to **1501 proven, 1397 `modulo 0`, PSS 333 -> 275**,
suite 1220/0; `submodule-fg` bills 9 leaves, all `well-known` finsum/group facts. Batch 3 the
same evening: **1549 proven, 1467 `modulo 0`, PSS 247**; `submodule-fg` bills two --
`finsum-well-defined` and `finsum-congruence`, and the second was FALSE AS STATED (see the
batch-J driver bullet). **The user chose "shape 1"** (2026-09-17 evening): the `=` conclusion
with the POINTWISE typing `forall z in S. f z in CARR(ag)` as a second antecedent, after the
equality, so every citer's `fact` keeps its arguments. Proven `modulo 0` in
rake-finsum-laws.scm (from the `==` form plus the new `finsum-type-ptwise`). The 52 bills were
transitive: only SEVEN files cite it directly (19 sites), repaired by three agents in one
pass, every bill byte-identical -- the fix at each site is one `have!` of the pointwise
typing before the `fact`, closed by `fun-apply-type-c` off a FUN typing the driver already
held (plus `interval-widen` where the summand's lambda domain is `[1, succ n]` and the index
set `[1, n]`). Spell the `have!` binder `z_`, not the theorem's `z`: `asms-find` is
alpha-aware and `z` would shadow the summand lambda's own binder. Batch 4 the same night took
the finsum FLOOR (`sum-ag-permutation-invariance`, `finsum-well-defined`), `finsum-fubini`,
`card-power-nn`, the setoid facts and the ring powers: **1649 proven, 1601 `modulo 0`, PSS
205, and `submodule-fg` and `matmul-assoc` bill `modulo 0`** -- the theorem the project was
built to prove has, for the first time, no asserted step under it.

**The rake's universe is the BILLS, and that is two-thirds blind** (the user, 2026-09-17).
The PSS holds 333 asserted supports; only 131 are on any bill. The other 202 are cited by
nothing proven, so `debt-greedy-order` scores them zero and `DEBT-BUNDLE.md` never names
them -- among them two-line facts like `ball-is-set` (SEP sethood) and 27 entries warranted
`proof`, a tier that claims a machine-checked proof exists for a fact nobody checked. The
standing instruction is to rake ALL the leaves: the 27 first, then the sethood /
membership / typing shapes (~40, one recipe per shape), then the bill-carrying leaves in
greedy order, then the rest by area.

Also deliberately left `asserted`: the arity 3-5 forms (`nary-plus-3`, ...), which are not
converses of anything -- they FIX the reading of the parser's flat n-ary node as a left
fold, and nothing else in the theory states it. They have no dependents.

**The shelf grew a FIFTH time on 2026-08-24: `nn-add-succ`** (`a + succ b = succ(a+b)`,
structure-library/nn-arith.scm), stamped `definitional` by the user's decision that Peano
recursion for `+` is part of what NN IS. It was the largest single leaf left, and by the
ranking that matters rather than the obvious one: by CITATIONS it was only third (55,
behind `entry-in-carrier` 63 and `interval-card-in-nn` 60), but by SOLE-leaf count it was
first by half again -- **20**, against 13 for `rr-le-all-pos-nonpos` and 8 for
`metric-dist-real`, and neither of the two more-cited leaves is EVER a bill's only one.
Triage by BILL, again. Measured before/after over 719 proven results: `modulo 0`
**448 -> 468**, 35 further bills shortened, NO bill grew, `trust: none` unmoved at **3**
(block-family-combinatorial, totally-bounded-has-cauchy-subsequence, zz-bezout).
`cc-complete` and `rr-complete` clear together, being the same bill; every fact Example 4.7
(`prove-scripts/drives/poly-antiderivative-drive.scm`) must cite is now debt-free, so that
drive can reach `modulo 0`. The sole-leaf ranking was then headed by
`rr-le-all-pos-nonpos` at 13 -- **PROVEN 2026-08-31**, see the raking entry below. Wrapped as a `fluid-let` at the axiom site, not a later `register-provenance!` --
which is what stamped the auto-generated `nn-add-succ-rev` companion too (the load's
`classification:` line went 17 -> **19** de-supported, two names not one).

**And the stamp is NOT free, which is why the site carries a comment saying so.**
`definitional` contributes {} to every bill, so a stamp does not merely re-tier a fact --
it makes the fact invisible to the debt ledger. number-systems.scm axiomatises `+` by its
ALGEBRAIC laws (closure, assoc, comm, `a+0 = a`) and never by its recursion, so calling
the recursion equation "definitional" ALSO asserts that the algebraically-axiomatised `+`
SATISFIES Peano recursion. That is a claim, not a definition, and it is established
nowhere in this tree. The block above the axiom states it plainly and names the exit:
construct NN's `+` by recursion, derive the algebraic laws from it, prove the constructed
operation agrees with the posited one. **Standing rule, confirmed by the user the same
day: a stamp must record its claim.** The `warrant! 'reference` was removed rather than
reworded, on the ordinals precedent -- a warrant is a better tier of DEBT, and
`definitional` says there is no debt.

**`nn-mul-succ` was measured and deliberately NOT stamped -- and the restraint PAID,
because its argument was NOT identical.** The entry here used to say it was. It is
**PROVEN** `modulo 0` (2026-08-31, theorem-library/nn-parity-proof.scm): `succ(b) = b + 1`
is `nn-succ-plus-one`, already proven there, and then `nn-distributive` and `nn-one-mul`
-- both `primitive` -- give `a * succ(b) = a*(b+1) = a*b + a*1 = a*b + a` in four
rewrites. Addition's recursion has to be ASSUMED (nothing in the tree implies it;
`nn-succ-plus-one` is proved FROM it, so the reverse move is circular); multiplication's
does not. A stamp by analogy would have assumed what a proof establishes -- which is the
argument for the one-explicit-decision-per-fact rule, now with a scar to point at.
It sits in nn-parity-proof rather than a file of its own because `nn-succ-plus-one` is
produced there and consumed thirty lines later: no separate file fits between.

**THE RAKE, 2026-08-31: the greedy what-if is MECHANIZED, and the ranking is not the
obvious one.** This file already said triage by BILL, not by citation count, and named
`nary-neg-1` as the scar. That triage is now a procedure and a generated document:
`debt-greedy-order` (proof-debt.scm) repeatedly takes the leaf that would empty the most
bills OUTRIGHT, removes it from every bill and goes again; `debt-entry-routes` attributes
each leaf of a bill to the direct citation it entered through. Both are written to
`reference/DEBT-BUNDLE.md` at load, recomputed and never stored, so the ranking cannot go
stale the way `debt-keystones` misleads. Section 1 answers "prove these N, in this order,
and N bills reach `modulo 0`"; section 2 turns a 113-leaf bill into "87 via
smith-diagonalization, 41 via free-transport" -- the arcs, not a wall of symbols.
Routes OVERLAP by construction (a leaf reachable two ways is counted under both), so the
columns do not sum to the bill; that is stated in the file.

Measured over one session with it: **981 -> 990 proven, `modulo 0` 635 -> 680**, billed
results 346 -> 310, one-leaf bills 70 -> 38. Nine facts crossed from asserted to proven,
and the ordering mattered more than the count -- `rr-le-all-pos-nonpos` alone was 20
bills, and by CITATIONS it was nowhere near the top.

**Seven of those nine fell to ONE driver, and the derivation had been written down in May
and never run.** `theorem-library/op-typing.scm` proves the codomain typing of a structure
operation in APPLIED form -- `((MUL r) a b) in CARR(r)`, `((DIST s) x y) in RR` -- for
ring ADD/MUL/NEG, commutative-ring ADD, METRIC-SPACE DIST, NVS VNRM/VADD. Every one was a
separate support whose warrant recited the same four lines ("From (op MUL (CARTESIAN CARR
CARR) CARR) + fun-apply"). The driver is: peel, `mac-h` the IS-X unfold, split, and then
either `fun-apply-type-c` directly (unary) or bridge the TUPLING first -- a structure
operation eats one pair while the parser emits the curried `(f a b)`. Two mechanics make
it work and neither is obvious:

* **`apply-tupling-2` is stated with `==`, and `subst` takes a `==` as happily as a `=`**
  (pi-eq-subst!). So the bridge is one rewrite of the goal. It has to be `==`: both sides
  are undefined when `f` is not tuple-typed, and `=` is the definedness predicate.
* **`binary-apply-type` does not exist and is not needed.** The May note said these
  closure axioms "become derivable via IS-X unfold + the typing conjunct +
  binary-apply-type"; the two pieces that would have built it (`fun-apply-type-c`,
  proven; `pair-in-cartesian`, proven) do the job directly.

`nvs-act-in-vec` has the same shape and does NOT fall to it: ACT's domain in the NVS
declaration is the scalar ring's carrier, not `CARTESIAN(RR, VEC(m))`, so the pair does
not type without the normed-field view. Left asserted, deliberately.

**`ineq` premise indices are 1-BASED** (ineq-oracle.scm:206 -- `(>= i 1)`,
`(list-ref asms (- i 1))`). A 0-based finder is in range, names the neighbouring
formulas, and the oracle then reports "goal not a linear-RR consequence" -- blaming the
goal, exactly the misdirection the 2026-08-15 skip-a-non-arithmetic-premise comment
describes one line above the check.

**Proving a fact that used to be an axiom moves it past the view specializer.**
`view-as-auto-specialize!` runs inside `def-functor`, i.e. when views.scm loads
(load.scm:195) -- long before the interactive tactics exist, so a theorem proved in
theorem-library/ (load.scm 500+) is invisible to it and its view companions are never
built. `abelian-group-idempotent-is-id-module-vector-ag` is cited BY NAME in
theorem-library/module-zero-act, so the move would have silently deleted it.
cancellation.scm already re-ran the specializer for RING-ADDITIVE-AG for this exact
reason. The trap: the unrestricted re-run installed **67** companions -- every
abelian-group theorem proved since views.scm -- to deliver the one that was needed. So
`view-as-auto-specialize!` now takes an optional SECOND argument naming a single theorem
(structures.scm), and errors on an unknown name:

    (view-as-auto-specialize! 'MODULE-VECTOR-AG 'abelian-group-idempotent-is-id)   ; 1, not 67

Reach for the unrestricted form only when carrying a whole backlog across a view is what
you mean, as the RING-ADDITIVE-AG line does.

(The companion figure "438 of 1325 asserted facts carry no warrant" was measured
2026-07-23 and is stale: 117 facts left the asserted column on 2026-08-01. It wants
re-measuring, not adjusting.)

**The continuity algebra is six-sevenths proven, and the last two cost no estimate**
(2026-08-18). `cont-transfer-ptwise-eq` (theorem-library/continuity-transfer.scm) and
`sub-continuous-at` (theorem-library/continuity-sub.scm) are PROVEN `modulo 0`, and with
them **`diff-implies-continuous` bills `modulo 0`**. Only `compose-continuous-at` and
`cont-agree-off-pt` are still asserted in continuity-algebra.scm.

Neither needed an eps/delta argument, and that is the transferable part:

* The TRANSFER is what the algebra was missing. `sum-continuous-at` concludes about the
  LITERAL term it builds, not about "any map that happens to be the sum" -- so without a
  transfer the algebra can only ever conclude about lambdas it built itself. The proof is
  two instances of the pointwise hypothesis and two `subst`; the distance is never opened
  into `abs`, so nothing in it is about RR. (It is stated at RR-MS only because that is
  where continuity-algebra states it.)
* Given the transfer, the DIFFERENCE is a composition of three theorems already in the
  tree -- `neg-continuous-at`, `sum-continuous-at`, `cont-transfer-ptwise-eq` -- plus one
  `crs` to bridge `(- (g w) (h w))` and `(+ (g w) (- (h w)))`. The retired warrant
  proposed the eps/2 route ("a difference is the sum estimate with `-' throughout"), which
  is a second copy of continuity-sum's driver. It was not needed. `neg-continuous.scm`
  moved earlier in load.scm to make this available.

Two mechanics worth keeping. **`mac-h` is destructive, so read a typing off a hypothesis
inside a `have!` LANE**: `(have! '(IN g (FUN RR RR)) (lambda () (mac-h 'is-continuous-at ...)
(split) (slot-h 'PTS ...) (ass)))` unfolds on the side branch only, and the main branch
keeps `IS-CONTINUOUS-AT` intact for the next `fact`. Done in the main branch instead, the
following `fact` silently lands an implication. And `slot-h` is destructive the same way:
in continuity-transfer.scm `(IN b (PTS RR-MS))` is needed as itself (to detach g's
delta-universal) AND as `(IN b RR)` (to detach the pointwise hypothesis), so the `inst+`
must come BEFORE the `slot-h`. continuity-sum.scm meets the same trap and solves it the
other way, with a `have!` that puts the PTS form back.

When a proof turns into a grind, that is a finding, not a failure: add the obvious
lemma to the PSS and record the obstacle. Do not slog.

**`prop` (prop.scm, 2026-08-15) is the second worked example** of that principle, and the
cheapest one to reach for: it decides whether the focus goal follows from the context by
PROPOSITIONAL logic and closes it if so. It dissolves a whole class of leaves that were
each obvious and each wanted a different hand-picked dance -- `(oi-l)(ass)` when a disjunct
is in context, `(oi-r)` plus a conjunction split when it is not, `(ai)` on a negation when
the context is contradictory, `use-em` plus two bodies when the goal needs a case. Atoms
are opaque: `x in a`, an equation, a whole `forall(...)` -- so it will NOT instantiate a
quantifier or reason about equality, and it declines with a COUNTERMODEL naming which atom
must be true and which false, which is usually the missing hypothesis. It **adds no
trust**: it decides semantically (three-valued evaluation, pruned search), then discharges
through `di`/`ai`/`oi-l`/`oi-r`/`ass`/`use-em`/`have!`/`detach!`, so a `qed` over a
`prop`-closed proof bills `modulo 0` and the recorded script is the ordinary step-by-step
proof (verified: `scratchpad/prop-debt-probe.scm`). It is in `*what-now-fire-probes*`, so
the copilot now prints `(prop) => CLOSES the goal` on such a leaf.

Two traps it hit, both the alpha-self-loop above, reached through helpers: an opening
`pbc` put `not G` in the context and then `use-em`'s own `em-prove!` re-assumed it (fixed
by checking the GOAL against the assignment instead -- no pbc at all); and splitting on the
atom of a goal that IS `(OR p (not p))` cuts the goal itself (fixed by routing that shape
to `em-prove!`). Battery: `scratchpad/prop-battery.scm`, 19 cases including five that must
NOT close.

**`contra` (contra.scm, 2026-08-15) is the third**, and it came out of a leaf the user
was driving: unfolding `make-set-membership` in a list-induction base case leaves

    nth(i,l) = x,  i <= length(l),  1 <= i,  i in nn,
    x in set,  length(l) = 0,  l in tuples(a)   |-   x in empty-set

which is closable only because `1 <= i <= length(l) = 0` is absurd. The copilot said
nothing, and the reason was worth more than the leaf. `prop` cannot see it -- the three
order facts are opaque atoms to it, and it correctly reports a countermodel. `ineq` can
do the arithmetic, but **two input-handling traps kept it out of reach**, and both are
now fixed:

* A named premise that is NOT arithmetic used to make the whole call fail. `(ineq 1)`
  closed a goal that `(ineq 1 2)` refused, where 2 was a harmless `u in rr` typing -- and
  the message said "goal not a linear-RR consequence", blaming the goal. Such a premise
  is now SKIPPED; dropping a premise can only make Fourier-Motzkin prove less, so this is
  soundness-preserving by construction.
* `ineq-atom-rr-ok?` demands an `IN _ RR` certificate for every atom of every accepted
  premise. A combinatorial context types its terms in NN, so the oracle refuses. **The
  fix is NOT to weaken the oracle** -- it is trusted, and widening what it accepts widens
  the trusted surface. `contra` DISCHARGES the precondition instead: land the `IN t NN`
  facts the context already fires (found generically by the forward-citation scan, e.g.
  `length(l) in nn` from `l in tuples(a)`), then lift each to RR by `nn-in-rr` (proven,
  `modulo 0`).

The remaining trap is the sharp one: an `=` is arithmetic in SHAPE, so `nth(i,l) = x`
gets accepted and contributes the atoms `x` and `nth(i,l)`, which can never be certified
-- one irrelevant equation in the context poisons a call whose real premises were fine.
`contra--usable-indices` therefore filters premises by the oracle's own test before
naming any. It **probes on a scratch state before committing** (there is no undo: a
composite that cut first would strand two unprovable leaves), adds no trust beyond
`ineq`'s, and is in `*what-now-fire-probes*`, so the panel prints `(contra) => CLOSES the
goal`. Four suite checks; suite 880/0.

Before adding a support, ask whether it is an *instance* of something a tactic could do.
`minimize!` (minimize.scm) is the worked example: `(minimize! '(v ...) GUARD MEASURE)` =
"choose v satisfying GUARD with MEASURE as small as possible", leaving only the two
obligations any minimization owes -- MEASURE lands in NN, and GUARD is satisfiable. It
turned `min-degree-entry` and `class-min-pivot` from `'well-known` warrants into
theorems. It uses no choice: well-ordering returns a *member* of the value set, which is
a `SEP` set, so `sep-me` recovers the witness.

