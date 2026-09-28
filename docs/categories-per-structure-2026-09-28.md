# The category of a structure: what is generated, where it is wrong, and a proposal (2026-09-28)

The user's notes-43: "How is the Hom functor defined in the category corresponding to a structure? I may
have been a little careless. It is easy enough for some kinds, but in general algebraic structures it may
not be so easy. Also, even for metric spaces there may be more than one category. Maybe the approach is
that there is a DEFAULT category corresponding to a structure (in most cases very restrictive) but it would
allow us to define alternatives to the default, like the Lipschitz category or the continuous category."

## What the tree does today (structures.scm, batch 33 of 2026-09-25)

A `declare-structure` of `X` with carriers `C_1 ... C_k` generates the morphism predicate
`IS-HOM-X(a, b, f_1, ..., f_k)`, one map per carrier, holding exactly when

* `IS-X(a)` and `IS-X(b)`;
* `f_i in FUN(C_i(a), C_i(b))`;
* `S(a) = S(b)` for each SUBSTRUCTURE slot `S`;
* `f_i(c(a)) = c(b)` for each constant `c` landing in carrier `i`;
* `f_j(OP(a)(x, ...)) = OP(b)(f(x), ...)` for each operation slot, argument by argument, a sort that
  is not a carrier (the reals of a norm or a distance, the scalars) being mapped by the identity.

For a structure with one carrier the declaration also installs the hom-set `HOM-X(a, b)` as the SEP of
`FUN(C(a), C(b))` by `IS-HOM-X`, and `theorem-library/hom-laws.scm` proves, by one generic driver over the
slot list, that the identity is a morphism, that morphisms compose, and that the hom-set is a set;
`hom-functors.scm` proves that post- and pre-composition by a morphism map hom-sets to hom-sets, with the
functor laws once over any set of functions. `declare-hom!` REPLACES the generated predicate by a
hand-written one; the hom-set names the predicate, so it sees the replacement. Three species use it:
`TOP-SPACE` and `METRIZABLE-TOP-SPACE` (continuous maps: preimages of opens are open) and `RINGOID`.

So the generated notion is the homomorphism of the SIGNATURE, which is the standard notion for an
algebraic structure (semigroups to fields, modules over a fixed ring, vector spaces). It is also the
generated notion for every structure whose defining data is NOT an operation, and there it is wrong or
beside the point. Read off `reference/DEFINITIONS.md`:

| structure | generated arrows | verdict |
|---|---|---|
| `METRIC-SPACE` | isometries: `dist(b)(f x, f y) = dist(a)(x, y)` | deliberate (metric-continuity.scm:108), but not the category analysis works in |
| `NORMED-VECTOR-SPACE`, `NORMED-AG`, `NORMED-FIELD` | linear and norm-preserving | the isometric category again; bounded linear maps are the working one |
| `MEASURABLE-SPACE` | `f in FUN(PTS a, PTS b)` and `SIGMA(a) = SIGMA(b)` | WRONG: `SIGMA` was treated as a substructure slot to be held EQUAL; `f` is unconstrained. A measurable map has `PREIMAGE(f, E) in SIGMA(a)` for every `E in SIGMA(b)`. |
| `MEASURE-SPACE` | the same plus `MEAS(a)(E) = MEAS(b)(E)` for all `E` | WRONG for the same reason, and the measure clause compares the two measures on the same sets instead of `MEAS(b)(E) = MEAS(a)(PREIMAGE(f, E))` |
| `C-METRIC-SPACE`, `PSEUDOMETRIC-SPACE` | isometries | as for METRIC-SPACE |
| `TOP-SPACE`, `METRIZABLE-TOP-SPACE` | continuous maps (declared by hand) | right |
| `SETOID` | nothing (two carriers) | open, as recorded |

The two WRONG rows are the carelessness the note suspected, and they were not caught because
`hom-laws.scm` proves the identity and composition laws for them and those laws hold for the wrong
predicate too (the identity preserves `SIGMA`, composition preserves equality). The generic driver
checks that the declared arrows form a category, not that they are the intended arrows. Nothing in the
tree cites either predicate.

## The proposal: a default category per structure, and named alternatives

1. **The default.** `IS-HOM-X` / `HOM-X` stay the DEFAULT category of `X`, generated as now, with two
   repairs at the generator: a slot whose value is a FAMILY OF SUBSETS of a carrier (`SIGMA`, `OPENS`)
   generates the preimage clause `forall E in S(b). PREIMAGE(f, E) in S(a)`, not equality, so
   `MEASURABLE-SPACE` gets measurable maps and `TOP-SPACE` no longer needs its override; and a slot whose
   value is a FUNCTION ON such a family (`MEAS`) generates the transport clause
   `MEAS(b)(E) = MEAS(a)(PREIMAGE(f, E))`, so `MEASURE-SPACE` gets measure-preserving maps. Substructure
   slots that are STRUCTURES (`SCAL`) keep the equality convention (modules over one ring). The isometric
   default for a norm or a distance stays: it is what "preserve every slot" means, it is restrictive as
   the note expects a default to be, and the working categories are declared beside it.
2. **The alternatives.** A new declaration form,

       (declare-category! 'CAT 'X '(a b f) BODY)

   installs the predicate `IS-CAT-MAP(a, b, f)` := `IS-X(a) and IS-X(b) and f in FUN(C a, C b) and BODY`,
   the hom-set `HOM-CAT(a, b)`, the membership theorem, and the OBLIGATIONS `hom-CAT-id`,
   `hom-CAT-compose`, `hom-CAT-in-set` as statements to be proven in a theorem-library file (as the
   TOP-SPACE override's were); the Hom functors' typing theorems then follow from the generic driver.
   Several categories may share the objects: for `METRIC-SPACE`, `ISOMETRIC` (the default),
   `LIPSCHITZ`, `UNIFORMLY-CONTINUOUS`, `CONTINUOUS`; for `NORMED-VECTOR-SPACE`, `BOUNDED-LINEAR`. The
   inclusions between them (`HOM-ISOMETRIC(a, b) subset HOM-LIPSCHITZ(a, b) subset ...`) are theorems, one
   line each, and are the identity-on-objects functors between the categories.
3. **Naming.** `declare-hom!` remains the way to REPLACE a wrong default (it is what `TOP-SPACE` did);
   `declare-category!` ADDS a category and never touches the default. A view (`def-functor`) that is
   functorial for the default should say for which categories it is functorial; today's
   `functoriality.scm` speaks of the default only.
4. **The obligations are the point.** The proof that Lipschitz maps compose (the constants multiply) or
   that continuous maps compose is where the mathematics is; the generator must not stamp it. The
   generic driver proves the laws only for the GENERATED predicate, where they are bookkeeping.

## Decisions asked of the user

* D1. Repair the two wrong defaults (`MEASURABLE-SPACE`, `MEASURE-SPACE`) at the generator as in 1, or by
  `declare-hom!` beside each declaration? Recommended: the generator, so the next family-of-subsets slot
  cannot repeat the mistake; `TOP-SPACE`'s override then becomes an instance and can go.
* D2. `declare-category!` as in 2, with `LIPSCHITZ`, `UNIFORMLY-CONTINUOUS`, `CONTINUOUS` on
  `METRIC-SPACE` and `BOUNDED-LINEAR` on `NORMED-VECTOR-SPACE` as the first four, each with its
  composition theorem proven. Recommended: yes, one batch; the tree has `is-continuous-at` pointwise and
  the Lipschitz predicate on functions of a real variable, so the global predicates are to be defined.
* D3. The isometric default for metric and normed structures: keep (recommended, as the restrictive
  default the note describes), or make `CONTINUOUS` the default of `METRIC-SPACE` as structures.scm's
  own comment once anticipated.

## notes-44 (2026-09-28): carriers, their names, and several of them

**Which slots are carriers.** A slot is a carrier because the declaration's `(carriers ...)` clause names
it, whatever it is called: `CARR` for the algebraic species (semigroup to field, ringoid, the normed
groups and fields), `PTS` for the spaces (metric, pseudometric, C-metric, topological, metrizable,
measurable, measure), `VEC` for module, normed vector space and complex inner-product space, whose
scalars are the SUBSTRUCTURE slot `SCAL`. The generator reads the KIND of a slot, never its name, so
`PTS` is a carrier exactly as `CARR` is. `FIELD` declares a second, DERIVED carrier `NON-ZERO` (the domain
of `INV`); the hom generator counts INDEPENDENT carriers only, so a field morphism is one map, and that it
maps `NON-ZERO(a)` into `NON-ZERO(b)` is the theorem `hom-field-non-zero`.

**More than one carrier.** The generated predicate already handles k independent carriers with k maps,
`IS-HOM-X(a, b, f1, ..., fk)` (a Malcev-style two-sorted structure "just works", structures.scm:1400).
`SETOID` (`PTS`, `REL`) is the one such structure in the tree. What was NOT built for it is the hom-SET,
because an arrow is a k-tuple of maps: `HOM-SETOID(a, b)` is the SEP of `CARTESIAN(FUN(PTS a, PTS b),
FUN(REL a, REL b))` by `IS-HOM-SETOID` on the components, and the identity, composition and functors are
componentwise. `CARTESIAN` is binary in the tree, so k = 2 is available now and k >= 3 waits for the open
foundational item (no SEP over triples). `declare-category!` takes `(a b f1 ... fk)` for the same reason.
Proposal 1 (the family-of-subsets and transport clauses) is per slot and per carrier, so it applies
unchanged with several carriers.

**A systematic notation for the components.** Today the names are per role, from a closed vocabulary:
`CARR`, `PTS`, `VEC` for carriers, `SCAL` for the scalar substructure, and the operation and constant
names as mathematics writes them (`ADD`, `MUL`, `DIST`, `NRM`, `ZERO`, `ONE`); every accessor is one
global name for one slot (the 2026-09 rule, after `X`, `D`, `ID` collided with binders). Two ways to make
this systematic: (a) a POSITIONAL notation, `CARRIER(s, 1)`, `OP(s, 2)`, uniform across species -- it
would undo the one-name-one-slot rule, read badly in statements ("`(OP(s, 1))(x, y)`" for a sum) and cost
a rename of `PTS` / `CARR` across the tree for no logical gain; (b) keep the role names and make the ROLES
the systematic part: the declaration's slot kinds (`carrier`, independent or derived; `op`; `constant`;
`substructure`; and, after proposal 1, `family` for a set of subsets of a carrier and the measure-like
`function on a family`), a fixed vocabulary for carrier names by role documented in structures.scm, and
the generated `reference/STRUCTURES.md` listing every structure's slots WITH their kinds and the arrow
notion each kind generates. Recommended: (b). The hom generator then has one rule per KIND, which is what
notes-43 asked for, and a reader can see for each structure what its default category is.

## Built (batch 39, 2026-09-28)

Decisions D1 and D2 were taken as recommended (the user approved proposals 1 and 2, with "a family of
subsets of a carrier" and "a function on such a family" as two new slot kinds); D3 was not touched (the
isometric default of `METRIC-SPACE` stays).

**The generator (`structures.scm`).** Two slot kinds:

* `(family F C)` -- `F(s)` is a set of subsets of the carrier `C(s)`. Its conjunct of `IS-X` is
  `F(s) in POWER(POWER(C s))`, exactly what the former `(constant F (POWER (POWER C)))` spelling gave.
  Its hom clause is `forall u in F(t). PREIMAGE(s, f, u) in F(s)` (over a carrier other than `PTS`, the
  separation that `PREIMAGE` abbreviates).
* `(family-fun M F R)` -- `M(s)` is a function on the family `F(s)` into `R`. Its conjunct of `IS-X` is
  `M(s) in FUN(F(s), R)`, what `(op M F R)` gave. Its hom clause is
  `forall u in F(t). M(t)(u) = M(s)(PREIMAGE(s, f, u))`.

When a family slot is present the hom variables are `s`, `t` (the body of `PREIMAGE` binds `a`).
`MEASURABLE-SPACE` and `MEASURE-SPACE` declare `SIGMA` as a family and `MEAS` as a family-fun;
`TOP-SPACE` declares `OPENS` as a family. The four structure predicates are alpha-equal before and after
(checked on the band). The generated arrows now read:

    is-hom-measurable-space(s, t, f) iff is-measurable-space(s) and is-measurable-space(t)
      and f in fun(pts(s), pts(t)) and forall([u in sigma(t)], preimage(s, f, u) in sigma(s))
    is-hom-measure-space(s, t, f) iff ... and forall([u in sigma(t)], preimage(s, f, u) in sigma(s))
      and forall([u in sigma(t)], (meas(t))(u) = (meas(s))(preimage(s, f, u)))
    is-hom-top-space(s, t, f) iff is-top-space(s) and is-top-space(t)
      and f in fun(pts(s), pts(t)) and forall([u in opens(t)], preimage(s, f, u) in opens(s))

The third is, symbol for symbol, the `declare-hom!` that stood in `top-space.scm`; that override was
deleted. The override of `METRIZABLE-TOP-SPACE` is kept: as a refinement its generated hom is
`IS-METRIZABLE-TOP-SPACE(s) and IS-METRIZABLE-TOP-SPACE(t) and IS-HOM-TOP-SPACE(s, t, f)`, the same arrows
under a different formula, and `hom-laws.scm` reads the override's last conjunct.

For a structure with TWO independent carriers `install-hom-set!` now installs the hom-set as a set of
pairs: `HOM-SETOID(a, b) = {p in CARTESIAN(FUN(PTS a, PTS b), FUN(REL a, REL b)) :
IS-HOM-SETOID(a, b, NTH(1, p), NTH(2, p))}`. Three or more carriers still get nothing.

**`declare-category!`** `(declare-category! 'CAT 'X '(a b f1 .. fk) BODY)`, k = 1 or 2, installs
`definitional` the arrow predicate `IS-CAT-ARROW` (definition `is-CAT-arrow-def`: `IS-X(a) and IS-X(b)
and fi in FUN(Ci a, Ci b) and BODY`) and the hom-set `HOM-CAT(a, b)`, and registers the category in
`*categories*` with three obligations, `hom-CAT-id`, `hom-CAT-compose` and `hom-CAT-in-set`, recorded as
statements. `category-obligations-audit` lists the obligations that are not a theorem of that name, of
that statement (up to alpha), with provenance `proven` or `certified`; `(category-obligation NAME)` returns
one as a goal; `category-member-iff` returns the membership statement, which is not an obligation.
`report-category-obligations!` is the load gate (warn-only; `#t` makes it fatal). The default category
of `X` (`IS-HOM-X`, `HOM-X`) is not touched.

**The four categories (`theorem-library/categories.scm`).**

| category | on | the arrow condition |
|---|---|---|
| `LIPSCHITZ` | `METRIC-SPACE` | `forsome K in RR, 0 <= K and forall x, y in PTS(a). DIST(b)(f x, f y) <= K * DIST(a)(x, y)` |
| `UNIFORMLY-CONTINUOUS` | `METRIC-SPACE` | `IS-UNIFORMLY-CONTINUOUS(a, b, f)` (the tree's predicate) |
| `CONTINUOUS` | `METRIC-SPACE` | `IS-CONTINUOUS(a, b, f)` (the tree's predicate) |
| `BOUNDED-LINEAR` | `NORMED-VECTOR-SPACE` | `SCAL(a) = SCAL(b)`, additive, homogeneous (the clauses of the generated hom), and `forsome K in RR, 0 <= K and forall x in VEC(a). VNRM(b)(f x) <= K * VNRM(a)(x)` |

For each: `hom-CAT-member-iff`, `-id`, `-compose`, `-in-set`, and the Hom-functor typings `-post-type`,
`-pre-type`. The inclusions are theorems, arrow by arrow and as hom-sets:
`HOM-METRIC-SPACE(a, b) subset HOM-LIPSCHITZ(a, b) subset HOM-UNIFORMLY-CONTINUOUS(a, b) subset
HOM-CONTINUOUS(a, b)` (an isometry is 1-Lipschitz; a K-Lipschitz map is uniformly continuous with
delta = eps / (K + 1); `uniformly-continuous-is-continuous`), and `HOM-NORMED-VECTOR-SPACE(a, b) subset
HOM-BOUNDED-LINEAR(a, b)` (K = 1). The identity laws are read off these inclusions and the default's
identity law. Composition: the Lipschitz and the bounded-linear constants multiply; uniform continuity is
the nested choice of deltas; continuity is pointwise, by `ms-compose-continuous-at`.

**The laws of the family kinds and of two carriers (`theorem-library/hom-kinds.scm`).** The generic
driver of `hom-laws.scm` cannot close a pulled-back clause (it instantiates the f clause where the
composite's clause needs g's first), so `MEASURABLE-SPACE` and `MEASURE-SPACE` are proved by a driver
with one rule per kind (`PREIMAGE(s, ID, u) = u`; `PREIMAGE(s, g o f, u) = PREIMAGE(s, f,
PREIMAGE(t, g, u))`). The file also proves the four `SETOID` laws, componentwise, and
`measure-space-as-measurable-space-functorial`, which the sweep of `functoriality.scm` cannot: the view
occurs inside `PREIMAGE(V a, f, u)`, where its accessor rewriting does not reach.

**The audit.** At the end of batch 39 the four declared categories owe nothing
(`;; category obligations: none outstanding (4 declared categories)`).

## Built (batch 40, 2026-09-28)

The user's decision of 2026-09-28: the relation of a setoid is not a second carrier. It is a slot of a
new kind, and a setoid arrow is ONE map of points that sends related points to related points. (An
indicator-function design, `r : X x X -> {0, 1}`, was considered and withdrawn. The reflecting arrow,
`x ~ y iff f(x) ~ f(y)`, is not built; it is one `declare-category!` on `SETOID` away.)

**The generator (`structures.scm`).** A third slot kind beside the two family kinds:

* `(relation R C)` -- `R(s)` is a set of pairs of points of the carrier `C(s)`. Its conjunct of `IS-X`
  is `R(s) in POWER(CARTESIAN(C s, C s))`. Its hom clause, under the map `f` of `C`, is
  `forall x1_ in C(a). forall x2_ in C(a). [x1_, x2_] in R(a) implies [f(x1_), f(x2_)] in R(b)`.
  A relation over a slot that is not a carrier is an error at declaration time.

`SETOID` is re-declared `(carriers PTS) (relation REL PTS) (property is-equivalence REL PTS)`. Its
predicate changes, and this is the only structure predicate that changes:

    before: is-setoid(s) iff length(s) = 2 and pts(s) in set and rel(s) in set
              and is-equivalence(rel(s), pts(s))
    after:  is-setoid(s) iff length(s) = 2 and pts(s) in set
              and rel(s) in power(cartesian(pts(s), pts(s))) and is-equivalence(rel(s), pts(s))

The new typing repeats the first conjunct of `is-equivalence`. The duplication is harmless and
`is-equivalence` is left as it is. The generated arrows now read:

    is-hom-setoid(a, b, f) iff is-setoid(a) and is-setoid(b) and f in fun(pts(a), pts(b))
      and forall([x1_ in pts(a), x2_ in pts(a)], [x1_, x2_] in rel(a) implies [f(x1_), f(x2_)] in rel(b))

In words: "f is a setoid morphism from a to b". With one carrier, `SETOID` gets the one-carrier hom-set
`HOM-SETOID(a, b) = {f in FUN(PTS a, PTS b) : IS-HOM-SETOID(a, b, f)}`. The two-carrier branch of
`install-hom-set!` (the set of pairs of maps) is kept as generic code, although no structure in the tree
now has two carriers. A suite check pins it on a toy structure.

**The laws (`theorem-library/hom-kinds.scm`).** The batch 39 `SETOID` section proved the laws for pairs
of maps; it is replaced. `hom-setoid-member-iff`, `-id`, `-compose` and `-in-set` are now proved in the
one-carrier shapes, all `proven modulo 0`. The identity and composition are driven by one rule for the
relation kind:

* identity: `id-fun-apply` rewrites `ID-FUN(PTS a)(x)` to `x`;
* composition: f's clause, then f's typing, then g's clause, with `compose-apply` for `(g o f)(x)`.

`SETOID` is added to the list of `hom-functors.scm`, which gives `hom-setoid-post-type` and
`hom-setoid-pre-type` (both modulo 0). The driver needed no new case. `SETOID` stays out of
`hom-laws.scm`'s generic list, because that driver closes an equation and this clause is an implication.

**The cone.** Two constructions of setoids prove the new typing conjunct from the `is-equivalence`
they already establish:

* `ringoid-setoid-is-setoid` (ringoid-setoid-proof.scm): the typing conjunct is closed by
  `is-equivalence`'s first conjunct;
* `cauchy-setoid-is-setoid` (rake-setoid2.scm): the conjunct goes to the driver's existing leaf (a).

Every other citer of `IS-SETOID` re-proved unchanged.

**The structure cards.** `describe-structure` and the Markdown card now print the three kinds that
printed "?": "a family of subsets of C", "a function on the family F into R" and "a relation on C".
`reference/STRUCTURE-INDEX.md` (`struct-index--emit-structure`, interactive.scm) lists every slot with
its kind, and gives one line per structure with the default arrows, as the generated (or
`declare-hom!`-replaced) definition.

**The definedness certificate.** `pi--defined?` (primitive-inferences.scm) certifies an applied structure
operation `((ACC s) a1 .. an)` for a `family-fun` slot as well as for an `op` slot. With
`IS-MEASURE-SPACE(s)` and `u in SIGMA(s)` in context, `MEAS(s)(u)` is certified. This is a kernel file,
so every certificate is invalid until the next exam.

**`dk-name!`** (driver-kit.scm). `(dk-name! T [CLASS])` names a term typed in context as a fresh symbol
`v`, landing `v in CLASS` and `v = T`. It is the cure for `ineq` dropping a non-linear premise. It
replaces the verbatim copies `cpsl-name!` (cc-power-series-laws.scm) and `clh-name!`
(cc-log-holomorphic.scm).
