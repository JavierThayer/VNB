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
