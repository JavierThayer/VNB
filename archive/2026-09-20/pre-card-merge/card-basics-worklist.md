# Putting the CARD layer on a firm basis

State on 2026-08-12.  `CARD` is AXIOMATISED; `CARD-STAR` is DEFINED
(`theorem-library/card-defined.scm`) as

    CARD-STAR(A)  ==  IOTA alpha.  alpha in ORD
                    and  forsome phi. phi in BIJECTION(A, ORD-SEGMENT alpha)
                    and  forall beta with ORD-LT(beta, alpha).
                           not forsome psi. psi in BIJECTION(A, ORD-SEGMENT beta)

and the migration is: prove the fact about `CARD-STAR`, delete the `CARD` axiom,
rename -- one name at a time.

## What exists

Proven: `cd-body-unique`, `cd-seg-body`, `card-star-segment` (= `CARD-STAR(S(n)) = n`),
`pigeonhole-segments`, `pigeonhole-segments-gen`, `ord-segment-zero-no-members`,
`ord-well-ordered`.

Asserted: the eight `primitive` CARD axioms (`card-in-ord`, `card-empty`,
`card-insert`, `card-segment`, `card-finite-bij`, `card-union-disjoint`,
`finite-set-induction`, and `card-image-injection` in `injection.scm`), plus five
`asserted` ones (`card-singleton`, `card-subset-nn`, `card-power-nn`,
`interval-card`, `interval-card-in-nn` -- the last at 60 bills, the #2 keystone).

Because the eight are `primitive` they contribute `{}` to every bill: **no bill
anywhere records that cardinality is being assumed.**

## The mechanism to build first, before any individual fact

`card-star-segment`'s proof is an `iota-d` over the description, and its script is
already generic in the class: replacing `(ORD-SEGMENT n_)` by a variable gives

    card-star-from-body :  cd-body(A, al)  =>  CARD-STAR(A) = al

i.e. "anything satisfying the description IS the cardinal".  Under it, one
transport lemma does the rest of the finite layer:

    card-star-transport :  phi in BIJECTION(A, B)  =>  ( cd-body(B, al) => cd-body(A, al) )

**and it needs no inverse**, which is what keeps the track choice-free.  Both
clauses of the body compose with `phi` on the RIGHT: the existence clause turns
`psi : B -> S(al)` into `psi . phi : A -> S(al)`, and the leastness clause turns a
hypothetical `A -> S(beta)` back into a `B -> S(beta)` the same way.  (An inverse
would be needed only for the converse implication, which nothing wants.)

The two compose into the workhorse:

    card-star-bij :  n in NN,  phi in BIJECTION(A, ORD-SEGMENT n)  =>  CARD-STAR(A) = n

"to compute a cardinal, exhibit a bijection to a segment."  Every finite fact
below is then an instance -- exhibit the bijection, cite `card-star-bij`.

## Ordered worklist

1. **`bijection-identity` and `bijection-compose`** -- both `informal`, both
   flagged in `bijection.scm` as "derivable, mechanization deferred".
   `bijection-identity` is already the worst leaf of `cd-seg-body`, so the whole
   CARD arc reads `[trust: informal]` until it is proven; `bijection-compose` is
   what `card-star-transport` will cite.  Home: `structure-library/bijection-derived.scm`,
   which already proves the three projections `modulo 0`.
2. **`card-star-from-body`** -- generalize `card-star-segment`'s `iota-d` script off the
   segment.  `card-star-segment` then becomes its corollary.
3. **`card-star-transport`**, then **`card-star-bij`**.
4. **`card-star-empty`** -- `EMPTY-SET = ORD-SEGMENT(0)` by `class-extensionality`
   (`ord-segment-zero-no-members` is proven), then `card-star-segment` at `n := 0`.
   This one needs neither (1) nor (3).
5. **`card-star-singleton`** -- the bijection `{x} -> ORD-SEGMENT(1)` sending `x` to `0`.
6. **`interval-card` / `interval-card-in-nn`** -- the bijection
   `INTERVAL(1,n) -> ORD-SEGMENT(n)`, `j |-> PRED(j)`.  `PRED` and the segment
   bridges exist (`theorem-library/finite-surgery.scm`,
   `theorem-library/ord-segment-arith.scm`).  This is the 60-bill keystone.

## Blocked, and on what

* **`card-star-insert`** -- needs `EXTEND-BY` (the finite-surgery kit's second member,
  unbuilt): a bijection `A -> S(n)` extends to `A + {x} -> S(succ n)`.
* **`card-star-union-disjoint`** -- needs `EXTEND-BY` and a concatenation map.
* **`card-subset-nn`**, **`card-power-nn`** -- a subset of a finite set is finite;
  the power set of a finite set is finite.  Both want `finite-set-induction`,
  which is itself one of the axioms to retire.
* **`card-image-injection`** -- an injection `A -> B` restricted to its image is a
  bijection; then `card-star-bij`.  Needs the image machinery, not `EXTEND-BY`.
* **`card-in-ord`** and **`card-finite-bij`** -- **Track B (Zermelo)**.  These two
  are the only ones that need well-ordering of an arbitrary set.  Without them
  `CARD-STAR` is simply PARTIAL -- defined on well-orderable sets, undefined
  elsewhere -- and the finite layer above does not care.

## Track B status

`theorem-library/zen-step.scm` (load.scm:683) holds rungs 1 and 2, all `modulo 0`:

* `ord-lt-succ-iff-le`
* `zen-step` -- the uniform recursion equation for the enumeration `ZEN`
* `zen-hits` -- at any ordinal with an inhabited avoid-set, `ZEN` lands in it
* `zen-exhausts` -- for a SET, some ordinal has an empty avoid-set

What remains is the assembly: turn `zen-exhausts`'s ordinal `alpha*` into an
actual bijection `ORD-SEGMENT(alpha*) -> X` as a SET function (through
`image-set`, i.e. replacement) and prove `BIJECTION` membership.  Zorn needed
only a contradiction; Zermelo needs the object.  Estimated comparable to
`zorn-route-two` (6 qeds, ~650 lines) and then some.
