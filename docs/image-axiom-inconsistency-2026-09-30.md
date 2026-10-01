# FALSITY from the image axioms (found 2026-09-30, notes-52)

## The finding

The base theory as loaded on 2026-09-30 (tree 9b859b4) proves FALSITY, modulo 0. Two
probes on worker-03 against the certified band of that tree:

1. `docs/probes/set-in-set-probe.scm`: `SET in SET`, then FALSITY, each `qed` reporting
   `proven modulo 0 [oracles: arith]`.
2. `docs/probes/image-functoid-probe.scm`: `SET in SET` again with a named functoid and no
   `vnb-lambda`, so no beta step: `(def-functoid 'PROBE-CONST-SET '(x_) 'SET)`.

The derivation, in the second form:

    image-membership-iff at phi := PROBE-CONST-SET, S := NN, w := SET
        SET in IMAGE(PROBE-CONST-SET, NN)  iff  forsome x in NN. PROBE-CONST-SET(x) = SET
    the right-hand side, witness 0:  0 in NN by arith;  PROBE-CONST-SET(0) = SET by
        (mac 'PROBE-CONST-SET) then rfl (SET is an atomic constant, certified defined)
    hence SET in IMAGE(PROBE-CONST-SET, NN)            (prop, from the iff)
    membership-implies-sethood:  SET in SET
    subset-def + membership-implies-sethood:  ORD subset SET
    subclass-of-set-is-set:  ORD in SET
    burali-forti:  not (ORD in SET).  FALSITY.

The first form replaces the functoid by `(VNB-LAMBDA x_ NN SET)`, whose application at
0 `lam-b` reduces to SET.

## What is wrong

`image-membership-iff` (structure-library/injection.scm):

    forall phi, S, w.  w in IMAGE(phi, S)  iff  forsome x. x in S and phi(x) = w

`phi` is unguarded: `forall-elim` instantiates it at anything in function position -- a
`vnb-lambda` (a class of pairs), a function variable, a named functoid, a `lambdoid`
(the definedness certificate never certifies a bare lambdoid record, so that last one
cannot be completed, but a NAMED functoid is a symbol and is certified at once).  A
functoid may take a proper class as its value; a class of pairs cannot (a proper class
is a member of nothing: `membership-implies-sethood`).  For a class-valued `phi` the
right-hand side is true at `w := phi(x)` while the left-hand side asserts a
membership, and `membership-implies-sethood` turns that into `phi(x) in SET`.

The same species as `finsum-congruence` and the old `eplus` axioms (CLAUDE.md,
"Statements: the species of FALSE support"): a strict `=` beside a membership, with the
term untyped.

`image-set` (replacement) is not at fault: with the membership corrected, IMAGE(phi, S)
is the image of the set-valued part of phi's graph, a set when S is.

## The second door

Under the theory's own reading of `vnb-lambda` as a class of pairs (`app-graph`, adopted
2026-07-28; the manual: "vnb-lambda ... is a set"), `(VNB-LAMBDA x_ NN SET)` is the EMPTY
class -- no set equals SET -- and its application at 0 is undefined.  `lam-b` reduced it
to SET and `rfl` closed `SET = SET`.  The beta licence (`pi--beta-licensed?`,
primitive-inferences.scm:2044) checks that the ARGUMENT is in the domain and nothing
about the VALUE.  No contradiction has been derived from this door alone (the pair
`<0, SET>` would have to become a member of something), but the reduction proves a false
equation and should not be licensed unless the value is certified a set (typed in some
class, or the lambda typed in FUN(A, B) by lam-t).

## Repair options (the user's decision; the base theory is his)

A. `image-membership-iff` gets the sethood conjunct:

       w in IMAGE(phi, S)  iff  w in SET and forsome x in S. phi(x) = w

   90 citations in 38 files (theorem-library and structure-library).  The direction
   "w in IMAGE => exists x" is unchanged for a citer that splits the conjunction; the
   direction "exists x => w in IMAGE" now needs `w in SET`, which the citer almost
   always has (w is typed) or gets from `membership-implies-sethood` when w came out of
   a set.  A certified build after the change re-proves every citer (their cited
   statement hash changes), so the exam is the measure of the cost: one night.

B. Guard `phi` instead: state both IMAGE axioms for `phi in FUN(S, B)` only.  Kills the
   class-function uses (`ord-no-injection`, Zorn) that the primitive shelf was widened
   for.  Not recommended.

C. The beta licence (second door): require the instantiated body to be certified a
   SET, or the lambda typed.  A kernel change with its checker (rule-checkers-schema.scm
   `rcs-lambda-beta`) and two suite controls; the cost is every `lam-b` whose body
   value has no typing in context -- unknown until an exam runs with the stricter
   licence, which VNB_NO_RULE_CHECK-style A/B can measure.

Recommendation: A now (one axiom, one night), C as the next kernel item.

## The quantifier question (notes-52), answered by the probe

An unguarded `forall phi` ranges over everything the instantiation rule accepts in
function position, and that includes named functoids whose values are proper classes.
Functoids are not classes; `def-functor` views are functoids (`def-functoid` of a LIST
of the source's slots, structures.scm:1247).  There is no inconsistency in QUANTIFYING
over them; the inconsistency was in an axiom that let one of them manufacture a member.

## Addendum, 2026-10-01: the third door, and the design question underneath

`docs/probes/app-graph-probe.scm`, against the repaired tree: with `PROBE-C2(x_) := SET`,
`app-graph` instantiated at the functoid gives `PROBE-C2(0) == iota(val_, [0, val_] in PROBE-C2)`;
beta gives `PROBE-C2(0) = SET`; so the IOTA equals SET, `iota-e` grants its defining property, and

    [0, SET] in PROBE-C2        proven modulo 0
    [0, SET] in SET             proven modulo 0

A pair with a proper class in it is a member of a functoid, and is a set.  No FALSITY was
derived from it tonight (the tree has no axiom reading a component off a set pair), but it
is a false statement proven, of the same species as the two repaired: an axiom with an
unguarded variable in function position (`fn_` in `app-graph`, `f` in `dom-membership`,
`phi` in `image-membership-iff`) read as a class of pairs, instantiated at a functoid.

The user's argument (2026-10-01): if an unguarded `forall([x], P(x))` ranges over all classes
and functoids fall within its scope, functoids are classes; if they are not classes, they
must be outside the scope.  As the kernel stands they are inside (forall-elim accepts a
named functoid) and not classes (no axiom gives `x in PHI` a truth value), and every axiom
with an unguarded variable is therefore also an axiom about functoids.  Two coherent
designs:

  (i) Functoids OUTSIDE the range of quantification -- the manual's original sentence.
      Enforced at one point: `forall-elim` refuses an instance term that is a bare
      functoid (a registered functoid name, or a lambdoid record, which the definedness
      certificate already refuses).  A functoid applied (`POWER(X)`) is a class term and
      is unaffected.  app-graph and the rest are then sound as written; the two repairs
      stay as improvements.  Cost: any library proof that instantiates an axiom variable
      at a bare functoid name breaks (a keep-going load counts them).
 (ii) Functoids INSIDE the range: a two-sorted universe under one variable sort, which
      needs a primitive sort predicate (`IS-CLASS`) as a guard on app-graph and on every
      axiom that reads a class of pairs off a variable in function position, plus an audit
      gate for the pattern.  Costlier, and it makes a functoid an object with neither
      members nor membership.

Recommendation: (i).
