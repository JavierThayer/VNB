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
