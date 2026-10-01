# Decisions pending, written 2026-10-01 for the morning

Three items, each with the exact text, what hangs on it, the cost, and the recommendation.
Background: docs/image-axiom-inconsistency-2026-09-30.md (the finding, its addendum, the
probes in docs/probes/).

## 1. The DOM axiom

Current (library.scm, `dom-membership`, base theory):

    forall([f, x], x in dom(f) iff (x in set and f(x) = f(x)))

Proposed, exactly:

    forall([f, x], x in dom(f) iff (x in set and f(x) in set))

What hangs on it: `range-membership` (theorem-library/rake-compose-typing.scm),
`a in dom(f) implies f(a) in ran(f)`, and its six companions `fun-range-membership`,
`ran-subset-codomain`, `compose-type-2` .. `compose-type-5`.  With the repaired image
axiom, `f(a) in ran(f)` needs `f(a) in set`, and the kernel has no rule from "f(a) is
defined" to "f(a) is a set"; the current axiom gives only the former.  Until decided the
file is the one hole in the tree.

Why the change is right: on a class of pairs the two readings agree (f(x) is defined
exactly when a unique set y has <x, y> in f, and that y is a set); under design (i),
functoids outside the range of quantification, there is no other kind of f.  The new form
says directly what `dom` means: the points where the value is a set.  `dom-fun-membership`
(`f in fun(A) implies (x in dom(f) iff x in A)`) is unchanged and consistent with it.

Cost: one line; one citing file (rake-compose-typing.scm), whose proofs then go through;
a full exam, which the integration runs anyway.

Alternative if declined: retire the seven RAN theorems as unprovable under the corrected
image, and the three places that cite them.

Recommendation: yes.

## 2. The tuple axiom, as a tripwire

Proposed, exactly, `primitive`, beside `nth-in-range` in library.scm:

    tuple-members-are-sets:
    forall([L, c, k in nn], L in c implies ((1 <= k and k <= length(L)) implies nth(k, L) in set))

What it says: a tuple that is a member of anything has set components -- the sentence every
reduction of ordered pairs supplies and the primitive constructor LIST does not.  For a
non-tuple L, `length(L)` denotes junk, `k <= length(L)` is false under strict atoms, and the
axiom is vacuous.

What hangs on it: nothing today.  The two derivations that produced `[0, SET] in C` (a
functoid instantiated in `app-graph`; beta on a class-valued body) are closed by the
kernel changes of 2026-10-01, and the only axiom that reads a component off a tuple
without a TUPLES hypothesis, `make-set`'s membership, already carries `x in set`.  So the
pair with a proper class in it is currently neither provable nor usable.

Why add it anyway: as a tripwire.  Should a future door again manufacture such a pair, the
axiom turns it into FALSITY in two steps (`nth-r` reduces `nth(2, [0, SET])` to SET, then
`SET in set` against Burali-Forti), where tonight it sat inert and had to be noticed.

Cost: one line; no citer; every bill unchanged (primitive contributes {}).

Recommendation: yes, not urgent.

## 3. fun-image-set, when convenient

Prove, from union and separation and the FUN axioms, with no citation of `image-set`:

    fun-image-set:
    forall([A, B, f, S], f in fun(A, B) implies (S in set implies image(f, S) in set))

(or with `f in fun(A)`; the image of a set under a set function is a subclass of the union
of the second components of f's pairs, a set).  Then route the seventeen theorem-library
citations of `image-set` -- all at set functions: lambdas over sets, enumerations, paths --
through it, so that `image-set` (replacement, primitive) appears only on the bills of the
ordinal and cardinal layer, where it is genuinely used (`ord-no-injection-into-set`, the
definition of CARD, `def-by-ord-recursion`).

What hangs on it: nothing; a ledger property.  "What does the analysis rest on" then has
a visible answer, and it does not include replacement.

The user's instruction (2026-10-01): do it when convenient and if it will not affect
anything else.  Cost: one proof file plus seventeen one-token citation changes; a
certified build re-proves the seventeen citers.

Recommendation: after the two above are settled and the tree is whole again.
