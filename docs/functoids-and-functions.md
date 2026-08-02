# Functoids and functions

*Working note, 2026-07-28.*

**Status: ADOPTED.** The recommendation in section 8 was endorsed and the axiom is
installed. `app-graph` is in `theory.scm`, at the head of the function-space block,
inside the `primitive` wrapper -- so the base theory went from 92 axioms to 93. It is
**named-only** (`declare-named-only!`, `macetes.scm`), for the reason given in section
4. Adopting it moved nothing else: 219 proven theorems, every bill unchanged, every
load-time gate still passing. The term language was NOT rewritten, per section 8.

Two claims in the original draft turned out to be **wrong** and are corrected in
section 4a: `fun-domain-extensionality` is NOT derivable from `app-graph` -- it is
independent of it, and is itself the "no junk" half of the story -- and the `RES`
axioms are not reachable by an axiom quantified over a variable. Both stay as
axioms. What does remain open is only the naming: `def-functoid` still borrows the
word (section 6).

## 1. The question

VNB's manual introduces a third kind of object. `docs/ch-expressions.tex:283`:

> Proper VNB has two kinds of object: *sets* (elements of the class `SET`) and
> *proper classes* (collections that can have members but are not themselves
> members of anything). We retain that distinction and add a third kind,
> *functoids*.

and, in the remark that follows (`:304`):

> In a reductionist treatment one could introduce a distinguished class
> `FUNCTOID` subset `CLASS`, whose members are ordered pairs encoding signature
> and rule. This system instead treats functoids as a new kind of object,
> coordinate with sets and classes rather than reducible to them. The principal
> consequence is that the formal language does not quantify over functoids:
> "all functoids `F` satisfy..." is metalanguage, not an object-language formula.

The proposal under consideration rejects that, and rejects it differently from
the reduction the remark dismisses. It is not "a functoid is a pair encoding a
signature and a rule". It is:

> A functoid is a **class**. A function is a functoid which is a **set**. If `x`
> is any class, `(x a)` is syntactically correct but may be undefined.

This note sets out what is already true of VNB under that reading, what would
have to be added, where the reading cannot be sustained, and what the change
would cost.

## 2. Four things are called "functoid" in the tree

The word is overloaded, and the overloading is most of the confusion.

1. **`def-functoid`** (`structures.scm:856`). Installs an elementary macete
   rewriting `(name p1 ... pn)` to a body, stamps it `definitional`, registers
   the head in `*constant-registry*` (`expressions.scm`) and in the operator
   table (`operators.scm`). It is a definitional abbreviation schema. The head
   symbol has no standalone meaning: `EUCLIDEAN-GAUGES` alone is not a term, and
   there is nothing to quantify over. This is the usage that appears most often
   in the source.

2. **The manual's functoid** (`ch-expressions.tex:286`): an operation given by a
   signature declaration `A_1, ..., A_n -> B`, where the arrow is metanotation
   and no Cartesian product is implied. A third kind of object, not quantified
   over.

3. **The parser's "functoid records"** (`ch-expressions.tex:651`, `:682-702`):
   Scheme tagged structures produced by `lambda` / `lambdoid`, applied through
   the `apply-functoid` head. An implementation representation.

4. **A genuine class map.** `ch-math.tex:349-361` states transfinite recursion
   for "a functoid `E` from the class of ... " and then has to add, inside a
   mathematical proposition, that "both `E` and `f` ... are functoids, not
   functions" -- i.e. it drops into metalanguage in the middle of a statement it
   would prefer to make formally.

Usage 4 is the one the proposal is about. Usages 1 and 3 are implementation
devices. Usage 2 is the doctrine.

## 3. What the kernel already does

The syntax the proposal asks for is already in place. This is worth stating
precisely, because it means the proposal is not a change to the term language.

- **Application is total juxtaposition.** `validate-wff!` (`wff.scm`, the `else`
  branch of the term walk, around `:451`) accepts any compound whose head is not
  a recognised operator as a function application, and walks a compound head as
  a term in its own right, so `((MUL s) a b)` is well formed. Consequently
  `(x a)` is already syntactically correct for any class-denoting term `x`.
  There is no `apply-function` operator in the kernel; the name occurs only in
  two help strings in `interactive.scm`.

- **Definedness is already `(= t t)`.** Equality is partial, so `t = t` asserts
  that `t` is defined. `fun-domain-apply-def` (`theory.scm:352`) says, for
  `f` in `FUN(A)`, that `(f x) = (f x)` if and only if `x` is in `A`.

- **`DOM` is already stated for an arbitrary class.** `dom-membership`
  (`theory.scm:391`) reads: `x` is in `DOM(f)` if and only if `x` is a set and
  `(f x)` is defined -- quantified over all `f`, with no hypothesis that `f` is
  a function. This is the proposal's reading, already in the axiom table.

- **"Functions are sets" is already an axiom**, not a definition:
  `fun-elements-are-sets` (`theory.scm:336`) and
  `fun-domain-elements-are-sets` (`:342`).

- **Class functions are already used.** `theorem-library/ord-no-injection.scm`
  proves `ord-no-injection-into-set` about a `phi` that is an object-language
  *variable*, quantified with `FORALL`, applied as `(phi b)`, and never required
  to be a set. Its `H` is a `VNB-LAMBDA` over the proper class `ORD`.

What is **not** in place is any connection between `(f x)` and the membership of
`f`. No axiom constrains what a function contains. A function is, as far as the
theory says, a set about whose members nothing whatever is known.

## 4. The axiom

The connection to add is one axiom, and it should not be guarded:

```
app-graph:   forall f. forall x.   (f x)  ==  IOTA y. (LIST x y) in f
```

`==` rather than `=`: both sides may be undefined and `=` is strict
(`ch-expressions.tex:270`). The axiom *defines* application as the definite
description over the graph, rather than constraining a primitive.

Under it, the proposal is the literal content of the theory:

- every class is a functoid;
- `(NN 3)` is a well-formed term which is simply undefined, since no member of
  `NN` is a pair with first coordinate `3`;
- a function is a functoid which is a set;
- ~~`fun-domain-extensionality` becomes a consequence of
  `class-extensionality`~~ and ~~`res-typing` / `res-apply` become theorems~~ --
  **both of these claims were WRONG, and section 4a below replaces them.**

## 4a. What `app-graph` does NOT give you  [corrected 2026-07-28]

An earlier draft of this note claimed that adopting `app-graph` makes
`fun-domain-extensionality` derivable and turns the `RES` axioms into theorems.
Both claims are false, and the reason is structural rather than a matter of
finding the right proof.

### `fun-domain-extensionality` is independent, and is itself the missing half

`app-graph` constrains APPLICATION in terms of membership. It says nothing about
members of `f` that are not pairs.

Let `g` be a functional graph with domain `A`, let `c` be any set that is not an
ordered pair, and put `f = g union {c}`. The pairs of `f` are exactly the pairs
of `g`, so for every `x` the fibre `{y : (x,y) in f}` equals `{y : (x,y) in g}`,
and therefore `(f x) == (g x)` everywhere -- `f` and `g` are indistinguishable by
application. But `c` is a member of one and not the other, so by
`class-extensionality` they are distinct. If both lie in `FUN(A)`, they agree on
all of `A` and are unequal: `fun-domain-extensionality` fails.

Nothing in the remaining axioms forbids that interpretation. Every other
function axiom is phrased through application or definedness --
`fun-domain-apply-def`, `fun-codomain-iff`, `is-fun-def`, `dom-membership`,
`dom-fun-membership`, `dom-of-fun` -- so all of them survive unchanged in a model
built this way. Hence there is a model of everything else in which
`fun-domain-extensionality` is false, and it is therefore not a consequence of
`app-graph`. It must remain an axiom, and it earns its keep: given
`class-extensionality`, what it actually asserts is that **`FUN(A)` holds at most
one object per graph.**

So the design has two halves with genuinely different status:

- **`app-graph` -- unguarded.** It defines application, and can safely speak
  about every class, because a class with no pairs simply has undefined
  application everywhere.
- **the "no junk" half -- necessarily GUARDED.** Unguarded it would read "every
  class is a set of ordered pairs", which is false of `NN`, of `ORD`, of every
  ordinary set. It can only ever be asserted of things already known to be
  functions -- which is exactly the `f, g in FUN(A)` hypothesis
  `fun-domain-extensionality` already carries.

The `FUN(A)` guard is thus not an accident of an old design; it is forced. If the
stronger form is ever wanted explicitly, it is

```
fun-no-junk:  IS-FUN(f) => forall z. (z in f <=> exists x, y. z = LIST(x,y) and (f x) = y)
```

which would make `f` literally its graph and `fun-domain-extensionality` a
theorem. Adding it is a second foundational decision, not a consequence of the
first.

### The `RES` axioms are about a term-former `app-graph` cannot reach

`RES` is a primitive term-former, a constant head. `app-graph` quantifies over a
VARIABLE `f`, and an axiom is instantiated only at terms, so it can no more
constrain `RES` than it can constrain `POWER` (section 5). `res-typing` and
`res-apply` are therefore untouched by it.

They would become theorems only if `RES(f,B)` were REDEFINED as the separation
`{ z in f : NTH(1,z) in B }` -- and that is a redefinition of a kernel
term-former, not a derivation. It would also need `fun-no-junk` above to conclude
anything about application from the resulting set. Worth doing one day, together
with the rest of a graph-native function layer; not a consequence of adopting
`app-graph`.

### What this costs

Nothing that was gained. `app-graph` still does what section 4 says it does; the
error was in the follow-on bookkeeping, not in the axiom. The two axioms simply
stay where they are.

### Why no guard is needed

An earlier formulation guarded the axiom on `IS-FUN(f)`. That is wrong, and
instructively so: `is-fun-def` (`theory.scm:386`) defines `IS-FUN(f)` as "`f` is
in `FUN(A)` for some **set** `A`", so the guarded form speaks only about
set-functions -- precisely the restriction the proposal exists to remove.

The unguarded form is safe because `f` is a **variable**, and an axiom can only
be instantiated at *terms*. The operators of the language -- `UNION`, `POWER`,
`FUN`, `CARTESIAN`, `SEP`, `CHOICE`, the structure accessors, and every
`def-functoid` head -- are constant heads in `*constant-registry*`. `CARR` alone
is not a term; only `(CARR s)` is. The axiom therefore cannot be instantiated at
them, and makes no claim about them. It bites exactly where the head is a
variable, which is exactly the class-function case.

### n-ary application

`app-graph` is unary; VNB's application is n-ary. The two are already reconciled
by the `apply-tupling-N` axioms (`theorem-library/axioms.scm`, described at
`structures.scm:620-634`):

```
(f a_1 ... a_n)  =  (f (LIST a_1 ... a_n))
```

So the graph of a binary operation is a class of pairs `((a,b),c)`, and the
unary axiom covers it through the existing convention. Nothing new is required
here; the convention already carries this weight for the curried structure
operations (`mul(s)(a,b)` parsing to `((MUL s) a b)`).

## 5. Where the reading cannot be sustained

There are **three** things, not two, and no axiom collapses them to two.

1. **Operators of the language.** `FUN` is "a primitive class constructor, total
   over all classes" (`theory.scm:320`); `UNION`, `INTERSECTION` and
   `COMPLEMENT-IN` are likewise "total over classes -- they are defined whether
   or not their arguments are sets" (`theory.scm`, the union/intersection
   block); `ch-expressions.tex:337` says the same of the whole constructor list.

   These cannot be classes of pairs. `POWER(ORD)` is a legitimate term, but the
   pair `(ORD, POWER(ORD))` is not a legitimate object, because
   `membership-implies-sethood` forbids a proper class from being a member of
   anything. This is not a design decision that could be revisited: it is the
   same fact that makes `POWER` not a set.

2. **Class functions.** Classes of pairs of sets, whose domain may be a proper
   class. `ORD -> grd` is one. These *are* classes, and `app-graph` is exactly
   right for them.

3. **Functions.** Class functions which happen to be sets.

So "a function is a functoid which is a set" holds, exactly, between levels 2
and 3. Level 1 is not an object in any set theory, NBG included.

## 6. Consequence for the vocabulary

The word "functoid" should be retired from level 1. What lives there is an
*operator*: a term-forming symbol of the language with an arity, which is what
`operators.scm` -- the one table, keyed by head symbol -- already calls it, and
what `register-operator!` already records for every `def-predicate` and
`def-functoid`. On that reading `def-functoid` is misnamed and should be
`def-operator`, and the manual's "third kind of object" paragraph should be
replaced by the observation that operators are syntax, not objects.

"Functoid" is then free to mean level 2, which is what the transfinite-recursion
proposition in `ch-math.tex` wanted it to mean all along, and that proposition
can be stated formally instead of in metalanguage.

## 7. Cost

**The minimal change -- adopt `app-graph`.** One axiom added; nothing removed;
no existing proof invalidated, since the axiom constrains only what was
previously unconstrained. `fun-domain-extensionality` and the three `RES` axioms
become derivable and can be demoted to theorems at leisure. The pair encoding it
needs is already load-bearing elsewhere: `(IN (LIST a b) rho)` is how
`structure-library/setoid.scm:35`, `structure-library/ringoid.scm:179` and
`theorem-library/order-zorn.scm` encode relations; `tuple-equality-decompose`
(`theory.scm`) supplies `LIST` injectivity as a procedural macete; and
`membership-implies-sethood` makes `(LIST a b)` a set as soon as it is a member.

**The maximal change -- deriving application from the graph and deleting the
third kind of object.** This touches the application fall-through in `wff.scm`,
`*wff-term-form-heads*`, the constant-head registry in `expressions.scm`, and
every tactic that pattern-matches an application. Scope, as of 2026-07-28: 105
`.scm` files mention `FUN`, 87 mention `VNB-LAMBDA`, 30 of the former are in
`structure-library/` and 58 in `theorem-library/`; `fun-apply-type-c`
(`structure-library/order-lemmas.scm:74`) appears in 51 of the 219 proven bills.

There is a trap in estimating the second: the kernel `FUN` axioms carry
`primitive` provenance, so they contribute the empty set to every bill. **Zero**
bills mention `fun-set-iff`, `dom-membership`, `res-apply` or any of the other
fifteen. The proof-debt ledger therefore cannot tell you which proofs depend on
them; only re-running the suite and reading the failures can.

## 8. Recommendation  [adopted 2026-07-28]

Adopt `app-graph`; do not rewrite the term language. The axiom delivers the
semantics -- functions genuinely are functoids that are sets -- while the term
language, which already has total application and partial equality, stays as it
is. Separately, and regardless of that decision, rename `def-functoid`: it
installs a macete and nothing else, and its borrowing of the word is what makes
the manual's account of functoids read as false.
