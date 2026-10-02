# The VNB kernel

This page states, one by one, the operations that change a VNB proof, and what each of them
does. Part (a) covers the 59 operations that build hypothesis sequents, part (b) the 7 that
decide a goal by computation, part (c) the axioms. Together they are everything VNB assumes.

## The kernel and the tactics

A VNB proof is a **deduction graph**. It has two kinds of node.

* A **sequent node** holds a sequent `Γ ⊢ G`: a list of assumptions `Γ` and one assertion `G`.
* An **inference node** holds the name of a rule, one sequent node called its conclusion, and a
  list of sequent nodes called its hypotheses. It says: the conclusion follows from the
  hypotheses by this rule.

A sequent node is **grounded** when some inference node into it has all of its hypotheses
grounded. An inference node with no hypotheses grounds its conclusion at once. A proof is
complete when the node holding the statement is grounded, and a theorem is installed only then.

Posting a sequent that the graph already contains (up to renaming of bound variables) returns the
existing node. A new hypothesis may therefore be grounded on arrival.

Exactly one procedure, `dg-apply-rule!`, adds an inference node. The code that calls it is a
declared list of eight files, and a check at every startup refuses to start the system if a call
appears anywhere else (*Kernel map*).

Before it writes anything, `dg-apply-rule!` **checks the inference**. For each kernel operation
there is a *checker*: a procedure that takes the rule name recorded, the hypothesis sequents and the
conclusion sequent, and decides whether they stand in the relation the operation prescribes. For
`and-intro`: two hypotheses, the assumptions of each equal to those of the conclusion, the assertion
of the conclusion the conjunction of theirs. For `forall-intro` the relation includes the
eigenvariable condition. If there is no checker for the name, or the checker refuses, an error is
raised and the graph is unchanged. A refusal is printed even when output is suppressed, and the load
ends by reporting how many inferences were verified and how many refused.

A checker does not repeat the construction. It is written separately from the procedure that built
the hypotheses, from the statement of the rule, and uses only substitution, the free-variable
computation, equality of formulas up to renaming of bound variables, and one-way matching.
Assumption lists are compared as sets. An error in a kernel operation has to coincide with an error
in its checker to go unnoticed. Each checker has two controls in the test suite: the proofs of the
library, which it must accept, and an inference that is wrong in a stated way, which it must refuse.

Checking is on by default (`VNB_NO_RULE_CHECK=1` turns it off). On the library as loaded on
2026-09-20: 197,677 inferences verified, none refused; the load takes 30% longer with checking.

The kernel has three parts.

* **(a) Primitive procedures.** Each one inspects a sequent node, builds the hypothesis sequents
  its rule prescribes, and records one inference. Part (a) states, for each, exactly which
  hypotheses it builds.
* **(b) Oracles.** Decision procedures. An oracle computes, in Scheme, whether the assertion
  follows from some of the assumptions, and when it does it records an inference with no
  hypotheses. The computation is trusted; it leaves no trace in the graph except the rule name.
* **(c) Axioms.** The formulas that may enter a proof without proof.

A **tactic** is any other command. A tactic can change the graph only by calling procedures of
(a) and (b), and can introduce a formula without proof only by citing an axiom of (c) or a theorem
already installed. A wrong tactic can fail to prove something; it cannot make the graph accept a
wrong inference. *Tactic uses* lists, for each command, the operations of (a) and (b) it can
reach.

**Reading an entry.** `N` is the sequent node the procedure is applied to, with sequent `Γ ⊢ G`.
"Hypotheses" are the sequents of the new hypothesis nodes; the new inference node has conclusion
`N`. `Γ, A` is `Γ` with `A` added; `Γ − F` is `Γ` with `F` removed. `B[x:=t]` is substitution of
`t` for the free occurrences of `x`, with bound variables renamed where needed to avoid capture.
A procedure that **declines** leaves the graph unchanged.

Two conventions hold throughout. Formulas are compared up to renaming of bound variables: a
procedure whose argument is an assumption finds that assumption by comparing formulas that way,
and declines when none matches. And `Γ, A` is `Γ` itself when `Γ` already holds `A`; no context
carries the same assumption twice.

A procedure that takes an index or a pattern records it beside the name: the graph holds
`(cartesian-elim 2)`, `(macete NAME L R)`, `(ineq CERTIFICATE)`. The name under which the inference is counted is the leading
symbol; the arguments are data about one application.

**Definedness.** VNB terms may fail to denote, and the sign of denotation is `t = t`: strict
equality holds only between defined terms. Two operations, `forall-elim` and `reflexivity`,
therefore consult a **definedness certificate**, one test applied to a term and the assumptions of
`N`. `Γ` certifies `t` when `t` is a variable or an atomic constant, a numeral or a ground
arithmetic term, a term that `Γ` types (`t ∈ X`) or equates (`t = u`), a term occurring outside
every binder in an assumption of the form `∈`, `=`, `≤` or `<`, a total class constructor applied
to certified arguments, a separation, comprehension or indexed union whose domain is certified, an
accessor of a structure `Γ` carries, an applied structure operation whose arguments `Γ` types in
its declared domain, or `f(a)` with `f ∈ FUN(D, ·)` and `a ∈ D` in `Γ`. A term headed by `CHOICE`
or `IOTA`, and an application of an untyped function, are never certified. The policy is
`docs/definedness-instantiation-2026-09-18.md`.

---

## (a) Primitive procedures

### Logic, equality, induction and the structure eliminators

#### Direct inference

Procedure `pi-direct-inference!`. Command `di`. The rule depends on the form of the assertion `G`.

| `G` | rule recorded | hypotheses |
|---|---|---|
| `A and B` | `and-intro` | `Γ ⊢ A` and `Γ ⊢ B` |
| `A implies B` | `implies-intro` | `Γ, A ⊢ B` |
| `A iff B` | `iff-intro` | `Γ, A ⊢ B` and `Γ, B ⊢ A` |
| `not A` | `not-intro` | `Γ, A ⊢ FALSITY` |
| `forall x. B` | `forall-intro` | `Γ, guards ⊢ body` (below) |
| anything else | none | declines |

For `forall-intro`, all the leading universal quantifiers are removed in the one step. Each bound
variable `x` is replaced by an **eigenvariable**: `x` itself when `x` is not free in `Γ` or in a
guard already collected, otherwise a new variable. When the formula under the quantifier just
removed has the form `(x in A) implies C`, the formula `x in A` is collected as a guard and the
removal continues in `C`. No other antecedent is collected: `forall x. P(x) implies C` yields the
hypothesis `Γ ⊢ P(x) implies C`, and a second direct inference is needed for `Γ, P(x) ⊢ C`.

#### Disjunction introduction

Procedures `pi-or-intro-left!`, `pi-or-intro-right!`. Rules `or-intro-left`, `or-intro-right`.
Commands `oi-l`, `oi-r`. `G` must be `A or B`; the hypothesis is `Γ ⊢ A` for the left and
`Γ ⊢ B` for the right. Both decline when `G` is not a disjunction.

#### Supplying a witness

Procedure `pi-exists-witness!`. Rule `forsome-intro`. Command `ew`. Argument: a term `t`.
`G` must be `forsome x. B`. Hypothesis: `Γ ⊢ B[x:=t]`. The substituted formula must pass the
well-formedness check; a malformed witness raises an error rather than recording anything. No
definedness obligation is posted for `t`, so the procedure is not the mirror of `forall-elim` in
that respect.

#### `truth-intro`

Procedure `pi-truth!`. `G` must be `TRUTH`; no hypotheses, and `N` is grounded.

Unreachable. No proof command calls this procedure, and a `TRUTH` assertion is already closed by
`assumption` and by `reflexivity`, both of which accept it. It is listed because the code is
present and a future command could reach it.

#### Antecedent inference

Procedure `pi-antecedent-inference!`. Command `ai`. Argument: an assumption `F` of `N`.

| `F` | rule recorded | hypotheses |
|---|---|---|
| `A and B` | `and-elim` | `(Γ − F), A, B ⊢ G` |
| `A or B` | `or-elim` | `(Γ − F), A ⊢ G` and `(Γ − F), B ⊢ G` |
| `not A`, with `A` in `Γ` | `not-elim` | none: `N` is grounded |
| `forsome x. B` | `forsome-elim` | `(Γ − F), B[x:=y] ⊢ G`, with `y` free neither in `G` nor in `Γ − F` |
| `A iff B` | `iff-elim` | `(Γ − F), A implies B, B implies A ⊢ G` |
| anything else | none | declines |

It declines when `F` is not an assumption of `N`, when `F` is `not A` and `A` is not in `Γ`, and
when `F` is an implication or a universal formula. Those two are used by detachment and by
instantiation.

#### Instantiation of a universal assumption

Procedure `pi-instantiate!`. Rule `forall-elim`. Commands `inst`, `inst+`; also called by `fact`.
Arguments: an assumption `forall x. B` of `N`, and a term `t`.

Hypotheses: `Γ, B[x:=t] ⊢ G`, and, unless `Γ` certifies that `t` is defined, also `Γ ⊢ t = t`.

The universal assumption stays in `Γ`. The formula `B[x:=t]` must pass the well-formedness check;
otherwise the procedure raises an error and the graph is unchanged. The second hypothesis is there
because terms may be undefined (`f(a)` for `a` outside the domain of `f`, a description with no
referent), and a universal formula speaks only of defined values. The certificate is the one
stated above.

The same rule is recorded, once per term, by `pi-spec!` (command `apply-thm`), which cites a
theorem and then instantiates it at a list of terms.

#### The goal is already in the context

Procedure `pi-assumption!`. Rule `assumption`. Command `ass`. No arguments, no hypotheses; `N` is
grounded. It fires when `G` is `TRUTH`, or when `Γ` contains `G`, and declines otherwise.

#### Citing a theorem or an axiom

Procedure `pi-theorem-assumption!`. Rule `theorem-assumption`. Command `ta`; also called by
`fact`. Argument: a name.

Hypothesis: `Γ, S ⊢ G`, where `S` is the formula installed under that name. It declines when no
formula is installed under the name.

This is the only way a formula enters a proof without being proved in it. `S` is an axiom of part
(c), a definition, a proven theorem, or an asserted support. The bill printed when a theorem is
installed (`proven modulo ...`) lists the asserted supports it reaches through this rule, directly
or through the theorems it cites.

#### Introducing a lemma

Procedure `pi-cut!`. Rule `cut`. Commands `cut`, `have!`. Argument: a formula `A`.
Hypotheses: `Γ ⊢ A` and `Γ, A ⊢ G`. `A` is checked for well-formedness first, and a malformed
lemma raises an error before anything is recorded.

The procedure never declines. When `Γ` already holds `A`, the second hypothesis is `Γ ⊢ G`, which
is the sequent of `N` itself, so the inference has `N` among its own hypotheses and grounds
nothing. The same happens when `A` is `G`. A command that cuts a formula already present therefore
appears to succeed and leaves the proof where it was.

#### Dropping an assumption

Procedure `pi-weaken!`. Rule `weakening`. Command `wk`. Argument: an assumption `F` of `N`.
Hypothesis: `(Γ − F) ⊢ G`. It declines when `F` is not an assumption of `N`.

#### Forward modus ponens

Procedure `pi-detach!`. Rule `detach`. Command `detach!`. Argument: an assumption `A implies B`
of `N` whose antecedent `A` is also an assumption of `N`. Hypothesis: `Γ, B ⊢ G`; the implication
and its antecedent both stay. It declines when the named assumption is not an implication, or when
its antecedent is not in `Γ`.

#### Reducing the goal to an antecedent

Procedure `pi-backchain!`. Rule `backchain`. Commands `bc`, `bc*`. Argument: an assumption
`A implies B` of `N` whose consequent `B` is the assertion `G`. Hypothesis: `Γ ⊢ A`. It declines
when the named assumption is not an implication, or when its consequent is not `G`.

#### Proof by contradiction

Procedure `pi-proof-by-contradiction!`. Rule `proof-by-contradiction`. Command `pbc`. No
arguments. Hypothesis: `Γ, not G ⊢ FALSITY`. It never declines.

#### `contraposition`

Procedure `pi-contraposit!`. Argument: an assumption `A implies B` of `N`; `G` must be `not A`.
Hypothesis: `Γ ⊢ not B`.

Unreachable: no proof command calls this procedure.

#### Rewriting the assertion by a context equation

Procedure `pi-eq-subst!`. Rule `eq-subst`. Command `subst`. Argument: an equation `s = t` or a
quasi-equation `s == t`. `Γ` must contain it, in either orientation and under either of the two
heads. Hypothesis: `Γ ⊢ G'`, where `G'` is `G` with every occurrence of `s` replaced by `t`. It
declines when no such assumption is present, and when `G'` is `G`.

Occurrences in operator position are replaced as well as occurrences in argument position. A
subterm below a binder whose bound variable occurs free in `s` or in `t` is left alone, since
rewriting there would capture. `G'` is checked for well-formedness.

The direction of the rewrite is fixed by the argument, not by the orientation in which `Γ` happens
to hold the equation. To use a context equation from right to left, name it the other way round.

#### Reflexivity and quasi-reflexivity

Procedures `pi-reflexivity!`, `pi-quasi-reflexivity!`. Commands `rfl`, `qrfl`. Neither takes an
argument, and neither posts a hypothesis: on success `N` is grounded.

`reflexivity` fires when `G` is `TRUTH`, or when `G` is `t = u` with `t` and `u` the same term and
`Γ` certifying `t` defined. `quasi-reflexivity` fires when `G` is `t == u` with `t` and `u` the
same term, and asks nothing further: quasi-equality holds between two undefined terms as well.

#### Conditional terms

Procedures `pi-if-true!`, `pi-if-false!`. Commands `if-true`, `if-false`. Argument: a conditional
term `IF(p, a, b)`. It need not occur in `G`.

| rule | hypotheses |
|---|---|
| `if-true` | `Γ ⊢ p` and `Γ, IF(p,a,b) = a ⊢ G` |
| `if-false` | `Γ ⊢ not p` and `Γ, IF(p,a,b) = b ⊢ G` |

The assertion is not rewritten. The branch equation arrives as an assumption, and it takes an
`eq-subst` to use it. An argument that is not a conditional term raises an error rather than
declining.

#### Cartesian products

Procedures `pi-cartesian-intro!`, `pi-cartesian-elim!`. Commands `ci`, `ce`.

For `cartesian-intro`, `G` must be `[a_1..a_n] in A_1 × ... × A_m`, with a literal tuple on the
left and a literal product on the right. It declines unless `n = m`; the hypotheses are then
`Γ ⊢ a_i in A_i`, one per `i`.

`cartesian-elim` takes such a membership as an assumption and an index `k`. Hypothesis:
`Γ, a_k in A_k ⊢ G`; the membership stays. It declines unless `n = m` and `1 ≤ k ≤ n`. The index
is recorded with the name.

#### Tuples

Procedures `pi-tuples-intro!`, `pi-tuples-elim!`. Commands `ti`, `te`. `TUPLES(A)` is the class of
finite tuples over `A`. For `tuples-intro`, `G` must be `[a_1..a_n] in TUPLES(A)`, and the
hypotheses are `Γ ⊢ a_i in A`, one per `i`. `tuples-elim` takes such a membership and an index `k`
with `1 ≤ k ≤ n`, and posts `Γ, a_k in A ⊢ G`. The index is recorded with the name.

#### Unions

Procedures `pi-union-intro!`, `pi-union-elim!`. Commands `ui`, `ue`. `UNION` takes `n` arguments.
`union-intro` takes an index `k` with `1 ≤ k ≤ n` and a goal `x in A_1 ∪ ... ∪ A_n`; the hypothesis
is `Γ ⊢ x in A_k`, and the index is recorded with the name. `union-elim` takes such a membership as
an assumption `F` and posts `n` hypotheses `(Γ − F), x in A_i ⊢ G`; the membership is consumed.

#### Intersections

Procedures `pi-intersection-intro!`, `pi-intersection-elim!`. Commands `ii`, `ie`. For a goal
`x in A_1 ∩ ... ∩ A_n`, `intersection-intro` posts `n` hypotheses `Γ ⊢ x in A_i`.
`intersection-elim` takes such a membership as an assumption and an index `k` with `1 ≤ k ≤ n`, and
posts `Γ, x in A_k ⊢ G`; the membership stays, and the index is recorded with the name.

#### `NTH` and `LENGTH` of a literal tuple

Procedures `pi-nth-reduce!`, `pi-length-reduce!`. Commands `nth-r`, `len-r`. Neither takes an
argument. `nth-reduce` replaces every subterm `NTH(k, [t_1..t_n])` of `G` by `t_k`, and
`length-reduce` replaces every subterm `LENGTH([t_1..t_n])` by `n`. Each posts the single
hypothesis `Γ ⊢ G'` and declines when `G'` is `G`. `nth-reduce` raises an error on an index outside
`1 ≤ k ≤ n`.

Neither asks anything of the entries. A literal tuple has `n` places whether or not the terms in
them denote.

#### Functoid application

Procedure `pi-functoid-beta!`. Rule `functoid-beta`. Command `beta`. No argument. Every application
of a functoid to a matching number of arguments, anywhere in `G`, is reduced by parallel
substitution of the arguments for the bound variables; an application whose argument count differs
from the functoid's is left alone. Hypothesis: `Γ ⊢ G'`, and it declines when `G'` is `G`.

#### Induction on `NN`

Procedure `pi-nn-induction!`. Rule `nn-induction`. Command `ni`. No argument. `G` must have the
shape `forall n. n in NN implies B`, with the guard on the variable the quantifier just bound.
Hypotheses:

    Γ ⊢ B[n:=0]
    Γ ⊢ forall n. n in NN implies (B implies B[n:=succ n])

It declines on any other shape. In particular the induction variable must be the outermost one: a
statement that quantifies over something else first is not of this shape.

#### Transfinite induction

Procedure `pi-tfi!`. Rule `transfinite-induction`. Command `tfi`. No argument. `G` must be
`forall α. α in ORD implies P`. One hypothesis:

    Γ ⊢ forall α. (α in ORD and forall β. β <_ORD α implies P[α:=β]) implies P

with `β` free neither in `Γ` nor in `G`. This is strong induction: the hypothesis of the step is
`P` at every smaller ordinal.

The operation `transfinite-induction` and the axiom of the same name in
`structure-library/ordinals.scm` are two different objects. One is code in the kernel, the other a
formula in the catalog.

#### Transfinite induction in three cases

Procedure `pi-tfi3!`. Rule `transfinite-induction-3cases`. Command `tfi3`. No argument, and the
same goal shape. Three hypotheses:

    base       Γ ⊢ P[α:=0]
    successor  Γ ⊢ forall α. (α in ORD and P) implies P[α:=succ_ORD α]
    limit      Γ ⊢ forall α. (LIMIT-ORD(α) and forall β. β <_ORD α implies P[α:=β]) implies P

### Set formation, descriptions and functions

The three binders of this group carry a formula or a class expression in their body, with a
variable of the binder free in it. A first-order axiom would need a variable ranging over formulas,
which VNB does not have, so each is characterised by operations instead. `SEP(x, A, p)` is
`{x ∈ A | p}`, `COMP(x, p)` is `{x | p}`, and `BIG-UNION(z, A, b)` is `⋃_{z ∈ A} b`.

#### Separation

Procedures `pi-sep-sethood!`, `pi-sep-mem-intro!`, `pi-sep-mem-elim!`. Commands `sep-set`,
`sep-mi`, `sep-me`.

| rule | applies to | hypotheses |
|---|---|---|
| `sep-sethood` | `G` is `SEP(x,A,p) in SET` | `Γ ⊢ A in SET` |
| `sep-mem-intro` | `G` is `y in SEP(x,A,p)` | `Γ ⊢ y in A` and `Γ ⊢ p[x:=y]` |
| `sep-mem-elim` | assumption `F`: `y in SEP(x,A,p)` | `(Γ − F), y in A, p[x:=y] ⊢ G` |

Each declines when the assertion, or the named assumption, is not of the stated shape. The
membership assumption is consumed by `sep-mem-elim`.

#### Comprehension

Procedures `pi-comp-mem-intro!`, `pi-comp-mem-elim!`. Commands `comp-mi`, `comp-me`. A
comprehension is in general a proper class, and its members are sets, so the domain condition of
separation is replaced by membership in `SET`. For `G` of the form `y in COMP(x,p)`,
`comp-mem-intro` posts `Γ ⊢ y in SET` and `Γ ⊢ p[x:=y]`. For an assumption `F` of that form,
`comp-mem-elim` posts `(Γ − F), y in SET, p[x:=y] ⊢ G` and consumes `F`.

There is no sethood rule for comprehension. A comprehension is a set only when it is separately
shown to be bounded by one.

#### Indexed union

Procedures `pi-big-union-sethood!`, `pi-big-union-mem-intro!`, `pi-big-union-mem-elim!`. Commands
`bu-set`, `bu-mi`, `bu-me`. Write `U` for `BIG-UNION(z, A, b)`.

| rule | hypotheses |
|---|---|
| `big-union-sethood` | `Γ ⊢ A in SET` and `Γ ⊢ forall z. z in A implies b in SET` |
| `big-union-mem-intro` | `Γ ⊢ w in A` and `Γ ⊢ x in b[z:=w]` |
| `big-union-mem-elim` | `(Γ − F), e in A, x in b[z:=e] ⊢ G` |

`big-union-sethood` applies to a goal `U in SET` and renames `z` away from `A`, `b`, `G` and `Γ`.
`big-union-mem-intro` applies to a goal `x in U` and takes the witness `w` as its argument;
`x in b[z:=w]` is checked for well-formedness. `big-union-mem-elim` takes an assumption `F` of the
form `x in U`, consumes it, and introduces an eigenvariable `e` free in none of `G`, `A`, `b`, `x`
and `Γ − F`.

#### Definite descriptions

Procedures `pi-iota-def!`, `pi-iota-in-elim!`. Commands `iota-d`, `iota-e`. `IOTA(x, p)` is the
unique `x` satisfying `p`, and denotes nothing when there is no such `x` or more than one. Both
take the term as their argument; it need not occur in `G`. Both grant the defining property
`p[x := IOTA(x,p)]` as an assumption, and they differ in what pays for it.

`iota-def` pays with a proof. Hypotheses:

    Γ ⊢ forsome x. (p and forall y. p[x:=y] implies x = y)
    Γ, p[x := IOTA(x,p)] ⊢ G

`iota-in-elim` pays with the context. It fires only when an assumption witnesses that the
description denotes, by the first two clauses of the definedness certificate: an assumption
`IOTA(x,p) in X`, or one equating it strictly with something. Its single hypothesis is
`Γ, p[x := IOTA(x,p)] ⊢ G`. With no such assumption it declines.

#### Typing a function term

Procedure `pi-lambda-type!`. Rule `lambda-type`. Command `lam-t`. `VNB-LAMBDA(σ, A, b)` is the set
of pairs `{(x, b) : x ∈ A}`, with `σ` the binder, a variable or a list of variables. The term
carries its domain.

No argument. `G` must be `VNB-LAMBDA(σ, A, b) in FUN(A', B)` with `A` and `A'` the same class term.
Two hypotheses, in this order:

    Γ ⊢ forall x. x in A implies b in B
    Γ ⊢ A in SET

For a binder list `[x_1..x_n]` the domain must be `A_1 × ... × A_n` with the same `n`, and the
first hypothesis becomes the `n`-fold guarded universal.

It declines when the declared domain differs from the one the `FUN` claims, and when a binder list
meets a domain that is not a product of the matching length. Neither condition is decoration.
Without the first, one term types into `FUN(A,B)` for every `A`. Without the sethood hypothesis, a
function on a proper class, which is itself a proper class, would be certified into a `FUN`.

#### Beta reduction of a function term

Procedures `pi-lambda-beta!`, `pi-lambda-beta-hyp!`. Commands `lam-b`, `lam-b-h`. `lambda-beta`
takes no argument and reduces every redex `VNB-LAMBDA(σ, A, b)(u_1..u_n)` in `G` by parallel
substitution. `lambda-beta-hyp` takes an assumption `F` and reduces the redexes in it. Each
declines when the reduction changes nothing.

The reduced formula is the first hypothesis: `Γ ⊢ G'` for the goal, `(Γ − F), F' ⊢ G` for an
assumption. After it come the **obligations**, one per redex whose licence is not evident: `u in A`
for a single argument, `[u_1..u_n] in A` otherwise. A licence is evident when that membership is in
`Γ`, or holds where the redex sits, which the walker reads off the enclosing guarded universals and
off the domains of enclosing `VNB-LAMBDA`, `SEP` and `BIG-UNION` binders. A member of `FUN(A,B)` is
defined exactly on `A`, so reducing off the domain without the obligation would make a term denote
that the theory says does not.

The obligation is posted in the context of `N`. A redex under a binder that has not yet been
introduced therefore owes a membership in which the bound variable is free, and that leaf cannot be
closed. Introducing the binder and typing the argument first is not a preference but the condition
under which the obligation is provable.

### Rewriting

#### Application of a macete to the assertion

Procedure: the one built for each installed theorem by `make-elementary-macete`. Rule
`(macete NAME L R)`, where `NAME` is the theorem and `L`, `R` are the two sides below. Commands `mac`, `macm`.

A **macete** is a rewrite rule read off an installed theorem. The theorem has the form

    forall x1 ... xn.  C1 implies ( ... (Ck implies  L = R))

where `=` may also be `==` (equal when either side is defined) or `iff`, and a theorem with no
equation is read as `L iff TRUTH`. The conditions `C1 ... Ck` may be absent.

Hypothesis: `Γ ⊢ G'`, where `G'` is `G` with each subterm that matches `L`, and whose conditions
hold where it stands, replaced by the corresponding instance of `R`. It declines when `G'` is `G`.
Matching is one-way: the variables `x1 ... xn` are bound to subterms of `G`, and no variable of
`G` is bound. The theorem's name and the two patterns are recorded, so that the checker can confirm
the rewrite is an instance of the theorem it claims to apply.

A condition **holds where the subterm stands** when its instance is in the **local context** of
that position: `Γ`, together with what the position itself supplies. Inside `B` in `A implies B`
the local context gains `A`; inside `B` in `A and B` it gains `A`; inside either disjunct of
`A or B` it gains the negation of the other (Monk). Below a binder, the assumptions in which the
bound variable occurs free are dropped from the local context. A condition also counts as held when
it is `TRUTH`, or a closed arithmetic sentence that evaluates to true, or matches an assumption
after `succ` of a numeral is folded into that numeral on both sides. A match whose conditions do not
all hold is left alone, and the rewriter descends into its subterms instead.

#### Application of a macete to an assumption

Procedure `apply-macete-to-assumption!`. Rule `(macete-hyp NAME L R)`. Commands `mac-h`, `mac-h*`.
Arguments: the name of a macete and an assumption `F` of `N`. The rewrite is made whether or not
the conditions hold. Hypotheses: `(Γ − F), F' ⊢ G`, and one hypothesis `Γ ⊢ Ci'` for each
instantiated condition that the local context does not contain.

Besides declining when the rewrite changes nothing, this rule declines on two conditions the
goal-side one does not impose, both read off the named theorem. The theorem's core must be an
equivalence, that is an `iff` or one of the two equalities, since replacing an assumption by a
consequence of it would lose information. And no variable of `R` or of a condition may be left
undetermined by the match, since such a variable would be conjured free into the context.

#### `cartesian-decompose`

Procedure: a closure in the macete table (`theory.scm`). Command `mac`. Every subformula of `G` of
the form `x in A_1 × ... × A_n` is replaced by

    forsome a_1. a_1 in A_1 and ( ... and forsome a_n. a_n in A_n and x = [a_1..a_n])

with the `a_i` fresh. Hypothesis: `Γ ⊢ G'`, and it declines when `G'` is `G`.

This is the membership condition of the product, and it is not a formula in the catalog: the fresh
witnesses cannot be written as a fixed template, so it is code. It is on the primitive shelf and
contributes nothing to a bill.

#### `tuple-equality-decompose`

Procedure: a closure in the macete table (`theory.scm`). Command `mac`. Every subformula of `G` of
the form `[a_1..a_n] = [b_1..b_n]`, with literal tuples of equal length on both sides, is replaced
by the conjunction of the `a_i = b_i`; for `n = 0` the replacement is `TRUTH`. Hypothesis: `Γ ⊢ G'`,
and it declines when `G'` is `G`.

Tuples of different lengths are not rewritten. That two of them cannot be equal is a separate fact
and not this rule's business.

---

## (b) Oracles

An oracle decides a class of assertions by computation. On success it records an inference with no
hypotheses, so `N` is grounded at once; the computation itself leaves no trace in the graph. Three
of the seven print the certificate they found, for the reader.

### Ground arithmetic

Procedure `pi-arith!` (`arith-eval.scm`). Rules `arith-ground`, `arith-forsome`, `arith-simplify`.
Command `arith`. One procedure records all three, trying them in this order.

`arith-ground` fires when `G` evaluates to true. The evaluator reads `=` and `<=` between terms it
can reduce to exact numbers, membership in `NN`, `ZZ`, `QQ`, `RR` and `CC`, and the connectives
`not`, `and`, `or`, `implies`. Everything else is undecided: a free variable, a quantifier, a
biconditional, a strict `<`, or a value that is not exact. Arithmetic is exact throughout; a
computed floating-point value is refused rather than rounded.

`arith-forsome` fires when `G` is `forsome x. x in C and e = x`, or the same with the equation
reversed, `e` reduces to a number and that number lies in `C`.

`arith-simplify` is the fallback. When replacing the ground numeric subterms of `G` by their values
changes `G`, it posts the single hypothesis `Γ ⊢ G'`. This is the one rule of the three that is not
a closure.

The command declines when none of the three applies.

### `ring-simplify`: identities of rings

Procedure `pi-ring-simplify!` (`structure-library/ring-simplify.scm`). Commands `rs`, `simp`. No
arguments, no hypotheses. Leading universals of `G`, each guarded by a membership in one of the
number domains, are peeled first; what remains must be an equation `e_1 = e_2`. Each side is
normalised in the free associative ring `ZZ[generators]`, where a **generator** is a maximal subterm
that ground evaluation cannot reduce to a number, and where multiplication does not commute. It
fires when the two normal forms are equal and every generator of either side is certified in a
number domain, by a guard just peeled or by an assumption. It declines otherwise.

The generators counted are those of the two sides as written, including any that cancel. Otherwise
`x - x = 0` would close for an `x` of which nothing is known, and in VNB a membership is also what
says that a term denotes.

### `comm-ring-simplify`: identities of commutative rings

Procedure `pi-comm-ring-simplify!` (`structure-library/comm-ring-simplify.scm`). Command `crs`. No
arguments, no hypotheses. The same normal-form test, in the free commutative ring `ZZ[generators]`,
where a monomial is a sorted multiset of generators. Two readings are tried in turn. The first is
over the number domains, with literal powers expanded first. The second is over the operations of an
arbitrary structure, `(ADD R)`, `(MUL R)`, `(NEG R)`, `(ZERO R)` and `(ONE R)`, and requires
`IS-COMMUTATIVE-RING(R)` from a peeled guard or from `Γ`; the generators are then certified in the
carrier `CARR(R)`.

### `ineq`: linear arithmetic over the reals

Procedure `pi-ineq!` (`structure-library/ineq-oracle.scm`). Command `ineq`. Arguments: the positions
in `Γ` of the assumptions to use as premises, counted from one. No hypotheses: when the procedure
succeeds `N` is grounded, and otherwise it declines.

The assertion and each named premise are read as linear equations or inequalities in their **atoms**,
the maximal subterms that are not themselves sums, differences, or products by a numeral. A named
premise that does not read this way is left out, which can only make the procedure prove less; an
index outside the range of `Γ` is an error and abandons the call. Every atom of the assertion and of
a premise that is used must be certified real, including an atom that cancels: `Γ` contains
`a in RR`, or `a` is `abs(t)` with the atoms of `t` certified, or `a` is a variable bound by a leading
quantifier of the assertion restricted to `RR`. A variable bound by such a quantifier must not occur
free in any assumption of `N`; otherwise the operation declines. Fourier-Motzkin elimination is then
run on the premises together with the negation of the assertion. It succeeds when the elimination
reaches `0 < 0`. The nonnegative combination of premises that produces it (a **Farkas certificate**)
is printed and is recorded in the graph with the rule name.

The checker of `ineq` does not run the elimination again. It verifies the certificate by rational
arithmetic: with its own reader of linear forms, it confirms that the stated combination of the
premises and the negated assertion is an absurd inequality between constants, that the multipliers
are nonnegative, that every atom is certified real, and the condition on bound variables.

The condition on bound variables is the eigenvariable condition of `forall-intro`. Until 2026-09-20
the oracle did not impose it: from `x in RR, x <= 0` it closed `forall x in RR. x <= 0`. The defect
was found when the checker was written for this operation. No proof in the library had used it.

### `sos`: nonnegativity by a sum of squares

Procedure `pi-sos!` (`structure-library/sos-oracle.scm`). Command `sos`. Arguments: the terms
`c_1..c_n` to be squared. No hypotheses. Leading universals of `G` guarded by membership in `RR` are
peeled first; what remains must be `a <= b` or `b >= a`. The difference `b - a` and the squares
`c_i^2` are normalised as `comm-ring-simplify` normalises, every generator being certified in `RR`
as `ineq` requires. An exact linear program then decides whether
`b - a = λ_1 c_1^2 + ... + λ_n c_n^2` with every `λ_i ≥ 0`. On success the `λ_i` are printed; the
graph does not record them.

The oracle verifies a certificate, it does not search for one: the squares are supplied by the
caller. A strict inequality is not accepted, since a square may be zero.

---

## (c) Axioms

*Outline.* The axioms are the formulas installed with provenance `primitive`: 198 of them, counted
from the Axioms section of the theorem catalog, where each is listed with its statement. This part
will present them in groups. By count, from the catalog:

| group | axioms |
|---|---:|
| the number systems `NN`, `ZZ`, `QQ`, `RR`, `CC` (closure, ring and order laws, completeness of `RR`) | 102 |
| ordinals (well-ordering, successor and limit, suprema, transfinite induction) | about 25 |
| sets and classes (extensionality, the empty set, power set, union, intersection, complement, finite sets by listing) | about 25 |
| functions, application, domains, images (`app-graph`, `image-set`, `fun-*`, `dom-*`, `res-*`, `partial-fun-*`) | about 21 |
| tuples, lists, Cartesian products | about 10 |
| equality, quasi-equality and choice (`choice-axiom`) | about 9 |
| the two infinite points of the extended reals | 4 |

Separation, class comprehension and the indexed union are not formulas but rules, and are in
part (a). The grouping above is by the names in the catalog; the final text will be produced from
the catalog, not written by hand, so that the two cannot disagree.

A **definition** (`def-predicate`, `def-constant`, a structure declaration) installs a formula that
introduces a new symbol and says what it means. Definitions are not axioms and add nothing to a
bill. An **asserted support** is a formula assumed for the time being, with a stated warrant.
Supports are not part of the kernel: every theorem that reaches one says so on its bill.
