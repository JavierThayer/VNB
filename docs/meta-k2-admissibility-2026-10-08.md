# Admissibility of the kernel rules over a core -- design note (2026-10-08)

## 1. The decision

The user opened a session devoted to META questions about VNB on 2026-10-08, the first being
whether VNB can prove the correctness of large parts of its own kernel, oracles excluded. Five
readings of "correct" were distinguished:

* K1, semantic soundness: each rule preserves truth in every SET model of the axioms. A theorem,
  but only relative to set models (Tarski: VNB cannot define truth over the class universe) and
  never "and such a model exists" (Goedel).
* K2, admissibility over a core: each of the 59 non-oracle rules is admissible in a small core
  system. A theorem about derivations as data; no semantics, no Goedel toll; it grounds nothing,
  it reduces what has to be trusted.
* K3, implementation faithfulness: the Scheme checker computes the relation. Not provable in
  VNB without a model of Scheme.
* K4, infrastructure: grounding is a least fixed point, `qed` installs only a grounded root,
  only eight files write the graph. Testable; provable only under K3's device.
* K5, assumptions that are not theorems: consistency of the axioms, the certificate hash, MIT
  Scheme.

**The user chose K2 (2026-10-08).** This note is its design.

## 2. The object

Since 2026-09-20 every inference passes `dg-apply-rule!`, which refuses it unless the checker
registered for the rule's name accepts the (hypotheses, conclusion) pair. The 50 `pi-*`
builders therefore carry no soundness: a wrong builder can only fail to prove. What decides
whether a false sequent can be grounded is the RELATION each checker enforces, together with the
expression layer the checkers use (`alpha-equiv?`, `free-vars`, `subst-free`, the one-way
matcher), the write point and the grounding propagation (deduction-graphs.scm), the install
(`qed`), and the axioms.

K2 is about the 59 relations of `rule-checkers-logic.scm` (42), `rule-checkers-schema.scm` (13)
and `rule-checkers-rewrite.scm` (4). The 7 oracle relations are excluded by the user's
instruction.

## 3. The claim

Fix a theory `T`: a set of formulas (the axioms of the catalog and the theorems installed at the
time; a cited theorem is a member of `T`, nothing more). Let `CORE` be the set of rule relations
of section 4, each a relation between a finite list of hypothesis sequents and a conclusion
sequent. `DERIVABLE(T)` is the least set of sequents closed under every relation of `CORE`
(with `T` as the parameter of `theorem-assumption`). For every one of the 59 operations `R`,
with `REL-R(T, hyps, concl)` the relation its checker enforces, transcribed into VNB:

    forall T, hyps, concl.
        REL-R(T, hyps, concl)  and  (forall h in hyps. h in DERIVABLE(T))
        implies  concl in DERIVABLE(T).

For a rule that is in `CORE` the theorem is the closure clause. The content is the 28 rules of
section 4.6, where the proof is a derivation template constructed by recursion on the syntax
(so each is in fact DERIVABLE, which implies admissible).

What the 59 theorems establish: trusting the 59 relations is no more than trusting `CORE`. What
they do not establish: that `CORE` is sound (K1), and that the Scheme of a checker computes
`REL-R` (K3). The transcription of each checker into `REL-R` is by hand and is K3's open flank;
each `REL-R` is to be kept beside its checker, with the checker's line numbers, and reviewed as
a pair.

## 4. The core

The core is chosen so that every member is either a standard rule of natural deduction with its
side condition, or a ONE-LINE schema (an iff or an equation) that a reader checks against the
intended meaning of the constructor. A kernel rule whose checker is more than a page is not in
the core.

### 4.1 Logic (22)

`and-intro`, `and-elim`, `or-intro-left`, `or-intro-right`, `or-elim`, `implies-intro`,
`backchain`, `not-intro`, `not-elim`, `iff-intro`, `iff-elim`, `forall-intro` (the eigenvariable
condition), `forall-elim` (see 4.7), `forsome-intro`, `forsome-elim` (eigenvariable),
`assumption`, `theorem-assumption` (any member of `T`), `cut`, `weakening`,
`proof-by-contradiction`, `truth-intro`.

`backchain` is kept and `detach` retired; either is modus ponens and one suffices.

### 4.2 Equality (3)

`eq-subst`, `reflexivity` (see 4.7), `quasi-reflexivity`.

### 4.3 Conditional terms (2)

`if-true`, `if-false`. The condition of `IF` is a formula, so no catalog axiom can state these.

### 4.4 Set formation, descriptions, functions (10)

One schema per constructor and direction, as an IFF where the kernel has an intro and an elim:

| core schema | replaces |
|---|---|
| `sep-sethood` | itself |
| `sep-mem`: `y in SEP(x,A,p) iff y in A and p[x:=y]` | `sep-mem-intro`, `sep-mem-elim` |
| `comp-mem`: `y in COMP(x,p) iff y in SET and p[x:=y]` | `comp-mem-intro`, `comp-mem-elim` |
| `big-union-sethood` | itself |
| `big-union-mem`: `x in BIG-UNION(z,A,b) iff forsome z. z in A and x in b` | `big-union-mem-intro`, `big-union-mem-elim` |
| `iota-def` | itself |
| `iota-in-elim` | itself |
| `lambda-type` | itself |
| `lambda-beta-eq`: from `u in A`, `VNB-LAMBDA(s,A,b)(u) = b[s:=u]` | `lambda-beta`, `lambda-beta-hyp` (with 4.5) |
| `functoid-beta-eq`: `(apply-functoid F v..) == body[params:=v..]` | `functoid-beta` (with 4.5) |

### 4.5 Contextual rewriting: a target, not a core member

Four kernel rules (`macete`, `macete-hyp`, `lambda-beta`, `nth-reduce`, with `length-reduce`
and `functoid-beta`) rewrite a subterm at an arbitrary position of the goal, under binders,
with the conditions of the rewrite discharged by the LOCAL CONTEXT of the position (Monk's
clauses: the antecedent inside a consequent, a conjunct inside the other, the negation of the
other disjunct; assumptions mentioning a bound variable dropped under its binder). Call the
general principle CR:

    from  Gamma, Delta(pi) |- s == t   and   Gamma |- G[pi := t]
    infer Gamma |- G,                            where G has s at position pi

(and `=` or `iff` in place of `==` according to the kind of the position). CR under a FORALL,
FORSOME, NOT, AND, OR, IMPLIES or IFF is derivable from 4.1 alone. CR under a term binder (SEP,
COMP, BIG-UNION, IOTA, VNB-LAMBDA, a functoid record) needs the extensionality of that
constructor, which is a member of `T` for sets and functions (`class-extensionality`,
`fun-domain-extensionality`) and is to be derived for IOTA from `iota-def`, `iota-in-elim` and
`quasi-eq-def`. CR is therefore stated as a THEOREM (phase 3), proved by induction on the
position. Where the proof fails for some binder, that binder's congruence rule enters the core
explicitly, or the kernel's licence at that binder is narrowed; the choice is the user's.

### 4.6 Structural membership and tuple schemas (7)

The kernel's `UNION`, `INTERSECTION`, `CARTESIAN`, `TUPLES`, `NTH`, `LENGTH` and tuple
equality are n-ary, and their membership conditions exist today ONLY as kernel rules: the
catalog's `union-membership` and `intersection-membership` are binary, say nothing for n > 2,
and nothing relates them to the rules for n = 2. The core states each once, for every n:

| core schema | replaces |
|---|---|
| `union-mem`: `x in UNION(S_1..S_n) iff x in S_1 or .. or x in S_n` | `union-intro k`, `union-elim` |
| `intersection-mem` | `intersection-intro`, `intersection-elim k` |
| `cartesian-mem`: `x in CARTESIAN(A_1..A_n) iff forsome a_1..a_n. a_i in A_i and x = [a_1..a_n]` | `cartesian-intro`, `cartesian-elim k`, `cartesian-decompose` |
| `tuples-mem`: `[e_1..e_n] in TUPLES(A) iff e_1 in A and .. and e_n in A` | `tuples-intro`, `tuples-elim k` |
| `nth-eq`: `NTH(k, [t_1..t_n]) == t_k` | `nth-reduce` (with 4.5) |
| `length-eq`: `LENGTH([t_1..t_n]) == n` | `length-reduce` (with 4.5) |
| `tuple-eq`: `[a_1..a_n] = [b_1..b_n] iff a_1 = b_1 and .. and a_n = b_n` | `tuple-equality-decompose` |

Whether these seven should ALSO enter the catalog as axioms, so that the catalog and the kernel
state the same thing once, is an open decision for the user (section 8).

### 4.7 Definedness

`forall-elim` and `reflexivity` consult the certificate `pi--defined?`
(docs/definedness-instantiation-2026-09-18.md). In the core, `forall-elim` ALWAYS posts the
side sequent `t = t`, and `reflexivity` fires only for a variable or an atomic constant. Each
clause of the certificate then becomes a rule of its own, `DEF-k`, with hypotheses the context
facts the clause reads, and is either DERIVED from `T` (a term typed in context: strictness; an
application `f(a)` with `f in FUN(D,_)` and `a in D`: `fun-domain-apply-def`) or listed in the
core as a schema (a total class constructor on defined arguments; an accessor of a structure in
context). This makes the certificate's clauses visible as the rules they are. Note that the
`forall-elim` checker today calls the builder's `pi--defined?` directly
(rule-checkers-logic.scm:827), the one place where a checker is not independent of the kernel.

### 4.8 Induction: nothing in the core

`nn-induction` and `transfinite-induction` are CLASS-FORM AXIOMS of the catalog
(`forall C. 0 in C and (forall n in NN. n in C implies succ n in C) implies forall n in NN. n in C`;
the ordinal one likewise). The three kernel rules `nn-induction`, `transfinite-induction`,
`transfinite-induction-3cases` are derivable from them with `comp-mem` at `C := COMP(n, B)`.
The three-case form needs in addition the trichotomy zero / successor / limit of an ordinal,
to be located in the catalog (phase 4); if absent, that is a finding.

### 4.9 The count

Core: 22 + 3 + 2 + 10 + 7 = 44 relations, of which four carry a side condition that needs
reading (`forall-intro`, `forsome-elim`, `eq-subst`, `lambda-type`) and the rest are one-line
schemas. Retired, 28: `detach`, `contraposition`, `cartesian-intro`, `cartesian-elim`,
`tuples-intro`, `tuples-elim`, `union-intro`, `union-elim`, `intersection-intro`,
`intersection-elim`, `nth-reduce`, `length-reduce`, `functoid-beta`, `nn-induction`,
`transfinite-induction`, `transfinite-induction-3cases`, `sep-mem-intro`, `sep-mem-elim`,
`comp-mem-intro`, `comp-mem-elim`, `big-union-mem-intro`, `big-union-mem-elim`, `lambda-beta`,
`lambda-beta-hyp`, `macete`, `macete-hyp`, `cartesian-decompose`,
`tuple-equality-decompose`. By checker size the retired rules are about 2000 of the 3500
lines, and they include every rule on which a checker defect has been found (the `lambda-beta`
licence, the `macete` numeral bridge, the `eq-subst` capture and the `big-union-sethood`
cases of 2026-09-24).

## 5. The encoding

Formulas must be VNB objects, since the rules are schemas and VNB has no formula variables. The
representation is the one the strand-space work built for messages (structure-library/
strand-messages.scm): tagged nested lists, a class defined as a BIG-UNION over NN of stages, the
least closed relation as an intersection over POWER.

**Locally nameless** (Aydemir et al., "Engineering formal metatheory", 2008): a bound variable
is a de Bruijn index, a free variable is a name. Alpha-equivalence is then equality, the
capture condition of `eq-subst` disappears (an occurrence under a binder is an index, not the
name), and substitution for a free variable is structural. The translation from the kernel's
named syntax to this one is outside VNB and belongs to K3.

Every node is a list whose first entry is a numeral tag, so the cases are disjoint by
arithmetic and no token law is needed:

    FVAR n          [0, n]           n in NN, a free variable
    BVAR k          [1, k]           k in NN, a bound variable (de Bruijn index)
    CONST c         [2, c]           c in NN, an atomic constant (NN, RR, EMPTY-SET, a numeral...)
    APP h l         [3, h, l]        h in NN a head code, l a list of expressions
    BIND h n a b    [4, h, n, a, b]  h a head code, n in NN the number of variables bound,
                                     a a list of expressions outside the binder (the domain
                                     of SEP, VNB-LAMBDA, BIG-UNION), b the body, in which
                                     indices 0 .. n-1 refer to this binder

One syntactic category: the kernel's expression layer distinguishes terms from formulas by the
head, and so does the encoding, through a well-formedness predicate `WF` (arity and kind per
head code, the formula/term positions) that every core relation requires of its conclusion. The
head codes are a table in the definition file, mirrored by the (future) translator; the heads
are `*wff-term-form-heads*` (wff.scm:473) plus the connectives, quantifiers and the three
atomic relations.

    EXPR-STAGE(0)       = the FVAR, BVAR and CONST nodes
    EXPR-STAGE(succ n)  = EXPR-STAGE(n) u APP nodes over lists of stage-n expressions
                                        u BIND nodes with stage-n arguments and body
    EXPR                = BIG-UNION over n in NN of EXPR-STAGE(n)

The operations, each a function on EXPR defined by recursion on the stage (a function per stage
by `def-by-nn-recursion`, the value at an expression read off the stage of its rank):

    FV(e)               the finite set of free names
    OPEN(e, k, u)       replace index k (at its depth) by the expression u
    SUBST(e, n, u)      replace the free variable n by u
    LC(e)               locally closed: no dangling index

and the lemmas every metatheory needs: SUBST on a name not in FV is the identity; FV of a
SUBST; SUBST and OPEN commute when the substituted expression is locally closed (corrected 2026-10-08
by the phase-1 probe: with v = BVAR(k) the commutation fails); OPEN of a locally
closed expression is the identity.

**Sequents and contexts.** A sequent is `[Gamma, G]` with `Gamma` a FINITE set of locally
closed well-formed formulas (the checkers compare contexts as sets up to alpha, which is
equality here) and `G` one such formula. Finiteness is what makes "a name free in nothing of
Gamma" exist. `SEQ` is a set, as `EXPR` is.

**Derivability.** `DERIVABLE(T)` is the intersection of the subsets of `SEQ` closed under the
core relations, each relation a `def-predicate` over `T`, a list of sequents and a sequent.

## 6. The phases

1. **The cost probe.** The encoding of section 5, `FV`, `OPEN`, `SUBST`, `LC`, and the
   substitution lemmas, as a definitions file and a laws file on the strand template, probed on
   the band. The deliverable is the measure (theorems, lines, days) and the obstacles: in
   particular whether a general device for structural recursion over a staged class is needed
   in the kit (the strand work defined its one function, the rank, through IOTA, and its
   relations as least closed; four functions by hand will say whether a definition form is
   warranted).
2. `SEQ`, `WF`, the core relations, `DERIVABLE`, and the first three admissibility theorems
   (`detach`, `contraposition`, `union-intro`) to exercise the closure.
3. CR (section 4.5) as a theorem, then `nth-reduce`, `length-reduce`, `functoid-beta`,
   `lambda-beta`, `lambda-beta-hyp`, `macete`, `macete-hyp`.
4. The induction rules from the class axioms; the structural intros and elims and the two
   decomposes from the schemas of 4.6.
5. The definedness clauses (4.7).

Files: `structure-library/meta-syntax.scm` (definitions), `theorem-library/meta-syntax-laws.scm`
(the lemmas), and `meta-*.scm` siblings per phase. Nothing is wired into load.scm or
libraries.sexp until a phase is complete; when wired, the files form a library `meta`
importing `core`.

## 7. What this does not cover

The seven oracles; the certificate store and its hash; `qed` and the install; the undo journal;
the expression layer's Scheme (`alpha-equiv?`, `subst-free`), which the ENCODED operations
re-state but do not verify; MIT Scheme.

## 8. Decisions

Taken by Claude as routine (2026-10-08): locally nameless binders; tagged lists over NN; one
syntactic category with a well-formedness predicate; contexts as finite sets.

Open for the user:

* (a) Whether the seven n-ary schemas of 4.6 should also enter the catalog as axioms, so that
  the kernel's rules and the catalog state each membership condition once. Recommendation: yes,
  and retire the binary `union-membership` and `intersection-membership` as their instances.
* (b) When CR fails for a binder (4.5): add that binder's congruence to the core, or narrow the
  kernel's rewriting licence there. Recommendation: decide per binder when the proof says.
* (c) Whether, after K2, the checkers are to be rewritten over the encoding so that the VNB
  definition `REL-R` and the running checker are one object (K3 by Milawa's device, a translator
  of about a hundred lines being the residue). Not before phase 3 has measured the encoding.

## 9. Findings so far

* The `forall-elim` checker calls the builder's definedness certificate
  (rule-checkers-logic.scm:827); the certificate's clauses are unstated rules (4.7).
* The catalog's membership axioms for `UNION` and `INTERSECTION` are binary while the kernel's
  heads are n-ary; for n > 2 the kernel rules are the only statement (4.6).
* The three induction rules are derivable from the class-form axioms and `comp-mem` (4.8), so
  the kernel carries three rules it does not need to trust.

## 10. Phase 1 result (2026-10-08, 02:33Z to 04:00Z)

Done: `structure-library/meta-syntax.scm` (211 lines) and `theorem-library/meta-syntax-laws.scm` (2859
lines), 83 theorems, all `modulo 0`, every page re-runnable, probed on worker-01 against the band; not
wired. Report: `scratchpad/triage/META-1-REPORT.md`. Measured cost: about 1.5 hours of agent time, 55
probes, 36 s of proving for the whole file.

* The functions are defined per stage with a KEEP clause (coherence by construction) and read at one
  shared rank, so a new operation costs one generic call plus its value equations. The report proposes
  `def-by-structural-recursion` with an interface, and a kit driver `dk-expr-induction!`.
* The commutation of SUBST and OPEN needs `EXPR-LC(v)` (section 5, corrected above).
* Missing in the tree and met here: a map over a list (`LIST-MAP`, defined locally by IOTA), a
  congruence for BIG-UNION and SEP (done by extensionality, about 85 helper lines), "a finite union of
  finite sets is finite" (`bu-finite-nn`, NN only).
* Before a `meta` library can pass `library-gate!`, three generic lemmas the laws cite
  (`pair-self-member`, `pair-self-eq`, `cartesian3-set`) must move from the strand library to core.
* Two hazards that pass `qed` silently: a capture rename inside a driver's `subst-free` of a class into
  an induction principle (only the page audit saw it), and a theorem installed with its class variable
  free after a case-fold rename (the free-variable audit is warn-only and runs only at load end).

## 11. Phase 2 result (2026-10-08, 14:38Z to 15:58Z)

Done: `structure-library/meta-core.scm` (481 lines) and `theorem-library/meta-core-laws.scm` (2157 lines),
129 theorems, all `modulo 0`, every page re-runnable, probed on worker-01 against the 02:30Z band; not
wired. Report: `scratchpad/triage/META-2-REPORT.md`. Built: the head table and WF (with preservation by
SUBST and OPEN), `CTX-SET` and `SEQ-SET` (renamed from CTX / SEQ: a constant `SEQ` collides with a binder
`seq` in frechet-open-mapping.scm under the constant-binder gate), the eigenvariable lemma
`fresh-name-exists`, 42 core relations each with its closure theorem, `DERIVABLE` with its induction
principle, and `adm-detach`, `adm-contraposition`, `adm-union-intro`.

**Two kernel rules prove FALSITY modulo 0.** Both reproduced independently on worker-01 at 16:03Z
(`scratchpad/meta2/ifprobe-falsity.scm`, `scratchpad/meta2/exprobe.scm`; the tree's `if-true` and
`forsome-intro` are unchanged since the band). Let `u` be `IOTA z. (z in NN and FALSITY)`, which denotes
nothing.

* `if-true` / `if-false` hand over the STRICT equation `IF(p, a, b) = a`. At `a := u` that equation is
  false; in context it certifies `u` as defined (a term occurring in a true `=` hypothesis), `iota-e`
  then yields `u in NN and FALSITY`. Four steps. Repair: the rule hands over `IF(p, a, b) == a`.
* `forsome-intro` (`ew`) places no definedness condition on the witness. `NOT(u = u)` is provable
  (assume `u = u`; it certifies `u`; `iota-e`), so `ew u` gives `FORSOME y. NOT(y = y)`, refuted by
  reflexivity on the eigenvariable. Repair: `forsome-intro` owes `Gamma |- t = t` exactly as
  `forall-elim` does (section 4.7), discharged by the same certificate `pi--defined?`.

The core (section 4) is stated with both repairs. The kernel's repair is the user's decision: the IF
drivers (`dk-if-branch!`, `dk-case-if!`) consume the strict form, and an `ew` at an uncertified witness
would open an owed leaf.

**Other findings.** `functoid-beta-eq` has no encoding (the syntax has no functoid records), so 42 of the
note's relations, not 44, are defined; and section 4.1 lists 21 logic rules, not 22. `contraposition`'s
checker is unreachable (`pi-contraposit!` has no caller); recommendation: retire the rule from the kernel.
The list rules are stated with the list denoting (`nth-reduce` and `tuple-equality-decompose` do not
require it; no FALSITY was found there). About 520 lines of phase-1 helpers were copied: a shared
`meta-kit.scm` is proposed, and a `dk-derive!` driven by a derivation tree for the remaining 25
admissibility proofs.

## 12. The repairs as built (2026-10-08, the user's decision "yes to all four"), and a third FALSITY

**if-true / if-false.** The rule hands over the strict equation `IF(p, a, b) = a` when the parent context
certifies the branch `a` as defined (`pi--if-equation`, primitive-inferences.scm), and the quasi-equation
`IF(p, a, b) == a` otherwise. The strict form is then true, and the checker re-decides the split from the
parent context alone, so the new equation cannot certify itself. Handing over `==` unconditionally broke
29 proofs and 41 files in a keep-going load (most of them cascades), because drivers had relied on the strict
equation to certify branches that were in fact typed elsewhere (`PRED j_`, `recip(u_)`).

**forsome-intro.** The witness `t` is accepted when the context certifies it, OR when a top-level conjunct
of the instance `p[t]` is a strict atom (`IN`, `=`, `<=`, `<`) with `t` outside binders: an atom with an
undefined argument is false, and the conjunct is proven along with the instance. Otherwise the rule owes
`Gamma |- t = t`. The checker re-decides this case independently (`chk-instance-certifies?`).

**contraposition** is retired from the kernel.

**A third FALSITY, found while repairing (reproducer `scratchpad/meta2/ifsub-falsity.scm`, `modulo 0` on the
kernel with the first two repairs).** The certificate's clause "the term occurs outside binders in a true
strict hypothesis" (`pi--subterm-outside-binders?`, and the checker's independent clause (c),
`chk-elim-outside-binders?`) descended into an `IF` as if it were a strict position. But `IF(p, a, b)`
denotes when the branch that `p` selects denotes, so the term certifies neither branch and nothing in `p`.
`if-true` gives `IF(TRUTH, 0, u) = 0` (strictly, since `0` is certified); the hypothesis certified `u`;
`rfl` gave `u = u`; and `iota-e` gave FALSITY. Repair: both walkers stop at an `IF`. Suite: a refused case
and an accepted control, plus the accepted body-certified `forsome-intro`.

**A statement the hole had been proving.** `monomial-off` asserted `MONOMIAL(a, c, n)(k) = ZERO(a)` with
nothing typing `a`. The strict equation asserts that `ZERO(a)` denotes, and only the unconditional strict
`if-false` made it provable. It is now guarded by `IS-RING(a)`, which every citer has in context.

**A certificate defect found while repairing (a completeness defect, not a soundness one).** In
`pi--defined?` the two functoid clauses (a functoid application, and `NTH` of one) were written as `cond`
clauses with `=>`. When the functoid's instantiated body could not be certified, the whole certificate
answered `#f`, so the clauses after them, among them the predicate-hypothesis clause, were never tried on a
functoid term. `IS-DIFF-ON(K, U, f, a, CC-SERIES-LIMIT(g))` in context therefore did not certify
`CC-SERIES-LIMIT(g)`, although `IS-DIFF-ON`'s definition has the conjunct `L in CARR(K)`. Both clauses are
now plain tests, so a failure falls through to the later clauses. Every term certified this way is certified
by a clause that already existed.

**Breakage and its repair.** Keep-going loads after each round of repairs: 29 holes / 41 failed files (the
unconditional `==`); 15 / 39 (the certified-branch refinement); 20 / 41 (the IF walker repaired, which
exposed proofs that had leaned on it); 12 / 37; 2 / 9; then the run with the fall-through fix. Every driver
repair was the same species: a branch or a witness typed AFTER the step that needs it. The fix is the typing
citation moved before `if-true` / `if-false` / `ew`, or a context filter that accepts `==`. Files touched:
recip-star, poly-degree-laws (monomial-off guarded), elem-entry-readoffs, elem-actions-proof,
elem-row-actions-proof, smith-proof, c-int-oriented, bernstein-density, regulated-algebra, line-int-laws,
cauchy-criterion-left, cauchy-criterion-right, rake-completion-complete, finite-surgery.

**Decision recorded (2026-10-09).** The user approved the third repair (the definedness walkers of the
builder and of the checker stop at IF), relayed by the ordinary session after he had read a plain-language
summary of this section: "I approve." His stated standard: any crack, however small, makes the building
uninhabitable. The keep-going run kgo6 (fall-through fix included) left two holes, `cps-translate-holomorphic`
and `holomorphic-compose` (analytic-log-laws.scm), both of the pattern of this section: the witness of `ew`
was certified only by the `IS-DIFF-ON` fact cited after it. The citation now precedes the `ew`.

## 13. Phase 3 result (2026-10-09, 02:30Z to 05:00Z), and three further kernel falsities

Done: `structure-library/meta-cr.scm` and `theorem-library/meta-cr-laws.scm`, 86 theorems `modulo 0`, not wired;
report `scratchpad/triage/META-3-REPORT.md`. CR is proven for positions under the connectives, the atoms, the
quantifiers, IF, the arguments of predicates and term constants, and the domain of SEP / BIG-UNION / VNB-LAMBDA. It
is not derivable for the BODY of a term binder over the present core: the core certifies no compound term as
defined (the DEF rules of 4.7 are phase 5). For SEP, BIG-UNION, VNB-LAMBDA and COMP bodies this is a dependency on
phase 5. For an IOTA body it is not: an equation between descriptions comes only from an instance of a member of T,
and that instance owes the description's definedness. This is open decision (b) for IOTA: an IOTA congruence rule
in the core, or a narrower rewriting licence under IOTA.

The one-position forms of six rewriting rules are proven admissible. The kernel's `macete` / `macete-hyp`
relations are FALSE. Each of the three defects below was reproduced independently at 05:00Z on worker-01, each a
FALSITY `modulo 0`.

* **13.1 Symmetric OR context** (macetes.scm `lc-extend`; checker `rkw--descend`). Both disjuncts are rewritten in
  one step, each under the negation of the other's ORIGINAL form. That is sound only in a positive position.
  `scratchpad/meta3/or-ctx-falsity.scm`. The checker's AND clause has the same defect; no tactic produces it
  (`and-ctx-checker.scm`).
* **13.2 Spawned minor premise under a binder** (`rkw--condition-discharged?`, last clause; the spawn in
  `rewrite-expr`). The condition is posted with the crossed bound variable free and is closed by an outer
  variable of the same name. `minor-capture-falsity.scm`.
* **13.3 Macete instantiation without definedness** (`rewrite-expr`; checker `rkw--macete-explainer`). The match
  `x := t` is a `forall-elim` at `t` with no `t = t` owed. `macete-defined-falsity.scm`.

The repairs are the user's decision. They are listed in the report, sections 0, 0b and 0c.
