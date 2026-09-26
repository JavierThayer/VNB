# Universal instantiation and definedness -- design note (2026-09-18)

## 1. The defect

VNB's equality is partial: `t = t` is the definedness predicate, and the manual states the
LUTINS semantics (docs/ch-expressions.tex, "Strict equality"): variables and class constants
always denote; an application `f(x)` denotes when `f in FUN(A,B)` and `x in A`.  The kernel
implements this for reflexivity (`pi-reflexivity!` closes `t = t` only when `t` is
syntactically defined or a context assumption types it) and NOT for universal instantiation:
`pi-instantiate!` and `pi-spec!` (primitive-inferences.scm) substitute an arbitrary term into
a universal with no side condition.  Consequently

    forall a. a = a                       (di) (rfl): a variable denotes
    instantiated at recip(0)              gives  recip(0) = recip(0)

and the kernel proves that every term denotes.  With the axiom `fun-domain-apply-def`
(theory.scm), an IFF `f in FUN(A) => (f(x) = f(x) <=> x in A)`, this reaches `FALSITY`:
take the empty function on `EMPTY-SET` and any `x`.  The probe `scratchpad/mx/mx-probe5.scm`
closes against the library of 2026-09-17 in twelve steps.  Found by rake batch P
(2026-09-17) while trying to prove `mul-defined-factors`; confirmed 2026-09-18.

## 2. The repair: LUTINS instantiation

    forall x. p        t defined
    ------------------------------   forall-elim
              p[x := t]

`forall-elim` posts the side sequent `t = t` unless the term is certified defined, by the
same test reflexivity uses, extended as in section 4.  `fact`, `inst+`, `inst*!` and the
copilot's inst lane discharge the side sequent by the typing search reflexivity already
runs; what they cannot discharge stays an open leaf, visible at `qed`.  The rule for
variables is unchanged: a variable ranges over classes, all of which denote.

## 3. What it costs, measured

Audit of one full load (2026-09-18, `VNB_DEF_AUDIT`, hook `def-audit-note!` in
primitive-inferences.scm): 64850 instantiations, of which 3466 (5.3%) were at a term that
neither the syntactic test nor a literal context assumption certifies.  Classified by the
head of the term:

| class of term                                                     | count | discharge            |
|-------------------------------------------------------------------|------:|----------------------|
| structure accessor (`CARR`, `SCAL`, `VEC`, `PTS`, `MS`) on a variable that carries an `IS-*` hypothesis | 1648 | section 4(b) |
| comprehension-bodied constructor (`FUN`, `INTERVAL`, `ORD-SEGMENT`, `TUPLES`, `SEP`, `CCINT`, `BDD-METRIC`, `PRODUCT-CARRIER`, ...) on certified arguments, and `succ` | ~800 | section 4(a) |
| structure view (`RING-ADDITIVE-AG`, `MODULE-VECTOR-AG`, `FIELD-AS-*`, ...), a `LIST` of accessors | ~400 | 4(a) + 4(b) |
| `VNB-LAMBDA` over a certified domain, `ENUM-FAM`                  |  ~200 | 4(a) (the 2026-08-30 rule) |
| comprehension over an UNcertified argument                        |   108 | recursive certificate, else a leaf |
| arithmetic (`* + - recip /`)                                      |    88 | typing search (`IN t RR`) |
| accessor with no structure hypothesis in context                  |    30 | leaf |
| applications of variables (`phi(i)`, `f(x)`), `IOTA`, `CHOICE`, `COMPOSE`, `AMAP`, and the IOTA-bodied matrix constructors (`MATMUL`, `MATACT`, `BORDER`, `ELEM-F`, `BERNSTEIN-BASIS`, `SERIES-PARTIAL-SUM`, `NTH-DERIV`, ...) | ~190 | typing search, else a leaf |

So roughly nine in ten dissolve by two extensions of the certificate, and about three
hundred sites become owed leaves that a typing citation closes, or that expose a proof
leaning on the hole.  The last group is the honest measure of the damage and is expected
to be small: those constructors are IOTAs, and their typing theorems (`matmul-type`,
`matof-in-mat`, ...) are what the drivers cite one line earlier.

## 4. The certificate, extended (policy)

(a) **A class term denotes when its arguments do.**  `SEP`, `COMP`, `UNION`, `INTERSECTION`,
    `COMPLEMENT-IN`, `CARTESIAN`, `POWER`, `IMAGE`, `BIG-UNION`, `SINGLETON`, `PAIR`, `LIST`,
    `TUPLES`, `FUN`, `succ`, and every `def-functoid` whose body is one of these (the
    functoid registry knows the body), transitively.  This is the NBG stance the manual
    already takes ("the quantifiers range over all classes"), and the 2026-08-30 rule for
    `VNB-LAMBDA` (it denotes whenever its domain does) is its instance.  IOTA-bodied
    functoids (`MATOF` and everything built on it, `CHOICE`, `IOTA`, function application)
    are NOT in this class.

(b) **A structure hypothesis certifies its accessors.**  `IS-RING(s)` in the context
    certifies `CARR(s)`, `ADD(s)`, ...: the predicate's defining IFF has the slot typings as
    conjuncts, one unfold away.  The certificate search reads `*structure-registry*` for the
    slot list rather than unfolding.

(c) **Strictness.**  `IN`, `=`, `<=`, `<` are strict relations and every total constructor
    is strict in its arguments, so a term occurring outside any binder in a true atomic
    hypothesis of those shapes denotes -- in every position, the operator included.  A
    `def-predicate` hypothesis certifies what the conjuncts of its defining body certify,
    leading existentials stripped, to a small depth (`IS-ANTIDERIVABLE(s(k), a, b)` has
    `s(k) in FUN(RR,RR)` one unfold and one `forsome` down).

(d) Otherwise the leaf `t = t` is posted.  A hook at the command boundary
    (`dk-discharge-owed!`, driver-kit.scm; the kernel tags the leaves it posts) cites the
    term's typing theorem and closes it by reflexivity when the term is a matrix constructor
    (the seventeen with a `-type` theorem), `FINSUM` / `LINCOMB` with a typed summand, an
    `ENTRY`, or arithmetic; the steps are recorded, so the page replays them.  What the hook
    cannot close stays open and is reported at `qed`.

## 5. What it cost, measured after the fact

Nine loads on 2026-09-18.  With the rule and no certificate beyond reflexivity's: 130 files
failed.  With the certificate of section 4 (a)-(c) and the hook: 37 theorems with an owed
leaf and 24 files failing at a lane, 120 owed instantiations.  After a repair wave of four
agents over those 45 files (one typing citation moved above an instantiation, at 60-odd
sites; no statement changed) and the certificate extensions the agents' reports asked for:
**1649 proofs, no hole, 4 owed instantiations in the whole load, all four closed by the
hook**, suite 1220 checks passed.  The `mx-probe5` derivation no longer closes.

Two further things the wave found: `every` in this tree is two-argument (deduction-graphs.scm),
so a two-list call raises -- and an error inside the rule aborted the whole `fact` rather
than posting a leaf, which is worse than the defect being repaired; and an owed leaf carries
the SAME context as the node that posted it, so a driver that focuses "the leaf whose
context holds X" finds the owed leaf first.

## 6. The plan, as executed

1. Implement (a) and (b) in `term-self-defined?` / `asm-establishes-defined?`, then
   the side sequent in `pi-instantiate!` and `pi-spec!`; `fact` / `inst+` / `inst*!` /
   `dk-apply!` discharge it.  Kernel files only; the kernel-callers audit is unchanged.
2. Keep-going cold load: the failing proofs are the ~300 sites; agents repair them by
   citing the typing (a `have!` of `IN t X` before the `fact`), as in the finsum-congruence
   wave.  No theorem statement changes.
3. `mx-probe5` joins the controls that must fail; the suite gains checks that a variable
   instantiation owes nothing, a comprehension owes nothing, and `recip(0)` owes `recip(0) =
   recip(0)`.
4. The manual's account (ch-expressions "Strict equality", ch-proofs on `inst`) gains the
   rule and the date; `reference/KERNEL-RULES.md`'s `forall-elim` row gains the side
   condition.

The audit hook stays in the kernel file, off by default, as the instrument for re-measuring.
