# VNB structure catalog

The mathematical structures the system knows at startup, and the relations
between them. Prose notes; the machine-generated, always-current listing —
every structure's declaration, slots, parent and theorems — is
`STRUCTURE-INDEX.md`.

## How a structure is encoded

A *structure* is a VNB list (a tuple); its accessors are projections
(`(CARR s) = (NTH 1 s)`, …). A *structure species* — the symbol `RING`,
`FIELD`, … — denotes the proper class `{ s | IS-X(s) }`.

Every structure is declared by **`declare-structure`**. That is a macro over
the procedure `def-structure-from-clauses` — `(declare-structure NAME clause
...)` expands to `(def-structure-from-clauses 'NAME (list 'clause ...))` and
they are otherwise the same thing; the macro exists to spare you the quoting,
the procedure is what you call if you ever compute the clauses. Everything
below — the class axiom, the accessor macetes, the `IS-X` definition, the
operator-table entry, the recorded declaration the browser shows — comes out
of that one funnel.

**Declaration is grouped; instance is flat.** The clauses `(carriers CARR
OTHER) (op MUL …) (constant IDEN …)` are *parsing sugar*: the parser consumes
the grouping and installs each carrier, op and constant at a single flat
top-level slot, in declaration order. A 2-carrier `BONGO-GROUP` with one op
`MUL` and one constant `IDEN` has 4 flat slots:

```
(LIST carr-val other-val mul-val iden-val)     ; correct: 4 slots, (LENGTH _) = 4
(LIST [carr-val other-val] mul-val iden-val)   ; WRONG: 3 slots, IS-BONGO-GROUP refutes
```

So when building an instance by hand (or a bridge from another structure, e.g.
the additive AG of a ring), write the slots flat in declaration order; do not
nest the carriers as a sub-list. `IS-X` enforces it — a misaligned `LIST` is
simply refutable in the class — but writing it right the first time is easier
with the convention spelled out.

### Two ways to declare, not two mechanisms

`IS-X` always means "is an X", never merely "is X-shaped": the laws are clauses
of the declaration and `build-is-axiom` folds them into the definition. What
differs between two structures is whether the declaration brings its own
*shape*.

- **Shape structures** declare slots — `(carriers …)`, `(op …)`,
  `(constant …)`, `(derived …)`, `(substructure …)` — plus their laws, as
  `(property is-associative OPR CARR)` (a named law from
  `operation-properties.scm`) or `(law "…")` (an arbitrary law in surface
  syntax, over the structure variable `s`). SEMIGROUP, MONOID, COMM-MONOID,
  GROUP, ABELIAN-GROUP, NORMED-AG, RING, FIELD, NORMED-FIELD, MODULE,
  NORMED-VECTOR-SPACE, METRIC-SPACE, TOP-SPACE, SETOID.

- **Refinements** declare `(same-shape-as PARENT)` and laws, and *no slots*:
  the accessors are the parent's. `def-substructure` generates
  `IS-X(s) <=> IS-PARENT(s) and <laws>`, parent conjunct first and literal.
  COMMUTATIVE-RING, INTEGRAL-DOMAIN, EUCLIDEAN-RING, PID, VECTOR-SPACE.

A refinement *must not* add a shape clause, and it is an error to try. A
shape-only `IS-COMMUTATIVE-RING` would be equivalent to `IS-RING` (same six
slots) and so force every ring commutative; INTEGRAL-DOMAIN's `ONE ≠ ZERO`
would outright contradict the zero ring. The literal `IS-PARENT` conjunct is
load-bearing twice over: it carries the shape, and it is why
`euclidean-ring-is-integral-domain` is provable modulo 0 by a single `mac-h`
(`structure-library/subtype-laws.scm`) — the parent is right there on the RHS.

Nobody hand-writes an `is-X-def` IFF axiom any more. (Until 2026-07-12 the
refinements did, which is why older notes speak of "definitional predicates"
as if they were a separate mechanism; they are not.)

## Hierarchy

Two different relations hold structures together, and the difference is the
shape:

* **Subtype** — same shape, more laws. `IS-X(s) => IS-PARENT(s)`, on the nose.
* **Functor** (`def-functor`, `structure-library/views.scm`) — *different*
  shape. It builds the parent-shaped tuple out of the child's slots, and
  specializes the parent's theorems to it. A ring's additive abelian group is
  a functor, and so is FIELD's route back to the RING chain: FIELD has eight
  slots (it carries `NON-ZERO` and `RECIP`), so it is not a RING-shaped tuple
  at all.

```
SEMIGROUP                 CARR; OPR
└─ MONOID                 + IDEN                     (comm-monoid-is-monoid: axiom)
   ├─ COMM-MONOID         + OPR commutative
   └─ GROUP               + INV                      (abelian-group-is-group: PROVEN)
      └─ ABELIAN-GROUP    + OPR commutative
         └─ NORMED-AG     + NRM: CARR → RR           (a separate shape; functor back)

RING                      CARR; ADD MUL NEG; ZERO ONE          (6 slots)
└─ COMMUTATIVE-RING       same shape + MUL commutative         PROVEN
   └─ INTEGRAL-DOMAIN     same shape + ONE≠ZERO, no zero divisors   PROVEN
      ├─ EUCLIDEAN-RING   same shape + a Euclidean degree exists    PROVEN
      └─ PID              same shape + every ideal principal

FIELD                     RING's 6 slots + NON-ZERO (derived) + RECIP   (8 slots)
NORMED-FIELD              RING's 6 slots + FNRM: CARR → RR             (7 slots)
   — related to the RING chain by functor, not subtype:
     FIELD-AS-INTEGRAL-DOMAIN, FIELD-AS-EUCLIDEAN-RING,
     NORMED-FIELD-AS-COMMUTATIVE-RING, NORMED-FIELD-AS-INTEGRAL-DOMAIN

MODULE                    SCAL (a RING); VEC; VADD VZERO VNEG; ACT
└─ VECTOR-SPACE           same shape + SCAL is a field
NORMED-VECTOR-SPACE       MODULE's slots + VNRM (a separate shape; functor back)

METRIC-SPACE              PTS; DIST: PTS×PTS → RR
TOP-SPACE                 PTS; OPENS ⊆ P(PTS)         (Met → Top: the METRIC-TOP functor)
SETOID                    PTS; REL an equivalence
```

Slots 1–6 of FIELD and NORMED-FIELD deliberately mirror RING's, so the shared
accessor macetes (`ADD`, `MUL`, `NEG`, `ZERO`, `ONE`) keep the same `NTH` index
on all three. FIELD's `NON-ZERO` is a **derived** slot: `IS-FIELD` pins it to
`CARR \ {ZERO}`, so it is not a set the tuple may choose freely, and a field
morphism is one map, not two.

The four subsumptions marked PROVEN (`abelian-group-is-group`,
`commutative-ring-is-ring`, `integral-domain-is-commutative-ring`,
`euclidean-ring-is-integral-domain`) are theorems, modulo 0, in
`subtype-laws.scm` — a one-breath `mac-h` off the parent conjunct. They were
asserted axioms until `mac-h` existed.

## Numeric instances

Installed by `declare-instance!` (`structure-library/numeric-instances.scm`,
`complex.scm`), which precomputes the instance's slots.

| Domain | Instance | Memberships |
|---|---|---|
| NN | `NN-ADD-MONOID` | COMM-MONOID |
| ZZ | `ZZ-RING` | RING, COMMUTATIVE-RING, INTEGRAL-DOMAIN, EUCLIDEAN-RING |
| QQ | `QQ-RING`, `QQ-FIELD` | RING, COMMUTATIVE-RING, INTEGRAL-DOMAIN; FIELD |
| RR | `RR-NORMED-FIELD`, `RR-MS` | NORMED-FIELD; METRIC-SPACE (and complete) |
| CC | `CC-NORMED-FIELD`, `CC-MS` | NORMED-FIELD; METRIC-SPACE |

ZZ is a Euclidean ring (degree = `abs`) but not a field. QQ/RR/CC are fields.
The Euclidean / normed witnesses are existential; for the numeric instances
the actual functions are `abs` (RR) and `magnitude` (CC).

## Functions on RR / CC

- **RR**: `+ * - recip abs <=`; `power(x,n)` for `n ∈ NN`; and, from
  `structure-library/real-powers.scm`, `RPOW(a,b)` for `a > 0` and `b ∈ QQ`,
  and `SQRT(a)` for `a >= 0` (`sqrt-sq`, `sqrt-of-sq`, `sqrt-mono`,
  `sqrt-mul`, `SQRT(a) = RPOW(a, 1/2)`). RPOW and SQRT are axiomatized
  outright, as warranted supports — they are not constructed.
- **CC**: `+ * - recip conjugate magnitude` (the modulus, `CC→RR`,
  axiomatized directly — it needs no `SQRT`); `power(x,n)` for `n ∈ NN`.
- `power` takes only `NN` exponents; for anything else use `RPOW`.

## Matrices

`MATRIX(S)` — the class of matrices over a set `S`: a list of rows, each row
a list of elements of `S`, all rows of equal length. Formally a matrix is an
element of `TUPLES(TUPLES S)` with equilong rows (`matrix-membership`);
`MATRIX(S)` is a set when `S` is (`matrix-sethood`). `SIZE(M)` = `[rows,
columns]` = `[LENGTH M, LENGTH(NTH 1 M)]`. A class-former like `FUN`/`TUPLES`,
not an algebraic structure. `structure-library/matrix.scm`.
