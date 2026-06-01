# VNB structure catalog

The mathematical structures the system knows at startup, and the relations
between them. All relations listed here are **axioms** (no proofs yet).

## How a structure is encoded

A *structure* is a VNB list (a tuple); its accessors are projections
(`(A s) = (NTH 1 s)`, …). A *structure species* — the symbol `RING`,
`FIELD`, … — denotes the proper class `{ s | IS-X(s) }`.

**Declaration is grouped; instance is flat.** The clauses in a
`def-structure-from-clauses` call — `(carriers A B) (op MUL …)
(constant E …)` — are *parsing sugar*: the parser consumes the
grouping, then installs each carrier, op, and constant at a single
flat top-level slot in declaration order. A 2-carrier `BONGO-GROUP`
with one op `MUL` and one constant `E` has 4 flat slots:

```
(LIST a-val bongo-val mul-val e-val)        ; correct: 4 slots, (LENGTH _) = 4
(LIST [a-val bongo-val] mul-val e-val)      ; WRONG: 3 slots, IS-BONGO-GROUP refutes
```

So when building an instance by hand (or a bridge from another
structure, e.g. the additive AG of a ring), write the slots flat in
declaration order; do not nest the carriers as a sub-list. The IS-X
predicate enforces this — a misaligned LIST is simply refutable in
the class — but writing it correctly the first time is easier with
the convention spelled out.

Two kinds of `IS-X`:

- **Shape predicates** (`def-structure-from-clauses`): `IS-X(s)` checks only
  that `s` has the right length and its slots are typed. SEMIGROUP, MONOID,
  COMM-MONOID, GROUP, ABELIAN-GROUP, RING, METRIC-SPACE.
- **Definitional predicates** (plain `IFF` axiom): `IS-X(s)` is
  `IS-parent(s) ∧ <characteristic properties>`. Used where a property would
  be violated by an existing instance — e.g. INTEGRAL-DOMAIN's `ONE ≠ ZERO`
  is false in the zero ring, so `IS-INTEGRAL-DOMAIN` cannot be shape-only.
  COMMUTATIVE-RING, INTEGRAL-DOMAIN, FIELD, EUCLIDEAN-RING, NORMED-FIELD.

## Hierarchy

```
SEMIGROUP                       carrier A; MUL
└─ MONOID                       + identity E
   ├─ COMM-MONOID               + MUL commutative
   └─ GROUP                     + inverse INV
      └─ ABELIAN-GROUP          + MUL commutative

RING                            carrier A; ADD MUL NEG; ZERO ONE
└─ COMMUTATIVE-RING             + MUL commutative
   └─ INTEGRAL-DOMAIN           + ONE≠ZERO, no zero divisors
      ├─ EUCLIDEAN-RING         + a Euclidean degree function exists
      └─ FIELD                  + every nonzero element is invertible
         └─ NORMED-FIELD        + a norm A→RR exists
   (also: FIELD ⊆ EUCLIDEAN-RING)

METRIC-SPACE                    carrier X; distance D: X×X → RR
```

Relation axioms: `comm-monoid-is-monoid`, `abelian-group-is-group`,
`commutative-ring-is-ring`, `integral-domain-is-commutative-ring`,
`field-is-integral-domain`, `euclidean-ring-is-integral-domain`,
`field-is-euclidean-ring`, `normed-field-is-field`. Each `def-structure`'d
shape predicate also collapses with its parent (e.g. a richer-shape GROUP is
not a structural subtype of MONOID — note there is no `group-is-monoid`).

## Numeric instances

| Domain | Instance | Memberships |
|---|---|---|
| NN | `NN-ADD-MONOID` | COMM-MONOID |
| ZZ | `ZZ-RING` | RING, COMMUTATIVE-RING, INTEGRAL-DOMAIN, EUCLIDEAN-RING |
| QQ | `QQ-RING` | RING, COMMUTATIVE-RING, INTEGRAL-DOMAIN, FIELD |
| RR | `RR-RING` | …, FIELD, NORMED-FIELD |
| CC | `CC-RING` | …, FIELD, NORMED-FIELD; `CC-MS`: METRIC-SPACE |

ZZ is a Euclidean ring (degree = `abs`) but not a field. QQ/RR/CC are fields.
The Euclidean / normed witnesses are existential; for the numeric instances
the actual functions are `abs` (RR) and `magnitude` (CC).

## Functions on RR / CC

- **RR**: `+ * - recip abs <=`; `power(x,n)` for `n ∈ NN`.
- **CC**: `+ * - recip conjugate magnitude` (the modulus, `CC→RR`,
  axiomatized directly — needs no `sqrt`); `power(x,n)` for `n ∈ NN`.
- No `sqrt`; `power` takes only `NN` exponents.

## Matrices

`MATRIX(S)` — the class of matrices over a set `S`: a list of rows, each row
a list of elements of `S`, all rows of equal length. Formally a matrix is an
element of `TUPLES(TUPLES S)` with equilong rows (`matrix-membership`);
`MATRIX(S)` is a set when `S` is (`matrix-sethood`). `SIZE(M)` = `[rows,
columns]` = `[LENGTH M, LENGTH(NTH 1 M)]`. A class-former like `FUN`/`TUPLES`,
not an algebraic structure. `structure-library/matrix.scm`.

## Not yet defined

VECTOR-SPACE (two-sorted: vectors + a scalar field) — deferred.
