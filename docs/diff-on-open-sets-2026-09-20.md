# Differentiation on a subset, over a normed field: design note

2026-09-20. DECIDED the same day (section 5). It concerns the first step
towards complex analysis: what "f is differentiable at a" is to mean when f is defined on a
subset U of the real or the complex numbers.

## 1. The problem

The derivative in the library is

    IS-DIFF-AT(f, a, L)  iff  f in FUN(RR, RR), a in RR, L in RR, and for some phi in FUN(RR, RR):
                              phi is continuous at a (RR-MS to RR-MS), phi(a) = L,
                              and for all x in RR:  f(x) - f(a) = phi(x) * (x - a)

(`theorem-library/differentiation.scm:37`, the Caratheodory form of the notes). About fifty
theorems are stated with it: uniqueness, continuity, sum, product, chain rule, power rule, the
inverse rule, Rolle, the mean value theorems, Taylor.

Two things are fixed in that definition and both must move.

* **The function is total on RR.** A member of `FUN(A, B)` is defined exactly on `A`, so "f
  differentiable on an open U" cannot be said. This is the wall recorded in
  `chain-rule.scm`, `inverse-function.scm`, `directional-derivative.scm` and
  `heine-borel-baby.scm`: there is no way to speak of a function, or of continuity, on a subset.
* **The field is RR.** A holomorphic function is a function on an open subset of CC whose
  difference quotient has a limit in CC.

## 2. What the library already has

* `NORMED-FIELD` is a declared structure (`structure-library/normed-field.scm`: carrier, ADD, MUL,
  NEG, ZERO, ONE, and the norm FNRM into RR). `rr-normed-field` and `cc-normed-field` are
  instances, both proven to be normed fields.
* `NF-METRIC-SPACE(K)` is the metric space of a normed field (`normed-field-metric.scm`): its
  points are `CARR(K)`, its distance is `FNRM(x - y)`. `RR-MS` and `CC-MS` are metric spaces,
  and `cc-complete` is proven.
* `IS-CONTINUOUS-AT(s, t, f, a)` is stated for arbitrary metric spaces `s`, `t`
  (`metric-continuity.scm`), with the continuity algebra (sum, product, composition, transfer along
  pointwise equality) proven for `RR-MS`.
* `comm-ring-simplify` decides identities on both surfaces: the numeric `+ * -`, and the
  operations `(ADD R)`, `(MUL R)`, `(NEG R)` of a structure certified to be a commutative ring.
  `ineq` works on real numbers only, which is where norms take their values.
* 79 theorems about `CC` (field laws, conjugation, `magnitude` and its triangle inequalities).

What is missing: a metric on a SUBSET of a metric space, and a restriction operator on functions.

## 3. Proposal

### 3.1 The metric subspace

    SUBSPACE-MS(s, A)    points:   A
                         distance: the distance of s, on CARTESIAN(A, A)

for `A` a subset of `PTS(s)`. To prove: it is a metric space; a set is open in it iff it is the
trace on `A` of an open set of `s`; a map continuous at `a` on `s` restricts to a map continuous at
`a` on `A`; a closed subset of a compact space is compact as a subspace; and, as the first use,
Heine-Borel for a closed interval as a space (Bolzano-Weierstrass is proven since 2026-09-19).

    RESTRICT(f, A) = VNB-LAMBDA x in A. f(x)

with its value law and its typing (`f in FUN(D, B)`, `A` a subset of `D`, gives
`RESTRICT(f, A) in FUN(A, B)`).

### 3.2 The derivative

For a normed field `K`, write `M = NF-METRIC-SPACE(K)` and `+ . -` for the operations of `K`.

    IS-DIFF-ON(K, U, f, a, L)  iff
        IS-NORMED-FIELD(K),  U open in M,  f in FUN(U, CARR(K)),  a in U,  L in CARR(K),
        and for some phi in FUN(U, CARR(K)):
            phi is continuous at a, from SUBSPACE-MS(M, U) to M,
            phi(a) = L,
            for all x in U:  f(x) - f(a) = phi(x) . (x - a)

This is the definition of the notes with two parameters made explicit.  By the user's decision
(section 5) `U` is OPEN in `M`, and the definition says so; the two bullets that follow record what
an arbitrary `U` would have given, and are kept for the record.

* Uniqueness of `L` needs `a` to be a limit point of `U`. It is a hypothesis of the uniqueness
  theorem, not of the definition. Every point of an open subset of RR or CC is a limit point of it.
* Taking `U` a closed interval gives the one-sided derivatives at its endpoints with no further
  definition. The fundamental theorem of calculus wants exactly that.
* `HOLOMORPHIC-ON(U, f)`: `U` is open in `CC-MS` and `f` is differentiable on `U` at every point of `U`,
  with `K = cc-normed-field`.

### 3.3 The real theory stays where it is

Nothing stated with `IS-DIFF-AT` changes. One bridge theorem connects the two:

    IS-DIFF-AT(f, a, L)  iff  IS-DIFF-ON(rr-normed-field, RR, f, a, L)

Its proof is the read-off of the instance's slots (`(ADD rr-normed-field)` is the numeric `+`, and
so on) and the fact that the subspace of a space on all of its points is that space. New results
proven for `IS-DIFF-ON` reach the real line through it; the fifty existing theorems are not
re-proven.

### 3.4 Order of work

1. The subspace and `RESTRICT` (3.1).
2. `IS-DIFF-ON`: uniqueness, differentiable implies continuous, constants and the identity,
   sum, product, the chain rule. Algebra by `comm-ring-simplify` on the operations of `K`; estimates
   on `FNRM` values by `ineq`.
3. The bridge of 3.3, and as a test the LOCAL inverse function theorem on the line.
4. `HOLOMORPHIC-ON`; then power series in CC (radius of convergence, termwise differentiation),
   `exp`; later, integrals of CC-valued functions on an interval, and Cauchy's theorem.

## 4. The alternative, and why it is not proposed

Define the complex derivative separately, with the numeric operations on CC, and port the real
development: about fifteen core theorems, each proof nearly verbatim. It is quick, and every
tool works on the numeric surface at once. It is rejected here because it proves everything twice
and leaves the subset problem unsolved for both copies: "differentiable on an open U" is needed
on the real line as much as in the plane.

## 5. Decisions of the user (2026-09-20)

1. **One derivative, over a normed field.** "A normed field suffices."
2. **`U` is OPEN, by definition.** "U is open usually when considered as domains for functions."
   `IS-DIFF-ON(K, U, f, a, L)` therefore carries `IS-OPEN(NF-METRIC-SPACE(K), U)` among its
   conjuncts. Every point of `U` is then a limit point of `U` (for RR and CC; in general for a normed
   field whose norm is not trivial), so uniqueness of the derivative needs no extra hypothesis
   beyond that. One-sided derivatives at the endpoints of a closed interval are NOT instances of
   this definition; if the fundamental theorem of calculus wants them, they get a definition of
   their own at that time.
3. **Names.** The new symbols are `SUBSPACE-MS(s, A)` and `RESTRICT(f, A)` (defined 2026-09-20 in
   `structure-library/metric-subspace.scm`), `IS-DIFF-ON(K, U, f, a, L)`, `DERIV-ON(K, U, f, a)` and
   `HOLOMORPHIC-ON(U, f)`. They stand unless the user prefers others.
4. **Nothing in the real theory changes.** `IS-DIFF-AT` and the fifty theorems stated with it stay
   as they are. The bridge theorem of 3.3 is an additional theorem; it is how a result proven for
   `IS-DIFF-ON` is used on the real line, and it changes no existing statement.
