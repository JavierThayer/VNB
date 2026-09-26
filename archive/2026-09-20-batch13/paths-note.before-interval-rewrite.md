# Paths in CC and the integral along a path: design note

2026-09-21. It serves section 3.1 of the user's notes (`~/docs/complex-analysis.pdf`). The user
agreed on 2026-09-21 to the four points of section 4 and to the three of section 5. Proven so far:
section 3.1 (`theorem-library/cc-coords-laws.scm`).

## 1. The sources

**The user's notes, 3.1.** The integral of a piecewise continuous CC-valued function on `[a, b]` is
defined componentwise, equation (44): the integral of `f` is the integral of its real part plus `i`
times the integral of its imaginary part. The line integral is introduced as a limit of sums (46)
over pointed partitions, and for a continuously differentiable path it equals the integral of
`f(gamma(t)) gamma'(t)`.

**Dieudonne, Foundations of Modern Analysis** (the user's copy, `~/docs/Dieudonne-ocr.pdf`).

* 8.7: a continuous `g` on an interval `I` is a PRIMITIVE of `f` if there is a denumerable set `D`
  such that `g` is differentiable at every point of `I - D` with `g' = f` there. Two primitives
  differ by a constant (8.7.1); every regulated function has a primitive (8.7.2).
* 9.6: a PATH is a continuous mapping of a compact interval `[a, b]`, not reduced to a point, into
  C; a LOOP is a path with `gamma(a) = gamma(b)`. A ROAD is a path that is a primitive of a
  regulated function; a CIRCUIT is a closed road. The opposite of a road and the juxtaposition of
  two roads are roads. For `f` continuous on the image of a road, the integral of `f` along the
  road is the integral from `a` to `b` of `f(gamma(t)) gamma'(t)`: the integrand is regulated. Two
  roads related by a bijection `phi` of the intervals, with `phi` and its inverse primitives of
  regulated functions, have the same integral (by 8.7.4).

Dieudonne does not use the sums (46); the formula with `gamma'` is his definition.

## 2. What the library has

* `real-part`, `imag-part` (defined through `conjugate`), `cc-re-im-decompose`
  (`z = real-part(z) + 1i * imag-part(z)`), `cc-re-im-of` (uniqueness), `cc-re-sub`, `cc-im-sub`, the
  bounds `cc-abs-re-le-magnitude`, `cc-abs-im-le-magnitude`, `cc-magnitude-le-re-im`, and
  `cc-converges-of-coords`. The correspondence between CC and `cartesian(rr, rr)` is not stated as
  a map.
* The real integral: `C-INT(phi, a, b)` is the value `F(b) - F(a)` for an antiderivative `F`,
  where `IS-ANTIDERIVATIVE(F, phi, a, b)` says: `F` and `phi` are in `FUN(RR, RR)`, `a < b`, `F` is
  continuous at every point of `[a, b]`, and `F` is differentiable with derivative `phi(t)` at EVERY
  `t` with `a < t < b`. There is no exceptional set. About sixty results are stated with it
  (additivity over adjacent intervals, change of variable, `c-int-defined-for-continuous`, the
  oriented integral `C-INT-OR`).
* `IS-PARTITION(p, n, a, b)`, `IS-PIECEWISE-CONTINUOUS(f, a, b)`, `IS-STEP-FN`, `IS-REGULATED(f, a, b)`
  (one-sided limits at every point), all for total functions `FUN(RR, RR)` with the interval as
  parameters.
* Since 2026-09-20: `SUBSPACE-MS`, `RESTRICT`, `IS-DIFF-ON(K, U, f, a, L)` on an OPEN `U`.

Consequence: a polygon, or the boundary of a rectangle, taken as ONE path, has no antiderivative
in the library's sense, because it is not differentiable at its corners.

## 3. Proposal

### 3.1 CC and cartesian(rr, rr)

    CC-COORDS   = the map  z in CC |-> [real-part(z), imag-part(z)]          in FUN(CC, cartesian(RR, RR))
    CC-OF-PAIR  = the map  [a, b] in cartesian(RR, RR) |-> a + b * 1i        in FUN(cartesian(RR, RR), CC)

To prove: the typings; each is the inverse of the other, hence both are bijections; additivity and
compatibility with multiplication by a real number; the two-sided estimate
`max(|re z|, |im z|) <= |z| <= |re z| + |im z|` stated as a comparison of `CC-MS` with the product
metric on `cartesian(RR, RR)`; and the three transfer principles that the rest of the development
uses, each an equivalence: a sequence in CC converges iff both coordinate sequences do; a map into
CC is continuous at a point iff both coordinate maps are; a CC-valued function of a real variable
is differentiable at a point iff both coordinate functions are, the derivative being taken
coordinatewise.

### 3.2 The primitive with a finite exceptional set

    IS-PW-ANTIDERIVATIVE(F, phi, a, b)  iff
        F, phi in FUN(RR, RR),  a < b,  F continuous at every point of [a, b],  and for some
        partition p of [a, b] in n pieces:  for every i < n and every t with p(i) < t < p(i+1),
        IS-DIFF-AT(F, t, phi(t))

This is Dieudonne's primitive with `D` finite: the points of the partition, the two endpoints
among them. No derivative is ever taken at an endpoint, so no one-sided derivative is needed, in
agreement with the decision of 2026-09-20 that the domain of differentiation is open. Two such
primitives of one `phi` differ by a constant on `[a, b]` (the classical mean value theorem on each
piece, and continuity at the partition points). Every `IS-ANTIDERIVATIVE` is an
`IS-PW-ANTIDERIVATIVE` (one piece), so the sixty existing results remain usable.

    PW-INT(phi, a, b) = the v such that for some F:  IS-PW-ANTIDERIVATIVE(F, phi, a, b)  and  v = F(b) - F(a)

defined as `C-INT` is, by IOTA, the uniqueness obligation being the statement above. To prove:
agreement with `C-INT` when `phi` is antiderivable; additivity over adjacent intervals; linearity;
existence for a piecewise continuous `phi` with one-sided limits at the partition points (from
`c-int-defined-for-continuous` on each piece).

### 3.3 The integral of a CC-valued function

For `phi in FUN(RR, CC)`:

    CC-INT(phi, a, b) = PW-INT(re o phi, a, b) + 1i * PW-INT(im o phi, a, b)

which is equation (44) of the notes. To prove: CC-linearity, additivity over adjacent intervals,
and the estimate (45), `|CC-INT(phi, a, b)| <= PW-INT(|phi|, a, b)`, by the argument of the notes.

### 3.4 Paths and roads

    IS-PATH(gamma, a, b)   iff  gamma in FUN(RR, CC),  a < b,  gamma continuous at every point of [a, b]
    IS-ROAD(gamma, dgamma, a, b)  iff  IS-PATH(gamma, a, b),  dgamma in FUN(RR, CC),  the coordinates of
                                       dgamma are piecewise continuous on [a, b] with one-sided limits at
                                       the partition points (decision 5.3),  and each coordinate of gamma is
                                       an IS-PW-ANTIDERIVATIVE of the corresponding coordinate of dgamma
    TRACE(gamma, a, b) = IMAGE(gamma, CCINT(a, b))
    LINE-INT(f, gamma, dgamma, a, b) = CC-INT( t |-> f(gamma(t)) * dgamma(t),  a, b )

A loop is a path with `gamma(a) = gamma(b)`; a circuit is a closed road. To prove: the trace is
compact (Heine-Borel for the interval as a space, proven 2026-09-20, and continuity); the opposite
road and the juxtaposition of two roads are roads, with (9.6.1) and (9.6.2); invariance under an
affine change of parameter first, under Dieudonne's equivalence later if it is needed; the
estimate `|LINE-INT| <= sup|f| * length`; and the first computation, the integral of `1/(z - c)`
along a circle.

## 4. Decided by the user, 2026-09-21

1. The exceptional set is FINITE (a partition), not denumerable.
2. The endpoints of the interval belong to the exceptional set.
3. The integral along a road is Dieudonne's, `f(gamma(t)) gamma'(t)` integrated over `[a, b]`,
   taken componentwise through 3.1. The sums (46) of the notes are not the definition.
4. The names `IS-PATH` (continuous) and `IS-ROAD` (piecewise regulated-differentiable), after
   Dieudonne.

## 5. The three further points -- DECIDED by the user, 2026-09-21

The user accepted the three recommendations below ("I wouldn't have done it that way, but I see
your reasoning and it looks like it will work more easily with the available machinery, so go
with it"). They are choices of convenience with respect to the existing library, not statements
about how the theory ought to be written; the alternatives are recorded so that they can be
revisited.

1. **The domain of a path.** The proposal writes `gamma in FUN(RR, CC)` with the interval as two
   parameters, because that is the convention of the whole real calculus in the library
   (`IS-ANTIDERIVATIVE`, `IS-REGULATED`, `C-INT` and the sixty results about them), and the values of
   `gamma` outside `[a, b]` are never looked at. The alternative is
   `gamma in FUN(CCINT(a, b), CC)`, which is what Dieudonne writes and what `SUBSPACE-MS` now
   allows, at the price of a `RESTRICT` between every path and every existing theorem about
   antiderivatives. Recommendation: the first, total functions with the interval as parameters.
2. **The derivative as a separate argument.** `IS-ROAD(gamma, dgamma, a, b)` names the derivative
   `dgamma` explicitly, as `IS-DIFF-AT(f, a, L)` names `L`, because `gamma'` is not determined at the
   partition points and an IOTA-defined `gamma'` would be undefined there. Recommendation: keep it
   explicit; prove that the line integral does not depend on the choice of `dgamma`.
3. **Regulated or piecewise continuous** for `dgamma`. Regulated is Dieudonne's hypothesis and the
   library has the predicate; existence of the primitive of a regulated function (8.7.2) is NOT
   proven in the library, while existence for a piecewise continuous function follows from
   `c-int-defined-for-continuous`. Recommendation: state `IS-ROAD` with piecewise continuity of
   `dgamma` (with one-sided limits at the partition points); every path of chapters 3 to 10 of the
   notes is of that kind.

## 6. Order of work

1. 3.1 (CC and `cartesian(rr, rr)`): DONE 2026-09-21, 29 theorems; `IS-CC-DIFF-AT(g, a, L)`, the
   coordinatewise derivative of a map RR -> CC, was defined there because no derivative in the
   library fits such a map.
2. 3.2 and 3.3, then 3.4 (batch 14-B).
3. Then section 3.2 of the notes (Cauchy's theorem): read the chapter first and write down which
   form of the theorem the integration layer has to support.
