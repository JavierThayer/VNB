# Roads as primitives of regulated functions (decided by the user, 2026-09-23)

## The decision

A road is what Dieudonne says it is (*Foundations of Modern Analysis*, IX.6): a path that is a
PRIMITIVE of a REGULATED function. A primitive (VIII.7) of f on an interval I is a continuous g
such that g'(t) = f(t) for every t outside a DENUMERABLE set D. A regulated function (VII.6) has
one-sided limits at every point; on a compact interval it is exactly a uniform limit of step
functions (7.6.1). No finiteness clause appears anywhere, and none is needed.

Why the change. The path-integral layer of 2026-09-21/22 used a FINITE exceptional set and a
predicate `IS-PW-CONTINUOUS-ON` meaning "continuous off a finite set". Under that predicate
Dieudonne's 8.7.2 (a regulated function has a primitive) is false: phi(t) = 1/(t - c) off c,
phi(c) = 0, is continuous off {c} and has no continuous primitive on [a, b]. The user's notes
defined a path as "continuously differentiable except at finitely many points", which admits
gamma(t) = t^2 sin(1/t), whose derivative exists everywhere and has no one-sided limit at 0. The
user will rewrite the notes' definition; the library follows Dieudonne.

## The definitions (structure-library/regulated-primitive.scm, batch 20-D)

* `IS-COUNTABLE(D)`: D is a set, and D is empty or the image of a function on NN
  (`e in FUN(NN, D)`, every point of D is some `e(n)`). Finite sets are countable
  (`finite-implies-countable`, from `card-finite-bij`).
* `IS-RIGHT-LIMIT-WITHIN(f, W, x, l)` and `IS-LEFT-LIMIT-WITHIN(f, W, x, l)`: the one-sided limit
  of a function given ONLY on the set W, at a point x that need not lie in W: for every eps > 0
  some delta > 0 has |f(t) - l| < eps for all t in W with x < t < x + delta (resp. x - delta < t
  < x). The tree had no limit of a function on a set (16-D's finding); this is the first.
* `IS-REGULATED-ON(f, a, b)`: a < b reals, `f in FUN(CCINT(a, b), RR)`, a right limit within
  CCINT(a, b) at every x < b and a left limit at every x > a. (The 2026-09-08 `IS-REGULATED` is
  the same for a TOTAL f and stays for its own theorems.)
* `IS-PRIMITIVE(g, f, a, b)`: a < b reals, g and f in `FUN(CCINT(a, b), RR)`, g continuous on
  CCINT(a, b) (`IS-CONTINUOUS-ON`), and a countable D subset CCINT(a, b) with
  `HAS-DERIV-AT(g, t, f(t))` for every t in OOINT(a, b) outside D. This is `IS-PW-ANTIDERIVATIVE`
  with "countable" for "card in NN" (`pw-antiderivative-implies-primitive`).
* Complex values are taken COORDINATEWISE, as the path-integral file already does.

Then, in `structure-library/path-integral.scm` (integrator, wave 2): `IS-ROAD(gamma, dgamma, a, b)`
= `IS-PATH(gamma, a, b)`, `dgamma in FUN(CCINT(a, b), CC)`, re and im of dgamma `IS-REGULATED-ON`,
re and im of gamma `IS-PRIMITIVE` of re and im of dgamma. `PW-INT(f, a, b)` = g(b) - g(a) for a
primitive g (IOTA), `CC-INT` and `LINE-INT` unchanged in form. The names stay; `PW-` no longer
means piecewise and may be renamed later with `rename-sym.py`.

## The theorems

1. **Constancy off a countable set** (batch 20-A): g continuous on CCINT(a, b), D countable, D
   subset CCINT(a, b), `HAS-DERIV-AT(g, t, 0)` for t in OOINT(a, b) outside D; then g(s) = g(t)
   for all s, t in CCINT(a, b). Dieudonne's remark after (8.6.1), through (8.5.2) / (8.5.3): the
   mean value inequality with a denumerable exceptional set, proved with an enumeration of D
   and the weights 2^-n against a least upper bound. The finite version is
   `pw-zero-deriv-off-finite-set` (finite-set induction) and stays as its special case.
2. **Uniqueness of the primitive** (8.7.1), from 1: two primitives of f differ by a constant, so
   `PW-INT` is well defined (`pw-int-value` unconditional again).
3. **Existence** (8.7.2): a regulated function on [a, b] has a primitive. Step functions have
   piecewise affine primitives (`pw-affine-antiderivative`); a regulated function is a uniform
   limit of step functions (7.6.1; `uniform-limit-of-regulated` is the converse direction, check);
   primitives pass to uniform limits (`antiderivable-uniform-limit`, stated for total functions:
   bridge through EXTEND-CONST). With it every line-integral statement of batches 17-19 loses
   its "primitives of the integrand's coordinates" hypotheses.
4. **Restatement** of batches 16-19 over the new predicates (wave 2): every finite exceptional
   set becomes a countable one; `finite-implies-countable` makes the old proofs' witnesses
   acceptable. The trace of a road is compact and a road is continuous as before.

## What is NOT decided here

The names (`PW-INT` etc.); whether `IS-REGULATED` (total) is retired once `IS-REGULATED-ON`
carries its theorems; Dieudonne's equivalent roads and change of variable (9.6, needs the
generalised reflection of 18-C).
