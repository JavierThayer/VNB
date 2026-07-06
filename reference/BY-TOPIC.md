# Theorems by topic

The library grouped by subject, like a textbook table of contents.  Each entry gives its statement and a link to the .scm file with its proof.  (The flat catalog is `THEOREMS.md`.)

## Calculus basics

### Vocabulary

- `is-diff-at` — forall([f, a, l], is-diff-at(f, a, l) iff f in fun(rr, rr) and a in rr and l in rr and forsome([phi in fun(rr, rr)], is-continuous-at(rr-ms, rr-ms, phi, a) and phi(a) = l and forall([x in rr], f(x) - f(a) = phi(x) * (x - a))))  see [~/prover/theorem-library/differentiation.scm](../theorem-library/differentiation.scm)
- `deriv` — _(definition / vocabulary)_
- `nth-deriv` — _(definition / vocabulary)_
- `little-o-at` — forall([g, a], little-o-at(g, a) iff g in fun(rr, rr) and a in rr and forsome([eps in fun(rr, rr)], is-continuous-at(rr-ms, rr-ms, eps, a) and eps(a) = 0 and forall([x in rr], g(x) = eps(x) * (x - a))))  see [~/prover/theorem-library/little-o.scm](../theorem-library/little-o.scm)
- `taylor-poly` — _(definition / vocabulary)_
- `taylor-differentiable` — forall([f, a, x, n], taylor-differentiable(f, a, x, n) iff forall([k], k in nn and k <= n implies forall([t in ccint(a, x)], is-continuous-at(rr-ms, rr-ms, nth-deriv(f, k), t))) and forall([k], k in nn and k <= n implies forall([t], a < t and t < x implies is-diff-at(nth-deriv(f, k), t, (nth-deriv(f, succ(k)))(t)))))  see [~/prover/theorem-library/taylor-proof.scm](../theorem-library/taylor-proof.scm)

### Differentiation rules

- `derivative-unique` — forall([f, a, l, m], is-diff-at(f, a, l) and is-diff-at(f, a, m) implies l = m)  see [~/prover/theorem-library/differentiation.scm](../theorem-library/differentiation.scm)
- `diff-implies-continuous` — forall([f, a, l], is-diff-at(f, a, l) implies is-continuous-at(rr-ms, rr-ms, f, a))  see [~/prover/theorem-library/differentiation.scm](../theorem-library/differentiation.scm)
- `deriv-const` — forall([c, a], c in rr and a in rr implies is-diff-at(vnb-lambda(x, c), a, 0))  see [~/prover/theorem-library/differentiation.scm](../theorem-library/differentiation.scm)
- `deriv-identity` — forall([a in rr], is-diff-at(vnb-lambda(x, x), a, 1))  see [~/prover/theorem-library/differentiation.scm](../theorem-library/differentiation.scm)
- `deriv-sum` — forall([f, g, a, l, m], is-diff-at(f, a, l) and is-diff-at(g, a, m) implies is-diff-at(vnb-lambda(x, f(x) + g(x)), a, l + m))  _[warrant: reference]_  see [~/prover/theorem-library/differentiation.scm](../theorem-library/differentiation.scm)
- `deriv-product` — forall([f, g, a, l, m], is-diff-at(f, a, l) and is-diff-at(g, a, m) implies is-diff-at(vnb-lambda(x, f(x) * g(x)), a, l * g(a) + f(a) * m))  _[warrant: reference]_  see [~/prover/theorem-library/differentiation.scm](../theorem-library/differentiation.scm)
- `deriv-chain` — forall([f, g, a, l, m], is-diff-at(f, a, l) implies is-diff-at(g, f(a), m) implies is-diff-at(compose(g, f), a, m * l))  _[warrant: reference]_  see [~/prover/theorem-library/differentiation.scm](../theorem-library/differentiation.scm)
- `deriv-neg` — forall([f, a, l], is-diff-at(f, a, l) implies is-diff-at(vnb-lambda(z, -f(z)), a, -l))  _[warrant: reference]_  see [~/prover/theorem-library/differentiation.scm](../theorem-library/differentiation.scm)
- `nth-deriv-one` — forall([f], nth-deriv(f, 1) == vnb-lambda(x, deriv(f, x)))  see [~/prover/theorem-library/higher-derivatives.scm](../theorem-library/higher-derivatives.scm)

### Little-o calculus

- `diff-iff-little-o` — forall([f, a, l], is-diff-at(f, a, l) iff f in fun(rr, rr) and a in rr and l in rr and little-o-at(vnb-lambda(x, f(x) - f(a) - l * (x - a)), a))  _[warrant: reference]_  see [~/prover/theorem-library/little-o.scm](../theorem-library/little-o.scm)
- `little-o-sum` — forall([g, h, a], little-o-at(g, a) implies little-o-at(h, a) implies little-o-at(vnb-lambda(x, g(x) + h(x)), a))  _[warrant: well-known]_  see [~/prover/theorem-library/little-o.scm](../theorem-library/little-o.scm)
- `little-o-scalar` — forall([c, g, a], c in rr implies little-o-at(g, a) implies little-o-at(vnb-lambda(x, c * g(x)), a))  _[warrant: well-known]_  see [~/prover/theorem-library/little-o.scm](../theorem-library/little-o.scm)

### Extreme & interior values (Fermat)

- `extreme-value-max` — forall([f, a, b], f in fun(rr, rr) and a in rr and b in rr and a <= b implies forall([x in ccint(a, b)], is-continuous-at(rr-ms, rr-ms, f, x)) implies forsome([c in ccint(a, b)], forall([x in ccint(a, b)], f(x) <= f(c))))  _[warrant: reference]_  see [~/prover/theorem-library/extreme-value.scm](../theorem-library/extreme-value.scm)
- `extreme-value-min` — forall([f, a, b], f in fun(rr, rr) and a in rr and b in rr and a <= b implies forall([x in ccint(a, b)], is-continuous-at(rr-ms, rr-ms, f, x)) implies forsome([c in ccint(a, b)], forall([x in ccint(a, b)], f(c) <= f(x))))  _[warrant: reference]_  see [~/prover/theorem-library/extreme-value.scm](../theorem-library/extreme-value.scm)
- `interior-max-deriv-zero` — forall([f, a, b, theta, l], f in fun(rr, rr) and a in rr and b in rr and theta in rr and a < theta and theta < b implies forall([x in ccint(a, b)], f(x) <= f(theta)) implies is-diff-at(f, theta, l) implies l = 0)  see [~/prover/theorem-library/interior-extremum-proof.scm](../theorem-library/interior-extremum-proof.scm)
- `interior-min-deriv-zero` — forall([f, a, b, theta, l], f in fun(rr, rr) and a in rr and b in rr and theta in rr and a < theta and theta < b implies forall([x in ccint(a, b)], f(theta) <= f(x)) implies is-diff-at(f, theta, l) implies l = 0)  see [~/prover/theorem-library/interior-extremum-proof.scm](../theorem-library/interior-extremum-proof.scm)

### Mean value theorems

- `rolle` — forall([h, a, b], h in fun(rr, rr) and a in rr and b in rr and a < b implies forall([x in ccint(a, b)], is-continuous-at(rr-ms, rr-ms, h, x)) implies forall([x], a < x and x < b implies forsome([l], is-diff-at(h, x, l))) implies h(a) = h(b) implies forsome([theta], a < theta and theta < b and is-diff-at(h, theta, 0)))  see [~/prover/theorem-library/rolle-proof.scm](../theorem-library/rolle-proof.scm)
- `mvt` — forall([f, a, b], f in fun(rr, rr) and a in rr and b in rr and a < b implies forall([x in ccint(a, b)], is-continuous-at(rr-ms, rr-ms, f, x)) implies forall([x], a < x and x < b implies forsome([l], is-diff-at(f, x, l))) implies forsome([theta], a < theta and theta < b and forsome([l], is-diff-at(f, theta, l) and l * (b - a) = f(b) - f(a))))  see [~/prover/theorem-library/mvt-proof.scm](../theorem-library/mvt-proof.scm)
- `generalized-mvt` — forall([f, g, a, b], f in fun(rr, rr) and g in fun(rr, rr) and a in rr and b in rr and a < b implies forall([x in ccint(a, b)], is-continuous-at(rr-ms, rr-ms, f, x) and is-continuous-at(rr-ms, rr-ms, g, x)) implies forall([x], a < x and x < b implies forsome([l], is-diff-at(f, x, l)) and forsome([m], is-diff-at(g, x, m))) implies forsome([theta], a < theta and theta < b and forsome([l, m], is-diff-at(f, theta, l) and is-diff-at(g, theta, m) and l * (g(b) - g(a)) = m * (f(b) - f(a)))))  see [~/prover/theorem-library/generalized-mvt-proof.scm](../theorem-library/generalized-mvt-proof.scm)

### Consequences of the mean value theorem

- `deriv-zero-implies-constant` — forall([f, a, b], f in fun(rr, rr) and a in rr and b in rr and a < b implies forall([x in ccint(a, b)], is-continuous-at(rr-ms, rr-ms, f, x)) implies forall([x], a < x and x < b implies is-diff-at(f, x, 0)) implies forall([u, v], u in ccint(a, b) and v in ccint(a, b) implies f(u) = f(v)))  see [~/prover/theorem-library/deriv-constant-proof.scm](../theorem-library/deriv-constant-proof.scm)
- `mvt-upper-bound` — forall([f, a, b, m], f in fun(rr, rr) and a in rr and b in rr and m in rr and a < b implies forall([x in ccint(a, b)], is-continuous-at(rr-ms, rr-ms, f, x)) implies forall([x], a < x and x < b implies forsome([l], is-diff-at(f, x, l) and l <= m)) implies f(b) - f(a) <= m * (b - a))  see [~/prover/theorem-library/mvt-bounds-proof.scm](../theorem-library/mvt-bounds-proof.scm)
- `mvt-lower-bound` — forall([f, a, b, m], f in fun(rr, rr) and a in rr and b in rr and m in rr and a < b implies forall([x in ccint(a, b)], is-continuous-at(rr-ms, rr-ms, f, x)) implies forall([x], a < x and x < b implies forsome([l], is-diff-at(f, x, l) and m <= l)) implies m * (b - a) <= f(b) - f(a))  see [~/prover/theorem-library/mvt-bounds-proof.scm](../theorem-library/mvt-bounds-proof.scm)
- `deriv-pos-strictly-increasing` — forall([f, a, b], f in fun(rr, rr) and a in rr and b in rr and a < b implies forall([x in ccint(a, b)], is-continuous-at(rr-ms, rr-ms, f, x)) implies forall([x], a < x and x < b implies forsome([l], is-diff-at(f, x, l) and 0 < l)) implies forall([u, v], u in ccint(a, b) and v in ccint(a, b) and u < v implies f(u) < f(v)))  see [~/prover/theorem-library/deriv-monotone-proof.scm](../theorem-library/deriv-monotone-proof.scm)

### Taylor's theorem

- `taylor-poly-at-center` — forall([f, x, n in nn], taylor-poly(f, x, n, x) = f(x))  _[warrant: reference]_  see [~/prover/theorem-library/taylor-proof.scm](../theorem-library/taylor-proof.scm)
- `taylor-lagrange` — forall([f, a, x, n], f in fun(rr, rr) and a in rr and x in rr and n in nn and a < x implies taylor-differentiable(f, a, x, n) implies forsome([theta], a < theta and theta < x and factorial(succ(n)) * (f(x) - taylor-poly(f, a, n, x)) = (nth-deriv(f, succ(n)))(theta) * (x - a) ^ succ(n)))  see [~/prover/theorem-library/taylor-proof.scm](../theorem-library/taylor-proof.scm)

## Vector calculus

### Vocabulary

- `is-vector-space` — forall([m], is-vector-space(m) iff is-module(m) and is-field(scal(m)))  see [~/prover/structure-library/finite-dimensional.scm](../structure-library/finite-dimensional.scm)
- `is-submodule` — forall([m, s], is-submodule(m, s) iff s subset vec(m) and vzero(m) in s and forall([x_ in s, y_ in s], (vadd(m))(x_, y_) in s) and forall([x_ in s], (vneg(m))(x_) in s) and forall([r_ in carr(scal(m)), x_ in s], (act(m))(r_, x_) in s))  see [~/prover/structure-library/finite-dimensional.scm](../structure-library/finite-dimensional.scm)
- `is-subspace` — forall([m, s], is-subspace(m, s) iff is-submodule(m, s))  see [~/prover/structure-library/finite-dimensional.scm](../structure-library/finite-dimensional.scm)
- `is-noetherian` — forall([m], is-noetherian(m) iff is-module(m) and forall([f_ in fun(nn, power(vec(m)))], forall([n_ in nn], is-submodule(m, f_(n_))) and forall([n_ in nn], f_(n_) subset f_(succ(n_))) implies forsome([k_ in nn], forall([n_], n_ in nn and k_ <= n_ implies f_(n_) = f_(k_)))))  see [~/prover/structure-library/finite-dimensional.scm](../structure-library/finite-dimensional.scm)
- `is-finite-dimensional` — forall([m], is-finite-dimensional(m) iff is-vector-space(m) and is-noetherian(m))  see [~/prover/structure-library/finite-dimensional.scm](../structure-library/finite-dimensional.scm)
- `span-add-one` — _(definition / vocabulary)_
- `is-normed-vector-space` — forall([m], is-normed-vector-space(m) iff length(m) = 7 and scal(m) = rr-ring and vec(m) in set and vadd(m) in fun(cartesian(vec(m), vec(m)), vec(m)) and vzero(m) in vec(m) and vneg(m) in fun(vec(m), vec(m)) and act(m) in fun(cartesian(carr(scal(m)), vec(m)), vec(m)) and vnrm(m) in fun(vec(m), rr) and is-associative(vadd(m), vec(m)) and is-commutative(vadd(m), vec(m)) and is-identity(vadd(m), vzero(m), vec(m)) and has-inverses(vadd(m), vzero(m), vneg(m), vec(m)) and forall([r_ in carr(scal(m)), x_ in vec(m), y_ in vec(m)], (act(m))(r_, (vadd(m))(x_, y_)) = (vadd(m))((act(m))(r_, x_), (act(m))(r_, y_))) and forall([r_ in carr(scal(m)), s_ in carr(scal(m)), x_ in vec(m)], (act(m))((add(scal(m)))(r_, s_), x_) = (vadd(m))((act(m))(r_, x_), (act(m))(s_, x_))) and forall([r_ in carr(scal(m)), s_ in carr(scal(m)), x_ in vec(m)], (act(m))((mul(scal(m)))(r_, s_), x_) = (act(m))(r_, (act(m))(s_, x_))) and forall([x_ in vec(m)], (act(m))(one(scal(m)), x_) = x_) and forall([x_ in vec(m)], 0 <= (vnrm(m))(x_)) and forall([x_ in vec(m)], (vnrm(m))(x_) = 0 iff x_ = vzero(m)) and forall([r_ in carr(scal(m)), x_ in vec(m)], (vnrm(m))((act(m))(r_, x_)) = abs(r_) * (vnrm(m))(x_)) and forall([x_ in vec(m), y_ in vec(m)], (vnrm(m))((vadd(m))(x_, y_)) <= (vnrm(m))(x_) + (vnrm(m))(y_)))  see [~/prover/structure-library/normed-vector-space.scm](../structure-library/normed-vector-space.scm)
- `is-linear-functional` — forall([m, f], is-linear-functional(m, f) iff f in fun(vec(m), rr) and forall([x_ in vec(m), y_ in vec(m)], f((vadd(m))(x_, y_)) = f(x_) + f(y_)) and forall([r_ in rr, x_ in vec(m)], f((act(m))(r_, x_)) = r_ * f(x_)))  see [~/prover/structure-library/linear-functional.scm](../structure-library/linear-functional.scm)
- `is-linear-functional-on` — forall([m, s, f], is-linear-functional-on(m, s, f) iff f in fun(s, rr) and forall([x_ in s, y_ in s], f((vadd(m))(x_, y_)) = f(x_) + f(y_)) and forall([r_ in rr, x_ in s], f((act(m))(r_, x_)) = r_ * f(x_)))  see [~/prover/structure-library/linear-functional.scm](../structure-library/linear-functional.scm)
- `is-bounded-linear-functional` — forall([m, f], is-bounded-linear-functional(m, f) iff is-linear-functional(m, f) and forsome([c_ in rr], 0 <= c_ and forall([x_ in vec(m)], abs(f(x_)) <= c_ * (vnrm(m))(x_))))  see [~/prover/structure-library/linear-functional.scm](../structure-library/linear-functional.scm)
- `is-bounded-linear-functional-on` — forall([m, s, f], is-bounded-linear-functional-on(m, s, f) iff is-linear-functional-on(m, s, f) and forsome([c_ in rr], 0 <= c_ and forall([x_ in s], abs(f(x_)) <= c_ * (vnrm(m))(x_))))  see [~/prover/structure-library/linear-functional.scm](../structure-library/linear-functional.scm)
- `dual-norm` — _(definition / vocabulary)_
- `dual-norm-on` — _(definition / vocabulary)_
- `extends-on` — forall([s, g, f], extends-on(s, g, f) iff forall([x_ in s], g(x_) = f(x_)))  see [~/prover/structure-library/linear-functional.scm](../structure-library/linear-functional.scm)
- `npe` — forall([m, s, f, t, g], npe(m, s, f, t, g) iff is-submodule(m, t) and s subset t and is-linear-functional-on(m, t, g) and extends-on(s, g, f) and forall([w_ in t], abs(g(w_)) <= dual-norm-on(m, s, f) * (vnrm(m))(w_)))  see [~/prover/theorem-library/noetherian-maximal-proof.scm](../theorem-library/noetherian-maximal-proof.scm)
- `good-sub` — forall([m, s, f, t], good-sub(m, s, f, t) iff forsome([g_], npe(m, s, f, t, g_)))  see [~/prover/theorem-library/noetherian-maximal-proof.scm](../theorem-library/noetherian-maximal-proof.scm)
- `line` — _(definition / vocabulary)_
- `nvs-metric-space` — _(definition / vocabulary)_
- `is-diff-at-v` — forall([m, f, a, l], is-diff-at-v(m, f, a, l) iff is-normed-vector-space(m) and f in fun(rr, vec(m)) and a in rr and l in vec(m) and forsome([phi in fun(rr, vec(m))], is-continuous-at(rr-ms, nvs-metric-space(m), phi, a) and phi(a) = l and forall([x_ in rr], (vadd(m))(f(x_), (vneg(m))(f(a))) = (act(m))(x_ - a, phi(x_)))))  see [~/prover/theorem-library/vector-taylor-proof.scm](../theorem-library/vector-taylor-proof.scm)
- `deriv-v` — _(definition / vocabulary)_
- `nth-deriv-v` — _(definition / vocabulary)_
- `taylor-poly-v` — _(definition / vocabulary)_
- `taylor-differentiable-v` — forall([m, f, a, x, n], taylor-differentiable-v(m, f, a, x, n) iff forall([k], k in nn and k <= n implies forall([t in ccint(a, x)], is-continuous-at(rr-ms, nvs-metric-space(m), nth-deriv-v(m, f, k), t))) and forall([k], k in nn and k <= n implies forall([t], a < t and t < x implies is-diff-at-v(m, nth-deriv-v(m, f, k), t, (nth-deriv-v(m, f, succ(k)))(t)))))  see [~/prover/theorem-library/vector-taylor-proof.scm](../theorem-library/vector-taylor-proof.scm)

### Finite-dimensional spaces (noetherian / ascending chain condition)

- `noetherian-set-has-maximal` — forall([m], is-noetherian(m) implies forall([sig in set], sig subset power(vec(m)) implies forall([t in sig], is-submodule(m, t)) implies forsome([t0], t0 in sig) implies forsome([t in sig], forall([u], u in sig and t subset u implies t = u))))  see [~/prover/theorem-library/noetherian-maximal-proof.scm](../theorem-library/noetherian-maximal-proof.scm)
- `hb-good-has-maximal` — forall([m, s, f], is-finite-dimensional(m) implies is-submodule(m, s) implies is-bounded-linear-functional-on(m, s, f) implies forsome([t], good-sub(m, s, f, t) and forall([u], good-sub(m, s, f, u) and t subset u implies t = u)))  see [~/prover/theorem-library/noetherian-maximal-proof.scm](../theorem-library/noetherian-maximal-proof.scm)

### Hahn-Banach extension

- `hahn-banach-extend-one` — forall([m, s, f, v], is-normed-vector-space(m) and is-submodule(m, s) and is-bounded-linear-functional-on(m, s, f) and v in vec(m) and not(v in s) implies forsome([g_], is-linear-functional-on(m, span-add-one(m, s, v), g_) and extends-on(s, g_, f) and forall([w_ in span-add-one(m, s, v)], abs(g_(w_)) <= dual-norm-on(m, s, f) * (vnrm(m))(w_))))  see [~/prover/theorem-library/hahn-banach-proof.scm](../theorem-library/hahn-banach-proof.scm)
- `good-step` — forall([m, s, f, t, x], is-normed-vector-space(m) and is-bounded-linear-functional-on(m, s, f) and good-sub(m, s, f, t) and x in vec(m) and not(x in t) implies good-sub(m, s, f, span-add-one(m, t, x)))  see [~/prover/theorem-library/hahn-banach-full-proof.scm](../theorem-library/hahn-banach-full-proof.scm)
- `hahn-banach` — forall([m, s, f], is-normed-vector-space(m) and is-finite-dimensional(m) and is-submodule(m, s) and is-bounded-linear-functional-on(m, s, f) implies forsome([g_], is-linear-functional-on(m, vec(m), g_) and extends-on(s, g_, f) and forall([w_ in vec(m)], abs(g_(w_)) <= dual-norm-on(m, s, f) * (vnrm(m))(w_))))  see [~/prover/theorem-library/hahn-banach-full-proof.scm](../theorem-library/hahn-banach-full-proof.scm)

### The norm as a supremum of functionals

- `norm-bounded-by-functionals` — forall([m, f, x], is-normed-vector-space(m) and is-bounded-linear-functional(m, f) and x in vec(m) and dual-norm(m, f) <= 1 implies abs(f(x)) <= (vnrm(m))(x))  see [~/prover/theorem-library/norm-as-sup-proof.scm](../theorem-library/norm-as-sup-proof.scm)
- `norm-attained-by-functional` — forall([m, x], is-normed-vector-space(m) and is-finite-dimensional(m) and x in vec(m) implies forsome([g], is-bounded-linear-functional(m, g) and dual-norm(m, g) <= 1 and g(x) = (vnrm(m))(x)))  see [~/prover/theorem-library/norm-as-sup-proof.scm](../theorem-library/norm-as-sup-proof.scm)
- `norm-as-sup` — forall([m, x], is-normed-vector-space(m) and is-finite-dimensional(m) and x in vec(m) implies forall([f], is-bounded-linear-functional(m, f) implies dual-norm(m, f) <= 1 implies abs(f(x)) <= (vnrm(m))(x)) and forall([d], d in rr and forall([f], is-bounded-linear-functional(m, f) implies dual-norm(m, f) <= 1 implies abs(f(x)) <= d) implies (vnrm(m))(x) <= d))  see [~/prover/theorem-library/norm-as-sup-proof.scm](../theorem-library/norm-as-sup-proof.scm)

### Vector-valued Taylor (remainder-norm bound, reduced to scalar)

- `vector-taylor-remainder-bound` — forall([m, f, a, x, n], is-normed-vector-space(m) and is-finite-dimensional(m) and f in fun(rr, vec(m)) and a in rr and x in rr and n in nn and a < x implies taylor-differentiable-v(m, f, a, x, n) implies forsome([theta], a < theta and theta < x and factorial(succ(n)) * (vnrm(m))((vadd(m))(f(x), (vneg(m))(taylor-poly-v(m, f, a, x, n)))) <= (vnrm(m))((nth-deriv-v(m, f, succ(n)))(theta)) * (x - a) ^ succ(n)))  see [~/prover/theorem-library/vector-taylor-proof.scm](../theorem-library/vector-taylor-proof.scm)

## Linear algebra

### Vocabulary

- `mat` — _(definition / vocabulary)_
- `entry` — _(definition / vocabulary)_
- `matof` — _(definition / vocabulary)_
- `matmul` — _(definition / vocabulary)_
- `identmat` — _(definition / vocabulary)_
- `zeromat` — _(definition / vocabulary)_
- `matadd` — _(definition / vocabulary)_
- `matneg` — _(definition / vocabulary)_
- `mat-ring` — _(definition / vocabulary)_
- `matunit` — _(definition / vocabulary)_
- `elem-f` — _(definition / vocabulary)_
- `elem-g` — _(definition / vocabulary)_
- `elem-h` — _(definition / vocabulary)_
- `interval` — _(definition / vocabulary)_

### The matrix ring

- `matmul-assoc` — forall([a], is-ring(a) implies forall([m, n, k, l, p, q, r], p in mat(m, n, carr(a)) implies q in mat(n, k, carr(a)) implies r in mat(k, l, carr(a)) implies matmul(a, matmul(a, p, q), r) = matmul(a, p, matmul(a, q, r))))  see [~/prover/theorem-library/matmul-assoc-proof.scm](../theorem-library/matmul-assoc-proof.scm)
- `mat-ring-is-ring` — forall([a], is-ring(a) implies forall([n in nn], is-ring(mat-ring(a, n))))  see [~/prover/theorem-library/mat-ring-proof.scm](../theorem-library/mat-ring-proof.scm)

### The matrix unit and its column shift (Lemma 3.3)

- `matunit-col-shift` — forall([a], is-ring(a) implies forall([m, n, p, k, l], p in mat(m, n, carr(a)) implies k in interval(1, n) implies l in interval(1, n) implies forall([i in interval(1, m), c in interval(1, n)], entry(matmul(a, p, matunit(a, n, k, l)), i, c) = if(c = l, entry(p, i, k), zero(a)))))  see [~/prover/theorem-library/matunit-shift-proof.scm](../theorem-library/matunit-shift-proof.scm)

### Elementary column operations (Prop 3.5)

- `elem-f-action` — forall([a], is-ring(a) implies forall([m, n, p, k, l], p in mat(m, n, carr(a)) implies k in interval(1, n) implies l in interval(1, n) implies not(k = l) implies forall([i in interval(1, m), c in interval(1, n)], entry(matmul(a, p, elem-f(a, n, k, l)), i, c) = if(c = k, entry(p, i, l), if(c = l, entry(p, i, k), entry(p, i, c))))))  see [~/prover/theorem-library/elem-actions-proof.scm](../theorem-library/elem-actions-proof.scm)
- `elem-g-action` — forall([a], is-ring(a) implies forall([m, n, p, r, k, l], p in mat(m, n, carr(a)) implies r in carr(a) implies k in interval(1, n) implies l in interval(1, n) implies not(k = l) implies forall([i in interval(1, m), c in interval(1, n)], entry(matmul(a, p, elem-g(a, n, r, k, l)), i, c) = if(c = l, (add(a))(entry(p, i, l), (mul(a))(entry(p, i, k), r)), entry(p, i, c)))))  see [~/prover/theorem-library/elem-actions-proof.scm](../theorem-library/elem-actions-proof.scm)
- `elem-h-action` — forall([a], is-ring(a) implies forall([m, n, p, r, k], p in mat(m, n, carr(a)) implies r in carr(a) implies k in interval(1, n) implies forall([i in interval(1, m), c in interval(1, n)], entry(matmul(a, p, elem-h(a, n, r, k)), i, c) = if(c = k, (mul(a))(entry(p, i, k), r), entry(p, i, c)))))  see [~/prover/theorem-library/elem-actions-proof.scm](../theorem-library/elem-actions-proof.scm)

### Elementary inverses (Cor 3.6)

- `elem-f-inverse` — forall([a], is-ring(a) implies forall([n, k, l], k in interval(1, n) implies l in interval(1, n) implies not(k = l) implies matmul(a, elem-f(a, n, k, l), elem-f(a, n, l, k)) = identmat(a, n)))  see [~/prover/theorem-library/elem-inverses-proof.scm](../theorem-library/elem-inverses-proof.scm)
- `elem-g-inverse` — forall([a], is-ring(a) implies forall([n, r, k, l], r in carr(a) implies k in interval(1, n) implies l in interval(1, n) implies not(k = l) implies matmul(a, elem-g(a, n, r, k, l), elem-g(a, n, (neg(a))(r), k, l)) = identmat(a, n)))  see [~/prover/theorem-library/elem-inverses-proof.scm](../theorem-library/elem-inverses-proof.scm)
- `elem-h-inverse` — forall([a], is-ring(a) implies forall([n, r, s, k], r in carr(a) implies s in carr(a) implies (mul(a))(r, s) = one(a) implies k in interval(1, n) implies matmul(a, elem-h(a, n, r, k), elem-h(a, n, s, k)) = identmat(a, n)))  see [~/prover/theorem-library/elem-inverses-proof.scm](../theorem-library/elem-inverses-proof.scm)

### The binomial theorem

- `sum-expansion` — forall([n in nn, r], is-commutative-ring(r) implies forall([x in carr(r), y in carr(r), g in fun(zz, carr(r))], sum(r, vnb-lambda(k, (add(r))((mul(r))(x, g(k - 1)), (mul(r))(y, g(k)))), succ(n)) = (add(r))((add(r))((mul(r))((add(r))(x, y), sum(r, g, n)), (mul(r))(x, g(0 - 1))), (mul(r))(y, g(n)))))  see [~/prover/theorem-library/binomial-proof.scm](../theorem-library/binomial-proof.scm)
- `binomial-theorem` — forall([n in nn, r], is-commutative-ring(r) implies forall([x in carr(r), y in carr(r)], ring-power(r, (add(r))(x, y), n) = sum(r, comb-kk(r, x, y, n), succ(n))))  see [~/prover/theorem-library/binomial-proof.scm](../theorem-library/binomial-proof.scm)

## Combinatorial

### Vocabulary

- `inf-subsets` — _(definition / vocabulary)_
- `is-finite-cover` — forall([c, a], is-finite-cover(c, a) iff c in set and card(c) in nn and a subset big-union(u, c, u))  see [~/prover/theorem-library/block-family-combinatorial.scm](../theorem-library/block-family-combinatorial.scm)

### Dependent choice / recursion on NN

- `dc-on-nn` — forall([x in set, a in x, r in set], forall([k in nn, u in x], forsome([y in x], [k, u, y] in r)) implies forsome([f in fun(nn, x)], f(0) = a and forall([k in nn], [k, f(k), f(succ(k))] in r)))  _[warrant: informal]_  see [~/prover/theorem-library/dc-on-nn.scm](../theorem-library/dc-on-nn.scm)
- `dc-on-nn-pred` — forall([x in set, a in x, nxt], forall([k in nn, u in x], forsome([y in x], y in nxt(k, u))) implies forsome([f in fun(nn, x)], f(0) = a and forall([k in nn], f(succ(k)) in nxt(k, f(k)))))  _[warrant: reference]_  see [~/prover/theorem-library/dc-on-nn.scm](../theorem-library/dc-on-nn.scm)

### Infinite pigeonhole and the block family

- `pigeonhole-infinite` — forall([s], s in set and not(card(s) in nn) implies forall([f], f in set and card(f) in nn implies forall([pi in fun(s, f)], forsome([c in f], not(card({x in s: pi(x) = c}) in nn)))))  _[warrant: informal]_  see [~/prover/theorem-library/pigeonhole.scm](../theorem-library/pigeonhole.scm)
- `cover-block-step` — forall([v in set, f in fun(nn, v), c], is-finite-cover(c, v) implies forall([j in inf-subsets(nn)], forsome([j_ in inf-subsets(nn)], j_ subset j and forsome([u in c], forall([i in j_], f(i) in u)))))  _[warrant: well-known]_  see [~/prover/theorem-library/block-family-combinatorial.scm](../theorem-library/block-family-combinatorial.scm)
- `block-family-combinatorial` — forall([v in set, f in fun(nn, v), cov], forall([k in nn], is-finite-cover(cov(k), v)) implies forsome([blk in fun(nn, inf-subsets(nn))], forall([k in nn], blk(succ(k)) subset blk(k)) and forall([k in nn], forsome([u in cov(k)], forall([i in blk(k)], f(i) in u)))))  see [~/prover/theorem-library/block-family-combinatorial-proof.scm](../theorem-library/block-family-combinatorial-proof.scm)

### Diagonalization

- `diagonalization` — forall([s in fun(nn, inf-subsets(nn))], forall([k in nn], s(succ(k)) subset s(k)) implies forsome([f], strictly-mono-nn(f) and forall([k in nn, j in nn], k <= j implies f(j) in s(k))))  see [~/prover/theorem-library/diagonalization.scm](../theorem-library/diagonalization.scm)
- `nn-step-strictly-mono` — forall([g in fun(nn, nn)], forall([k in nn], g(k) < g(succ(k))) implies strictly-mono-nn(g))  _[warrant: well-known]_  see [~/prover/theorem-library/diagonalization-lemmas.scm](../theorem-library/diagonalization-lemmas.scm)
- `nn-nested-subset-chain` — forall([t], forall([k in nn], t(succ(k)) subset t(k)) implies forall([k in nn, j in nn], k <= j implies t(j) subset t(k)))  _[warrant: well-known]_  see [~/prover/theorem-library/diagonalization-lemmas.scm](../theorem-library/diagonalization-lemmas.scm)
- `inf-subset-nn-unbounded` — forall([t in inf-subsets(nn), u in nn], forsome([y in nn], y in t and u < y))  _[warrant: well-known]_  see [~/prover/theorem-library/diagonalization-lemmas.scm](../theorem-library/diagonalization-lemmas.scm)

### Well-ordering of NN

- `well-ordering-principle` — forall([s in set], forsome([phi], phi in bijection(ord-segment(card(s)), s)))  _[warrant: well-known]_  see [~/prover/theorem-library/well-ordering.scm](../theorem-library/well-ordering.scm)
- `nn-least-element` — forall([t], t subset nn and forsome([n], n in t) implies forsome([m in t], forall([k in t], m <= k)))  see [~/prover/theorem-library/nn-least-element.scm](../theorem-library/nn-least-element.scm)

## Metric spaces

### Vocabulary

- `is-ms-sequence` — forall([ms], is-ms-sequence(ms) iff forall([n in nn], is-metric-space(ms(n))))  see [~/prover/structure-library/product-metric.scm](../structure-library/product-metric.scm)
- `converges-to` — forall([s, f, l], converges-to(s, f, l) iff is-metric-space(s) and f in fun(nn, pts(s)) and l in pts(s) and forall([eps], pos-rr(eps) implies forsome([n in nn], forall([n_ in nn], n <= n_ implies (dist(s))(f(n_), l) <= eps))))  see [~/prover/structure-library/metric-completeness.scm](../structure-library/metric-completeness.scm)
- `converges` — forall([s, f], converges(s, f) iff forsome([l], converges-to(s, f, l)))  see [~/prover/structure-library/metric-completeness.scm](../structure-library/metric-completeness.scm)
- `is-cauchy-seq` — forall([s, f], is-cauchy-seq(s, f) iff is-metric-space(s) and f in fun(nn, pts(s)) and forall([eps], pos-rr(eps) implies forsome([n in nn], forall([m in nn, n_ in nn], n <= m and n <= n_ implies (dist(s))(f(m), f(n_)) <= eps))))  see [~/prover/structure-library/metric-completeness.scm](../structure-library/metric-completeness.scm)
- `is-complete` — forall([s], is-complete(s) iff is-metric-space(s) and forall([f], is-cauchy-seq(s, f) implies converges(s, f)))  see [~/prover/structure-library/metric-completeness.scm](../structure-library/metric-completeness.scm)
- `ball` — _(definition / vocabulary)_
- `is-open` — forall([s, u], is-open(s, u) iff is-metric-space(s) and u subset pts(s) and forall([y in u], forsome([r], pos-rr(r) and ball(s, y, r) subset u)))  see [~/prover/structure-library/metric-open-sets.scm](../structure-library/metric-open-sets.scm)
- `is-closed` — forall([s, a], is-closed(s, a) iff is-metric-space(s) and a subset pts(s) and is-open(s, complement-in(pts(s), a)))  see [~/prover/structure-library/metric-open-sets.scm](../structure-library/metric-open-sets.scm)
- `is-continuous-at` — forall([s, t, f, a], is-continuous-at(s, t, f, a) iff is-metric-space(s) and is-metric-space(t) and f in fun(pts(s), pts(t)) and a in pts(s) and forall([eps], pos-rr(eps) implies forsome([delta], pos-rr(delta) and forall([b in pts(s)], (dist(s))(a, b) <= delta implies (dist(t))(f(a), f(b)) <= eps))))  see [~/prover/structure-library/metric-continuity.scm](../structure-library/metric-continuity.scm)
- `is-continuous` — forall([s, t, f], is-continuous(s, t, f) iff is-metric-space(s) and is-metric-space(t) and f in fun(pts(s), pts(t)) and forall([a in pts(s)], is-continuous-at(s, t, f, a)))  see [~/prover/structure-library/metric-continuity.scm](../structure-library/metric-continuity.scm)
- `is-uniformly-continuous` — forall([s, t, f], is-uniformly-continuous(s, t, f) iff is-metric-space(s) and is-metric-space(t) and f in fun(pts(s), pts(t)) and forall([eps], pos-rr(eps) implies forsome([delta], pos-rr(delta) and forall([a in pts(s), b in pts(s)], (dist(s))(a, b) <= delta implies (dist(t))(f(a), f(b)) <= eps))))  see [~/prover/structure-library/metric-continuity.scm](../structure-library/metric-continuity.scm)
- `totally-bounded` — forall([s], totally-bounded(s) iff is-metric-space(s) and forall([r], r in rr and 0 <= r and not(0 = r) implies forsome([f], card(f) in nn and is-r-net(s, f, pts(s), r))))  see [~/prover/structure-library/metric-topology.scm](../structure-library/metric-topology.scm)
- `is-r-net` — forall([s, f, a, r], is-r-net(s, f, a, r) iff forall([p in a], forsome([c in f], (dist(s))(c, p) <= r and not((dist(s))(c, p) = r))))  see [~/prover/structure-library/metric-topology.scm](../structure-library/metric-topology.scm)
- `product-metric` — _(definition / vocabulary)_
- `completion` — _(definition / vocabulary)_

### Sequences, limits, completeness

- `complete-cauchy-converges` — forall([s], is-complete(s) implies forall([f], is-cauchy-seq(s, f) implies converges(s, f)))  see [~/prover/structure-library/metric-completeness.scm](../structure-library/metric-completeness.scm)

### Open / closed sets, balls

- `ball-is-open` — forall([s], is-metric-space(s) implies forall([x in pts(s), r], r in rr and 0 <= r and not(0 = r) implies is-open(s, ball(s, x, r))))  _[warrant: proof]_  see [~/prover/structure-library/metric-open-sets.scm](../structure-library/metric-open-sets.scm)
- `ball-membership` — forall([s, x, r, y], y in ball(s, x, r) iff y in pts(s) and (dist(s))(x, y) <= r and not((dist(s))(x, y) = r))  _[warrant: proof]_  see [~/prover/structure-library/metric-topology.scm](../structure-library/metric-topology.scm)
- `ball-center-in` — forall([s], is-metric-space(s) implies forall([x in pts(s), r], r in rr and 0 <= r and not(0 = r) implies x in ball(s, x, r)))  _[warrant: proof]_  see [~/prover/structure-library/metric-topology.scm](../structure-library/metric-topology.scm)
- `empty-is-open` — forall([s], is-metric-space(s) implies is-open(s, empty-set))  _[warrant: proof]_  see [~/prover/structure-library/metric-open-sets.scm](../structure-library/metric-open-sets.scm)
- `carrier-is-open` — forall([s], is-metric-space(s) implies is-open(s, pts(s)))  _[warrant: proof]_  see [~/prover/structure-library/metric-open-sets.scm](../structure-library/metric-open-sets.scm)
- `inter-of-opens-open` — forall([s], is-metric-space(s) implies forall([u, w], is-open(s, u) and is-open(s, w) implies is-open(s, intersection(u, w))))  _[warrant: proof]_  see [~/prover/structure-library/metric-open-sets.scm](../structure-library/metric-open-sets.scm)

### Continuity

- `continuous-is-continuous-at` — forall([s, t, f], is-continuous(s, t, f) implies forall([a in pts(s)], is-continuous-at(s, t, f, a)))  _[warrant: informal]_  see [~/prover/structure-library/metric-continuity.scm](../structure-library/metric-continuity.scm)
- `continuous-implies-open-preimage` — forall([s, t, f], is-continuous(s, t, f) implies forall([v], is-open(t, v) implies is-open(s, preimage(s, f, v))))  _[warrant: proof]_  see [~/prover/structure-library/metric-open-sets.scm](../structure-library/metric-open-sets.scm)
- `open-preimage-implies-continuous` — forall([s, t, f], is-metric-space(s) and is-metric-space(t) and f in fun(pts(s), pts(t)) implies forall([v], is-open(t, v) implies is-open(s, preimage(s, f, v))) implies is-continuous(s, t, f))  _[warrant: proof]_  see [~/prover/structure-library/metric-open-sets.scm](../structure-library/metric-open-sets.scm)
- `continuous-implies-closed-preimage` — forall([s, t, f], is-continuous(s, t, f) implies forall([a], is-closed(t, a) implies is-closed(s, preimage(s, f, a))))  _[warrant: proof]_  see [~/prover/structure-library/metric-open-sets.scm](../structure-library/metric-open-sets.scm)
- `closed-preimage-implies-continuous` — forall([s, t, f], is-metric-space(s) and is-metric-space(t) and f in fun(pts(s), pts(t)) implies forall([a], is-closed(t, a) implies is-closed(s, preimage(s, f, a))) implies is-continuous(s, t, f))  _[warrant: proof]_  see [~/prover/structure-library/metric-open-sets.scm](../structure-library/metric-open-sets.scm)

### Completion

- `completion-is-metric-space` — forall([m], is-metric-space(m) implies is-metric-space(completion(m)))  _[warrant: well-known]_  see [~/prover/structure-library/metric-completion.scm](../structure-library/metric-completion.scm)
- `completion-is-complete` — forall([m], is-metric-space(m) implies is-complete(completion(m)))  _[warrant: well-known]_  see [~/prover/structure-library/metric-completion.scm](../structure-library/metric-completion.scm)
- `embed-isometry` — forall([m], is-metric-space(m) implies forall([u in pts(m), v in pts(m)], (dist(completion(m)))(embed(m, u), embed(m, v)) = (dist(m))(u, v)))  _[warrant: well-known]_  see [~/prover/structure-library/metric-completion.scm](../structure-library/metric-completion.scm)

### Compactness / total boundedness

- `totally-bounded-has-cauchy-subsequence` — forall([s], totally-bounded(s) implies forall([f in fun(nn, pts(s))], forsome([phi], strictly-mono-nn(phi) and is-cauchy-seq(s, subseq(f, phi)))))  see [~/prover/theorem-library/cauchy-subseq-proof.scm](../theorem-library/cauchy-subseq-proof.scm)
- `cauchy-rapid-subsequence` — forall([s, f, rad], is-cauchy-seq(s, f) and rad in fun(nn, rr) and forall([k in nn], pos-rr(rad(k))) implies forsome([phi in fun(nn, nn)], forall([m in nn, n_ in nn], m < n_ implies phi(m) < phi(n_)) and forall([k in nn], (dist(s))(f(phi(k)), f(phi(succ(k)))) <= rad(k))))  _[warrant: well-known]_  see [~/prover/structure-library/metric-completeness.scm](../structure-library/metric-completeness.scm)

### Product metric spaces

- `product-is-metric-space` — forall([ms], is-ms-sequence(ms) implies forall([w], summable-weight(w) implies is-metric-space(product-metric-w(ms, w))))  _[warrant: well-known]_  see [~/prover/structure-library/product-metric.scm](../structure-library/product-metric.scm)
- `product-projection-continuous` — forall([ms], is-ms-sequence(ms) implies forall([w], summable-weight(w) implies forall([n in nn], is-continuous(product-metric-w(ms, w), ms(n), product-proj(ms, n)))))  _[warrant: well-known]_  see [~/prover/structure-library/product-metric.scm](../structure-library/product-metric.scm)
- `product-convergence-coordinatewise` — forall([ms], is-ms-sequence(ms) implies forall([w], summable-weight(w) implies forall([seq in fun(nn, product-carrier(ms)), l in product-carrier(ms)], converges-to(product-metric-w(ms, w), seq, l) iff forall([n in nn], converges-to(ms(n), vnb-lambda(k, (seq(k))(n)), l(n))))))  _[warrant: well-known]_  see [~/prover/structure-library/product-metric.scm](../structure-library/product-metric.scm)
- `compact-countable-product` — forall([ms], is-ms-sequence(ms) implies forall([n in nn], is-compact(ms(n))) implies is-compact(product-metric(ms)))  see [~/prover/theorem-library/tychonoff-proof.scm](../theorem-library/tychonoff-proof.scm)

### Normed-field metric

- `nf-metric-space-is-metric-space` — forall([nf], is-normed-field(nf) implies is-metric-space(nf-metric-space(nf)))  _[warrant: informal]_  see [~/prover/structure-library/normed-field-metric.scm](../structure-library/normed-field-metric.scm)

