# The definitions for Cauchy-Goursat (decided 2026-09-25)

The user's decisions of 2026-09-25 for complex-analysis ch. 3, section 3.2 (Lemma 3.4 to Cor 3.9),
recorded before batch 30 was launched. The survey behind them: the line-integral and holomorphy layers
were complete (batches 22-24, 26); the geometric objects of 3.2 were absent.

1. **The segment.** `SEG-PATH(z1, z2)` and `SEG-DERIV(z1, z2)` are the road `s |-> z1 + s*(z2 - z1)`,
   `s |-> z2 - z1` on `[0, 1]` (the shape of `segment-is-road`); `SEG-INT(f, z1, z2)` is
   `LINE-INT(f, SEG-PATH(z1,z2), SEG-DERIV(z1,z2), 0, 1)`, the notes' integral over `<z1, z2>`.
2. **The triangular path.** `TRI-INT(f, a, b, c)` is `SEG-INT(f,a,b) + SEG-INT(f,b,c) + SEG-INT(f,c,a)`,
   which is what the notes' Prop 3.1 (path additivity) reduces the integral over the triangular path to.
   The juxtaposition of roads (Dieudonne 9.6; Prop 3.1 in general) is a later batch of its own; when it
   exists, the equality of the two readings is a theorem and no statement of 3.2 changes.
3. **The convex hull of three points and convexity.** `CONV3(a, b, c)` is the set of `z in CC` for which
   there are `al, be, ga in [0, 1]` with `al + be + ga = 1` and `z = al*a + be*b + ga*c` (a SEP over CC);
   `IS-CONVEX(U)` says `z + t*(w - z) in U` for all `z, w in U` and `t in [0, 1]`. `CC-MID(x, y)` is
   `(x + y) * recip(2)`, the notes' `m(x, y)`.
4. **No diameter, no length.** The notes' (57) and (58) become arithmetic on the vertices: the estimate
   is done one segment at a time (`segment-int-abs-bound`: `|SEG-INT| <= |w| * M`) with the perimeter
   `|b - a| + |c - b| + |a - c|` as a term. Batch 24's open decision on the LENGTH of a road stays open.
5. **The exceptional point.** Prop 3.6 to Cor 3.9 are proven first for `f` holomorphic on all of `U`
   (names `goursat-triangle`, `cauchy-convex-segments`, `cauchy-convex-primitive`, `cauchy-convex-closed`);
   the strengthening "continuous on `U`, holomorphic off one point `x`" keeps the notes' statements and
   comes as a later batch, since the Cauchy integral formula needs it.

The route for the common point of the nested triangles (batch 29-B's finding): no Cantor intersection
and no compactness. The chosen sub-triangles are driven on the STANDARD triangle (barycentric
coordinates encoded as `al + i*be` in CC) and mapped by the real-affine `V(xi) = re(xi)*a + im(xi)*b +
(1 - re(xi) - im(xi))*c`, which commutes with midpoints; the abstract vertex sequence telescopes
(`cc-telescoping-limit-bound`), its limit keeps the closed coordinate conditions, and `V` of it lies in
`CONV3(a, b, c)` by definition, hence in `U`.
