# VNB Test Report

Run 2026-06-22 by `vnb-test`.  The driving exam: every theorem with a
runnable proof re-proved in sequence.  PSS members and definitions are
not examined (excused by design).

**Result: 2 FAILURE(S)** -- 17 theorem(s) certified.

| stage | result | time | detail |
|---|---|---|---|
| `LOAD (at-load proofs)` | PASS | 11s | 15 theorem(s) |
| `calculus/prop-3-14-proof.scm` | PASS | 32s | 1/1 qed: converges-to-compose-continuous |
| `calculus/prop-3-15-proof.scm` | FAIL | 16s | 0/1 qed: none |
| `calculus/uniqueness-of-limits.scm` | FAIL | 12s | 0/3 qed: none |
| `calculus/euclidean-ring-pid.scm` | PASS | 12s | 1/1 qed: euclidean-ring-is-pid |

## Certified theorems

- `abelian-group-is-group` -- certified 2026-06-22
- `abelian-group-mul-comm` -- certified 2026-06-22
- `bijection-in-fun` -- certified 2026-06-22
- `bijection-injective` -- certified 2026-06-22
- `bijection-is-injection` -- certified 2026-06-22
- `bijection-surjective` -- certified 2026-06-22
- `commutative-ring-is-ring` -- certified 2026-06-22
- `converges-to-compose-continuous` -- certified 2026-06-22
- `euclidean-ring-is-integral-domain` -- certified 2026-06-22
- `euclidean-ring-is-pid` -- certified 2026-06-22
- `metric-pos` -- certified 2026-06-22
- `metric-self-zero` -- certified 2026-06-22
- `metric-sym` -- certified 2026-06-22
- `metric-triangle` -- certified 2026-06-22
- `metric-zero-eq` -- certified 2026-06-22
- `module-zero-act` -- certified 2026-06-22
- `nn-least-element` -- certified 2026-06-22
