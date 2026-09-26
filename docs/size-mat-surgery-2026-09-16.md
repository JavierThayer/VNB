# The SIZE/MAT surgery -- design note (2026-09-16)

This note records a soundness repair to the matrix layer of the VNB library, the
decisions it rested on, and the shape the repaired statements take.  The repair
specification that drove the agents on the day is preserved in
`scratchpad/surgery/SPEC.md`; this document is the account of it.

## 1. The defect

Until 2026-09-16 the library contained a false assertion.  `matof-exists`, a
warranted support in `structure-library/matrix.scm`, stated that the tabulation
`MATOF(m, n, g)` of an entry function over the index box exists, with the
dimensions `m` and `n` unquantified.  Instantiated at `m := ORD`, the class of
ordinals, it yields a matrix with `ORD` rows; the lemma `mat-rows-in-nn` then reads
`ORD in NN` off the matrix, and the Burali-Forti theorem refutes that.  The probe
`scratchpad/mx/mx-probe3.scm` derived `FALSITY` from the library in this way.

Two further weaknesses were found in the audit that followed.

* `SIZE` was partial at a matrix with no rows: `SIZE(M)` read the column count off
  the first row, and `[]` has none.  A zero-row matrix therefore had no determinate
  size, and no zero-row matrix belonged to any `MAT(0, n, X)`.
* The base case of the span arc (`spans-fg-base`) read the empty linear combination
  as the `(1,1)` entry of a one-by-zero product, `NTH(1, [])`, an unspecified value.

The lesson is the one the bill ledger exists for.  An assertion that was harmless
when written became unsound when a lemma proved much later, for an unrelated
reason, met it.

## 2. The decisions

The user took three decisions, in this order.

1. `SIZE` is total, and a matrix with no rows is `[]`, the unique element of
   `MAT(0, n, X)` for every natural `n`.  Membership in `MAT` does not determine
   the column count of a matrix with no rows.
2. The linear combination of the span arc is a finite sum over the index interval
   (`LINCOMB`), so the empty combination is the zero vector by construction and no
   product of degenerate shape is ever read.
3. Every law about a product whose middle dimension may be zero carries a guard
   stating the condition under which the law holds, and the guard is placed so that
   the binder lists of the statements are unchanged.

`matof-exists`, `entry-of-matof` and `matof-in-mat` became theorems, guarded on
`m, n in NN`.

## 3. The definitions after the repair

    SIZE(M)      = [LENGTH M, IF(LENGTH M = 0, 0, LENGTH(NTH 1 M))]
    MAT(m, n, X) = SEP P in MATRIX(X).
                       n in NN
                       and (LENGTH P = 0  =>  m = 0)
                       and (LENGTH P /= 0 =>  SIZE P = [m, n])

    LINCOMB(md, n, c, u)
      = FINSUM(MODULE-VECTOR-AG md,
               VNB-LAMBDA j in INTERVAL(1, n).  ACT(md)(ENTRY(c, 1, j), ENTRY(u, j, 1)),
               INTERVAL(1, n))

`GENERATES`, `REL-FREE`, `SPANS`, `SPAN`, `span-membership`, `LASTCOEFF-SET` and
`lastcoeff-set-membership` read `LINCOMB(md, n, c, u)` where they previously read
`ENTRY(MATACT(md, c, u), 1, 1)`.

Membership in `MAT` is read only through the lemmas of
`theorem-library/mat-basics.scm` (`mat-in-matrix`, `mat-cols-in-nn`, `mat-length`,
`mat-rows-in-nn`, `mat-size`, `mat-cols`, `mat-size-rows`, `mat-size-cols`,
`mat-intro`, `mat-intro-empty`, `nil-in-mat`), never by unfolding the definition
in a proof.

## 4. Why the product laws need guards

`MATMUL(A, P, Q)` and `MATACT(md, P, u)` read the column count of their result off
`SIZE` of the right factor.  When the middle dimension `n` is zero the right factor
is `[]`, `SIZE([]) = [0, 0]`, and the product of an `m`-by-`0` matrix with it is
`m`-by-`0`, not `m`-by-`k`.  Any statement about a product whose middle dimension
can be zero while both outer dimensions are at least one is therefore false.

The guards, by the kind of law:

* Entry laws, whose citers hold indices in the interval: `1 <= n` on the middle
  dimension (`matmul-entry`, `matact-entry`, `triple-entry-left/right`,
  `matact-triple-left/right`).
* Typing and whole-matrix laws, for `P : m x n` and `Q : n x k`:
  `n = 0  =>  (m = 0 or k = 0)` (`matmul-type`, `matact-type`,
  `mat-colcount-transfer`, `generates-coeff-matrix` in the form `n = 0 => m = 0`).
  A citer with square or one-sided-square dimensions discharges it by propositional
  reasoning.
* Associativity, for `P : m x n`, `Q : n x k`, `R : k x l`: the pair

      G1:  n = 0  =>  (m = 0 or (k = 0 and l = 0))
      G2:  k = 0  =>  (l = 0 or (n = 0 and m = 0))

  These are sufficient, not exact (the exact condition is
  `n = 0 => (m = 0 or k = 0 or l = 0)`); they were chosen because every citer
  discharges them propositionally and the extensionality route needs both sides
  typed `m`-by-`l`.  From G1 and G2 the typing guard of each of the four inner
  products follows.

Each guard is a premise placed after the binders, so that every citation's argument
list is unchanged.  A comment above each guarded statement gives the counterexample
that forces the guard.

## 5. The renames in the span arc

The content of the following statements changed, so their names changed with it.

| retired            | replaced by       |
|--------------------|-------------------|
| matact-row-add     | lincomb-row-add   |
| matact-row-scale   | lincomb-row-scale |
| matact-zerorow     | lincomb-zerorow   |
| matact-unitrow     | lincomb-unitrow   |
| matact-empty-vzero | lincomb-empty     |
| matact-row-peel    | lincomb-row-peel  |
| matact-snoc        | lincomb-snoc      |

Two bridges connect the old reading to the new: `lincomb-unfold`, the unfold
equation of the functoid, and `matact-lincomb`, which states that for `1 <= n` the
`(1,1)` entry of `MATACT(md, c, u)` is `LINCOMB(md, n, c, u)`.

## 6. The further supports that were guarded

The same audit found about twenty-five asserted matrix supports whose statements
assumed, without saying so, that a dimension is a natural number, that a structure
is a ring, or that an entry they read is defined (`entry-of-identmat`,
`unitrow-type`, `entry-of-block`, `entry-of-snoc-col`, `matadd-entry`,
`zeromat-type`, `entry-of-submat`, the `border-*` entry laws, `elem-f-type`,
`elem-h-type`, `elem-f-symmetric`, among others).  Each was guarded; twenty of them
were proven rather than re-asserted.

## 7. Consequences

After the repair the library loads cleanly with 1410 proofs, of which 1295 bill
`modulo 0`.  `spans-fg-base` bills `modulo 0`; `submodule-fg` bills sixteen leaves,
all `well-known`.  The three controls `scratchpad/mx/mx-probe1.scm`,
`mx-probe3.scm` and `mx-probe4.scm` no longer close.  The suite reports 1220 checks
passed and none failed.

Two consequences for the working rules:

* An asserted support with unquantified dimensions is a statement about every
  class, and must be read that way before it is warranted.
* "Proven with no asserted step" is a claim about a bill, and a bill is re-read,
  not remembered.
