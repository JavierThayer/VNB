<!-- VERBATIM copy of a section of CLAUDE.md as it stood on 2026-09-18, moved here when
CLAUDE.md was trimmed to its operational rules.  Nothing was edited.  The dated findings,
measurements and case histories behind each rule in CLAUDE.md are in this text. -->

## Where the project is going

The **prove-theorem stage is done** (2026-07-11): `spans-submodule-fg` -- and with it
`submodule-fg` -- is proven. Its purpose was never the theorems themselves: it was to
exercise and stress the machinery, and it delivered, right at the end, the
simultaneous-substitution bug in the macete rewriter (below).

**Until 2026-09-16 this paragraph said "proven, with no asserted step". That was false
in two ways.** (1) The bill was never empty: on 2026-09-16 it named 32 asserted leaves,
all `well-known`. (2) One of them was unsound. `matof-exists`, an asserted support with
unquantified dimensions, proved FALSITY once instantiated at m := ORD (`mat-rows-in-nn`
reads `ORD in NN` off the matrix; burali-forti refutes it; probe
`scratchpad/mx/mx-probe3.scm`). And the n = 0 base case read the empty linear
combination as the (1,1) entry of a 1-by-0 product, `NTH(1, [])`, an unspecified value,
because a matrix with no rows had no determinate size.

Repaired 2026-09-16 (the user's decisions):
* `SIZE` is total, and `[]` is the unique 0-by-n matrix for each natural n; membership
  in `MAT` does not determine the column count of a matrix with no rows
  (structure-library/matrix.scm, header).
* The linear combination is `LINCOMB`, a FINSUM over [1,n], so the empty combination is
  VZERO by construction (structure-library/mod-seq.scm).
* A product whose middle dimension is 0 reads its column count off `[]`, so the product
  laws carry guards: entry laws `1 <= n`; typing laws `n = 0 => (m = 0 or k = 0)`;
  associativity the two-dimension pair G1/G2
  (docs/size-mat-surgery-2026-09-16.md, the design note; the repair specification the
  agents worked from is scratchpad/surgery/SPEC.md).
* `matof-exists`, `entry-of-matof` and `matof-in-mat` are THEOREMS guarded on
  `m, n in NN`. About thirty further matrix supports that assumed a natural dimension or
  a ring without saying so were guarded, and twenty of them proven.

After the repair, `spans-fg-base` bills `modulo 0`, and `submodule-fg` bills 16 leaves,
all `well-known`. Five of them are matrix typing supports (`block-type`, `matadd-type`,
`matscale-type`, `snoc-col-type`, `snoc-row-type`); the audit found all five true at
every dimension under the new definitions. The controls `mx-probe1`,
`mx-probe3` and `mx-probe4` no longer close. The lesson is the one the bill ledger exists
for: an assertion that was harmless when written became unsound when a lemma proved much
later, for an unrelated reason, met it; and "no asserted step" was a claim that nobody
re-checked against the bill.

Then the project **refocuses**, onto three things:

1. **Print proofs and read proofs.** `proof-tex` (full trace) and `proof-reader` (sketch)
   exist and are faithful, but they report the *official* level -- three lemma citations --
   where a human wants the *content* level: "Since `a` is a Euclidean ring, `a` is a ring."
   The table is BUILT (`operators.scm`, the ONE table keyed by head symbol; populated by
   `def-predicate` / `def-functoid` at definition time via `register-operator!`, and the
   reading declared next to the definition with `notation!`). It is read by `wff-english`
   (`operator-ref` / `operator-english`), `describe-structure` and `OPERATORS.md`.
   `expr->tex` reads it too, and the old entry here -- "expr->tex does NOT read it" --
   was half wrong: the hook (`operator-render-tex`, tex-output.scm) had been in the
   `expr->tex` cond all along, but BELOW tex-output's own binop/special tables and,
   more to the point, **no head in the tree declared a `tex` template** (195 `notation!`
   calls, 0 with a `'tex` key), so it never fired. Fixed 2026-08-10: the branch now sits
   ABOVE the two built-in tables (a declaration beats a default) and BELOW the
   arithmetic-prefix branch (a fluid MODE beats a declaration), and `==` declares
   `($1 \simeq $2)` -- the manual's own reading -- instead of falling through to
   `\operatorname{==}(...)`. `abs` got the CARD treatment (`\lvert x \rvert`) in
   tex-output's special table, where it belongs: it is a primitive with no operator entry.
   STILL OUTSTANDING on the reader: collapse a run of subtype-subsumption
   citations (`register-definitional-structure!` already records the parent chain); capture
   the goal BEFORE each step, not only after, so the reader can always name an existential's
   bound variable (see the `proof-reader--goal-before` comment); render `IS-EUCLIDEAN-RING(a)`
   as "a is a Euclidean ring".

**Where a definition lives, and the trap under it.** `def-predicate` / `def-constant`
install a THEOREM (the defining iff), so they land in `theory-definitions` and hence in
`reference/DEFINITIONS.md`. `def-functoid` installs only a rewrite MACETE -- no theorem --
so a functoid is in neither that registry nor `*theorem-table*`. Two consequences, and they
are the same fact seen from two sides:

* `mac` unfolds a functoid in a GOAL; **`mac-h` cannot unfold one in an ASSUMPTION by the
  functoid's own name.** It warns `unknown theorem/macete` and the driver continues with
  the hypothesis untouched. A constructor whose members get read out of the context
  therefore needs a membership `iff` beside it (`span-membership`,
  `principal-ideal-membership`, `zz-bezout-set-membership`, ...). That iff is a
  CONSEQUENCE of the definition -- the functoid unfold composed with the SEP separation
  schema -- not the definition.

  **But it does NOT have to be ASSERTED, and this entry said for weeks that it did.**
  The unfold equation is PROVABLE, one line per functoid, and the proof is `modulo 0`:

      (sp (make-wff '(FORALL a_ (FORALL m_ (== (FINSUPP a_ m_) (SEP f_ ...))))))
      (di) (mac 'FINSUPP) (qrfl)

  `mac` unfolds the functoid in the GOAL -- which is the half that works -- and `qrfl`
  closes the resulting `X == X`. The result is a THEOREM, and `mac-h` rebuilds its rule
  from the theorem table, so `(mac-h 'finsupp-unfold h)` rewrites the hypothesis into a
  literal SEP membership that `sep-me` reads apart. Demonstrated side by side in
  `scratchpad/pl-probe2.scm` (2026-08-20): `(mac-h 'FINSUPP 1)` warns and no-ops;
  `(mac-h 'finsupp-unfold 1)` rewrites, then `(sep-me)` `(ass)` closes. Seven such
  theorems for SUPP/FINSUPP/POLY are in `theorem-library/poly-membership.scm`, all
  `modulo 0`. `interval-basics.scm` and `mat-basics.scm` already did this the long way,
  via `have!` + `subst`; the `mac-h` route is one step and works in place.

  So every `definitional`-stamped constructor membership law in the tree is a candidate
  for PROOF instead of a stamp. NOT DONE for the existing ones: re-tiering moves every
  citing bill, so it is a separate measurement (triage by BILL).
* Until 2026-08-10 **DEFINITIONS.md carried no functoid at all**; all 113 were only in
  `FUNCTORS.md`. Looking up `zz-bezout-set` there found only its membership law, which
  reads exactly like a definition and is not one. `write-definitions-md` now emits an
  "Unfold-only constructors (functoids)" section from `*functoid-registry*`, filtered by
  `lookup-view-as` as FUNCTORS.md filters it, so the counts cannot drift (113 in both).

And a name-shape trap worth stating once: `zz-bezout` is a THEOREM; the thing defined is
`ZZ-BEZOUT-SET`. Searching the definition index for a theorem's name lands you on whatever
shares its prefix.

2. **A large database of theorems without proofs**, suitable as raw material for building new
   proofs. Statements, indexed and searchable; the PSS is the seed.

3. Revisiting the manual against all of it.

Do not treat "prove one more theorem" as the goal. The deliverable of a proof request is
usually the obstacles it exposes.

