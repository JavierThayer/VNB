# Manual revision — defect & gap catalog (2026-07-20)

Assessment of `docs/*.tex` against the live codebase, five parallel verification
passes. Every claim below was grep-checked against `/home/ubuntu/prover`. This is
the working evidence base for the ground-up revision.

## Cross-cutting systemic problems (hit multiple chapters)

1. **The case-fold accessor rename never propagated to the manual.** Code uses
   `CARR` (algebraic carrier) / `PTS` (metric), `OPR` (operation), `IDEN`
   (identity), `DIST` (distance), `INV`. The manual still uses the pre-rename
   `A`/`X`, `MUL`, `E`/`ID`, `D`. Pervasive in ch-proofs (tables, snippets, a
   runnable example) and ch-defs (all five algebra declarations, metric-space).
   `RING`'s `MUL` is correct; group/monoid `MUL` is wrong — the manual conflates
   them.

2. **Files named that do not exist.** `algebraic.scm` (ch-proofs 174,923;
   ch-defs 510,1392), `basic-rings.scm` (ch-defs 1539,1706), `normal-math`
   theory (ch-syntax 30,66,84,112 — real base theory is `VNB-SET-THEORY`). Real
   homes: structures in `structure-library/<name>.scm`; ring instances in
   `numeric-instances.scm`.

3. **Forms/procedures named that do not exist or were renamed.**
   `def-view-as` → **`def-functor`** (ch-defs 1046–1161). `extend-theory` —
   never existed (ch-syntax 74–93, "local contexts as theory extensions" is
   fiction: `declare-local-context` just pushes a record). `CARRIER` accessor —
   real is `CARR`/`PTS` (ch-defs 84,943; ch-expressions §2 copy-paste `CARR` into
   `fun-set-iff`/`cartesian-set-iff` where code has `A`). `ring-poly-equal?` —
   does not exist (ch-proofs 174).

4. **Non-existent theorem/axiom names cited in examples.**
   `monoid-carrier-closed-mul` (real `…-opr`), `comm-monoid-mul-comm`,
   `monoid-identity-in` (real `group-identity-in`), `ball-subset-carrier` (code
   explicitly notes its absence). These make worked examples un-runnable.

5. **Stale counts / status.** app-tests "165 passed" — now **755**. ch-math
   "Still pending: iota-def/lambda-type/lambda-beta" — all now implemented
   primitives (`primitive-inferences.scm` pi-iota-def!/pi-lambda-type!/
   pi-lambda-beta!). ch-defs metric "five axioms" — now proven laws.

6. **`ch-source` appendix grossly stale** (this is the worst-hit file): calls
   `theorem-library/` "just `axioms.scm`" (it holds 100+ qed proofs); lists ~12
   of ~80 structure-library files; omits `calculus/` entirely; omits central
   root files (`proof-tex`, `proof-reader`, `minimize`, `driver-kit`,
   `proof-debt`, `sketch`, `vlet`, `prep`, `parser`, `load`, `operators`, …);
   puts `vnb.el`/`vnb-launch.el` at the root (they're in `emacs/`).

7. **Coverage gaps — central machinery undocumented.**
   - Tactics: `fact`, `obtain`, `minimize!`, `vlet`, `grind`, `mac-h*`,
     `detach!`, `have!`/`from-context!`, `inst+`, `to-binary`/`to-nary`,
     `repeat`/`orelse`, `focus-id`.
   - Definition forms: `same-shape-as`, `derived`, `law` clauses; `declare-hom!`,
     `def-constructed-functor`, `declare-instance!`, `notation!`,
     `support`/`warrant!` (used but never introduced).
   - Soundness: the **`proof-cycle-check` gate** (now a hard load error) is
     absent from ch-classification.
   - Math: the entire structure library (groups→…→metrizability) and the proven
     theorem corpus are absent from ch-math.

8. **Duplication & internal contradiction.** Intro IMPS paragraph verbatim twice
   (ch-intro 10–16 / 101–108). ch-expressions functoid-record remark twice
   (631–647 / 677–684) and category-theory motivation twice (241–254 / 761–785).
   ch-syntax `free-vars` vs `wff-free-vars` contradicts ch-source. Within-chapter
   naming splits (`ID` vs `CARR`; metric `X/D` vs `PTS/DIST` in adjacent snippets).

9. **Roadmap prose presented as documentation.** ch-expressions ISOPER /
   apply-operator / define-object / FORSOME-UNIQUE (all absent from code);
   ch-math "Pending axioms" section; ch-defs SUM-SET/PROD-SET. Needs triage:
   keep as clearly-marked future work, or cut.

10. **Author's own TODO markers** still inline in ch-intro (references/citations:
    l.8, 20–22, 26, 34–36 — "NO HALLUCINATIONS please").

Side-finding: `CLAUDE.md`'s stated trust order (`none hand-wave informal
reference well-known proof`) is itself STALE — code and manual agree on
`none hand-wave well-known reference informal proof`. The manual (ch-classification)
is correct.

## Per-chapter disposition (health, from assessments)

| Chapter | Lines | Health | Core problem |
|---|---|---|---|
| ch-intro | 534 | draft | TODO citation markers; duplicated IMPS para; UI/API to re-verify |
| ch-classification | 267 | **healthy** | accurate; one gap: cycle-check soundness gate |
| ch-expressions | 1270 | sound-but-stale | conceptual scaffolding good; concrete identifiers/precedence table wrong; duplication; roadmap prose |
| ch-syntax | 152 | broken | `normal-math`/`extend-theory`/`get-context` fiction; `free-vars` wrong |
| ch-proofs | 1475 | **most stale** | MUL/ID accessors, non-existent theorems, `algebraic.scm`, B/B+ confusion, big tactic gaps |
| ch-math | 532 | thin | accurate as far as it goes; entire structure library + corpus missing; stale "pending" |
| ch-defs | 1768 | scaffolding-good/identifiers-broken | `def-view-as`, two dead files, whole accessor generation, 6+ undocumented forms |
| ch-source | 127 | grossly stale | ~12/80 structure files; theorem-library "just axioms.scm"; central files omitted |
| app-tests | 439 | stale-count | "165 passed" (→755); wrong invocation; abridged coverage over-promised |

## What's actually SOUND (keep the bones)
- ch-classification's proof-debt/trust-tier content (verified correct).
- The conceptual scaffolding of ch-expressions (strict/quasi equality, functoids,
  partiality) and ch-defs (shape-vs-property, view-as-as-forgetful-functor,
  name/instance/class, totality-vs-typing).
- The chapter ordering is roughly defensible.

## Governing principle for the rewrite
**Verify-before-write.** Every code example, identifier, tactic, form, file name,
count, and citation is re-derived from the running system before it goes in. No
citation is added that cannot be verified (the author's own standing rule). This
is the discipline the current draft failed at — nearly every defect above is a
claim that drifted from code.
