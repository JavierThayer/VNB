# VNB Proof Checker — Critical Soundness Review

Date: 2026-05-15
Mandate: comprehensive bongo-hunt across kernel, axioms, functoid instances, and manual exposition. Project is mid-development; this review is a checkpoint, not a gate.

Findings ordered by severity. Each finding cites `file:line`. Severity codes:

| Code | Meaning |
|---|---|
| **SOUNDNESS** | Could let an unsound theorem be proved or admit FALSITY |
| **CORRECTNESS** | Would crash, reject a true theorem, or breach a kernel invariant |
| **DRIFT** | Manual claims something the source does not implement (or vice versa) |
| **DESIGN** | Redundancy, missing case, incomplete/conservative behaviour, undocumented convention |
| **STYLE** | Cosmetic or pedagogical |

---

## 0. Top bongos (TL;DR)

The five highest-priority items, in rough order of how badly they bite:

1. **S-1 — `pairing` collapses the class/set distinction.** Combined with `membership-implies-sethood`, makes every class a set, contradicting `burali-forti`. (`theory.scm:151-157`)
2. **S-2 — `cmd-qed` drops the root sequent's assumptions.** A theorem proved under a context `Γ ⊢ φ` is installed as the bare `φ`, usable in any context. (`proof-commands.scm:189-195`)
3. **S-3 — `subst-free` and `free-vars` skip compound heads.** Instantiating the metavariable `m` in `((MUL m) a b)` does nothing — the metavariable is invisible to substitution because it sits in head position. (`expressions.scm:185-188, 289-294`)
4. **S-4 — `VNB-LAMBDA` is not registered as a binder anywhere.** Its bound variable is reported free; `subst-free` corrupts the binder. Live axioms in `algebraic.scm`/`complex.scm`/`sequences.scm` use `VNB-LAMBDA`. (`expressions.scm`, `wff.scm:219-226`)
5. **S-5 — Macete `lc-extend` doesn't invalidate local-context assumptions when descending under a shadowing binder.** Conditional macetes can fire on hypotheses that no longer mean what they did. (`macetes.scm:306-313`)

Items 6–10 are still soundness-class but more localised: weak `fresh-var` (S-6), `pi-theorem-assumption!` accepts arbitrary formulas (S-7), `pi-functoid-beta!` is sequential rather than parallel (S-8), `make-set-membership` quantifies over unbounded indices (S-9), schema variables in macete conditions can match coincidentally (S-10).

---

## 1. SOUNDNESS findings

### S-1. `pairing` + `pairing-membership` + `membership-implies-sethood` ⇒ every class is a set  ✓ FIXED 2026-05-15
- **Fix:** Both `pairing` and `pairing-membership` now require `(IN a SET) ∧ (IN b SET)` as antecedent. `card-insert` (`cardinality.scm:27`) updated correspondingly to require `(IN x SET)` since it uses `(PAIR x x)`. Manual `ch-math.tex:373-376` updated. Theory.scm docstring (`:107-110`) updated. 206/206 tests pass; manual compiles clean.
- **Where**: `theory.scm:151-157`, with `theory.scm:128` (`membership-implies-sethood`).
- **What**: `pairing` asserts `∀a,b. PAIR(a,b) ∈ SET` with **no** sethood hypothesis on `a, b`. `pairing-membership` then gives `x ∈ PAIR(a,b) ↔ (x = a ∨ x = b)`. Take any class `a`: `a ∈ PAIR(a, a)` (RHS holds since `a = a`), so by `membership-implies-sethood`, `a ∈ SET`. **Every class is a set.** Directly contradicts `burali-forti` (`ordinals.scm:17`).
- **Witness**: `BONGO ∈ PAIR(BONGO, BONGO)` ⇒ `BONGO ∈ SET`. So `ORD ∈ SET` ⇒ FALSITY.
- **Recommendation**: Restrict to `(IMPLIES (AND (IN a SET) (IN b SET)) (IN (PAIR a b) SET))` and likewise condition `pairing-membership` on sethood. The standard NBG move is to make `PAIR` *total* but return `EMPTY-SET` on proper classes, with the membership iff stated only for sets.

### S-2. `cmd-qed` discards the root sequent's assumptions  ✓ FIXED 2026-05-15
- **Fix:** `cmd-qed` now wraps the assertion in `(FORALL <binding> ...)` for each root assumption (outermost first), then runs `expand-destructuring-quantifiers` to convert each `(FORALL (IN x A) B)` into `(FORALL x (IMPLIES (IN x A) B))`. The installed theorem is now the universal closure / implication discharge of `Γ ⊢ φ`. A one-line `qed: discharged N context assumption(s).` message prints when discharge happens. Two regression tests added (test-suite.scm §6m): one verifies the discharge for a non-empty context, one verifies `qed` with no contexts still installs the bare formula verbatim. 208/208 tests pass.
- **Side fix:** While testing S-2, found a typo in `interactive.scm:149, 169, 184` — three calls to `vnb--require-proof` (no `!`) where the actual definition is `vnb--require-proof!` (line 61). Affects `(focus n)`, `(qed name)`, `(replay-proof name)`. Fixed all three. **This was a separate latent bug not in the original audit; logging it here as C-6.**
- **Where**: `proof-commands.scm:189-195`; sets up the issue at `proof-commands.scm:15-24` (`start-proof` lifts contexts to assumptions).
- **What**: `cmd-qed` extracts `(sequent-node-assertion (proof-state-root ps))` and registers it as a top-level theorem, ignoring the root assumptions that came in via `wff-contexts`. So `Γ ⊢ φ` becomes "`φ`" — context-free.
- **Witness**: Declare a context `Γ` containing `(IN x (MAKE-SET (LIST 0)))`. Prove `(= x 0)` — easy under that assumption. `(qed 'x-is-zero)` installs `(= x 0)` as a theorem available in **all** contexts.
- **Recommendation**: Either install the universal closure / implication over the root assumptions, or refuse `qed` if the root has nonempty assumptions and require an explicit `discharge` step.

### S-3. `subst-free` and `free-vars` skip compound heads  ✓ FIXED 2026-05-15
- **Fix:** Both `free-vars` and `subst-free` else branches now recurse into the head when it's a pair (`((MUL m) a b)` correctly exposes/substitutes `m`). **Symbol heads are intentionally NOT substituted** — see Note below for why.
- **Note (case-folding workaround):** MIT Scheme case-folds symbols, so the carrier accessor `A` and the bound variable `a` are the SAME symbol. Substituting symbol heads would wrongly rewrite `(A m)` to `((PROD-ORD m f n) m)` whenever the user instantiates `eq-subst-membership`-style axioms (witness: prod-ord-type proof breaks). This collision affects all single-letter accessors (`A`, `E`, etc.). The fix preserves the existing pass-through-symbol-heads workaround. A future deeper fix would require either case-sensitive symbols or a syntactic constant/variable distinction.
- **Where**: `expressions.scm:185-188` (free-vars else branch), `expressions.scm:289-294` (subst-free else branch). Compare `alpha-equiv-under?:381-389` which DOES recurse into the head.
- **What**: For an expression `(h a b ...)` where `h` is itself a pair (compound head, e.g. `(MUL m)`), both functions iterate only over `(cdr expr)` and never touch `(car expr)`. A free variable in head position is invisible to free-vars and untouched by subst-free.
- **Witness**: `(free-vars '((MUL m) a b))` returns `(a b)` — `m` missing. Then for axiom `(FORALL m (FORALL a (FORALL b (= ((MUL m) a b) ((MUL m) b a)))))`, instantiating `m → r` rewrites no occurrence — every use of `m` is in head position. The "instance" is the original axiom unchanged, with `m` quietly retained.
- **Recommendation**: In both functions, recurse into `(car expr)` exactly as `alpha-equiv-under?` does.

### S-4. `VNB-LAMBDA` is not registered as a binder  ✓ FIXED 2026-05-15
- **Fix:** Added `vnb-lambda-bvars` helper to `expressions.scm` extracting the bound variable list from either single-var (`(VNB-LAMBDA i body)`) or multi-var (`(VNB-LAMBDA (LIST p q) body)`) form. Added explicit `VNB-LAMBDA` cases to: `free-vars` and `subst-free` (with capture avoidance — clashing bvars get fresh-renamed against the replacement) in `expressions.scm`; `alpha-equiv-under?` (allows cross-shape comparison `(VNB-LAMBDA x P) ~ (VNB-LAMBDA (LIST y) P[y/x])`); `walk-term` in `wff.scm`; `rewrite-expr` in `macetes.scm` (refuses to rewrite under a binder when any bvar coincides with a schema-var, otherwise recurses into body). Live axioms in `algebraic.scm` (RING-PROD), `complex.scm` (CC-RING/CC-MS), `sequences.scm` (sum-left-scalar) all use the symbolic form and are now properly bound.
- **Where**: `expressions.scm:165-189` (free-vars), `expressions.scm:245-294` (subst-free), `wff.scm:287-368` (walk-term), `macetes.scm:316-325` (rewriter else).
- **What**: `VNB-LAMBDA` is a binding form (used inside `algebraic.scm` `RING-PROD`, `complex.scm`, `sequences.scm` axioms — e.g. `(VNB-LAMBDA i ((MUL r) a (f i)))`), but appears in none of the binder-aware switches. It falls through to the generic else branch in subst-free, which substitutes blindly into the binding-list and body.
- **Witness**: `(subst-free 'i 99 '(VNB-LAMBDA i (+ i 1)))` → `(VNB-LAMBDA 99 (+ 99 1))` — binder corrupted. `(free-vars '(VNB-LAMBDA i ((MUL r) a (f i))))` reports `i` as free.
- **Recommendation**: Two paths. (a) Make the parser produce `<functoid>` records before any axiom is installed, so raw `VNB-LAMBDA` S-exprs never reach the kernel; or (b) add `VNB-LAMBDA` (and any sibling binders like `lambda`, `lambdoid` if they exist as raw heads) to a single canonical `*binder-heads*` table consumed by free-vars, subst-free, walk-term, alpha-equiv-under?, and the macete rewriter. (b) is the safer fix and converges with the suggestion in S-13 below.

### S-5. Macete `lc-extend` does not invalidate ctx assumptions when descending under a shadowing binder  ✓ FIXED 2026-05-15
- **Fix:** Added `lc-drop-shadowed bvars local-ctx` helper to `macetes.scm` (drops every assumption whose `free-vars` mention any of the bvars). Threaded through every binder descent in `rewrite-subexpressions`: FORALL/FORSOME/IOTA, SEP body (not domain), VNB-LAMBDA, and the functoid record body. Five regression tests added (test-suite.scm §5h): three for the helper directly, plus the audit's exact witness — installs `(FORALL y (IMPLIES (= y 0) (= (foo y) y)))` and applies it to `(IMPLIES (= x 0) (FORALL x (= (foo x) (g x))))`; expected #f (no rewrite under the shadowing FORALL); plus a control that verifies the same macete still fires when not shadowed. 225/225 tests pass (was 220).
- **Where**: `macetes.scm:157-169` (no-quantifier descent), `macetes.scm:306-313` (FORALL/FORSOME/IOTA descent).
- **What**: When the rewriter descends into `(FORALL bv body)`, the local-ctx is passed unchanged. Any assumption in local-ctx that mentions `bv` free is now reinterpreted as referring to the *new* bound `bv` — silently changing its semantics. The macete's `condition-holds?` then accepts a coincidentally-named match.
- **Witness** (from agent): Install `(FORALL y (IMPLIES (= y 0) (= (foo y) y)))` as an elementary macete. Goal: `(IMPLIES (= x 0) (FORALL x (= (foo x) (g x))))`. Descending into the consequent of IMPLIES adds `(= x 0)` to local-ctx. Descending into `FORALL x` keeps `(= x 0)` even though the inner `x` is fresh. Pattern-match binds `y → x`; substituted condition `(= x 0)` matches the (now-shadowed) ctx entry; rewrite fires and produces `(IMPLIES (= x 0) (FORALL x (= x (g x))))`. Premise about the *outer* x doesn't justify equating the *inner* x with `(g x)`.
- **Recommendation**: When descending under a binder, drop any local-ctx assumption whose `free-vars` include the binder; alternatively alpha-rename the binder to a globally fresh name before descending. The drop is simpler and conservative.

### S-6. `fresh-var` ignores ambient context and the substitution's replacement  ✓ FIXED 2026-05-15
- **Fix:** `fresh-var` is now variadic — `(fresh-var hint . avoid-exprs)` — and rejects any candidate appearing in `(free-vars e)` for any e in avoid-exprs. Updated all call sites: subst-free's four rename branches now pass `replacement`; `peel-foralls-raw` now takes an `ambient-avoids` parameter (threaded with accumulated bounds across peels — the S-14 fix); pi-direct-inference passes asms; pi-antecedent-inference's FORSOME branch passes goal+other-asms; pi-tfi and pi-tfi3 pass var+asms+goal. Two regression tests (test-suite.scm §6p): (a) `fresh-var` avoids free vars of every avoid arg; (b) the audit's exact witness — forces the counter so that without the fix `fresh-var` returns `y_42` and recaptures the replacement's `y_42`. 227/227 tests pass.
- **Where**: `expressions.scm:299-307`; callers at `expressions.scm:229,263,274` (subst-free) and `primitive-inferences.scm:41,150,577,610` (eigenvariable introduction in pi-direct-inference, pi-antecedent-inference FORSOME branch, pi-tfi, pi-tfi3, pi-nn-induction).
- **What**: `fresh-var` only checks the candidate against `(free-vars expr)` — typically just the body. It ignores: (a) the replacement term in `subst-free`'s rename-then-substitute branch, (b) the ambient sequent's assumptions and goal in primitive inferences. The global `*fresh-counter*` makes accidental clashes unlikely in practice but does not guarantee freshness.
- **Witness (subst-free)**: `(subst-free 'x '(+ y y_0) '(FORALL y x))` → `(FORALL y_0 (+ y y_0))` if the counter happens to land on `y_0` — captures the previously-free `y_0`.
- **Witness (eigenvariable)**: A sequent with a free `y_0` in its assumption list, plus a `pi-antecedent-inference!` on a FORSOME assumption: the introduced eigenvariable can collide with `y_0`, allowing one to derive contradictions involving that hypothesis.
- **Recommendation**: Pass the union of free vars of `asms`, `goal`, and (where applicable) the term/replacement into `fresh-var`. Best: refactor to `fresh-var-avoiding` taking a list of "avoid sets".

### S-7. `pi-theorem-assumption!` accepts an arbitrary formula as a "theorem"  ✓ FIXED 2026-05-15
- **Fix:** `pi-theorem-assumption!` now takes a theorem **name** (symbol) and looks up the formula in `*theorem-table*` itself, returning `#f` if the name is unknown. The cmd wrapper at `proof-commands.scm:178-182` is now a thin pass-through that turns a `#f` into a "unknown theorem" warning. Two regression tests (test-suite.scm §6q): kernel returns `#f` on a fresh nonexistent name; kernel succeeds on a known one. 229/229 tests pass.
- **Where**: `primitive-inferences.scm:344-351`. The cmd wrapper at `proof-commands.scm:178-182` does look up the registry, but the kernel layer is exposed.
- **What**: The kernel call adds an arbitrary S-expression to the sequent's assumptions with no consultation of the theorem registry and no theory-match check. Anyone calling `pi-*` directly (or any future scripting layer that does) can introduce `(NOT TRUTH)` and then derive anything.
- **Witness**: `(pi-theorem-assumption! sqn '(NOT TRUTH))` adds `(NOT TRUTH)` to the assumptions; refute with `pi-direct-inference!` to derive FALSITY.
- **Recommendation**: Take a theorem *name* (symbol) at the kernel layer; look it up and verify the theory matches the goal's theory. Make `cmd-theorem-assumption` a thin wrapper.

### S-8. `pi-functoid-beta!` performs sequential rather than parallel substitution  ✓ FIXED 2026-05-15
- **Fix:** `reduce-functoid-in-expr` now does parallel substitution by first renaming every binding variable to a globally-fresh name (chosen to avoid the body and ALL args), then substituting fresh-name → arg in any order — the freshness guarantees no later substitution can rewrite an earlier-substituted occurrence. One regression test (test-suite.scm §6r) using the audit's exact witness — `(lambda (x y) (LIST x y))` applied to `(y, 0)` now reduces to `(LIST y 0)` (correct), not `(LIST 0 0)` (sequential bug). 230/230 tests pass.
- **Where**: `primitive-inferences.scm:502-509`, in `reduce-functoid-in-expr`.
- **What**: Multi-arg functoid application reduces by `fold-left` of one substitution at a time. When a later parameter's value-expression coincidentally contains a name that an earlier substitution introduced, the later substitution rewrites those occurrences as well.
- **Witness**: Functoid `f = (lambda (x y) (LIST x y))`. Apply to `(y, 0)`. Sequential: subst `x:=y` gives `(LIST y y)`; then `y:=0` gives `(LIST 0 0)`. Correct (parallel) result is `(LIST y 0)`. So `pi-functoid-beta!` "proves" `(= (apply-functoid f y 0) (LIST 0 0))` when the true reduct is `(LIST y 0)` — an outright equational falsehood.
- **Recommendation**: Implement parallel substitution: rename all parameters to fresh names first, then substitute the args, then substitute fresh→params. Or use a single n-ary substitution primitive.

### S-9. `make-set-membership` quantifies over unbounded `i ∈ NN`  ✓ FIXED 2026-05-15
- **Fix:** Added the `1 ≤ i ∧ i ≤ LENGTH(L)` bounds to the existential, with explanatory comment in source. Updated the manual statement at `docs/ch-expressions.tex:355-356` to match. 227/227 tests pass; manual compiles clean.
- **Where**: `theory.scm:240-243`. Cross-referenced by manual `ch-expressions.tex:355-356`.
- **What**: `x ∈ MAKE-SET(L) ↔ ∃i ∈ NN. NTH(i, L) = x`. The bound `1 ≤ i ≤ LENGTH(L)` is missing. NTH out of range is unspecified; if it returns a sentinel `v`, then `v` is a member of every MAKE-SET — wrong.
- **Witness**: With `L = [a, b]` and NTH unspecified at `i=0` or `i=3`, the axiom permits any value to be claimed a member if it happens to coincide with NTH off-range.
- **Recommendation**: `(EXISTS i (AND (IN i NN) (AND (<= 1 i) (AND (<= i (LENGTH L)) (= (NTH i L) x)))))`. Update the manual line in lockstep.

### S-10. Schema variables in macete conditions but not in the source pattern can match coincidentally  ✓ FIXED 2026-05-15
- **Fix:** Added `theorem-rogue-schema-vars` helper and a check in `theorem->elementary-macete`. When any schema-var appears in conditions or replacement but NOT in source, emit a warning and return an INERT macete (always `#f`). The theorem stays registered in `*theorem-table*` and is usable via `(ta name)` + manual instantiation; only the unsound rewrite mode is suppressed. Three regression tests (test-suite.scm §6s).
- **Note:** **14 existing axioms in the codebase trip this check on load** (e.g. `equality-symmetry` written as `(IMPLIES (= a b) (= b a))` extracts source `b` and replacement `a` — `a` is rogue). They were silently producing unsound macetes before. Each now emits a one-line load-time warning so you can audit them. None of the test proofs depended on the unsound macete behavior — 233/233 still pass.
- **Where**: `macetes.scm:204-214` (`rewrite-expr`) plus construction in `make-elementary-macete`.
- **What**: `top-match` only binds schema-vars that appear in the source pattern. Schema-vars appearing only in `conditions` remain unbound after match; `apply-subst` leaves them as named symbols; `condition-holds?` then matches against any local-ctx assumption that happens to share the name.
- **Witness**: Install `(FORALL n (FORALL k (IMPLIES (IN k NN) (= (foo n) n))))`. Schema-vars `(n k)`, source `(foo n)`, conditions `((IN k NN))`, replacement `n`. Matching `(foo a)` binds `n → a`; `k` is unbound. Substituted condition `(IN k NN)`. If the user's local-ctx happens to contain `(IN k NN)` for some unrelated `k`, the rewrite fires.
- **Recommendation**: At `theorem->elementary-macete` time, error out when `free-vars(conditions) ⊄ free-vars(source) ∪ globally-bound`. (Or extend the pattern algorithm to require that condition-only vars be matched somewhere.)

### S-11. `power-typing-nonneg`: curried/uncurried convention mismatch  ✓ FIXED 2026-05-15
- **Fix:** Replaced `(IN power (FUN (CARTESIAN CC NN) CC))` with the closure form `∀x∀n. (x∈CC ∧ n∈NN) → (power x n)∈CC`, matching the actual two-argument application syntax used in `power-zero`/`power-succ` and the user-facing infix `x ^ n`. Manual `ch-math.tex:65-68` updated.
- **Where**: `number-systems.scm:430` (typing) vs `power-zero`/`power-succ` recursion equations at `:438-446`.
- **What**: The typing axiom declares `power ∈ FUN(CARTESIAN(CC, NN), CC)` — a function on pairs. The recursion equations write `(power x 0)`, `(power x (succ n))` — two-argument applications. If `power` is genuinely curried, the typing should be `power ∈ FUN(CC, FUN(NN, CC))`. If it takes a pair, the call sites are not well-formed.
- **Recommendation**: Pick one convention and align typing axiom + recursion equations.

### S-12. Possible soundness issue: `case` dispatch on compound heads in subst-free / free-vars  ✓ FIXED 2026-05-15
- **Fix:** Subsumed by S-3 fix — the else-branch fall-through for compound heads now recurses correctly.
- **Where**: `expressions.scm:166, 246`.
- **What**: When `(car expr)` is a pair, `case` falls through to `else`. Combined with the else-branch failing to recurse into the head (S-3), this is the *mechanism* by which compound heads escape rewriting. Same root cause as S-3; mention here so the fix touches both sites.
- **Recommendation**: Handle compound-head case explicitly before the `case` form.

### S-13. `walk-term` accepts unknown binders as ordinary applications  ✓ FIXED 2026-05-15
- **Fix:** Added explicit `VNB-LAMBDA` case to `walk-term`; the else-branch for general compounds now also walks the head when it's a pair, so symbols inside a compound head are tracked. The deeper recommendation (canonical `*binder-heads*` table) is deferred — it would require touching parser, matcher, and several other consumers; no concrete benefit until a new binder is added.
- **Where**: `wff.scm:362-366`.
- **What**: The "wff-only heads" rejection list catches the standard logical operators, but `VNB-LAMBDA`, `lambda`, `lambdoid` (as raw symbols, not records) — and any future binder a developer adds — are silently treated as ordinary function applications. The "domain expression" or "body" gets walked as a term with no scoping established. `validate-wff!`'s bound/free warnings become unreliable.
- **Recommendation**: Maintain a single canonical `*binder-heads*` table consumed by `free-vars`, `subst-free`, `walk-term`, `alpha-equiv-under?`, and the macete rewriter. Adding a binder becomes a one-line change. Converges with the fix for S-4.

### S-14. `peel-foralls-raw` reuses the eigenvariable strategy across multiple peels  ✓ FIXED 2026-05-15
- **Fix:** Subsumed by S-6 fix — `peel-foralls-raw` now accepts and threads `ambient-avoids`, plus the recursion appends each peel's accumulated `added` bounds into the avoid list for subsequent peels.
- **Where**: `primitive-inferences.scm:37-51`.
- **What**: Each peel calls `(fresh-var x body)` against the residual body only — not against earlier-peeled `y`s or against `asms`/`goal`. Same root cause as S-6.
- **Recommendation**: Thread a "must-avoid" set through `peel-foralls-raw` containing previously chosen `y`s plus the sequent's free vars.

### S-15. `cc-self-conj-nonneg` uses real `<=` on a complex expression  ✓ FIXED 2026-05-15
- **Fix:** Now states `(AND (IN (* a (conjugate a)) RR) (<= 0 (* a (conjugate a))))` — bundles the realness fact (was a separate lemma `cc-self-conj-real`) with the inequality, so `<=` is unambiguously over RR.
- **Where**: `number-systems.scm:383`.
- **What**: `∀a∈CC. 0 ≤ a · conjugate(a)`. Sound only if `<=` is the real-restricted order and `a · conj a` is known to land in RR. `cc-self-conj-real` provides the latter; `<=` semantics on CC is not declared.
- **Recommendation**: Either declare `<=` as a RR-only relation, or add an `≤` typing axiom.

---

## 2. CORRECTNESS / KERNEL-INVARIANT findings

### C-1. Several `pi-*` accept unvalidated raw S-expressions  ✓ FIXED 2026-05-15
- **Fix:** `pi-cut!` now calls `validate-wff!` on the lemma before wrapping. `pi-instantiate!` and `pi-exists-witness!` validate the substituted result (`(subst-free x term body)`), which catches malformed terms via the embedded position. Malformed inputs now produce a kernel-level error instead of a malformed sequent that surfaces deeper in the proof.
- **Where**: `primitive-inferences.scm:178-187` (cut), `:192-206` (instantiate), `:211-222` (exists-witness), and S-7 above for theorem-assumption.
- **What**: User-supplied lemmas/terms/formulas are wrapped via `wff-child` (no validation) instead of `make-wff`. Garbage inputs yield malformed sequents; downstream behaviour is unpredictable, sometimes silently accepting, sometimes erroring deep inside another rule.
- **Recommendation**: Route user formulas/terms through `make-wff` / term validators before wrapping.

### C-2. `pi-cartesian-elim!` length-check misses arity mismatch  ✓ FIXED 2026-05-15
- **Fix:** Added `(= (length elems) (length sets))` precondition; now refuses cleanly when the tuple length doesn't match the CARTESIAN arity.
- **Where**: `primitive-inferences.scm:386-388`.
- **What**: Checks `k ≤ (length elems)` but not `(length elems) = (length sets)`. Asymmetric: in some cases it errors, in others vacuous-falsity behaviour leaks through.
- **Recommendation**: Require equal length; reject otherwise.

### C-3. `vnb-guard` assumes `condition/report-string` succeeds on any raised value  ✓ FIXED 2026-05-15
- **Fix:** Handler now checks `(condition? exn)` first; non-condition raises produce a generic message via `write` rather than themselves erroring inside the handler.
- **Where**: `errors.scm:42-45`.
- **What**: A user-level `(raise <non-condition>)` would land in `condition/report-string` and itself error inside the handler. Continuable conditions cannot be allowed to continue (the call/cc escape commits to non-continuation).
- **Recommendation**: Add a `(condition? exn)` guard before calling `condition/report-string`; emit a generic message for non-condition raises.

### C-4. `validate-wff!` block comment references the removed schematic/concrete distinction  ✓ FIXED 2026-05-15
- **Fix:** Stripped the obsolete schematic/concrete comment lines.
- **Where**: `wff.scm:233-238`.
- **What**: Comment claims the validator tracks `saw-schematic?`/`saw-concrete?` and returns 'concrete or 'schematic. Per memory, schematic was eliminated 2026-05-08; the comment is dead.
- **Recommendation**: Delete the obsolete comment.

### C-6. Typo: `vnb--require-proof` (without `!`) called in three places  ✓ FIXED 2026-05-15
- **Where**: `interactive.scm:149, 169, 184` — `(focus n)`, `(qed name)`, `(replay-proof name)`.
- **What**: These called `vnb--require-proof` but the function is defined as `vnb--require-proof!` (`interactive.scm:61`). The bug was masked by `vnb-guard` swallowing the unbound-variable error and reporting it as a vnb-error rather than crashing — so `(qed)` would silently no-op rather than installing the theorem. Surfaced when writing the S-2 regression test.
- **Fix:** All three call sites now use `vnb--require-proof!`.

### C-5. `*wff-term-form-heads*` and `*wff-only-heads*` lists are incomplete  ✓ FIXED 2026-05-15
- **Fix:** Populated `*wff-term-form-heads*` with the missing entries (TUPLES, succ_ORD, LIMIT-ORD, ORD-SEGMENT, SUP-ORD, RING-PROD, RING-PROD-N, PROD-ORD, SUM, CARD, ZERO-RING, VNB-LAMBDA, COMPLEMENT-IN, exp/sin/cos/real-part/imag-part/magnitude). Now category errors are caught earlier.
- **Where**: `wff.scm:219-226`.
- **What**: Missing many term-forming heads (`TUPLES`, `succ_ORD`, `LIMIT-ORD`, `ORD-SEGMENT`, `SUP-ORD`, `RING-PROD`, `RING-PROD-N`, `PROD-ORD`, `SUM`, `CARD`, `ZERO-RING`, `VNB-LAMBDA`, percent constants). Not a soundness hole because walk-term recognises some of them via other paths, but the lists' invariants are misleading.
- **Recommendation**: Either populate fully or drop and rely on dispatch.

---

## 3. MANUAL / SOURCE DRIFT

### D-1. Phantom FUN axioms in the manual  ✓ FIXED 2026-05-15
- **Fix:** Replaced the phantom names with the actual installed ones: `fun-domain-apply-def`, `fun-domain-extensionality`, `fun-codomain-iff`, `fun-apply-type` (in axioms.scm; derivable), `fun-set-iff`, `fun-elements-are-sets`, `fun-domain-elements-are-sets`. Dropped the `fun-monotone` claim (no such axiom installed). Added an intro sentence explaining the unary-vs-binary `FUN` relationship.
- **Where**: `docs/ch-expressions.tex:504-513`.
- **What**: Lists `fun-apply-def`, `fun-apply-in`, `fun-extensionality`, `fun-monotone` as installed. None of those names exist in source. Actual axioms: `fun-domain-apply-def`, `fun-codomain-iff` (subsumes `fun-apply-in`), `fun-domain-extensionality`, `fun-apply-type` (in `axioms.scm:58`). And `fun-monotone` is asserted in passing on line 304 but never installed anywhere.
- **Recommendation**: Rename to actual names; either add `fun-monotone` to the source or drop the claim.

### D-2. Single-argument `FUN(A)` form is undocumented  ✓ FIXED 2026-05-15
- **Fix:** Rewrote the `fun(A,B)` bullet to introduce both the unary `fun(A)` and binary `fun(A,B)` forms, including the relationship `fun(A,B) = {f ∈ fun(A) : ∀x∈A. f(x)∈B}` and the sethood asymmetry.
- **Where**: `docs/ch-expressions.tex:300-303`.
- **Recommendation**: Add a paragraph to §3.4.

### D-3. `def-by-ord-recursion` example signature wrong  ✓ FIXED 2026-05-15
- **Fix:** Replaced the 3-arg example with a correct 6-arg form (name, base, succ-spec, succ-expr, lim-spec, lim-expr) plus a paragraph explaining the bound-name convention. Comments document the three resulting axioms.
- **Where**: `docs/ch-defs.tex:670-677`.
- **What**: Example shows three arguments; source `ordinals.scm:250` defines six (`f-name base-val succ-spec succ-expr lim-spec lim-expr`). The example as written errors.
- **Recommendation**: Rewrite to match the source signature; mirror the working `COPY-ORD` example earlier in the same chapter.

### D-4. Wrong short-form names in worked example  ✓ FIXED 2026-05-15
- **Fix:** `(ol)` → `(oi-l)`, `(ref)` → `(rfl)`.
- **Where**: `docs/ch-proofs.tex:756-757`.
- **What**: Uses `(ol)` and `(ref)`. Actual names: `(oi-l)` (`interactive.scm:108`) and `(rfl)` (`interactive.scm:106`). Example crashes with "Unbound variable".
- **Recommendation**: `s/ol/oi-l/`, `s/ref/rfl/`.

### D-5. `(bc 'theorem-name)` doesn't work as written  ✓ FIXED 2026-05-15
- **Fix:** Updated `test-suite.scm:524-535` (bc test) — now uses `(ta 'nn-add-closed)` + two `(inst ...)` peels + `(bc <formula>)` + assumptions; added `proof-done?` check at the end so the test catches incomplete proofs (the original silently passed because `check-proof` only verifies no-exception). The manual line 358 the audit pointed to actually contains tfi3 not bc; the bc pattern was only in the test-suite. **Latent bug found:** `check-proof` doesn't verify completion — many tests may "pass" even if their proofs fail to close. Out of scope to retrofit all tests.
- **Where**: `test-suite.scm` (originally `:487`, now `:524`).
- **What**: `pi-backchain!` (`primitive-inferences.scm:272`) requires the argument to be an implication formula already in the assumption list. A bare theorem-name symbol matches nothing; the command silently warns and no-ops. Correct usage: `(ta 'nn-add-closed)` first, then `(bc <formula>)`.
- **Recommendation**: Rewrite the example.

### D-6. `COMPLEMENT-IN`, n-ary `UNION`/`INTERSECTION`/`CARTESIAN` promised in manual but missing in source  ✓ FIXED 2026-05-15
- **Fix:** Validator now accepts n-ary `UNION`/`INTERSECTION` (`wff.scm:309-321`, ≥ 2 args); n-ary semantics in proofs is provided by the pre-existing kernel rules `pi-union-intro!`/`-elim!` and `pi-intersection-intro!`/`-elim!` (which were already n-ary). `COMPLEMENT-IN` installed as a binary constructor: added `make-complement-in` (`expressions.scm:106`); arms in `free-vars`/`subst-free`/`alpha-equiv-under?` (`expressions.scm:190-193,287-290,427-429`); validator arm in `wff.scm:316-321`; matcher arm in `macetes.scm:82-86`; rewriter arm in `macetes.scm:281-285`. Four new axioms in `theory.scm:294-329`: `union-membership` (binary IFF), `intersection-membership` (binary IFF; was previously only kernel-rule), `complement-in-set-closure` (`A∈SET → A\B ∈ SET`), `complement-in-membership` (`x∈A\B ↔ x∈A ∧ ¬(x∈B)`). Manual `ch-expressions.tex:277-296` updated. CARTESIAN was already n-ary in the validator and via `pi-cartesian-elim!`; `cartesian-set-iff` remains binary (n-ary sethood follows by induction). 12 regression tests added (test-suite.scm §6t). 245/245 tests pass.
- **Bonus fix surfaced:** Unary `(FUN A)` (the primary form per `theory.scm:187`) used to crash the binary-FUN dispatch in `free-vars`/`subst-free`/`alpha-equiv-under?`/`match-expr`/`rewrite-subexpressions`. Four axioms — `fun-domain-elements-are-sets`, `fun-domain-apply-def`, `fun-domain-extensionality`, `fun-codomain-iff` — silently failed to install their macetes (vnb-guard caught the car-of-() error and the theorem still registered, so usage via `(ta name)` worked but the macete form did not). Now both arities (2 and 3) are handled uniformly. The macetes now install and the underlying S-10 issue surfaces correctly as rogue-schema-var warnings (the symbol heads `f`/`g` look like schema-vars when extracted from rewrite patterns; same family as S-3, downstream concern). 10 additional regression tests added (test-suite.scm §6u). 255/255 tests pass total.
- **Where**: Manual `docs/ch-expressions.tex:281-291`; source: `expressions.scm:104` only has unary `(COMPLEMENT a)`; `wff.scm:310-313` requires `UNION`/`INTERSECTION` to be binary; `cartesian-set-iff` (`theory.scm:224`) is binary only although the validator accepts n-ary.
- **Recommendation**: Choose one direction. Either install n-ary axioms (UNION-membership, n-ary CARTESIAN-membership, COMPLEMENT-IN) and relax the validator, or update the manual to match the binary-only reality.

### D-7. Several functoids have NO defining axioms  ✓ FIXED 2026-05-15
- **Fix:** Installed kernel-level characterizations (the body formula `p`/`body` is a genuine schema and can't appear cleanly in a FOL axiom, so kernel rules are the soundness-preserving form). Added 7 new pi-* rules in `primitive-inferences.scm:747-963` plus cmd wrappers in `proof-commands.scm:396-455` plus short-form names + replay dispatch in `interactive.scm`:
  - **SEP** (separation): `pi-sep-sethood!` (goal `(IN (SEP x A p) SET)` → subgoal `(IN A SET)`); `pi-sep-mem-intro!` (goal `(IN y (SEP x A p))` splits into `(IN y A)` and `p[x:=y]`); `pi-sep-mem-elim!` (assumption form). Short forms `(sep-set)`, `(sep-mi)`, `(sep-me ...)`.
  - **COMP** (class comprehension): `pi-comp-mem-intro!` (goal `(IN y (COMP x p))` splits into `(IN y SET)` and `p[x:=y]`); `pi-comp-mem-elim!` (assumption form). Short forms `(comp-mi)`, `(comp-me ...)`.
  - **IOTA** (definite description): `pi-iota-def!` (takes an `(IOTA x p)` term; posts the existence-uniqueness obligation `FORSOME-UNIQUE x p` plus the original goal augmented with `p[x := IOTA x p]` as an assumption). Short form `(iota-d ...)`.
  - **VNB-LAMBDA**: `pi-lambda-type!` (single-binder shape — goal `(IN (VNB-LAMBDA x body) (FUN A B))` reduces to `(FORALL x (IMPLIES (IN x A) (IN body B)))`, with x renamed fresh against asms+goal+A+B+body); `pi-lambda-beta!` (parallel-substitution beta reduction of `((VNB-LAMBDA x body) arg ...)` anywhere in goal, both single and multi-binder shapes). Short forms `(lam-t)`, `(lam-b)`.
- **2-arg POWER**: installed `power-exp` axiom in `axioms.scm:99-101`: `(FORALL A (FORALL B (= (POWER A B) (FUN B A))))` — A^B = functions B→A, matching `power(2,3)=2^3=8` (functions from a 3-set to a 2-set). Sethood + membership inherit from `fun-set-iff` / `fun-codomain-iff`.
- `axioms.scm:1-25` pending-list comment updated to reflect what's now installed (separation, comp-membership, iota-def, lambda-type, lambda-beta, power-exp removed; equality-substitution, union-set, infinity, tuples-induction, prepend remain pending).
- Manual `ch-expressions.tex:318-348` rewritten for SEP/COMP/POWER to point to the kernel rules; `ch-expressions.tex:405-414` rewritten for IOTA; `ch-expressions.tex:424-449` rewritten for VNB-LAMBDA explaining the record-vs-symbolic distinction. 73 pages compile clean (was 71).
- 15 regression tests added (test-suite.scm §6v): pi-sep-{sethood, mem-intro, mem-elim}; pi-comp-{mem-intro, mem-elim}; pi-iota-def; pi-lambda-type; reduce-lambda-in-expr (incl. parallel-substitution test analogous to S-8); power-exp axiom installed + macete fires. **270/270 tests pass total (was 255 → +15).**
- **Where**: `axioms.scm:8` (`separation` pending), `:11` (`comp-membership` pending), `:15-16` (`lambda-type`, `lambda-beta` pending), `:17` (`iota-def` pending). Validator accepts 2-arg `(POWER A B)` (`wff.scm:325-331`) but no axiom relates it to FUN exponentiation.
- **What**: `SEP`, `{x|p}`, `IOTA`, `VNB-LAMBDA`, 2-arg `POWER` are syntactic husks — total in form, semantically empty. The manual's "constructors are total functoids" claim invites users to think they carry axiomatic content; they don't.
- **Recommendation**: Until axioms exist, either flag these heads in the validator with a "pending" warning, or install at least skeletal characterising axioms. (`SEP` is the most urgent — separation is basic.)

### D-8. IS-NAME structure axiom uses `(SET (A s))`, not `(IN (A s) SET)`  ✓ FIXED 2026-05-15
- **Fix:** `structures.scm:70` now emits `(IN (acc ivar) SET)` (membership form), matching the manual's categorical statement that there is no `SET(_)` predicate.
- **Where**: `structures.scm:71`.
- **Recommendation**: Change the source to emit `(IN (acc ivar) SET)` (preferred), or correct the manual.

### D-9. `def-structure` vs `declare-structure`  ✓ FIXED 2026-05-15
- **Fix:** `ch-source.tex:27-30` now mentions both — `declare-structure` (user-facing macro) and `def-structure` (lower-level).
- **Where**: `docs/ch-source.tex:28-29`.
- **Recommendation**: Update `ch-source.tex` to mention the macro.

### D-10. `FORSOME-UNIQUE` referenced but doesn't exist  ✓ FIXED 2026-05-15
- **Fix:** Replaced the `FORSOME-UNIQUE` reference with the explicit FORSOME+FORALL expansion plus a parenthetical note that a `FORSOME-UNIQUE` macro abbreviation is planned.
- **Where**: `docs/ch-expressions.tex:378`.
- **What**: Per project memory, FORSOME is the only existential. Either add a footnote that FORSOME-UNIQUE would be an abbreviation `(FORSOME x (AND p (FORALL y (IMPLIES p[x:=y] (= x y)))))`, or replace the example.

### D-11. Removed feature still referenced  ✓ FIXED 2026-05-15
- **Fix:** Stale `<schematic-wff>` comment was already removed as part of C-4. Orphan `make-complement` removed in housework pass: deleted the constructor in `expressions.scm:106`, dropped `COMPLEMENT` from `term?` (`expressions.scm:84-87`), `free-vars` / `subst-free` / `alpha-equiv-under?` (`expressions.scm:188,288,435`), `*wff-term-form-heads*` and `walk-term` (`wff.scm:222,329`), and `match-expr` / `rewrite-subexpressions` (`macetes.scm:71,286`). Absolute complement was never used after `COMPLEMENT-IN` replaced it; its kernel scaffolding was dead code. 270/270 tests still pass.
- The orphan `make-complement` in `expressions.scm:104` (one-arg complement) has no manual mention but is still in source as dead code.
- `<schematic-wff>` only survives as a stale comment in `wff.scm:235`.

---

## 4. REDUNDANCIES (axioms derivable from others)  ✓ ANNOTATED 2026-05-15

All entries below now carry an inline `;;; DERIVED (REVIEW.md R-N): ...` comment at their definition site naming the axioms they reduce to. None were removed — they remain installed as named lemmas for direct use; the comments serve as a checklist for eventual demotion to proven theorems. No semantic change. Tests: 270/270 pass.

These are not bugs; flagged so you can decide which to keep as named lemmas vs. delete. Most are worth keeping with a comment that they are derived.

| Axiom | Where | Derivable from |
|---|---|---|
| `monoid-identity-in` | `algebraic.scm:69` | Auto-generated `IS-MONOID` IFF (`(constant E A)` clause) |
| `ring-zero-in` | `algebraic.scm:209` | Auto-generated `IS-RING` IFF |
| `ring-carrier-closed-add` | `algebraic.scm:213` | `IS-RING` IFF + `fun-apply-type` |
| `monoid-carrier-closed-mul` | `algebraic.scm` (analogue) | `IS-MONOID` IFF + `fun-apply-type` |
| `equality-symmetry`, `equality-transitivity` | `axioms.scm:22, 26` | Reflexivity + Leibniz substitution (if Leibniz is primitive) |
| `eq-subst-membership` | `axioms.scm:69` | Leibniz subst with `λx. (IN x S)` |
| `fun-apply-type` | `axioms.scm:58` | `fun-codomain-iff` |
| `list-sethood` | `axioms.scm:81` | `membership-implies-sethood` |
| `prod-ord-type`, `sum-type`, `ring-prod-n-is-ring` | `sequences.scm:28, 65, 102` | NN induction + closure axioms (already noted as TODO) |
| `prod-ord-singleton`, `sum-singleton` | `sequences.scm:40, 75` | `*-succ` at 0 + `*-zero` + identity laws |

`ring-prod-is-ring` (`algebraic.scm:249`) and `zero-ring-is-ring` (`:270`) are *provable* from the construction + `IS-RING` IFF but require expanding lambda bodies and verifying ring axioms — defensible to keep as axioms, eventually derive.

---

## 5. DESIGN / DOCUMENTATION notes

### G-1. `lc-extend` for OR is asymmetric (completeness only, not soundness)  ✓ FIXED 2026-05-15
- **Fix:** `macetes.scm:163-175` now adds the symmetric assumption: descending into the LEFT disjunct of `(OR A B)` adds `(NOT B)`, descending into the RIGHT disjunct adds `(NOT A)`. Previously only the right side got its assumption — a completeness gap; both directions are sound. 270/270 tests still pass (no regressions from the new context entries).
- **Where**: `macetes.scm:165-168`.
- **What**: Right disjunct of `(OR A B)` gets `(NOT A)`; left disjunct gets nothing. Symmetric move would be sound: when descending into the left, add `(NOT B)`.
- **Recommendation**: Add the symmetric case. Cheap improvement.

### G-2. CARD on a proper class is silently uncharacterised  ✓ FIXED 2026-05-15
- **Fix:** Added a `\begin{remark}` block to `docs/ch-defs.tex:704-714` documenting the convention: `CARD` is total over all classes but characterised only when its argument is a set; equational uses on proper classes will not discharge.
- **Where**: `cardinality.scm:13-16`. `card-in-ord` is conditional on `(IN A SET)`.
- **What**: `(CARD BONGO)` is a syntactically well-formed term with no axiom. Consistent with the totality framing, but no formal expression of "undefined" exists.
- **Recommendation**: Document the convention in the manual's CARD bullet.

### G-3. `choice-axiom` is global choice, not just AC  ✓ FIXED 2026-05-15
- **Fix:** Added a multi-line comment at `theory.scm:177-182` documenting that this is global choice in the NBG/Bourbaki sense (A ranges over all classes, including proper classes), strictly stronger than ZFC-AC.
- **Where**: `theory.scm:169`.
- **What**: `∀A. (∃x∈A) → CHOICE(A) ∈ A` ranges A over all classes — including proper classes. So `CHOICE(ORD) ∈ ORD` is asserted. This is global choice (NBG-style), stronger than ZFC-AC.
- **Recommendation**: Add a comment to that effect.

### G-4. `nn-induction` exists as both axiom and primitive inference  ✓ FIXED 2026-05-15
- **Fix:** Updated the `(ni)` entry in `docs/ch-proofs.tex:348-358` to clarify: the kernel rule `pi-nn-induction!` is self-contained and the named axiom `nn-induction` (in `number-systems.scm`) coexists as a redundant convenience for direct use via `(ta 'nn-induction)`.
- **Where**: `number-systems.scm:94` (axiom), `primitive-inferences.scm:634` (`pi-nn-induction!`).
- **What**: They coexist consistently; the primitive is self-contained, not a reduction-via-axiom. Worth a one-sentence note in the manual that `(ni)` invokes the primitive and the axiom is a redundant convenience.

### G-5. `def-by-nn-recursion` / `def-by-ord-recursion` install equations as definitions
- **Where**: `ordinals.scm:225-227, 250, 287`.
- **What**: These treat the recursion theorem as an admissible definition principle (commented as such). Sound modulo trusting the underlying recursion theorem; the substitution machinery (`subst-free`) is capture-avoiding so no bound-variable problems. Step-function partiality is silently accepted.

### G-6. `RING-PROD-N` builds tuples from `RING-PROD val (f n)` even when `f n` isn't a ring  ✓ FIXED 2026-05-15
- **Fix:** Added a documentation paragraph at `sequences.scm:97-104` explaining: when the hypothesis "all f(i) are rings" fails, the resulting term is still a syntactically well-formed 6-LIST whose components may be junk; soundness is preserved because `ring-prod-n-is-ring` then doesn't apply (its IS-RING antecedent is false), so no false ring identity can be derived from the junk. Users should not destructure RING-PROD-N(f, n) without first proving the hypothesis.
- **Where**: `sequences.scm:97`. `ring-prod-n-is-ring` (`:102`) hypothesises that all `f i` are rings.
- **What**: When the hypothesis fails the result is a 6-LIST whose components may be junk — soundness preserved (the typing claim simply doesn't apply). Worth a comment.

### G-7. `validate-wff!` accepts 2-arg `POWER` but no axiom covers it  ✓ FIXED 2026-05-15
- **Fix:** Subsumed by D-7. The `power-exp` axiom `(POWER A B) = (FUN B A)` is now installed in `axioms.scm:99-101`.
- **Where**: `wff.scm:325-331`.
- **What**: Either install `power-exp` axiom or reject 2-arg `POWER` at validation time. Same shape issue as D-6 for n-ary UNION.

### G-8. `*fresh-counter*` is a global mutable state  ✓ FIXED 2026-05-15
- **Fix:** Added a 9-line block comment immediately above `*fresh-counter*` (`expressions.scm:359-367`) explicitly stating the MONOTONICITY INVARIANT: never reset, even by snapshot/restore fixtures or REPL state resets, since this is the implicit safety net behind S-6 and S-14.
- **Where**: implicit in `expressions.scm`.
- **What**: Not a bug today; flagged because it's the implicit safety net behind S-6/S-14. If anything ever rolls the counter back (testing fixtures, snapshot/restore), the freshness guarantee evaporates. Consider documenting that the counter is monotonic and never reset.

### G-9. Pending manual tasks (per project memory)
- Transfinite recursion props 2.1 & 2.2 in `ch-math.tex` could move to `ch-defs.tex:106-142` adjacent to `def-by-ord-recursion`.
- §6 of `ch-proofs.tex` lacks a self-contained `(mac)` example closing a goal in 2-3 lines.

### G-10. `card-insert` uses raw `PAIR(x,x)` instead of `make-set([x])`  ✓ ANNOTATED 2026-05-15
- **Note:** Added an inline comment at `cardinality.scm:29-33` flagging the cosmetic inconsistency and noting the rewrite path (would need verifying that the equational change doesn't perturb existing card-insert proofs). Not a fix per se — the existing axiom is sound; the comment serves as a TODO for a future cleanup pass.
- **Where**: `cardinality.scm:32`. `ch-defs.tex:707` notes the equivalence.
- **What**: Cosmetic; the rest of the manual writes singletons as `make-set([x])`.

---

## 6. LaTeX hygiene  ✓ FIXED 2026-05-15

- **Clean compile**: no undefined refs, no missing labels, no math-mode errors.
- **Overfull boxes** worth fixing:
  - `ch-proofs.tex:424-429` (67.5pt)  — **fixed**: rewrote the long parenthetical-of-command-names into a `\begin{quote}...\end{quote}` list so the line wraps naturally.
  - `ch-proofs.tex:985` (119pt) — **fixed**: split the `(let* ((mem-node ...)))` snippet by extracting `dg` into its own binding so each line stays under the verbatim width.
  - `ch-proofs.tex:780-787` (57pt) — **fixed**: split the `; nn-add-closed:` comment header onto separate lines.
  - Bonus: also split long `(ta 'monoid-carrier-closed-mul)`, `(ta 'fun-apply-type)`, `(ta 'prod-ord-succ)` macete-tutorial snippets and the long `;; n_k is (cadr ...)` comment for the same readability reason.
- **Hyperref unicode warnings** in section titles with `$...$` — **fixed**: wrapped both math-mode section titles in `\texorpdfstring{...}{...}`:
  - `app-tests.tex:410` — `\section{Arithmetic in $\mathbb{Z}$, ...}` → `\section{Arithmetic in \texorpdfstring{$\mathbb{Z}$, ...}{Z, ...}}`.
  - `ch-proofs.tex:863` — `\subsection{$\beta$-reduction with \texttt{(beta)}}` → `\subsection{\texorpdfstring{$\beta$}{beta}-reduction with \texttt{(beta)}}`.
  - Now only one residual `Token not allowed` warning remains (an internal `\@ifnextchar` from hyperref itself, unrelated to our content).
- **Broken VNBcode example**: `ch-defs.tex:50-51` `omega1-is-least-unc` — **fixed**: moved the missing `)` from outside the string to inside (it now closes the `forall(...)` correctly).
- Manual still 73 pages, compiles clean.

---

## 7. Verified clean

These items were specifically checked and look correct:

- `alpha-equiv-under?` compound-head branch (`expressions.scm:381-389`) handles nested compound heads `(((F x) y) z)` correctly via recursion at line 384.
- `expand-destructuring-quantifiers` tuple case (`wff.scm:125, 179`) chooses a fresh `t` against `class`, `body`, and `vars`.
- The FORALL/FORSOME/IOTA/SEP capture-avoidance branches in `subst-free` (`expressions.scm:262-267, 273-281`) DO trigger when `bv ∈ free-vars(replacement)`. The remaining gap is the fresh-name-vs-replacement issue (S-6).
- Compound-head printer (`sequents.scm:234-242`) round-trips with the parser's chained `p-maybe-apply` (`parser.scm:443-454`) for nested cases.
- No live dispatch on a `'schematic` kind in any reviewed file.
- `pi-direct-inference`, `pi-or-intro-{left, right}`, `pi-truth`, `pi-reflexivity`, `pi-quasi-reflexivity`, `pi-assumption`, `pi-backchain` direction, `pi-contraposit` direction, `pi-proof-by-contradiction`, `pi-tuples-{intro, elim}`, `pi-nth-reduce`, `pi-union-{intro, elim}`, `pi-intersection-{intro, elim}` — all clean modulo the cross-cutting issues above.
- `make-elementary-macete`'s `local-ctx` seeding from current sequent assumptions (`macetes.scm:369-389`) is not stale.
- `appl-macete` seeds `local-ctx` as `'()` — conservative and sound.
- `card-union-disjoint` disjointness side-condition is correctly stated (`cardinality.scm:71`).
- Transfinite induction principle in the manual (`ch-math.tex:273-279`) matches `ordinals.scm:203-212` exactly.
- NN-induction step in manual (`ch-proofs.tex:351-354`) matches `pi-nn-induction!`.
- `pdflatex` runs cleanly on first pass.

---

## 8. Suggested fix order

A defensible order if you triage one bongo at a time:

1. **S-1** (pairing) — one-line axiom change. Highest impact for least work.
2. **S-2** (cmd-qed drops assumptions) — small fix; high-impact correctness gate on every `qed`.
3. **S-3 + S-12** (compound heads in subst-free / free-vars) — single root cause; recurse into `(car expr)`.
4. **S-4 + S-13** (VNB-LAMBDA not a binder) — introduce `*binder-heads*` table; routes through five functions.
5. **S-5** (lc-extend under shadowing binder) — drop ctx assumptions whose free-vars include the binder.
6. **S-6 + S-14** (fresh-var ignores ambient context) — refactor to `fresh-var-avoiding`.
7. **S-9** (make-set-membership unbounded `i`) — add `1 ≤ i ≤ LENGTH(L)`.
8. **S-7** (pi-theorem-assumption registry check) — kernel-boundary cleanup.
9. **S-8** (pi-functoid-beta parallel subst) — replace fold with simultaneous substitution.
10. **S-10** (schema vars only in conditions) — add a check at `theorem->elementary-macete`.

After the soundness queue: D-1 through D-11 (manual drift), C-1 through C-5 (correctness/kernel hygiene), then redundancies and design notes at leisure.

---

*End of review. ~30 distinct findings, of which ~15 are soundness-class. The framework is well-organised and the underlying design is coherent; the bongos cluster around (a) substitution machinery's incomplete coverage of compound heads and binders, (b) `lc-extend` not respecting binder scope, (c) the kernel-API surface accepting raw S-expressions in places where `make-wff` validation should mediate. Each is a localised fix; none requires architectural change.*
