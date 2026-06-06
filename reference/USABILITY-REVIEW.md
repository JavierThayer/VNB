# VNB Proof Checker — Usability Review (2026-05-16)

**Scope.** Practical recommendations to lower the learning curve.
*Not* a soundness audit (see `REVIEW.md` for the prior soundness pass).

**Format.** Numbered recommendations grouped by theme.  Each carries
a difficulty tag:

- **[Q]** Quick win — paragraph-sized doc edit, hours of code, or a tiny new helper.
- **[M]** Medium — half-day to a few days of focused work.
- **[L]** Long-term — design effort, multi-week.  Park unless prioritized.

The user is the *sole* user today.  "Beginner" below means *any future
collaborator* who hasn't lived inside this codebase for weeks — not a
hypothetical first-year student.

---

## 1. Manual ordering and onboarding path

**The current path through the manual:**

> Intro → Expressions → Math content → Definitions → Proofs → Syntax → Source → Tests

A first-time reader spends four chapters on language and ontology before
seeing a single complete proof.  The Quick Start (§1.3) shows
installation and the Emacs interface but stops short of walking through
*a worked proof end-to-end*.

### Recommendations

1. **[Q]** Move **`ch-syntax` (local contexts) before `ch-proofs`**.
   Local contexts are a prerequisite for `sp`/`qed` — they currently
   appear *after* the chapter that uses them.  The order
   *Intro → Expressions → Syntax → Proofs → Math → Definitions → Source*
   matches actual reading dependency.

2. **[Q]** **Promote a "First proof" section** into Quick Start
   (currently §1.3), showing exactly: declare context → `make-wff-from-string`
   → `sp` → two or three short forms → `qed`.  Use a goal that takes
   ≤5 commands.  Annotate every command (what changed, why).  Reader
   should be able to copy-paste the whole transcript into the REPL and
   see the same output.

3. **[Q]** **Annotate each chapter's opening paragraph** with "Read this
   when…" — e.g., `ch-math` opens with "Read this to find out which
   number systems and ordinals are pre-loaded; skip on a first pass."

4. **[M]** **Split `ch-defs.tex` (currently ~1450 lines, the largest
   chapter)** into two: one chapter on *how to declare* new
   structures/predicates/constants (the `declare-structure` /
   `def-predicate` / `def-by-nn-recursion` machinery), and one on
   *what's already declared* (cardinality, sequences, ring instances,
   metric space, extended reals).  These currently coexist and a
   newcomer can't tell where the "rules of the road" end and the
   "stock library" begins.

5. **[Q]** **Index the short forms** — append a one-page reference card
   at the end of `ch-proofs.tex` listing the ~40 short forms by
   one-line description, sorted by category (goal-decomposition,
   assumption-discharge, arithmetic, structure, focus).  `vnb-commands.lisp`
   already has the data — render it to TeX.

6. **[Q]** **Inline the `[[NOTE: References needed. NO HALLUCINATIONS please]]`
   in ch-intro.tex** — this leaked into the rendered PDF and is the
   first non-prose thing a reader sees.  Either remove or replace with
   real citations.

---

## 2. What to highlight (and what to demote)

### Recommendations

7. **[Q]** **"Macetes" needs a 3-sentence motivation up front**.  The
   word is unfamiliar (Portuguese: *trick/knack*), borrowed from IMPS.
   First mention in `ch-proofs` should say: "A *macete* is a conditional
   rewrite rule derived from a theorem.  `(mac 'thm-name)` applies it
   to the current goal.  Read this section once you've finished your
   first proof — macetes are how you scale beyond toy goals."  Then the
   reader knows when to come back.

8. **[Q]** **The cycle `declare → sp → commands → qed` is THE workflow.**
   Put a single diagram or numbered list of this loop early in
   `ch-proofs` — currently the chapter dives into sequents and
   deduction graphs (correct, but reader can't see the loop).

9. **[Q]** **Demote `ch-source` (file overview) to an appendix.**  It's
   reference material for someone editing the prover, not for someone
   *using* it.  Newcomers will not benefit from "load order is …" on
   the way to learning how to prove things.

10. **[M]** **Goal-shape → command-recipe cheat sheet.**  A short
    table indexed by goal shape:
    | Goal shape           | First try            |
    |----------------------|----------------------|
    | `(IMPLIES p q)`      | `(di)` to move `p` to context |
    | `(AND p q)`          | `(di)` to split into two subgoals |
    | `(FORALL x P)`       | `(di)` to introduce fresh `x` |
    | `(= a a)`            | `(rfl)` |
    | `(= e₁ e₂)` (ring)   | `(rs)` |
    | ground arithmetic    | `(arith)` |
    | `(IN x A)` from ctx  | `(ass)` |

    This is the single biggest "what do I type now" pain for beginners.

11. **[Q]** **De-emphasize implementation notes that leaked into the user
    manual.**  Examples: REVIEW.md tag references like "S-12", "G-1",
    "R-9" appear in user-facing prose.  These are meaningful to whoever
    ran the soundness review; they're noise to a reader trying to use
    the system.  Move to design-notes.md or a `.scm` comment.

---

## 3. Emacs interactive UX

The current Emacs setup (`vnb.el`) gives a two-buffer layout:
`*VNB*` (REPL) + `*VNB State*` (the focus goal + sibling open goals).
The deduction graph itself is *not* shown.

### Recommendations

12. **[Q]** **Make the keybinding cheatsheet visible on `M-x vnb`.**
    The first time the user starts the interface, briefly display the
    main keybindings (e.g., in `*VNB State*` for 3 seconds, or as a
    header comment in `*VNB*`).  Currently you have to know to call
    `vnb-help` (or read `vnb.el` source) to find them.

13. **[Q]** **Document the `vnb-insert-command` completion entry point
    in the Quick Start chapter, not just in `vnb-complete.el`.**  TAB
    completion on the ~40 short forms is one of the highest-value
    discoverability features and is currently invisible to manual-only
    readers.

14. **[Q]** **Add a "what could I try?" hint command.**  `(?)` or
    `(suggest)` examines the current goal's shape and prints 1-3
    candidate commands (matching the cheat sheet from recommendation
    10).  Pure heuristic — no soundness implications.

15. **[M]** **Show a goal trail in `*VNB State*`.**  When the focus is
    deep inside an IMPLIES-intro inside a FORALL-intro inside …, the
    user sees the leaf goal but not the ancestry.  A 5-line breadcrumb
    above the focus would orient: "FORALL x. IMPLIES (IN x NN) →
    AND-intro (right) → current focus."

16. **[M]** **Persistent open-goals overview pane.**  A third buffer
    (or split inside `*VNB State*`) showing *all* open goals at all
    times, numbered, with the focus highlighted.  Beginners often
    `(focus n)` blind because they don't have a stable mapping from
    `n` to goal content.

17. **[Q]** **Color-code `;VNB warning:` vs. `;; VNB error:` vs.
    success.**  Currently both warnings and the success-show output
    arrive as plain text; in a long session it's easy to miss that the
    last command failed.

18. **[Q]** **Echo the just-applied command at the top of every
    `*VNB State*` refresh** — e.g., `Last: (di)`.  Currently you have
    to scroll the REPL buffer to see what got you here.

---

## 4. Deduction graph visualization

This is the single largest gap.  The `print-proof-state` output is just
*focus goal + list of sibling open goals* — it does not communicate the
*shape* of the proof tree.  IMPS dedicated 717 lines
(`presentation/dg-emacs.t`) to a per-graph `*Deduction-…*` buffer with
a tree view of nodes, grounded/ungrounded status, and incremental
updates.  Worth borrowing the idea, not necessarily the code.

### Recommendations

19. **[M]** **Add a `(tree)` command that renders the current DG as
    indented text.**  Each node a sequent number, with `✓` for grounded
    and `?` for open; rule labels on the edges; indentation by depth.
    Even a single static snapshot beats no view at all.
    Example mockup:
    ```
    [0] ⊢ ∀x∈NN. P(x) → Q(x)
     └─ forall-elim → [1] (IN x NN), (P x) ⊢ (Q x)
         ├─ implies-intro → [2] (IN x NN) ⊢ (IMPLIES (P x) (Q x))
         │   └─ ✓ ...
         └─ ? FOCUS
    ```

20. **[M]** **An auto-refreshing `*VNB DG*` buffer** that shows the
    above on every command.  Mirror IMPS's `*Deduction-N*` buffer
    naming and the per-DG buffer model.

21. **[L]** **Clickable nodes in the DG buffer** that switch the focus
    to that node.  Big interactive payoff, requires Emacs Lisp button
    overlays — straightforward but not trivial.

22. **[Q]** **Expose `proof-open-goals` as a numbered command, e.g.
    `(goals)`**, that prints `1. <goal-1>`, `2. <goal-2>`, … with the
    current focus marked.  Cheap intermediate before the full DG view
    lands.

---

## 5. PDF / TeX proof presentation

IMPS exported proofs to TeX (`presentation/imps-to-tex.t`, 877 lines;
`tex-prescriptive-presentation.t`, 299 lines) and rendered them as
PDF — a sequence of sequents with rule annotations, suitable for
showing a proof to a human reader who isn't running the prover.

This is the single highest-value *external* presentation feature, and
the one most directly motivating a "proof of concept" pitch.

### Recommendations

23. **[M]** **`(present-proof 'name)` writes `proof-name.tex`** —
    one sequent per node, in `\inferrule{premises}{conclusion}{rule}`
    form (mathpartir or bussproofs package).  Even a flat unindented
    list, with one sequent per line and a rule label, would be a leap
    forward.

24. **[M]** **Re-use the existing infix printer (`expr->str` in
    `sequents.scm`) for the TeX output** but with `\Rightarrow`,
    `\forall`, `\in`, `\le`, `\emptyset` substituted for the ASCII
    equivalents.  The `wff->string` machinery already knows precedence
    and infix; only the symbol table changes.

25. **[L]** **Borrow the IMPS infix-to-TeX symbol table directly from
    `tea/presentation/imps-to-tex.t`**.  Most of the work is already
    done there — adapt rather than rewrite.

26. **[L]** **Stretch goal: animated proof replay**, e.g.\ a sequence
    of PDFs (one per command) that can be flipped through to see how
    the deduction graph grows.  Probably overkill until other things
    land.

---

## 6. Other concrete friction points

### Recommendations

27. **[Q]** **`make-wff-from-string` should be `mkw` or similar at the
    REPL.**  Every `(sp …)` requires this incantation; a 3-character
    alias would save thousands of keystrokes over time.

28. **[Q]** **`(sp "…")` should auto-call `make-wff-from-string` on a
    bare string.**  Currently `(sp (make-wff-from-string "…"))` is
    needed.  Same content, less friction.

29. **[Q]** **Document the `RR*` infix-parsing caveat** at the top of
    `ch-syntax` or in a "Known limitations" subsection — it'll bite
    anyone trying to talk about extended reals.  Currently only flagged
    in `extended-reals.scm` and the new manual section.

30. **[Q]** **`(qed name)` should print the just-installed theorem
    formula**, not just save silently.  Helps with the "did that really
    work?" anxiety.

31. **[Q]** **Add a `(theorems)` command listing recently installed
    theorems**, since users can't always remember what they named
    things.  `*theorem-table*` is already a hash table.

32. **[M]** **Replace numeric REVIEW.md tags in user-facing error
    messages with prose.**  E.g., `(REVIEW.md S-12)` mid-error gives
    no actionable information.

33. **[Q]** **Use `;;;` comments uniformly for documentation, `;;` for
    asides** — current code mixes both heavily inside the same file.
    Minor but readability-affecting in a literate codebase.

---

## 7. Long-term: GUI

The user flagged GUI as a long-term direction.  Two realistic targets:

34. **[L]** **Browser-based.**  A small web frontend (vanilla JS + a
    Scheme HTTP server) that wraps the REPL.  Lower barrier than
    Emacs; portable.  Major work item: serializing proof states over
    a wire protocol.

35. **[L]** **A standalone Tk or GTK app via FFI.**  More native feel,
    but tied to MIT Scheme's FFI story.  Defer until 34 looks
    insufficient.

The PDF presentation (§5) is a much smaller and higher-leverage
investment than either GUI direction, and it's strictly compatible with
both — do that first.

---

## Priority summary

If picking one thing per category to start with:

- **Manual**: recommendation **2** (worked first proof in Quick Start).
- **Highlighting**: recommendation **10** (goal-shape → command cheat sheet).
- **Emacs**: recommendation **14** (`(?)` suggest command — quickest
  payoff, no UI work).
- **DG visualization**: recommendation **19** (`(tree)` command, text
  output, no Emacs work).
- **PDF presentation**: recommendation **23** (`(present-proof 'name)`).

Each is at most a day of focused work and would noticeably lower the
"can someone else use this?" barrier.
