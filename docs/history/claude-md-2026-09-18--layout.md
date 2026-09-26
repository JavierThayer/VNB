<!-- VERBATIM copy of a section of CLAUDE.md as it stood on 2026-09-18, moved here when
CLAUDE.md was trimmed to its operational rules.  Nothing was edited. -->

## Layout

    structure-library/   definitions, structures, vocabulary, warranted supports
    theorem-library/     proofs that reach (qed ...); loaded, gated, counted
    calculus/            probes and stress tests; MOSTLY not in load.scm -- but
                         `calculus/finite-ball-subcover-proof` IS loaded (load.scm:787),
                         and load.scm's per-file environment containment covers
                         `calculus/` exactly because such files can be loaded
    reference/           MIXED, and the distinction matters.  Most of it is GENERATED
                         at load (PSS.md, THEOREMS.md, GLOSSARY.md, DEFINITIONS.md,
                         PROOF-DEBT.md, DEBT-BUNDLE.md, TACTICS.md, ...) -- never
                         hand-edit those, the next load overwrites them.  Five are
                         HAND-WRITTEN and always were: LIBRARY.md, KERNEL-RULES.md,
                         KERNEL-MAP.md, REVIEW.md, USABILITY-REVIEW.md, VNB-TEST.md.
                         `build-reference-html.py`'s DOCS list is what reaches the
                         browser, and a .md absent from it is on disk and reachable
                         from nowhere -- which is what KERNEL-RULES.md was for months.
    scratchpad/          throwaway drivers (untracked)

Also on disk, not described above: `prove-scripts/`, `stress-tests/`, `examples/`,
`structure-notes/`, `archive/`, `printouts/`, `emacs/`, `docs/`, and a SECOND
scratch directory `scratch/` alongside `scratchpad/` (both in use; no rule
distinguishes them).

**Load order matters.** A file using `sp`/`qed`/`make-wff` must come after `interactive`
and `proof-debt` in `load.scm`. Misplacing it gives "Unbound variable: make-wff".

