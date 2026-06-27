# Stress tests

A stress test is a proof *probe*, not a proof. You drive the prover at a hard
target and the deliverable is **the surfaced obstacle**, not a QED. Per the
project lens "proof requests are PSS probes": a request the prover cannot close
is telling you which reusable lemma (or which tactic capability) is missing.

These files are kept as readable, narrative records on purpose. They are
**training material** -- for a new human user, and for an LLM driving the
prover -- showing the real texture of a session: which `(di)` peels what, why a
`bc*` refuses to fire, which forward step slogs, and exactly which PSS support
finally closes the gap.

Nothing here is loaded by `load.scm` or `test-suite.scm`. Each file is a
standalone script run against a built image.

## The two flavors

- **Machinery-gap probe** -- names the missing reusable lemmas. The header's
  `PSS SUPPORTS LEANED ON` block lists them, and `OUTCOME` records what closed
  the gap. Example: `compact-tb-stress.scm`.
- **Tactic/search-capability probe** -- leans on no library lemma; the
  deliverable is what the scout / `inst` / `grind` lanes can and cannot drive.
  Example: `quantifier-swap-stress.scm`.

## Header convention

Every stress test opens with:

```
;;; <name>.scm -- one-line statement of the target
;;;   ./prover -i stress-tests/<name>.scm        ; the run command
;;;
;;; KIND: machinery-gap probe | tactic/search-capability probe
;;; PSS SUPPORTS LEANED ON (see theorem-library/pss-categories.scm):
;;;   <support-name>   <gloss>   (<category bucket>)
;;;   ...
;;; OUTCOME: <what closed it, or "left as a documented probe">
```

For a tactic/search probe, state plainly that it leans on no PSS support and
say what capability is under test instead.

The `PSS SUPPORTS LEANED ON` block is the point of today's convention: a reader
can see, without re-running anything, exactly which curated lemmas the argument
consumed and which bucket each lives in.

## Index

| File | Target | Kind | Status |
|------|--------|------|--------|
| `compact-tb-stress.scm` | compact => totally bounded (Prop 3.12, (1)=>(4)) | machinery-gap | gap closed -> `compact-tb` proven |
| `quantifier-swap-stress.scm` | exists/forall swap (nonstandard-analysis shape) | tactic/search | unguarded swap auto-closes; guarded swap + applied witnesses still open |

Add new probes here and give them a header block per the convention above.
