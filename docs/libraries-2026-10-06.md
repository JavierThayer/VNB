# The libraries (2026-10-06)

The user's remark (notes-61): "It might be a good idea to start thinking of libraries. Users
that are interested in Analysis might not be interested in strands." His decision the same
evening: build it, and produce a PDF of every theorem and definition, without proofs, in an
order in which each theorem follows what it depends on, split into parts ("books") that are
the libraries.

## What a library is

A library is a declared set of `theorem-library/` and `structure-library/` files with declared
imports. The table is `libraries.sexp` at the root, hand-kept:

    (library analysis
      (title "Analysis")
      (about "...")
      (imports linear-algebra)
      (files "structure-library/metric-space" ... ))
    (cross-cutting "theorem-library/hom-laws" ...)
    (exempt "theorem-library/pss-topics" "theorem-library/reference-topics")

The seven libraries and their imports, in the table's order (a topological order of the
imports): core; algebra (core); linear-algebra (algebra); analysis (linear-algebra);
complex-analysis (analysis); measure (analysis); strand (core).

The load list is untouched: the libraries interleave in it. A file belongs to the library its
MATHEMATICS belongs to; when a lemma inside it is cited from a library that does not import
that one, the lemma is misplaced and moves, not the file.

**Cross-cutting files.** Some files state theorems of several libraries by construction: the
generated hom laws of every structure (`hom-laws`, `hom-kinds`, `hom-functors`, `hom-views`),
the views, `functoriality`, `op-typing`, `subtype-laws`, and the rake batches that collected
asserted leaves across areas (`rake-algebra`, `rake-setoid`, `rake-setoid2`, `rake-analysis2`,
`rake-inequalities`, `rake-combinatorics`, `rake-finsum-core`, `rake-finsum-laws2`,
`rake-finsum-typing`, `cancellation`, `discrete-space`). A proven or asserted theorem of such a
file is placed by its VOCABULARY: the join of the libraries of its statement's heads (the
smallest library whose import closure holds them all), falling back on the file's nominal
library. Its definitions stay with the file. `library-join`, libraries.scm.

## The gate

`library-gate!` (libraries.scm) runs at the end of every load, before the proof-cycle check.
For every theorem whose source file is assigned it checks two things against the import
closure of its library: every name it cites (`proof-citations-of`, the live graph, certified
theorems included) and every applied head of its statement that is a functoid, a defined
head, or `IS-X` / `HOM-X` / `X-CLASS` for a declared structure X (shape or refinement). It also
lists the load-list files the table does not assign and the table entries the load list does
not have. Warn-only while the backlog is worked down; it goes fatal in a strict load at zero,
on the connective-arity precedent. Suite: six checks (coverage, no stale entry, the closure of
analysis, a violation control, an inside-closure control, a vocabulary control).

How to read the report: `;;   core -> algebra: N citation(s)  e.g. A uses B` means a theorem A
of a core file cites B, which is stated in an algebra file. The probe
`scratchpad/libraries/gate-detail.scm` prints every violation with its source and target
files; the per-file aggregation is what decides whether a file is misassigned (many
violations into one library) or a lemma is misplaced (one or two).

## The first run and what it found

The first assignment was by file name and the citation cones computed from `certificates/`
(the gate's own code could not run until the table existed). The first gate run reported 403
citation violations and 626 vocabulary violations. Nearly all were whole files: the finite-sum
typing files carrying matrix material (`lam-fun-bricks`), the Lebesgue integral under analysis
(`integral-laws`, `integral-convergence`), the IS-DIFF-ON laws under complex analysis
(`holomorphic-basics`), the quotient-and-completion batch `rake-setoid2` under algebra, the
arrays (`structure-library/matrix`: `MAT`, `ENTRY`, `INTERVAL` over an arbitrary set) under
linear algebra when every core file uses `INTERVAL`, and the finite sums under core when their
statements all say `IS-ABELIAN-GROUP` (they are algebra). Five lemmas were genuinely
misplaced and moved:

| lemma | was in | now in |
|---|---|---|
| `subset-refl` | discrete-space (analysis) | subset-lemmas (core) |
| `nn-succ-not-le` | poly-degree-laws (algebra) | nn-order-proof (core) |
| `centre-set-finite-guarded` | card-image-finite (core) | ball-cover-lemmas (analysis) |
| `bt-succ-minus-1` | comb-kk-laws (algebra) | nn-parity-proof (core) |
| `nn-le-gap` | series-block-abs (analysis) | nn-order-proof (core) |

The runs, each a certified build on worker-02 (about six minutes):

| run | citation | vocabulary | what changed before it |
|---|---|---|---|
| 1 | 403 | 626 | the first table, by name and cone |
| 2 | 48 | 11 | ~40 files reassigned; cross-cutting files placed by vocabulary; 3 lemmas moved |
| 3 | 41 | 1 | 6 more reassigned; `IS-X` / `HOM-X` / `X-CLASS` of refinements resolved; 2 lemmas moved |
| 4 | 18 | 0 | core as the floor of the join |
| 5 | 2 | 0 | the join takes the citations' libraries too |

| 6 | 0 | 0 | `nn-add-cancel` and `nn-mul-cancel` re-proven over RR in the core file `nn-cancel.scm` (they had been proven through ZZ's group and integral domain, so two NN facts cited from core rested on algebra) |

The gate is FATAL in a strict load since run 6 (2026-10-07).

## The book

`library-book.scm` writes `reference/library-book.tex` at every load; `docs/library-book.tex`
is the wrapper and `make library-book` in `docs/` (part of `make all`) produces the PDF. One
`\part` per library in table order, a section per source file in load order, and inside a
file: the definitions (structures, functoids, defined heads, the other defining axioms, each
group in order of first mention in the source text), then the axioms (primitive), the
assumptions (asserted, with the warrant tier), then the propositions in install order. The
machine-minted companions (`-rev`, view specialisations) are left out. A def-predicate or
def-constant head is one entry with all its defining axioms; a declared structure is one entry
and its `IS-X` law is not repeated; a functoid reads `name(params) := body`. A proposition's
proof is `(display-proof 'NAME "file.pdf")`.

The writer checks the dependency claim against the live citation graph and prints the
exceptions (`;; library-book: ... N citation(s) out of order`): zero since run 6.
4896 entries in 640 file sections, about 750 pages.

## Open

* The gate's vocabulary check covers functoids, defined heads and structure predicates; an
  accessor (`pts`, `dist`) names no owner and is not checked.
* `structure-library/matrix` defines `MAT-RING` beside the arrays; it reads in the Foundations
  book. A split of the file would put it with linear algebra.
* Per-library faces beyond the book (THEOREMS / DEFINITIONS / BY-TOPIC filtered, `find-theorem`
  and what-now restricted to the open libraries) and the selective load `VNB_LIBRARIES=...`:
  not built; the gate makes both safe.
