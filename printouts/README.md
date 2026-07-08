# printouts/

Proof printout **sources** (`.tex`), kept in the source tree so they ride the
source tarball -- you can read a proof's output after unpacking without a
running prover.

- `reader-<name>.tex` -- human-readable bulleted sketch (`proof-reader.scm`),
  written by `(view-proof-reader-pdf 'name)` / `(write-proof-reader 'name path)`.
- `proof-<name>.tex` -- full machine step-trace (`proof-tex.scm`), written by
  `(view-proof-pdf 'name)`.

The rendered **PDFs** are regenerable and are NOT kept here; they land in
`~/.cache/vnb/tex/` (out of the tree, excluded from the tarball). Re-render any
`.tex` with `pdflatex -output-directory=$HOME/.cache/vnb/tex <file>.tex`, or just
call the `view-*` command again.
