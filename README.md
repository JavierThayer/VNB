# VNB

VNB is a proof checker and a mathematical assistant: it checks proofs, and it
helps a user discover them.  It is written in MIT/GNU Scheme, with a user
interface in GNU Emacs and reference documentation in a web view.  The logical
framework is von Neumann-Bernays set theory, with a large stock of ready-made
constructors.

**Where things are:** `MAP.md` lists every source file by role (kernel, surface,
tactics, vocabulary, output, ledger, build; the structure library by theory), as
links; it is the grouped view `~/vnb` of the tarball, rendered for the flat
directory a repository shows.

## Requirements

* **MIT/GNU Scheme 12.1** -- required.
* **GNU Emacs** -- required for the user interface.
* Optional, each enabling one feature and nothing else:
  * `pdflatex` and `dvipng` -- LaTeX-rendered sequents in the workspace, and
    printed proofs;
  * `graphviz` (`dot`) -- the structure graph;
  * `python3` -- a few helper scripts.

## First run

Run these once, in this order.

    tar xzf prover-src.tar.gz -C ~      # unpacks ~/prover and ~/vnb
    cd ~/prover
    ./VNB-with-compile                  # about 10 minutes
    ./prover --build-band               # about 4 minutes
    ./VNB                               # the Emacs workspace

The archive holds two directories and they must land in the **same parent**:
`prover` is the system, and `vnb` is a navigation view of it made of relative
symlinks (`../prover/...`).  Nothing loads from `vnb`, so if you unpack only
`prover` you lose nothing but that view.

**The first step is not optional, and skipping it is the most common way to
form a wrong impression of this system.**  The distributed tree contains no
compiled files, so out of the box every source file is interpreted.  Measured
on the development machine, interpreted against compiled:

| | interpreted | compiled |
|---|---|---|
| library load | about 11 minutes | 24 seconds |
| full test suite | about 42 minutes | about 6 minutes |

Nothing on screen reports this.  A load that seems inexplicably slow is almost
always an uncompiled tree; `ls *.com` answers the question in one command.

The second step saves a heap image (`vnb.band`) with the whole library already
loaded, after which `./prover -b` starts in about 0.2 seconds instead of
re-proving the library.  The image is not distributed because it is roughly
eleven times the size of this entire source tree, and because an MIT Scheme
band is tied to the exact Scheme build that wrote it: one built elsewhere would
fail to load, with an error that does not explain itself.  Building it locally
is the four minutes above.

Rebuild the band after editing any `.scm` file outside `scratchpad/`,
`scratch/` or `prove-scripts/`; `./prover -b` warns when the band is older than
a source file, so this is not something to remember unaided.

## Everyday use

    ./VNB                     # Emacs workspace (graphical)
    ./VNB -nw                 # terminal-only
    ./prover                  # plain REPL
    ./prover -b               # REPL from the saved image -- the usual choice
    ./prover -b file.scm      # run a proof script against the image
    ./prover -i file.scm      # run a script, then stay in the REPL

After editing prover sources, `./VNB-with-compile` recompiles and relaunches.
An edited file that is not recompiled loads from source, which is harmless for
a leaf proof script and ruinous for a core file.

The full check suite is separate from the launcher, and must be run **alone and
in the foreground** -- started alongside another Scheme process it can die
partway through and still exit 0:

    timeout 3600 mit-scheme --quiet --load test-suite.scm < /dev/null

It prints `=== SUMMARY: N passed, M failed ===`.  Check for that line; exit 0
does not by itself mean the suite ran.

## Where things are

| | |
|---|---|
| `CLAUDE.md` | the working brief: operational facts, traps, and why decisions were made |
| `docs/manual.tex` | the manual (master file; chapters are `ch-*.tex`) |
| `reference/` | **generated** at load -- theorem catalogue, definitions, glossary, debt ledger. Never hand-edit |
| `structure-library/` | definitions, structures, vocabulary, warranted supports |
| `theorem-library/` | proofs that reach `qed`; loaded, gated and counted at every load |
| `emacs/` | the Emacs interface |
| `scratchpad/`, `scratch/` | throwaway drivers; not part of the library |

`CLAUDE.md` is the file to read second.  It is written for a working
contributor rather than a new reader, and it records the failures that produced
each rule, which is usually the fastest way to understand one.

## Licence

VNB is released under the Apache License, Version 2.0: see `LICENSE` for the
terms and `NOTICE` for the copyright statement and the attribution of
third-party software (none is bundled; MIT/GNU Scheme and GNU Emacs are
installed separately).  Contributions are accepted under the same licence, as
section 5 of the License provides.
