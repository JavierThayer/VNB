# Makefile for the VNB manual.
#
#   make          regenerate the generated sections and (re)build manual.pdf
#   make gen      regenerate only the generated reference sections
#   make kindle   build manual-kindle.pdf, the same manual at 105x140 mm
#   make both     manual.pdf and manual-kindle.pdf, one `gen' between them
#   make clean    remove LaTeX build intermediates (keeps both PDFs)
#
# `make` always rebuilds, on purpose.  The generated sections are emitted from
# the LIVE system -- the source tree and reference/TACTICS.md -- and those inputs
# change without any tracked file's timestamp changing (add a .scm, reload the
# prover), so timestamp rules cannot tell when they are stale.  Refreshing them
# every build is what keeps the manual from drifting:
#   app-source-generated.tex   <- source tree (each file's `;;; name -- desc' header)
#   app-tactics-generated.tex  <- reference/TACTICS.md (the *tactic-help* registry)
#   app-glossary-generated.tex <- reference/GLOSSARY.md (every name, from the registries)
#   ch-kernel-ops-generated.tex <- tactics-help.scm (*kernel-rule-tags*, the list the startup
#                                  check uses) and reference/THEOREMS.md (the axiom count)
#   app-tactic-uses-generated.tex <- reference/kernel-map-static.sexp + tactics-help.scm:
#                                  the kernel operations each proof command can reach.  The
#                                  same table goes to reference/TACTIC-USES.md and, as Scheme
#                                  data, to tactic-uses-data.scm, which tactics-help.scm reads
#                                  so that each entry of reference/TACTICS.md carries its own
#                                  `Uses' line.  The .sexp is written by the two kernel-map
#                                  instruments (kernel-map-static.scm, kernel-map-trace.scm);
#                                  its header says how to regenerate it.  gen-tactics-ref.py
#                                  puts the same line inside each entry of the manual's
#                                  tactic reference, so it runs after this one.

LATEX := pdflatex -interaction=nonstopmode -halt-on-error
# The index is built between the two LaTeX passes: pass 1 writes the .idx,
# makeindex sorts it to .ind, pass 2 typesets \printindex.  Without the
# middle step \printindex silently produces an EMPTY index -- the failure
# is invisible in the log, so it is wired into every target, not documented.
MAKEINDEX := makeindex -q

.PHONY: all gen kindle both clean check-fresh

all: gen
	$(LATEX) manual.tex
	$(MAKEINDEX) manual
	$(LATEX) manual.tex

# The Kindle edition.  Same sources, same generated sections: manual-kindle.tex
# sets the page size and the code font, then \input's manual.tex.  Twice, for
# the table of contents and the cross-references, exactly like the print build.
kindle: gen
	$(LATEX) manual-kindle.tex
	$(MAKEINDEX) manual-kindle
	$(LATEX) manual-kindle.tex

both: all
	$(LATEX) manual-kindle.tex
	$(MAKEINDEX) manual-kindle
	$(LATEX) manual-kindle.tex

gen: check-fresh
	python3 gen-source-appendix.py
	python3 gen-tactic-uses.py
	python3 gen-tactics-ref.py
	python3 gen-structures.py
	python3 gen-categories.py
	python3 gen-glossary.py
	python3 gen-kernel-ops.py

# TACTICS.md and STRUCTURE-INDEX.md are rewritten ONLY by a prover load (load.scm
# runs (write-tactics-md) etc.), never by make.  So if their source registries were
# edited more recently than the .md was last written, the generated chapters would
# be built from a STALE .md.  Warn (do not block) -- the fix is to reload the prover.
check-fresh:
	@if [ ../tactics-help.scm -nt ../reference/TACTICS.md ]; then \
	  echo "*** WARNING: tactics-help.scm is newer than reference/TACTICS.md."; \
	  echo "***   The tactic chapter may be STALE.  Reload the prover (./prover or"; \
	  echo "***   ./VNB) to rewrite TACTICS.md, then re-run make."; \
	fi
	@if [ ../glossary.scm -nt ../reference/GLOSSARY.md ]; then \
	  echo "*** WARNING: glossary.scm is newer than reference/GLOSSARY.md."; \
	  echo "***   The glossary appendix may be STALE.  Reload the prover, then make."; \
	fi
	@if [ ../structures.scm -nt ../reference/STRUCTURE-INDEX.md ]; then \
	  echo "*** WARNING: structures.scm is newer than reference/STRUCTURE-INDEX.md."; \
	  echo "***   The structure sections may be STALE.  Reload the prover, then make."; \
	fi
	@if [ ../theorem-library/categories.scm -nt ../reference/CATEGORIES.md ]; then \
	  echo "*** WARNING: theorem-library/categories.scm is newer than reference/CATEGORIES.md."; \
	  echo "***   The categories section may be STALE.  Reload the prover, then make."; \
	fi

clean:
	rm -f manual.aux manual.log manual.out manual.toc
	rm -f manual-kindle.aux manual-kindle.log manual-kindle.out manual-kindle.toc
	# .idx/.ind too: \printindex runs on BOTH passes, so pass 1 re-reads whatever
	# .ind is on disk.  A .ind left by a FAILED build therefore breaks the next
	# build before makeindex ever gets to rewrite it -- the error points at the
	# stale index, not at the change that caused it.  Hit while adding the index.
	rm -f manual.idx manual.ind manual.ilg
	rm -f manual-kindle.idx manual-kindle.ind manual-kindle.ilg

# The major theorems of the notes as the library states them (reference/major-theorems.tex is written at load).
.PHONY: major-theorems
major-theorems:
	$(LATEX) major-theorems.tex && $(LATEX) major-theorems.tex && $(LATEX) major-theorems.tex
