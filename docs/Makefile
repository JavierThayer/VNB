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

LATEX := pdflatex -interaction=nonstopmode -halt-on-error

.PHONY: all gen kindle both clean check-fresh

all: gen
	$(LATEX) manual.tex
	$(LATEX) manual.tex

# The Kindle edition.  Same sources, same generated sections: manual-kindle.tex
# sets the page size and the code font, then \input's manual.tex.  Twice, for
# the table of contents and the cross-references, exactly like the print build.
kindle: gen
	$(LATEX) manual-kindle.tex
	$(LATEX) manual-kindle.tex

both: all
	$(LATEX) manual-kindle.tex
	$(LATEX) manual-kindle.tex

gen: check-fresh
	python3 gen-source-appendix.py
	python3 gen-tactics-ref.py
	python3 gen-structures.py
	python3 gen-glossary.py

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

clean:
	rm -f manual.aux manual.log manual.out manual.toc
	rm -f manual-kindle.aux manual-kindle.log manual-kindle.out manual-kindle.toc
