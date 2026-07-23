# Makefile for the VNB manual.
#
#   make          regenerate the generated sections and (re)build manual.pdf
#   make gen      regenerate only the generated reference sections
#   make clean    remove LaTeX build intermediates (keeps manual.pdf)
#
# `make` always rebuilds, on purpose.  The generated sections are emitted from
# the LIVE system -- the source tree and reference/TACTICS.md -- and those inputs
# change without any tracked file's timestamp changing (add a .scm, reload the
# prover), so timestamp rules cannot tell when they are stale.  Refreshing them
# every build is what keeps the manual from drifting:
#   app-source-generated.tex   <- source tree (each file's `;;; name -- desc' header)
#   app-tactics-generated.tex  <- reference/TACTICS.md (the *tactic-help* registry)

LATEX := pdflatex -interaction=nonstopmode -halt-on-error

.PHONY: all gen clean check-fresh

all: gen
	$(LATEX) manual.tex
	$(LATEX) manual.tex

gen: check-fresh
	python3 gen-source-appendix.py
	python3 gen-tactics-ref.py
	python3 gen-structures.py

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
	@if [ ../structures.scm -nt ../reference/STRUCTURE-INDEX.md ]; then \
	  echo "*** WARNING: structures.scm is newer than reference/STRUCTURE-INDEX.md."; \
	  echo "***   The structure sections may be STALE.  Reload the prover, then make."; \
	fi

clean:
	rm -f manual.aux manual.log manual.out manual.toc
