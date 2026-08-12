# slides/Makefile -- the VNB talks.
#
#   make            English deck (en/main.pdf)
#   make es         Spanish deck, when es/main.tex exists
#   make all        every deck that exists
#   make code       regenerate shared/code/*.txt from the source tree
#   make proofs     regenerate shared/proofs/*.tex by RUNNING the checker
#   make numbers    print where each quoted figure comes from
#   make clean      LaTeX droppings;  make distclean  also removes the PDFs
#
# `code' and `proofs' both regenerate slide content FROM THE TREE rather than
# from a transcription of it.  Run both before a talk and read the diff: that
# is the whole defence against a slide that quietly stops being true.

LATEX  := pdflatex -interaction=nonstopmode -halt-on-error
PROVER := ./prover      # run from prover/, i.e. after the `cd ..' below

DECKS  := $(patsubst %/main.tex,%,$(wildcard */main.tex))

.PHONY: all en es code proofs figures numbers clean distclean

all: $(DECKS)

en: en/main.pdf
es: es/main.pdf

# Two passes: \tableofcontents needs the first one's .toc.
SHARED := shared/preamble.tex shared/numbers.tex \
          $(wildcard shared/code/*.txt) $(wildcard shared/proofs/*.tex) \
          shared/figures/structure-graph.pdf

%/main.pdf: %/main.tex $(SHARED)
	cd $(dir $<) && $(LATEX) main.tex >/dev/null && $(LATEX) main.tex >/dev/null
	@echo "built $@ ($$(pdfinfo $@ 2>/dev/null | awk '/^Pages/{print $$2}') pages)"

code:
	@sh shared/code/extract.sh

# The structure graph, from the .dot the prover itself writes.  Regenerate the
# .dot from a REPL first if the hierarchy has moved:  (structure-graph-dot-file)
figures: shared/figures/structure-graph.pdf
shared/figures/structure-graph.pdf: ../reference/structure-graph.dot
	@mkdir -p shared/figures
	dot -Gratio=0.55 -Tpdf $< -o $@   # 0.55 -> roughly 16:9; node boxes keep their size
	@echo "  $@  <-  $<  ($$(grep -c 'tooltip=' $< ) nodes and edges)"

# Needs a compiled tree (see CLAUDE.md: an interpreted load takes ~11 minutes).
proofs:
	cd .. && $(PROVER) slides/shared/proofs/regen.scm
	@for f in shared/proofs/raw-*.tex; do \
	   out=shared/proofs/$$(basename $$f | sed 's/^raw-//'); \
	   sed -n '/\\begin{proposition}/,/\\end{proof}/p' $$f \
	     | sed 's/\\begin{itemize}\[[^]]*\]/\\begin{itemize}/' > $$out; \
	   echo "  $$out  <-  $$f"; \
	 done
	@echo "  (preamble dropped; itemize options dropped -- beamer supplies its own)"

# `parity' RETIRED 2026-08-11.  It diffed the \fid{...} frame skeletons of en/
# and es/ and failed the build when they diverged -- the right gate for the
# Spanish deck as originally planned, an IDIOMATIC TRANSLATION of the English
# one.  That plan is off: es/ is a different talk (general audience, time
# limited), there will be no translation, and the two decks are not meant to
# correspond frame for frame.  A gate whose premise is false is worse than no
# gate, so it is gone rather than left to report a divergence that is correct
# and uninteresting.
#
# The \fid{...} markers stay in en/main.tex.  They typeset nothing, they cost
# nothing, and they are still the stable way to name a frame in a discussion
# ("the reader-substantive one") when the page numbers have moved.

numbers:
	@sed -n '1,25p' shared/numbers.tex

clean:
	rm -f */*.aux */*.log */*.nav */*.out */*.snm */*.toc */*.vrb

distclean: clean
	rm -f */main.pdf
