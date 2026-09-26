# Makefile for the VNB proof checker.  `make help' lists the targets.
#
# Every target is a thin wrapper around a command that already exists
# (./prover, mit-scheme on load.scm or test-suite.scm, the generators under
# reference/ and docs/).  Nothing here is needed to use the system; it is a
# memory aid and a way to get the order of the first-time steps right.
#
# A LOAD OF THE LIBRARY NEEDS ABOUT 2 GB OF RAM.  compile, band, check and run
# each load it once; do not run two of them at the same time on a small machine.

SHELL      := /bin/bash
SCHEME     := mit-scheme
HEAP       := 120000
SUITE_HEAP := 200000
ROOT       := $(abspath $(dir $(lastword $(MAKEFILE_LIST))))

.PHONY: help doctor setup compile compile-full band check panel-check run repl \
        html manual docs clean-binaries

help:
	@echo "VNB proof checker"
	@echo ""
	@echo "  first time:"
	@echo "    make doctor         check that MIT/GNU Scheme 12.1, Emacs, python3 are present"
	@echo "    make setup          doctor + compile + band   (about 25 minutes, once)"
	@echo ""
	@echo "  every day:"
	@echo "    make run            start the VNB workspace (Emacs)"
	@echo "    make repl           start a plain REPL from the saved image (seconds)"
	@echo ""
	@echo "  after editing source files:"
	@echo "    make compile        recompile the files that changed (one library load)"
	@echo "    make compile-full   recompile everything (after editing a macro)"
	@echo "    make band           rebuild the saved image  ./prover -b  starts from"
	@echo ""
	@echo "  checking:"
	@echo "    make check          the full test suite (about 15 minutes); prints the SUMMARY line"
	@echo "    make panel-check    the Emacs workspace checks (seconds)"
	@echo ""
	@echo "  documentation:"
	@echo "    make html           rebuild reference/reference.html from reference/*.md"
	@echo "    make manual         rebuild docs/manual.pdf (generated appendices, index, two passes)"
	@echo "    make docs           html + manual"
	@echo ""
	@echo "    make clean-binaries remove every .com/.bin/.bci (the tree then runs interpreted: SLOW)"

# --- first time ------------------------------------------------------------

doctor:
	@ok=1; \
	if command -v $(SCHEME) >/dev/null 2>&1; then \
	  v=$$(timeout 30 $(SCHEME) --quiet --eval '(begin (write-string (get-subsystem-version-string "release")) (newline) (exit))' < /dev/null 2>/dev/null | head -1); \
	  echo "scheme : MIT/GNU Scheme $$v"; \
	  case "$$v" in *"12.1"*) ;; *) echo "         WARNING: the saved image and the .com files are for MIT/GNU Scheme 12.1";; esac; \
	else echo "scheme : NOT FOUND (install MIT/GNU Scheme 12.1)"; ok=0; fi; \
	if command -v emacs >/dev/null 2>&1; then echo "emacs  : $$(emacs --version | head -1)"; \
	else echo "emacs  : not found (needed for 'make run'; the REPL works without it)"; fi; \
	if command -v python3 >/dev/null 2>&1; then echo "python3: $$(python3 --version)"; \
	else echo "python3: not found (needed for 'make html' and 'make manual')"; fi; \
	if command -v pdflatex >/dev/null 2>&1; then echo "latex  : pdflatex present"; \
	else echo "latex  : pdflatex not found (needed only for 'make manual')"; fi; \
	n=$$(find $(ROOT) -maxdepth 1 -name '*.com' | wc -l); echo "compiled core files at the root: $$n  (0 means the tree is INTERPRETED: run 'make compile')"; \
	if [ -f $(ROOT)/vnb.band ]; then echo "saved image: $$(ls -la --time-style=+%F_%R $(ROOT)/vnb.band | awk '{print $$6}')"; \
	else echo "saved image: none (run 'make band')"; fi; \
	[ $$ok = 1 ]

setup: doctor compile band
	@echo "setup done.  'make run' starts the workspace; 'make check' runs the suite."

# --- compile ---------------------------------------------------------------
# One library load.  Files whose .com is current load compiled; a file whose
# .scm is newer loads from source and is then recompiled.  Files that use a
# top-level macro are listed in *vnb-no-compile-files* and are skipped.

compile:
	cd $(ROOT) && env -u INSIDE_EMACS VNB_RECOMPILE=1 $(SCHEME) --heap $(HEAP) --quiet \
	  --load load.scm --eval '(begin (compile-vnb!) (exit))' < /dev/null

compile-full:
	cd $(ROOT) && env -u INSIDE_EMACS VNB_RECOMPILE=1 VNB_FULL_RECOMPILE=1 $(SCHEME) --heap $(HEAP) --quiet \
	  --load load.scm --eval '(begin (compile-vnb!) (exit))' < /dev/null

band:
	cd $(ROOT) && ./prover --build-band < /dev/null

# --- checking --------------------------------------------------------------
# Exit status 0 from the suite does not mean it ran: under memory pressure it can
# die silently.  The target therefore fails unless the SUMMARY line is present,
# and fails if that line reports a failure.

check:
	cd $(ROOT) && timeout 4000 $(SCHEME) --heap $(SUITE_HEAP) --quiet --load test-suite.scm < /dev/null \
	  > test-suite.log 2>&1; \
	line=$$(grep '=== SUMMARY' test-suite.log | tail -1); \
	if [ -z "$$line" ]; then echo "check: NO SUMMARY LINE -- the suite did not finish (see test-suite.log)"; exit 1; fi; \
	echo "$$line"; grep '^FAIL' test-suite.log | head -20; \
	case "$$line" in *" 0 failed"*) ;; *) exit 1;; esac

panel-check:
	cd $(ROOT) && emacs --batch -l emacs/vnb-panel-check.el

# --- running ---------------------------------------------------------------

run:
	cd $(ROOT) && ./VNB

repl:
	cd $(ROOT) && ./prover -b

# --- documentation ---------------------------------------------------------

html:
	cd $(ROOT) && python3 reference/build-reference-html.py

manual:
	$(MAKE) -C $(ROOT)/docs all

docs: html manual

# --- housekeeping ----------------------------------------------------------

clean-binaries:
	@echo "removing .com/.bin/.bci under $(ROOT) (the saved image is kept)"
	cd $(ROOT) && find . -path ./archive -prune -o \( -name '*.com' -o -name '*.bin' -o -name '*.bci' \) -print -delete | wc -l
