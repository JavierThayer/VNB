#!/bin/bash
# build-by-topic.sh -- turn reference/BY-TOPIC.tex (emitted at prover load by
# reference-topics.scm's write-by-topic-tex) into a PDF and, if LaTeXML is
# installed, an HTML page.
#
#   PDF  : always (needs pdflatex)
#   HTML : if `latexmlc` (or latexml + latexmlpost) is on PATH
#          -- see https://github.com/brucemiller/LaTeXML ; install e.g.
#             `cpan LaTeXML`  or  `apt-get install latexml`.
#
# Usage:  reference/build-by-topic.sh        (from anywhere)

set -e
DIR="$(cd "$(dirname "$0")" && pwd)"
cd "$DIR"
TEX=BY-TOPIC.tex

if [ ! -f "$TEX" ]; then
  echo "build-by-topic: $DIR/$TEX not found (load the prover to emit it)." >&2
  exit 1
fi

echo "build-by-topic: pdflatex -> BY-TOPIC.pdf"
pdflatex -interaction=nonstopmode "$TEX" > by-topic-latex.log 2>&1 || true
pdflatex -interaction=nonstopmode "$TEX" > by-topic-latex.log 2>&1 || true
if [ -f BY-TOPIC.pdf ]; then
  echo "build-by-topic: wrote $DIR/BY-TOPIC.pdf"
else
  echo "build-by-topic: PDF FAILED -- see $DIR/by-topic-latex.log" >&2
fi

if command -v latexmlc >/dev/null 2>&1; then
  echo "build-by-topic: latexmlc -> by-topic.html"
  latexmlc --dest=by-topic.html "$TEX" > by-topic-latexml.log 2>&1 \
    && echo "build-by-topic: wrote $DIR/by-topic.html" \
    || echo "build-by-topic: LaTeXML FAILED -- see $DIR/by-topic-latexml.log" >&2
elif command -v latexml >/dev/null 2>&1 && command -v latexmlpost >/dev/null 2>&1; then
  echo "build-by-topic: latexml + latexmlpost -> by-topic.html"
  latexml --dest=BY-TOPIC.xml "$TEX" > by-topic-latexml.log 2>&1 \
    && latexmlpost --dest=by-topic.html BY-TOPIC.xml >> by-topic-latexml.log 2>&1 \
    && echo "build-by-topic: wrote $DIR/by-topic.html" \
    || echo "build-by-topic: LaTeXML FAILED -- see $DIR/by-topic-latexml.log" >&2
else
  echo "build-by-topic: LaTeXML not found; skipping HTML."
  echo "  install with 'cpan LaTeXML' or 'apt-get install latexml', then re-run."
fi

# tidy aux files
rm -f BY-TOPIC.aux BY-TOPIC.out BY-TOPIC.toc BY-TOPIC.xml 2>/dev/null || true
