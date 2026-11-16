#!/usr/bin/env python3
"""check-overfull.py -- list the lines of the manual that run into the margin.

Runs pdflatex once over manual.tex through a wrapper that writes a marker into
the log as each chapter file begins and ends, so every `Overfull \\hbox' that
TeX reports is attributed to its chapter file and source line.  Reports the
overruns at least THRESHOLD points wide (default 3pt; anything smaller is not
visible in print), per file, then each one in the hand-written files.

    python3 check-overfull.py [THRESHOLD] [--all]

--all also lists each overrun in the generated files (*-generated.tex).  Run
it after `make'; it reuses manual.aux, so references resolve as in the PDF.
The temporary files are vnb-overfull-check.*; the log is kept for reading.
"""
import collections, os, re, shutil, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
JOB = "vnb-overfull-check"
args = [a for a in sys.argv[1:] if a != "--all"]
THR = float(args[0]) if args else 3.0
ALL = "--all" in sys.argv

os.chdir(HERE)
with open(JOB + ".tex", "w") as f:
    f.write("\\AtBeginDocument{\\let\\VNBoldinput\\input"
            "\\def\\input#1{\\typeout{@@BEGIN #1}\\VNBoldinput{#1}\\typeout{@@END #1}}}\n"
            "\\input{manual}\n")
for ext in ("aux", "ind", "toc"):
    if os.path.exists("manual." + ext):
        shutil.copy("manual." + ext, JOB + "." + ext)
subprocess.run(["pdflatex", "-interaction=nonstopmode", JOB + ".tex"],
               stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)

stack, rows = ["manual"], []
pat = re.compile(r"Overfull \\hbox \(([\d.]+)pt too wide\) (?:in paragraph at lines (\d+)--\d+"
                 r"|detected at line (\d+)|in alignment at lines (\d+)--\d+)")
for line in open(JOB + ".log", errors="replace"):
    m = re.match(r"@@BEGIN (\S+)", line)
    if m:
        stack.append(m.group(1)); continue
    if line.startswith("@@END"):
        stack.pop(); continue
    m = pat.match(line)
    if m and float(m.group(1)) >= THR:
        kind = "paragraph" if m.group(2) else ("display or verbatim" if m.group(3) else "table")
        rows.append((stack[-1], int(m.group(2) or m.group(3) or m.group(4)), float(m.group(1)), kind))

by = collections.Counter(r[0] for r in rows)
print("overruns of %gpt or more: %d" % (THR, len(rows)))
for name, n in by.most_common():
    print("  %-32s %5d" % (name + ".tex", n))
for name, line, w, kind in sorted(rows):
    if ALL or not name.endswith("-generated"):
        print("  %s.tex:%d  %.0fpt  %s" % (name, line, w, kind))
for ext in ("pdf", "aux", "ind", "toc", "out", "idx", "tex"):
    if os.path.exists(JOB + "." + ext):
        os.remove(JOB + "." + ext)
