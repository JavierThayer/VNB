#!/usr/bin/env python3
"""exam-slice-plan.py -- cut the contained proof files into N slices for the sliced exam.

    exam-slice-plan.py --tree TREE --n N --out PLAN.tsv [--times TIMES.tsv ...] [--report]

Writes PLAN.tsv, one line per file, `K<TAB>FILE' (FILE = the load-list key,
e.g. theorem-library/goursat), the format load.scm's VNB_EXAM_SLICE_PLAN reads.

The files: every certificate file of TREE/certificates/ (a contained proof file with
at least one qed) plus every file named in a --times manifest.  A contained proof
file the plan does not name is placed by load.scm by a fixed hash, so a missing file
unbalances a night but is never left unexamined.

The weight of a file, in CPU ms, best first:
  1. its MEASURED off-mode time: the cpu_ms of its `off' row in the newest --times
     file that has one (the manifest.tsv each slice of a sliced night writes; the
     orchestrator keeps them in ~/mailbox/metrics/exam-slice/);
  2. else an ESTIMATE from the last exam's core pages (TREE/core-pages/<name>.core.gz,
     the gzipped size, summed over the file's theorems) and its theorem count:
     A_MS_PER_BYTE * bytes + B_MS_PER_THEOREM * theorems.  The constants were fitted
     2026-11-12 on worker-08 (scratchpad/triage/EXAM-SLICE-REPORT.md).
Then LPT: heaviest first, each to the slice with the least weight so far.
"""
import argparse, glob, os, sys

A_MS_PER_BYTE = 0.25
B_MS_PER_THEOREM = 300.0

ap = argparse.ArgumentParser()
ap.add_argument('--tree', required=True)
ap.add_argument('--n', type=int, required=True)
ap.add_argument('--out', required=True)
ap.add_argument('--times', action='append', default=[])
ap.add_argument('--report', action='store_true')
ap.add_argument('--only', help='plan only the files listed in this file (one load-list key per line; a cut-down test)')
a = ap.parse_args()
if a.n < 1: sys.exit('exam-slice-plan: --n must be >= 1')

certdir = os.path.join(a.tree, 'certificates')
names = {}          # file -> [theorem names]
for p in glob.glob(os.path.join(certdir, '**', '*.cert'), recursive=True):
    f = os.path.relpath(p, certdir)[:-len('.cert')]
    ns = []
    with open(p, errors='replace') as fh:
        for line in fh:
            if line.startswith('(') and not line.startswith('(vnb-certificate-file'):
                ns.append(line[1:].split(' ', 1)[0])
    names[f] = ns

measured = {}       # file -> cpu_ms of an off row; later --times files win
for t in a.times:
    if not os.path.exists(t): continue
    with open(t) as fh:
        for line in fh:
            if line.startswith('#'): continue
            r = line.rstrip('\n').split('\t')
            if len(r) >= 4 and r[2] == 'off':
                measured[r[0]] = float(r[3])
            names.setdefault(r[0], [])

if a.only:
    keep = set(open(a.only).read().split())
    names = {f: ns for f, ns in names.items() if f in keep}

pages = os.path.join(a.tree, 'core-pages')
def page_bytes(n):
    p = os.path.join(pages, n.replace('/', '%2F') + '.core.gz')
    return os.path.getsize(p) if os.path.exists(p) else 0

weight, source = {}, {}
for f, ns in names.items():
    if f in measured:
        weight[f] = measured[f]; source[f] = 'measured'
    else:
        weight[f] = A_MS_PER_BYTE * sum(page_bytes(n) for n in ns) + B_MS_PER_THEOREM * len(ns)
        source[f] = 'estimated'

load = [0.0] * a.n
plan = {}
for f in sorted(weight, key=lambda f: (-weight[f], f)):
    k = min(range(a.n), key=lambda i: (load[i], i))
    plan[f] = k + 1; load[k] += weight[f]

with open(a.out + '.tmp', 'w') as fh:
    fh.write('# exam-slice plan: N=%d, %d files (%d measured, %d estimated)\n'
             % (a.n, len(plan), sum(1 for f in plan if source[f] == 'measured'),
                sum(1 for f in plan if source[f] == 'estimated')))
    for k in range(a.n):
        fh.write('# slice %d: predicted %.0f s of proof work\n' % (k + 1, load[k] / 1000))
    for f in sorted(plan):
        fh.write('%d\t%s\n' % (plan[f], f))
os.replace(a.out + '.tmp', a.out)
if a.report:
    for k in range(a.n):
        print('slice %d: %4d files, predicted %6.0f s' % (k + 1, sum(1 for f in plan if plan[f] == k + 1), load[k] / 1000))
