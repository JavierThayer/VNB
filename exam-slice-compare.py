#!/usr/bin/env python3
"""exam-slice-compare.py -- compare the products of a sliced night with a single exam's.

    exam-slice-compare.py A B [--what certificates,core-pages,reference] [--show N]

A and B are directories holding certificates/, core-pages/, reference/ (a tree, or the
`merged' directory of a --compare run of vnb-nightly-exam-sliced).  For each kind:
  certificates/  byte comparison per .cert file; for a differing file, the records
                 (one per line) that differ, by theorem name;
  core-pages/    the DECOMPRESSED content of each <name>.core.gz (gzip headers carry a
                 timestamp), pages only in A / only in B / different; SUMMARY.txt as text;
  reference/     byte comparison per file.
Exit 0 when everything compared is identical, 1 otherwise.
"""
import argparse, gzip, hashlib, os, re, sys

ap = argparse.ArgumentParser()
ap.add_argument('a'); ap.add_argument('b')
ap.add_argument('--what', default='certificates,core-pages,reference')
ap.add_argument('--show', type=int, default=10)
ap.add_argument('--exact', action='store_true', help='core pages byte for byte (default: modulo the counter suffix of renamed binders)')
o = ap.parse_args()
bad = 0

def files(root, sub):
    base = os.path.join(root, sub); out = {}
    for d, _, fs in os.walk(base):
        for f in fs: out[os.path.relpath(os.path.join(d, f), base)] = os.path.join(d, f)
    return out

# A binder renamed by capture-avoiding substitution takes a suffix from the GLOBAL counter
# (b -> b_430), so its spelling depends on how many proofs ran before in that image: a
# single exam and a slice (or two exams of different trees) print the same step with
# different suffixes.  same_mod_suffixes(): the two pages have the same tokens except
# NAME_<digits> tokens, and those correspond by a BIJECTION (consistent both ways, the
# unchanged ones included) -- a renaming, never a merge of two names.
SUF = re.compile(rb'[A-Za-z][A-Za-z0-9_-]*_[0-9]+')
SPLIT = re.compile(rb'([\s()]+)')
def same_mod_suffixes(x, y):
    tx, ty = SPLIT.split(x), SPLIT.split(y)
    if len(tx) != len(ty): return False
    fw, bw = {}, {}
    for a, b in zip(tx, ty):
        if SUF.fullmatch(a) or SUF.fullmatch(b):
            if not (SUF.fullmatch(a) and SUF.fullmatch(b)): return False
            if fw.setdefault(a, b) != b or bw.setdefault(b, a) != a: return False
        elif a != b: return False
    return True

def show(label, xs):
    xs = sorted(xs)
    print('  %s: %d%s' % (label, len(xs), (' -- ' + ' '.join(xs[:o.show]) + (' ...' if len(xs) > o.show else '')) if xs else ''))

for what in o.what.split(','):
    fa, fb = files(o.a, what), files(o.b, what)
    print('== %s: %d files in A, %d in B%s' % (what, len(fa), len(fb), ' (core pages modulo binder suffixes)' if what == 'core-pages' and not o.exact else ''))
    onlya = set(fa) - set(fb); onlyb = set(fb) - set(fa); diff = []
    for k in set(fa) & set(fb):
        if what == 'core-pages' and k.endswith('.gz'):
            x = gzip.open(fa[k]).read(); y = gzip.open(fb[k]).read()
            if not o.exact and x != y and same_mod_suffixes(x, y): y = x
        else:
            x = open(fa[k], 'rb').read(); y = open(fb[k], 'rb').read()
        if x != y: diff.append(k)
    show('only in A', onlya); show('only in B', onlyb); show('different', diff)
    bad += len(onlya) + len(onlyb) + len(diff)
    if what == 'certificates':
        for k in sorted(diff)[:o.show]:
            ra = {l.split(' ', 1)[0]: l for l in open(fa[k]) if l.startswith('(')}
            rb = {l.split(' ', 1)[0]: l for l in open(fb[k]) if l.startswith('(')}
            d = [n for n in set(ra) | set(rb) if ra.get(n) != rb.get(n)]
            print('    %s: %d record(s) differ: %s' % (k, len(d), ' '.join(sorted(d)[:5])))
print('== %s' % ('IDENTICAL' if bad == 0 else '%d difference(s)' % bad))
sys.exit(0 if bad == 0 else 1)
