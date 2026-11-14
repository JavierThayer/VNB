#!/usr/bin/env python3
"""exam-slice-merge.py -- merge the N slices of a sliced exam into one tree.

    exam-slice-merge.py --dest TREE SLICE_DIR_1 ... SLICE_DIR_N [--reference-from K] [--dry-run]

Each SLICE_DIR holds what one slice's load wrote, pulled back from its worker:
    exam-slice/manifest.tsv        (load.scm, exam-slice-load-end!)
    exam-slice/core-results.tsv    (idem; the core replay's verdicts per theorem)
    certificates/                  (the whole store as that worker left it)
    core-pages/                    (*.core.gz of the proofs that RAN on that worker)
    reference/                     (optional; only the slice named by --reference-from is used)
SLICE_DIR_k is slice k (the order of the arguments is the slice number).

What it does, refusing (exit 1, nothing written) on any inconsistency:
 1. CHECK the manifests: every slice loaded the SAME contained proof files in the SAME
    order (one load list), each file is `off' in exactly one slice and that slice is the
    one its row names, and every manifest names N slices' worth of files.
 2. CERTIFICATES: for every file, TREE/certificates/<file>.cert := the OWNING slice's
    copy (the slice that loaded it in off mode); when the owner has none (a file whose
    every qed went away), TREE's is deleted.  Records written by a NON-owning slice
    (a theorem re-proved there because its certificate was invalid at the start of the
    night, or a fallback file) are ignored: the owner ran the same proof in off mode.
 3. CORE PAGES: TREE/core-pages/ is replaced by the union of each theorem's page from
    the slice that owns its file (theorem -> file read off the merged certificates);
    a page of a theorem in no certificate (a proof outside the contained files -- the
    generated projections and functorials, which run on every worker) is taken from
    slice 1.
 4. SUMMARY.txt: rebuilt from the per-theorem verdicts of the owners, in the format
    cc--summary-lines prints (core-capture.scm), so vnb-nightly-exam's readers parse it.
 5. REFERENCE (optional, --reference-from K): TREE/reference/ := SLICE_DIR_K/reference/.
Prints one line per step; `--dry-run' checks and counts without writing.
"""
import argparse, glob, os, shutil, sys

ap = argparse.ArgumentParser()
ap.add_argument('--dest', required=True)
ap.add_argument('--reference-from', type=int, default=0)
ap.add_argument('--dry-run', action='store_true')
ap.add_argument('--scripts-out', help='write the owners\' scripts of the major theorems (exam-slice/scripts.sexp of each slice) to this file')
ap.add_argument('slices', nargs='+')
a = ap.parse_args()
N = len(a.slices)
def die(msg):
    print('exam-slice-merge: REFUSED -- ' + msg, file=sys.stderr); sys.exit(1)

# ---------------------------------------------------------------- 1. manifests
man = []
for k, d in enumerate(a.slices, 1):
    p = os.path.join(d, 'exam-slice', 'manifest.tsv')
    if not os.path.exists(p): die('slice %d has no %s' % (k, p))
    rows = [l.rstrip('\n').split('\t') for l in open(p) if not l.startswith('#') and l.strip()]
    man.append(rows)
order = [r[0] for r in man[0]]
owner = {}
for k, rows in enumerate(man, 1):
    if [r[0] for r in rows] != order:
        die('slice %d loaded a different list of proof files than slice 1 (load lists differ)' % k)
    for r in rows:
        if int(r[1]) < 1 or int(r[1]) > N: die('slice %d: %s placed in slice %s of %d' % (k, r[0], r[1], N))
        if (r[2] == 'off') != (int(r[1]) == k):
            die('slice %d: %s is %s but placed in slice %s' % (k, r[0], r[2], r[1]))
        if r[2] == 'off': owner[r[0]] = k
for f in order:
    if f not in owner: die('%s was examined by no slice' % f)
place = [int(r[1]) for r in man[0]]
for k, rows in enumerate(man[1:], 2):
    if [int(r[1]) for r in rows] != place: die('slice %d placed the files differently from slice 1 (plans differ)' % k)
proven = sum(int(r[4]) for rows in man for r in rows if r[2] == 'off')
reproven = sum(int(r[4]) for rows in man for r in rows if r[2] == 'on')
print('exam-slice-merge: %d slices, %d proof files, each examined once; %d proofs run off-mode, %d re-run outside their slice'
      % (N, len(order), proven, reproven))

# ---------------------------------------------------------------- 2. certificates
def cert(d, f): return os.path.join(d, 'certificates', f + '.cert')
def names_in(p):
    with open(p, errors='replace') as fh:
        return [l[1:].split(' ', 1)[0] for l in fh if l.startswith('(') and not l.startswith('(vnb-certificate-file')]
copied = deleted = same = 0
thm_owner = {}
thm_file = {}           # theorem -> position of its file in the load list
for f in order:
    src = cert(a.slices[owner[f] - 1], f); dst = cert(a.dest, f)
    if os.path.exists(src):
        for n in names_in(src): thm_owner[n] = owner[f]; thm_file[n] = order.index(f)
        if os.path.exists(dst) and open(src, 'rb').read() == open(dst, 'rb').read():
            same += 1; continue
        copied += 1
        if not a.dry_run:
            os.makedirs(os.path.dirname(dst), exist_ok=True); shutil.copyfile(src, dst + '.tmp'); os.replace(dst + '.tmp', dst)
    elif os.path.exists(dst):
        deleted += 1
        if not a.dry_run: os.remove(dst)
print('exam-slice-merge: certificates: %d unchanged, %d rewritten, %d deleted (%d theorems)' % (same, copied, deleted, len(thm_owner)))

# ---------------------------------------------------------------- 3. core pages
def page_name(fn): return fn[:-len('.core.gz')].replace('%2F', '/')
pages = {}            # file name -> source path
extra = 0
for k, d in enumerate(a.slices, 1):
    for p in glob.glob(os.path.join(d, 'core-pages', '*.core.gz')):
        fn = os.path.basename(p); n = page_name(fn)
        o = thm_owner.get(n, 1)
        if o == k: pages[fn] = p
        else: extra += 1
lost = [n for n in thm_owner if (n.replace('/', '%2F') + '.core.gz') not in pages]
print('exam-slice-merge: core pages: %d kept from their owners, %d duplicates from non-owners ignored, %d theorems of the certificates without a page'
      % (len(pages), extra, len(lost)))
if not a.dry_run:
    cp = os.path.join(a.dest, 'core-pages')
    new = cp + '.merge-new'
    shutil.rmtree(new, ignore_errors=True); os.makedirs(new)
    for fn, p in pages.items(): shutil.copyfile(p, os.path.join(new, fn))

# ---------------------------------------------------------------- 4. SUMMARY.txt
lowered, failed, lines, stats = set(), {}, {}, {}
for k, d in enumerate(a.slices, 1):
    p = os.path.join(d, 'exam-slice', 'core-results.tsv')
    if not os.path.exists(p): continue
    # the rows of each kind are written newest first (core-capture's lists): reversed here,
    # so the seq number is the qed order within the slice
    rows = [l.rstrip('\n').split('\t') for l in open(p, errors='replace')]
    rows.reverse()
    for seq, r in enumerate(rows):
        if r[0] == 'stat':
            stats.setdefault(r[1], []).append(r[2]); continue
        n = r[1] if r[0] in ('lowered', 'failed') else r[2]
        if thm_owner.get(n, 1) != k: continue
        if r[0] == 'lowered': lowered.add(n)
        elif r[0] == 'failed': failed[n] = r[2]
        elif r[0] == 'line': lines.setdefault(r[1], []).append(((thm_file.get(n, -1), seq), r[3]))
# in load order: the file's place in the load list, then the qed order inside the slice (a
# theorem outside the contained files -- run on every worker -- is placed first)
lines = {k: [t for _, t in sorted(v)] for k, v in lines.items()}
nb = len(lines.get('kernel-bill', [])); no = len(lines.get('kernel-oracles', []))
nref = len(lines.get('core-replay-refused', [])); nrai = len(lines.get('core-replay-raised', []))
replay_on = any(v == '1' for v in stats.get('replay_on', []))
replay_s = sum(int(v) for v in stats.get('replay_s', []))
out = []
out.append(';; kernel-bill: %d agree, %d differ' % (len(lowered) - nb, nb))
out += lines.get('kernel-bill', [])[:40]
out.append(';; kernel-oracles: %d differ' % no)
out += lines.get('kernel-oracles', [])[:20]
out.append(';; core-lowering: %d page(s) lowered, %d failed (merged from %d slices by exam-slice-merge.py; per-slice step counts are in each slice log)'
           % (len(lowered), len(failed), N))
if replay_on:
    out.append(';; core-replay: core-replayed %d of %d (%d refused, %d raised; replay %d s wall, summed over %d slices)'
               % (len(lowered) - nref - nrai, len(lowered), nref, nrai, replay_s, N))
    out += lines.get('core-replay-refused', []) + lines.get('core-replay-raised', [])
text = '\n'.join(out) + '\n'
print('exam-slice-merge: SUMMARY: ' + out[0][3:] + ('; ' + [l for l in out if l.startswith(';; core-replay:')][0][3:] if replay_on else ''))
if not a.dry_run:
    with open(os.path.join(new, 'SUMMARY.txt'), 'w') as fh: fh.write(text)
    old = cp + '.merge-old'
    shutil.rmtree(old, ignore_errors=True)
    if os.path.exists(cp): os.rename(cp, old)
    os.rename(new, cp); shutil.rmtree(old, ignore_errors=True)

# ---------------------------------------------------------------- 4b. the major theorems' scripts
if a.scripts_out:
    kept = {}
    for k, d in enumerate(a.slices, 1):
        p = os.path.join(d, 'exam-slice', 'scripts.sexp')
        if not os.path.exists(p): die('slice %d has no %s' % (k, p))
        for l in open(p, errors='replace'):
            if not l.startswith('('): continue
            n = l[1:].split(' ', 1)[0].rstrip(')')
            if thm_owner.get(n, 1) == k: kept[n] = l
    if not a.dry_run:
        with open(a.scripts_out + '.tmp', 'w') as fh:
            for n in sorted(kept): fh.write(kept[n] if kept[n].endswith('\n') else kept[n] + '\n')
        os.replace(a.scripts_out + '.tmp', a.scripts_out)
    print('exam-slice-merge: scripts of the major theorems: %d, from their owners' % len(kept))

# ---------------------------------------------------------------- 5. reference
if a.reference_from:
    src = os.path.join(a.slices[a.reference_from - 1], 'reference')
    if not os.path.isdir(src): die('slice %d has no reference/' % a.reference_from)
    if not a.dry_run:
        dst = os.path.join(a.dest, 'reference')
        subprocess_ok = os.system("rsync -a --delete '%s/' '%s/'" % (src, dst)) == 0
        if not subprocess_ok: die('rsync of reference/ failed')
    print('exam-slice-merge: reference/ from slice %d' % a.reference_from)
print('exam-slice-merge: done' + (' (dry run: nothing written)' if a.dry_run else ''))
