#!/bin/sh
# build-vnb-view.sh -- (re)build ~/vnb, a navigation VIEW of ~/prover made of
# relative symlinks.
#
# ~/prover RETAINS its status as the official directory.  Nothing loads from
# ~/vnb; load.scm still resolves everything against *prover-dir*.  The view
# exists so the code base can be read in a grouped layout without moving a
# single file.
#
# GENERATED, not maintained.  The root of ~/prover gained 54 tracked files in
# the 60 days before this script was written -- about one a day -- so a view
# refreshed "periodically" would be stale within the week, silently.  It is
# rebuilt by the Stop hook on every turn instead, which costs milliseconds.
#
# RELATIVE links, so the pair survives `tar czf ... -C /home/ubuntu prover vnb'
# and resolves wherever it is extracted, provided the two are extracted as
# siblings.  tar stores a directory symlink as a link and does not descend, so
# the view adds ~60 near-zero-byte entries and duplicates no content.
#
# SAFETY: this script deletes only SYMLINKS and EMPTY directories.  It never
# removes a real file.  If it finds one it leaves it alone and reports it --
# an editor backup written through the view would otherwise be destroyed.
#
# ATOMIC: the view is built in a sibling temp directory and swapped in at the
# end.  Tearing the live view down first and rebuilding in place would mean that
# any failure in between -- and the Stop hook runs this on EVERY turn, right
# before the tarball is rolled -- leaves a stripped or half-built ~/vnb, and the
# tarball would faithfully ship the wreckage.  With the swap, a failure leaves
# the previous good view untouched.

set -eu

home=${VNB_VIEW_HOME:-/home/ubuntu}
src=$home/prover
view=$home/vnb

[ -d "$src" ] || { echo "build-vnb-view: no such directory: $src" >&2; exit 1; }

# ------------------------------------------------------- build out of the way
# $build is what everything below writes into; it becomes $view only at the end.
build=$home/.vnb-build.$$
trap 'rm -rf "$build"' EXIT INT TERM
rm -rf "$build"
mkdir -p "$build"

# ------------------------------------------------------------------ helpers
# link_into <subdir-under-view> <path-under-prover>
# Computes the ../ prefix from the link's own directory, so the link is relative.
link_into() {
  sub=$1; target=$2
  name=$(basename "$target")
  dir=$build/$sub
  mkdir -p "$dir"
  # How many "../" to climb from the LINK's own directory up to $home.
  # A link at vnb/a/b/ needs three: b -> a -> vnb -> home.  So it is one more
  # than the number of path components in $sub, and $sub = "." has none.
  # (`wc -l` counts newlines, so it under-counts components by one -- getting
  # this wrong produced a whole tree of dangling links that pointed at
  # vnb/prover/... instead of ../prover/...)
  if [ "$sub" = "." ]; then depth=1; else
    depth=$(printf '%s' "$sub" | awk -F/ '{print NF + 1}')
  fi
  up=""
  i=0
  while [ $i -lt $depth ]; do up="../$up"; i=$((i + 1)); done
  [ -e "$src/$target" ] || return 0        # skip what is not there
  ln -sfn "${up}prover/$target" "$dir/$name"
}

group() {
  sub=$1; shift
  for f in "$@"; do link_into "$sub" "$f.scm"; done
}

# ------------------------------------------------- the flat root, grouped
# The 42 .scm files at the root of ~/prover are the only ones that need
# per-file links; every subdirectory below is linked whole.  The count is prose,
# not a check -- the stderr report below is what actually catches an omission.
group scm-dir/kernel     wff expressions sequents deduction-graphs \
                         primitive-inferences theory macetes errors contexts \
                         rule-checkers-logic rule-checkers-schema rule-checkers-rewrite rule-checkers-oracle
group scm-dir/surface    interactive proof-commands parser input-context \
                         tactics-help driver-kit
group scm-dir/tactics    calc prep minimize sketch vlet transport suggest \
                         parts arith-eval prop contra mp push-not witness-tactics \
                         ineq-supply preamble cite-index harvest
group scm-dir/vocabulary structures operators number-systems glossary
group scm-dir/output     proof-tex tex-output wff-english proof-reader \
                         proven-theorems proof-map presentation major-theorems
group scm-dir/ledger     proof-debt audit clobber-guard page-audit page-audit-support \
                         replay-audit mint-attribution ra-diverge kernel-map-static kernel-map-trace
group scm-dir/build      load test-suite test-suite-negative mutation-check tactic-uses-data \
                         extend-band band-dump certificates

# ------------------------------------------ whole directories, linked once
# A directory link never goes stale when files are added inside it, which is
# why everything that can be one, is one.
link_into .        emacs                 # el-dir, below, is the friendly name
ln -sfn ../prover/emacs "$build/el-dir"
rm -f "$build/emacs"

# ------------------------------------------- the structure library, BY THEORY
# Split into theories rather than left flat, on the IMPS model: a theory is the
# unit, and the interpretations between theories (VNB's view-as functors) are a
# unit of their own.  20 of these files carry a `declare-structure'; the rest is
# the supporting material each theory family needs.
#
# This is the one per-file grouping below the root, so it is the one that can go
# stale -- a new structure-library file would simply not appear.  It cannot go
# stale SILENTLY: every .scm in the directory is linked, anything not classified
# below lands in _unfiled/ and is reported on stderr.
sl() { for f in $2; do link_into "library/structure-library/$1" "structure-library/$f.scm"; done; }

sl algebra    "semigroup monoid monoid-power group abelian-group ring ring-power \
               commutative-ring integral-domain integral-domain-laws euclidean-ring \
               field ideal polynomial ringoid setoid operation-properties subtype-laws \
               binomial poly-degree prod-of-sums"
sl module     "module finite-dimensional linear-functional zz-action matrix \
               elementary-matrix mat-equiv determinant finsum finprod"
sl metric     "metric-space metric-laws metric-completeness metric-completion \
               metric-continuity metric-open-sets metric-topology pseudometric \
               bounded-metric product-metric compactness separable inf-subsets top-space \
               metric-subspace c-metric-space trunc-metric baire-category \
               ascoli-arzela-statement cauchy-subsequence seq-compact-product subsequence-capture"
sl normed     "normed-ag normed-ag-metric normed-field normed-field-metric \
               normed-vector-space nvs-metric complex-inner-product dual-space \
               seminorm-hahn-banach frechet-open-mapping"
sl numbers    "complex extended-reals extended-reals-pos extended-arith nn-arith zz-arith \
               zz-divisibility qq-fractions real-powers numeric-instances \
               order-predicates order-lemmas rr-ineq scalar-inequalities linear-arith \
               sequences reduce mod-seq sqn nn-minus extended-sum summability cc-coords"
sl sets       "set-basics cardinality ordinals injection bijection bijection-derived \
               compose compose-typing sigma-algebra list-recursion measure integral \
               intersection-of set-vocabulary order-zorn measurable-space block-family-combinatorial"
sl oracles    "ring-simplify comm-ring-simplify ineq-oracle sos-oracle sos-arith"
sl functorial "views functoriality functor-invariance definitional-reclass"
sl calculus   "derivative one-sided-derivative diff-on antiderivative little-o \
               interval-calculus interval-extremum interval-taylor extreme-value \
               regulated regulated-primitive path-integral power-series cc-power-series"
sl misc       "references user-additions"

# the flat directory as well, as a single link: it never goes stale, so it is the
# escape hatch when the grouping above is behind.
ln -sfn ../../../prover/structure-library "$build/library/structure-library/_all"

# anything not classified above -- report it and file it, never drop it
for f in "$src"/structure-library/*.scm; do
  b=$(basename "$f")
  if ! find "$build/library/structure-library" -name "$b" -print -quit | grep -q .; then
    link_into "library/structure-library/_unfiled" "structure-library/$b"
    echo "build-vnb-view: structure-library/$b is not classified -- filed under _unfiled/" >&2
  fi
done

for d in theorem-library calculus; do link_into library "$d"; done
for d in scratch scratchpad stress-tests prove-scripts examples \
         structure-notes printouts archive; do link_into work "$d"; done
for d in docs reference; do link_into . "$d"; done
[ -d "$src/slides" ] && link_into . slides    # not yet created; linked when it is

# ------------------------------------------------------ top-level entries
for f in CLAUDE.md; do link_into . "$f"; done
for f in VNB VNB-nw VNB-with-compile prover mutation-check pull-vnb.sh \
         scan-case-fold.py build-vnb-view.sh \
         vnb-band vnb-band-compare vnb-suite vnb-probe vnb-slot vnb-test vnb-metrics-run \
         vnb-idle-stop vnb-idle-stop-install; do link_into run "$f"; done
# the proof-certificate store (2026-09-25): one .cert per theorem-library file
[ -d "$src/certificates" ] && link_into . certificates

# ------------------------------------------------ did we link every root .scm?
# The groups above are a HAND-MAINTAINED list, and a root .scm missing from it
# is simply absent from the view -- which looks exactly like a view that is
# complete.  That is how `glossary.scm', `test-suite-negative.scm' and
# `mutation-check.scm' stayed invisible until someone went looking for one of
# them by name.  Report the gap on stderr (the Stop hook discards stdout only)
# and name the fix, but do not fail: an unlinked file is a defect in the VIEW,
# and refusing to swap in an otherwise good tree would be the worse outcome.
for f in "$src"/*.scm; do
  name=$(basename "$f")
  if [ -z "$(find "$build/scm-dir" -name "$name" -print -quit 2>/dev/null)" ]; then
    echo "build-vnb-view: $name is at the prover root but in no group -- it is" >&2
    echo "                MISSING from ~/vnb.  Add it to a \`group' line." >&2
  fi
done

# ---------------------------------------------------------------- README
cat > "$build/README.md" <<'EOF'
# ~/vnb -- a navigation view of ~/prover

Every entry here is a **relative symlink** into `../prover`.  `~/prover` is the
official directory and the only one anything loads from; this tree exists so the
code base can be read in a grouped layout without moving a file.

**Generated.**  Rebuilt by `prover/build-vnb-view.sh`, which the Stop hook runs
on every turn.  Do not edit anything here expecting it to persist as a file --
edits *through* a link reach the real file in `../prover` and are safe; new
files created here are not, and the rebuild will report them.

## Installing a fresh tarball

On a machine that only READS this tree -- no git repo, nothing compiled, no
local edits -- clobber first and extract second:

    rm -rf ~/prover ~/vnb
    tar xzf prover-src.tar.gz -C ~

That is the whole recipe.  A fresh extract into an empty parent is correct by
construction: no stale links, no files deleted upstream left lying around, and
no rebuild step.  Both directories must land in the SAME parent -- the links are
relative (`../prover/...`), which is what makes them work wherever you unpack.

Two things the tarball does not carry, so clobbering discards them:

  * `.git` -- excluded.  Do NOT clobber a checkout you care about.
  * `*.com` / `*.bin` -- excluded.  A freshly unpacked tree is INTERPRETED, and
    nothing says so; the library load goes from ~24 s to ~11 min until you run
    `./VNB-with-compile` once.  Irrelevant if you only read the sources.

  * and anything you edited locally and have not sent back -- `docs/` above all,
    since the manual is the one file normally edited by hand.  Clobbering is for
    a mirror, not for a working copy.

If you would rather extract OVER an existing install than clobber, regenerate
the view afterwards:

    VNB_VIEW_HOME=<parent> sh <parent>/prover/build-vnb-view.sh

`tar` never deletes.  It corrects any link whose path it also carries, but a
link left over from an older grouping -- a file since moved from `algebra/` to
`sets/`, say -- survives the overlay and is left duplicated, or dangling if its
target is gone.  The rebuild tears every symlink down and rebuilds, so the tree
matches the script rather than the history of what was extracted there.  Note
this fixes the view only: a `.scm` deleted upstream still survives an overlay of
`prover/`, and `load.scm` may still load it.

    scm-dir/    the .scm files at the prover root, grouped
      kernel/       wff, expressions, sequents, deduction-graphs,
                    primitive-inferences, theory, macetes, errors, contexts
      surface/      interactive, proof-commands, parser, input-context,
                    tactics-help, driver-kit
      tactics/      calc, prep, minimize, sketch, vlet, transport, suggest,
                    parts, arith-eval, prop, contra, mp, push-not, witness-tactics,
                    ineq-supply, preamble, cite-index, harvest
      vocabulary/   structures, operators, number-systems, glossary
      output/       proof-tex, tex-output, wff-english, proof-reader,
                    proven-theorems, proof-map, presentation, major-theorems
      ledger/       proof-debt, audit, clobber-guard, page-audit(-support),
                    replay-audit, mint-attribution, ra-diverge, kernel-map-*
      build/        load, test-suite, test-suite-negative, mutation-check,
                    extend-band, band-dump, certificates
    certificates -> prover/certificates (the proof-certificate store, 2026-09-25)
    el-dir      -> prover/emacs
    library/
      structure-library/   split BY THEORY, on the IMPS model -- a theory is the
                           unit, and the interpretations between theories (VNB's
                           view-as functors) are a unit of their own:
        algebra/      semigroup -> monoid -> group -> ring -> field, plus ideals,
                      polynomials, setoid, ringoid, the operation properties
        module/       modules, finite-dimensionality, matrices, determinants, finsum
        metric/       metric spaces, completeness, continuity, topology, compactness
        normed/       the bridge: normed groups, fields, vector spaces
        numbers/      NN/ZZ/QQ/RR/CC and their arithmetic, order, sequences
        sets/         set basics, cardinality, ordinals, injections, sigma-algebras,
                      the CONS/TUPLES generation principle (list-recursion)
        oracles/      the trusted decision procedures
        functorial/   views, functoriality, invariance -- the theory INTERPRETATIONS
        misc/         references, user-additions
        _all          -> the flat directory, which never goes stale
        _unfiled/     anything the grouping above does not classify.  It is also
                      reported on stderr, so a new file cannot vanish silently.
      theorem-library, calculus
    docs        -> prover/docs        (the manual)
    reference   -> prover/reference   (generated at every prover load)
    work/       scratch, scratchpad, stress-tests, prove-scripts, examples,
                structure-notes, printouts, archive
    run/        VNB, VNB-with-compile, prover, and the helper scripts: vnb-band,
                vnb-band-compare, vnb-suite, vnb-probe, vnb-slot, vnb-test,
                vnb-metrics-run, vnb-idle-stop(-install)
EOF

# ---------------------------------------------------- carry over intruders
# A real file inside the OLD view (an editor backup written through a link, say)
# is not ours to delete: move it across so the swap does not lose it, and say so.
if [ -d "$view" ]; then
  find "$view" \! -type l \! -type d \! -name README.md 2>/dev/null | while read -r f; do
    rel=${f#$view/}
    mkdir -p "$build/$(dirname "$rel")"
    cp -p "$f" "$build/$rel"
    echo "build-vnb-view: carried over a real file found in the view: $rel" >&2
  done
fi

# --------------------------------------------------------------- swap it in
# rename(2) onto a directory needs the target gone first, so this is not a
# single atomic step -- but the window is one syscall wide and the new tree is
# already complete, which is the property that matters.
old=$home/.vnb-old.$$
if [ -d "$view" ]; then mv "$view" "$old"; fi
mv "$build" "$view"
rm -rf "$old"
trap - EXIT INT TERM

exit 0
