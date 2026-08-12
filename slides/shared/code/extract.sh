#!/bin/sh
# extract.sh -- regenerate every listing named in MANIFEST from the source tree.
#
# Run from anywhere:  sh shared/code/extract.sh   (or `make code' in slides/).
# Fails, loudly and non-zero, if a source file is missing or a range is empty --
# a silently empty listing on a slide is the failure mode this exists to prevent.

set -e
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)          # prover/
status=0

while IFS= read -r line; do
    case "$line" in ''|\#*) continue ;; esac
    out=$(printf '%s\n' "$line" | cut -f1)
    src=$(printf '%s\n' "$line" | cut -f2)
    rng=$(printf '%s\n' "$line" | cut -f3)
    first=${rng%-*}
    last=${rng#*-}
    if [ ! -f "$root/$src" ]; then
        echo "extract.sh: MISSING SOURCE $src (for $out)" >&2
        status=1
        continue
    fi
    sed -n "${first},${last}p" "$root/$src" > "$here/$out"
    if [ ! -s "$here/$out" ]; then
        echo "extract.sh: EMPTY RANGE $src $rng (for $out)" >&2
        status=1
        continue
    fi
    echo "  $out  <-  $src:$rng  ($(wc -l < "$here/$out") lines)"
done < "$here/MANIFEST"

exit $status
