#!/bin/bash
# pull-vnb.sh -- sync the prover tree FROM the build box to this machine, then
# compile and launch.  Runs on the LOCAL machine (the one with Emacs on it).
#
#   ./pull-vnb.sh              full rebuild: every .com discarded and remade
#   ./pull-vnb.sh --keep-com   incremental: recompile only what actually changed
#   ./pull-vnb.sh --no-launch  sync and compile, but do not start Emacs
#
# The point of the exercise is that a FAILED FETCH MUST NOT LOOK LIKE A
# SUCCESSFUL ONE.  With `set -e` and an explicit check on the download, a box
# that has moved (EC2 hands out a new public IP on every stop/start unless the
# address is elastic) stops the script instead of quietly rebuilding yesterday's
# sources and letting you test a fix that was never delivered.

set -euo pipefail

# ---- configuration --------------------------------------------------------
REMOTE_HOST="${VNB_REMOTE:-ubuntu@44.211.233.212}"
REMOTE_TAR="prover-src.tar.gz"
SSH_KEY="$HOME/.ssh/claude-api-key-pair.pem"
DEST="$HOME/prover"
STAGE="$HOME/.vnb-sync"          # staging area; never the live tree

# Local-only paths, preserved across the sync.  --delete removes whatever the
# tarball does not carry, and the tarball deliberately carries neither .git nor
# the compiled artifacts -- so without these excludes the sync would erase a
# local clone's history and every .com, the latter making --keep-com a lie.
# Compiled artifacts are handled explicitly in step 4 instead.
KEEP=(--exclude=.git --exclude=scratchpad/ --exclude=scratch/
      --exclude='*.com' --exclude='*.bin' --exclude='*.bci' --exclude='*.ext')

KEEP_COM=no
LAUNCH=yes
for arg in "$@"; do
    case "$arg" in
        --keep-com)  KEEP_COM=yes ;;
        --no-launch) LAUNCH=no ;;
        *) echo "pull-vnb.sh: unknown option $arg" >&2; exit 2 ;;
    esac
done

# ---- 1. fetch, and prove we fetched ---------------------------------------
# Into the staging area, not over the copy we are still using: if this step
# dies, the working tree is untouched and the old tarball is still on disk.
mkdir -p "$STAGE"
echo "pull-vnb: fetching $REMOTE_HOST:$REMOTE_TAR ..."
scp -i "$SSH_KEY" "$REMOTE_HOST:~/$REMOTE_TAR" "$STAGE/$REMOTE_TAR"

[ -s "$STAGE/$REMOTE_TAR" ] || { echo "pull-vnb: downloaded tarball is empty." >&2; exit 1; }
tar tzf "$STAGE/$REMOTE_TAR" >/dev/null \
    || { echo "pull-vnb: downloaded tarball is corrupt." >&2; exit 1; }

# Say out loud what arrived, so a stale fetch is visible rather than inferred.
echo "pull-vnb: got $(du -h "$STAGE/$REMOTE_TAR" | cut -f1), built $(date -r "$STAGE/$REMOTE_TAR" '+%Y-%m-%d %H:%M')"

# ---- 2. stop anything holding the old binaries ----------------------------
# -x matches the EXECUTABLE.  `pkill -f mit-scheme' matches whole command lines
# and will happily kill the shell you launched this from.  `|| true' because
# pkill exits 1 when nothing matches, which is the normal case.
pkill -x mit-scheme 2>/dev/null || true
sleep 1
pkill -9 -x mit-scheme 2>/dev/null || true

# ---- 3. unpack to staging, then swap in with deletes ----------------------
rm -rf "$STAGE/tree"
mkdir -p "$STAGE/tree"
tar xzf "$STAGE/$REMOTE_TAR" -C "$STAGE/tree"      # one step; keeps the .gz
[ -d "$STAGE/tree/prover" ] || { echo "pull-vnb: no prover/ in the tarball." >&2; exit 1; }

# rsync, not tar-over-the-top: --delete removes files that went away upstream.
# A plain extraction only ever ADDS, so every renamed or deleted file survives
# locally forever (this tree has renamed plenty: X->CARR, D->DIST, ID->IDEN).
mkdir -p "$DEST"
echo "pull-vnb: syncing into $DEST ..."
rsync -a --delete "${KEEP[@]}" "$STAGE/tree/prover/" "$DEST/"

# ---- 4. compiled artifacts ------------------------------------------------
# The tarball ships no .com/.bin, so the tree is INTERPRETED as it stands: 11
# minute loads, and nothing tells you (CLAUDE.md, "COMPILE THE TREE FIRST").
#
# Full (default): discard every local binary and rebuild.  Slow, always right.
# --keep-com: rsync preserves each source's mtime from the build box, so
# load.scm's file-fresh-com? sees an unchanged .scm as older than its local .com
# and skips it -- seconds instead of ten minutes.  Use the default if an upstream
# change ever went BACKWARDS in time, which is the one case mtimes misjudge.
if [ "$KEEP_COM" = yes ]; then
    echo "pull-vnb: keeping existing .com (incremental compile)."
    COMPILE_ARGS=()
else
    echo "pull-vnb: discarding compiled artifacts (full rebuild)."
    find "$DEST" \( -name '*.com' -o -name '*.bin' -o -name '*.bci' -o -name '*.ext' \) -delete
    COMPILE_ARGS=(--full)
fi

# ---- 5. compile, then launch ----------------------------------------------
if [ "$LAUNCH" = no ]; then
    # Compile without the Emacs launch: same load, then stop.
    ( cd "$DEST" && env VNB_RECOMPILE=1 mit-scheme --heap 120000 --quiet \
        --load "$DEST/load.scm" --eval '(begin (compile-vnb!) (exit))' )
    echo "pull-vnb: compiled; not launching (--no-launch)."
    exit 0
fi

exec "$DEST/VNB-with-compile" "${COMPILE_ARGS[@]}"
