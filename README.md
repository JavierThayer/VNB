# VNB

VNB is a proof checker and a mathematical assistant: it checks proofs, and it
helps a user discover them.  It is written in MIT/GNU Scheme, with a user
interface in GNU Emacs and reference documentation in a web view.  The logical
framework is von Neumann-Bernays set theory, with a large stock of ready-made
constructors.

**Where things are:** `MAP.md` lists every source file by role (kernel, surface,
tactics, vocabulary, output, ledger, build; the structure library by theory), as
links; it is the grouped view `~/vnb` of the tarball, rendered for the flat
directory a repository shows.

## Requirements

* **MIT/GNU Scheme 12.1** -- required.
* **GNU Emacs** -- required for the user interface.
* Optional, each enabling one feature and nothing else:
  * `pdflatex` and `dvipng` -- LaTeX-rendered sequents in the workspace, and
    printed proofs;
  * `graphviz` (`dot`) -- the structure graph;
  * `python3` -- a few helper scripts.

## First run

Run these once, in this order.  **From GitHub**, clone and check the release
before running anything (*Verifying a release*, below), then start at `cd`:

    git clone https://github.com/JavierThayer/VNB.git ~/prover
    # ... check the release: steps 1-3 of "Verifying a release" ...

**From the tarball** (a copy handed to you directly):

    tar xzf prover-src.tar.gz -C ~      # unpacks ~/prover and ~/vnb

Then, either way:

    cd ~/prover
    ./VNB-with-compile                  # about 10 minutes
    ./prover --build-band               # about 4 minutes
    ./VNB                               # the Emacs workspace

The archive holds two directories and they must land in the **same parent**:
`prover` is the system, and `vnb` is a navigation view of it made of relative
symlinks (`../prover/...`).  Nothing loads from `vnb`, so if you unpack only
`prover` you lose nothing but that view.

**The first step is not optional, and skipping it is the most common way to
form a wrong impression of this system.**  The distributed tree contains no
compiled files, so out of the box every source file is interpreted.  Measured
on the development machine, interpreted against compiled:

| | interpreted | compiled |
|---|---|---|
| library load | about 11 minutes | 24 seconds |
| full test suite | about 42 minutes | about 6 minutes |

Nothing on screen reports this.  A load that seems inexplicably slow is almost
always an uncompiled tree; `ls *.com` answers the question in one command.

The second step saves a heap image (`vnb.band`) with the whole library already
loaded, after which `./prover -b` starts in about 0.2 seconds instead of
re-proving the library.  The image is not distributed because it is roughly
eleven times the size of this entire source tree, and because an MIT Scheme
band is tied to the exact Scheme build that wrote it: one built elsewhere would
fail to load, with an error that does not explain itself.  Building it locally
is the four minutes above.

Rebuild the band after editing any `.scm` file outside `scratchpad/`,
`scratch/` or `prove-scripts/`; `./prover -b` warns when the band is older than
a source file, so this is not something to remember unaided.

## Everyday use

    ./VNB                     # Emacs workspace (graphical)
    ./VNB -nw                 # terminal-only
    ./prover                  # plain REPL
    ./prover -b               # REPL from the saved image -- the usual choice
    ./prover -b file.scm      # run a proof script against the image
    ./prover -i file.scm      # run a script, then stay in the REPL

After editing prover sources, `./VNB-with-compile` recompiles and relaunches.
An edited file that is not recompiled loads from source, which is harmless for
a leaf proof script and ruinous for a core file.

The full check suite is separate from the launcher, and must be run **alone and
in the foreground** -- started alongside another Scheme process it can die
partway through and still exit 0:

    timeout 3600 mit-scheme --quiet --load test-suite.scm < /dev/null

It prints `=== SUMMARY: N passed, M failed ===`.  Check for that line; exit 0
does not by itself mean the suite ran.

## Where things are

| | |
|---|---|
| `CLAUDE.md` | the working brief: operational facts, traps, and why decisions were made |
| `docs/manual.tex` | the manual (master file; chapters are `ch-*.tex`) |
| `reference/` | **generated** at load -- theorem catalogue, definitions, glossary, debt ledger. Never hand-edit |
| `structure-library/` | definitions, structures, vocabulary, warranted supports |
| `theorem-library/` | proofs that reach `qed`; loaded, gated and counted at every load |
| `emacs/` | the Emacs interface |
| `scratchpad/`, `scratch/` | throwaway drivers; not part of the library |

`CLAUDE.md` is the file to read second.  It is written for a working
contributor rather than a new reader, and it records the failures that produced
each rule, which is usually the fastest way to understand one.

## Verifying a release

Before running VNB, check that what you downloaded is what its author published.
Each release `vYYYY.MM.DD` has, in `releases/`, a **manifest** -- the SHA-256 hash of
every file of the repository at the release's commit -- and the author's **SSH
signature** of it.  Checking both takes standard tools only (OpenSSH 8.0 or later,
`git`, `sha256sum`); no VNB script is involved.

1. **Get the author's public signing key**, and check it in a place that is not GitHub:
   * GitHub: <https://api.github.com/users/JavierThayer/ssh_signing_keys>, and the
     key printed below, under *The signing key*;
   * the fingerprint published off GitHub (see *The signing key*).  The GitHub copies
     alone are not enough: whoever takes over the author's GitHub account can change
     both of them, and this README with them.

   Put it in a file `vnb-signers`, one line:

        javier namespaces="vnb-release" ssh-ed25519 AAAA...the key...

2. **Check the signature** (in your clone; `V` is the release):

        V=v2026.11.17
        cp releases/$V.manifest releases/$V.manifest.sig ..
        ssh-keygen -Y verify -f ../vnb-signers -I javier -n vnb-release \
            -s ../$V.manifest.sig < ../$V.manifest

   It must print `Good "vnb-release" signature for javier`.

3. **Check the files** against the manifest, at the release's commit:

        git checkout $(sed -n 's/^# commit //p' ../$V.manifest)
        diff <(grep -v '^#' ../$V.manifest) <(git ls-files -z | xargs -0 sha256sum) \
            && echo "all files match"

   (On Windows, clone with `git -c core.autocrlf=false clone ...`: converted line
   endings change every hash.)

### What checking protects you from, and what it does not

If the three steps succeed, you are protected from:

* **a doctored copy**: a fake fork, a tampered mirror, a file changed on the way to you;
* **a forged release**: no one can sign a release without the author's private key,
  which exists only on the author's own computer -- not on GitHub, and not on the
  server where VNB is developed;
* **a planted proof certificate**: certificates are files of the release, checked like
  every other file.

You are **not** protected from:

* **changes after the download.**  The check is made once.  A file changed later -- by a
  program, an intruder or a child -- goes unnoticed unless you check again.  Step 3 can
  be rerun at any time, and `vnb-start` (below) reruns a check at every start;
* **a computer already taken over.**  An intruder in control of your machine can change
  VNB, the checking tools, or `ssh-keygen` itself.  No signature protects a computer
  that is no longer yours;
* **a stolen key.**  If the author's key and passphrase were stolen, the thief's releases
  would check as good until the author withdraws the key;
* **bad code.**  A good signature says the files are the ones the author published, not
  that they are harmless.  VNB is a program: run it under an ordinary user account,
  never as root;
* **wrong proofs.**  The signature does not make a theorem true.  For that you need not
  trust the author: the exam, `VNB_CERTIFIED=off ./prover --build-band` (several hours),
  re-runs every proof through VNB's kernel, and the certificates in the release are then
  only a cache.

Checking hides nothing: it is about where the files came from, not about who can read
them.  VNB keeps your own work on your own computer.

### Keeping your copy checked: `vnb-start`

`trust/` holds two scripts, `vnb-trust` and `vnb-start`.  After the three steps, copy
them OUT of the tree, so that a change to the tree cannot change them too:

    mkdir -p ~/bin && cp trust/vnb-trust trust/vnb-start ~/bin/

Then, once, with a key of your own (`ssh-keygen -t ed25519 -f ~/.ssh/vnb-signing`):

    # first the two build steps of "First run" (VNB-with-compile, prover --build-band):
    # they write the compiled files and the band, which the check covers
    vnb-trust setup ~/.ssh/vnb-signing
    vnb-trust accept ~/prover            # "this is the tree I checked, now built"

From then on start VNB with `vnb-start`.  It hashes the tree, starts VNB if it is the
tree you accepted, and otherwise lists the files that changed and does not start.  It
catches accidents and casual tampering; it cannot defend a computer taken over (above).
After installing a new release, check it (steps 1-3) and run `vnb-trust accept` again.

### The signing key

Javier Thayer's release signing key (ed25519), added 2026-11-17:

    javier namespaces="vnb-release" ssh-ed25519 AAAAC3NzaC1lZDI1NTE5AAAAINvqpG1lfo/uew0X/luQERtTgM5gS7Jmj13E8NuX5tH8

Its fingerprint is `SHA256:pvv9BBY6uAVZrlz0H7G/xub84NareBQos+3Af8jHTvk` (`ssh-keygen -lf` on a file holding the key prints it).
Compare it with the key GitHub lists for the account `JavierThayer`, and with the
fingerprint published off GitHub, in the author's Bluesky profile:
<https://bsky.app/profile/javiertf.bsky.social>.  If any of them
differ, stop.

## Licence

VNB is released under the MIT License: see `LICENSE`.  MIT/GNU Scheme and GNU
Emacs, which VNB runs on, are not bundled; each is licensed separately by its
authors.  No third-party source code is included.
