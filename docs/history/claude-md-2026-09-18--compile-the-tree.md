<!-- VERBATIM copy of a section of CLAUDE.md as it stood on 2026-09-18, moved here when
CLAUDE.md was trimmed to its operational rules.  Nothing was edited.  The dated findings,
measurements and case histories behind each rule in CLAUDE.md are in this text. -->

## COMPILE THE TREE FIRST -- everything below depends on it

`.com`/`.bin` are in `.gitignore` AND excluded from the tarball, so a fresh clone or
unpacked tarball is **interpreted**, and nothing tells you. Compiled vs interpreted, on
this box:

    library load     24 s   vs  ~11 min
    full test suite   6 min vs  ~42 min

Compile once, after a clone/unpack (~10 min, includes one source load):

    ./VNB-with-compile          # or, from a REPL that has loaded load.scm:
    (compile-vnb!)              # incremental: skips files whose .com is fresh
    (recompile-vnb!)            # source-load everything, then compile

If you are ever tempted to conclude "this box is slow", check `ls *.com` first.
`compile-vnb!` skips `*vnb-no-compile-files*` (`test-suite`, `driver-kit`,
`clobber-guard`: the latter two capture `(the-environment)`, which compiles WITHOUT
COMPLAINT and then reports the wrong frame) and any file using a top-level macro
(the .com aborts on load).

After editing a `.scm`, delete BOTH the `.com` and the `.bin`, or Scheme silently
loads the stale binary. `load.scm` names files without extension and prefers `.com`.
(`file-fresh-com?` compares mtimes, so a plain re-save is usually enough.)

**Then RE-COMPILE the files you edited, before you run anything.** An edited file
loads from source; that is fine for a leaf proof script and ruinous for a core
file. Editing `wff.scm` (whose `subst-free`/`free-vars`/`validate-wff!` run in every
inner loop) took one library load from 24 s to **over 14 minutes**. Compiling the
edited files back is a couple of seconds and needs no loaded library:

    mit-scheme --quiet --eval '(begin (compile-file "/abs/path/wff.scm") (exit))'

`compile-vnb!` does the whole tree incrementally but wants a loaded REPL -- which is
the very load you just made slow. Compile first, load second.

**And check WHICH files it actually compiled.** `vnb-file-uses-bc*-macro?` (load.scm)
decides what `compile-vnb!` skips. It is now done **with the READER** (2026-08-15), and
the two failed textual attempts before it are the argument for that:

* It began as a raw per-line `substring?` for `(bc* ` / `(declare-structure ` / `(vlet `,
  which matched COMMENTS -- so `macetes.scm` (`(bc* ` at :134) and `interactive.scm` (a
  docstring at :2619) were silently never compiled. Fixed 2026-08-12 by cutting each line
  at its first `;`.
* Cutting at `;` does not help when the mention is DATA: a string (`suggest.scm:2733`,
  `(string-append "(bc* '" ...)`), a quoted list (`suggest.scm:3851`,
  `(memq (car step) '(bc* fact ta))`), or an alist key (`tactics-help.scm`,
  `(bc* . "a library theorem's ...")` and `(bc* composite (backchain))`). So **`suggest`
  and `tactics-help` -- the two copilot files, and the ones most likely to be edited --
  were skipped forever**, along with `proof-tex`. A line scan cannot fix the last two at
  all: the quote making them data is on an enclosing line.

The check now `read`s the file and looks for the macro applied in CODE position
(`vnb--form-uses-macro?`, which returns #f under `quote`). The reader knows what a
string, a comment and a quote are; a textual scan can only guess at all three. After the
change the skip list is 31 files, every one a genuine `declare-structure` structure or
`bc*` driver, and `*vnb-top-level-macros*` keys are SYMBOLS now, not strings.

**How it was found, and why it matters:** the user unpacked the tarball fresh, ran
`./VNB-with-compile --full`, and had **31** root `.com` files where this box had 33. The
one-liner that names the difference is worth keeping:

    cd ~/prover; for f in *.scm; do b="${f%.scm}"; [ -f "$b.com" ] || echo "  $b"; done

The legitimately-uncompiled root set is 8: `clobber-guard driver-kit load mutation-check
proof-tex proven-theorems test-suite-negative test-suite` -- and `proof-tex` left that
list with this fix, so it is 7. Anything else in that output is a file the scan is
wrongly skipping. Compiling the three recovered files took the **full suite from ~6
minutes to 3m12s**. The failure mode is silent and it compounds: an uncompiled core file
costs the whole library load (an interpreted `wff.scm` once took a 24 s load to over 14
minutes) and nothing reports it. If a load is inexplicably slow, the question is not
"is the tree compiled" but "is THIS file compiled": `ls -la <file>.com`.

**But never compile a file that USES a top-level macro that way.** `compile-file` from a
bare REPL cannot see `bc*` (interactive.scm), `declare-structure` (structures.scm) or
`vlet` (vlet.scm) -- the three entries of `*vnb-top-level-macros*` (load.scm:1236) -- so
it compiles the form as an APPLICATION: a fresh `structure-library/ring.com` then dies on
load with `;Unbound variable: carr`, stranding every file after it. `compile-vnb!` knows
this (`*vnb-top-level-macros*` in load.scm) and SKIPS such files -- they load from source,
which costs nothing measurable (their work is in the compiled procedures they call:
moving the whole structure-library to source-load changed a cold load by under a second,
36.8 s -> 36.9 s). So `(compile-vnb!)` from a loaded REPL is the safe recipe; the one-file
`--eval (compile-file ...)` is only for files with no macro use.

**There is no skip-proofs mode.** `VNB_SKIP_PROOFS` was removed (2026-07-09): it had
silently stopped working, and a mode that installs goals as theorems without running their
tactics would give you a library whose `qed` bills read `trust: none` about proofs nobody
checked. Compiling is the honest speedup. If you find the variable named in an old
comment, the comment is stale.

