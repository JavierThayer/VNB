# VNB proof checker -- working brief

VNB is a proof checker and more generally a math assistant to help
users discover proofs. It is written in MIT Scheme with a user interface in
GNU/Emacs. Much of the documentation is available using a web
interface. There is also a manual which needs periodic update.  The
logical framework is von Neumann-Bernays set theory but with copious
ready-made constructors. Its research state (what is proven, what is
next) lives in Claude's memory index, not here. This file holds the
operational facts that are expensive to rediscover.

## Where the project is going

The **prove-theorem stage is done** (2026-07-11): `spans-submodule-fg` -- and with it
`submodule-fg` -- is proven, with no asserted step. Its purpose was never the theorems
themselves: it was to exercise and stress the machinery, and it delivered, right at the
end, the simultaneous-substitution bug in the macete rewriter (below).

Then the project **refocuses**, onto three things:

1. **Print proofs and read proofs.** `proof-tex` (full trace) and `proof-reader` (sketch)
   exist and are faithful, but they report the *official* level -- three lemma citations --
   where a human wants the *content* level: "Since `a` is a Euclidean ring, `a` is a ring."
   The table is BUILT (`operators.scm`, the ONE table keyed by head symbol; populated by
   `def-predicate` / `def-functoid` at definition time via `register-operator!`, and the
   reading declared next to the definition with `notation!`). It is read by `wff-english`
   (`operator-ref` / `operator-english`), `describe-structure` and `OPERATORS.md`.
   `expr->tex` reads it too, and the old entry here -- "expr->tex does NOT read it" --
   was half wrong: the hook (`operator-render-tex`, tex-output.scm) had been in the
   `expr->tex` cond all along, but BELOW tex-output's own binop/special tables and,
   more to the point, **no head in the tree declared a `tex` template** (195 `notation!`
   calls, 0 with a `'tex` key), so it never fired. Fixed 2026-08-10: the branch now sits
   ABOVE the two built-in tables (a declaration beats a default) and BELOW the
   arithmetic-prefix branch (a fluid MODE beats a declaration), and `==` declares
   `($1 \simeq $2)` -- the manual's own reading -- instead of falling through to
   `\operatorname{==}(...)`. `abs` got the CARD treatment (`\lvert x \rvert`) in
   tex-output's special table, where it belongs: it is a primitive with no operator entry.
   STILL OUTSTANDING on the reader: collapse a run of subtype-subsumption
   citations (`register-definitional-structure!` already records the parent chain); capture
   the goal BEFORE each step, not only after, so the reader can always name an existential's
   bound variable (see the `proof-reader--goal-before` comment); render `IS-EUCLIDEAN-RING(a)`
   as "a is a Euclidean ring".

**Where a definition lives, and the trap under it.** `def-predicate` / `def-constant`
install a THEOREM (the defining iff), so they land in `theory-definitions` and hence in
`reference/DEFINITIONS.md`. `def-functoid` installs only a rewrite MACETE -- no theorem --
so a functoid is in neither that registry nor `*theorem-table*`. Two consequences, and they
are the same fact seen from two sides:

* `mac` unfolds a functoid in a GOAL; **`mac-h` cannot unfold one in an ASSUMPTION by the
  functoid's own name.** It warns `unknown theorem/macete` and the driver continues with
  the hypothesis untouched. A constructor whose members get read out of the context
  therefore needs a membership `iff` beside it (`span-membership`,
  `principal-ideal-membership`, `zz-bezout-set-membership`, ...). That iff is a
  CONSEQUENCE of the definition -- the functoid unfold composed with the SEP separation
  schema -- not the definition.

  **But it does NOT have to be ASSERTED, and this entry said for weeks that it did.**
  The unfold equation is PROVABLE, one line per functoid, and the proof is `modulo 0`:

      (sp (make-wff '(FORALL a_ (FORALL m_ (== (FINSUPP a_ m_) (SEP f_ ...))))))
      (di) (mac 'FINSUPP) (qrfl)

  `mac` unfolds the functoid in the GOAL -- which is the half that works -- and `qrfl`
  closes the resulting `X == X`. The result is a THEOREM, and `mac-h` rebuilds its rule
  from the theorem table, so `(mac-h 'finsupp-unfold h)` rewrites the hypothesis into a
  literal SEP membership that `sep-me` reads apart. Demonstrated side by side in
  `scratchpad/pl-probe2.scm` (2026-08-20): `(mac-h 'FINSUPP 1)` warns and no-ops;
  `(mac-h 'finsupp-unfold 1)` rewrites, then `(sep-me)` `(ass)` closes. Seven such
  theorems for SUPP/FINSUPP/POLY are in `theorem-library/poly-membership.scm`, all
  `modulo 0`. `interval-basics.scm` and `mat-basics.scm` already did this the long way,
  via `have!` + `subst`; the `mac-h` route is one step and works in place.

  So every `definitional`-stamped constructor membership law in the tree is a candidate
  for PROOF instead of a stamp. NOT DONE for the existing ones: re-tiering moves every
  citing bill, so it is a separate measurement (triage by BILL).
* Until 2026-08-10 **DEFINITIONS.md carried no functoid at all**; all 113 were only in
  `FUNCTORS.md`. Looking up `zz-bezout-set` there found only its membership law, which
  reads exactly like a definition and is not one. `write-definitions-md` now emits an
  "Unfold-only constructors (functoids)" section from `*functoid-registry*`, filtered by
  `lookup-view-as` as FUNCTORS.md filters it, so the counts cannot drift (113 in both).

And a name-shape trap worth stating once: `zz-bezout` is a THEOREM; the thing defined is
`ZZ-BEZOUT-SET`. Searching the definition index for a theorem's name lands you on whatever
shares its prefix.

2. **A large database of theorems without proofs**, suitable as raw material for building new
   proofs. Statements, indexed and searchable; the PSS is the seed.

3. Revisiting the manual against all of it.

Do not treat "prove one more theorem" as the goal. The deliverable of a proof request is
usually the obstacles it exposes.

## Running it

    ./prover                  # interactive REPL
    ./prover file.scm         # load a proof script, exit
    ./prover -i file.scm      # load a script, then drop into the REPL
    ./VNB                     # launcher (cold boot re-proves the library: 24 s compiled)
    ./VNB-with-compile        # recompile sources, then launch

Full check suite (distinct from the launcher):

    timeout 900 mit-scheme --quiet --load test-suite.scm < /dev/null

It prints `=== SUMMARY: N passed, M failed ===`.

**RUN IT ALONE, and check for that line -- exit 0 does not mean it ran.** Note there is
no `--heap` here: the suite takes MIT's default heap, not the ~1 GB `./prover` asks for.
Started alongside a `./prover` process (2026-08-10) it died partway through the library
load, ran zero checks, printed no `SUMMARY`, no `;Aborting!`, nothing on stderr, and
**exited 0** -- indistinguishable from a clean run except that the log stops early and
always at the same place. A `./prover script.scm` sharing the box failed the same silent
way. Under contention it also gets much slower (>20 min against the usual ~6) before it
dies, so a suite that is dragging is already the warning.

**It is not only contention** (2026-08-18). The same silent death -- 786 lines, stopping
mid-library-load, no `SUMMARY`, no `;Aborting!`, nothing on stderr, exit 0 -- happened
with `pgrep -x mit-scheme` reporting ZERO other processes beforehand. The one difference
from the clean run was the launch: `nohup ... &` in the background rather than in the
foreground. Re-run in the FOREGROUND, alone, it was 905/0 in 5m14s. So the rule stands
and gets one clause: run it alone, in the FOREGROUND, and check for the SUMMARY line.

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

## This box

~3.8 GB RAM (resized 2026-07-08 from 1.9 GB), plus a 2 GB swapfile. One prover run
requests `--heap 120000`, about 1 GB. **Two concurrent provers fit; three do not.**

Never `pkill -f mit-scheme` from a shell command: the pattern matches the killing
command's own command line and takes down the shell (exit 144). A bracket class
(`pgrep -f "[m]it-scheme"`) only saves `pgrep` from matching *itself* -- if the surrounding
shell was launched as `... mit-scheme ...`, `-f` still matches it and you kill your own
shell. Match the executable, not the command line: **`pgrep -x mit-scheme`**.

## Case folding -- the trap that keeps biting

Both the VNB reader and MIT Scheme fold symbols to lowercase. `X` is `x`, `SP` is `sp`.
Three consequences, each of which has cost a debugging session:

1. **Never name a top-level `define` in a proof file like a tactic or a registered
   constant.** `(define BC ...)` rebinds the `bc` TACTIC to a term; the next
   `(bc 'thm)` dies with "The object (...) is not applicable". Real cases: `BC` in
   bordered-eq-border-proof.scm, `TT` in hahn-banach-full-proof.scm and
   nn-least-element.scm, `SP` in a Smith driver, `ID` in mat-equiv-proof.scm.
   Use the file's helper prefix (`ss-`, `bm-`, `cc-`, `hb-`, `me-`). Single/double
   capitals (`BC` `TT` `SP` `NI` `AI` `DI`) are the danger zone. `case-fold-audit` and
   `constant-binder-audit` both inspect WFF binders only, never Scheme defines --
   **`clobber-guard.scm` is the gate that does**: it snapshots every procedure binding
   after `minimize` loads and, after each later file, errors if any was rebound to a
   non-procedure, naming file and symbol. (It found `(define Tm ...)` in
   noetherian-maximal-proof.scm silently killing the `tm` surface helper.) Macros are
   invisible to it -- `environment-lookup` refuses a syntactic keyword, so `bc*` is
   never watched.

2. Structure accessors may inadvertently collide with obvious binder names, but a
   warning is issued (`constant-binder-audit`). `X` used to be a carrier accessor
   and is now `CARR` for algebraic structures, `PTS` for metric spaces (whose
   distance `D` is now `DIST`). Same story for `A`, and for `ID`, now `IDEN`.
   In general avoid single letters -- not a hard and fast rule.

3. Inner binders that would collide take a trailing underscore: `i_`, `j_`, `n_`, `r_`.
   The same fold makes **`bd-K` and `bd-k` ONE variable**, so a driver holding two
   eigenvariables apart by capitalisation holds one (found 2026-08-17 in
   ccint-bounded.scm: the merged bound overwrote the inherited one, and the finder for
   the inherited one's bounding universal then matched nothing, several steps later).
   `clobber-guard` cannot see this -- both bindings are non-procedures in the file's own
   frame -- so the rule is simply never to distinguish two names by case. They are now
   `bd-k` and `bd-merged`.

4. **A binder list scopes LEFT TO RIGHT, so a guard may mention only binders to its
   LEFT.** `forall([s in CARR(r), r], FUBA(s))` expands to
   `(FORALL s (IMPLIES (IN s (CARR r)) (FORALL r (FUBA s))))`: the guard's `r` is
   OUTSIDE the scope of the `forall r`, hence FREE, and the later binder binds a
   different variable of the same name. With a body that mentions `r` too, one formula
   carries two distinct variables both spelled `r`, and the printer round-trips it
   faithfully -- nothing on screen shows it. `validate-wff!` warned generically
   ("symbol r is both bound (in some binder) and free"); since 2026-08-15
   `warn-forward-guard-reference!` (wff.scm) fires at binding-list expansion -- so on
   TYPED input, not only on install -- and names both positions. It returns its findings
   (`binding-list-forward-refs`) as well as printing them. Warn-only: the form has a
   meaning, it is simply almost never the intended one. Nothing in the library trips it.

**`lambda` is gone; the binders are `vnb-lambda` and `lambdoid`** (2026-08-18, the user's
call). Surface `lambda([x in A], body)` built a functoid RECORD -- the set-domain sibling of
`lambdoid` -- and so was NOT `VNB-LAMBDA`, which builds a set of ordered pairs, an element
of `FUN(A,B)`. They carry different obligations and different rules: `vnb-lambda` is typed
by `lam-t` (which opens the `A in SET` leaf) and reduced by `lam-b`; a functoid has no
typing rule and reduces by `beta`. One unadorned word standing for the construct no library
proof uses, beside a hyphenated one standing for the construct every proof uses, is a
confusion with no upside. `parser.scm` now ERRORS on `lambda`, naming both replacements.

Three things were checked before removing it, and they are the reason it was safe:

* **Zero installed formulas contain a functoid record** (measured over `*theorem-table*`),
  and `functoid-beta` is in `kernel-rules-audit`'s "not exercised by this load" list. The
  whole functoid-record machinery is reachable only from a hand-typed `lambdoid`.
* **The `'lambda` functoid KIND was dead.** Every reader of `functoid-kind` either
  preserves it, compares two for equality, or prints it -- nothing branches on it, so the
  documented "domain must be a SET" was enforced nowhere. `make-functoid` now REFUSES
  `'lambda`: `expr->str` prints the kind verbatim, so such a record would have printed as
  `lambda(...)`, which no longer parses, and a round-trip that silently stops round-tripping
  is worse than an error.
* **`vnb-lambda` was never "waved through by the parser"**, which is what it looks like:
  `VNB-LAMBDA` appears nowhere in parser.scm, and `vnb-lambda(...)` reaches the generic
  application branch. The binder is built by `expand-destructuring-quantifiers`
  (wff.scm:306-338) -- the same desugarer that handles `forall([x in A], ...)` -- which
  collapses the single-binder case to the bare-symbol form, REJECTS a partly-typed binder
  list, and REJECTS the domainless form. Plus a dedicated `make-wff` branch and five suite
  checks. It is a design, not an accident.

Only two suite checks used the surface `lambda` (both converted to `lambdoid`); four new
checks pin the removal and the error text. Suite 909/0.

A related naming question is still OPEN and is the same species: `def-functoid` installs a
macete and nothing else, and `docs/functoids-and-functions.md` section 8 (adopted
2026-07-28) says its borrowing of the word "is what makes the manual's account of functoids
read as false". That rename has not been done.

## Vocabulary

BONGO refers to a bug, a "tournant dangereux", or an otherwise bad idea.
FUBA, GUBA, RUBA, BLAH etc are generic names.

RANDO MUBA and his sister RANDA MUBA are hypothetical VNB users, invoked when a
question is about the WORKFLOW rather than about the mathematics: "RANDO finishes a
proof and types `qed` -- then what?". Either party may raise them. The user uses them
to request a clarification; Claude uses them to give one. The answer they call for is
a concrete end-to-end walkthrough -- which command, on which surface, writing which
file, at which moment, and what it costs -- with the file and line the claim comes
from, not a description of the design intent. If the walkthrough cannot be given
without checking the code, check the code.

## Working with the user

Treats Claude as a colleague, and can be ill-tempered at times. Does
not appreciate Claude forgetting previously settled questions. Does
not appreciate gratuitous compliments. Avoid obvious narrative
statements such as: "Let me check BLAH before relying on memory". Just
say "Checking BLAH".

Register: The user's interaction with the assistant is on an informal
register, very much like the register coworkers would use to interact
in the course of a technical discussion. Use of metaphor, imagery,
analogies to current events etc. to animate the conversation and ease
the burden of finding a pedantic formulation of an idea. The assistant
is allowed to use the same register if the alternative is too
pedantic. However, in any form of documentation the register should be
formal and precise, even if pedantic.

**More interested in technique than in bulk.** One general mechanism that
dissolves a class of obligations beats N bespoke lemmas that discharge them one
at a time. When a proof needs a nasty step, ask first whether the step is an
instance of something the *machine* can do, and only then whether it is a lemma
the PSS should assert. A tactic is untrusted; a support is trusted surface.

## Writing proof drivers

Proof scripts navigate a deduction graph by moving focus between open leaves.

* **Never navigate by goal shape alone.** Sibling branches routinely share a goal head.
  `(forall k. IN k NN => IH => ...)` and a row conjunct `(forall i_. ... => ... => ...)`
  are both `FORALL/IMPLIES/IMPLIES`. Discriminate on the binder, or better, on a
  CONTEXT formula unique to the branch.
* **Never name an ASSUMPTION by shape either** -- same rule, one level down. An induction
  step's context holds the IH, the instantiated IH, and look-alike `SPANS`/`FORSOME`
  siblings; and a `mac-h`/`ai` fed a formula the driver RECONSTRUCTED (with its own guess
  at the eigenvariable names) matches nothing, silently no-ops, and every later command
  runs in the wrong branch. Use the `dk-` kit in `driver-kit.scm`: run the tactic, DIFF
  the assumption list, keep what appeared. `dk-landed` (errors if nothing landed --
  a silent no-op IS the bug), `dk-landed-1`, `dk-landed-find`, `dk-split!` (ai the landed
  conjunctions to exhaustion), `dk-opened` (leaves a branching tactic opened).
  **`fact` and `inst+` land their whole instantiation chain**, not one formula -- the
  theorem, each partly-peeled form, and the detached result -- so use `dk-fact!` /
  `dk-deepest`, which take the landing no other landing contains.
* **Never rely on where `ass` or `cut` leave focus.** `cut` opens a side goal plus the
  main branch; the `ass` that closes the side goal hands focus to an engine-chosen leaf.
  Re-focus explicitly afterwards.
* A focus helper that returns `#f` and leaves focus put on a miss will hide all of the
  above for weeks. Make it **error**.
* `fact` peels leading universals and auto-detaches each antecedent already in context;
  it will NOT split a conjunctive antecedent (use backward `bc*` for those). If a `fact`
  seems inert, dump the context and look for the one missing typing hypothesis.
  `ord-le-total`, `ord-le-antisymm`, `ord-le-trans` and `ord-succ-immediate` all have
  AND antecedents, so each wants a `(have! '(AND ...))` immediately before the `fact`.
  Without it the citation lands the *implication*, silently, and a following `use-cases`
  cuts the disjunction it was supposed to find in context -- leaving an exhaustiveness
  obligation open branches away.
* **`di` is greedy.** One call takes the whole leading FORALL/IMPLIES prefix, and the
  next call will take a `NOT` (assuming it, goal `FALSITY`) or SPLIT an `AND` goal into
  two leaves. Counting `di`s is therefore not a way to land on a chosen goal -- write a
  peel-until-the-head-changes helper and guard it on progress (`zb-peel!` in
  zz-bezout-proof.scm, `z2-peel!` in zorn-route-two.scm).
  **Greediness costs you INDUCTION, and there is no undo.** `ni`
  (`pi-nn-induction!`) tests the goal's SHAPE -- literally `(FORALL n (IMPLIES (IN n NN)
  body))` at the top -- so it also misses `forall([a, n in nn, ...], ...)`, where the
  mathematics is the same and only the binder ORDER differs. State an induction variable
  FIRST. If the `di` already happened, the induction is still recoverable without a
  restart: `cut` the generalization with the NN variable outermost, `ni` that, and close
  the leaf from it by instantiation. `what-now`'s **induction lane** (suggest.scm,
  2026-08-15) reports both cases and prints the `(cut "...")` built from the goal and the
  CONTEXT's typings; it stays silent when `ni` already fires, since the live-fire lane has
  that. It quantifies only eigenvariables that carry a typing assumption -- an untyped one
  (from an unrestricted `forall([a], ...)`) stays free, which is sound because it is fixed.
  Four suite checks, including that the emitted cut parses with the variable outermost.
* **A GUARDED universal goes whole under one `di`; an UNGUARDED one does not.**
  `(FORALL t (IMPLIES (IN t S) body))` -- what the surface writes `forall([t in S], ...)`
  -- lands `(IN t S)` in a single call. `(FORALL y (IMPLIES (AND ...) ...))`, the shape a
  hand-built hypothesis takes when its antecedent is a conjunction rather than a typing,
  peels the QUANTIFIER and lands NOTHING; the antecedent comes on the next call. A
  `dk-landed-1` around one `di` therefore errors on the second shape and succeeds on the
  first, which is indistinguishable from a driver bug until you print the goal. Loop on
  the LANDING, not on a `di` count: `bd-di-landed!` (ccint-bounded.scm) calls
  `dk-landed*` until something lands and errors if nothing ever does.
* `ai` on a `NOT` assumption is NOT-ELIM, not "reduce the goal to the positive": it fires
  only when the positive is ALREADY in context. Every contradiction is therefore
  `have!` the positive, then `ai` the negation -- never an `ai` you expect to leave the
  positive as your new goal.
* **`obtain` cannot skolemize an existential that is ALREADY in the context**, and it
  does not say so. It diffs the context around its own LANE (sketch.scm), so a `FORSOME`
  that `di` landed a moment earlier is invisible to it -- `(obtain (lambda () #t))`
  reports "no existential landed". Write the three-line local skolemizer instead:
  `ai` the formula, `dk-split!` whatever lands, and read the eigenvariable off by
  free-variable set difference (`bd-skolem!` in ccint-bounded.scm, `ev-skolem!` in
  evt-proof.scm). Worse, `obtain` runs its lane under `vnb-guard`, so an ERROR raised
  inside the lane -- a finder that matched nothing, say -- is swallowed and reported as
  "nothing obtained": the `quietly`-hides-errors trap, one level in.
* **Discriminate a hypothesis on its CONSEQUENT, not on a symbol it contains.** A finder
  reading "the FORALL that mentions `IS-CONTINUOUS-AT`" picks
  `continuous-bounded-above-on-ccint` once that theorem has been cited, because the
  continuity universal is its own ANTECEDENT and `fact` lands the whole instantiation
  chain nearer the top of the context than the hypothesis sits. The instantiation then
  goes to the wrong theorem, at the wrong argument, and lands something unusable rather
  than nothing. Both EVT drivers now test `(car (caddr body))`.
* **A GUARDED macete: `mac` refuses, `mac-h` spawns.** `rr-ms-dist` is
  `forall u,v in RR. (DIST RR-MS)(u,v) == abs(u-v)`. On an ASSUMPTION, `mac-h` applies it
  and posts the typing as a side-condition subgoal ("1 side-condition(s) spawned"). On a
  GOAL whose arguments are not already typed in context, `mac` does not apply it at all --
  it warns `apply-macete: macete not applicable` and leaves the goal untouched, and the
  driver sails on rewriting a formula that never changed. So type the arguments BEFORE the
  `mac`. (Corollary for the operator, not the tree: `;VNB warning:` lines carry this
  information and are easy to filter out of a log grep. Grep for them.)
* **`lam-t` opens TWO leaves, not one:** the pointwise typing of the body, and the
  SETHOOD of the domain. A `VNB-LAMBDA` is a set of pairs, so `(IN RR SET)` has to be
  discharged (`rr-is-set`) before the lambda is a function at all. A driver that expects
  one leaf leaves the other open and finds out at `qed`.
* `dk-split!` begins by `ai`-ing the formula you hand it, so handing it an ATOM is an
  error (`dk-landed: the tactic landed no assumption`), not a no-op. It is for
  conjunctions only; for a single landed atom keep `dk-landed-1`.
* `detach!` takes the **IMPLIES** formula, not its antecedent. `(detach! <antecedent>)`
  is a silent no-op.
* **`lam-b` needs the argument TYPED, and needs it BEFORE the reduction.** A lambda
  carries its domain and is defined only there, so `((VNB-LAMBDA x A b) u)` reduces
  cleanly only when `(IN u A)` is evident -- in the context, or supplied by an
  enclosing guarded universal or by an enclosing `VNB-LAMBDA`/`SEP`/`BIG-UNION`
  binder (the walker threads all three). Otherwise the step still fires but **owes
  `(IN u A)` as an extra leaf**, and a driver that was not expecting it wanders.
  **And the owed leaf can be UNPROVABLE, not merely extra** (2026-08-17, the SQRT work).
  `pi-lambda-beta!` (primitive-inferences.scm:1404) licenses a redex against
  `(append scope asms)` -- it threads the enclosing binders -- but posts the obligation as
  `(make-sequent asms ...)`, the OUTER context alone. So a `lam-b` fired on a goal that is
  still `forall y in PTS(RR-MS). ... ((VNB-LAMBDA z RR ...) y) ...`, where the walker
  cannot see `PTS(RR-MS)` as `RR`, owes `(IN y RR)` at a node whose context predates `y`
  entirely: `y` is FREE there and nothing constrains it. That leaf cannot be closed by any
  later step, and nothing says so until `qed`. PEEL AND TYPE FIRST, THEN BETA.
  The fix is always the same and always one line: land the typing fact *above* the
  `lam-b`, not below it. `mat-ring-proof`'s `mr-close-conj` is the worked example
  (type -> `lam-b` -> cite -> `ass`), and it is why `mr-rops` no longer betas: at the
  point it used to, the binders whose typings were needed did not exist yet.
* `mac-h` **replaces** the assumption it unfolds. Unfolding `(IS-IDEAL s I)` to reach its
  closure conjuncts therefore deletes the hypothesis that `ideal-elt-in-carrier` (and
  every other `fact` guarded on `IS-IDEAL`) needs. Get the projection another way, or
  unfold last.
* `minimize!` lands `GUARD[v:=w]` as **one conjunction**, not as its conjuncts. `ai` it
  before detaching anything against it.
* **A multi-variable substitution is NOT single substitution iterated.** `subst-free*`
  (expressions.scm) is the only multi-binding substitution in the tree; a fold of
  `subst-free` exposes whatever each binding substitutes IN to every later binding.
  That fold WAS `apply-subst` (the macete rewriter) until 2026-07-11: unfolding `SPANS`
  -- parameters `(md n u sm)` -- at `SPANS(md,k,w, INTERSECTION(sm, SPAN(md,n,BLOCK(u,n,1))))`
  let the pending `n:=k`, `u:=w` bindings rewrite the caller's own `n` and `u` INSIDE the
  term matched to `sm`. No error, no warning: a different theorem. It is the case-fold
  disease (a name collision) one level down, and it bites precisely when a recursive
  construction is fed back into its own definition. Iterating `subst-free` is legitimate
  ONLY when peeling nested quantifiers one binder at a time (`cmd-fact`, `mz--type-at!`),
  where the remaining variables are still BOUND.
* **`subst` cannot rewrite a term in OPERATOR position.** Its Leibniz walk reaches
  argument positions only, so `(subst '(= (VADD md) (MUL (MODULE-VECTOR-AG md))))` is a
  silent no-op on the goal `((VADD md) x y)` -- whose head *is* the term you meant to
  replace. Structure accessors (`VADD`, `MUL`, `ADD`, `ACT`) are almost always in operator
  position. Use the equation as a **macete**: `mac` on the goal, `mac-h` on an assumption.
  Any unconditional equation (e.g. `mvag-op`) is one.
* A macete rewrites **every** occurrence. If `fact` lands `SUM(λz. (MUL ag) …) = (MUL ag) …`
  and you `mac-h` it, the operator changes in the summand lambda *and* at the top, while
  the goal's copy of that same summand does not. Normalize **both sides** with the same
  macete (`mac` the goal, `mac-h` the assumption), or `ass` silently fails to match.
* **`cut` of a formula already in context (up to ALPHA) is a silent self-loop.**
  `dg-post!` hash-conses sequent nodes by alpha-equivalence of the assertion plus
  equality of the context, and `context-add-assumption` is alpha-idempotent -- so the
  "main" child of the cut *is* the focus node. One leaf opens instead of two, the graph
  gains a cycle, and the failure surfaces branches later as a missing leaf. Guard with
  `alpha-equiv?` before cutting anything you did not just construct fresh. (This is what
  `minimize!` does; see `mz--cut!` in minimize.scm.)
* **`use-em` on a proposition the context already DECIDES is not a case split**, and
  since 2026-08-15 it ERRORS rather than doing it. If `P` is an assumption, the P-branch
  is hash-consed straight back onto the node it was split from (`context-add-assumption`
  is alpha-idempotent, sequents.scm:51) and the NOT-P branch has a contradictory context;
  the caller sees one new leaf that reads like a real obligation, is closable only by
  NOT-elim, and -- there being no undo in the tree -- cannot be taken back. The same holds
  mirrored when `NOT P` is the assumption. On a disjunctive goal whose disjunct is already
  in context the move is `(oi-l)` / `(oi-r)` then `(ass)`, and the error says so.
  `what-now`'s disjunction lane proposed the split unconditionally from the day it was
  written (2026-08-14) until the same date; it now checks both disjuncts against the
  context (`what-now--disjunct-in-context`, suggest.scm) and names the two-move close
  instead. Suite checks: five, beside the driver-kit containment block.
* **A PROBE MUST BIND `*replaying?*`, not just `*ps*`.** `what-now` / `scout` probe by
  running the REAL interactive tactic on a scratch state (`vnb-apply?` evals it by name),
  and every interactive tactic goes through `vnb--run!`, which calls `record-cmd!` and
  `vnb--capture-step!`. Those write to the GLOBAL `*proof-script*` and `*live-trace*` --
  which a `fluid-let` of `*ps*` does not protect. Until 2026-08-15 every FIRING probe
  therefore appended a step nobody took: to the script the emitter writes out and to the
  trace `proof-tex` prints from. Measured: one probed `(oi-l)` = +1 to each; a whole
  `what-now` = one per firing candidate. `*replaying?*` is the existing switch for exactly
  this (interactive.scm:25) and `vnb--scout-replay` already bound it; the what-now probes
  did not. All three now go through `vnb--probing` (suggest.scm), which binds `*ps*`,
  `*replaying?*` and `quietly` together. Library proofs were never affected -- they run
  from files and never call the copilot -- so this was an interactive-session defect only.
  Suite: two counter checks, plus `scratchpad/probe-pollution-demo.scm`, which fires the
  same tactic through the old and new wrappers and prints both deltas.
* `quietly` silences `vnb-guard` as well as `show`, so a tactic that *errors* inside it
  becomes a silent no-op and every later command runs in the wrong branch. A composite
  tactic wants `show` quiet and the guard loud (`mz--quietly`), plus a per-step
  "did this rule fire?" check -- every primitive inference gives its focus node an
  in-arrow, so `(null? (sequent-node-in-arrows n))` afterwards means it did not.
* **A command that changes nothing now SAYS so, and is not recorded** (2026-08-24).
  `vnb--run!` (interactive.scm) had three outcomes -- error, soft warning, success -- and
  a fourth hiding inside the third: a tactic that raised nothing, declined nothing, and
  returned the state it was handed fell to the success branch, was appended to
  `*proof-script*` and to the `*live-trace*` `proof-tex` prints from, and `show`ed the
  unchanged goal as though it had landed. The boundary now tests for it and prints
  `;VNB warning: <cmd>: nothing changed -- no rule fired and the focus did not move.
  The step was NOT recorded.`
  **What discriminates a real move is the deduction GRAPH plus the focus NODE** --
  a node posted, an inference recorded, an arrow written, something grounded; or else
  the focus moved. Not the goal formula (a `mac-h` lands a hypothesis and leaves the goal
  alone; a branching tactic can leave it alone too), not the assumption list (mirror
  image), not the open-leaf count (`ass` closes one and hands focus to another; a
  one-premise rule leaves the count put). And a pure focus move -- `focus`, `focus-id`,
  `dk-focus!` -- writes nothing into the graph and is nonetheless a real step, which is
  why the focus half is there.
  This is STRONGER than the in-arrow test this file names two bullets up
  (`(null? (sequent-node-in-arrows n))`): that one is right about one primitive on the
  focus node and wrong about everything else -- it calls a hypothesis-side rewrite inert
  (the rule fired on a node the focus is not) and calls a re-visited node a firing (the
  in-arrow was already there). Keep the in-arrow test for a per-step "did THIS rule fire"
  check inside a composite; the boundary uses the graph.
  **One surface tactic BYPASSES the boundary and had to be wired by hand**, and it is the
  one that found the only real instance in the tree. `to-binary` / `to-nary` drive `mac`
  in a saturation loop inside `quietly`, so the inner `mac` warnings are swallowed: a
  saturation with nothing to saturate was completely silent -- no warning, nothing
  recorded, an unchanged goal redisplayed. They now take the same mark and report through
  the same notice, and on the first run that reported **32 declines per library load, all
  of them from `in-rr`**, which opens with an unconditional `(to-binary)` as a speculative
  "push the arithmetic onto the structure surface first" step that most typing goals have
  no arithmetic for. That call is now `quietly`, which is what a speculative pre-step
  inside a composite should always have been: the notice is a soft warning, so `quietly`
  suppresses it exactly as it suppresses every other.
  **After that fix: zero inert notices over the whole library load**, so no script, no
  `*live-trace*` and no `qed` bill moved. `*vnb-inert-count*` is the tally and
  `*vnb-inert-at-load*` is it frozen at the end of load.scm -- the suite asserts THAT one,
  since the live counter goes on rising through the suite's own deliberate no-ops. It
  counts notices ISSUED, not inert calls detected, so it equals
  `grep -c "nothing changed"` over the log: a speculative pre-step that declines under
  `quietly` is not a dead step anyone took, and counting it would make the tally disagree
  with what the log shows. This is the SILENCE half, and it is not optional -- a notice
  that fires on every command is as useless as none.
  Note what the notice does NOT catch, because those cases are already loud: the dozen
  silent no-ops this file lists are all soft WARNINGS at the `cmd-*` layer (`subst` in
  operator position returns #f from `pi-eq-subst!`, `mac-h` on a functoid name warns
  `unknown theorem/macete`, `detach!` on an antecedent warns). The tree had been guarding
  its known no-ops one tactic at a time -- `cmd-mac-h*` returns a warning rather than
  `ps0` "so the surface wrapper records no no-op", in its own words. What the boundary
  closes is the residual FOURTH outcome, which nothing else was watching and which every
  tactic written from here on gets for free.
* **`backup-one` (alias `undo`) is the undo, and a STATE STACK is not what it is.**
  There is exactly one `<proof-state>` object per proof: `start-proof` (proof-commands.scm)
  is its only constructor, every `cmd-*` mutates it through `set-proof-state-focus!` and
  returns THAT SAME OBJECT, and `vnb--run!`'s `(set! *ps* result)` therefore assigns `*ps*`
  the value it already had. Pushing the old `*ps*` on a stack pushes the object about to be
  mutated and restores nothing. (interactive.scm's own `to-binary--saturate` comment had
  half of this: "`(eq? *ps* ...)` never changes because tactics mutate `*ps*` in place --
  repeat/orelse rely on that identity and so silently run once, a separate latent bug".)
  The state lives in the deduction graph, so the rollback is there. `deduction-graphs.scm`
  now journals the only four writes there are -- `dg-add-sequent-node!`,
  `dg-add-inference-node!`, `dg-apply-rule!` (arrows), `dg-propagate-grounding!` -- and
  `dg-rollback!` undoes the journalled per-node writes newest-first, then restores the two
  node lists and the node counter. **That is what settles the orphan-leaf question**: the
  nodes posted since the mark are DROPPED from the graph, not orphaned, so
  `proof-open-leaves` cannot count a node from an abandoned branch and `qed` cannot be
  handed a phantom obligation. Checked both ways in the suite: after backing up over a
  branching `di` the leaf count is the pre-branch count, and a proof finished after two
  backups still `qed`s `modulo 0`.
  Cost: an A/B over a full library load, same binary, machinery off vs on, was
  1m52.868s vs 1m52.518s -- nothing. The mark holds the inference list (cons-built, a
  shared tail) and the node COUNTER rather than the node list (`append`-built, so a held
  pointer would pin a whole copy); `list-head` rebuilds the prefix at rollback time.
  Two things it does NOT do. It does not restore `*fresh-counter*`, so backing up over an
  `ai`/`ew` that minted `u_4` and re-running it mints `u_5`. And it is gated on
  `*replaying?*`: no mark is taken during a replay or a copilot probe, since a probe runs
  the real tactic on a SCRATCH proof state and a mark naming that state on the live stack
  would make the next `backup-one` set `*ps*` to it. The composites that record THEMSELVES
  rather than their expansion -- `prop`, `minimize!`, `bc*`, `dk-focus!` -- take their own
  mark outside their `fluid-let`, so one script entry is one undo.
* Debugging recipe that works: `head -N` the proof file into scratchpad, append a dump of
  `(proof-leaves)` with each leaf's goal head and a distinguishing context formula, run it.

## Where a driver helper lives

**Every proof-driving Scheme procedure is either in `driver-kit.scm` -- loaded before any
proof -- or is local to the file that defines it.** There is no third place.

`load.scm` enforces the second half: once `driver-kit` has loaded, each `theorem-library/`
and `calculus/` file is loaded into a fresh `extend-top-level-environment`. A driver's
top-level `define`s stay in its own frame; its `set!` of `*ps*` still reaches the real
binding, and it still sees every tactic, every macro (`bc*`) and everything `driver-kit`
defines. So a stray `(define BC '(succ p))` now breaks only its own file.

Before this, both halves were false and nobody had said so: `proof-leaves` and `any-pred`
were defined *only* inside `theorem-library/nn-least-element.scm` -- a proof script -- and
used by `interactive.scm`, `macetes.scm` and eighteen drivers; `deriv-constant-proof.scm`
exported a thirteen-procedure `dc-` kit to nine drivers, under a comment calling it
"file-local". It worked only because Scheme resolves free variables at call time.

If exactly one file needs a helper, define it there with the file's prefix. If two do, it
belongs in `driver-kit.scm`.

## Layout

    structure-library/   definitions, structures, vocabulary, warranted supports
    theorem-library/     proofs that reach (qed ...); loaded, gated, counted
    calculus/            probes and stress tests; MOSTLY not in load.scm -- but
                         `calculus/finite-ball-subcover-proof` IS loaded (load.scm:787),
                         and load.scm's per-file environment containment covers
                         `calculus/` exactly because such files can be loaded
    reference/           GENERATED (PSS.md, THEOREMS.md, GLOSSARY.md, ...) -- never hand-edit
    scratchpad/          throwaway drivers (untracked)

Also on disk, not described above: `prove-scripts/`, `stress-tests/`, `examples/`,
`structure-notes/`, `archive/`, `printouts/`, `emacs/`, `docs/`, and a SECOND
scratch directory `scratch/` alongside `scratchpad/` (both in use; no rule
distinguishes them).

**Load order matters.** A file using `sp`/`qed`/`make-wff` must come after `interactive`
and `proof-debt` in `load.scm`. Misplacing it gives "Unbound variable: make-wff".

## Library-build policy

New mathematical facts are added as **warranted supports** (`support` + `warrant!`),
not as kernel axioms. A `qed` prints its bill: `proven modulo {...} [trust: ...]`, the
set of asserted facts it leans on.

**The primitive shelf CAN grow, but only by an explicit foundational decision.**
`primitive` provenance (proof-debt.scm:12) is trusted base: it contributes {} to every
bill, exactly like the ~92 axioms of `make-vnb-base-theory`, which theory.scm:613 installs
inside `(fluid-let ((*current-provenance* 'primitive)) ...)`. This brief used to say the
~92 never grow. They grew, once, on 2026-07-27: the **28 ordinal axioms** of
structure-library/ordinals.scm (burali-forti, ord-le-*, ord-succ-*, limit-ord-iff,
ord-segment-*, sup-ord-*, transfinite-induction) are now wrapped the same way, by the
user's decision that the ordinals are foundational rather than owed an argument. They had
been billing as `asserted` only because `theory-add-axiom!` defaults to that
(macetes.scm:1405) and nobody had written the fluid-let. Note the distinction that makes
this NOT a loophole: a `warrant!` moves a fact from `none` to `well-known` -- a better tier
of DEBT; `primitive` says it is not debt at all. Use it only where a mathematician would
answer "because that is what ordinals are", and say so in the file.

They grew a second time on 2026-07-28, and this one is INSIDE
`make-vnb-base-theory`, so the count itself moved: **92 -> 93**. The new axiom is
`app-graph` (theory.scm, at the head of the function-space block):

    forall f, x.   (f x)  ==  IOTA y. (LIST x y) in f

"A functoid is a class; a function is a functoid that is a set." It DEFINES
application as the description over the graph, unguarded -- guarding it on `IS-FUN`
would restrict it to set-functions, which is the restriction it exists to remove.
Safe unguarded because `f` is a VARIABLE and an axiom is instantiated only at TERMS:
`UNION`, `POWER`, `FUN`, `CHOICE`, the accessors and every `def-functoid` head are
constant heads, and `CARR` alone is not a term. Operators are syntax, not objects.
The argument is `docs/functoids-and-functions.md`.

It is **named-only** and has to be: its left-hand side is a bare application with both
sides schema variables, so as a live macete it would rewrite every application in every
goal into an `IOTA`. `declare-named-only!` (macetes.scm) is the new facility that says
so -- distinct from S-10, which catches a rewrite that is UNSOUND; this catches one that
is sound and ruinous to fire automatically. It suppresses the `-rev` companion too.
Adding it moved nothing else: 219 proven, every bill unchanged, every gate still ok.

The shelf grew a THIRD time on 2026-07-28: **`image-set`** (replacement,
structure-library/injection.scm) is now wrapped `primitive` too, by the user's decision
that the image of a set under a class function being a set is what sets ARE. It was the
SOLE entry in the bills of `ord-no-injection-into-set` and, through it, **Zorn's lemma** --
both now read `modulo 0`. Catalog moved 94 -> 95 axioms and 263 -> 262 assertions, i.e. one
fact crossed columns and nothing else did.

The shelf grew a FOURTH time on 2026-08-01, and this one is much the largest: the
user's rebuild of the **arithmetic base**. `number-systems.scm` joined
`*primitive-files*` in load.scm -- the list `prover-load` wraps in
`(fluid-let ((*current-provenance* 'primitive)) (load path))`, alongside
`theorem-library/axioms` -- so its ~107 axioms (Peano closure, the ZZ/QQ/RR/CC field
and order axioms, abs) stopped billing as debt. They had been `asserted` with no
`warrant!` at all, which is exactly `trust: none`, so every arithmetic proof in the
library was billing the axioms of arithmetic as unjustified assumptions. Measured
across all 238 bills, before vs after: **81 shrank, 0 grew, 45 changed trust tier,
5 cleared to `modulo 0`**; `trust: none` bills went 96 -> 51, `modulo 0` 62 -> 67, and
the catalog columns moved 95 -> 212 axioms / 273 -> 156 assertions.

The same cleanup ADDED the axioms that say what each system IS, since the ring/field
axioms alone pinned down none of them (QQ is a model of ZZ; RR was any ordered field):
`zz-generated-by-nn` (moved in from zz-arith.scm), `qq-is-fraction`,
`rr-sup-in`/`rr-sup-upper`/`rr-sup-least` (order completeness, with `SUP` and the
predicates `RR-UPPER-BOUND` / `RR-BOUNDED-ABOVE`), and for CC `cc-i-in`,
`cc-i-squared`, `cc-generated-by-rr`, `cc-conjugate-fixes-rr`, `cc-conjugate-i`.
`qq-dense-in-rr` is the one that is NOT in the base: it needs `<` and `POS-RR`, which
do not exist until order-predicates.scm, so it lives there and stays `asserted` --
honest, since density is a theorem of the base rather than part of it.

A LATER FINDING of the same cleanup, 2026-08-01: **binary minus had no axiom at all.**
Every minus axiom was UNARY (`rr-neg-closed`, `rr-neg-inverse`, ...), while the parser
emits binary `(- x y)` for "x - y"; nothing said `u - v` was a difference. The only
statement about that head was `rr-sub-in-rr`, a `well-known` support that read like a
restatement of `rr-add-closed`. It mattered because **`ineq` -- a TRUSTED oracle --
"linearizes over + - *"**, so it was reading a meaning the theory declined to state.
number-systems.scm now carries `binary-minus-def` (`(- a b) == a + (- b)`), stamped
`definitional` and `declare-named-only!` -- as a live macete its left side matches every
difference in the library. `rr-sub-in-rr` is now PROVEN `modulo 0` in
theorem-library/binary-minus-laws.scm, and that alone shrank **ten** bills (the whole
differentiation/MVT/Taylor arc), because every one of them differences two reals.
The same question was open for `/` and is now CLOSED the same way (verified
2026-08-04): number-systems.scm:107 carries `binary-divide-def`,
`(/ a b) == a * recip(b)`, stamped `definitional` and `declare-named-only!`
(its left side matches every quotient in the library, so firing it live would
rewrite all arithmetic into recip form). The 14 quoted supports that carry a
literal `/` head -- `bdd-fn-*`, the `product-metric` weights, `young-inequality`,
`holder-finite`, `amgm-2-sqrt`, `sqrt-rpow` -- are therefore about the real
quotient now, not an uninterpreted binary operator. Writing `recip` directly is
still the better habit in new statements.

Two consequences worth keeping in view. **The archimedean property is now derivable**
(`nn-unbounded-in-rr` in order-predicates.scm was re-tiered `well-known` -> `informal`
on that basis, and `rr-le-all-pos-nonpos` / `rr-pos-halvable` / `rr-pos-shrink` are in
the same position but were deliberately left alone -- re-tiering moves every citing
bill). And **numeric literals are now exact rationals**: parser.scm's `p--exact-num`
reads every literal with the `#e` prefix, so `0.1` is `1/10` -- NOT
`(inexact->exact .1)`, the dyadic value of the double. arith-eval.scm's sound-arith
gate stays; its remaining job is rejecting inexactness arithmetic PRODUCED
(exp/sin/cos/magnitude), which is a different thing from a literal that was read.

The `card-*` axioms (cardinality.scm) were listed here as "still asserted, awaiting the
same call". That is STALE, and the truth is worse than either state: **the shelf is
SPLIT** (measured 2026-08-04). `primitive` -- so contributing {} to every bill --
are `card-empty`, `card-finite-bij`, `card-image-injection`, `card-in-ord`,
`card-insert`, `card-segment`, `card-union-disjoint`. Still `asserted/well-known`
are `card-singleton`, `card-subset-nn`, `card-power-nn`, `interval-card`,
`interval-card-in-nn`. So `card-insert` (add an element, the cardinal goes up) is
trusted base while `card-singleton` (a one-element set has cardinal 1) is debt.
No decision produced that split; it is the residue of two sessions.

It matters more than the tidiness suggests, and the reason is in cardinality.scm's
own header: **CARD is AXIOMATISED, not defined.** The intended meaning -- the least
ordinal in bijection with X -- is stated there in prose and declined in the code. So
`primitive` here does not say "this is what cardinality IS" the way it does for the
ordinals; it says "we are assuming the theory of cardinals", and no bill records it.
Either define CARD (the L1/L2 route in the Zermelo ladder makes that possible) or
demote the seven back to `asserted` + `warrant!` so the assumption is visible.

**One obstacle to defining CARD is now gone (2026-08-12): `interval-card-in-nn` is
GUARDED.** It read `forall a, b. CARD(INTERVAL(a,b)) in NN`, which a defined CARD makes
FALSE -- INTERVAL(1, b) for a non-natural b is all of NN, whose cardinal is omega -- so
the unguarded form blocked the definition outright. It now carries `(IN b NN)` on the
UPPER bound alone (matrix.scm), and the guard is not free: 34 `fact` citations across 13
proof files. 7 already had the typing from their own premises; 26 now land it with
`mat-rows-in-nn` (theorem-library/mat-basics.scm -- `IN Q (MAT m n X) => IN m NN`, which
is why that file exists) off a matrix already in context, and border-mult's `[1, succ q]`
citation lands it with `nn-succ-closed`. The matrix statements type no dimension
(matmul-assoc quantifies `m n k l` with premises only `IN P (MAT m n (CARR A))`), so the
typing has to come off the MATRIX; where the dimension is a data matrix's COLUMN count
the square elementary/unit matrix typed one line earlier (ELEM-F/G/H, MATUNIT: n-by-n)
supplies it, which is how the sites are reached without the column read-off mat-basics
deliberately declines to prove. Library after: 307 proven, every bill byte-identical,
suite 799/0. The failure mode here is LOUD, and that was checked rather than assumed:
delete the two `mat-rows-in-nn` lines from matmul-assoc-proof.scm and the load reports
`qed: proof is not complete; cannot install matmul-assoc` plus its cascade.

**`trust: none` is the WEAKEST tier.** `*pd-trust-order*` (proof-debt.scm) is
`(none hand-wave well-known reference informal proof)`, worst to best, and
`debt-trust-level` reports the worst leaf. It is literally
`(cons 'none *warrant-kinds*)`, so the ranking cannot drift from macetes.scm.
Note that `informal` OUTRANKS `reference` and `well-known`: `informal` means a
rigorous paper-proof exists (just not mechanized), which beats both a citation
nobody has checked and a textbook fact asserted with no argument at all.
`none` means *some leaf has no `warrant!`
at all* -- "scarier than a hand-wave: nothing was even claimed to justify it", as the
code says. The unconditional case prints `modulo 0` and no tier at all; **that** is
the strongest thing a `qed` can say. This brief claimed the reverse until 2026-07-10,
and the misreading is loose in old commit messages ("PROVEN to QED (trust:none)");
proof-debt.scm and the ledger's design notes always had it right. (The brief also
had `informal` and `well-known` swapped until 2026-07-23 -- the same swap that was
fixed in proof-debt.scm on 2026-07-10 and never propagated here.)

**The shape projections.** A structure declaration generates an IS-X IFF; each
operation-property conjunct of it, unfolded, IS one of the structure's laws. Stating
those laws separately as `theory-add-axiom!` and never warranting them is what used to
drag every algebra proof to `trust: none` -- the weakest report there is, for facts that
are literally part of the definition. Three different resolutions are now in the tree,
and the difference between them matters:

* module.scm wraps its projections in `(fluid-let ((*current-provenance* 'definitional))
  ...)` (module.scm:64) and pays nothing.
* ring.scm does the same thing by a different door: a `register-provenance! ...
  'definitional` sweep over the eleven names (ring.scm:139, with the reasoning in the
  comment above it). This brief said until 2026-08-10 that ring.scm "contains no
  provenance wrap at all" -- that check looked for `fluid-let` and missed the sweep.
* group.scm's four (`group-assoc`, `group-left-id`, `group-left-inv`,
  `group-identity-in`) are, since 2026-08-10, **PROVEN** `modulo 0` in
  structure-library/subtype-laws.scm (`stl--project!`), beside `abelian-group-opr-comm`,
  which was already done that way. Same work as a provenance stamp and it says more: the
  unfold is CHECKED, not asserted to exist. `ag-cancel-right` -- whose entire bill was
  those three, and which is the deck's worked example of a proof that still owes
  something -- now reports `modulo 0`.

`abelian-group-idempotent-is-id` was the fourth case and the different one: not a
projection but a genuinely DERIVED fact, and with 14 dependents the most-cited
unwarranted leaf in the library. It is **PROVEN** `modulo 0` (2026-08-10) in
theorem-library/cancellation.scm beside `group-cancel-left`, whose shape it borrows --
`a*a = a` and `a*e = a` give `a*a = a*e`, cancel `a` on the left. It became reachable the
same day *because* of the projections above: it needs the right identity (not a group
axiom -- group.scm states only left-id -- but one commutation away in an abelian group)
and `IDEN(s)` in the carrier, i.e. `group-identity-in`.

Measured after all five (2026-08-10): **293 proven, 105 `modulo 0`, 32 `trust: none`**
(was 288 / 97 / 54). Note `\Ntrustnone` is a TALLY, not a grep: PROOF-DEBT.md's own legend
contains the string `trust: none`, so `grep -c` reports one more than the truth.

**The `nary-*` bridge, and what "the weakest leaf" costs you.** `nary-plus-2`,
`nary-times-2` and `nary-neg-1` (numeric-instances.scm) are the CONVERSE, written out, of
`binplus-apply` / `bintimes-apply` / `binneg-apply`, which sit forty lines above them in
the same file stamped `definitional` as the defining equations of the bridge symbols; the
file's own comment says so ("Arity 2 is just binplus-apply / bintimes-apply reversed").
`==` is quasi-equality, hence symmetric, so the converse of a conservative definition
introduces nothing. On the user's call (2026-08-10) all three are now wrapped
`definitional` -- individually, since they are not contiguous, and as a WRAP rather than a
later `register-provenance!` so that `install-theorem!` stamps the auto-generated `-rev`
companion too.

**Stamping those three moved 27 leaf citations and ZERO bills.** The tier of a bill is its
WORST leaf, and every proof citing those three also cites `nary-minus-2`, which was left
`asserted` in the first pass. `trust: none` stayed at 32. `nary-minus-2` was then stamped
too, on a SEPARATE decision because the argument is a different one -- it is not a converse
but a COMPOSITION: `(- x y) == x + (- y)` is `binary-minus-def` (number-systems.scm), and
the two converses rewrite the right-hand side to `binplus x (binneg y)`. `==` is a
congruence, so the chain substitutes, and every step is definitional. That single stamp
took `trust: none` **32 -> 19** and left `modulo 0` at 105 -- so `nary-minus-2` was never
any bill's ONLY leaf, it was merely the worst one in thirteen of them.

The lesson outlives the arithmetic: **reclassifying or proving a leaf buys nothing until it
is the LAST unwarranted leaf of the bills that name it.** Triage by BILL, not by citation
count -- `debt-keystones` ranks by citations and misled exactly here, putting `nary-neg-1`
(14 dependents) at the top of the list when it was worth nothing on its own. The
measurement to run first is the what-if: drop a candidate leaf from every bill and recount
the tiers (`scratchpad/nary-what-if.scm`). It has been right every time.

It happened TWICE in one day. `integral-domain-cancel-zero` was then PROVEN
(below) -- and `trust: none` again did not move, because all seven of its bills also cited
`zz-is-integral-domain`. Proving THAT took 19 -> **11**. Two of the day's five repairs
moved nothing on their own; both were nonetheless necessary, because the shadowing leaf had
to go too.

**`integral-domain-cancel-zero` was already proved -- in a file nobody loaded.**
structure-library/integral-domain-laws.scm unfolds the no-zero-divisor conjunct of
`is-integral-domain-def` and closes it, and it had sat on disk for weeks WITHOUT AN ENTRY IN
`load.scm`, so the proof never ran while integral-domain.scm went on asserting the same fact
unwarranted into seven bills. Nothing catches this: a `.scm` in structure-library/ that
load.scm does not name is simply invisible, and no gate counts files. If you write a proof
file, the entry in load.scm is half the work.

**`zz-is-integral-domain` (7 bills, the last big one) is PROVEN**, in
theorem-library/zz-integral-domain.scm, together with `zz-is-commutative-ring`. Pattern:
zz-ring-is-ring.scm's, one storey up -- unfold the defining IFF, `surface-goal!` the
accessors down to integer arithmetic, and the conjuncts fall to `crs` / `arith` / a
citation. The one piece of real content is that **ZZ has no zero divisors**, which nothing
in number-systems.scm states (there is no ZZ zero-divisor axiom and no sign or trichotomy
machinery for the integers). It is proved where the fact comes from, one system up: QQ is a
FIELD, so `qq-recip-closed` / `qq-recip-inverse` invert any b /= 0, `zz-subset-qq`
(primitive) carries the integers in, and

    a = a.1 = a.(b.b^-1) = (a.b).b^-1 = 0.b^-1 = 0

is four rewrites. `zz-no-zero-divisors` bills `modulo 0`. No induction, no order, no
descent: the integers have no zero divisors because the rationals have inverses.

`integral-domain-nontrivial` went the same way (five lines beside its sibling): it is not
an INSTANCE of a conjunct of `is-integral-domain-def`, it IS one, verbatim. The axiom it
replaced carried the comment "a conjunct of is-integral-domain-def, surfaced as a citable
theorem" -- the proof, written in prose and then not run. Watch for that species of
comment; it is the same failure as the unloaded proof file, one line long.

Three more went the same afternoon, and the pair among them is the cleanest illustration
of the shadowing rule anywhere in the tree, because the what-if PREDICTED it:

* `qq-is-ring` -- PROVEN. `theorem-library/zz-ring-is-ring.scm` is now PARAMETERISED over
  the instance (carrier, defining equation, set-hood fact, three typing axioms) and called
  for ZZ-RING and QQ-RING, rather than copied. The file's name is historical; a third
  numeric ring is one more line of instance data.
* `comm-monoid-is-monoid` -- PROVEN, one line in subtype-laws.scm (`stl--prove-pred!`, the
  abelian-group-is-group shape).
* `nn-add-monoid-is-comm-monoid` -- PROVEN, theorem-library/nn-add-monoid.scm. Those two
  were the ONLY unwarranted leaves of ONE bill (`poly-is-ring`) and shadowed each other:
  measured in advance, either alone moved nothing and the two together moved one.

**`nn-add-monoid` is where NOT to use `crs`.** Its three law conjuncts are closed by
citing `nn-add-assoc` / `nn-add-comm` / `nn-add-zero`, not by the ring simplifier: `crs`
decides commutative-RING identities and **NN is not a ring** -- it has no negation. All
three identities are true of NN, so `crs` would have closed them and nothing would have
looked wrong, but the justification would have been "this holds in any commutative ring",
which is not a statement about NN. An oracle is sound where it applies; knowing that it
applies is the caller's job.

Two driver lessons from that file, both of which cost a run: read the eigenvariables off
the GOAL, never off the context (`dk-asms` order is not the peel order -- taking the
NN-typed hypotheses in context order gives `(w v u)` where the goal wants `(u v w)`, and
`fact` then builds an instance `ass` quietly refuses); and run probe scripts with
`< /dev/null`, because an `error` inside one drops into the `2 error>` REPL and waits on
stdin forever, which looks exactly like an infinite loop.

**`principal-ideal-membership` (5 bills, the largest single one left) is `definitional`**,
stamped at source in ideal.scm. This entry used to end "-- and it is the case where a
PROOF is not available and the stamp is the settled answer". **That was wrong**, and the
counter-example is above: the functoid's unfold equation is provable `modulo 0` by
`(di) (mac 'THE-FUNCTOID) (qrfl)`, and the resulting THEOREM is what `mac-h` needs. The
stamp is still what is IN the tree, and re-tiering moves every citing bill, so it stays
until that measurement is made -- but it is a stamp of convenience, not of necessity. `def-functoid` installs only a rewrite MACETE, not a
theorem, so `mac-h` cannot unfold `PRINCIPAL-IDEAL` in an ASSUMPTION: it warns "unknown
theorem/macete" and the driver sails on with the hypothesis untouched. That is why the
axiom exists at all -- it is the only way to read a member of (a) out of the context,
which is exactly what zz-bezout-proof and spans-submodule-fg-proof do with it. And it is
legitimately definitional: the functoid unfold composed with the SEP separation schema,
both trusted base, i.e. exactly the IFF `def-predicate' would have generated had
PRINCIPAL-IDEAL been a predicate. Same treatment and reasoning as `span-membership`
(mod-seq.scm, 2026-07-10) and the five constructor membership characterisations in
definitional-reclass.scm; this one had simply been missed. Any `SEP`-bodied `def-functoid`
whose members get read out of the context wants the same one-line wrap.

End of 2026-08-10: **301 proven, 109 `modulo 0`, 4 `trust: none`**, in ten repairs, THREE
of which moved nothing on their own. The four that remain have NO shadowing left -- each
is the SOLE unwarranted leaf of its bill, so each is worth its full count:
`zz-is-euclidean-ring` (zz-bezout; needs the division algorithm on ZZ, a different piece
of work), `rr-is-metric-space` (rr-complete), and `inf-subsets-is-set` (two bills:
totally-bounded-has-cauchy-subsequence, block-family-combinatorial).

Also deliberately left `asserted`: the arity 3-5 forms (`nary-plus-3`, ...), which are not
converses of anything -- they FIX the reading of the parser's flat n-ary node as a left
fold, and nothing else in the theory states it. They have no dependents.

**The shelf grew a FIFTH time on 2026-08-24: `nn-add-succ`** (`a + succ b = succ(a+b)`,
structure-library/nn-arith.scm), stamped `definitional` by the user's decision that Peano
recursion for `+` is part of what NN IS. It was the largest single leaf left, and by the
ranking that matters rather than the obvious one: by CITATIONS it was only third (55,
behind `entry-in-carrier` 63 and `interval-card-in-nn` 60), but by SOLE-leaf count it was
first by half again -- **20**, against 13 for `rr-le-all-pos-nonpos` and 8 for
`metric-dist-real`, and neither of the two more-cited leaves is EVER a bill's only one.
Triage by BILL, again. Measured before/after over 719 proven results: `modulo 0`
**448 -> 468**, 35 further bills shortened, NO bill grew, `trust: none` unmoved at **3**
(block-family-combinatorial, totally-bounded-has-cauchy-subsequence, zz-bezout).
`cc-complete` and `rr-complete` clear together, being the same bill; every fact Example 4.7
(`prove-scripts/drives/poly-antiderivative-drive.scm`) must cite is now debt-free, so that
drive can reach `modulo 0`. The sole-leaf ranking is now headed by `rr-le-all-pos-nonpos`
at 13. Wrapped as a `fluid-let` at the axiom site, not a later `register-provenance!` --
which is what stamped the auto-generated `nn-add-succ-rev` companion too (the load's
`classification:` line went 17 -> **19** de-supported, two names not one).

**And the stamp is NOT free, which is why the site carries a comment saying so.**
`definitional` contributes {} to every bill, so a stamp does not merely re-tier a fact --
it makes the fact invisible to the debt ledger. number-systems.scm axiomatises `+` by its
ALGEBRAIC laws (closure, assoc, comm, `a+0 = a`) and never by its recursion, so calling
the recursion equation "definitional" ALSO asserts that the algebraically-axiomatised `+`
SATISFIES Peano recursion. That is a claim, not a definition, and it is established
nowhere in this tree. The block above the axiom states it plainly and names the exit:
construct NN's `+` by recursion, derive the algebraic laws from it, prove the constructed
operation agrees with the posited one. **Standing rule, confirmed by the user the same
day: a stamp must record its claim.** The `warrant! 'reference` was removed rather than
reworded, on the ordinals precedent -- a warrant is a better tier of DEBT, and
`definitional` says there is no debt.

**`nn-mul-succ` was measured and deliberately NOT stamped.** Its argument is identical.
Measured BEFORE the `nn-add-succ` stamp it clears **nothing** -- all 10 of its bills also
named `nn-add-succ`, the shadowing rule again -- and only afterwards is it worth its own
count: **8** bills (the parity / trichotomy / sqrt-3 block). One explicit decision per
fact; growing the shelf by analogy with a neighbouring decision is exactly how it stops
being explicit.

**Proving a fact that used to be an axiom moves it past the view specializer.**
`view-as-auto-specialize!` runs inside `def-functor`, i.e. when views.scm loads
(load.scm:195) -- long before the interactive tactics exist, so a theorem proved in
theorem-library/ (load.scm 500+) is invisible to it and its view companions are never
built. `abelian-group-idempotent-is-id-module-vector-ag` is cited BY NAME in
theorem-library/module-zero-act, so the move would have silently deleted it.
cancellation.scm already re-ran the specializer for RING-ADDITIVE-AG for this exact
reason. The trap: the unrestricted re-run installed **67** companions -- every
abelian-group theorem proved since views.scm -- to deliver the one that was needed. So
`view-as-auto-specialize!` now takes an optional SECOND argument naming a single theorem
(structures.scm), and errors on an unknown name:

    (view-as-auto-specialize! 'MODULE-VECTOR-AG 'abelian-group-idempotent-is-id)   ; 1, not 67

Reach for the unrestricted form only when carrying a whole backlog across a view is what
you mean, as the RING-ADDITIVE-AG line does.

(The companion figure "438 of 1325 asserted facts carry no warrant" was measured
2026-07-23 and is stale: 117 facts left the asserted column on 2026-08-01. It wants
re-measuring, not adjusting.)

**The continuity algebra is six-sevenths proven, and the last two cost no estimate**
(2026-08-18). `cont-transfer-ptwise-eq` (theorem-library/continuity-transfer.scm) and
`sub-continuous-at` (theorem-library/continuity-sub.scm) are PROVEN `modulo 0`, and with
them **`diff-implies-continuous` bills `modulo 0`**. Only `compose-continuous-at` and
`cont-agree-off-pt` are still asserted in continuity-algebra.scm.

Neither needed an eps/delta argument, and that is the transferable part:

* The TRANSFER is what the algebra was missing. `sum-continuous-at` concludes about the
  LITERAL term it builds, not about "any map that happens to be the sum" -- so without a
  transfer the algebra can only ever conclude about lambdas it built itself. The proof is
  two instances of the pointwise hypothesis and two `subst`; the distance is never opened
  into `abs`, so nothing in it is about RR. (It is stated at RR-MS only because that is
  where continuity-algebra states it.)
* Given the transfer, the DIFFERENCE is a composition of three theorems already in the
  tree -- `neg-continuous-at`, `sum-continuous-at`, `cont-transfer-ptwise-eq` -- plus one
  `crs` to bridge `(- (g w) (h w))` and `(+ (g w) (- (h w)))`. The retired warrant
  proposed the eps/2 route ("a difference is the sum estimate with `-' throughout"), which
  is a second copy of continuity-sum's driver. It was not needed. `neg-continuous.scm`
  moved earlier in load.scm to make this available.

Two mechanics worth keeping. **`mac-h` is destructive, so read a typing off a hypothesis
inside a `have!` LANE**: `(have! '(IN g (FUN RR RR)) (lambda () (mac-h 'is-continuous-at ...)
(split) (slot-h 'PTS ...) (ass)))` unfolds on the side branch only, and the main branch
keeps `IS-CONTINUOUS-AT` intact for the next `fact`. Done in the main branch instead, the
following `fact` silently lands an implication. And `slot-h` is destructive the same way:
in continuity-transfer.scm `(IN b (PTS RR-MS))` is needed as itself (to detach g's
delta-universal) AND as `(IN b RR)` (to detach the pointwise hypothesis), so the `inst+`
must come BEFORE the `slot-h`. continuity-sum.scm meets the same trap and solves it the
other way, with a `have!` that puts the PTS form back.

When a proof turns into a grind, that is a finding, not a failure: add the obvious
lemma to the PSS and record the obstacle. Do not slog.

**`prop` (prop.scm, 2026-08-15) is the second worked example** of that principle, and the
cheapest one to reach for: it decides whether the focus goal follows from the context by
PROPOSITIONAL logic and closes it if so. It dissolves a whole class of leaves that were
each obvious and each wanted a different hand-picked dance -- `(oi-l)(ass)` when a disjunct
is in context, `(oi-r)` plus a conjunction split when it is not, `(ai)` on a negation when
the context is contradictory, `use-em` plus two bodies when the goal needs a case. Atoms
are opaque: `x in a`, an equation, a whole `forall(...)` -- so it will NOT instantiate a
quantifier or reason about equality, and it declines with a COUNTERMODEL naming which atom
must be true and which false, which is usually the missing hypothesis. It **adds no
trust**: it decides semantically (three-valued evaluation, pruned search), then discharges
through `di`/`ai`/`oi-l`/`oi-r`/`ass`/`use-em`/`have!`/`detach!`, so a `qed` over a
`prop`-closed proof bills `modulo 0` and the recorded script is the ordinary step-by-step
proof (verified: `scratchpad/prop-debt-probe.scm`). It is in `*what-now-fire-probes*`, so
the copilot now prints `(prop) => CLOSES the goal` on such a leaf.

Two traps it hit, both the alpha-self-loop above, reached through helpers: an opening
`pbc` put `not G` in the context and then `use-em`'s own `em-prove!` re-assumed it (fixed
by checking the GOAL against the assignment instead -- no pbc at all); and splitting on the
atom of a goal that IS `(OR p (not p))` cuts the goal itself (fixed by routing that shape
to `em-prove!`). Battery: `scratchpad/prop-battery.scm`, 19 cases including five that must
NOT close.

**`contra` (contra.scm, 2026-08-15) is the third**, and it came out of a leaf the user
was driving: unfolding `make-set-membership` in a list-induction base case leaves

    nth(i,l) = x,  i <= length(l),  1 <= i,  i in nn,
    x in set,  length(l) = 0,  l in tuples(a)   |-   x in empty-set

which is closable only because `1 <= i <= length(l) = 0` is absurd. The copilot said
nothing, and the reason was worth more than the leaf. `prop` cannot see it -- the three
order facts are opaque atoms to it, and it correctly reports a countermodel. `ineq` can
do the arithmetic, but **two input-handling traps kept it out of reach**, and both are
now fixed:

* A named premise that is NOT arithmetic used to make the whole call fail. `(ineq 1)`
  closed a goal that `(ineq 1 2)` refused, where 2 was a harmless `u in rr` typing -- and
  the message said "goal not a linear-RR consequence", blaming the goal. Such a premise
  is now SKIPPED; dropping a premise can only make Fourier-Motzkin prove less, so this is
  soundness-preserving by construction.
* `ineq-atom-rr-ok?` demands an `IN _ RR` certificate for every atom of every accepted
  premise. A combinatorial context types its terms in NN, so the oracle refuses. **The
  fix is NOT to weaken the oracle** -- it is trusted, and widening what it accepts widens
  the trusted surface. `contra` DISCHARGES the precondition instead: land the `IN t NN`
  facts the context already fires (found generically by the forward-citation scan, e.g.
  `length(l) in nn` from `l in tuples(a)`), then lift each to RR by `nn-in-rr` (proven,
  `modulo 0`).

The remaining trap is the sharp one: an `=` is arithmetic in SHAPE, so `nth(i,l) = x`
gets accepted and contributes the atoms `x` and `nth(i,l)`, which can never be certified
-- one irrelevant equation in the context poisons a call whose real premises were fine.
`contra--usable-indices` therefore filters premises by the oracle's own test before
naming any. It **probes on a scratch state before committing** (there is no undo: a
composite that cut first would strand two unprovable leaves), adds no trust beyond
`ineq`'s, and is in `*what-now-fire-probes*`, so the panel prints `(contra) => CLOSES the
goal`. Four suite checks; suite 880/0.

Before adding a support, ask whether it is an *instance* of something a tactic could do.
`minimize!` (minimize.scm) is the worked example: `(minimize! '(v ...) GUARD MEASURE)` =
"choose v satisfying GUARD with MEASURE as small as possible", leaving only the two
obligations any minimization owes -- MEASURE lands in NN, and GUARD is satisfiable. It
turned `min-degree-entry` and `class-min-pivot` from `'well-known` warrants into
theorems. It uses no choice: well-ordering returns a *member* of the value set, which is
a `SEP` set, so `sep-me` recovers the witness.

## The gates on the install door

`support` and `theory-add-axiom!` install a raw S-expression. Four load-time gates now
grade what comes through, and they are complementary -- each catches a defect the others
call well-formed:

* `connective-arity-audit` (audit.scm) -- FATAL. A flat `(AND a b c)` is read with
  binary-left/right, so extra conjuncts are silently dropped.
* `free-variable-audit` -- warn-only. A free name means whatever the CALLER spells it.
* `head-registry-sweep` (audit.scm, added 2026-08-04) -- warn-only. Every applied head in
  every installed formula, checked against `*constant-registry*` (expressions.scm) --
  the table `free-vars` / `subst-free` actually consult. An unregistered head is read as
  an applied function VARIABLE. `unknown-head-audit` does NOT do this job: it accepts a
  head that is in `*operators*` or on its own allowlist, and reported 0 while 71 heads
  leaked. `register-operator!` now feeds the registry, so the two tables cannot drift.
  Register a new head in `*wff-term-form-heads*` (wff.scm) if it is a TERM constructor;
  a PREDICATE gets a bare `register-constant!` beside `LIMIT-ORD`, because a predicate in
  the term-form list makes `make-wff` reject every goal that mentions it.
* `install-grading` (`install--grade!`, macetes.scm) -- warn-only, and it fires at
  install time, naming the file. It runs `validate-wff!` -- the grading `make-wff`
  applies -- over every installed formula. It grades SHAPE only: arity, and
  wff-vs-term position. The four variadic macete schemas (RESTVAR/SPLICE) are exempt
  by shape.

Controls for the last two: `scratchpad/gate-control.scm`. A gate that passes everything
reads exactly like a clean library, so make it fail on purpose before believing it.

**`COMP` was in none of the expression walkers** (found and fixed 2026-08-15, while
testing the binder-scope diagnostic above -- its one false positive WAS this bug). The
string `COMP` did not occur in expressions.scm at all. `{x | p}` is `(COMP x p)`, which
binds `x` in `p` and has exactly the `FORALL`/`FORSOME`/`IOTA` shape, but it fell through
to the general compound branch, so `free-vars` called the bound variable FREE,
`subst-free` rewrote it (`r := zz` turned `{r | r in a}` into `{zz | zz in a}`) and
captured into it (`a := f(r)` gave `{r | r in f(r)}`, no rename), and `alpha-equiv?` said
two alpha-variants differed. The repair is one symbol at six case labels, all of shape
`(HEAD var body)`: `free-vars`, `subst-free`, `alpha-equiv-under?` (expressions.scm),
`match-expr`, `rewrite-expr` (macetes.scm), `replace-term` (primitive-inferences.scm),
plus `COMP` in the `term?` head list.

It was LATENT, and that is why it survived: **no installed formula in the tree contains a
COMP** (measured -- 0 of the theorem table), so nothing the library does was ever walked
wrong. It was reachable only by a user who TYPED `{x | p}`, which the parser has always
accepted and the manual documents. `validate-wff!` knew COMP was a binder the whole time
(wff.scm, "COMP bound var not symbol"), so the form graded clean -- a gate that checks
shape cannot see a walker that does not know the shape binds. 10 suite checks over the
two repairs; suite 870/0.

**Nullary application is an error except for `list()` and `set_of()`** (2026-08-15, the
user's call). `h()` used to be accepted everywhere: `p-parse-arglist` returns `'()` on an
immediate `)`, `p-maybe-apply` built `(h)`, `validate-wff!`'s generic application branch
had no arity floor, and `(f)` **printed as `f`** -- so `(= (f) f)` displayed as `f = f`
while `rfl` refused it, the two sides being different S-expressions. `cartesian()` and
`power()` went the same way; `union()` was rejected, but only by the `>= 2 args` floor the
binary case wanted, not by any decision about arity 0.

The rule is enforced at BOTH doors, because `support` / `theory-add-axiom!` install a raw
S-expression that never meets the parser: `p-check-nullary!` (parser.scm, list
`*p-nullary-ok*`) and an arity floor in `validate-wff!`'s generic term-application,
predicate-application and `CARTESIAN` branches (wff.scm). `LIST` keeps its own branch with
no floor -- `(LIST)` is `[]`, the empty TUPLE, which `empty-in-tuples` and `length-of-empty`
are about; `set_of()` is `{}` and never reaches the check, its branch in `p-parse-primary`
calling `expand-set-of` directly. The conventional nullary readings of the other
constructors (empty product, empty union, empty intersection) are deliberately declined:
nothing needs them and the last is a proper class. `expr->str` (sequents.scm) now prints a
nullary application as `f()`, so the arm can no longer hide one. 17 suite checks; the whole
suite is 856/0 and `install-grading` still reports ok, which is the evidence that no
installed formula in the tree ever had a nullary application but `(LIST)`.

Related, and the reason the question came up: `length([]) = 0` is the axiom
`length-of-empty` (theory.scm:648), inside `make-vnb-base-theory` and so `primitive`. It is
not derivable -- `length-cons` characterises `length` only on a `CONS`, and
`tuple-length-zero` runs the other way -- and it carries definedness for free, `=` being
partial. Note also that `set_of(l)` is NOT the set of entries of the tuple `l`:
`expand-set-of` wraps its arguments in a LIST literal, so `set_of(l)` is `{l}`, the
singleton. The set of entries is `make-set(l)`, which is writable on the surface like any
other registered head.

**A printed term must re-parse to the term that was printed** (2026-08-24, found while
proving Example 4.7). `expr->str` printed every same-head child of `+ * and or iff`
without parentheses, on the theory that those operators are associative. They are
associative in RR; they are not associative in the KERNEL, which holds S-expressions.
So the stored `(* (* (succ m) (* (recip (succ m)) c)) v)` -- the shape a chain of
`nary-times-2` rewrites leaves behind -- printed as `succ(m) * recip(succ(m)) * c * v`,
which the reader returns as the FLAT `(* (succ m) (recip (succ m)) c v)`: a different
S-expression, so not `equal?`, so `ass` declines a goal retyped from its own printed
form. Same species as `(f)` printing as `f`, and repaired the same way -- the PRINTER
was made honest, never the comparison lenient. Widening `alpha-equiv?`/`ass` to absorb
the difference was rejected outright: it enlarges what the kernel calls the same term.

The READER held the mirror half, and it is why parenthesising alone would have fixed
nothing. `p-parse-mul` / `p-parse-add` tested the SHAPE of the left operand
(`(eq? (car left) '*)`) instead of whether this loop had accumulated it, so `(a * b) * c`
was spliced into the flat `(* a b c)` -- the left-nested term was UNWRITABLE on the
surface -- while the mirror-image `a * (b * c)` built the nested node, the right operand
never being spliced. Both loops now carry a `mine?` flag. **Unparenthesised input reads
exactly as before**: `a + b + c` is still the flat node `nary-plus-3` fixes the meaning
of, and the `/` sugar branch is untouched, so every mixed `*` `/` chain reads as it did.
Making the parser LEFT-FOLD instead -- the other way to reconcile the two -- would have
retired the flat n-ary node the `nary-*-3/4/5` axioms exist to interpret, and rewritten
the statement of every arithmetic theorem in the tree. Not that.

The only two strings in the tree whose reading changed are in `theorem-library/ell-two.scm`
(`rr-sq-add-le`, `cc-magnitude-sq-add-le`), which write
`((u * u) + (u * u)) + ((v * v) + (v * v))` and MEANT the grouping: the `have!` three lines
below each writes that nested S-expression by hand, so author and parser now agree where
they used not to. Both still `qed`, no leaves. Blast radius of the defect: 48 installed
formulas held a nested `+`/`*` and 8 a left-nested `and`/`or`; 55 of them stopped
round-tripping, and now do. The 24 with a genuinely FLAT 3-or-more-ary node still print
unparenthesised -- a suite check pins that, so a later repair cannot buy honesty by
bracketing everything. The checks test the STORED FORM, print-then-parse-then-`equal?`;
a string check cannot tell the flat node from the left-nested one, which is the defect.

**The name half of that is now REPAIRED (2026-08-24): 108 of 3891 -> 3.** Seven constants
were spelled with characters the tokenizer reads as operators, and between them they cost
105 of the 108 remaining round-trip failures. They are gone, renamed to the spellings the
surrounding axiom names already used:

    <=_ORD -> ORD-LE            (ord-le-refl, ord-le-trans, ... already said so)
    <_ORD  -> ORD-LT            (ord-lt-iff)
    RR*    -> RR-STAR           (rr-star-membership, pos-inf-in-rr-star)
    RR+*   -> RR-POS-STAR       (rr-pos-star-membership); the monoid is
                                RR-POS-STAR-ADD-MONOID
    CARD*  -> CARD-STAR         the DEFINED cardinal, companion to axiomatised CARD
    INJECTIVE* -> INJECTIVE-STAR  the class-level injectivity, companion to INJECTION

Six of the seven errored out, which is annoying but honest. **`card*` did not**:
`read-ident` stops at the `*`, `read-op` takes it, and `card*(a)` parsed as the PRODUCT
`(* card a)` -- a different term, no error, no warning. That is the case that made this
worth doing. A suite check now pins BOTH readings (`card-star(a)` is an application;
`card*(a)` is still a product) so the reason cannot be forgotten. `succ_ORD` was NOT
renamed and does not need to be: a leading letter makes `_` an ordinary identifier
character, which is why the project's own `i_`/`r_` convention works.

No old spelling survives as an alias. `alias!` (macetes.scm:1354) records human search
names for THEOREMS -- it cannot give a constant a second spelling at all -- and an alias
that could would reinstate the one thing the rename removes, `card*` included.

The rename moved NO bill (732 proven, every debt set and trust tier byte-identical; five
proven theorem NAMES changed, `card*-segment` -> `card-star-segment` and siblings, and
none of them is any bill's leaf). It also let the doc round-trip gate drop its one
exemption: `IS-MEASURE-SPACE` was exempt because its MEAS slot's codomain was `RR+*`, and
`*doc-roundtrip-exempt*` is now `'()`.

**The 3 that remain are ONE defect, and it is not a name**: `cc-i-squared` (with its
`-rev`) and `rr-bernoulli` all hold the negative integer LITERAL `-1`, which prints as
`-1` and reads back as the unary application `(- 1)`. Same species as the `(f)`-prints-as-
`f` arm: a printed form that re-reads as a different S-expression. It wants its own
decision (print `0-1`, as the imaginary unit prints `0-i`, or make the reader fold a unary
minus over a literal), and it is the whole residue.

## Shipping

`~/prover-src.tar.gz` is rebuilt by a Stop hook (`~/.claude/settings.json`): gzipped tar
of `prover/`, no `.git`, no `.com`/`.bin`/`.ext`. That is what "the tarball" means.
