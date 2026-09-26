<!-- VERBATIM copy of a section of CLAUDE.md as it stood on 2026-09-18, moved here when
CLAUDE.md was trimmed to its operational rules.  Nothing was edited.  The dated findings,
measurements and case histories behind each rule in CLAUDE.md are in this text. -->

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

