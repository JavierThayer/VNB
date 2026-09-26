<!-- VERBATIM copy of a section of CLAUDE.md as it stood on 2026-09-18, moved here when
CLAUDE.md was trimmed to its operational rules.  Nothing was edited.  The dated findings,
measurements and case histories behind each rule in CLAUDE.md are in this text. -->

## The gates on the install door

`support` and `theory-add-axiom!` install a raw S-expression. The end of `load.scm` now
runs SEVEN numbered gates; the four below are the ones on THAT door, and they are
complementary -- each catches a defect the others call well-formed. (The other three
guard different doors: `sethood-audit` is the fifth, `report-page-audit` the sixth -- both
described in their own sections above -- and `kernel-callers-audit` the seventh, below.)

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

An eighth, `install-duplicate-audit` (load.scm, 2026-09-16, warn-only), counts theorem
names installed twice during the load. The overwrite warning had printed on every load
for weeks without anyone acting on it. The first count was seven, of four kinds:
* a definitional fact re-added as an asserted PSS entry, which changes every later bill;
* a fact asserted twice;
* a fact proven twice;
* four supports never retired after their proofs landed.

All seven were repaired, and the count is now zero.

And the seventh gate is on a DIFFERENT door -- not what a formula says, but **who may
write the deduction graph**:

* `kernel-callers-audit` (audit.scm, added 2026-09-12) -- FATAL. `dg-apply-rule!`
  (deduction-graphs.scm:283) is the sole procedure that writes an inference into a
  deduction graph and it VALIDATES NOTHING: it records the tag it is handed. So the
  trusted code base is exactly the set of procedures that call it, and nothing bounded
  that set -- `kernel-rules-audit` checks that the TAGS are documented, never which
  procedures stamp them. This reads every loaded file and counts calls in code position
  **and uses of the name as a VALUE**, the second being the escape hatch the first
  misses: `(map dg-apply-rule! ...)` moves the call site to wherever the caller lives.
  The allowlist is `*kernel-caller-files*` (8 files: `primitive-inferences`, `macetes`,
  `theory`, `arith-eval`, and the four oracles). Enlarging the trusted base now costs a
  deliberate entry there, on the same one-explicit-decision-per-fact discipline as the
  primitive shelf. FATAL on the `connective-arity-audit` precedent -- a gate goes fatal
  once its backlog is zero, and this one's backlog is zero; a limit that only warns is
  not a limit. Load line: `68 call site(s) ... in 8 file(s), all allowed; 0 value use(s)`.

  Two things from building it. **A definition's formal list is spelled exactly like a
  call**: counting `(define (dg-apply-rule! dg rule hyps concl) ...)` reported 69 sites
  in 9 files, the extra being deduction-graphs.scm, where the writer LIVES and which is
  not a caller. With formals skipped this scan and the kernel map's independently written
  one agree exactly (68 / 8 / 0), which is the cross-check worth having. And the **cost is
  I/O, not parsing**: a reader pass over all 433 files was 17.3 s, and a text pre-filter
  skipping the 422 that cannot contain the call took it to 7.4 s -- about 4% of the load.
  That floor is why `duplicate-define-audit` stays out of the load and in the suite.

Controls for the last two: `scratchpad/gate-control.scm`. A gate that passes everything
reads exactly like a clean library, so make it fail on purpose before believing it. The
kernel-caller gate's control is in the suite instead (three checks, one of them the
definition/quote/value battery), for the same reason.

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

