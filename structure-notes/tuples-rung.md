# The TUPLES generation rung

Specification, 2026-08-12. Not yet built.

## 1. The two defects

`TUPLES` is axiomatised entirely by consequences of membership and never by a
construction. Its complete inventory is five one-way facts:

    tuples-sethood     theory.scm:583      A in SET  =>  TUPLES(A) in SET
    make-set-sethood   theory.scm:603
    length-in-nn       theory.scm:633      L in TUPLES(A)  =>  LENGTH(L) in NN
    nth-in-range       theory.scm:636      ... 1 <= i <= LENGTH(L)  =>  NTH(i,L) in A
    list-sethood       theorem-library/axioms.scm:169

Nothing anywhere is an `IFF`. Two consequences follow, and both were reached
from the same direction.

**(1) `LENGTH` is not pinned on a variable tuple.** Only four formulas
constrain it -- the two above, plus `length-of-empty` (theory.scm:619) and the
index bound inside `make-set-membership` (theory.scm:595) -- and all four are
satisfied by the interpretation

    LENGTH(L) = 0   for every L.

`length-of-empty` holds by fiat; `length-in-nn` holds since `0 in NN`;
`nth-in-range` and `make-set-membership` hold **vacuously**, there being no `i`
with `1 <= i <= 0`, which also makes `MAKE-SET(L)` empty for every `L` in
agreement with `make-set-empty` and `make-set-sethood`. The axioms therefore do
not distinguish the intended interpretation from the constant-zero one.
theory.scm:616 concedes this in its own parenthesis.

The trusted base is larger than the axiom list, and the kernel rule
`reduce-length-in-expr` / `pi-length-reduce!` (primitive-inferences.scm:801,
surface `len-r`) reduces `(LENGTH (LIST t_1 ... t_n))` to `n` structurally. That
excludes the constant-zero reading for *literal* tuples. For a variable `L` it
changes nothing: `LENGTH(L)` remains constrained from above and not at all from
below.

The practical cost is that membership in `MAT(m,n,X)` -- a `SEP` over
`MATRIX(X)` requiring `SIZE(P) = [m,n]`, i.e. `LENGTH(P) = m`
(structure-library/matrix.scm:33 and :47) -- is a claim about `LENGTH` that the
axioms cannot reach for a non-literal `P`. Hence `matof-in-mat` is a `support`
warranted `well-known` (matrix.scm:136) rather than a theorem, and the two
nonvacuity results `mat-1-0-nonempty` / `mat-0-1-nonempty`
(theorem-library/span-bricks2-proof.scm:332-348) both route through it. This is
incompleteness and not unsoundness: everything proved holds in the intended
model. But from the axioms alone, every `forall P in MAT(m,n,X)` theorem is
consistent with being about nothing, and the fact ruling that out is asserted.

**(2) No fact about entries ever concludes membership.** In particular
monotonicity of `TUPLES` is unstatable, which is what made the `SET` guard on
`length-in-nn` unbuildable rather than merely inconvenient: from
`Q in TUPLES(TUPLES X)`, which is what `matrix-membership` (matrix.scm:17)
supplies, reaching `Q in TUPLES(SET)` needs the inclusion
`TUPLES(A) subset TUPLES(SET)`, and no such fact exists. (The other half of that
bridge, "every member of a class is a set", *is* available --
`membership-implies-sethood`, theory.scm:249. The comments at theory.scm:627 and
theorem-library/mat-basics.scm:34 misstate this and should be corrected to name
the missing half only.) The guard was generalised away on 2026-08-11 by fiat for
exactly this reason.

## 2. Expected effect on the debt ledger: none

The axioms below belong in base, hence bill `{}`; the two they retire are
primitive and bill `{}` already. No bill should move. The return on this rung is
what becomes provable and what stops being underdetermined. If a bill does move,
something else is wrong.

## 3. The constructor

`PREPEND`, the name theorem-library/axioms.scm:24 already reserves.
`(PREPEND x L)` denotes `L` with `x` in front.

Registration:

* **wff.scm:217**, `*wff-term-form-heads*` -- add `PREPEND`. It is a term
  constructor, so this is the correct list, and wff.scm:248 feeds it onward to
  `register-constant!`, satisfying `head-registry-sweep` and `free-vars` in one
  edit. (A predicate would instead take a bare `register-constant!` beside
  `LIMIT-ORD`; a predicate placed in the term-form list makes `make-wff` reject
  every goal mentioning it.)
* **primitive-inferences.scm:566**, `*total-term-heads*` -- a decision, not a
  default. `LIST` is already on that list. Adding `PREPEND` lets `rfl` close
  `(= (PREPEND x L) (PREPEND x L))` with no definedness obligation, on `LIST`'s
  own reasoning: the constructor is a total spine and does not inspect its
  arguments. Recommended. If it is left off, every use owes a definedness step.
* `register-operator!` and `notation!` beside the definition, per the operator
  table convention.

## 4. The axioms

Binary `AND` nesting throughout; `connective-arity-audit` is fatal on a flat
one. The template is `nn-induction` (number-systems.scm:167), whose step
antecedent is likewise `(AND (IN n NN) (IN n C))`.

    A1  tuples-nil
        (FORALL A (IN (LIST) (TUPLES A)))

    A2  prepend-closed
        (FORALL A (FORALL x (FORALL L
          (IMPLIES (AND (IN x A) (IN L (TUPLES A)))
                   (IN (PREPEND x L) (TUPLES A))))))

    A3  tuples-induction
        (FORALL A (FORALL C
          (IMPLIES (AND (IN (LIST) C)
                        (FORALL x (FORALL L
                          (IMPLIES (AND (IN x A) (AND (IN L (TUPLES A)) (IN L C)))
                                   (IN (PREPEND x L) C)))))
                   (FORALL L (IMPLIES (IN L (TUPLES A)) (IN L C))))))

    A4  length-prepend
        (FORALL A (FORALL x (FORALL L
          (IMPLIES (AND (IN x A) (IN L (TUPLES A)))
                   (= (LENGTH (PREPEND x L)) (succ (LENGTH L)))))))

    A5  nth-prepend-1
        (FORALL A (FORALL x (FORALL L
          (IMPLIES (AND (IN x A) (IN L (TUPLES A)))
                   (= (NTH 1 (PREPEND x L)) x)))))

    A6  nth-prepend-succ
        (FORALL A (FORALL i (FORALL x (FORALL L
          (IMPLIES (AND (IN i NN) (AND (IN x A) (AND (IN L (TUPLES A))
                        (AND (<= 1 i) (<= i (LENGTH L))))))
                   (= (NTH (succ i) (PREPEND x L)) (NTH i L)))))))

A3 is the no-junk principle, so no separate "every tuple is nil or a prepend"
axiom is required. A4-A6 are guarded rather than unguarded because `LENGTH` and
`NTH` are partial: an unguarded equation would assert something about
`(PREPEND x junk)`.

## 5. The primitive inference

`pi-tuples-induction!`, modelled on `pi-nn-induction!`
(primitive-inferences.scm:1007). On a goal of the shape

    (FORALL L (IMPLIES (IN L (TUPLES A)) body))

it produces

    base:  body[L := (LIST)]
    step:  (FORALL x (FORALL L
             (IMPLIES (AND (IN x A) (IN L (TUPLES A)))
                      (IMPLIES body body[L := (PREPEND x L)]))))

Wiring follows `ni` exactly: `cmd-tuples-induction` in proof-commands.scm beside
:605, the surface entry in interactive.scm beside :434, and the dispatcher case
at interactive.scm:3927.

**The one point at which the template does not carry over.**
`pi-nn-induction!` reuses the goal's own binder; the step here introduces a new
binder `x` that must be fresh against `body`. Use the fresh-var machinery, not a
fixed name.

**The surface name must be `tind`, not `ti`.** `ti` is already bound, to
`cmd-tuples-intro` (interactive.scm:427) -- and note that `tuples-intro` and
`tuples-elim` are both on `kernel-rules-audit`'s list of documented tags that no
proof in the library exercises, so the collision is with a rule that is live but
unused rather than with a dead name. `tind` also stays clear of the two-capital
case-fold danger zone that `TI` would occupy.

## 6. Consequences

Retired, by proof, in a new `theorem-library/tuples-laws.scm` -- **whose entry in
load.scm is half the work**, a file the loader does not name being simply
invisible:

* `length-in-nn` (theory.scm:633). Base from `length-of-empty` and `0 in NN`;
  step from A4 and succ-closure.
* `nth-in-range` (theory.scm:636). Induction on `L`, using A5 and A6, with A4
  for the index bound.

Newly available:

* **`tuples-mono`**: `A subset B  =>  TUPLES(A) subset TUPLES(B)`. Induction with
  `C := TUPLES(B)`; base A1, step A2. This is the fact whose absence forced the
  `SET` guard to be removed by fiat.
* **`tuples-entry-iff`**: `L in TUPLES(A)` iff `L in TUPLES(SET)` and
  `NTH(i,L) in A` for every `1 <= i <= LENGTH(L)`. Forward is `nth-in-range`;
  backward by induction. The membership characterisation the constructor has
  never had.
* `TUPLES(A) subset TUPLES(SET)` for every `A`, from `tuples-mono` and
  `membership-implies-sethood`. `TUPLES(SET)` is thus the maximal one, and the
  natural home for an `IS-TUPLE` predicate should one be wanted.
* `LENGTH` is pinned: A4 with succ-not-zero excludes the constant-zero
  interpretation, and `LENGTH(L) = 0 => L = (LIST)` becomes provable.

**Not** consequences, stated here so that they are not later assumed:

* `tuples-sethood` (theory.scm:583). Induction establishes properties of the
  members of a class, not sethood of the class itself. `TUPLES(A)` is morally the
  union over `n` of `A^n`, so its sethood wants replacement together with a union
  over `NN` -- a separate rung. The axiom stays.
* `make-set-sethood` (theory.scm:603). Provable only with a `MAKE-SET` prepend
  law (`MAKE-SET(PREPEND x L)` = `MAKE-SET(L)` with `x` inserted) as a seventh
  axiom, or by derivation from `make-set-membership` and separation. Decide
  which; do not leave it implicit.
* `matof-exists` (matrix.scm:124), and with it the nonvacuity of the matrix
  layer. matrix.scm:112 already names what that needs -- "a general
  list-tabulation / 2-index recursion primitive" -- and this is the honest limit
  of the present rung: **A3 supplies proof by induction, not definition by
  recursion.** The recursive law for `LENGTH` is postulated as A4, not derived
  from a recursion theorem, and each further recursive function on tuples will
  likewise require its own defining law until such a theorem exists. That is the
  next rung, not this one.

## 7. Placement, and the provenance decision

Placing A1-A6 in `make-vnb-base-theory` (theory.scm) puts them under the
`primitive` fluid-let at theory.scm:613, so they contribute `{}` to every bill --
the treatment `nn-induction` receives by living in a `*primitive-files*` entry.
That is growth of the primitive shelf, which by standing policy requires an
explicit decision, recorded with its reason in the file. The axiom count moves
95 -> 101, or 102 with the `MAKE-SET` law.

The alternative is a new structure-library file using `support` and `warrant!`,
which keeps the assumption visible in bills and permits promotion later. These
axioms say what a finite sequence *is*, which argues for the base, but the call
is not a default and should be made deliberately.

## 8. Build order

1. **Control script first**, `scratchpad/tuples-control.scm`, run BEFORE any
   edit: probes for `tuples-mono`, for `tuples-entry-iff`, and for `LENGTH` of a
   variable tuple, each of which must fail as things stand. A rung that passes on
   the first run reads exactly like a clean library.
2. Register the head; install A1-A6; recompile the edited files *before* loading
   anything; check all four install gates and the load log.
3. Add `pi-tuples-induction!` and its surface; confirm on a probe that the rule
   actually fires -- every primitive inference gives its focus node an in-arrow,
   so `(null? (sequent-node-in-arrows n))` afterwards means it did not.
4. Prove `length-in-nn` and `nth-in-range` in `theorem-library/tuples-laws.scm`;
   add the load.scm entry.
5. Retire the two axioms; dump all bills and diff byte-for-byte against the
   baseline; run the full suite alone, checking for the `SUMMARY` line, since
   exit 0 does not mean it ran.

Step 5 is expected to produce no change, for the reason given in section 2.
