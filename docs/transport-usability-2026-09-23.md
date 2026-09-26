# Using a structure theorem at another structure: the state of the mechanisms (2026-09-23)

Question (the user, 2026-09-23): "I hope we could get the 'cross structure' theorem
application to some degree of usability. I really don't have a clue how to use it."

This note answers with (1) a walkthrough of what a user types today, per target, with the
real output; (2) a table of the mechanisms; (3) the defects and gaps, each with a
reproduction; (4) a proposal for one user-facing command, not built.

**Provenance of the output quoted below.** Every quoted goal, landing and error comes from
four probes run against a band, kept in `scratchpad/triage/transport/tpu1.scm` ..
`tpu4.scm`; the full logs are on the workers at `/home/ubuntu/probes/transport__tpu{1..4}.scm.log`.
The brief named worker-01 with a band built after 22:00 UTC. worker-01's band was built at
19:46 UTC and worker-04's at 21:09 UTC, so neither met that condition. `tpu1` ran on
worker-04; worker-04 then started a cold build (`batch24-cold`) and its band was absent during the build, so
`tpu2`-`tpu4` ran on worker-01. Every theorem and mechanism these probes use predates both
bands. The output is quoted here with line breaks added, and nothing else changed.

The running example is RANDO's lemma, proved generically in two lines (`dk-peel!`, `crs`),
`proven modulo 0`:

    rando-square : forall([r], is-commutative-ring(r) implies
                     forall([x in carr(r), y in carr(r)],
                       (mul(r))((add(r))(x, y), (add(r))(x, y))
                       = (add(r))((add(r))((mul(r))(x, x),
                                           (add(r))((mul(r))(x, y), (mul(r))(x, y))),
                                  (mul(r))(y, y))))

together with the library's own `binomial-theorem` (binomial-proof.scm), `ring-power-of-one`
(bernstein-basis.scm:139), `ring-power-succ` and `ring-power-type`.

---------------------------------------------------------------------------------------------

## 1. The walkthrough

All commands below are Scheme forms. They are typed at the REPL (`./prover -i`, or the Emacs
prover buffer) or written in a proof file; there is no menu item, button or `TACTICS.md`
entry for any of them (`grep -i transport emacs/*.el reference/TACTICS.md` finds nothing).
Two kinds of command must be kept apart:

* **installers** -- `transport!`, `view-as-auto-specialize!`, `specialize-structure` (`spec`).
  Each creates a NEW named theorem. `transport!` also opens its own proof with `sp`
  (transport.scm:194) and closes it with `qed`, so it must never be called while a proof is
  open: it replaces `*ps*`.
* **in-proof steps** -- `fact`, `slot-h`, `mac-h`, `dk-lam-b-h!`, `in-rr`, `ass`. These land
  the instance as a hypothesis of the proof in progress and install nothing.

### (a) At ZZ-RING (a `declare-instance!` constant)

ZZ-RING is the 6-tuple of numeric-instances.scm:233. Its slots hold lambdas, e.g.
`ADD(ZZ-RING) == vnb-lambda([x_, y_], cartesian(zz, zz), x_ + y_)` (theorem `zz-ring@add`,
minted by `declare-instance!`, structures.scm:438).

**The installer route: `transport!`.**

    (transport! 'rando-square 'ZZ-RING 'zz-is-commutative-ring)

This form FAILS. The first surface rewrite spawns two side conditions, the loop loses track
of the hypothesis, and the call errors:

    ;; mac-h: lam-slot-add-apply applied; 2 side-condition(s) spawned as subgoal(s) ...
    ;VNB warning: mac-h: lam-slot-mul-apply does not occur in the cited assumption: forall([x in zz,
        y in zz], (vnb-lambda([x_, y_], cartesian(zz, zz), x_ * y_))(x + y, x + y) = ...
    *** transport!: rando-square at zz-ring did NOT close.
       GOAL: forall([x in zz, y in zz], (vnb-lambda(...x_ * y_))(x + y, x + y) = ...
       GOAL: (vnb-lambda(... x_ + y_))((vnb-lambda(... x_ * y_))(x, x), ...) in zz
    transport!: unfinished rando-square zz-ring

The cause is Finding F2 below. `transport!` succeeds only when the body has no NESTED
operation applications. On the library's flat laws it works. Two examples:

    (transport! 'ring-power-type 'ZZ-RING 'zz-is-commutative-ring)
    ;; qed ring-power-type@zz-ring: proven modulo 0
    ring-power-type@zz-ring : forall([x in zz, n in nn], ring-power(zz-ring, x, n) in zz)

    (transport! 'ring-power-succ 'ZZ-RING 'zz-is-commutative-ring)
    ;; qed ring-power-succ@zz-ring: proven modulo 0
    ring-power-succ@zz-ring : forall([x in zz, n in nn], ring-power(zz-ring, x, succ(n))
                               = (vnb-lambda([x_, y_], cartesian(zz, zz), x_ * y_))(ring-power(zz-ring, x, n), x))

The second result is NOT in the surface vocabulary. The MUL lambda survives, because its
argument `ring-power(zz-ring, x, n)` has no typing the rewriter can see. `ring-power(zz-ring, ...)`
also survives, because no bridge to `x ^ n` exists (Finding F5).

The existing cancellation example (cancellation.scm:190) works because its body
`a + c = b + c => a = b` is flat. It is also a two-step composition: a view companion, then
`transport!`.

    (transport! 'ring-power-of-one 'ZZ-RING 'zz-is-commutative-ring)
    transport!: nothing to normalize -- is INSTANCE declared? zz-ring
    (transport! 'binomial-theorem 'ZZ-RING 'zz-is-commutative-ring)
    transport!: nothing to normalize -- is INSTANCE declared? zz-ring

Both theorems have the NN binder outermost (`forall([n in nn, r], ...)`, the shape `ni`
demands). `transport!` substitutes ZZ-RING for `n`, finds nothing to rewrite, and blames
the instance (Finding F1).

**The in-proof route: `fact` plus the slot doors.** This one works, and it is what a user
should do today. The proof file below proves the ZZ instance of rando-square in the surface
language (tpu3, `(a-hand)`, `proven modulo 0 [oracles: crs arith]`):

    (sp (make-wff '(FORALL x (IMPLIES (IN x ZZ) (FORALL y (IMPLIES (IN y ZZ)
          (= (* (+ x y) (+ x y)) (+ (+ (* x x) (+ (* x y) (* x y))) (* y y)))))))))
    (dk-peel!)
    (fact 'zz-is-commutative-ring)
    (dk-have! '(IN x (CARR ZZ-RING)) (lambda () (slot 'CARR) (ass)))
    (dk-have! '(IN y (CARR ZZ-RING)) (lambda () (slot 'CARR) (ass)))
    (fact 'rando-square 'ZZ-RING 'x 'y)       ; lands 7 formulas; the deepest is E0
    (slot-h 'ADD E0)                          ; -> E1
    (slot-h 'MUL E1)                          ; -> E2
    ;; one in-rr typing per compound subterm, SIX here:
    (dk-have! '(IN (+ x y) ZZ) (lambda () (in-rr)))   ... (* x x), (* x y), (* y y),
                                                          (+ (* x y) (* x y)), (+ (* x x) ...)
    (dk-lam-b-h! E2)                          ; one pass
    (ass)

The goal before `fact` is `(x + y) * (x + y) = (x * x + (x * y + x * y)) + y * y`. The
hypotheses step by step:

    E0  (mul(zz-ring))((add(zz-ring))(x, y), (add(zz-ring))(x, y)) = (add(zz-ring))(...)
    E1  (mul(zz-ring))((vnb-lambda([x_, y_], cartesian(zz, zz), x_ + y_))(x, y), ...) = ...
    E2  (vnb-lambda(... x_ * y_))((vnb-lambda(... x_ + y_))(x, y), ...) = ...
    E3  (x + y) * (x + y) = (x * x + (x * y + x * y)) + y * y        -- closes by ass

The route costs fourteen commands for a one-line fact. The user has to know `slot-h`
(interactive.scm:1556), the rule that an instance-value macete must never be fired by name,
`dk-lam-b-h!` (driver-kit.scm:2455), and that beta needs every argument typed first. The
`E0`..`E2` names have to be captured from the context diff, because `fact` lands the whole
instantiation chain.

**The binomial theorem at ZZ-RING** goes the same way and stops short of the goal (tpu3,
`(a-binom)`):

    (fact 'binomial-theorem 2 'ZZ-RING 'x 'y)   (slot-h 'ADD E0)   (dk-have! '(IN (+ x y) ZZ) ...)
    (dk-lam-b-h! E1)
    landed:  ring-power(zz-ring, x + y, 2) = sum(zz-ring, comb-kk(zz-ring, x, y, 2), succ(2))
    goal:    (x + y) ^ 2 = (x ^ 2 + 2 * (x * y)) + y ^ 2

No theorem in the table relates `ring-power` to `^`: the probe filtered all 5,265 theorems for
one mentioning both `ring-power` and ` ^ ` and found none. Nor does one relate `sum(zz-ring, ...)`
to a surface sum, or evaluate `comb-kk` at literals. The instance is true and cannot be
used. For this particular goal the theorem is not needed, since `crs` expands literal powers
(tpu4: `(x+y)^3` on CC closes by `(dk-peel!) (crs)` alone).

**specialize-structure / spec** (structures.scm:1280, interactive.scm:5621). This is the
door the manual documents (docs/ch-defs.tex:716-800):

    (specialize-structure 'ZZ-RING 'COMMUTATIVE-RING 'zz-is-commutative-ring)
    64 theorems specialized for zz-ring
    ring-power-succ-zz-ring : forall([x in carr(zz-ring), n in nn],
        ring-power(zz-ring, x, succ(n)) = (mul(zz-ring))(ring-power(zz-ring, x, n), x))
    provenance: asserted     debt-of: (ring-power-succ-zz-ring)     debt-of ring-power-succ: ()
    binomial-theorem-zz-ring present? #f

It installs statements in the ACCESSOR vocabulary, without proof, as unwarranted ASSERTIONS
(Finding F7). It also skips every theorem whose structure binder is not outermost.

### (b) At RR, seen as a ring through NORMED-FIELD-AS-COMMUTATIVE-RING

RR-NORMED-FIELD is a 7-tuple (numeric-instances.scm:277). It reaches the ring world only
through the view `NORMED-FIELD-AS-COMMUTATIVE-RING` (views.scm:167). The view has a typing
axiom, `normed-field-as-commutative-ring-is-commutative-ring` (stamped `definitional`), and
six PROVEN read-offs at RR, `rr-scalar-ring-{carr,add,mul,neg,zero,one}`
(normed-field-ring-view.scm:117 ff.).

**`transport!` directly at the view term or at the 7-tuple:**

    (transport! 'rando-square '(NORMED-FIELD-AS-COMMUTATIVE-RING RR-NORMED-FIELD) 'rr-is-normed-field)
    transport: not a declared instance (normed-field-as-commutative-ring rr-normed-field)

    (transport! 'rando-square 'RR-NORMED-FIELD 'rr-is-normed-field)
    ... is-commutative-ring(rr-normed-field) implies forall([x in rr, y in rr], ...)
    transport!: unfinished rando-square rr-normed-field

The second call instantiates a COMMUTATIVE-RING theorem at a 7-tuple, which can never
satisfy it. `transport!` does not compare the witness with the guard and goes on to fail
later with an unrelated message (Finding F3).

**Two installers composed by hand: a view companion, then `transport!`.** This works for flat
statements:

    (view-as-auto-specialize! 'NORMED-FIELD-AS-COMMUTATIVE-RING 'rando-mulcomm)
    ;; def-functor normed-field-as-commutative-ring: 1 commutative-ring theorems specialized ...
    rando-mulcomm-normed-field-as-commutative-ring : forall([r], is-normed-field(r) implies
        forall([x in carr(r), y in carr(r)], (mul(r))(x, y) = (mul(r))(y, x)))
    (transport! 'rando-mulcomm-normed-field-as-commutative-ring 'RR-NORMED-FIELD
                'rr-is-normed-field 'rando-mulcomm@rr)
    ;; qed rando-mulcomm@rr: proven modulo 0
    rando-mulcomm@rr : forall([x in rr, y in rr], x * y = y * x)

The same two calls on `rando-square` fail exactly as in (a), for the nested terms.
On `ring-power-type` they succeed but leave the view in the statement:

    ring-power-type@rr : forall([x in rr, n in nn],
        ring-power(normed-field-as-commutative-ring(rr-normed-field), x, n) in rr)

The companion's accessor reduction (`view-as-reduce-accessors`, structures.scm:1087) rewrites
only `ACC(VIEW(r))`, and nothing rewrites a derived operator applied to the view.

    (view-as-auto-specialize! 'NORMED-FIELD-AS-COMMUTATIVE-RING 'binomial-theorem)
    ;; ... 0 commutative-ring theorems specialized (restricted to binomial-theorem).

**The in-proof route (tpu2, `(b8)`) works.** It has the same fourteen-command shape as
(a), with the view read-offs as theorems:

    (fact 'rr-is-normed-field)
    (fact 'NORMED-FIELD-AS-COMMUTATIVE-RING-is-COMMUTATIVE-RING 'RR-NORMED-FIELD)
    (dk-have! '(IN x (CARR (NORMED-FIELD-AS-COMMUTATIVE-RING RR-NORMED-FIELD)))
              (lambda () (mac 'rr-scalar-ring-carr) (ass)))           ; and y
    (fact 'rando-square '(NORMED-FIELD-AS-COMMUTATIVE-RING RR-NORMED-FIELD) 'x 'y)
    (mac-h 'rr-scalar-ring-add E0)   (mac-h 'rr-scalar-ring-mul E1)
    six (dk-have! '(IN t RR) (lambda () (in-rr)))
    (dk-lam-b-h! E2)   (ass)                                          ; closed

This is the pattern bernstein-basis.scm (from :91, `bn-r`) follows to run the binomial
theorem at RR. There the SUM side is bridged by the RR-only theorem
`series-partial-sum-is-ring-sum` (bernstein-basis.scm, section 2), and the power side never
has to reach `^`, because the identity ends in `1^n = 1`.

### (c) At CC

CC-NORMED-FIELD (numeric-instances.scm:284) has no `cc-scalar-ring-*` read-offs
(`cc-scalar-ring-add` is absent from the theorem table). It needs none: the GENERIC read-offs
`normed-field-ring-view-*` (normed-field-ring-view.scm, section 1, e.g.
`add(normed-field-as-commutative-ring(f_)) == add(f_)`) followed by the instance's own slot
equations do the same job. Both routes were probed:

* the two installers composed: `(transport! 'rando-mulcomm-normed-field-as-commutative-ring
  'CC-NORMED-FIELD 'cc-is-normed-field 'rando-mulcomm@cc)` gives
  `forall([x in cc, y in cc], x * y = y * x)`, `proven modulo 0`;
* the in-proof route (tpu4, `(c-hand)`), `proven modulo 0`, where the carrier typing is
  `(mac 'normed-field-ring-view-carr) (slot 'CARR) (ass)` and the rewrites are
  `(mac-h 'normed-field-ring-view-add E0) (mac-h 'normed-field-ring-view-mul E1)
  (slot-h 'ADD E2) (slot-h 'MUL E3)`, then six `in-rr` typings, `dk-lam-b-h!` and `ass`:
  sixteen commands.

The binomial theorem at CC fails for the same reasons as at ZZ (Findings F1 and F5).

### (d) Inside a structure-generic proof, the structure a bound variable

This is the case that works well, provided the guard matches.

* Same structure class: `(fact 'rando-square 'q 'x 'x)` with `IS-COMMUTATIVE-RING(q)` in
  context lands the instance in `q`'s own accessors; `ass` closes.
* A refinement: with `IS-INTEGRAL-DOMAIN(q)` in context the same `fact` lands only the
  implication `is-commutative-ring(q) implies ...` and says nothing (tpu2, `(d3)`). The user
  must know to cite `integral-domain-is-commutative-ring` first. After that the `fact` detaches.
* Through a view, with the companion installed: `(fact 'rando-square-normed-field-as-commutative-ring 'k 'x 'x)`
  with `IS-NORMED-FIELD(k)` lands the statement in `k`'s accessors, and `ass` closes
  (`tpu-d1`, `proven modulo 0`).
* Through a view, without a companion: `(fact 'rando-square '(NORMED-FIELD-AS-COMMUTATIVE-RING k) 'x 'x)`
  lands `(mul(normed-field-as-commutative-ring(k)))(...)`. Each accessor must then be
  rewritten with `mac-h 'normed-field-ring-view-add` / `-mul`. Only this view has such
  generic read-offs, and it has them because someone proved them by hand.

The companion exists only if somebody installed it. `def-functor` specializes the target
theorems that exist when the view is DECLARED (structures.scm:1232). views.scm loads before
ring-power.scm, so at load time `NORMED-FIELD-AS-COMMUTATIVE-RING` has 3 companions, while
the table now holds 64 commutative-ring theorems of the matching shape (tpu4 census). The
comparable ratios for other views: RINGOID-AS-RING 20 of 224 ring theorems,
COMMUTATIVE-RING-MULTIPLICATIVE-CM 1 of 33. A theorem proved later is available through a
view only after `(view-as-auto-specialize! 'VIEW 'thm)`, which cancellation.scm:186
does for one theorem and documents as a trap.

### (e) At a substructure or a quotient

Neither is a view. `SUBSPACE-MS(s, a)` (metric-subspace.scm:58) and
`RINGOID-QUOTIENT-RING(r)` (ringoid.scm:104) are `def-functoid` constructions, each with a
PROVEN typing theorem (`subspace-is-metric-space`, `ringoid-quotient-is-ring`) and read-off
theorems (`subspace-pts`, `subspace-dist`; the `rq-*` family, stamped definitional).
`transport!` refuses both (`transport: not a declared instance (ringoid-quotient-ring q)`),
and `lookup-view-as` returns `#f`. The in-proof route works:

    (fact 'subspace-is-metric-space 's 'a)
    (dk-have! '(IN u (PTS (SUBSPACE-MS s a))) (lambda () (mac 'subspace-pts) (ass)))   ; and v
    (fact 'metric-sym '(SUBSPACE-MS s a) 'u 'v)
        -> (dist(subspace-ms(s, a)))(u, v) = (dist(subspace-ms(s, a)))(v, u)
    (mac-h 'subspace-dist E0)
        -> (dist(s))(u, v) = (dist(s))(v, u)                     ; ass closes (tpu3, (e4))

For the quotient, `(fact 'ring-carrier-closed-mul '(RINGOID-QUOTIENT-RING q))` after
`ringoid-quotient-is-ring` lands `(mul(ringoid-quotient-ring(q)))(a, b) in carr(ringoid-quotient-ring(q))`.
The `rq-*` read-offs take it to DESCEND2 / CLASS terms. There is no further "surface" for a
quotient, and that is correct.

---------------------------------------------------------------------------------------------

## 2. The table of what exists

| Mechanism | Accepts | Produces | Limits | Surface | Documentation |
|---|---|---|---|---|---|
| `fact THM TERM ...` (with `inst+`, `dk-fact!`) | any theorem, any terms, including a view or constructor term | the instance as HYPOTHESES (whole instantiation chain) | a guard left undischarged is landed silently as an implication; the result speaks the source's accessor vocabulary | in-proof | TACTICS.md (as instantiation, not as transport) |
| `transport! GENERIC INSTANCE WITNESS [NAME]` (transport.scm:175) | a theorem `(FORALL s (IMPLIES (IS-X s) BODY))` with `s` OUTERMOST; a `declare-instance!` SYMBOL; a witness theorem | a NEW theorem `GENERIC@instance`, proven, in the surface vocabulary | outermost-binder defect (F1); nested operations fail (F2); no witness/guard check (F3); no terms, no views (F4); no derived-operator bridges (F5); opens its own proof (cannot run mid-proof) | installer, proof file or REPL | file header only; not in TACTICS.md, not in the manual |
| `view-as-auto-specialize! VIEW [THM]` (structures.scm:1122) | theorems `(FORALL s (IMPLIES (IS-TGT s) P))`, bare guard, `s` outermost (`generic-for-struct?`, :1006) | NEW axioms `THM-view`, stamped `definitional`, source recorded for the bill | no subtype guard (IS-COMMUTATIVE-RING theorems invisible to an INTEGRAL-DOMAIN view); no composition of views; derived operators keep the view term; runs automatically only at `def-functor` time | installer | ch-defs.tex:1114-1160 (as part of def-functor) |
| `def-functor NAME SRC COMPS TGT SLOTS` (structures.scm:1191) | a forgetful view between shape or refinement structures | functoid, typing axiom (`definitional`), companions of the target theorems existing at that moment | read-off theorems NOT generated (normed-field-ring-view.scm exists because of that); snapshot at declaration time | structure-library file | ch-defs.tex:1067 ff. |
| `specialize-structure INST STRUCT ISTHM` / `spec` (structures.scm:1280, interactive.scm:5621) | as `generic-for-struct?` | NEW theorems `THM-inst`, accessor vocabulary, installed WITHOUT proof, provenance `asserted`, no warrant | F7; no surface; outermost-only | installer, REPL | ch-defs.tex:716-800, the only door the manual teaches |
| `declare-instance!` (structures.scm:438) | a constant and its tuple | tuple equation, per-slot value theorems `INST@ACC` (`==`, definitional) | the values are lambdas; the surface needs beta with typed arguments | structure-library file | ch-defs.tex (around :700) |
| `slot ACC` / `slot-h ACC F` (interactive.scm:1525, :1556) | an accessor applied to an instance (goal / one hypothesis) | the slot value | `slot-h` errors on two instances of one accessor in one hypothesis; a view term is not an instance, so `slot` on `ADD(VIEW(RR-NORMED-FIELD))` needs `mac 'VIEW` and `nth-r` first | in-proof | TACTICS.md |
| view read-offs `normed-field-ring-view-*`, `rr-scalar-ring-*` | the one view NORMED-FIELD-AS-COMMUTATIVE-RING | `==` theorems, proven modulo 0 | hand-written, one view only; every other view has none | cite by `mac` / `mac-h` | normed-field-ring-view.scm header |
| surface bridges `lam-slot-{add,mul,neg}-apply` (lambda-slot-apply.scm) | a slot lambda applied to typed arguments | the surface operator | guarded: each argument must be typed in the domain first | `mac` / `mac-h`, used by transport! | transport.scm:41-55 |
| `crs` | commutative-ring identities in a structure's ADD/MUL/NEG once IS-COMMUTATIVE-RING of it is in context, and number-domain identities | closes the goal | not a transport; it re-derives. It is often the right tool for a concrete identity | in-proof | TACTICS.md |
| inclusion theorems (`integral-domain-is-commutative-ring`, ...) and view typing axioms | one structure predicate | another | never cited automatically by `fact` | cite by `fact` | STRUCTURES.md |

---------------------------------------------------------------------------------------------

## 3. Findings

**F1. `transport!` substitutes the OUTERMOST binder without checking that it is the
structure binder (transport.scm:180-185), and blames the instance.** Reproduction:
`(transport! 'ring-power-of-one 'ZZ-RING 'zz-is-commutative-ring)` and the same with
`'binomial-theorem` both give `transport!: nothing to normalize -- is INSTANCE declared?
zz-ring`. ZZ-RING is declared. The theorems read `forall([n in nn, r], ...)`, which is the
shape `ni` requires, so every induction-proved structure law has it. The same limit is in
`generic-for-struct?` (structures.scm:1006), which serves `view-as-auto-specialize!` and
`specialize-structure`. Census over the band (tpu4; the counts include `-rev` twins): among
theorems with an `(IS-X v)` guard on a prefix variable, the shape test misses 29 of 93 for
IS-COMMUTATIVE-RING, 204 of 428 for IS-RING, 36 of 167 for IS-METRIC-SPACE, 65 of 206 for
IS-NORMED-VECTOR-SPACE and 52 of 68 for IS-MONOID. Named misses include `binomial-theorem`,
`ring-power-of-one`, `ring-power-mult-ind`, `det-alternating-rows`, `sum-ag-permutation-invariance`
and `metric-chain-bound`. Some misses have the guard inside an `AND` antecedent, a second
form of the same limit (memory note of 2026-05-23).

**F2. `transport!` fails on any statement with nested operation applications.**
Reproduction: `(transport! 'rando-square 'ZZ-RING 'zz-is-commutative-ring)`, output in 1(a).
Mechanism: `tr--surface-assumption!` (transport.scm:121) PREDICTS each rewrite with the pure
rewriter (`tr--rewrite-1`, `surface-normalize`, :90) and then asks the kernel to perform it
with `mac-h`. The pure rewrite of the guarded `lam-slot-add-apply` rewrote every occurrence.
The kernel rewrote the occurrences whose argument typings it could establish and spawned
the rest as side conditions ("2 side-condition(s) spawned"). The loop then continues from
its PREDICTED formula, which is not in context ("lam-slot-mul-apply does not occur in the
cited assumption"), and ends with an open main leaf and two open typing leaves. The kernel
behaves correctly. The loop's prediction is what goes wrong. The same statement goes
through by hand once the six compound subterms are typed with `in-rr` (1(a), in-proof
route). The fix therefore has two parts: read the kernel's ACTUAL result off the context
diff, and type the arguments before beta. Every existing use (cancellation.scm:190-191,
nn-integral.scm:59) transports a flat body, which is why the defect went unseen.

**F3. `transport!` does not check the witness against the guard.** Reproductions:
`(transport! 'ring-power-type 'ZZ-RING 'zz-is-ring 'rpt-bad)`, where the guard is
IS-COMMUTATIVE-RING and the witness proves IS-RING, fails with `goal not in context ... did
NOT close ... unfinished`. `(transport! 'rando-square 'RR-NORMED-FIELD 'rr-is-normed-field)`
instantiates a 6-slot predicate at a 7-tuple and fails the same way. The only error is the
generic "did NOT close". The loop also does not stop at the first failed rewrite, and the
failure prints the open goal ten times over (visible in the logs).

**F4. `transport!` accepts only a `declare-instance!` symbol.** A view term
(`NORMED-FIELD-AS-COMMUTATIVE-RING(RR-NORMED-FIELD)`), a constructor term
(`RINGOID-QUOTIENT-RING(q)`, `SUBSPACE-MS(s, a)`) or a bound variable gives
`transport: not a declared instance ...` (transport.scm:113). Its own header says so
(transport.scm:31-34). The workaround composes two installers, `view-as-auto-specialize!`
and then `transport!` at the underlying instance (1(b)). It is correct, but a user has to
know it, it installs two theorems, and it inherits F1 and F2.

**F5. No bridge from derived structure operators to the surface.** No theorem relates
`ring-power(R, x, n)` to `x ^ n` at any numeric instance or view (probe filter over the
full table: empty). The two recursions even differ in side: `ring-power-succ` multiplies on
the RIGHT, `power-succ` (number-systems.scm:854) on the LEFT. The only SUM bridge is
`series-partial-sum-is-ring-sum` (bernstein-basis.scm, RR view only). None exists for
`sum(zz-ring, ...)`, `sum(qq-ring, ...)` or CC, and none evaluates `comb-kk` at literals. So
the binomial theorem at ZZ-RING lands
`ring-power(zz-ring, x + y, 2) = sum(zz-ring, comb-kk(zz-ring, x, y, 2), succ(2))`, and no
chain of existing commands turns that into the surface goal. Transport stops at the
accessor slots and says nothing about the operators DEFINED from them, which is where
algebraic theorems live.

**F6. View companions are a load-order snapshot.** `def-functor` specializes when the view is
declared (structures.scm:1232). views.scm loads before ring-power.scm, binomial.scm and
almost every proof, so companions are missing for most target theorems: 3 of 64 for
NORMED-FIELD-AS-COMMUTATIVE-RING, 20 of 224 for RINGOID-AS-RING, 1 of 33 for
COMMUTATIVE-RING-MULTIPLICATIVE-CM (tpu4; approximate, counted by name). Recovering one is a
by-hand `(view-as-auto-specialize! 'VIEW 'thm)`, and cancellation.scm:175-186 documents the
trap. There is no composition of views (FIELD -> INTEGRAL-DOMAIN -> COMMUTATIVE-RING is not
followed; `(view-as-auto-specialize! 'FIELD-AS-INTEGRAL-DOMAIN 'rando-square)` specializes 0),
and no subtype matching on the guard.

**F7. `specialize-structure`, the door the manual teaches, installs unproven assertions.** It
calls `install-theorem!` (structures.scm:1301) with the default provenance `asserted`
(macetes.scm:1691). Measured: `ring-power-succ-zz-ring` has provenance `asserted` and
`debt-of` equal to itself, i.e. an unwarranted leaf (trust: none), while its source
`ring-power-succ` bills nothing. The manual (ch-defs.tex:762) says "No new axioms are
introduced". No bill is laundered, since the result is billed as an assertion, but a
proven, modulo-0 fact is turned into debt, and the output is in the accessor vocabulary.
The library never calls it; the suite does (test-suite.scm:2942). Recommendation: route it
through the proposal's core or retire it, and correct the manual either way.

**F8. The def-functor typing axiom is a `definitional` stamp of a real claim.**
`normed-field-as-commutative-ring-is-commutative-ring : forall([r], is-normed-field(r)
implies is-commutative-ring(normed-field-as-commutative-ring(r)))` has provenance
`definitional` (tpu1). This is a mathematical statement (the field laws imply the ring laws
of the projection), and every view companion inherits its zero cost. It is true, and this
note alleges no unsoundness. It is the kind of stamp the library-build policy asks to be
recorded or proved (CLAUDE.md, "A stamp must record its claim"). `def-constructed-functor`
already OWES its typing theorem (structures.scm:1731, `functor-obligations`); `def-functor`
does not.

**F9. No documentation at the point of use.** `transport!` and `view-as-auto-specialize!`
appear in neither TACTICS.md nor the manual. The manual teaches `specialize-structure`
(F7). The worked examples are scattered: cancellation.scm:175-191 (view companion plus
transport), nn-integral.scm:59, bernstein-basis.scm (RR by hand),
normed-field-ring-view.scm (read-offs). Nothing tells a user which route fits which target.

**F10. Silent partial success on the in-proof route.** `fact` of a theorem whose guard is a
refinement of what is in context lands the implication and says nothing (1(d)); the same
behaviour CLAUDE.md records for conjunctive antecedents. `transport!` called twice installs
twice with only an overwrite warning (tpu3, `(a-name)`).

---------------------------------------------------------------------------------------------

## 4. Proposal: one command, `at` (working name)

**What the user types.** In a proof:

    (at 'binomial-theorem 'ZZ-RING)                                      ; instance
    (at 'rando-square '(NORMED-FIELD-AS-COMMUTATIVE-RING RR-NORMED-FIELD)) ; view term
    (at 'rando-square 'k)                                                ; bound variable, any IS-Y(k) in context
    (at 'metric-sym '(SUBSPACE-MS s a))                                  ; constructor with read-offs

Each call LANDS one hypothesis: the theorem, with its structure binder instantiated at the
target, every other binder kept in place, every accessor, view and derived operator
rewritten to the target's surface vocabulary as far as proven read-offs and bridges reach.
It installs nothing. Outside a proof, `(at! 'THM TARGET [NAME])` does the same and installs
the result as a named theorem; `transport!` becomes that. For example,
`(at 'binomial-theorem 'ZZ-RING)` would land
`forall([n in nn, x in zz, y in zz], (x + y) ^ n = <surface sum>(...))`, once the F5 bridges exist.

**The algorithm.** It is composed from parts that exist.

1. Find the structure binder ANYWHERE in the leading quantifier prefix by its guard,
   including inside an `AND` antecedent (fixes F1).
2. Find the witness: the target's IS-X theorem, or a chain through inclusion theorems and
   view typing axioms, depth-limited; report the chain; error naming what was searched
   (fixes F3, F10).
3. Build the specialized statement, prove it on a lane with `dk-peel!` / `fact` / `ass`, and
   land it. This is `transport!`'s proof shape, with the witness chain in front.
4. Normalize by rewriting the landed hypothesis with the kernel. Read each step's result
   off the context diff rather than predicting it (fixes F2). Apply, in order, instance slot
   theorems (`slot-h`), view read-offs, lambda slot bridges preceded by `in-rr` typings of
   the arguments, `dk-lam-b-h!`, then the registered derived-operator bridges.
5. Stop at a fixpoint. If an accessor or a lambda survives, say which, rather than fail.

**Decisions for the user, each with a recommendation.**

* D1. One command, landing in the proof, with `at!` as the installing variant. *Recommend
  yes; hypotheses do not grow the theorem table, and `transport!` / `spec` reduce to `at!`.*
* D2. Where the structure binder may sit. *Recommend: anywhere in the leading prefix, the
  other binders kept in their order.*
* D3. Witness: found automatically, or always named. *Recommend: automatic, with an optional
  explicit witness, and an error that lists the chain searched.*
* D4. Guard subsumption along proven inclusions and view typing axioms. *Recommend yes,
  depth-limited, the chain printed.*
* D5. Views compose at the TERM level (a view applied to an instance is just a term whose
  read-offs compose), with no composite views declared. *Recommend yes; it removes the
  need for companions altogether.*
* D6. `def-functor` generates and PROVES the generic slot read-offs
  (`nfrv-prove-generic!` generalised, modulo 0) for every view. *Recommend yes; 19 views
  times their slot counts, all mechanical.*
* D7. Derived-operator bridges (F5) as a registry of PROVEN theorems:
  `ring-power(R, x, n) = x ^ n` at ZZ-RING, QQ-RING, and the RR and CC views; the ring SUM
  against a surface finite sum at the same four. *Recommend yes, with the bridges proven
  once per instance, or once generically over the numeric instances. This is the part that
  makes the binomial theorem usable.*
* D8. Companion auto-specialization at `def-functor` time: keep or drop. *Recommend keep
  the existing companions (cited by name), stop generating new ones, and let `at` compute
  on demand.*
* D9. `specialize-structure` / `spec`. *Recommend rewrite on `at!` (proven, billed through
  the source) or retire; fix ch-defs.tex:716-800 either way.*
* D10. The def-functor typing axiom (F8). *Recommend turning it into an OWED theorem, as
  `def-constructed-functor` does; a separate decision, not needed for `at`.*

**Reuse.** `generic-for-struct?` (generalised), `tr--deepest`, `subst-free`, `slot-h` and
`slot--instance-macetes`, `view-as-reduce-accessors`, `*view-as-table*`,
`*structure-instances*`, `in-rr`, `dk-lam-b-h!`, `dk-have!`, and the ledger's existing
treatment of a proven lemma's bill. Nothing new is trusted: every step is `fact`, `mac-h`,
beta or `ass`.

**Cost.** Roughly 300 to 400 lines in transport.scm plus a TACTICS.md entry and suite
controls (accepted and refused per target kind), about a day of one agent. The generated
view read-offs (D6) are another half day. The F5 bridges are one induction per instance
for `ring-power` (the left/right mismatch is one `crs`) and one per instance for the sum:
four to eight short proofs. One cold load for verification. The manual section is a
separate documentation task.

---------------------------------------------------------------------------------------------

## Summary

The three worst obstacles a user meets today:

1. **The installer that exists breaks on real statements.** `transport!` fails on any
   nested identity (F2). It misreads every induction-shaped law as having no structure to
   transport, and blames the instance (F1). When the witness does not match the guard, its
   only message is "did NOT close" (F3).
2. **Views and constructed structures are not targets.** Only a declared instance symbol is
   accepted (F4). View companions exist only for the theorems that predate the view (F6),
   and nothing follows inclusions. Every use through a view is a hand-built chain of about
   fifteen commands (`fact`, `slot-h` / `mac-h` read-offs, six `in-rr` typings, beta).
3. **Transport stops at the slots.** Nothing takes `ring-power` or the ring `SUM` to `^` or
   a surface sum (F5), so the binomial theorem cannot be used at ZZ, RR or CC even by hand.

The one thing that would fix most of them is a single command, `at THM TARGET` (section 4).
It finds the structure binder anywhere in the prefix, finds the witness through instances,
inclusions and views, and normalizes with the kernel's actual results. It needs one addition
to the library: a registry of proven derived-operator bridges (`ring-power = ^`, ring
`SUM` = surface sum) for the four numeric instances.
