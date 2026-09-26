<!-- VERBATIM copy of a section of CLAUDE.md as it stood on 2026-09-18, moved here when
CLAUDE.md was trimmed to its operational rules.  Nothing was edited.  The dated findings,
measurements and case histories behind each rule in CLAUDE.md are in this text. -->

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
* **`prop` can DECLINE a one-step contradiction in a deep context** (2026-09-17,
  finsum-single-support): with ~20 assumptions its atom cap (12, then radius narrowing)
  drops the pair `P` / `NOT P` and it prints "does not follow propositionally" with an
  EMPTY countermodel. That message means "I did not look at the right atoms", not "this
  is not propositional". For a contradiction already in context use `(ai <the NOT>)`
  directly; where propositional reasoning is really needed, `dk-only!` the context down
  to the relevant formulas first and `prop` fires.
* **`if-true` does not rewrite the goal.** It opens the condition as one leaf and hands
  the other leaf the equation `IF(p,a,b) = a` as an ASSUMPTION; the goal still holds the
  `IF`, and needs an explicit `subst` of that equation. A driver written as if `if-true`
  had rewritten dies steps later with `reflexivity: goal is not (= a a)`.
* **Two things the tree does NOT have** (same file): a RESTRICTION of a set-function to a
  subset (no `RESTRICT`, no "f in FUN(S,Y) => f|X in FUN(X,Y)"), and the converse of
  `card-insert` (`CARD X in NN` from `CARD(X u {k}) in NN`; the only lemma of that shape
  is the asserted `card-subset-nn`). A finite-sum argument that wants to peel one index
  off a SET therefore goes through the enumeration instead (induct on the fold length,
  transfer along `FIN-ENUM`), as `sum-ag-single-ind` does.
* **Rake batch 1 findings (2026-09-17, 27 `proof`-warranted supports proven by four
  agents in one afternoon; every warrant was an accurate plan nobody had run):**
  `dk-apply!` / `dk-fact!` inside a `dk-landed-1` thunk land the whole instantiation chain
  and error, same as `inst*!`/`inst+`/`fact`. An alpha-variant pair of leaves (the support
  spells a binder `y_`, the functoid body `x_`) closes by `ass`, which is alpha-aware, and
  NOT by `prop`, which is not. `ineq` certifies an atom only from a STANDALONE `(IN t RR)`:
  with `POS-RR r` or the typing inside an unsplit conjunction the atom is uncertified and the
  message blames the goal (cite `rr-pos-rr-in-rr`). A shape-based premise finder ("every
  `< <= =`-headed assumption") hands `ineq` a SET equation like `U = BALL(s,c,r)` and
  poisons the call; name premises by formula. A `proof`-warranted induction stated with the
  induction variable NOT outermost (`strictly-mono-ge-id`: `phi` first) needs a companion
  statement with the NN binder outermost plus one `fact`, not just a driver. Lemmas the
  tree still lacks, each built inline twice: `complement-in-involutive`
  (`PTS \ (PTS \ X) = X` for `X subset PTS`, beside `complement-in-subset`) and
  ball-monotone-in-radius (`BALL(s,y,m) subset BALL(s,y,r)` for `m <= r`, beside
  `ball-is-open`). And `continuous-implies-open-preimage` (metric-open-sets.scm, `informal`)
  is now the ONLY support left in that file; its argument is the mirror of
  `open-preimage-implies-continuous` in rake-open-sets.scm, so it is one assignment away.
* **A `same-shape-as` structure has NO citable unfold** (2026-09-17, rake batch F).
  `VECTOR-SPACE` is declared `same-shape-as MODULE` plus a law, which installs the MACETE
  `is-vector-space` and no theorem, so `mac-h 'IS-VECTOR-SPACE` warns `unknown
  theorem/macete` and no-ops, while `mac-h 'IS-RING` and `mac-h 'IS-NORMED-VECTOR-SPACE`
  work. It is the def-functoid trap one storey up, in a predicate. The one-line cure is the
  same: `is-vector-space-unfold` (theorem-library/rake-setoid.scm, `(di) (mac ...) (qrfl)`),
  and every other `same-shape-as` structure has the same hole until its unfold is proven.
  Also from that batch: DESCEND's well-definedness on a quotient is exactly `iota-d`'s two
  obligations (existence: `a in [a]` by REL reflexivity through `sep-mi`; uniqueness:
  RESPECTS), so `quotient-rep` / `class-self` / `descend-computes` were not needed; and
  `forall-guarded` emits all binders first and then the implication chain, so a hand
  transcription of a RESPECTS2-style body is a DIFFERENT formula (copy the constructor
  call, never the reading).
* **Rake batch E (matrix typing, 2026-09-17): three cheap retirements it exposed, and one
  duplicate.** `matrix-sethood` (matrix.scm) is an UNWARRANTED axiom (`trust: none` to any
  citer) and is provable in four lines -- `MATRIX(X)` is a subclass of the set
  `TUPLES(TUPLES X)`, so `tuples-sethood` twice plus `subclass-of-set-is-set`; it is cited
  nowhere. `pred-in-interval` (order-lemmas.scm, `well-known`) is provable (inline as
  `rkm-pred-in-interval!`, ~45 lines). The tree has `nn-succ-mono` and NO converse
  (`succ a <= succ b => a <= b`), re-derived by a three-lemma contradiction every time; one
  line in nn-order-ord.scm. `mpow-type` (monoid-power.scm, `informal`) is the WHOLE bill of
  `det-in-carrier` and, one view up, of `ring-power-type`: an NN induction nobody ran; and
  no `mpow-type-ring-multiplicative-monoid` view companion exists, so the read-off goes
  through the new `rmm-carr` (rake-mat-typing.scm; belongs in ag-view-read-offs.scm). The
  IF-tower resolver (`mtb-if-branch!` / `mtb-close-if!` in mat-typing-bundle.scm) is now
  duplicated as `rkm-if-branch!` / `rkm-close-if!`: it belongs in driver-kit.scm. And the
  entrywise typings (MATADD/MATSCALE/MATNEG) are NOT one-liners after the SIZE/MAT repair:
  they tabulate at `NTH(2, SIZE P)`, which is not `n` at zero rows, so each goes through
  `mat-colcount-transfer` with its guard closed by `prop` -- that is what makes them true
  at m = 0 rather than merely unchecked there.
* **Rake batch G (finsum / NN typing, 2026-09-17).** THREE warrants ("induction on |S| via
  finsum-insert": submodule-finsum-closed, finsum-all-id, finsum-single-support) named a
  finite-SET induction the tree does not have and a restriction it cannot express; the
  fold-length induction plus FIN-ENUM transfer does the job every time, and the general
  lemma `finsum-in-subset` (rake-finsum-typing.scm: a finite sum stays in any
  IDEN-containing, OPR-closed subset of an abelian group) should retire the next such leaf
  for free. `funcomp-succ-type` was FALSE with `q` untyped (q = 3/2: INTERVAL(1, succ q)
  can be empty while INTERVAL(1, q) = {1}) and is installed guarded `(IN q NN)`.
  `choose-in-nn` bottoms out in the asserted `card-power-nn` (finiteness of the powerset)
  and stays. `monoid-identity-in` / `monoid-carrier-closed-opr` (monoid.scm) are UNWARRANTED
  axioms (`trust: none` to any citer) -- the batch proved COMM-MONOID versions instead;
  retiring the monoid ones needs the `view-as-auto-specialize!` care (their view companions
  go with them). `mpow-type` is redundant at a commutative monoid (`mpow-comm-monoid-type-ind`
  is its induction, run). `def-functor` views still need a hand read-off per slot
  (`crmcm-carr` here, `rmm-carr` in batch E, six in ag-view-read-offs.scm): a shared view
  read-off driver would pay for itself. series-block-abs.scm's header still says `nn-le-gap`
  bills `nn-not-le-zero-pos`; that leaf is proven and the bill is `modulo 0`.
* **Rake batch L (analysis and sets, 2026-09-17).** `fun-domain-in-set` (`f in FUN(A,B) =>
  A in SET`; rake-analysis2.scm) did not exist: a member of a class is a set, `fun-no-junk`
  says a function IS its graph, and the first-coordinate image of a set is a set by
  replacement -- so any `lam-t` sethood leaf over the domain of an already-typed function
  closes by citation now. `centre-set-contains-choice` was UNDERDETERMINED (CHOICE of an
  empty class; F = {EMPTY-SET}) and carries `forsome c. c in CENTRES(s,U,r)` since. Three
  leaves stay asserted with their routes written in that file's report: `card-power-nn`
  is `finite-set-induction` (primitive) with `C = {x | CARD(POWER x) in NN}`, the step
  needing only the INCLUSION `POWER(S u {x}) subset POWER S u IMAGE(T |-> T u {x}, POWER S)`
  plus `card-image-finite` and `card-union-nn` (both proven) -- a 150-250 line driver of
  card-subset-nn.scm's shape; `subsequence-capture` is `dc-on-nn-pred` at `X := S`,
  `nxt(k,u) = {y in S | u < y}` (totality is the PROVEN `inf-subset-nn-unbounded`) plus one
  NN induction, so it chains to `dc-on-nn`; and `dc-on-nn-pred` cannot be derived from
  `dc-on-nn` without a SEP over triples the tree cannot form (CARTESIAN is binary, no
  TUPLES-membership lemma for a literal LIST, no tuple-extensionality read-off) -- honest
  debt, and its warrant says exactly that.
* **`succ` off NN is an uninterpreted term, and statements that forget it are FALSE**
  (rake batch K, 2026-09-17). Every axiom and theorem about `succ` is NN-guarded, so a
  statement that puts `succ t` in an INTERVAL bound or an index without typing `t` asserts
  something a model may interpret freely: `succ-in-interval` (q = 3/2, succ(3/2) := 0) and
  `pred-in-interval` (p = 1/2, succ(1/2) := 100) were both refutable and are now guarded on
  the bound; `comb-kk-laws`' note on `bt-succ-minus-1` over ZZ is the same species. Worth a
  SWEEP of the remaining PSS for `succ` applied to an untyped variable; these two were found
  by trying to prove them, not by an audit. Also from that batch: the "`succ a <= succ b =>
  a <= b`" helper the earlier batches wanted already existed as the asserted
  `nn-succ-le-cancel` (now proven, rake-intervals.scm); `succ-nn-minus-1` (order-lemmas.scm)
  is one line from it; the two IDENTMAT identity laws needed NO guard (the middle dimension
  is one of the outer ones, so the product guard is propositionally trivial); and
  `elem-entry-readoffs` sits one slot above `mat-ring-proof`, an empty window for anything
  that wants both -- it can move anywhere in [235, 332).
* **Rake batch J (the finsum laws, 2026-09-17). `finsum-congruence` was FALSE as stated**:
  `f`, `g` untyped (deliberately, 2026-08-02, so back-peeled families fit) but the
  conclusion a strict `=`, which is definedness -- a constant map with a value outside
  `CARR(ag)` satisfies the hypothesis and the FINSUM does not denote; the literal statement
  drives down to `t = t` and `rfl` refuses. It is now stated with `==` (rake-finsum-laws.scm;
  `subst` takes `==` as `=`, and the 52 citers `fact` then rewrite), with the typed `=`
  form beside it as `finsum-congruence-guarded`. **`enum-fam-value`** (`(ENUM-FAM ag u phi
  n)(i) == u(phi i)` on the segment, `u`, `phi` VARIABLES so `lam-b` has one redex) is the
  brick the whole finsum arc had been re-doing inline; with it every law is a pointwise
  relation between two ENUM-FAMs plus the fold-length induction. `sum-ag-type-ptwise` is the
  matching typing (sum-ag-type wants `f in FUN(NN, ...)`, which a sliced family never is).
  `finsum-embed` stays asserted: `finite-set-induction` DOES exist (class form), and the
  restriction blocker is now dissolvable (`VNB-LAMBDA z u (f z)` typed by `lam-t`, transported
  by the untyped `finsum-congruence`), but the surgery `S = (S \ {x}) u {x}` still wants
  `difference-membership` and a converse of `card-insert`. Also new and previously missing:
  `abelian-group-opr-interchange` (`(a.b).(c.d) = (a.c).(b.d)`; there is no abelian-group
  normalizer, `crs` is rings only), `module-act-zero-vec` (`r . 0_V = 0_V`, the twin of
  `module-zero-act`), `interval-succ-insert`; `ord-segment-insert` (finsum-additive.scm, still
  asserted) is the ORD-SEGMENT twin of the last and the same driver closes it.
* **`F(M, u)` for a ONE-parameter functoid `F` is `F` applied to the pair `[M, u]`, not
  `F(M)(u)`** (rake batch O, 2026-09-17). `apply-tupling-2` makes an n-ary application an
  application to the TUPLE, so the support `embed-isometry` wrote `(EMBED M u)`, which is
  EMBED at `[M,u]` -- a function on `PTS([M,u])`, not a point of the completion -- and `mac
  'EMBED` declined on it. The statement is now `((EMBED M) u)`, the term `embed-in-fun`
  types, and is proven (rake-setoid2.scm). Any support that applies a def-functoid to MORE
  arguments than its parameter list has is the same misspelling; worth a sweep. Also from
  that batch: `rko2-quad` (the quadrilateral inequality `|d(a,b) - d(c,e)| <= d(a,c) +
  d(b,e)`) and `rko2-dist-converges` (the metric is continuous along sequences) did not exist
  and are what every representative-independence argument about a completion needs;
  `dk-split-all!` with NO argument splits every conjunction in context, including a `have!`
  just landed and the theorem's own AND antecedent -- pass it the landing.
* **UNIVERSAL INSTANTIATION OWES DEFINEDNESS since 2026-09-18** (the LUTINS rule; the
  entry below records how the hole was found). `forall-elim` posts the side sequent `t = t`
  unless the CERTIFICATE (`pi--defined?`, primitive-inferences.scm) accepts `t`: a variable; a
  ground number; a term the context types or equates; a term occurring OUTSIDE binders in a
  true `IN` / `=` / `<=` / `<` hypothesis, in any position, the operator included
  (strictness); a class term on defined arguments (SEP, COMP, FUN, TUPLES, POWER, IMAGE,
  INTERVAL, ORD-SEGMENT, BIJECTION, MATRIX, ... and any functoid whose body is one);
  `VNB-LAMBDA`/SEP/BIG-UNION over a certified domain; `NTH k` of a LIST; `LENGTH` of a term
  typed in a tuples class; arithmetic (`+ - * min max abs succ ^`) on number-typed arguments;
  an accessor of a structure the context has (`IS-RING s` or `s in RING`, through the
  definitional parent chain); an applied structure operation on arguments typed in its
  declared domain; `f(a)` with `f in FUN(D,_)` and `a in D`; a `def-predicate` hypothesis
  whose defining body's conjuncts certify (`IS-ANTIDERIVABLE(s(k),a,b)` types `s(k)`, to
  depth 3, existentials stripped). NEVER: CHOICE, IOTA, an untyped application, ENTRY without
  range typing, the IOTA-bodied matrix constructors, FINSUM. `rfl` uses the same test. The
  policy and the measurements are docs/definedness-instantiation-2026-09-18.md.
  **What the leaf costs a driver:** nothing when the term's typing is in context BEFORE the
  instantiation, or one citation away for a matrix constructor, FINSUM, LINCOMB, ENTRY or
  arithmetic -- `dk-discharge-owed!` (driver-kit.scm), called at the command boundary on the
  leaves the kernel TAGGED (`*pi-owed-nodes*`), cites the typing and closes by `rfl`,
  recording its steps. Anything else stays open and `qed` reports it. Under
  `VNB_KEEP_GOING` a proof that ends with open leaves installs as an ASSERTED HOLE and prints
  its goals (`*vnb-qed-holes*`), so one load lists every root. Three traps the repair wave
  hit: an owed leaf has the SAME context as its parent, so a "focus the leaf whose context
  holds X" helper picks the owed leaf first and the driver dies branches later with `cdr of
  #f`; `ai` / `dk-split!` / `dk-skolem!` REPLACE the formula they open, so exposing a typing
  conjunct as a certificate must be a `have!` lane; and `every` in this tree is 2-ary
  (deduction-graphs.scm) -- a two-list call raises, and an error inside a kernel rule aborts
  the whole `fact`. The audit hook stays: `VNB_DEF_AUDIT=1` prints the owed count by head at
  the end of a load and dumps the terms to /home/ubuntu/def-audit-terms.txt.
  **Two copilot lanes had to learn the rule too:** `what-now`'s typing lane now emits the
  forward typing BEFORE the backchain (suggest.scm; the closure law's `bc*` instantiates at
  the term, which owes definedness until the fact has typed it) and drops the owed leaf from
  the probe's subgoals; and `ineq-supply` no longer cites typings at atoms that sit UNDER a
  binder of the formula they came from (`f(n_)` inside the lambda of a partial sum: the
  variable is out of scope at the node, so the citation owed a leaf nothing could close, and
  `supply` refused the whole goal). The two suite `ni` proofs (`prod-ord-type`, `sum-type`)
  now rewrite along the recursion equation instead of instantiating at the recursion term.
  The hook is TRANSACTIONAL: an attempt that does not close the leaf is rolled back (graph,
  focus, script, trace, undo stack), so a failed closer leaves no half-cut leaf behind.
* **THE KERNEL PROVES THAT EVERY TERM DENOTES** (rake batch P, 2026-09-17; probe
  `scratchpad/rkp/defprobe.scm`). `term-self-defined?` (primitive-inferences.scm) grants every
  VARIABLE definedness, so `(FORALL a (= a a))` is provable `modulo 0` by `(di) (rfl)`; and
  `pi-instantiate!` substitutes an arbitrary TERM into a universal with no definedness side
  condition, so that theorem instantiated at `recip(0)` closes `recip(0) = recip(0)`. That
  collapses the partial-equality reading `(= t t)` is supposed to carry. It is a foundational
  decision, the user's, of the `iota-in-elim` kind: either instantiation owes a definedness
  obligation for the instantiating term, or `rfl` must not certify a bare variable. Until it
  is made, `mul-defined-factors` (order-lemmas.scm) is "provable" for the wrong reason and
  `recip-defined-nonzero` is unprovable (nothing relates recip's definedness to its argument;
  no strictness axiom, no elimination for definedness); both stay asserted. Also from that
  batch: `card-zero-is-empty` (`CARD A = 0 => A = EMPTY-SET`) did not exist (rake-
  combinatorics.scm has it, by finite-set-induction whose step never uses the IH);
  `card-power-nn` needs no disjointness (`card-union-nn` asks none); `fact` of a membership
  IFF lands BOTH the instance and the universal and `dk-deepest` cannot separate them;
  `pairing-membership`'s guard sits BETWEEN its binders, so `fact` stops at the detached
  `forall x` and the element must come from `inst*!`; `crs` does not reach a structure's
  `(MUL R)`, so ring regrouping is hand-chained (`ring-mul-interchange`); `choose-succ`
  (Pascal) is a ~150-line assignment on the CHOOSE-SET split plus `card-image-injection`.
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
* **`subst` rewrites in OPERATOR position since 2026-09-16.** Until then the Leibniz walk
  (`replace-term`, primitive-inferences.scm) visited argument positions only. Substituting
  for a VARIABLE was never affected, because it goes through `subst-free`, which walks
  heads. A COMPOUND term, though, was invisible inside a head: `((VADD md) x y)`, an
  applied `VNB-LAMBDA`, `((f (g r)) r)`. And when the term occurred both in the head and
  in an argument, only the argument was rewritten, SILENTLY. The walk now visits the
  head; the binder cases still block capture. Probe with before/after logs:
  `scratchpad/mx/subst-head-probe.scm`; five suite checks. Old drivers that `mac` an
  equation to reach an operator (`mvag-op`, `ras-op`) still work, and `subst` is now an
  alternative there.
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
  silent no-ops this file lists are all soft WARNINGS at the `cmd-*` layer (`subst` with
  nothing to rewrite returns #f from `pi-eq-subst!`, `mac-h` on a functoid name warns
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
* **The peel / split / pick kit is in driver-kit.scm (2026-09-14); stop copying it.** Measured
  that day: ~90 `<prefix>-peel!`, ~40 `<prefix>-skolem!`, ~10 `<prefix>-di-var!` and a dozen
  conjunction splitters in theorem-library/, verbatim or nearly. The shared ones are
  `dk-peel!`, `dk-split-all!`, `dk-pick`, `dk-only!`, `dk-apply!`, `dk-di-var!`,
  `dk-conj-close!`, `dk-skolem!` and `dk-halve!` (given `POS-RR eps` in context, lands
  `POS-RR d`, `d + d = eps`, `d in RR`, `0 < d` and returns `d`). A driver that defines one
  of these under its own prefix is duplicating.
* **Never put `inst*!`, `inst+` or `fact` inside a `dk-landed-1` thunk**: they land the whole
  instantiation chain, so the thunk lands several formulas and `dk-landed-1` errors. Wrap
  the `detach!` alone (`dk-apply!` does this).
* **Get `d in RR` and `0 < d` out of `POS-RR d` by CITATION** -- `rr-pos-rr-in-rr`,
  `rr-lt-of-pos-rr` (theorem-library/pos-rr-bridges.scm) -- never by `mac-h 'pos-rr`, which
  deletes the hypothesis the next `inst+` needs. Four drivers carried comments about
  sequencing the unfold after the instantiation; they were all this.
* **`slot` on a VIEW built by `def-functor` has no per-slot projection** (2026-09-14):
  `install-functor-projections!` runs only for `def-constructed-functor`, so `slot 'IDEN`
  on `IDEN(COMMUTATIVE-RING-MULTIPLICATIVE-CM R)` falls through to the global last-write-wins
  accessor index and produced `NTH(3, ...)`, not `ONE(R)`. The working pattern is
  `(slot 'IDEN) (mac 'commutative-ring-multiplicative-cm) (nth-r)` -- open the view's own
  functoid list -- and then ASSERT the goal is literally `(== (ONE R) (ONE R))` before
  `qrfl`, so a drifted index cannot close it with the wrong component.
* **`slot-h` has no accessor fallback; `slot` does.** Goal-side `slot 'DIST` rewrote every
  occurrence but the one under a `VNB-LAMBDA` binder, and `slot-h` refused the hypothesis
  outright (`mac-h: unknown theorem/macete: dist`). Bridge with a one-line `have!` lane
  (`nth(2,s)(x,y) == d(x,y)` by `(slot 'DIST)(qrfl)`) and one `subst`.
* **A proof file states its theorem LITERALLY.** `(sp (make-wff (lookup-theorem 'name)))`
  works against the band -- where the support is still installed -- and dies on the cold
  load, where it has been retired. Wave 1 lost a cold load to it.
* **`else` is shadowed in the per-file environment.** A `case`/`cond` with an `else` clause
  in a theorem-library file dies with "Special keyword can't be expanded"; write `(#t ...)`.
* **`seg-mem-succ-le` drags the UNGUARDED `co-le-trans` into every bill that cites it**
  (its backward half uses it). The five-line inline -- `seg-mem-lt`, `nn-le-succ`,
  `nn-le-trans-guarded`, `nn-le-imp-neq-succ` -- is `modulo 0`; interval-card-in-nn.scm
  does it, and poly-tail-zero / pigeonhole-segments / finite-surgery could.
* **A guard that keeps the binder list byte-identical beats the citer's own hypothesis.**
  The G-side Taylor facts (taylor-g-at-a/-at-x/-in-fun, taylor-poly-in-rr) needed only
  `DFUN(f,n)` -- every derivative up to order n is a total real function -- and
  TAYLOR-DIFFERENTIABLE implies it (`taylor-derivs-in-fun`, taylor-proof.scm). Guarding on
  TD itself would have forced a new binder `a` and an `a < x` antecedent into statements
  that never mention the interval. One `fact` of the bridge in the citer lands DFUN and
  every guarded fact then auto-detaches.
* **When a proof's window is INSIDE another proof file, splice it there.** The guarded
  Taylor facts cite taylor-proof.scm's lemma block and are cited by its taylor-lagrange;
  load.scm loads each theorem-library file into its own environment, so a split would
  strand the file-local helpers. Two marked blocks ("BEGIN spliced block") sit in
  taylor-proof.scm for that reason; the originals are in archive/spliced-2026-09-14/.
* **`vnb-probe` ships one file inside one SSM command, GZIPPED since 2026-09-17** (capataz
  refuses at 97 KB of command text, not 128; a 90 KB two-file chain is 28 KB gzipped) and
  refuses over 90 KB on the wire. Its `--timeout` bounds the PROVER inside the memory slot
  (`VNB_RUN_TIMEOUT` in vnb-slot), not the wait for a slot, which once killed a probe that
  had queued four minutes. And `scratchpad/surgery/mkprobe-slim.py` wraps a chain in
  `(fluid-let ((*vnb-loading* #t)) ...)`: the per-step `show` dumps go, warnings and qed lines
  stay, and a chain that was killed at 610 s verbose ran in 69 s. And
  the tree on a worker is only as fresh as the last push: an agent that `(load ...)`s a
  file "from the tree on the worker" gets whatever was pushed, not what the primary holds.
* **IOTA definedness has no elimination rule** (found 2026-09-14 on the vector Taylor arc).
  `iota-d` runs one way -- post exists-unique, then grant the property -- and nothing lets a
  proof pass from `(IN (IOTA x p) X)` to `p[x := (IOTA x p)]`. TAYLOR-DIFFERENTIABLE-V's
  continuity conjunct says every `NTH-DERIV-V m f k` is a total map into VEC(m), i.e. the
  IOTA `DERIV-V(m, f^(k-1), x)` DENOTES everywhere, which is semantically the
  differentiability the `gof-nth-deriv` induction needs -- and the kernel cannot use it.
  The missing principle is `iota-in-elim`: `(IN (IOTA x p) X) => p[(IOTA x p)]`, a kernel
  rule or base axiom; it is the user's call (it is a foundational decision about IOTA), and
  `gof-nth-deriv`, `g-of-remainder` and `gof-taylor-diff` wait on it. The other gap under
  them is a step lemma, "a bounded linear functional composed with a vector-differentiable
  map is differentiable with derivative g(L)", whose own bricks (BLF continuity in the norm
  metric, composition of continuity across DIFFERENT metric spaces, `g(VNEG v) = -g(v)`) do
  not exist. Exact statements in the spliced block of theorem-library/vector-taylor-proof.scm.
* **A slice of a proof file probed on the band must be loaded into
  `(extend-top-level-environment *driver-kit-env*)`**, as load.scm does: the band's top
  level is the library's own environment, and a slice's `(define SF ...)` rebinds the band
  PROCEDURE `sf` (case-folded). And check `(proof-done? *ps*)` before believing a missing
  `qed` line: a slice cut short of its own `qed` looks exactly like a divergence.
* **"Max over a finite family" is `nn-finite-subset-bounded` over an IMAGE** (2026-09-15, the
  last Ascoli rung): index the family by a finite set, map each index to its threshold by a
  CHOICE lambda, `card-image-finite` makes the image finite, and the bound of that image is
  the max. No `nn-finite-max` lemma is needed. And a cover whose members carry their own
  threshold as a SEP property (`{u | IS-OPEN u and forsome n. n serves u}`) needs no
  CENTRES/CHOICE-of-centre construction: `sep-me` reads the threshold off the member.
  `compact-seq-has-cluster` wants the same shape.
* **`sep-me` CONSUMES the membership it opens**, so a `lam-b` licensed by that membership must
  fire BEFORE it, or the beta owes a leaf nothing can close. And `have!` of a claim equal to
  the focus goal has no main branch (the cut is a self-loop; exhibit the witness with `ew`).
* **The finsum floor is enumeration-independence, and it is PROVEN (2026-09-17, rake batch
  N, rake-finsum-welldef.scm, `modulo 0`).** `sum-ag-permutation-invariance` did NOT need the
  archived splice-out argument (1200 lines, eight unwarranted `delete-at-*` / `inverse-bij-*`
  axioms): the content is ONE-ENTRY REPLACEMENT (`g = gp` off `k` => `SUM(g,n).gp(k) =
  SUM(gp,n).g(k)`, peeling the top index with `sum-ag-succ` and `(a.b).c = (a.c).b`) and the
  induced permutation of `OS(n)` is phi RE-ROUTED (`rho(i) = IF phi(i) = n THEN phi(n) ELSE
  phi(i)`), never compressed, so no index shifts and no inverse. Stated over the four LAWS
  (identity-in, closure, assoc, comm) as curried hypotheses, so the comm-monoid and
  abelian-group forms are fifteen lines each. `finsum-well-defined` and its comm-monoid twin
  follow, and `finsum-insert` / `finsum-insert-ag` (finsum-insert.scm, moved below them in
  load.scm) now bill `modulo 0`. `finsum-reindex` / `-ag` stay: they need `CARD S = CARD T`
  from a bijection, which the tree cannot conclude (`card-finite-bij` runs the other way;
  `card-star-bij` is about CARD-STAR) -- a card-layer lemma via `pigeonhole-segments-gen`
  both ways. Also from batch M: `finsum-fubini` is a DOUBLE FOLD with every family a VARIABLE
  (the rectangle curried), `ni` on the row count; two `def-functor` views with the same slot
  list are quasi-equal in four lines (`cra-is-rag`: `(di) (mac A) (mac B) (qrfl)`), which
  retires a same-shape support per three lines; `mac 'FINSUM` does not rewrite under a
  `VNB-LAMBDA` binder; a stray `'` before `)` reads as "Unbalanced close parenthesis".
  `finsum-embed` stays: it is the permutation floor in another hat (an INJECTION between index
  sets), closed by a `sum-ag-support-inj` lemma stated in rake-finsum-core.scm's header.
  `INSERT-LAST` (finsum.scm) is
  unusable for its purpose: its lambda has domain NN, so it can never be in a BIJECTION out
  of ORD-SEGMENT(succ n); the proof uses an inline lambda with the right domain.
* **Convolution associativity in the monoid algebra owes `finsum-reindex-inverse`**: a
  reindexing along a pair of mutually inverse maps (not a BIJECTION term, which
  `finsum-reindex-ag` demands). Exact statement in theorem-library/monalg-is-ring.scm's
  header; `monalg-mul-assoc` stays asserted until it exists.
* **Two of the bt- shims were character-for-character primitive axioms** (`bt-nn-in-zz` =
  `nn-subset-zz`, `bt-succ-in-nn` = `nn-succ-closed`) carrying 60+ bills each. The
  duplicate audit compares only against PROVEN theorems; it should compare against the
  primitive and definitional shelves too.

