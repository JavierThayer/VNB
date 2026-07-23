;;; tactics-help.scm -- a self-describing registry of the interactive tactics.
;;;
;;; Motivation: the short-form commands in interactive.scm are powerful but
;;; opaque -- a newcomer (or the user months later) sees `(di)' `(bc* ...)'
;;; `(mac-h ...)' with no clue what they do.  This file is the ONE place that
;;; names every surface tactic with a one-line gloss (and a longer blurb for
;;; the subtle ones), and renders it two ways:
;;;
;;;   * `(tactics)'        -- print the grouped menu at the REPL.
;;;     `(tactics 'mac-h)' -- print the long blurb for a single tactic.
;;;   * `(write-tactics-md)' -- emit reference/TACTICS.md, which
;;;     build-reference-html.py folds into the browser reference (the `R'
;;;     button) as a "Tactics" section.  Single source of truth, so the menu
;;;     can never fossilise the way a hand-maintained doc would.
;;;
;;; Keep this registry in sync when a tactic is added to interactive.scm.  The
;;; glosses describe the SURFACE behaviour, not the kernel rule -- the cmd-*
;;; layer is the authority for the latter.

;;; Each category is (TITLE entry ...); each entry is
;;;   (name "signature" "one-line gloss" "optional longer blurb")
;;; The blurb is shown by (tactics 'name) and in the .md; omit it (3-element
;;; entry) when the one-liner says everything.

(define *tactic-help*
  '(("Starting & finishing a proof"
     (sp   "(sp goal)"        "Start a proof of `goal' (a \"string\", a raw S-expr, or a wff); clears the script."
       "Begin a new proof: state what you want to prove.  The goal may be a \"string\" in surface syntax, a raw S-expr, or an already-built wff (e.g. (wff \"...\") or (make-wff '(...)));  sp coerces a string/S-expr for you.  This becomes your one open goal and clears any previous script.  (Technically: set the proof goal.)")
     (qed  "(qed 'name)"     "Install the finished proof as theorem `name' and save its replayable script."
       "Finish: once there are no open goals, this records the result as a named theorem you can cite later, and saves the replayable script.  (Technically: install-theorem! plus script capture; reports the asserted facts the proof still rests on, `proven modulo {...}'.)")
     (save-proof   "(save-proof 'name)"   "Save the current script under a name without finishing."
       "Save the current (possibly unfinished) proof script under a name, to resume or replay later.  (Technically: snapshot the script without installing a theorem.)")
     (replay-proof "(replay-proof 'name [subst])"
       "Re-run a saved script on the current goal, optionally renaming free vars."
       "The optional subst is an alist ((old . new) ...) applied to every command argument before replay -- this is how one proof is reused at fresh eigenvariables."))

    ("Decomposing the goal"
     (di   "(di)"   "Direct inference: split an AND goal, move an IMPLIES antecedent into the assumptions, or introduce a fresh eigenvariable for a leading FORALL."
       "Break the goal into its pieces.  A conjunction `A and B' splits into two goals, A and B.  An implication `P implies Q' assumes P (P becomes a hypothesis you may use) and leaves you to prove Q.  A universal `for all x, ...' fixes an arbitrary x (a new constant standing for `any x') and asks for the statement at that x.  Apply it repeatedly until the goal is a single atomic statement.  (Technically: the goal-side introduction rules for AND / IMPLIES / FORALL; the constant introduced for a FORALL is an eigenvariable.  Pairs with mac, which unfolds a definition in the goal.)")
     (pbc  "(pbc)"  "Proof by contradiction: assume the goal's negation, prove FALSITY."
       "Argue by contradiction: assume the goal is false and derive an absurdity.  (Technically: classical reductio -- adds the negation of the goal as a hypothesis and changes the goal to FALSITY.)")
     (oi-l "(oi-l)" "OR-intro left: reduce an (OR a b) goal to a."
       "Prove a disjunction `A or B' by proving the LEFT alternative, A.  (Technically: or-introduction, left.)")
     (oi-r "(oi-r)" "OR-intro right: reduce an (OR a b) goal to b."
       "Prove a disjunction `A or B' by proving the RIGHT alternative, B.  (Technically: or-introduction, right.)")
     (ew   "(ew term)" "Existential witness: discharge a FORSOME goal by supplying the witness term."
       "Prove `there exists an x with property P' by exhibiting a specific witness: you supply the term, and the goal becomes `P holds of that term'.  The everyday `take x = ...' step.  (Technically: existential introduction for a FORSOME goal.)")
     (ci   "(ci)"   "Cartesian intro: prove a CARTESIAN-product membership component-wise."
       "Prove that a pair (or tuple) belongs to a Cartesian product A x B by proving each coordinate lies in its factor.  (Technically: Cartesian-membership introduction, component-wise.)")
     (ti   "(ti)"   "Tuple intro: prove a tuple/LIST membership component-wise."
       "Prove that a list belongs to the set of tuples over A by proving each entry lies in A.  (Technically: tuple-membership introduction, component-wise.)")
     (ii   "(ii)"   "Intersection intro: prove (IN x (INTERSECTION ...)) for each branch."
       "Prove that x lies in an intersection of sets by proving it lies in each of them.  (Technically: intersection-membership introduction.)")
     (ui   "(ui k)" "Union intro: reduce a goal (IN x (UNION ...)) to membership of x in the k-th set (1-based)."
       "Prove that x lies in a union of sets by proving it lies in the k-th one (you choose which).  (Technically: union-membership introduction at branch k.)")
     (ni   "(ni)"   "Natural-number induction on the goal's leading FORALL over NN."
       "Prove `for all natural numbers n, P(n)' by induction: show P(0), and that P(n) implies P(n+1).  (Technically: natural-number induction on the goal's leading FORALL over NN.)"))

    ("Using a hypothesis"
     (ai   "(ai hyp)" "Antecedent inference: decompose a cited assumption -- AND-split, OR-into-cases, or FORSOME-elimination to a fresh eigenvariable."
       "Break a hypothesis into its pieces -- the mirror image of di, but on the assumptions instead of the goal.  From a hypothesis `A and B' you get both A and B; from `A or B' you split into two cases (prove the goal in each); from `there exists x, P(x)' you get a fresh name for such an x together with P(x).  Cite the hypothesis by its number in the display, its formula, or a \"string\".  (Technically: the hypothesis-side elimination rules for AND / OR / FORSOME; the fresh name is an eigenvariable.)")
     (ass  "(ass)"  "Close the goal by an assumption alpha-equivalent to it."
       "Finish the goal because it is already one of your hypotheses -- the `that is exactly what we assumed' step.  Renaming of dummy/bound variables doesn't matter (`there exists x, P(x)' closes `there exists y, P(y)').  (Technically: the assumption rule, matching up to alpha-equivalence.)")
     (inst "(inst forall-hyp term)" "Instantiate a universally-quantified assumption at `term', adding the instance to context."
       "Use a `for all x, ...' hypothesis at a particular value: you supply the term, and the statement with x replaced by that term is added to your hypotheses.  (Technically: universal instantiation of an assumption.)")
     (inst+ "(inst+ forall-hyp term)" "Instantiate an in-context universal at `term', then forward-detach any guards whose antecedents are in context."
       "inst followed by detach: from `forall x. (x in S) => P(x)' and `t in S' already known, this lands `P(t)' directly (peeling nested guards level by level), instead of leaving the guarded implication for you to detach by hand.  The hypothesis-side analogue of `fact' (which assembles a THEOREM); this assembles an in-context UNIVERSAL.  scout's inst lane emits these to close witness-needing goals like the metric laws.  (Technically: pi-instantiate! then pi-detach! while the consequent stays a guard with an in-context antecedent.)")
     (detach! "(detach! impl)" "Forward modus ponens: from an in-context (IMPLIES A B) whose A is also in context, leave B in context."
       "If you have both `P' and `P implies Q' among your hypotheses, this adds `Q' to them.  It grows what you KNOW (the hypotheses) rather than changing the goal -- the forward counterpart of bc.  (Technically: forward modus ponens, the kernel rule pi-detach!; sound since P and P=>Q give Q.)")
     (fact "(fact 'thm term ...)" "Forward APPLICATION of a theorem: bring it in, instantiate its leading universals with the terms, and auto-detach every antecedent already in context, landing the consequent as a hypothesis."
       "Handles interleaved forall/implies (e.g. forall s. IS-X(s) => forall a. a in CARR(s) => P): consumes one term per FORALL, detaches each IMPLIES whose antecedent is in context.  The forward-assembly workhorse -- a law `forall x. H(x) => P(x)' becomes the usable fact P in one call, instead of ta + inst* + cut/backchain.  See theorem-library/module-zero-act.scm.")
     (ce   "(ce hyp k)" "Cartesian elim: project the k-th component out of a CARTESIAN-membership assumption."
       "From a hypothesis that a tuple lies in a Cartesian product, extract that its k-th coordinate lies in the k-th factor.  (Technically: Cartesian-membership elimination, k-th projection.)")
     (te   "(te hyp k)" "Tuple elim: project the k-th component out of a tuple-membership assumption."
       "From a hypothesis that something is a tuple over A, extract that its k-th entry lies in A.  (Technically: tuple-membership elimination, k-th projection.)")
     (ie   "(ie hyp k)" "Intersection elim: extract the k-th branch of an INTERSECTION-membership assumption."
       "From a hypothesis that x lies in an intersection, extract that x lies in the k-th set.  (Technically: intersection-membership elimination.)")
     (ue   "(ue hyp)" "Union elim: split a cited (IN x (UNION ...)) membership assumption into one subgoal per set -- union-side case analysis, the dual of `ui'."
       "From a hypothesis that x lies in a union, split into cases -- one for each set x might belong to -- and prove the goal in each.  (Technically: union-membership elimination, case analysis; the dual of ui.)")
     (cut  "(cut formula)" "Cut: prove `formula' as a side subgoal, then continue the main goal with `formula' added as an assumption (Gentzen cut)."
       "Introduce a lemma you prove on the spot.  You state a formula; it becomes a side goal to prove, and on the main line you may then use it as a hypothesis.  The standard `we first show that ..., and now using it ...' move.  (Technically: Gentzen's cut -- nothing is left assumed-but-unproved, the side goal discharges it.)")
     (wk   "(wk hyp)" "Weaken: drop a cited assumption from the context to tidy the hypothesis list.  `hyp' may be a formula, a \"string\", or a 1-based assumption index."
       "Discard a hypothesis you no longer need, to keep the assumption list readable.  (Technically: weakening -- removing a hypothesis is always sound.)"))

    ("Rewriting"
     (mac   "(mac 'name)" "Rewrite the GOAL with an equivalence macete (unfold a definition, apply an iff/=/== law).  Fires only where the macete's side-conditions already hold in context."
       "Rewrite the goal using a definition or a known equivalence/equality (a `macete').  For instance, replace a defined predicate by what it stands for, or apply an identity.  It fires only where the law's side-conditions already hold in your hypotheses; where they don't, it leaves that spot untouched and looks deeper inside.  (Technically: goal-side rewriting by an equivalence/equality macete; all-or-nothing -- it does NOT spawn unmet side-conditions as goals.  Its hypothesis-side cousin is mac-h; the minor-premise-spawning variant is macm.)")
     (slot  "(slot 'acc)" "Reduce a structure ACCESSOR to its projection: (CARR s) becomes (NTH 1 s).  The one door for accessor reductions -- use it, never mac, on an accessor name."
       "Replace an accessor by the tuple position it stands for: (CARR s) is slot 1, so it becomes (NTH 1 s).  Pair it with nth-r to compute on a concrete structure -- (MUL ZZ-RING) reduces to bintimes.  It refuses anything that is not an accessor.  (Technically: fires the accessor's macete, which def-structure installs at declaration.  It exists so that ALL accessor reductions go through ONE procedure: the reduction is currently global and unconditional -- index k for every argument -- and making it structure-relative later, guarded by IS-X(s), should change this door and not its callers.  accessor-callsite-audit fails the suite if any file fires an accessor macete by name.)")
     (macm  "(macm 'name)" "Like mac, but a CONDITIONAL macete fires even when its side-conditions are not yet in context: each unmet condition is left as a new subgoal."
       "The minor-premises variant of mac.  mac only rewrites where the law's side-conditions ALREADY hold; macm rewrites regardless, spawning each unmet condition as a fresh goal to discharge -- the goal-side mirror of what mac-h already does on hypotheses.  This is what makes conditional finite-sum lemmas (finsum-*, sum-*, ...) usable as goal rewrites instead of only forward via fact.  (Technically: goal-side rewriting by a conditional macete; it emits the SAME single `macete' kernel rule as mac -- the unmet conditions become that one step's minor-premise subgoals.  It introduces NO new inference rule.)")
     (mac-h "(mac-h 'name hyp)" "Rewrite a cited ASSUMPTION in place with an equivalence macete; any side-condition not already in context is spawned as a new subgoal."
       "Like mac, but rewrites inside one of your HYPOTHESES instead of the goal -- replacing it by an equivalent statement (e.g. unfolding a definition in a hypothesis).  If the rewrite law has a side-condition you haven't established, that side-condition becomes a new goal to prove.  (Technically: hypothesis-side rewriting by Leibniz substitution of equivalents; sound because the macete is a genuine equivalence under its side-conditions, which are spawned as goals.)")
     (|mac-h*| "(mac-h*)" "Saturating mac-h: repeatedly unfold every defined predicate in the hypotheses and split the conjunctions they expose, until nothing is left folded.  One step in the trace instead of a dozen."
       "The hands-free version of mac-h.  Instead of naming each definition and each conjunction by hand -- (mac-h 'IS-METRIC-SPACE A1), split, (mac-h 'is-metric A2), split, ... -- (mac-h*) keeps unfolding any assumption whose head is a defined predicate and splitting any AND assumption, restarting until a full pass changes nothing.  It records as a SINGLE step, so the proof (and its PDF) is far shorter.  It adds no kernel rule: every unfold is the same kernel-checked mac-h, every split the same ai -- just driven to a fixpoint.  Ask (what-now) to see which hypotheses it would touch first.")
     (grind "(grind)" "Saturate the no-choice moves at the focus: decompose the goal connective (di) and break open the hypotheses (mac-h*), repeatedly, until neither fires.  The whole introduce-everything prefix in one step."
       "The deterministic normalizer.  It keeps applying di -- which strips a leading FORALL/IMPLIES/AND, introducing the bound variables and moving antecedents into your hypotheses -- and mac-h*, which unfolds defined predicates and splits conjunctions in the hypotheses, until the goal head is no longer a connective and no hypothesis is foldable.  None of these moves involves CHOOSING a lemma, so there is never anything to reconsider: grind just puts the focus into normal form (e.g. a metric-law goal becomes `(d s)(x,y) = (d s)(y,x)' with the metric's defining properties sitting unfolded in context).  It collapses the di...di mac-h* prefix that bloats proofs into a single step, and adds no kernel rule.")
     (scout "(scout [depth [branch [nodes]]])" "Speculatively search to a bounded depth across INDEPENDENT scratch branches; RETURNS a nested list (number-of-branches (d b) goal best-partials closing-branches) rather than printing.  Never touches the live proof."
       "The copilot's deep lane.  Where (what-now)/(tt) suggest one move, scout actually TRIES sequences: it clones the focus into a fresh deduction graph per branch (so backtracking is free -- a dead branch is just discarded), and does a BEST-FIRST search (frontier ordered by open subgoals left, ties broken deeper-first so it dives toward a closure) whose alphabet is (grind), the closers (ass/rfl/crs/arith), the top rewrite-index (mac) rules, the parameterless backchain (bc*) lemmas, and the INST LANE -- (inst+ <universal hyp> <context-typed term>), instantiating a `forall' hypothesis at a term the context already types and detaching the guard.  It RETURNS the result as data -- (examined-count (depth branch) goal best-partials closing-branches), where best-partials is ((open-goals-left (form ...)) ...) most-reduced first and closing-branches is ((form ...) ...) shortest first -- so you can pick it apart programmatically; use (scout-show ...) for the readable REPL report.  Every move is the real, kernel-checked tactic, so a closing branch is a genuine proof when you adopt it with (scout-run k).  A CITATION GUARD suppresses circular closures: a branch that discharges the goal by citing a library theorem that is the goal -- DIRECTLY (statement alpha-equal to the goal, `P proved by P') or TRANSITIVELY (the cited theorem was itself proven using the goal, i.e. a name alpha-equal to the goal is in its proof-debt closure -- the `compact=>complete by compact=>bongo + bongo=>complete' trap) -- is dropped from closing-branches, the theorem name recorded in *scout-citations*, and scout-show notes `the goal is already theorem X'.  (Loops built purely from independent ASSERTED facts have no live dependency edge to detect; that is warrant/debt hygiene, not scout's to check.)  Bounds: depth (default 6), per-node fan-out branch (default 3), total nodes (default 600).  El cheapo: it does not reason about which move is wise (only the witness terms are guessed, from what the context already types -- a bad guess just dies on the clone); it brute-forces a small tree and you eyeball the survivors.  The inst lane closes the metric laws past grind; goals that need a witness scout can't type (a fresh existential, a constructed term) still surface under best-partials.")
     (scout-show "(scout-show [depth [branch [nodes]]])" "Like (scout), but PRINTS the human-readable report (examined count, goal, closing branches or best partials) to the REPL.  Returns the same nested list (scout) does."
       "The eyeball version of scout: same search, same return value, but it also prints the numbered CLOSING branches (or, when none close, the best partials with how many goals each leaves open).  Use scout-show interactively, (scout) when you want to consume the result as data.")
     (scout-run "(scout-run k)" "Adopt closing branch k from the last (scout)/(scout-show) onto the live proof, running its tactics for real (they record and display normally)."
       "After scout finds CLOSING branches [1], [2], ..., (scout-run k) replays branch k's tactic forms through the real tactics on your live *ps*, from the same focus scout cloned -- so the proof advances and the steps are recorded for the script / PDF exactly as if you had typed them.  Works after either (scout) or (scout-show); both stash the closing branches.")
     (prep "(prep 'ineq)" "Why will a tactic not fire here, and what must be done first?  Runs the tactic's OWN preconditions one at a time, marks each ok / PREP / STOP, names the library lemma that repairs each unmet one, and prints a PLAN it has checked by running it on a scratch clone.  READ-ONLY: the live proof is never touched.  (prep 'ineq) is the only method so far."
       "A tactic reports failure as a boolean, so every unmet precondition comes out as the same #f and the same warning -- (ineq) says `goal not a linear-RR consequence of the named assumptions' whether your goal merely needs a di, or an atom needs a typing fact the library already proves, or the goal is simply false.  prep runs the same predicates separately and tells you WHICH failed.  For ineq the obligations are: the goal must BE an order relation (repair: di, counted by measuring, since one di consumes a typed FORALL and its guard together); every atom must be certified in RR by a LITERAL (IN t RR) scan -- (IN k NN) does not count, the oracle does no subtype reasoning (repair: a coercion lemma, e.g. nn-in-rr); some assumption must be order-shaped, since a fact like not(k=0) is invisible to Farkas (repair: a bridge lemma, e.g. nn-pos-of-nonzero); and the goal must actually follow, which only Fourier-Motzkin decides -- a STOP there means no prepping will help, which is the useful answer.  The repair search is by SHAPE over the whole library and is verified by SPECULATION: a candidate counts only if ineq then fires, not merely because it landed something order-shaped.  Every repair that works is reported, not just the first -- they come out alphabetical, which is no order of merit, and if the goal is itself a library theorem then citing IT is one of the closers.  Worked case: |- forall k in NN. ~(k=0) => k < 2k.  prep returns (di) (di) (fact 'nn-in-rr 'k) (fact 'nn-pos-of-nonzero 'k) (ineq 4) -- six steps, where the hand-built cut/crs route through k = k+0 < k+k = 2k took thirteen and billed two extra transitivity lemmas.  A tactic joins the table with (prep-method! 'FUBA proc); crs and ass are the obvious next two.")
     (subst "(subst '(= s t))  |  (subst '(== s t))" "Rewrite s -> t throughout the goal, using an equation s = t -- or a quasi-equation s == t -- that is in context, in EITHER orientation (Leibniz substitution).  Cannot reach a term in OPERATOR position: use the equation as a macete instead."
       "Use an equation among your hypotheses to replace s by t everywhere in the goal.  BOTH equalities license it: `=' is VNB's partial equality, and `s = t' already entails s = s and t = t, so t is defined wherever s was and the rewrite never replaces a defined term by an undefined one; `==' is quasi-equality (same definedness, equal where defined), which is a congruence and so substitutes exactly as `=' does -- which you need, since the partial-op recursion and bridge facts are stated with `=='.  The head you pass need not match the head in context, and neither need the orientation: all four of (= s t), (= t s), (== s t), (== t s) are searched for, and the goal is always rewritten s -> t.  LIMIT: the rewrite walk reaches argument positions only, so it is a silent no-op on a term in OPERATOR position -- (subst '(= (VADD md) ...)) will not touch the goal ((VADD md) x y).  Structure accessors are almost always in operator position; use the equation as a macete there (mac on the goal, mac-h on a hypothesis).  (Technically: Leibniz substitution from an in-context equality or quasi-equality.)")
     (beta  "(beta)"  "Beta-reduce a functoid application in the goal."
       "Simplify a function-expression applied to an argument by substituting the argument into its body.  (Technically: beta-reduction of a functoid application in the goal.)")
     (nth-r "(nth-r)" "Reduce an NTH applied to a literal LIST in the goal."
       "Simplify `the k-th entry of an explicit list [a1, a2, ...]' to that entry.  (Technically: reduce NTH applied to a literal LIST.)")
     (len-r "(len-r)" "Reduce a LENGTH applied to a literal LIST in the goal."
       "Simplify `the length of an explicit list [a1, ..., an]' to the count n.  Structural (the dual of nth-r): the spine of a list literal is total, so its length is n regardless of whether the entries are defined.")
     (rfl   "(rfl)"   "Close a reflexive equality goal (t = t)."
       "Close a goal `t = t' -- a thing equals itself.  (Technically: reflexivity of equality.)")
     (qrfl  "(qrfl)"  "Quasi-reflexivity: close t = t under the partial-equality definedness reading."
       "Close `t = t' under the partial-equality reading, where asserting t = t also asserts that t is DEFINED.  Use this rather than rfl when t might be undefined.  (Technically: quasi-reflexivity; see the partial-equality convention, where `t = t' is the definedness predicate.)"))

    ("Arithmetic & ring oracles"
     (arith "(arith)" "Discharge a ground arithmetic goal by evaluation."
       "Close a goal that is a concrete numerical fact with no variables -- e.g. 2 + 3 = 5, or 7 in NN -- by just computing it.  (Technically: decision by ground arithmetic evaluation.)")
     (rs    "(rs)"    "Ring-simplify the goal (normal form over the ambient ring)."
       "Simplify the goal to a normal form in the ambient ring (which need not be commutative).  The non-commutative companion of crs.  (Technically: ring-simplify to a canonical word form.)")
     (crs   "(crs)"   "Commutative-ring decision procedure: prove a polynomial identity over ZZ[generators].  Expands literal powers, so (x+y)^2 = ... closes directly."
       "Prove a polynomial identity that holds in EVERY commutative ring -- e.g. (x+y)^2 = x^2 + 2xy + y^2 -- by reducing both sides to a canonical sum-of-monomials form and checking they agree.  A genuine decision procedure: a true commutative-ring identity closes, a non-identity is refused.  Literal powers are expanded for you.  (Technically: normal form over the free commutative ring ZZ[generators].)")
     (simp  "(simp [target])" "Rewrite a commutative-ring SUBTERM of the goal to canonical form, IN PLACE (e.g. (x+y)^2 inside a larger goal becomes x^2 + 2*x*y + y^2).  Works on BOTH surfaces: concrete number domains (+ * - ^ over NN/ZZ/QQ/RR/CC) and a generic ring s ((ADD s)/(MUL s)/(NEG s), carrier (CARR s)).  No arg = outermost ring subterm; \"term\" targets a specific one.  Sound by cut + crs + eq-subst (no new kernel rule); needs the subterm's generators typed in context (true post-di), else refuses and names them.")
     (ineq  "(ineq i1 i2 ...)" "Close a linear-inequality goal over RR (<= < > >= = between RR terms) as a consequence of the named assumptions (1-based indices), via the Fourier-Motzkin/Farkas oracle.  Linearizes over + - * and the binplus/binneg/bintimes aliases; every MAXIMAL non-arithmetic subterm is an atom that must be certified in RR.  (Does NOT see through a generic ring's (ADD s)/(MUL s) -- those become opaque atoms.)"
       "Close a LINEAR inequality over the reals that follows from inequalities you cite (by their hypothesis numbers) -- by chaining them, adding them, and scaling by positive constants.  Anything that is not built from + - and multiplication-by-constants is treated as an opaque quantity, so it handles e.g. the triangle inequality where the distances are unknowns.  For NONLINEAR (polynomial) inequalities use sos instead.  (Technically: Fourier-Motzkin / Farkas over the ordered field RR; every atom must be certified real.)")
     (sos   "(sos \"c1\" \"c2\" ...)"
            "Sum-of-squares closer for a nonstrict polynomial inequality a <= b over RR (the nonlinear companion of (ineq)).  You supply the terms to be SQUARED; it finds the nonnegative coefficients.  (tactics 'sos) for the worked example."
            "A sum-of-squares closer.  To prove  a <= b  it is enough to exhibit\nb - a  as a sum of squares (each obviously >= 0), reducing the inequality to\nan algebraic identity.  You hand sos the terms to be SQUARED -- the c_i, NOT\nthe squares -- and it solves for nonnegative rationals lambda_i with\n\n      b - a  =  lambda_1 c_1^2 + ... + lambda_n c_n^2\n\n(matched coefficient-by-coefficient in crs's commutative-ring normal form),\nthen PRINTS the lambda_i it found.  You do not supply them.\n\nWorked example.  Goal  forall([x in rr, y in rr], x*y <= x^2 + y^2).  Here\nb - a = x^2 - x*y + y^2 = 1/2(x-y)^2 + 1/2 x^2 + 1/2 y^2,  so the things\nsquared are  x-y, x, y:\n\n      (sos \"x - y\" \"x\" \"y\")\n          ;; closes, printing  1/2(x-y)^2 + 1/2 x^2 + 1/2 y^2\n\n2*x*y <= x^2 + y^2 needs only one square:  (sos \"x - y\").  The three-variable\na*b+b*c+c*a <= a^2+b^2+c^2  wants  (sos \"a - b\" \"b - c\" \"c - a\").\n\nNotes.\n - Write the c_i with the goal's own variable names.  di preserves them, so\n   sos works before OR after di; skip di and sos peels the typed\n   forall([... in rr]) wrapper itself.\n - Every generator (variable) must be certified in RR -- a goal binder\n   x in rr  or an  (IN g RR)  assumption.\n - A wrong or insufficient certificate refuses cleanly: nothing is closed,\n   you simply try other squares.\n - Strict (<) goals are refused -- a square can be 0, so squares alone never\n   force a strict inequality."))

    ("Chained reasoning"
     (calc "(calc L0 (rel1 L1 [just1]) (rel2 L2 [just2]) ...)"
           "Ground the focus goal (REL L0 Ln) by a CHAIN of intermediaries L0 rel1 L1 rel2 L2 ... reln Ln: proves each link and composes them into the endpoint.  A link no lane can close is LEFT OPEN as a leaf -- the refinement point, and the PSS candidate.  Relations: = == (folded by transitivity), < <= (folded through the co-*-trans lemmas, with = steps riding along), IFF (chained per direction).  RETURNS the links, the open ones, and their PSS candidates as an alist."
           "Write the argument the way you would on paper -- as a chain through intermediate terms -- and let the machine prove each link:\n\n      Goal  k < 2*k   (with k in NN, ~(k=0))\n      (calc 'k '(= (+ k 0)) '(< (+ k k)) '(= (* 2 k)))\n          ;; i.e.  k = k+0 < k+k = 2*k\n\nEach step names a RELATION and the next LINE; calc cuts the link (rel L(i-1) Li), dispatches a lane at it, and on success composes the whole chain into the goal.  It is pure bookkeeping over the trusted tactics -- no kernel rule, no axiom of its own -- so a calc proof bills exactly the lemmas its lanes and composers cite.\n\nThe COMPOSER is forced by the relations you used, and there are three families: `cong' for = and ==, folded by eq-trans; `order' for < and <=, folded through the co-lt-trans / co-le-lt-trans / co-eq-lt-trans ... lemmas (a = step rewrites an endpoint of the running relation and rides along, which is why the chain above needs no separate arithmetic); and `iff', which di's the goal into its two directions and chains each with ai/detach!, because VNB cannot quantify over propositions and so has NO first-order iff-trans lemma to fold with.\n\nThe JUSTIFICATION of a link is optional and defaults to 'auto -- try the relation's lanes: crs then arith for = / ==; for < / <= the NN->RR bridge then ineq over the order-shaped premises; grind for IFF.  Otherwise pass 'scout (a small scout search), a macete/theorem NAME (mac it, then close), an explicit tactic form like '(fact 'nn-pos-of-nonzero 'k) eval'd at the link's focus, or 'open / #f to leave the link open ON PURPOSE.\n\nSanity first: calc ERRORS before touching the proof if the goal's head is not the composed relation, or its LHS is not L0, or its RHS is not Ln.  A link already in the main context is taken as a GIVEN and skipped -- cutting it would be an alpha self-loop that opens no leaf.\n\nWhat it is FOR is the open links.  A chain whose links are all closed is a proof; a chain with one open link has isolated your obstacle to a single formula, printed with its free variables and their context typing -- which is the PSS candidate to state as a lemma.  Refine by inserting more intermediaries until each link is discoverable.  (See also (prep 'ineq), which answers the other question: why a lane will not fire.)")
     (have! "(have! CLAIM [THUNK])"
       "Assert CLAIM as an intermediate step and carry on with it as a hypothesis: cut CLAIM, discharge the side goal from context (or by THUNK), and stay on the main branch."
       "The `we have X' step.  You state an intermediate fact CLAIM that follows immediately from what is already known; have! cuts it, proves the resulting side goal automatically, and returns you to the main branch with CLAIM now available as a hypothesis.  The automatic discharge (`from-context!') closes the everyday cases -- a conjunction, splitwise; an (IN (a*b) NN) by nn-mul-closed on the factors; a numeral membership by arith; otherwise the goal is already a context assumption up to alpha.  When the side goal needs more than that, pass a THUNK -- any tactic sequence -- as the second argument to discharge it your way.  It ERRORS, never silently no-ops, if CLAIM is already in context up to alpha: the cut would self-loop, opening one child and no main branch.  So a script reads as the argument does -- `we have q0*q0 = 3*(k*k); we have k =/= 0; ...'.  (Technically: composite -- cut then from-context! or THUNK; adds no kernel rule.)"))

    ("Backchaining with a theorem"
     (ta  "(ta 'name)" "Theorem-assumption: bring the named installed theorem into context as an assumption."
       "Bring an already-proved theorem into your current hypotheses so you can use it (instantiate it, detach from it, ...).  (Technically: adds the named installed theorem as an assumption.)")
     (wbc "(wbc ['name])" "Witness-shape backchain: on an `exists v. ...' goal, cite a PSS lemma that MANUFACTURES a witness of that shape, so you can finish with inst+/grind/ew."
       "The discovery move for existence proofs.  Faced with `there exists phi with ...', it looks up the produces-witness index for lemmas whose conclusion builds the RIGHT KIND of object -- the same existential-witness shape -- even when the rest of the statement differs (which is why plain bc* misses them: bc* demands the WHOLE conclusion unify).  E.g. on `exists phi. STRICTLY-MONO-NN(phi) and IS-CAUCHY-SEQ(SUBSEQ f phi)' it reaches for `diagonalization' (which makes a STRICTLY-MONO-NN phi from a nested family); on a nested-family goal it reaches for `block-family'.  With no argument it cites the top retrieved producer; (wbc 'name) cites the one you name.  It brings the lemma in (via ta); you then discharge its hypotheses (inst+), skolemize its existential (grind), and supply its witness to your goal (ew).  Circular `headline' lemmas that already conclude your exact goal are filtered out.  (See (witness-producers goal) for the raw retrieval; what-now lists the (wbc 'name) candidates on any existential goal.)")
     (bc  "(bc impl)"  "Backchain the goal through an (IMPLIES A B) already in context: if the goal matches B, the new goal is A."
       "Work backwards through an implication you already have.  If `P implies Q' is among your hypotheses and your goal is Q, this reduces the goal to proving P.  The everyday `to get Q it's enough to show P'.  (Technically: backchaining the goal through an in-context implication whose conclusion matches.)")
     (bc* "(bc* 'thm [((v val)...)] h1 h2 ...)"
       "Matching backchain: unify the theorem's conclusion against the goal, then leave its (instantiated) antecedents as subgoals -- optional handlers hk run on the k-th subgoal."
       "Apply a known theorem to your goal.  If you have a theorem `if A and B then C' and your goal is its conclusion C -- matching the theorem's variables to yours, and the names of any dummy/bound variables don't matter (`there exists a net N' applies to a goal `there exists a net F') -- this replaces `prove the goal' with `prove A' and `prove B', the theorem's hypotheses.  The everyday `by Theorem X it suffices to show A and B'.  You may attach a handler to each hypothesis to dispatch it; values the match can't determine you supply as ((v val) ...).  (Technically: peels the theorem's leading universals and implications, matches the conclusion -- alpha-aware on bound variables -- and replays ta/inst/cut/bc automatically.)"))

    ("Lambda, comprehension & description"
     (lam-t  "(lam-t)" "VNB-LAMBDA typing: reduce (IN (VNB-LAMBDA ...) (FUN A B)) to its body obligation."
       "Show that a function defined by a formula (`x |-> ...') maps A into B -- reduces to showing that, for an arbitrary input in A, the value lies in B.  (Technically: VNB-LAMBDA typing into FUN A B.)")
     (lam-b  "(lam-b)" "VNB-LAMBDA beta: reduce an applied lambda to its substituted body."
       "Simplify a function `x |-> e(x)' applied to an argument a to e(a) -- the body with the argument substituted in.  (Technically: VNB-LAMBDA beta-reduction.)")
     (lam-b-h "(lam-b-h hyp)" "VNB-LAMBDA beta in a cited ASSUMPTION -- what mac-h is to mac."
       "Beta-reduce an applied lambda inside a hypothesis, in place.  Needed because a `fact' that instantiates a theorem's function variable at a lambda lands the APPLIED lambda in the CONTEXT, where the goal-side `lam-b' cannot reach it: union-of-opens-open at the identity family g := x |-> x lands is-open(md, big-union(i, fam, (x |-> x)(i))).  Without this the proof must detour through a cut beta-equation and a subst.  Cites nothing, so it adds no debt.")
     (sep-set "(sep-set)" "Separation sethood: the separation set {x in A | p} is a set."
       "Show that a set-builder set {x in A | p(x)} is genuinely a set.  (Technically: separation sethood -- a subclass of a set is a set.)")
     (sep-mi  "(sep-mi)"  "Separation membership intro: prove (IN t {x in A | p})."
       "Prove that a term t belongs to {x in A | p(x)} by showing t lies in A and satisfies the condition p.  (Technically: separation-membership introduction.)")
     (sep-me  "(sep-me hyp)" "Separation membership elim: split a separation-membership assumption into A-membership and the predicate."
       "From a hypothesis that t belongs to {x in A | p(x)}, extract the two facts it packs: t lies in A, and p(t) holds.  (Technically: separation-membership elimination.)")
     (comp-mi "(comp-mi)" "Comprehension membership intro."
       "Prove that something belongs to a comprehension set by establishing the set's defining condition for it.  (Technically: comprehension-membership introduction.)")
     (comp-me "(comp-me hyp)" "Comprehension membership elim."
       "From a comprehension-membership hypothesis, extract its defining condition.  (Technically: comprehension-membership elimination.)")
     (iota-d  "(iota-d term)" "Definite-description: discharge the IOTA uniqueness obligation for `term'."
       "Justify `the unique x such that p(x)' (a definite description) by proving that exactly one such x exists.  (Technically: IOTA -- discharge the uniqueness obligation for the described term.)")
     (bu-set  "(bu-set)" "Big-union sethood."
       "Show that a big union (the union of an indexed family of sets) is itself a set.  (Technically: big-union sethood.)")
     (bu-mi   "(bu-mi w)" "Big-union membership intro via the index witness w."
       "Prove that an element lies in a big union by exhibiting one index w whose set already contains it.  (Technically: big-union-membership introduction via the index witness.)")
     (bu-me   "(bu-me hyp)" "Big-union membership elim."
       "From a hypothesis that an element lies in a big union, obtain an index whose set contains it (a fresh name for that index).  (Technically: big-union-membership elimination.)"))

    ("Conditional terms"
     (if-true  "(if-true t)"  "Reduce an (IF p a b) term on the p branch: spawns p as a subgoal; the continuation gains (= (IF p a b) a)."
       "Evaluate a conditional term `if p then a else b' on the assumption that p holds: you take on p as a side goal, and may then use that the conditional equals a.  (Technically: if-true reduction, spawning p.)")
     (if-false "(if-false t)" "Reduce an (IF p a b) term on the not-p branch: spawns (NOT p); the continuation gains (= (IF p a b) b)."
       "Evaluate a conditional term `if p then a else b' on the assumption that p fails: you take on `not p' as a side goal, and may then use that the conditional equals b.  (Technically: if-false reduction, spawning not p.)"))

    ("Navigation, display & tacticals"
     (focus  "(focus n)"  "Switch the focus to the n-th open goal (1-based).")
     (show   "(show)"     "Redisplay the current proof state.")
     (goal-status "(goal-status)" "One-line summary: done / N open goals.")
     (repeat "(repeat thunk [cap])" "Run thunk until it stops changing the proof state (LCF REPEAT).")
     (orelse "(orelse t1 t2 ...)" "Run thunks in order, stop at the first that makes progress (LCF ORELSE).")
     (quietly "(quietly thunk)" "Run thunk with state-dump output suppressed; returns its value."))

    ("Forward-reasoning idioms  [proof-local -- NOT yet surface tactics]"
     ;; detach! was promoted to a real surface tactic (see "Using a hypothesis"),
     ;; backed by the kernel rule pi-detach!; `fact' is built on it.
     (cut-mem!        "(cut-mem! mem A)" "Prove a membership (IN (f x) B) by fun-apply-type with domain A, leaving it in context.  [proof-local]")
     (metric-sym-eq!  "(metric-sym-eq! S P Q)" "Add (= ((DIST S) P Q) ((DIST S) Q P)) to context via the metric-sym axiom.  [proof-local]")
     (focus-leaf!     "(focus-leaf! substr)" "Focus the frontier leaf whose goal contains substr (never trust auto-advance).  [proof-local]")
     (split-ands!     "(split-ands!)" "Flatten every AND assumption of the focus into separate assumptions.  [proof-local]")
     (ass-all-frontier! "(ass-all-frontier!)" "Close every frontier leaf whose goal is already among its assumptions.  [proof-local]"))

    ("Choosing and naming witnesses"
     (minimize! "(minimize! '(v1 ... vk) GUARD MEASURE)"
       "Choose v1..vk satisfying GUARD with the NN-valued MEASURE as small as possible: lands the witnesses and their minimality, and opens the two obligations any minimisation owes (MEASURE lands in NN; GUARD is satisfiable)."
       "The `least such' / minimal-counterexample step, mechanised.  You give three things: the variables to choose, a GUARD formula they must satisfy, and a natural-number-valued MEASURE term to make small.  On the main branch it hands you fresh eigenconstants w1..wk with two hypotheses -- GUARD holds of them, and nothing satisfying GUARD has a strictly smaller MEASURE -- and it opens exactly the two side goals a minimisation genuinely owes: that MEASURE lands in NN wherever GUARD holds (the TYPE goal), and that GUARD holds somewhere (the NONEMPTY goal).  Everything in between -- forming the value set, well-ordering it, unpacking the least witness, and restating minimality in terms of your variables rather than the set -- is done for you.  Every vi must occur in MEASURE (a variable the measure ignores is not one you are minimising over).  Because it quantifies over the vk at the META level, no lambda and no FUN(U,NN) typing obligation ever enters the logic -- it takes a formula and a term, which is what a driver has in hand, and never forms the set U at all.  Returns (list (w1 ... wk) TYPE-node NONEMPTY-node); either node is #f when that obligation was already in context up to alpha, so test before refocusing.  (Technically: composite -- it drives cut / di / ai / ew / sep-mi / sep-me / fact / inst / detach! / subst / ass / rfl and adds no kernel rule; its one mathematical appeal is `nn-least-element', the well-ordering of NN, proven from ord-well-ordered.  NO choice principle is used: well-ordering returns a MEMBER of a separation set, and sep-me recovers the witness.)")
     (obtain "(obtain LANE)"
       "Run LANE -- a thunk whose forward step lands a `there exists' into context -- then eliminate that existential and RETURN the fresh witness's name, read off the proof state rather than guessed."
       "The `let w be such an x' step, with the eigenvariable named for you.  LANE is a zero-argument procedure whose effect is to land some `there exists v. P(v)' among your hypotheses -- e.g. (lambda () (fact 'nn-3-div-square w)).  obtain runs it, spots the existential that newly appeared, eliminates it (introducing a fresh eigenvariable and landing P at that witness), unpacks any conjunction in the body, and hands back the eigenvariable's NAME -- identified by free-variable set-difference (the symbol now in context that was not there before), so the driver never guesses what the engine called it.  This is the robust way to name a descended witness: (define k (obtain (lambda () ...))), then use k.  Returns #f (with a note) if the lane landed no existential.  (Technically: composite -- a guarded forward discharge followed by forsome-elim (ai) and AND-splitting.  Plain existential elimination, so it owes nothing and uses no choice.)")
     (vlet "(vlet (n1 ...) FORMER)"
       "Bind proof-object names from the current state.  FORMER is (match PATTERN) -- bind each name to its slot in a context formula matching PATTERN -- or (choice [v body]) -- eliminate an in-context existential and bind its witness."
       "A binding form for the pieces of a proof, so a driver NAMES what it needs instead of navigating to it by shape.  Two FORMERs.  (match PATTERN): the listed names ARE the holes (wildcards) in PATTERN; everything else is literal.  vlet searches the context for a formula or subterm matching PATTERN and binds each name to what filled its slot -- pure selection, no proof step, no obligation; a hard error if nothing matches (you named a piece of something absent).  (choice): eliminate the sole existential in context and bind its witness.  (choice v body): present-else-debt -- if `there exists v. body' is already in context up to alpha, eliminate it; otherwise cut it, LEAVE the existence side-goal open as a debt leaf, and eliminate on the main branch -- either way the witness is bound and body[witness] is landed.  vlet's (choice) and `obtain' are the same underlying mechanism -- eliminate an existential, name the witness by free-variable difference -- differing only in what they take: obtain runs a lane and names what it just produced, vlet names an existential already (or, with a body, about to be) in context.  No choice AXIOM is used; a single witness is plain existential-elimination.  (Technically: a define-syntax expanding to (define n ...) over vlet--match / vlet--choice!; composite, no kernel rule beyond forsome-elim and, for present-else-debt, cut.)"))))

;;; --------------------------------------------------------------------
;;; How arguments are entered -- ONE statement, rendered in both surfaces
;;; (the (tactics) menu and reference/TACTICS.md), so the per-entry
;;; signatures can use the bare arg names (`'name', term, hyp) without each
;;; one re-explaining quoting.  Two surfaces, same tactics:
;;;   * PROGRAMMATIC (Scratch Workspace / REPL / proof scripts): explicit,
;;;     quoted Scheme.
;;;   * INTERACTIVE (Focus Workspace prompts): the bare value, unquoted.
;;; --------------------------------------------------------------------

(define *tactics-arg-help*
  (string-append
   "Entering arguments.  The same tactics serve two surfaces:\n"
   "  * PROGRAMMATIC  (Scratch Workspace / REPL / scripts) -- write explicit\n"
   "    quoted Scheme, e.g. (mac 'IS-METRIC-SPACE), (cut \"x in nn\").\n"
   "  * INTERACTIVE   (Focus Workspace prompts) -- type the bare value at the\n"
   "    prompt (no outer quote): a name as NAME, a formula as its surface text.\n"
   "\n"
   "Three argument kinds (the per-entry signatures use these names):\n"
   "  'name   a quoted symbol -- a macete / theorem name.\n"
   "          mac, mac-h, ta, bc*, fact (1st arg), qed, save-proof, replay-proof.\n"
   "  term / formula / wff / impl / eq\n"
   "          a \"string\" in surface syntax (parsed for you) OR a raw quoted\n"
   "          S-expr '(...).  sp's goal, ew's witness, cut, subst, the term of\n"
   "          inst / inst+, fact's remaining args.\n"
   "  hyp     same as a formula -- \"string\" or '(...) -- OR a 1-based assumption\n"
   "          NUMBER from the Focus display.  ai, bc, wk, detach!, and the\n"
   "          hypothesis arg of inst / inst+ / mac-h / ce / te / ie.\n"
   "\n"
   "So a goal-citing arg and a hypothesis-citing arg accept the same forms; only\n"
   "a hypothesis arg additionally accepts its display number.  A 'name never\n"
   "takes a string.  Interactively, drop the quote/quotes and just type it.\n"))

;;; --------------------------------------------------------------------
;;; REPL printer
;;; --------------------------------------------------------------------

(define (tactics--all-entries)
  (apply append (map cdr *tactic-help*)))

(define (tactics--find name)
  (let loop ((es (tactics--all-entries)))
    (cond ((null? es) #f)
          ((eq? (caar es) name) (car es))
          (else (loop (cdr es))))))

(define (tactics--gloss e) (caddr e))
(define (tactics--blurb e) (if (> (length e) 3) (cadddr e) #f))

;;; --------------------------------------------------------------------
;;; "When useful" notes -- the APPLICABILITY trigger for each tactic
;;; ("reach for this when the goal looks like ...").  A dedicated field,
;;; separate from the gloss (what it DOES) and blurb (the long form), keyed
;;; by tactic name.  Rendered as a `when:' line in (tactics) / (tactics 'n)
;;; / TACTICS.md.  Its executable counterpart is (vnb-apply? 'name goal),
;;; and (what-now) lists which of these actually FIRE on the live goal.
;;; --------------------------------------------------------------------
(define *tactic-when*
  '((sp        . "starting a new proof")
    (qed       . "no open goals remain -- record the result")
    (di        . "the goal head is AND / IMPLIES / FORALL -- decompose before deciding")
    (pbc       . "a direct argument stalls and assuming the negation gives something concrete to work with")
    (oi-l      . "the goal is (OR a b) and the LEFT alternative is provable")
    (oi-r      . "the goal is (OR a b) and the RIGHT alternative is provable")
    (ew        . "the goal is FORSOME and you have a witness term in mind")
    (ci        . "the goal is membership in a CARTESIAN product")
    (ti        . "the goal is membership in a set of tuples / LIST")
    (ii        . "the goal is membership in an INTERSECTION")
    (ui        . "the goal is membership in a UNION and you know which branch")
    (ni        . "the goal is `forall n in NN, P(n)'")
    (ai        . "a hypothesis is an AND / OR / FORSOME to break apart")
    (ass       . "the goal already appears (up to bound-var renaming) among the hypotheses")
    (inst      . "you have a forall-hypothesis and a specific value to use it at")
    (inst+     . "a GUARDED forall-hyp whose guards are dischargeable from context (e.g. the metric laws post-grind)")
    (detach!   . "you have both P and (P => Q) in context and want Q")
    (fact      . "a library law `forall x. H(x) => P(x)' whose P you want landed as a hypothesis")
    (ce        . "a hypothesis is CARTESIAN-product membership")
    (te        . "a hypothesis is tuple membership")
    (ie        . "a hypothesis is INTERSECTION membership")
    (ue        . "a hypothesis is UNION membership -- case-split on it")
    (cut       . "you want to prove a lemma on the spot, then use it")
    (wk        . "the hypothesis list is cluttered with something no longer needed")
    (mac       . "the GOAL has a defined predicate to unfold / an identity to apply, side-conditions already met")
    (macm      . "the GOAL has a CONDITIONAL identity/definition to apply whose side-conditions you are willing to leave as subgoals")
    (mac-h     . "a HYPOTHESIS has a definition to unfold / an equivalence to apply")
    (|mac-h*|  . "several hypotheses are folded definitions / conjunctions to open at once")
    (grind     . "right after sp, or any time the focus has connective/definitional structure -- normalize first")
    (scout     . "you are stuck and want the machine to TRY move-sequences (returns data)")
    (scout-show . "same as scout but you want the readable report at the REPL")
    (scout-run . "scout found a closing branch you want to adopt onto the live proof")
    (subst     . "you have an equation s = t (or a quasi-equation s == t) in context and want to rewrite the goal by it -- and the target is not in operator position")
    (beta      . "the goal has a functoid applied to an argument")
    (nth-r     . "the goal has NTH of a literal LIST")
    (len-r     . "the goal has LENGTH of a literal LIST")
    (rfl       . "the goal is `t = t' with t manifestly defined")
    (qrfl      . "the goal is `t = t' but t might be UNDEFINED (partial =)")
    (arith     . "the goal is ground arithmetic -- no variables")
    (rs        . "the goal is a (possibly non-commutative) ring-word identity")
    (crs       . "the goal is a commutative-ring identity, e.g. (x+y)^2 = x^2+2xy+y^2")
    (simp      . "a ring SUBTERM of a larger goal should be put in normal form in place")
    (ineq      . "a LINEAR <= / < over RR that follows from inequalities you can cite")
    (sos       . "a NONSTRICT POLYNOMIAL <= over RR (the nonlinear cousin of ineq)")
    (calc      . "the goal is (REL L0 Ln) and you can WRITE the chain of intermediaries that gets there -- or you want the one link that will not close isolated as a PSS candidate")
    (ta        . "you want a library theorem available as a hypothesis")
    (wbc       . "an EXISTENCE goal whose witness a PSS lemma manufactures (diagonalization / block-family)")
    (bc        . "you have (P => Q) in context and the goal is Q")
    (bc*       . "a library theorem's CONCLUSION matches your goal")
    (lam-t     . "the goal types a VNB-LAMBDA into FUN(A,B)")
    (lam-b     . "the goal has a VNB-LAMBDA applied to an argument")
    (sep-set   . "the goal asserts a separation set { x in A | p } is a set")
    (sep-mi    . "the goal is membership in a separation set { x in A | p }")
    (sep-me    . "a hypothesis is separation-set membership -- unpack it")
    (comp-mi   . "the goal is comprehension-set membership")
    (comp-me   . "a hypothesis is comprehension-set membership")
    (iota-d    . "the goal involves IOTA and you must discharge its uniqueness obligation")
    (bu-set    . "the goal asserts a BIG-UNION is a set")
    (bu-mi     . "the goal is BIG-UNION membership -- you have the index witness")
    (bu-me     . "a hypothesis is BIG-UNION membership -- obtain its index")
    (if-true   . "the goal has an (IF p a b) term to evaluate on the p branch")
    (if-false  . "the goal has an (IF p a b) term to evaluate on the not-p branch")
    (tfi       . "the goal is `forall v. v in ORD => P(v)' -- transfinite induction")
    (tfi3      . "transfinite induction with explicit zero / successor / limit cases")
    (minimize! . "the goal falls to a `least such' / minimal-counterexample argument -- descent proofs (sqrt 2, sqrt 3 irrational), least-degree or least-pivot witnesses")
    (obtain    . "a forward step yields `there exists ...' and you want to name the witness for later use, without guessing the engine's eigenvariable")
    (have!     . "you want to state an intermediate fact that follows immediately from context and continue with it -- the `we have X' step")
    (vlet      . "you need to NAME a witness or a matched subterm from the proof state, rather than navigate to it by shape")))

(define (tactic-when-of name)
  (cond ((assq name *tactic-when*) => cdr) (else #f)))

;;; --------------------------------------------------------------------
;;; *tactic-kind* -- the TRUST taxonomy, one axis orthogonal to the
;;; functional grouping above.  Grounded in what each tactic actually
;;; emits into the deduction graph (the `dg-apply-rule!' tag), NOT
;;; editorial:
;;;
;;;   rule       ONE primitive kernel inference rule -- the fixed trusted
;;;              base.  A `rule' tactic is a thin wrapper over exactly one
;;;              dg-apply-rule! tag; the set of these tags does not grow
;;;              without a kernel change (and congressional approval).
;;;   oracle     a trusted DECISION PROCEDURE run as a black box.  Sound +
;;;              complete on its domain but trusted rather than mechanised
;;;              through the axioms; each closes via its own single tag.
;;;   composite  a Scheme procedure that only CHAINS kernel rules and other
;;;              tactics -- it introduces NO new inference rule.  `emits'
;;;              names the principal kernel tags it strings together.
;;;   meta       no deduction at all: session / search / navigation.
;;;
;;; Each entry is (tactic kind emits) where `emits' is the dg-apply-rule!
;;; tag (or a list of them), or #f for meta / search.
;;; --------------------------------------------------------------------
(define *tactic-kind*
  '((sp meta #f) (qed meta #f) (save-proof meta #f) (replay-proof meta #f)
    (di rule (forall-intro implies-intro and-intro))
    (ai rule (and-elim or-elim forsome-elim))
    (pbc rule proof-by-contradiction)
    (oi-l rule or-intro-left) (oi-r rule or-intro-right)
    (ew rule forsome-intro) (ci rule cartesian-intro) (ti rule tuples-intro)
    (ii rule intersection-intro) (ui rule union-intro)
    (ni rule nn-induction) (tfi rule transfinite-induction) (tfi3 rule transfinite-induction)
    (ass rule assumption) (ta rule theorem-assumption)
    (inst rule forall-elim) (detach! rule detach) (bc rule backchain)
    (cut rule cut) (wk rule weakening)
    (ce rule cartesian-elim) (te rule tuples-elim) (ie rule intersection-elim) (ue rule union-elim)
    (mac rule macete) (macm rule macete) (mac-h rule macete-hyp)
    (subst rule eq-subst) (rfl rule reflexivity) (qrfl rule quasi-reflexivity)
    (beta rule functoid-beta) (lam-b rule lambda-beta) (lam-b-h rule lambda-beta-hyp)
    (lam-t rule lambda-type)
    (nth-r rule nth-reduce) (len-r rule length-reduce)
    (if-true rule if-true) (if-false rule if-false)
    (sep-set rule sep-sethood) (sep-mi rule sep-mem-intro) (sep-me rule sep-mem-elim)
    (comp-mi rule comp-mem-intro) (comp-me rule comp-mem-elim) (iota-d rule iota-def)
    (bu-set rule big-union-sethood) (bu-mi rule big-union-mem-intro) (bu-me rule big-union-mem-elim)
    (arith oracle arith-eval) (rs oracle ring-simplify) (crs oracle comm-ring-simplify)
    (simp oracle ring-simplify) (ineq oracle ineq) (sos oracle sos)
    (inst+ composite (forall-elim detach))
    (fact composite (theorem-assumption forall-elim detach))
    (bc* composite (backchain))
    (mac-h* composite (macete-hyp))
    (grind composite (forall-intro implies-intro macete-hyp))
    (wbc composite (theorem-assumption forsome-intro))
    ;; calc adds no rule of its own: it cuts each link, dispatches an existing
    ;; lane at it, and folds the links with the co-*-trans / eq-trans supports.
    (calc composite (cut))
    (scout meta #f) (scout-show meta #f) (scout-run composite #f)
    (minimize! composite (cut forall-intro forsome-elim))
    (obtain composite (forsome-elim))
    (have! composite cut)
    (vlet composite (cut forsome-elim))))

(define (tactic-kind-of  name)(cond ((assq name *tactic-kind*) => cadr)  (else #f)))
(define (tactic-emits-of name)(cond ((assq name *tactic-kind*) => caddr) (else #f)))
(define (tactics--of-kind kind)
  (map car (filter (lambda (x) (eq? (cadr x) kind)) *tactic-kind*)))

(define *tactic-kind-legend*
  (string-append
   "Each tactic carries a KIND -- what it contributes to the trusted base:\n"
   "  rule       a single primitive KERNEL inference rule (di, ai, cut, ni, mac,\n"
   "             subst, ...).  The set of kernel rules is FIXED.\n"
   "  oracle     a trusted DECISION PROCEDURE run as a black box (arith, rs, crs,\n"
   "             ineq, sos) -- sound+complete on its domain, but trusted.\n"
   "  composite  a Scheme procedure that only CHAINS kernel rules (fact, inst+,\n"
   "             bc*, grind, mac-h*) -- it adds NO new inference rule.\n"
   "  meta       no deduction: session / search / navigation (sp, qed, scout).\n"))

;; (tactics)            -- print the whole grouped menu (sig + one-liner).
;; (tactics 'mac-h)     -- print the long blurb for one tactic.
(define (tactics #!optional what)
  (cond
    ((default-object? what)
     (newline)
     (display "VNB interactive tactics  --  (tactics 'name) for detail\n")
     (display "========================================================\n")
     (newline)
     (display *tactic-kind-legend*)
     (newline)
     (display *tactics-arg-help*)
     (for-each
       (lambda (cat)
         (newline)
         (display (car cat)) (newline)
         (for-each
           (lambda (e)
             (display "  ") (display (car e))
             (display (make-string (max 1 (- 10 (string-length (symbol->string (car e))))) #\space))
             (display (cadr e)) (newline)
             (display "             ") (display (tactics--gloss e)) (newline)
             (let ((k (tactic-kind-of (car e))) (em (tactic-emits-of (car e))))
               (when k
                 (display "             kind: ") (display k)
                 (when (and em (not (eq? em #f))) (display "  [emits ") (write em) (display "]"))
                 (newline)))
             (let ((w (tactic-when-of (car e))))
               (when w (display "             when: ") (display w) (newline))))
           (cdr cat)))
       *tactic-help*)
     (newline))
    (else
     (let ((e (tactics--find what)))
       (cond
         (e
          (newline)
          (display (car e)) (display "   ") (display (cadr e)) (newline)
          (display (make-string (string-length (symbol->string (car e))) #\-)) (newline)
          (display (tactics--gloss e)) (newline)
          (let ((w (tactic-when-of (car e))))
            (when w (display "when: ") (display w) (newline)))
          (let ((b (tactics--blurb e)))
            (when b (newline) (display b) (newline)))
          (newline))
         ;; Fall back to *command-aux* (the REPL meta-commands: what-now,
         ;; audit-unbounded, vnb-apply?, tt, ...) -- documented there with a
         ;; (name "(sig)" "desc") entry but absent from the curated menu.
         ((assq what *command-aux*)
          => (lambda (a)
               (newline)
               (display (car a)) (display "   ") (display (cadr a)) (newline)
               (display (make-string (string-length (symbol->string (car a))) #\-)) (newline)
               (display (caddr a)) (newline) (newline)))
         (else
          (display ";; no such tactic: ") (display what)
          (display "  -- try (tactics) for the menu\n")))))))

;;; --------------------------------------------------------------------
;;; reference/TACTICS.md  (folded into the browser reference by
;;; build-reference-html.py; section headers `### name' make it navigable
;;; with the same vnb-library-mode machinery as the other indexes).
;;; --------------------------------------------------------------------

(define (write-tactics-md)
  (let ((path (string-append *reference-dir* "TACTICS.md")))
    (with-output-to-file path
      (lambda ()
        (display "# Interactive tactics\n\n")
        (display "Auto-generated by `(write-tactics-md)` from the registry in ")
        (display "`tactics-help.scm`.  These are the short-form commands you type ")
        (display "at the REPL / Scratch Workspace during a proof.  At the REPL, ")
        (display "`(tactics)` prints this menu and `(tactics 'name)` the detail.\n\n")
        (display "## Entering arguments\n\n")
        (display "```\n")
        (display *tactics-arg-help*)
        (display "```\n\n")
        ;; Trust taxonomy -- the KIND axis, orthogonal to the functional groups.
        (display "## Tactic kinds (trust taxonomy)\n\n")
        (display "Every tactic is tagged with a **kind**, grounded in the `dg-apply-rule!` ")
        (display "tag it emits (not editorial), so the trusted base is legible at a glance:\n\n")
        (for-each
          (lambda (kd)
            (display "- **") (display (car kd)) (display "** -- ")
            (display (cadr kd)) (display ": ")
            (display (apply string-append
                            (map (lambda (n)(string-append "`" (symbol->string n) "` "))
                                 (tactics--of-kind (car kd)))))
            (newline))
          '((rule "a single primitive KERNEL inference rule (the fixed trusted base)")
            (oracle "a trusted DECISION PROCEDURE run as a black box, sound+complete on its domain but trusted")
            (composite "a Scheme procedure that only CHAINS kernel rules, adding no new inference rule")
            (meta "no deduction: session / search / navigation")))
        (display "\nThe `rule` set is the fixed kernel; a proof's trust surface is exactly ")
        (display "its `rule` steps plus whichever `oracle`s and asserted premises it cites.  ")
        (display "You can read any finished proof's actual rule inventory off its deduction ")
        (display "graph (each node records its justifying rule).\n\n")
        (for-each
          (lambda (cat)
            (display "## ") (display (car cat)) (display "\n\n")
            (for-each
              (lambda (e)
                (display "### ") (display (car e)) (newline) (newline)
                (display "    ") (display (cadr e)) (newline) (newline)
                (display (tactics--gloss e)) (newline) (newline)
                (let ((k (tactic-kind-of (car e))) (em (tactic-emits-of (car e))))
                  (when k
                    (display "*Kind:* `") (display k) (display "`")
                    (when (and em (not (eq? em #f)))
                      (display " (emits `") (write em) (display "`)"))
                    (newline) (newline)))
                (let ((w (tactic-when-of (car e))))
                  (when w (display "*When useful:* ") (display w) (newline) (newline)))
                (let ((b (tactics--blurb e)))
                  (when b (display b) (newline) (newline))))
              (cdr cat)))
          *tactic-help*)))
    path))

;;; --------------------------------------------------------------------
;;; emacs/vnb-commands.lisp  --  the COMPLETION catalog, generated.
;;;
;;; vnb-complete.el (M-x vnb-insert-command) reads a single sexp:
;;;   ((name (arg ...) "description") ...)
;;; It used to be a hand-maintained .lisp file that drifted badly from the
;;; live command set (missing bc*/crs/fact/sep-*/subst/... ; carrying renamed
;;; ghosts).  Now it is GENERATED from this registry plus `*command-aux*', so
;;; the button/M-x surface and the (tactics) menu can never diverge again.
;;;
;;; `*command-aux*' holds live commands the curated menu does not list but
;;; completion should still offer: genuine tactics the menu just omits
;;; (spec/tfi -- candidates to promote into *tactic-help*), plus wff/term
;;; constructors and REPL utilities.  Same entry shape as the menu.
;;; --------------------------------------------------------------------

(define *command-aux*
  '(;; --- proof tactics not (yet) in the curated menu ---
    (spec "(spec instance struct is-thm)" "Specialize: bring the axioms of structure instance `instance' into context as `struct', justified by its IS-STRUCT theorem `is-thm'.")
    (tfi  "(tfi)"         "Transfinite induction: on a goal (FORALL v. v in ORD => P) reduce to the ordinal induction step.")
    (tfi3 "(tfi3)"        "Transfinite induction, 3-case variant (zero / successor / limit) of `tfi'.")
    ;; --- wff / term constructors ---
    (fa   "(fa bindings body)" "Build a FORALL wff: each binding is (x), (x IN A), or (IN x A); nests right over `body'.")
    (fs   "(fs bindings body)" "Build a FORSOME wff: existential companion to `fa'.")
    ;; --- REPL utilities ---
    (pp   "(pp wff)"      "Pretty-print a wff / term in surface syntax.")
    (make-wff-from-string "(make-wff-from-string str)" "Parse a surface-syntax string into a <wff> object.")
    (parse-string "(parse-string str)" "Parse a surface-syntax string into a raw S-expression.")
    (find-mac "(find-mac substr)" "Search the rewrite-rule pool for names containing SUBSTR; tags the rules that fire on the current goal. The s-expr-surface counterpart to `mac' name completion.")
    (find-thm "(find-thm substr)" "Search the full theorem pool for names containing SUBSTR; tags the lemmas that backchain the current goal. Counterpart to `bc*'/`ta' name completion.")
    (audit-unbounded "(audit-unbounded)" "Library-hygiene scan: list every installed theorem/axiom whose statement has an UNBOUNDED universal variable (never typed by an (IN v D)) feeding a PARTIAL term under a strict `=' in assertion position -- i.e. it quietly asserts `undefined = undefined' off-domain (VNB `=' is partial).  Category A = arithmetic partial ops; B = function application / structure ops.  Predicate (`iff') definitions are excluded.")
    (things-to-try "(things-to-try)" "Alias (tt).  Unified \"what can I do here?\" menu for the current focus: aggregates the shape-based tactic checks (closers ass/rfl/crs/rs/arith/ineq, decomposition di, simplifiers simp, the to-binary/to-nary surface bridges) with the index-driven rewrite-macete and backchain-lemma suggesters and the forward-move scan. Advice only -- nothing is applied.")
    (what-now "(what-now)" "Proof copilot, first pass: for the OPEN SUBGOAL, classify the goal kind and name the right LANE -- (rfl)/(arith)/(crs) for an equality, the (bc* 'name) backchain lemmas whose CONCLUSION fingerprints to the goal otherwise (most-specific first, each shown with the conclusion it applies and a hint when bc* needs bindings), the hypotheses (mac-h*) would crack open, and the (inst+ assumption-# term) universals worth instantiating at a context-typed witness (the same ranked candidates scout's inst lane tries -- so the single-move and search copilots agree). A clean surface over (suggest-backchain). ALSO RETURNS the moves as a list of runnable tactic forms (e.g. ((di) (crs) (rs)), ((bc* 'n) ...), ((inst+ 3 'x) ...)) for an automated try-each tactic. No rewrite (mac) lane, no AC yet.")
    (vnb-apply? "(vnb-apply? 'name goal . args)" "Applicability PROBE for a tactic.  Does surface tactic `name' (given any extra `args' it takes) FIRE on `goal' -- a \"string\" / S-expr / wff (the assertion), or a full sequent to supply assumptions?  Runs the REAL tactic on a throwaway scratch deduction graph (the live *ps* is NEVER touched) and returns 'CLOSED (closes outright), a list of the new open subgoal formulas (fires, leaving these), or #f (does not apply).  The executable form of each tactic's `when:' note; (what-now) uses it to list which parameterless tactics fire on the live goal.  E.g. (vnb-apply? 'sos \"forall([x in rr,y in rr], x*y <= x*x+y*y)\" \"x - y\" \"x\" \"y\") => CLOSED.")
    (to-binary "(to-binary)" "Saturating one-shot rewrite of the goal's kiddie n-ary +/*/- onto the binary structure operators binplus/bintimes/binneg (= the (ADD s)/(MUL s)/(NEG s) slots of ZZ/QQ-RING and RR/CC-NORMED-FIELD), so a structure-level theorem can match. Unconditional (definitional bridge). Arities 2..5.")
    (to-nary "(to-nary)" "Inverse of to-binary: rewrite binplus/bintimes/binneg back to everyday +/*/-.")))

;;; Does string S contain character CH?  (avoid leaning on srfi string-index)
(define (vnb-cmd--str-has-char? s ch)
  (let loop ((i 0))
    (cond ((>= i (string-length s)) #f)
          ((char=? (string-ref s i) ch) #t)
          (else (loop (+ i 1))))))

;;; Drop the #f elements of a list.
(define (vnb-cmd--keep lst)
  (cond ((null? lst) '())
        ((car lst) (cons (car lst) (vnb-cmd--keep (cdr lst))))
        (else (vnb-cmd--keep (cdr lst)))))

;;; Split STR into tokens at whitespace, but only at paren/bracket depth 0,
;;; so a nested form like '(= s t) or [((v val)...)] stays one token.
(define (vnb-cmd--top-tokens str)
  (let loop ((i 0) (depth 0) (start #f) (acc '()))
    (if (>= i (string-length str))
        (reverse (if start (cons (substring str start i) acc) acc))
        (let ((c (string-ref str i)))
          (cond
            ((or (char=? c #\() (char=? c #\[))
             (loop (+ i 1) (+ depth 1) (or start i) acc))
            ((or (char=? c #\)) (char=? c #\]))
             (loop (+ i 1) (- depth 1) (or start i) acc))
            ((and (char-whitespace? c) (= depth 0))
             (loop (+ i 1) depth #f
                   (if start (cons (substring str start i) acc) acc)))
            (else
             (loop (+ i 1) depth (or start i) acc)))))))

;;; Keep only identifier characters (a-z 0-9 -) of S.  Used to guarantee the
;;; emitted arg symbol is readable by BOTH MIT Scheme and Emacs Lisp -- the
;;; latter has no |...| bar-escaping, so a symbol whose name carries a quote or
;;; bracket (e.g. from a sloppy `["term"]' signature) would make the generated
;;; vnb-commands.lisp UNREADABLE and abort the launcher's whole init.
(define (vnb-cmd--ident-sanitize s)
  (list->string
    (filter (lambda (c)
              (or (char-alphabetic? c) (char-numeric? c) (char=? c #\-)))
            (string->list s))))

;;; Normalise one argument token to a bare arg symbol, or #f to drop it.
;;; Strips [ ] optional markers, a leading quote, and surrounding "double
;;; quotes"; a nested form collapses to the generic kind `formula'; a `...'
;;; rest marker is dropped.  The final name is sanitised to identifier chars so
;;; it is always cleanly readable (no bar-escaping) -- a malformed help
;;; signature must never be able to wedge the Emacs launcher's catalog load.
(define (vnb-cmd--norm-arg tok)
  (let ((t tok))
    (when (and (> (string-length t) 1)
               (char=? (string-ref t 0) #\[)
               (char=? (string-ref t (- (string-length t) 1)) #\]))
      (set! t (substring t 1 (- (string-length t) 1))))
    (when (and (> (string-length t) 0) (char=? (string-ref t 0) #\'))
      (set! t (substring t 1 (string-length t))))
    (when (and (> (string-length t) 1)
               (char=? (string-ref t 0) #\")
               (char=? (string-ref t (- (string-length t) 1)) #\"))
      (set! t (substring t 1 (- (string-length t) 1))))
    (cond
      ((string=? t "") #f)
      ((string=? t "...") #f)
      ((or (vnb-cmd--str-has-char? t #\()
           (vnb-cmd--str-has-char? t #\[)) 'formula)
      ;; downcase + keep only identifier chars (MIT symbols read case-folded);
      ;; drop the token if nothing clean remains.  Display hints only.
      (else (let ((clean (vnb-cmd--ident-sanitize (string-downcase t))))
              (and (> (string-length clean) 0) (string->symbol clean)))))))

;;; Derive a vnb-commands.lisp arglist from a registry signature string,
;;; e.g. "(mac 'name)" -> (name), "(ce hyp k)" -> (hyp k), "(di)" -> ().
(define (vnb-cmd--sig->arglist sig)
  (let* ((n (string-length sig))
         (inner (if (and (> n 1)
                         (char=? (string-ref sig 0) #\()
                         (char=? (string-ref sig (- n 1)) #\)))
                    (substring sig 1 (- n 1))
                    sig))
         (toks (vnb-cmd--top-tokens inner)))
    (if (null? toks)
        '()
        (vnb-cmd--keep (map vnb-cmd--norm-arg (cdr toks))))))

;;; Flat list of (name (arg ...) "gloss") from menu registry ++ aux.
(define (vnb-cmd--all-commands)
  (map (lambda (e)
         (list (car e) (vnb-cmd--sig->arglist (cadr e)) (tactics--gloss e)))
       (append (tactics--all-entries) *command-aux*)))

(define (write-vnb-commands)
  (let ((path (string-append *reference-dir* "../emacs/vnb-commands.lisp")))
    (with-output-to-file path
      (lambda ()
        (display ";;; vnb-commands.lisp -- machine-readable VNB command registry\n")
        (display ";;;\n")
        (display ";;; GENERATED by (write-vnb-commands) from `*tactic-help*' +\n")
        (display ";;; `*command-aux*' in tactics-help.scm.  DO NOT EDIT BY HAND --\n")
        (display ";;; edit the registry and reload; the writer runs on load.\n")
        (display ";;;\n")
        (display ";;; Format: (command-name (arg ...) \"description\")\n")
        (display ";;; Read by emacs/vnb-complete.el: (read) the whole list.\n\n")
        (display "(\n")
        (for-each
          (lambda (c)
            (write c) (newline))
          (vnb-cmd--all-commands))
        (display ")\n")))
    path))
