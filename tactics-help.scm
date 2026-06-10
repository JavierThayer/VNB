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
     (sp   "(sp wff)"        "Start a proof of wff (a \"string\" or raw S-expr); clears the script.")
     (qed  "(qed 'name)"     "Install the finished proof as theorem `name' and save its replayable script.")
     (save-proof   "(save-proof 'name)"   "Save the current script under a name without finishing.")
     (replay-proof "(replay-proof 'name [subst])"
       "Re-run a saved script on the current goal, optionally renaming free vars."
       "The optional subst is an alist ((old . new) ...) applied to every command argument before replay -- this is how one proof is reused at fresh eigenvariables."))

    ("Decomposing the goal"
     (di   "(di)"   "Direct inference: split an AND goal, move an IMPLIES antecedent into the assumptions, or introduce a fresh eigenvariable for a leading FORALL."
       "The goal-side workhorse.  Pairs with `mac' (which unfolds a defined predicate in the goal).  After `(di)' on an implication the antecedent becomes a new assumption and the focus is the consequent.")
     (pbc  "(pbc)"  "Proof by contradiction: assume the goal's negation, prove FALSITY.")
     (oi-l "(oi-l)" "OR-intro left: reduce an (OR a b) goal to a.")
     (oi-r "(oi-r)" "OR-intro right: reduce an (OR a b) goal to b.")
     (ew   "(ew term)" "Existential witness: discharge a FORSOME goal by supplying the witness term.")
     (ci   "(ci)"   "Cartesian intro: prove a CARTESIAN-product membership component-wise.")
     (ti   "(ti)"   "Tuple intro: prove a tuple/LIST membership component-wise.")
     (ii   "(ii)"   "Intersection intro: prove (IN x (INTERSECTION ...)) for each branch.")
     (ni   "(ni)"   "Natural-number induction on the goal's leading FORALL over NN."))

    ("Using a hypothesis"
     (ai   "(ai hyp)" "Antecedent inference: decompose a cited assumption -- AND-split, OR-into-cases, or FORSOME-elimination to a fresh eigenvariable."
       "The hypothesis-side dual of `di'.  `hyp' may be the raw formula, a \"string\", or a 1-based assumption index from the Focus display.")
     (ass  "(ass)"  "Close the goal by an assumption alpha-equivalent to it.")
     (inst "(inst forall-hyp term)" "Instantiate a universally-quantified assumption at `term', adding the instance to context.")
     (ce   "(ce hyp k)" "Cartesian elim: project the k-th component out of a CARTESIAN-membership assumption.")
     (te   "(te hyp k)" "Tuple elim: project the k-th component out of a tuple-membership assumption.")
     (ie   "(ie hyp k)" "Intersection elim: extract the k-th branch of an INTERSECTION-membership assumption."))

    ("Rewriting"
     (mac   "(mac 'name)" "Rewrite the GOAL with an equivalence macete (unfold a definition, apply an iff/=/== law).  Fires only where the macete's side-conditions already hold in context."
       "All-or-nothing by design: where a conditional macete's side-conditions are NOT discharged from context, `mac' declines at that position and recurses into subterms rather than spawning goals.  The IMPS `apply-macete-with-minor-premises' behaviour -- fire on the GOAL regardless and leave the unmet conditions as new goals -- is a separate, planned goal-side command (`mac+'), not yet built.  (`mac-h' already spawns such conditions, but it acts on a hypothesis, not the goal.)")
     (mac-h "(mac-h 'name hyp)" "Rewrite a cited ASSUMPTION in place with an equivalence macete; any side-condition not already in context is spawned as a new subgoal."
       "The hypothesis-side dual of `mac': where `mac' rewrites the goal, `mac-h' rewrites inside a cited assumption, replacing H by an equivalent H'.  Sound by the Leibniz substitution of equivalents -- valid because the macete is a genuine equivalence under its side-conditions, any of which not already in context is spawned as a new goal (so nothing is left assumed-but-undischarged).  NB this is NOT IMPS's `apply-macete-with-minor-premises', which rewrites the GOAL and adds unmet hypotheses as goals; `mac-h' is its hypothesis-side cousin, not the same command.")
     (subst "(subst '(= s t))" "Rewrite s -> t throughout the goal, using an equation s = t that is in context (Leibniz substitution).")
     (beta  "(beta)"  "Beta-reduce a functoid application in the goal.")
     (nth-r "(nth-r)" "Reduce an NTH applied to a literal LIST in the goal.")
     (rfl   "(rfl)"   "Close a reflexive equality goal (t = t).")
     (qrfl  "(qrfl)"  "Quasi-reflexivity: close t = t under the partial-equality definedness reading."))

    ("Arithmetic & ring oracles"
     (arith "(arith)" "Discharge a ground arithmetic goal by evaluation.")
     (rs    "(rs)"    "Ring-simplify the goal (normal form over the ambient ring).")
     (crs   "(crs)"   "Commutative-ring decision procedure: prove a polynomial identity over ZZ[generators]."))

    ("Backchaining with a theorem"
     (ta  "(ta 'name)" "Theorem-assumption: bring the named installed theorem into context as an assumption.")
     (bc  "(bc impl)"  "Backchain the goal through an (IMPLIES A B) already in context: if the goal matches B, the new goal is A.")
     (bc* "(bc* 'thm [((v val)...)] h1 h2 ...)"
       "Matching backchain: unify the theorem's conclusion against the goal, then leave its (instantiated) antecedents as subgoals; optional handlers hk run on the k-th subgoal."
       "Peels leading FORALLs and right-nested IMPLIES, matches the conclusion, and replays the ta/inst/cut/bc idiom automatically.  Schema vars not pinned by the match are supplied as ((v val) ...).  Without handlers it focuses the first subgoal; with handlers it refocuses to each subgoal in tree order."))

    ("Lambda, comprehension & description"
     (lam-t  "(lam-t)" "VNB-LAMBDA typing: reduce (IN (VNB-LAMBDA ...) (FUN A B)) to its body obligation.")
     (lam-b  "(lam-b)" "VNB-LAMBDA beta: reduce an applied lambda to its substituted body.")
     (sep-set "(sep-set)" "Separation sethood: the separation set {x in A | p} is a set.")
     (sep-mi  "(sep-mi)"  "Separation membership intro: prove (IN t {x in A | p}).")
     (sep-me  "(sep-me hyp)" "Separation membership elim: split a separation-membership assumption into A-membership and the predicate.")
     (comp-mi "(comp-mi)" "Comprehension membership intro.")
     (comp-me "(comp-me hyp)" "Comprehension membership elim.")
     (iota-d  "(iota-d term)" "Definite-description: discharge the IOTA uniqueness obligation for `term'.")
     (bu-set  "(bu-set)" "Big-union sethood.")
     (bu-mi   "(bu-mi w)" "Big-union membership intro via the index witness w.")
     (bu-me   "(bu-me hyp)" "Big-union membership elim."))

    ("Conditional terms"
     (if-true  "(if-true t)"  "Reduce an (IF p a b) term on the p branch: spawns p as a subgoal; the continuation gains (= (IF p a b) a).")
     (if-false "(if-false t)" "Reduce an (IF p a b) term on the not-p branch: spawns (NOT p); the continuation gains (= (IF p a b) b)."))

    ("Navigation, display & tacticals"
     (focus  "(focus n)"  "Switch the focus to the n-th open goal (1-based).")
     (show   "(show)"     "Redisplay the current proof state.")
     (goal-status "(goal-status)" "One-line summary: done / N open goals.")
     (repeat "(repeat thunk [cap])" "Run thunk until it stops changing the proof state (LCF REPEAT).")
     (orelse "(orelse t1 t2 ...)" "Run thunks in order, stop at the first that makes progress (LCF ORELSE).")
     (quietly "(quietly thunk)" "Run thunk with state-dump output suppressed; returns its value."))

    ("Forward-reasoning idioms  [proof-local -- NOT yet surface tactics]"
     (detach!         "(detach! impl)" "Forward modus ponens on a local (IMPLIES A B) whose A is in context: leaves B in context."
       "Currently defined inline at the top of calculus/prop-3-14-proof.scm and copy-pasted into prop-3-15-proof.scm -- it is NOT loaded as a surface command.  Promoting these helpers to a shared tactics file is an open agenda item; until then they exist only inside those proof scripts.")
     (cut-mem!        "(cut-mem! mem A)" "Prove a membership (IN (f x) B) by fun-apply-type with domain A, leaving it in context.  [proof-local]")
     (metric-sym-eq!  "(metric-sym-eq! S P Q)" "Add (= ((D S) P Q) ((D S) Q P)) to context via the metric-sym axiom.  [proof-local]")
     (focus-leaf!     "(focus-leaf! substr)" "Focus the frontier leaf whose goal contains substr (never trust auto-advance).  [proof-local]")
     (split-ands!     "(split-ands!)" "Flatten every AND assumption of the focus into separate assumptions.  [proof-local]")
     (ass-all-frontier! "(ass-all-frontier!)" "Close every frontier leaf whose goal is already among its assumptions.  [proof-local]"))))

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

;; (tactics)            -- print the whole grouped menu (sig + one-liner).
;; (tactics 'mac-h)     -- print the long blurb for one tactic.
(define (tactics #!optional what)
  (cond
    ((default-object? what)
     (newline)
     (display "VNB interactive tactics  --  (tactics 'name) for detail\n")
     (display "========================================================\n")
     (for-each
       (lambda (cat)
         (newline)
         (display (car cat)) (newline)
         (for-each
           (lambda (e)
             (display "  ") (display (car e))
             (display (make-string (max 1 (- 10 (string-length (symbol->string (car e))))) #\space))
             (display (cadr e)) (newline)
             (display "             ") (display (tactics--gloss e)) (newline))
           (cdr cat)))
       *tactic-help*)
     (newline))
    (else
     (let ((e (tactics--find what)))
       (if (not e)
           (begin (display ";; no such tactic: ") (display what)
                  (display "  -- try (tactics) for the menu\n"))
           (begin
             (newline)
             (display (car e)) (display "   ") (display (cadr e)) (newline)
             (display (make-string (string-length (symbol->string (car e))) #\-)) (newline)
             (display (tactics--gloss e)) (newline)
             (let ((b (tactics--blurb e)))
               (when b (newline) (display b) (newline)))
             (newline)))))))

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
        (for-each
          (lambda (cat)
            (display "## ") (display (car cat)) (display "\n\n")
            (for-each
              (lambda (e)
                (display "### ") (display (car e)) (newline) (newline)
                (display "    ") (display (cadr e)) (newline) (newline)
                (display (tactics--gloss e)) (newline) (newline)
                (let ((b (tactics--blurb e)))
                  (when b (display b) (newline) (newline))))
              (cdr cat)))
          *tactic-help*)))
    path))
