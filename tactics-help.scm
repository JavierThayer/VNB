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
     (detach! "(detach! impl)" "Forward modus ponens: from an in-context (IMPLIES A B) whose A is also in context, leave B in context."
       "The forward dual of `bc' -- it grows the CONTEXT instead of the goal.  Sound (A and A=>B give B).  Realised by the kernel rule pi-detach!.")
     (fact "(fact 'thm term ...)" "Forward APPLICATION of a theorem: bring it in, instantiate its leading universals with the terms, and auto-detach every antecedent already in context, landing the consequent as a hypothesis."
       "Handles interleaved forall/implies (e.g. forall s. IS-X(s) => forall a. a in A(s) => P): consumes one term per FORALL, detaches each IMPLIES whose antecedent is in context.  The forward-assembly workhorse -- a law `forall x. H(x) => P(x)' becomes the usable fact P in one call, instead of ta + inst* + cut/backchain.  See theorem-library/module-zero-act.scm.")
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
     ;; detach! was promoted to a real surface tactic (see "Using a hypothesis"),
     ;; backed by the kernel rule pi-detach!; `fact' is built on it.
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
;;; (cut/wk/ui/ue/spec/tfi -- candidates to promote into *tactic-help*), plus
;;; wff/term constructors and REPL utilities.  Same entry shape as the menu.
;;; --------------------------------------------------------------------

(define *command-aux*
  '(;; --- proof tactics not (yet) in the curated menu ---
    (cut  "(cut formula)" "Cut: prove `formula' as a side subgoal, then continue with it added to context (Gentzen cut).")
    (wk   "(wk hyp)"      "Weaken: drop a cited assumption from the context.")
    (ui   "(ui k)"        "Union intro: prove (IN x (UNION a b)) via branch k (1 = left, 2 = right).")
    (ue   "(ue hyp)"      "Union elim: split a (IN x (UNION a b)) assumption into its two cases.")
    (spec "(spec instance struct is-thm)" "Specialize: bring the axioms of structure instance `instance' into context as `struct', justified by its IS-STRUCT theorem `is-thm'.")
    (tfi  "(tfi)"         "Transfinite induction: on a goal (FORALL v. v in ORD => P) reduce to the ordinal induction step.")
    (tfi3 "(tfi3)"        "Transfinite induction, 3-case variant (zero / successor / limit) of `tfi'.")
    ;; --- wff / term constructors ---
    (fa   "(fa bindings body)" "Build a FORALL wff: each binding is (x), (x IN A), or (IN x A); nests right over `body'.")
    (fs   "(fs bindings body)" "Build a FORSOME wff: existential companion to `fa'.")
    ;; --- REPL utilities ---
    (pp   "(pp wff)"      "Pretty-print a wff / term in surface syntax.")
    (calc "(calc term)"   "Evaluate a ground term and print the result.")
    (make-wff-from-string "(make-wff-from-string str)" "Parse a surface-syntax string into a <wff> object.")
    (parse-string "(parse-string str)" "Parse a surface-syntax string into a raw S-expression.")))

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

;;; Normalise one argument token to a bare arg symbol, or #f to drop it.
;;; Strips [ ] optional markers and a leading quote; a nested form collapses
;;; to the generic kind `formula'; a `...' rest marker is dropped.
(define (vnb-cmd--norm-arg tok)
  (let ((t tok))
    (when (and (> (string-length t) 1)
               (char=? (string-ref t 0) #\[)
               (char=? (string-ref t (- (string-length t) 1)) #\]))
      (set! t (substring t 1 (- (string-length t) 1))))
    (when (and (> (string-length t) 0) (char=? (string-ref t 0) #\'))
      (set! t (substring t 1 (string-length t))))
    (cond
      ((string=? t "") #f)
      ((string=? t "...") #f)
      ((or (vnb-cmd--str-has-char? t #\()
           (vnb-cmd--str-has-char? t #\[)) 'formula)
      ;; downcase placeholder names so `write' need not bar-escape them
      ;; (MIT symbols read case-folded); these are display hints only.
      (else (string->symbol (string-downcase t))))))

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
