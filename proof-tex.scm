;;; proof-tex.scm -- render a completed proof as a LaTeX step-trace.
;;;
;;; The IMPS-style "print the proof" facility: replay a proof recorded this
;;; session (it lives in *session-log* as (name goal script)) one tactic at a
;;; time, capture the focus goal after each step, and typeset the whole thing
;;; as a numbered derivation -- each row is the tactic applied and the goal it
;;; leaves.  Formulas go through expr->tex (tex-output.scm).
;;;
;;; Public entry points:
;;;   (proof-tex name)            -> the LaTeX document as a string
;;;   (write-proof-tex name path) -> writes path, returns path
;;;   (view-proof-pdf name)       -> write + pdflatex + open (best-effort)
;;;
;;; Loaded after tex-output.scm (needs expr->tex) and interactive.scm (needs
;;; the replay machinery: apply-recorded-cmd!, quietly, *replaying?*,
;;; *session-log*, proof-done?, proof-state-focus).

;;; --- replay with per-step capture ------------------------------------

(define (proof-tex--record name)
  (let loop ((rs *session-log*))
    (cond ((null? rs) #f)
          ((eq? (caar rs) name) (car rs))
          (else (loop (cdr rs))))))

(define (proof-tex--focus-goal)
  (if (proof-done? *ps*)
      #f
      (wff-formula (sequent-node-assertion (proof-state-focus *ps*)))))

;; The focus node's assumptions, as raw formulas (1-indexed to match the
;; assumption-by-number args that ai/inst/sep-me/... accept, e.g. (ai 2)).
(define (proof-tex--focus-asms)
  (if (proof-done? *ps*)
      '()
      (map wff-formula (sequent-node-assumptions (proof-state-focus *ps*)))))

;; The focus node's display number (the bracketed [k] of the state display),
;; or #f when the proof is complete.
(define (proof-tex--focus-id)
  (if (proof-done? *ps*)
      #f
      (sequent-node-number (proof-state-focus *ps*))))

;; The display numbers of all currently-open goals.
(define (proof-tex--open-ids)
  (map sequent-node-number (proof-open-goals *ps*)))

;; A recorded command's argument, rendered exactly as you would TYPE it in a
;; proof script so the step is reproducible:
;;   - a symbol (theorem/macete NAME, witness) is a QUOTED SYMBOL -- `'name' --
;;     because that is how it is passed, e.g. (fact 'null-rr-seq-exists) (a name
;;     must stay a symbol: cmd-fact looks it up by `symbol?', so a string fails);
;;   - a number (assumption index) is verbatim, e.g. (ai 2);
;;   - a formula / term is a QUOTED S-EXPRESSION -- `'(forsome rad ...)' -- the
;;     recorded internal form (lowercase, the reader case-folds), which
;;     ->raw-formula passes through UNCHANGED.  We do NOT render it as the
;;     surface string "forsome([rad], ...)": although prettier, surface does not
;;     round-trip (it reparses with a canonicalised binder, ((rad)) vs rad), so
;;     the quoted s-expr is the only form that names the SAME assumption `ai'
;;     actually decomposed.  Still not an opaque `...' -- you see the term;
;;   - the empty list (e.g. fact's no-arg tail) contributes nothing.
(define (proof-tex--arg-short a)
  (cond ((symbol? a) (string-append "'" (symbol->string a)))
        ((number? a) (number->string a))
        ((string? a) (string-append "\"" a "\""))
        ((null? a)   #f)                            ; render nothing
        ((pair? a)   (string-append "'" (call-with-output-string
                                          (lambda (p) (write a p)))))
        (else        (call-with-output-string (lambda (p) (write a p))))))

(define (proof-tex--cmd-label entry)
  (string-append
   "(" (symbol->string (car entry))
   (apply string-append
          (map (lambda (a)
                 (let ((s (proof-tex--arg-short a)))
                   (if s (string-append " " s) "")))   ; skip #f (empty-list) args
               (cdr entry)))
   ")"))

;; Replay the proof, capturing for each step a (label goal-or-#f asms) triple
;; (asms = the focus node's assumption formulas).  Returns a 5-list:
;;   (goal  steps  cmds  syms  heads)
;; where cmds is the de-duped set of tactic names used (for the tactic
;; glossary), syms every symbol that appears in any goal/assumption, and heads
;; every symbol used as an application head (for the notation glossary).
;; Build the proof-tex 5-list from a LIVE capture (interactive.scm's
;; *proof-live-trace*, snapshot as the proof actually ran) -- no replay, so
;; forward-`fact' proofs that defeat replay render faithfully.  Each live record
;; is (entry goal asms focus-id open-ids); new-ids = this step's open-ids minus
;; the previous step's.  Returns the same 5-list as proof-tex--steps, or #f when
;; no live capture exists for NAME (then the caller falls back to replay).
(define (proof-tex--steps-from-live name)
  (let ((trace (hash-table-ref/default *proof-live-trace* name #f)))
    (and (pair? trace)
         (let ((goal (cadr (car trace)))      ; sp record's focus goal = the claim
               (steps '()) (cmds '()) (forms '()) (prev '()))
           (for-each
            (lambda (rec)
              (let* ((entry (car rec)) (g (cadr rec)) (a (caddr rec))
                     (fid (cadddr rec)) (open (list-ref rec 4))
                     (added (sort (filter (lambda (k) (not (memv k prev))) open) <))
                     (label (if (eq? (car entry) 'sp) "sp" (proof-tex--cmd-label entry)))
                     ;; the oracle certificates the step recorded (6th field,
                     ;; interactive.scm's vnb--capture-step!); absent on old records
                     (certs (if (> (length rec) 5) (list-ref rec 5) '())))
                (set! prev open)
                (set! steps (cons (list label g a fid added
                                        (proof-tex--certs-text certs))
                                  steps))
                (set! cmds  (cons (car entry) cmds))
                (set! forms (append (if g (list g) '()) a forms))))
            trace)
           (let ((allforms (cons goal forms)))
             (list goal
                   (reverse steps)
                   (proof-tex--dedupe (reverse cmds))
                   (proof-tex--dedupe (apply append (map proof-tex--syms allforms)))
                   (proof-tex--dedupe (apply append (map proof-tex--heads allforms)))))))))

;;; -----------------------------------------------------------------------
;;; ORACLE CERTIFICATES ON THE PAGE (2026-09-25, the user's decision).
;;;
;;; An `ineq' step closes its node by a FARKAS certificate: a nonnegative
;;; combination of the numbered premises and of the negated goal whose sum has no
;;; atoms left and is an absurd constant inequality (manual, docs/ch-proofs.tex,
;;; the ineq paragraph).  The rule tag carries it (ineq-oracle.scm) and the live
;;; trace keeps it with the premises of the node it closed.  Rendered as
;;;
;;;     by ineq: 2 * (1) + 1 * (3) + 1 * (not goal) gives 0 < 0
;;;       where (1) is x <= y; (3) is y < z; (not goal) is z <= x
;;;
;;; (I) is the I-th assumption of the node closed -- the numbering `(ineq 1 3)'
;;; itself uses; (I, reversed) is an equation premise read right to left.  For an
;;; equation goal there are two combinations, one per direction.  The constant is
;;; computed with the rule checker's own linear arithmetic (rule-checkers-oracle.scm),
;;; so what is printed is what was verified.  An `sos' step prints its squares
;;; and weights:  by sos: b - a = 1 * (x - y)^2 + 2 * (x)^2.
(define (proof-tex--ineq-id-text id)
  (let ((k (rco--ineq-id id)))
    (cond ((eq? k 'goal) "(not goal)")
          ((pair? k) (string-append "(" (number->string (car k))
                                    (if (eq? (cdr k) 'rev) ", reversed" "") ")"))
          (#t (expression->string id)))))

(define (proof-tex--num-text q)
  (if (and (exact? q) (integer? q)) (number->string q) (string-append "(" (number->string q) ")")))

;;; One combination: its text, and (k . strict?) of `sum <= / < 0'.
(define (proof-tex--farkas-one cert asms neg gtext)
  (let loop ((cs cert) (acc (rco--l-zero)) (strict #f) (terms '()) (used '()))
    (if (null? cs)
        (let ((k (rco--l-k acc)))
          (string-append
           (if (null? terms) "0" (proof-tex--join (reverse terms) " + "))
           " gives " (number->string k) (if strict " < 0" " <= 0")
           (if (null? used)
               ""
               (string-append "  where "
                              (proof-tex--join (reverse used) "; ")))))
        (let* ((id (caar cs)) (m (cdar cs))
               (c (rco--ineq-constraint id asms neg))
               (k (rco--ineq-id id))
               (what (cond ((eq? k 'goal) (string-append "(not goal) is not(" gtext ")"))
                           ((and (pair? k) (<= (car k) (length asms)))
                            (string-append (proof-tex--ineq-id-text id) " is "
                                           (expression->string (list-ref asms (- (car k) 1)))))
                           (#t #f))))
          (if (or (string? c) (= m 0))
              (loop (cdr cs) acc strict terms used)
              (loop (cdr cs)
                    (rco--l-add acc (rco--l-scale (car c) m))
                    (or strict (cdr c))
                    (cons (string-append (proof-tex--num-text m) " * "
                                         (proof-tex--ineq-id-text id))
                          terms)
                    (if (and what (not (member what used))) (cons what used) used)))))))

;;; The note for one (TAG CERT ASMS GOAL) record, or #f.
(define (proof-tex--cert-text rec)
  (let ((tag (car rec)) (cert (cadr rec)) (asms (caddr rec)) (goal (cadddr rec)))
    (cond
      ((eq? tag 'ineq)
       (let* ((peel (rco--peel-rr goal))
              (gpr  (rco--lin-rel (car peel)))
              (gtext (expression->string (car peel))))
         (cond
           ((not gpr) (string-append "by ineq: certificate " (expression->string cert)))
           ((eq? (cdr gpr) 'eq)
            (let ((L (car gpr)))
              (string-append
               "by ineq: (<=) " (proof-tex--farkas-one (car cert) asms (cons (rco--l-neg L) #t) gtext)
               "; (>=) " (proof-tex--farkas-one (cdr cert) asms (cons L #t) gtext))))
           (#t
            (let ((L (car gpr)))
              (string-append
               "by ineq: "
               (proof-tex--farkas-one cert asms
                                      (if (eq? (cdr gpr) 'le)
                                          (cons (rco--l-neg L) #t)
                                          (cons (rco--l-neg L) #f))
                                      gtext)))))))
      ((eq? tag 'sos)
       (let* ((peel (rco--peel-rr goal)) (g (car peel)))
         (string-append
          "by sos: "
          (if (and (pair? g) (= (length g) 3))
              (string-append (expression->string (list '- (caddr g) (cadr g))) " = ")
              "")
          (proof-tex--join
           (map (lambda (p) (string-append (proof-tex--num-text (cdr p)) " * ("
                                           (expression->string (car p)) ")^2"))
                cert)
           " + "))))
      (#t #f))))

(define (proof-tex--certs-text certs)
  (let ((ts (filter (lambda (x) x)
                    (map (lambda (r) (call-with-current-continuation
                                      (lambda (k)
                                        (with-exception-handler
                                         (lambda (e) (k #f))
                                         (lambda () (proof-tex--cert-text r))))))
                         certs))))
    (and (pair? ts) (proof-tex--join ts " / "))))

(define (proof-tex--steps name)
  (or (proof-tex--steps-from-live name)        ; prefer the live capture
      (proof-tex--steps-by-replay name)))

(define (proof-tex--steps-by-replay name)
  (let ((rec (proof-tex--record name)))
    (if (not rec)
        (error "proof-tex: no proof named this in *session-log* (proofs run this session)" name)
        (let ((goal (cadr rec)) (script (caddr rec))
              (acc '()) (forms '()) (cmds (list 'sp)) (prev '()))
          ;; nodes opened by THIS step = open-now minus open-before.
          (define (new-ids)
            (let ((now (proof-tex--open-ids)))
              (let ((added (filter (lambda (k) (not (memv k prev))) now)))
                (set! prev now)
                (sort added <))))
          (quietly
           (lambda ()
            ;; Restore the fresh-var counter to the proof's sp-time value so
            ;; eigenvariables (ai/ew witnesses) replay to the SAME names the
            ;; recorded args pin.  fluid-let restores it afterward, preserving
            ;; the global monotonic invariant outside this read-only replay.
            (fluid-let ((*fresh-counter*
                         (hash-table-ref/default *proof-start-counter* name *fresh-counter*)))
             (sp (make-wff goal))
             (let ((g (proof-tex--focus-goal)) (a (proof-tex--focus-asms))
                   (fid (proof-tex--focus-id)) (nw (new-ids)))
               (set! acc (list (list "sp" g a fid nw)))
               (set! forms (append (if g (list g) '()) a forms)))
             (fluid-let ((*replaying?* #t))
               (for-each
                (lambda (entry)
                  (apply-recorded-cmd! (car entry) (cdr entry))
                  (set! cmds (cons (car entry) cmds))
                  (let ((g (proof-tex--focus-goal)) (a (proof-tex--focus-asms))
                        (fid (proof-tex--focus-id)) (nw (new-ids)))
                    (set! acc (cons (list (proof-tex--cmd-label entry) g a fid nw) acc))
                    (set! forms (append (if g (list g) '()) a forms))))
                script)))))
          (let ((allforms (cons goal forms)))
            (list goal
                  (reverse acc)
                  (proof-tex--dedupe (reverse cmds))
                  (proof-tex--dedupe (apply append (map proof-tex--syms allforms)))
                  (proof-tex--dedupe (apply append (map proof-tex--heads allforms)))))))))

;;; --- glossary machinery ----------------------------------------------

(define (proof-tex--dedupe lst)
  (let loop ((xs lst) (seen '()))
    (cond ((null? xs) (reverse seen))
          ((memq (car xs) seen) (loop (cdr xs) seen))
          (else (loop (cdr xs) (cons (car xs) seen))))))

;; Every symbol occurring anywhere in formula e.
(define (proof-tex--syms e)
  (cond ((symbol? e) (list e))
        ((pair? e) (apply append (map proof-tex--syms e)))
        (else '())))

;; Every symbol used as an application head (car of a pair) in formula e.
(define (proof-tex--heads e)
  (cond ((and (pair? e) (symbol? (car e)))
         (cons (car e) (apply append (map proof-tex--heads (cdr e)))))
        ((pair? e) (apply append (map proof-tex--heads e)))
        (else '())))

;; Tactic name -> one-line description.  Only tactics that the replayed proof
;; actually uses are emitted, so the glossary tracks the proof.  Descriptions
;; are plain text (no LaTeX-special characters), shown verbatim.
(define *proof-tex-tactic-doc*
  '((sp       . "start the proof: install the claim as the initial goal")
    (di       . "direct inference: break the goal at its top connective -- move an implication's hypothesis into the assumptions, split a conjunction, or introduce a universally quantified variable")
    (ai       . "antecedent inference: decompose a structured assumption, named by its number or its formula")
    (mac      . "macete: rewrite the goal using a named theorem or definition")
    (mac-h    . "macete in a hypothesis: unfold a defined predicate inside an assumption")
    (mac-h*   . "saturating hypothesis unfold: repeatedly unfold every defined predicate in the assumptions and split the conjunctions they expose, until nothing remains folded")
    (grind    . "normalize the focus: decompose the goal connective and break open the hypotheses (di + saturating hypothesis unfold) until neither applies")
    (bc       . "backchain: reduce the goal through a named implication")
    (bc*      . "iterated backchain: backchain repeatedly, sending each resulting subgoal to a recorded handler")
    (inst     . "instantiate: supply a witness term for a universally quantified assumption")
    (inst+    . "instantiate and detach: specialise a universal assumption at a term, then discharge its in-context guards")
    (wk       . "weaken: drop an assumption from the context")
    (keep     . "keep only the named assumptions (drop the rest)")
    (ass      . "assert: close the goal directly from the assumptions")
    (subst    . "substitute: rewrite the goal using an equality assumption")
    (cut      . "cut: introduce an intermediate lemma, discharged as a side goal")
    (simp     . "simplify: normalise a commutative-ring subterm of the goal")
    (ce       . "cartesian elimination: extract a component from a tuple or pair assumption")
    (te       . "tuple elimination: destructure a tuple assumption")
    (ie       . "intersection elimination: use a membership-in-an-intersection assumption")
    (sep-me   . "separation membership: use an assumption that an element lies in a separation set")
    (comp-me  . "comprehension membership elimination")
    (bu-me    . "big-union membership: use an assumption that an element lies in a big union")
    (focus    . "switch focus to another open subgoal")
    (focus-id . "switch focus to the subgoal with the given node number")
    (to-binary . "rewrite n-ary plus, times, minus into the binary structure operators")
    (to-nary  . "rewrite binary structure operators back into n-ary plus, times, minus")
    (qed      . "close the completed proof and install it as a theorem")))

;; Notation symbol -> plain-English meaning, for glyphs expr->tex emits that a
;; reader can't decode by sight.  Keyed by the (lower-cased) operator/atom.
(define *proof-tex-notation-doc*
  '((card    . "$|x|$ -- the cardinality (number of elements) of the set $x$")
    (nn      . "$\\mathbb{N}$ -- the natural numbers")
    (rr      . "$\\mathbb{R}$ -- the real numbers")
    (qq      . "$\\mathbb{Q}$ -- the rationals")
    (zz      . "$\\mathbb{Z}$ -- the integers")
    (cc      . "$\\mathbb{C}$ -- the complex numbers")
    (ord     . "$\\mathrm{Ord}$ -- the ordinals")
    (empty-set . "$\\emptyset$ -- the empty set")
    (in      . "$\\in$ -- set membership")
    (subset  . "$\\subseteq$ -- subset")
    (fun     . "$(CARR \\to B)$ -- the set of functions from $A$ to $B$")
    (cartesian . "$\\times$ -- Cartesian product")
    (union   . "$\\cup$ -- union")
    (intersection . "$\\cap$ -- intersection")
    (pair    . "$\\{a,b\\}$ -- the unordered pair (a singleton $\\{x\\}$ when the two are equal)")
    (list    . "$\\langle \\ldots \\rangle$ -- a finite tuple")
    (sep     . "$\\{x \\in A : \\varphi\\}$ -- the subset of $A$ carved out by the condition $\\varphi$")
    (choice  . "$\\varepsilon$ -- the global choice operator")
    (iota    . "$\\iota$ -- the definite-description operator")
    (inf-subsets . "$\\mathrm{Inf}(x)$ -- the infinite subsets of $x$")
    (iff     . "$\\Leftrightarrow$ -- if and only if")
    (implies . "$\\Rightarrow$ -- implies")
    (and     . "$\\wedge$ -- and")
    (or      . "$\\vee$ -- or")
    (not     . "$\\neg$ -- not")))

;; Itemised glossary of the tactics actually used, in first-use order.
(define (proof-tex--tactic-glossary cmds)
  (let ((entries (filter (lambda (c) (assq c *proof-tex-tactic-doc*)) cmds)))
    (if (null? entries)
        ""
        (apply string-append
          "\\subsection*{Tactics used}\n\\begin{itemize}\n"
          (append
           (map (lambda (c)
                  (string-append
                   "\\item \\texttt{" (proof-tex--escape-tt (symbol->string c))
                   "} -- " (cdr (assq c *proof-tex-tactic-doc*)) "\n"))
                entries)
           (list "\\end{itemize}\n\n"))))))

;; Itemised glossary of the notation used: known glyphs from the notation
;; table, plus any application head that is a registered definition (pointed at
;; the Definitions reference, which carries its full defining formula).
(define (proof-tex--notation-glossary syms heads)
  (let* ((noted (filter (lambda (s) (assq s *proof-tex-notation-doc*)) syms))
         (defs  (map car (theory-definitions *current-theory*)))
         (defheads (filter (lambda (h) (and (memq h defs)
                                            (not (assq h *proof-tex-notation-doc*))))
                           heads)))
    (if (and (null? noted) (null? defheads))
        ""
        (apply string-append
          "\\subsection*{Notation}\n\\begin{itemize}\n"
          (append
           (map (lambda (s)
                  (string-append "\\item " (cdr (assq s *proof-tex-notation-doc*)) "\n"))
                noted)
           (map (lambda (h)
                  (string-append
                   "\\item \\texttt{" (proof-tex--escape-tt (symbol->string h))
                   "}$(\\ldots)$ -- a defined term; see the Definitions reference (DEFINITIONS.md) for its full definition\n"))
                defheads)
           (list "\\end{itemize}\n\n"))))))

;;; --- LaTeX assembly --------------------------------------------------

;; Escape the few chars that bite inside \texttt{...}.
(define (proof-tex--escape-tt s)
  (apply string-append
         (map (lambda (c)
                (case c
                  ((#\_) "\\_") ((#\#) "\\#") ((#\%) "\\%")
                  ((#\&) "\\&") ((#\{) "\\{") ((#\}) "\\}")
                  (else (string c))))
              (string->list s))))

;; \fit shrinks a box to \linewidth ONLY when it would overflow, so small
;; goals stay normal size and wide sequents never run off the page.
(define proof-tex--preamble
  (string-append
   "\\documentclass[11pt]{article}\n"
   "\\usepackage[fleqn]{amsmath}\n"       ; left-align displayed equations
   "\\usepackage{amssymb, amsthm}\n"
   "\\usepackage[utf8]{inputenc}\n"
   "\\usepackage[margin=1in]{geometry}\n"
   "\\usepackage{graphicx}\n"
   "\\usepackage{enumitem}\n"
   "\\theoremstyle{plain}\n"
   "\\newtheorem{proposition}{Proposition}\n"
   ;; \fit remains for the full-trace step LABELS (proof-tex--row); reader
   ;; formulas now use displayed equations that wrap via expr->tex-display.
   "\\newcommand{\\fit}[1]{\\resizebox{\\ifdim\\width>\\linewidth\\linewidth\\else\\width\\fi}{!}{#1}}\n"
   "\\setlength{\\parindent}{0pt}\n"
   "\\begin{document}\n"))

;; A single formula as an editable align* block.  align* (not inline $...$ +
;; \fit) so the .tex is easy to hand-edit: insert `\\' for line breaks and `&'
;; to align/indent long formulas.  No auto-shrink -- manual control is the point.
;; `expr->tex-display' and NOT `expr->tex': the display renderer breaks a long
;; formula across rows (tex-output.scm), returning a bare string when one row is
;; enough, so short claims are unchanged.  `align*' does not wrap, so the plain
;; renderer put the whole claim on one line and anything long ran off the page --
;; which is what the Claim of antiderivative-lipschitz did (2026-09-06).
(define (proof-tex--formula-align e)
  (string-append "\\begin{align*}\n  " (expr->tex-display e) "\n\\end{align*}\n"))

;; A whole sequent (assumptions A1..An, a rule, then the goal after \vdash) as
;; ONE align* block, aligned at `&'.  One editable environment per step: break a
;; long row by hand with `\\ &  ...', indent by adjusting the alignment column.
;;
;; THE RULE.  The turnstile alone does not say what it ranges over -- with the
;; assumptions stacked above it and nothing marking where the list ends, "the
;; scope of the turnstile" is a guess (the user's note, 2026-09-10).  The bar
;; makes it an ordinary sequent: everything above it is assumed, the one line
;; below it is claimed.
;;
;; `\noalign' rather than a row of its own, and NOT the `array'+`\hline' that
;; would be the obvious way to get a bar.  Both matter:
;;   * an `array' cannot break across a page, and real sequents here get long --
;;     proof-bernstein-variance has a 92-assumption block, tb-cauchy-subseq 87.
;;     align* breaks between rows; array would run off the bottom of the page.
;;   * `\hrule' inside `\noalign' spans the enclosing box, which for an align*
;;     row group is the width of the WIDEST row -- so the bar tracks the content
;;     the way `\hline' does in an array, without being an array.  (The preamble
;;     already loads amsmath with `fleqn', so the block is flush left and the bar
;;     starts where the assumptions do.)
;; No assumptions, no rule: a bar with nothing above it reads as a stray line,
;; and a turnstile with nothing to range over has no scope to be unclear about.
(define (proof-tex--sequent-align asms goal)
  (string-append
   "\\begin{align*}\n"
   (apply string-append
     (map (lambda (i a)
            (string-append "  \\mathbf{A" (number->string i) ".}\\quad & "
                           (expr->tex-display a) " \\\\\n"))
          (iota (length asms) 1) asms))
   (if (null? asms) "" "  \\noalign{\\vskip3pt\\hrule\\vskip5pt}\n")
   "  \\vdash\\quad & " (expr->tex-display goal) "\n"
   "\\end{align*}\n"))

;; "adds nodes 79, 80, 81 -- focus 79" annotation for a step.
(define (proof-tex--nodes-line focus-id new-ids)
  (string-append
   "\\hfill{\\small "
   (if (null? new-ids)
       "adds no nodes"
       (string-append "adds node"
                      (if (> (length new-ids) 1) "s" "") " "
                      (proof-tex--num-list new-ids)))
   (if focus-id
       (string-append " $\\;\\cdot\\;$ focus " (number->string focus-id))
       "")
   "}"))

(define (proof-tex--num-list ks)
  (proof-tex--join (map number->string ks) ", "))

(define (proof-tex--join strs sep)
  (cond ((null? strs) "")
        ((null? (cdr strs)) (car strs))
        (else (string-append (car strs) sep (proof-tex--join (cdr strs) sep)))))

(define (proof-tex--row n label goal asms focus-id new-ids #!optional note)
  (string-append
   "\\medskip\\noindent\\textbf{" (number->string n) ".}\\quad "
   ;; \fit so a long faithful label (e.g. an `ai' on a big assumption) shrinks
   ;; to the line instead of overflowing the margin; short labels are untouched.
   "\\fit{\\texttt{" (proof-tex--escape-tt label) "}}"
   ;; the oracle's certificate, when the step closed a node by ineq / sos
   (if (and (not (default-object? note)) note)
       (string-append "\\\\\n\\hspace*{2em}{\\small\\texttt{"
                      (proof-tex--escape-tt note) "}}")
       "")
   (if goal
       (string-append
        (proof-tex--nodes-line focus-id new-ids)
        "\\\\[2pt]\n"
        (proof-tex--sequent-align asms goal))
       (string-append
        (proof-tex--nodes-line focus-id new-ids)
        "\\\\[2pt]\n\\emph{QED.}\\par\n"))))

(define (proof-tex name)
  ;; A theorem installed from its certificate (certificates.scm) has no proof in
  ;; this image: say so, instead of dying on the missing trace and script.
  (if (and (certified-theorem? name)
           (not (hash-table-ref/default *proof-live-trace* name #f)))
      (string-append
       proof-tex--preamble
       "\\section*{Proof of \\texttt{" (proof-tex--escape-tt (symbol->string name)) "}}\n"
       "Certified, no proof in this image: the theorem was installed from the "
       "certificate written by the exam of "
       (car (hash-table-ref *certified-theorems* name (lambda () '("?" "?"))))
       ", which ran and checked its proof.  Run the exam "
       "(\\texttt{VNB\\_CERTIFIED=off ./prover --build-band}) and print the proof "
       "from that image.\n\n\\end{document}\n")
      (proof-tex--full name)))

(define (proof-tex--full name)
  (let* ((data  (proof-tex--steps name))
         (goal  (list-ref data 0))
         (steps (list-ref data 1))
         (cmds  (list-ref data 2))
         (syms  (list-ref data 3))
         (heads (list-ref data 4)))
    (apply string-append
     proof-tex--preamble
     "\\section*{Proof of \\texttt{" (proof-tex--escape-tt (symbol->string name)) "}}\n"
     "\\textbf{Claim.}\n" (proof-tex--formula-align goal) "\\bigskip\n\n"
     (proof-tex--tactic-glossary cmds)
     (proof-tex--notation-glossary syms heads)
     "\\subsection*{Derivation}\nEach step shows the tactic applied; the goal "
     "nodes it opens and which one is now in focus (the bracketed \\texttt{[k]} "
     "of the workspace display); the focus node's assumptions (\\textbf{A1}, "
     "\\textbf{A2}, \\dots{}, the numbering the tactic args refer to); and, "
     "below the rule, the goal $G$ it leaves, written $\\vdash G$.  Everything "
     "above the rule is assumed; the single line below it is what is claimed.  "
     "Each sequent is an "
     "\\texttt{align*} environment: break a long formula by hand with "
     "\\texttt{\\textbackslash\\textbackslash\\ \\&} and indent at the "
     "alignment column.\n\n"
     (append
      (let loop ((ss steps) (n 0) (rows '()))
        (if (null? ss)
            (reverse rows)
            (let ((st (car ss)))
              (loop (cdr ss) (+ n 1)
                    (cons (proof-tex--row n (list-ref st 0) (list-ref st 1)
                                          (list-ref st 2) (list-ref st 3) (list-ref st 4)
                                          (and (> (length st) 5) (list-ref st 5)))
                          rows)))))
      (list "\n\\end{document}\n")))))

(define (write-proof-tex name path)
  (call-with-output-file path
    (lambda (port) (display (proof-tex name) port)))
  path)

;; Best-effort: write to the tex cache, run pdflatex, open the PDF.  Mirrors
;; the single-formula View-as-PDF pipeline (cache under ~/.cache/vnb/tex/).
;;; mkdir -p, in Scheme, and the emphasis is on NOT DYING ON AN ANCESTOR.
;;;
;;; History, because both of the obvious designs failed in the field and neither
;;; failed here.  Originally the two PDF viewers prepared their directories with
;;; one `run-shell-command "mkdir -p ..."'; where that call did not fire the
;;; failure surfaced as an unopenable .tex, naming the file and not the mkdir
;;; (reported 2026-09-05).  Replacing it with a walk that TESTS each component
;;; and creates the missing ones was worse: in the reporting user's environment
;;; `file-exists?' answered #f for "/home/ubuntu", so the walk tried to CREATE
;;; it and died with "Permission denied" -- a message about the home directory,
;;; from a request to view a proof.
;;;
;;; So: attempt each component, TRAP AND DISCARD every failure, and judge only
;;; the final state.  An ancestor that already exists, or that this process may
;;; not create, is not a problem provided the target directory is there at the
;;; end -- which is exactly what `mkdir -p' means and why it ignores EEXIST.
;;; The check at the end is the only one that can fail, and it names the
;;; directory it wanted.
(define (tex--try thunk)
  (call-with-current-continuation
    (lambda (k)
      (bind-condition-handler (list condition-type:error)
        (lambda (c) c (k #f))
        thunk))))

(define (tex--ensure-directory! dir)
  (let loop ((parts (filter (lambda (s) (not (string-null? s)))
                            (burst-string dir #\/ #f)))
             (path ""))
    (if (null? parts)
        (if (file-directory? dir)
            dir
            (error "tex--ensure-directory!: cannot create directory" dir))
        (let ((next (string-append path "/" (car parts))))
          (if (not (file-directory? next))
              (tex--try (lambda () (make-directory next))))
          (loop (cdr parts) next)))))

;;; Copy the rendered .tex into the source tree as an ARCHIVE, if this user can
;;; write there; otherwise say so once and carry on.
;;;
;;; The viewers used to render the .tex INTO `*printouts-dir*' -- the source tree
;;; -- with the stated reason that it then ships in the tarball.  That is right
;;; for the owner of the tree and wrong for everybody else: `/home/ubuntu' here
;;; is drwxr-x---, so a second user cannot traverse it, every path beneath it
;;; reports as absent, and the render died before it began (reported 2026-09-05,
;;; twice, from two different messages).  The PDF always went to a per-user
;;; cache under $HOME; now the .tex does too, and the source-tree copy is a
;;; best-effort extra.  Nothing a user needs to SEE a proof lives in a directory
;;; only one account can write.
(define (tex--archive-copy! from to)
  (if (tex--try (lambda ()
                  (tex--ensure-directory! (directory-namestring to))
                  (call-with-output-file to
                    (lambda (out)
                      (call-with-input-file from
                        (lambda (in)
                          (let loop ()
                            (let ((c (read-char in)))
                              (if (not (eof-object? c))
                                  (begin (write-char c out) (loop)))))))))
                  #t))
      to
      (begin (display ";; note: could not archive into ") (display to)
             (display " -- the PDF and .tex are in the cache.\n")
             #f)))

(define (view-proof-pdf name)
  ;; .tex lives in the source tree (*printouts-dir*) so it ships in the tarball;
  ;; the PDF + pdflatex aux junk render into the regenerable ~/.cache scratch.
  ;; load-option MUST precede any run-shell-command: run-shell-command is
  ;; unassigned until synchronous-subprocess is loaded.
  (load-option 'synchronous-subprocess)
  (let* ((cache (string-append (get-environment-variable "HOME") "/.cache/vnb/tex/"))
         (base  (string-append "proof-" (symbol->string name)))
         (tex   (string-append cache base ".tex")))     ; under $HOME, always writable
    (tex--ensure-directory! cache)
    (write-proof-tex name tex)
    (tex--archive-copy! tex (string-append *printouts-dir* base ".tex"))
    (run-shell-command
     (string-append "pdflatex -interaction=nonstopmode -output-directory=" cache
                    " " tex " > /dev/null 2>&1"))
    (let ((pdf (string-append cache base ".pdf")))
      (if (file-exists? pdf)
          (begin (ignore-errors
                  (run-shell-command (string-append "xdg-open " pdf " > /dev/null 2>&1 &")))
                 pdf)
          (error "view-proof-pdf: pdflatex produced no PDF -- see" (string-append cache base ".log"))))))
