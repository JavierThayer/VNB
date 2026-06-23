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

;; A recorded command's argument: render symbols/numbers verbatim (witnesses,
;; indices, macete names) and collapse formula/list args to an ellipsis, so the
;; step annotation stays a tidy `(inst ... x)' / `(mac totally-bounded-def)'.
(define (proof-tex--arg-short a)
  (cond ((symbol? a) (symbol->string a))
        ((number? a) (number->string a))
        ((null? a)   "()")
        (else        "...")))

(define (proof-tex--cmd-label entry)
  (string-append
   "(" (symbol->string (car entry))
   (apply string-append
          (map (lambda (a) (string-append " " (proof-tex--arg-short a)))
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
                     (label (if (eq? (car entry) 'sp) "sp" (proof-tex--cmd-label entry))))
                (set! prev open)
                (set! steps (cons (list label g a fid added) steps))
                (set! cmds  (cons (car entry) cmds))
                (set! forms (append (if g (list g) '()) a forms))))
            trace)
           (let ((allforms (cons goal forms)))
             (list goal
                   (reverse steps)
                   (proof-tex--dedupe (reverse cmds))
                   (proof-tex--dedupe (apply append (map proof-tex--syms allforms)))
                   (proof-tex--dedupe (apply append (map proof-tex--heads allforms)))))))))

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
    (wk       . "weaken: close the goal by matching it against an assumption")
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
    (fun     . "$(A \\to B)$ -- the set of functions from $A$ to $B$")
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
   "\\usepackage{amsmath, amssymb}\n"
   "\\usepackage[utf8]{inputenc}\n"
   "\\usepackage[margin=1in]{geometry}\n"
   "\\usepackage{graphicx}\n"
   "\\newcommand{\\fit}[1]{\\resizebox{\\ifdim\\width>\\linewidth\\linewidth\\else\\width\\fi}{!}{#1}}\n"
   "\\setlength{\\parindent}{0pt}\n"
   "\\begin{document}\n"))

;; A single formula as an editable align* block.  align* (not inline $...$ +
;; \fit) so the .tex is easy to hand-edit: insert `\\' for line breaks and `&'
;; to align/indent long formulas.  No auto-shrink -- manual control is the point.
(define (proof-tex--formula-align e)
  (string-append "\\begin{align*}\n  " (expr->tex e) "\n\\end{align*}\n"))

;; A whole sequent (assumptions A1..An, then the goal after \vdash) as ONE
;; align* block, aligned at `&'.  One editable environment per step: break a
;; long row by hand with `\\ &  ...', indent by adjusting the alignment column.
(define (proof-tex--sequent-align asms goal)
  (string-append
   "\\begin{align*}\n"
   (apply string-append
     (map (lambda (i a)
            (string-append "  \\mathbf{A" (number->string i) ".}\\quad & "
                           (expr->tex a) " \\\\\n"))
          (iota (length asms) 1) asms))
   "  \\vdash\\quad & " (expr->tex goal) "\n"
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

(define (proof-tex--row n label goal asms focus-id new-ids)
  (string-append
   "\\medskip\\noindent\\textbf{" (number->string n) ".}\\quad "
   "\\texttt{" (proof-tex--escape-tt label) "}"
   (if goal
       (string-append
        (proof-tex--nodes-line focus-id new-ids)
        "\\\\[2pt]\n"
        (proof-tex--sequent-align asms goal))
       (string-append
        (proof-tex--nodes-line focus-id new-ids)
        "\\\\[2pt]\n\\emph{QED.}\\par\n"))))

(define (proof-tex name)
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
     "\\textbf{A2}, \\dots{}, the numbering the tactic args refer to); and the "
     "goal $G$ it leaves, written $\\vdash G$.  Each sequent is an "
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
                                          (list-ref st 2) (list-ref st 3) (list-ref st 4))
                          rows)))))
      (list "\n\\end{document}\n")))))

(define (write-proof-tex name path)
  (call-with-output-file path
    (lambda (port) (display (proof-tex name) port)))
  path)

;; Best-effort: write to the tex cache, run pdflatex, open the PDF.  Mirrors
;; the single-formula View-as-PDF pipeline (cache under ~/.cache/vnb/tex/).
(define (view-proof-pdf name)
  (let* ((dir  (string-append (get-environment-variable "HOME") "/.cache/vnb/tex/"))
         (base (string-append "proof-" (symbol->string name)))
         (tex  (string-append dir base ".tex")))
    (ignore-errors (run-shell-command (string-append "mkdir -p " dir)))
    (write-proof-tex name tex)
    (load-option 'synchronous-subprocess)
    (run-shell-command
     (string-append "cd " dir " && pdflatex -interaction=nonstopmode "
                    base ".tex > /dev/null 2>&1"))
    (let ((pdf (string-append dir base ".pdf")))
      (if (file-exists? pdf)
          (begin (ignore-errors
                  (run-shell-command (string-append "xdg-open " pdf " > /dev/null 2>&1 &")))
                 pdf)
          (error "view-proof-pdf: pdflatex produced no PDF -- see" (string-append dir base ".log"))))))
