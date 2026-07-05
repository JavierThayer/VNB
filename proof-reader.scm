;;; proof-reader.scm -- the HUMAN-READABLE proof sketch ("reader mode"), the
;;; companion of proof-tex.scm (which dumps every tactic as a numbered sequent).
;;;
;;; It collapses the mechanical bookkeeping -- runs of `di' / `ai' (the
;;; decompose-goal / unpack-hypothesis kernel rules) -- into a single
;;; "Assume ...; Show ..." opening, and renders only the CONTENT-bearing steps
;;; (ew witnesses, mac unfolds, fact / lemma citations, oracle / assumption
;;; closes) as bullets.  Each bullet carries the ORIGINAL step-number range in
;;; its margin, so the sketch stays auditable against the full machine proof.
;;;
;;; FAITHFUL, not fluent.  It cites lemma NAMES and shows the actual witness
;;; term / unfolded goal / instantiated hypothesis the machine produced; it does
;;; NOT paraphrase what a lemma "means" (that would need per-lemma NL templates,
;;; a later layer).  What you read is exactly what the checker did, minus the
;;; di/ai noise.
;;;
;;; Entry points mirror proof-tex:
;;;   (proof-reader name)            -> the LaTeX document as a string
;;;   (write-proof-reader name path) -> writes path, returns path
;;;   (view-proof-reader-pdf name)   -> write + pdflatex + open (best-effort)
;;;
;;; Loaded after proof-tex.scm (reuses its preamble, expr->tex sequent/align
;;; helpers, replay machinery, *proof-live-trace*, *session-log*).

;;; --- capture: per-step records that KEEP the raw entry -----------------
;;; proof-tex--steps stores a truncated LABEL string ("(ew ...)"); the reader
;;; needs the raw (tactic . args) so it can show the actual witness term.  A
;;; record is (entry goal asms new-ids); the first record's entry is (sp).
(define (proof-reader--records name)
  (or (proof-reader--records-from-live name)
      (proof-reader--records-by-replay name)))

(define (proof-reader--records-from-live name)
  (let ((trace (hash-table-ref/default *proof-live-trace* name #f)))
    (and (pair? trace)
         (let ((prev '()) (out '()))
           (for-each
            (lambda (rec)
              (let* ((entry (car rec)) (g (cadr rec)) (a (caddr rec)) (open (list-ref rec 4))
                     (added (sort (filter (lambda (k)(not (memv k prev))) open) <)))
                (set! prev open)
                (set! out (cons (list entry g a added) out))))
            trace)
           (reverse out)))))

(define (proof-reader--records-by-replay name)
  (let ((rec (proof-tex--record name)))
    (if (not rec)
        (error "proof-reader: no proof named this in *session-log* (proofs run this session)" name)
        (let ((goal (cadr rec)) (script (caddr rec)) (acc '()) (prev '()))
          (define (new-ids)
            (let ((now (proof-tex--open-ids)))
              (let ((added (filter (lambda (k)(not (memv k prev))) now)))
                (set! prev now) (sort added <))))
          (quietly
           (lambda ()
             (fluid-let ((*fresh-counter*
                          (hash-table-ref/default *proof-start-counter* name *fresh-counter*)))
               (sp (make-wff goal))
               (set! acc (list (list (list 'sp) (proof-tex--focus-goal)
                                     (proof-tex--focus-asms) (new-ids))))
               (fluid-let ((*replaying?* #t))
                 (for-each
                  (lambda (entry)
                    (apply-recorded-cmd! (car entry) (cdr entry))
                    (set! acc (cons (list entry (proof-tex--focus-goal)
                                          (proof-tex--focus-asms) (new-ids)) acc)))
                  script)))))
          (reverse acc)))))

;;; --- classification ----------------------------------------------------
(define *proof-reader-structural* '(di ai))                 ; folded into prose
(define *proof-reader-closer*     '(ass rfl qrfl crs rs simp ineq sos arith))
;; fact-family tactics that merely DISCHARGE side-conditions (introduce a
;; hypothesis).  When everything such a step introduces is a typing/membership
;; predicate, it is BOOKKEEPING -- the in-carrier plumbing an oracle needs, not
;; something a human reader wants a bullet for.  A run of them collapses to one line.
(define *proof-reader-fact-tacs* '(fact ta inst inst+ pi-detach! detach))
(define (proof-reader--tac r) (car (car r)))
(define (proof-reader--structural? r) (memq (proof-reader--tac r) *proof-reader-structural*))
(define (proof-reader--closer? r)     (memq (proof-reader--tac r) *proof-reader-closer*))
(define (proof-reader--content? r)
  (and (not (eq? (proof-reader--tac r) 'sp)) (not (proof-reader--structural? r))))
;; a wff is TYPING if it is (or curries/quantifies down to) a membership `IN'.
(define (proof-reader--typing-wff? w)
  (and (pair? w)
       (case (car w)
         ((IN) #t)
         ((FORALL FORSOME) (proof-reader--typing-wff? (caddr w)))
         ((IMPLIES) (proof-reader--typing-wff? (caddr w)))
         (else #f))))

;;; --- grouping ----------------------------------------------------------
;; Attach a 0-based step index to each record: (idx entry goal asms new-ids).
(define (proof-reader--index records)
  (let loop ((rs records) (i 0) (out '()))
    (if (null? rs) (reverse out)
        (loop (cdr rs) (+ i 1) (cons (cons i (car rs)) out)))))
(define (ir-idx r)(car r))
(define (ir-rec r)(cdr r))

(define (proof-reader--all? p lst)
  (or (null? lst) (and (p (car lst)) (proof-reader--all? p (cdr lst)))))

;; new-asms of each record = its asms minus the immediately-preceding record's
;; asms (assumptions accumulate, so this is what the step introduced).  Returns a
;; hash idx -> (wff ...).  Used to tell a typing/bookkeeping step from a real one.
(define (proof-reader--annotate irecs)
  (let ((ht (make-equal-hash-table)) (prev '()))
    (for-each
     (lambda (ir)
       (let ((asms (caddr (ir-rec ir))))
         (hash-table-set! ht (ir-idx ir)
                          (filter (lambda (a) (not (member a prev))) asms))
         (set! prev asms)))
     irecs)
    ht))

;; kind of a group's MAIN record, given the new-asms hash.
(define (proof-reader--kind main-ir ht)
  (let* ((r (ir-rec main-ir)) (tac (proof-reader--tac r)))
    (cond ((proof-reader--closer? r) 'closer)
          ((and (memq tac *proof-reader-fact-tacs*)
                (let ((na (hash-table-ref/default ht (ir-idx main-ir) '())))
                  (and (pair? na) (proof-reader--all? proof-reader--typing-wff? na))))
           'typing)
          (else 'content))))

;; Split into (setup-irecs . body-groups).  setup = the opening run [sp di* ai*]
;; up to (not incl.) the first content step.  Each body group = a maximal
;; [structural* content] run (structural leads into the content step it sets up).
;; Then a group whose content is a pure CLOSER is merged into the preceding
;; group (so "by lemma L" and "which holds" become one bullet).
(define (proof-reader--group irecs)
  (let* ((ht (proof-reader--annotate irecs))
         (first-content
          (let loop ((rs irecs))
            (cond ((null? rs) #f)
                  ((proof-reader--content? (ir-rec (car rs))) (car rs))
                  (else (loop (cdr rs))))))
         (c0 (if first-content (ir-idx first-content) (length irecs)))
         (setup (filter (lambda (ir) (< (ir-idx ir) c0)) irecs))
         (body  (filter (lambda (ir) (>= (ir-idx ir) c0)) irecs)))
    ;; raw groups: accumulate structural, flush on each content record
    (let ((groups '()) (buf '()))
      (for-each
       (lambda (ir)
         (set! buf (cons ir buf))
         (when (proof-reader--content? (ir-rec ir))
           (set! groups (cons (reverse buf) groups))
           (set! buf '())))
       body)
      (when (pair? buf) (set! groups (cons (reverse buf) groups)))  ; trailing structural
      (define (grp-kind g)
        (let ((p (proof-reader--group-primary g)))
          (and p (proof-reader--kind p ht))))
      (let ((glist (reverse groups)))
        ;; merge a pure-closer group into its predecessor
        (let ((merged '()))
          (for-each
           (lambda (g)
             (let ((main (proof-reader--group-main g)))
               (if (and main (proof-reader--closer? main) (pair? merged))
                   (set-car! merged (append (car merged) g))   ; fold into previous
                   (set! merged (cons g merged)))))
           glist)
          ;; merge a RUN of typing/bookkeeping groups into one collapsed line
          (let ((tmerged '()))
            (for-each
             (lambda (g)
               (if (and (eq? (grp-kind g) 'typing) (pair? tmerged)
                        (eq? (grp-kind (car tmerged)) 'typing))
                   (set-car! tmerged (append (car tmerged) g))
                   (set! tmerged (cons g tmerged))))
             (reverse merged))
            (cons setup (reverse tmerged))))))))

;; the CONTENT record of a group = its last content record (there is exactly one
;; per raw group; after a closer-merge there may be two -- main + the closer).
(define (proof-reader--group-main g)
  (let loop ((rs (reverse g)))
    (cond ((null? rs) #f)
          ((proof-reader--content? (ir-rec (car rs))) (ir-rec (car rs)))
          (else (loop (cdr rs))))))

;; the PRIMARY content of a possibly-merged group (first content record) and the
;; trailing closer (if the group was merged with one).
(define (proof-reader--group-primary g)
  (let loop ((rs g))
    (cond ((null? rs) #f)
          ((proof-reader--content? (ir-rec (car rs))) (car rs))
          (else (loop (cdr rs))))))
(define (proof-reader--group-closer g primary)
  ;; a content record AFTER the primary that is a closer
  (let loop ((rs g) (seen-primary #f))
    (cond ((null? rs) #f)
          ((eq? (car rs) primary) (loop (cdr rs) #t))
          ((and seen-primary (proof-reader--content? (ir-rec (car rs)))
                (proof-reader--closer? (ir-rec (car rs)))) (ir-rec (car rs)))
          (else (loop (cdr rs) seen-primary)))))

(define (proof-reader--range g)
  (let ((idxs (map ir-idx g)))
    (let ((lo (apply min idxs)) (hi (apply max idxs)))
      (if (= lo hi) (number->string lo)
          (string-append (number->string lo) "--" (number->string hi))))))

;;; --- prose glosses -----------------------------------------------------
(define (proof-reader--arg-tex a)
  (cond ((string? a) (string-append "\\texttt{" (proof-tex--escape-tt a) "}"))
        ((or (pair? a) (symbol? a) (number? a)) (expr->tex a))
        (else (proof-tex--escape-tt (call-with-output-string (lambda (p)(write a p)))))))
;; a lemma CITATION: a symbol -> its name in \texttt; a raw wff (instantiating an
;; unnamed hypothesis) -> the phrase "the hypothesis" (no giant s-expr dump).
(define (proof-reader--cite a)
  (if (symbol? a)
      (string-append "\\texttt{" (proof-tex--escape-tt (symbol->string a)) "}")
      "the hypothesis"))
;; assumptions in R2 not (alpha-)in R1  -- the hypotheses a step introduced.
(define (proof-reader--new-asms before after)
  (filter (lambda (a) (not (member a before))) after))

;; prose for bare tactics that take no cited lemma / witness (the `else' fallback).
;; ni/subst/lam-b are handled explicitly above (they read the goal / induction var).
(define *proof-reader-tac-prose*
  '((cut       . "By a cut on the auxiliary claim.")
    (contra    . "By contradiction.")
    (weaken    . "Weakening the context.")
    (grind     . "By exhaustive simplification (\\texttt{grind}).")
    (unfold    . "Unfold the definition.")
    (gi        . "Generalize.")))

;; gloss for the PRIMARY content record; pre-goal = goal of the record before it,
;; pre-asms = assumptions before it.  Returns a LaTeX fragment (math via $...$).
(define (proof-reader--gloss main pre-goal pre-asms)
  (let* ((entry (car main)) (tac (car entry)) (args (cdr entry))
         (goal (cadr main)) (asms (caddr main))
         (news (proof-reader--new-asms pre-asms asms)))
    (case tac
      ((ew)
       (let ((v (and (pair? pre-goal) (eq? (car pre-goal) 'FORSOME) (cadr pre-goal)))
             (w (and (pair? args) (car args))))
         (string-append "Take $" (if v (expr->tex v) "w") " := \\fit{$"
                        (if w (proof-reader--arg-tex w) "\\cdot") "$}$.")))
      ((mac macm)
       (string-append "By " (proof-reader--cite (and (pair? args)(car args)))
                      (if goal (string-append ", reduce to \\fit{$" (expr->tex goal) "$}.") ".")))
      ((fact ta)
       (string-append "By " (proof-reader--cite (and (pair? args)(car args)))
                      (cond ((pair? news)      ; show only the CONCLUSION it detaches
                             (string-append ": \\fit{$" (expr->tex (car news)) "$}."))
                            (goal (string-append ", reduce to \\fit{$" (expr->tex goal) "$}."))
                            (else "."))))
      ((inst inst+)
       (string-append "Instantiate " (proof-reader--cite (and (pair? args)(car args)))
                      (if (pair? news)
                          (string-append ": \\fit{$" (expr->tex (car news)) "$}.")
                          ".")))
      ((bc bc*)
       (string-append "Backchain through " (proof-reader--cite (and (pair? args)(car args)))
                      (if goal (string-append "; it remains to show \\fit{$" (expr->tex goal) "$}.") ".")))
      ((ni)
       (let ((v (and (pair? pre-goal) (eq? (car pre-goal) 'FORALL) (cadr pre-goal))))
         (string-append "By induction"
                        (if v (string-append " on $" (expr->tex v) "$") "") ".")))
      ((subst) "Substitute the established equation.")
      ((lam-b) "$\\beta$-reduce the applied $\\lambda$.")
      ((ass) "\\emph{Holds by assumption.}")
      ((rfl qrfl) "\\emph{Holds by reflexivity.}")
      ((crs rs simp) "\\emph{Closes by commutative-ring simplification.}")
      ((ineq) "\\emph{Closes by linear arithmetic (ineq).}")
      ((sos) "\\emph{Closes by sum-of-squares.}")
      ((arith) "\\emph{Closes by ground arithmetic.}")
      (else
       (let ((p (assq tac *proof-reader-tac-prose*)))
         (if p (cdr p)
             (string-append "By \\texttt{" (proof-tex--escape-tt (symbol->string tac)) "}.")))))))

;;; --- assembly ----------------------------------------------------------
;; a collapsed line for a RUN of typing/bookkeeping steps: just the atoms they
;; established (each fact's detached conclusion), no per-step bullets.
(define (proof-reader--typing-row g ht)
  (let ((atoms '()))
    (for-each
     (lambda (ir)
       (when (memq (proof-reader--tac (ir-rec ir)) *proof-reader-fact-tacs*)
         (let ((na (hash-table-ref/default ht (ir-idx ir) '())))
           (when (pair? na) (set! atoms (cons (car na) atoms))))))
     g)
    (string-append
     "\\emph{Establish in-carrier / typing side-conditions:} "
     (let ((atoms (reverse atoms)))
       (if (pair? atoms)
           (string-append "\\fit{$" (proof-tex--join (map expr->tex atoms) "$},\\ \\fit{$") "$}.")
           "")))))

;; a bulletless sub-header row marking the base / inductive-step branch of an
;; `ni' proof (empty \item label -> no step number in the margin).
(define (proof-reader--branch-hdr indvar which)
  (let ((v (if indvar (expr->tex indvar) "n")))
    (if (eq? which 'base)
        (string-append "  \\item[]\\textbf{Base case} ($" v " = 0$):\n")
        (string-append "  \\item[]\\textbf{Inductive step} ($" v " \\to " v " + 1$):\n"))))

(define (proof-reader name)
  (let* ((records (proof-reader--records name))
         (claim   (cadr (car records)))            ; sp record's goal
         (indexed (proof-reader--index records))
         (ht      (proof-reader--annotate indexed))
         (grp     (proof-reader--group indexed))
         (setup   (car grp))
         (groups  (cdr grp))
         ;; setup sequent = state just before the first content step = the last
         ;; record in `setup' (or the sp record if setup is only sp).
         (setup-last (if (pair? setup) (ir-rec (car (last-pair setup))) (car records)))
         (setup-asms (caddr setup-last))
         (setup-goal (cadr setup-last))
         (setup-range (if (pair? setup) (proof-reader--range setup) "0")))
    (apply string-append
     proof-tex--preamble
     "\\section*{Reader sketch: \\texttt{" (proof-tex--escape-tt (symbol->string name)) "}}\n"
     "{\\small A human-level collapse of the machine proof: runs of \\texttt{di}/\\texttt{ai} "
     "(decompose / unpack) are folded into the opening; only content steps are shown, each "
     "with its original step range in the margin.  The full step-by-step is the \\texttt{proof-tex} "
     "rendering.}\\medskip\n\n"
     "\\textbf{Claim.}\n" (proof-tex--formula-align claim) "\\medskip\n\n"
     "\\textbf{Proof.}\\quad\\emph{Assume} \\textbf{[" setup-range "]}:\n"
     (proof-tex--sequent-align setup-asms setup-goal)
     "\n\\begin{itemize}\\setlength{\\itemsep}{4pt}\n"
     (append
      ;; walk groups, threading the pre-goal / pre-asms (the setup sequent seeds
      ;; it) and, for an `ni' proof, the induction variable + branch phase so we
      ;; can insert "Base case" / "Inductive step" sub-headers.  Branch signal:
      ;; the base leaf proves P(0) (indvar not free); the step leaf proves
      ;; P(n)=>P(n+1) (indvar free again).  See proof-reader--gloss for the ni row.
      (let loop ((gs groups) (pre-goal setup-goal) (pre-asms setup-asms)
                 (indvar #f) (phase 'none) (rows '()))
        (if (null? gs) (reverse rows)
            (let* ((g (car gs))
                   (primary (proof-reader--group-primary g))
                   (main    (and primary (ir-rec primary)))
                   (kind    (and primary (proof-reader--kind primary ht)))
                   (closer  (and primary (proof-reader--group-closer g primary)))
                   (gloss   (cond ((eq? kind 'typing) (proof-reader--typing-row g ht))
                                  (main (proof-reader--gloss main pre-goal pre-asms))
                                  (else "")))
                   (close-txt (cond ((not closer) "")
                                    ((memq (car (car closer)) '(ass)) "  \\emph{(holds by assumption)}")
                                    (else "  \\emph{(closes)}")))
                   (is-ni   (and main (eq? (car (car main)) 'ni)))
                   (new-indvar (if is-ni
                                   (and (pair? pre-goal) (eq? (car pre-goal) 'FORALL) (cadr pre-goal))
                                   indvar))
                   (ggoal   (or (and main (cadr main)) pre-goal))
                   (this-step? (and indvar (memq indvar (free-vars ggoal))))
                   ;; header + phase transition (only for an ni proof, after the ni row)
                   (hdr+phase
                    (cond (is-ni (cons "" 'await-base))
                          ((eq? phase 'await-base)
                           (if this-step?
                               (cons (proof-reader--branch-hdr indvar 'step) 'step)
                               (cons (proof-reader--branch-hdr indvar 'base) 'base)))
                          ((and (eq? phase 'base) this-step?)
                           (cons (proof-reader--branch-hdr indvar 'step) 'step))
                          (else (cons "" phase))))
                   (row (string-append
                         (car hdr+phase)
                         "  \\item[\\textbf{" (proof-reader--range g) "}] "
                         gloss close-txt "\n"))
                   (new-goal (if main (cadr main) pre-goal))
                   (new-asms (if main (caddr main) pre-asms)))
              (loop (cdr gs) new-goal new-asms new-indvar (cdr hdr+phase)
                    (cons row rows)))))
      (list "\\end{itemize}\n\\hfill$\\blacksquare$\n\\end{document}\n")))))

(define (write-proof-reader name path)
  (call-with-output-file path
    (lambda (port) (display (proof-reader name) port)))
  path)

(define (view-proof-reader-pdf name)
  (let* ((dir  (string-append (get-environment-variable "HOME") "/.cache/vnb/tex/"))
         (base (string-append "reader-" (symbol->string name)))
         (tex  (string-append dir base ".tex")))
    (ignore-errors (run-shell-command (string-append "mkdir -p " dir)))
    (write-proof-reader name tex)
    (load-option 'synchronous-subprocess)
    (run-shell-command
     (string-append "cd " dir " && pdflatex -interaction=nonstopmode " base ".tex > /dev/null 2>&1"))
    (let ((pdf (string-append dir base ".pdf")))
      (if (file-exists? pdf) pdf
          (error "view-proof-reader-pdf: pdflatex produced no PDF -- see" (string-append dir base ".log"))))))
