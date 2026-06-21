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

(define (proof-tex--nasm)
  (if (proof-done? *ps*)
      0
      (length (sequent-node-assumptions (proof-state-focus *ps*)))))

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

;; Returns a list of (label goal-or-#f nasm), label a plain string.
(define (proof-tex--steps name)
  (let ((rec (proof-tex--record name)))
    (if (not rec)
        (error "proof-tex: no proof named this in *session-log* (proofs run this session)" name)
        (let ((goal (cadr rec)) (script (caddr rec)) (acc '()))
          (quietly
           (lambda ()
             (sp (make-wff goal))
             (set! acc (list (list "sp" (proof-tex--focus-goal) (proof-tex--nasm))))
             (fluid-let ((*replaying?* #t))
               (for-each
                (lambda (entry)
                  (apply-recorded-cmd! (car entry) (cdr entry))
                  (set! acc (cons (list (proof-tex--cmd-label entry)
                                        (proof-tex--focus-goal)
                                        (proof-tex--nasm))
                                  acc)))
                script))))
          (cons goal (reverse acc))))))   ; car = the overall goal

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

(define (proof-tex--row n label goal nasm)
  (string-append
   "\\medskip\\noindent\\textbf{" (number->string n) ".}\\quad "
   "\\texttt{" (proof-tex--escape-tt label) "}"
   (if goal
       (string-append
        "\\hfill{\\small[" (number->string nasm) " asm]}\\\\[2pt]\n"
        "\\fit{$\\displaystyle " (expr->tex goal) "$}\\par\n")
       "\\hfill{\\small[proof complete]}\\\\[2pt]\n\\emph{QED.}\\par\n")))

(define (proof-tex name)
  (let* ((data  (proof-tex--steps name))
         (goal  (car data))
         (steps (cdr data)))
    (apply string-append
     proof-tex--preamble
     "\\section*{Proof of \\texttt{" (proof-tex--escape-tt (symbol->string name)) "}}\n"
     "\\textbf{Claim.}\\quad \\fit{$\\displaystyle " (expr->tex goal) "$}\n\\bigskip\n\n"
     (append
      (let loop ((ss steps) (n 0) (rows '()))
        (if (null? ss)
            (reverse rows)
            (loop (cdr ss) (+ n 1)
                  (cons (proof-tex--row n (car (car ss)) (cadr (car ss)) (caddr (car ss)))
                        rows))))
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
