;;; page-audit.scm -- THE GATE ON THE PRINTED PAGE.
;;;
;;; The standard (the user's, 2026-09-06): every proof must have a re-runnable
;;; script -- a rendition that fits on a sheet of paper and that anybody able to
;;; use a keyboard can type back in to reproduce the proof.  That is the bottom,
;;; invertible notch of the proof-resolution dial, and like the FORMULA dial's
;;; invertible notch (r1, defined by the print-parse-`equal?' round-trip check)
;;; it is a notch only because a load-time gate says so.
;;;
;;; WHAT THIS MEASURES, AND WHY IT IS NOT replay-audit.scm.  That file feeds the
;;; stored commands to `apply-recorded-cmd!' inside a harness that restores
;;; `*fresh-counter*'.  A person who types the page has no harness.  Measured
;;; 2026-09-07, and the gap is not small:
;;;
;;;     the page, typed in                      707 / 1022
;;;     the page + only the counter restored    983 / 1022
;;;     the dispatcher path, counter restored   979 / 1022
;;;
;;; So `replay-audit.scm' OVERSTATES the page by 272, and the counter is the only
;;; difference between the two harnesses that changes an outcome -- the surface
;;; path is if anything marginally better than the dispatcher path.
;;;
;;; ZERO of the failures are errors.  All of them are `incomplete': the page
;;; loads, nothing complains, and the proof is simply not finished.  A standard
;;; whose violations are silent is not a standard, which is the whole argument
;;; for putting this on the load line.
;;;
;;; WARN-ONLY, like install-grading and the free-variable audit.  A proof whose
;;; page does not re-run is still a proof -- the graph was checked at `qed' and
;;; nothing here can unsay that.  What is missing is its printed rendition.

;;; ---------------------------------------------------------------------
;;; Is X a name minted from the global fresh counter (`d_1787', `n__1591')?
;;; Trailing digits after an underscore, which is what `fresh-var' produces.
;;; One definition, in interactive.scm beside the emitter that also needs it.
(define (page--minted-name? x) (page-minted-name? x))

(define (page--mentions-minted? f)
  (cond ((pair? f) (or (page--mentions-minted? (car f))
                       (page--mentions-minted? (cdr f))))
        (else (page--minted-name? f))))

;;; ---------------------------------------------------------------------
;;; THE PAGE ITSELF.  `script--write-block' (interactive.scm) is the emitter the
;;; `W' key and `write-proof-script' use, so this is the same text a user gets.
;;; Rendered to a STRING rather than a file: a page is text, not a filesystem,
;;; and reading the forms back out of a string port is exactly what typing them
;;; would do -- without 1022 temp files per load.
(define (page-of name)
  (let ((goal   (hash-table-ref/default *theorem-table* name #f))
        (script (hash-table-ref/default *proof-script-table* name '())))
    (and goal (pair? script)
         (with-output-to-string
           (lambda ()
             (script--write-block (current-output-port) #f goal script
                                  (hash-table-ref/default *proof-mints-table* name '())
                                  (hash-table-ref/default *proof-start-counter*
                                                          name #f)))))))

;;; Type the page in.  Returns 'grounded / 'incomplete / 'error.
;;;
;;; `*ps*' and the four recording globals are saved and restored: this runs at
;;; the END of a load, and a gate must not leave a scratch proof in progress for
;;; whoever gets the REPL next.  `*replaying?*' is deliberately NOT bound --
;;; binding it would suppress the recording and the undo marks that a real typed
;;; session performs, and the number above was measured without it.
;;; AFTER (optional): a thunk run INSIDE the replay, once the page is typed in and
;;; before *ps* is restored -- what `graph-of' (interactive.scm) uses to write the
;;; replayed proof's graph for the Emacs browser (2026-10-03).
(define (page--type-in text #!optional after)
  (let ((status 'error))
    ;; STDOUT IS SWALLOWED, and `quietly' is not enough to do it: `focus' reports
    ;; an out-of-range index with a bare `display', outside the quiet channel, and
    ;; a page whose leaf numbering has shifted trips that on nearly every failing
    ;; proof -- some 300 stray lines into a load log.  Capturing the port also
    ;; means a tactic that learns to print tomorrow cannot start spamming the
    ;; gate.  (What those warnings SAY is real and worth keeping in mind: a page
    ;; that mints different variable names also opens a different number of
    ;; leaves, so `(focus 5)' can address a leaf that is not there.)
    (with-output-to-string
      (lambda ()
        (call-with-current-continuation
         (lambda (bail)
           (bind-condition-handler (list condition-type:error)
             (lambda (c) (set! status 'error) (bail #f))
             (lambda ()
               (fluid-let ((*ps* *ps*)
                           (*current-goal* *current-goal*)
                           (*proof-script* *proof-script*)
                           (*live-trace* *live-trace*)
                           (*vnb-undo-stack* *vnb-undo-stack*))
                 (quietly
                  (lambda ()
                    (let ((port (string->input-port text)))
                      (let loop ()
                        (let ((form (read port)))
                          (if (eof-object? form)
                              (begin
                                (set! status
                                      (if (and *ps* (proof-done? *ps*))
                                          'grounded 'incomplete))
                                (if (not (default-object? after)) (after)))
                              (begin (eval form user-initial-environment)
                                     (loop)))))))))))))))
    status))

;;; ---------------------------------------------------------------------
;;; RETURNS DATA: one (name status minted? steps) per proof with a script.
(define *page-audit-results* '())

(define (page-audit!)
  (set! *page-audit-results*
    (let loop ((names (sort (hash-table-keys *proof-script-table*)
                            (lambda (a b) (string<? (symbol->string a)
                                                    (symbol->string b)))))
               (acc '()))
      (if (null? names)
          (reverse acc)
          (let* ((nm   (car names))
                 (text (page-of nm)))
            (loop (cdr names)
                  (if (not text)
                      acc
                      (let ((script (hash-table-ref/default *proof-script-table* nm '())))
                        (cons (list nm
                                    (page--type-in text)
                                    (page--mentions-minted? script)
                                    (length script))
                              acc))))))))
  *page-audit-results*)

(define (page-audit-results)
  (if (null? *page-audit-results*) (page-audit!) *page-audit-results*))

;;; The names whose page does not reproduce the proof, worst first: a page that
;;; RAISES is easier to chase than one that quietly stops.
(define (page-audit-failures)
  (append (map car (filter (lambda (r) (eq? (cadr r) 'error))      (page-audit-results)))
          (map car (filter (lambda (r) (eq? (cadr r) 'incomplete)) (page-audit-results)))))

;;; Of the failures, those that do NOT name a minted variable -- i.e. the ones
;;; that are a genuine driver defect rather than the counter.
(define (page-audit-failures-not-counter)
  (map car (filter (lambda (r) (and (not (eq? (cadr r) 'grounded))
                                    (not (caddr r))))
                   (page-audit-results))))

;;; ---------------------------------------------------------------------
;;; The gate line.
(define (report-page-audit)
  (let* ((rs   (page-audit-results))
         (n    (length rs))
         (ok   (length (filter (lambda (r) (eq? (cadr r) 'grounded)) rs)))
         (bad  (- n ok))
         (drv  (length (page-audit-failures-not-counter))))
    (if (= bad 0)
        (begin (display ";; page-audit: ok (all ") (display n)
               (display " proof(s) emit a re-runnable script)\n"))
        (begin
          (display ";; page-audit: ") (display ok) (display "/") (display n)
          (display " proof(s) emit a re-runnable script -- ")
          (display bad) (display " do NOT")
          (newline)
          (display ";;   of those, ") (display (- bad drv))
          (display " name a counter-minted eigenvariable (d_1787) the page cannot")
          (newline)
          (display ";;   define, and ") (display drv)
          (display " fail for another reason -- (page-audit-failures) to list,")
          (newline)
          (display ";;   (page-audit-failures-not-counter) for the second group.")
          (newline)))))
