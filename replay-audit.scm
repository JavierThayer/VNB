;;; replay-audit.scm -- does a recorded proof SCRIPT replay to a grounded graph?
;;;
;;; NOT in load.scm: an instrument, like harvest.scm.  Run it against the band --
;;;
;;;   mit-scheme --quiet --band vnb.band \
;;;     --eval '(begin (load "replay-audit.scm") (ra-run!) (exit))' < /dev/null
;;;
;;; `(ra-run!)' takes every script in *proof-script-table*; `(ra-run! N STRIDE)'
;;; samples.  THREE outcomes, not two -- harvest.scm reports only "replayed" vs
;;; "failed", which hides the third and it is the dangerous one:
;;;
;;;   grounded    -- the replay ends with `proof-done?'.  The script reproduces
;;;                  the proof.
;;;   incomplete  -- every step ran, no error, and the graph is NOT grounded.
;;;                  SILENT.  Worse than an error.
;;;   error       -- a step raised.  Loud, and where you want to be.
;;;
;;; It restores `*fresh-counter*' from `*proof-start-counter*' the way proof-tex's
;;; replay does.  Without that, a recorded `ai'/`ew' witness (`u_4') names a
;;; variable this replay never minted and the script "fails" for a reason that is
;;; the harness's, not the script's -- which is what happened to harvest.scm and
;;; cost about 200 scripts of its 2026-08-19 baseline.
;;;
;;; Companion: scratchpad/ra-diverge.scm diffs a replay against
;;; *proof-live-trace* step for step, and is how you tell a replay that lands
;;; somewhere else from one that merely stops.

(define *ra* '())          ; (name status stepno cmd msg nsteps)

(define (ra--one name)
  (let ((goal   (ignore-errors (lambda () (lookup-theorem name))))
        (script (hash-table-ref/default *proof-script-table* name '())))
    (if (not (and (pair? goal) (pair? script)))
        (set! *ra* (cons (list name 'no-script 0 #f "" 0) *ra*))
        (let ((i 0) (cur #f) (n (length script)))
          (call-with-current-continuation
           (lambda (bail)
             (bind-condition-handler (list condition-type:error)
               (lambda (c)
                 (set! *ra* (cons (list name 'error i (and (pair? cur) (car cur))
                                        (condition/report-string c) n) *ra*))
                 (bail #f))
               (lambda ()
                 (quietly
                  (lambda ()
                   ;; Restore the fresh-var counter to this proof's sp-time
                   ;; value, as proof-tex's replay does: eigenvariable names
                   ;; (ai/ew witnesses) are minted from a monotonic global, and
                   ;; without this the recorded witness `u_4' names a variable
                   ;; the replay never created.
                   (fluid-let ((*fresh-counter*
                                (hash-table-ref/default *proof-start-counter*
                                                        name *fresh-counter*)))
                    (sp (make-wff goal))
                    (for-each (lambda (entry)
                                (set! i (+ i 1)) (set! cur entry)
                                (fluid-let ((*replaying?* #t))
                                  (apply-recorded-cmd! (car entry) (cdr entry))))
                              script))))
                 (set! *ra* (cons (list name
                                        (if (proof-done? *ps*) 'grounded 'incomplete)
                                        i #f "" n)
                                  *ra*))))))))))

(define (ignore-errors th)
  (call-with-current-continuation
   (lambda (k) (bind-condition-handler (list condition-type:error)
                 (lambda (c) (k #f)) th))))

(define (ra-run! #!optional limit stride)
  (set! *ra* '())
  (let* ((all (sort (hash-table-keys *proof-script-table*)
                    (lambda (a b) (string<? (symbol->string a) (symbol->string b)))))
         (st  (if (default-object? stride) 1 stride))
         (sel (let loop ((l all) (k 0) (acc '()))
                (cond ((null? l) (reverse acc))
                      ((= 0 (remainder k st)) (loop (cdr l) (+ k 1) (cons (car l) acc)))
                      (else (loop (cdr l) (+ k 1) acc)))))
         (names (if (default-object? limit) sel
                    (list-head sel (min limit (length sel))))))
    (for-each ra--one names)
    (ra-report!)))

(define (ra--count s) (length (filter (lambda (r) (eq? (cadr r) s)) *ra*)))

(define (ra-report!)
  (newline)
  (display ";; ==== REPLAY AUDIT: ") (display (length *ra*)) (display " scripts ====") (newline)
  (for-each (lambda (s)
              (display ";;   ") (display s) (display " : ") (display (ra--count s)) (newline))
            '(grounded incomplete error no-script))
  ;; error message classes
  (let ((h (make-equal-hash-table)))
    (for-each (lambda (r)
                (when (eq? (cadr r) 'error)
                  (let* ((msg (list-ref r 4))
                         ;; first 60 chars of the message = the class
                         (k (cons (list-ref r 3)
                                  (substring msg 0 (min 58 (string-length msg))))))
                    (hash-table-set! h k (+ 1 (hash-table-ref/default h k 0))))))
              *ra*)
    (newline)
    (display ";; -- error classes (cmd . message) --") (newline)
    (for-each (lambda (p)
                (display ";;  ") (display (cdr p)) (display "  ") (display (car p)) (newline))
              (sort (map (lambda (k) (cons k (hash-table-ref h k 0))) (hash-table-keys h))
                    (lambda (a b) (> (cdr a) (cdr b))))))
  ;; how far in did errors happen
  (let ((es (filter (lambda (r) (eq? (cadr r) 'error)) *ra*)))
    (newline)
    (display ";; -- first 12 error scripts (name step/total cmd) --") (newline)
    (for-each (lambda (r)
                (display ";;  ") (display (car r)) (display "  step ")
                (display (caddr r)) (display "/") (display (list-ref r 5))
                (display "  ") (display (list-ref r 3)) (newline))
              (list-head es (min 12 (length es)))))
  (let ((is (filter (lambda (r) (eq? (cadr r) 'incomplete)) *ra*)))
    (newline)
    (display ";; -- first 12 INCOMPLETE (ran to end, not grounded) --") (newline)
    (for-each (lambda (r) (display ";;  ") (display (car r))
                      (display "  steps ") (display (list-ref r 5)) (newline))
              (list-head is (min 12 (length is))))))
