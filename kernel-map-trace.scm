;;; kernel-map-trace.scm -- INSTRUMENT, not library; not in load.scm.
;;; Needs reference/kernel-map-static.sexp from kernel-map-static.scm first.
;;; Re-proves the library inside the band with every kernel entry point and
;;; tactic wrapped, and writes reference/kernel-map-dynamic.sexp.  With
;;; inference checking on (it is on in the band) the run takes about half an
;;; hour.  Report: reference/KERNEL-MAP.md
;;;
;;; 2026-09-20: the result is kept in the tree, and the run also records what
;;; the inference CHECKER did -- how many inferences it verified and every
;;; refusal -- since a checker that refused would leave the count short.
;;;
;;; km-dynamic2.scm -- DYNAMIC half of the kernel map, second version.
;;;
;;; Changes from km-dynamic.scm, each forced by the first run:
;;;  * NOTHING UNPREFIXED IS DEFINED HERE.  The first version did
;;;    (define ue user-initial-environment) -- and `ue' is the union-elim
;;;    TACTIC.  It overwrote the tactic with an environment object; clobber-guard
;;;    caught it on the re-run of theorem-library/axioms, and zorn-proof died
;;;    calling (ue ...).  Exactly the trap CLAUDE.md's case-fold section names.
;;;  * Re-declaring an instance that already exists is a no-op here.  In a band
;;;    that already has the instance this is semantically identical, and without
;;;    it the two exemplification files die at their first line.
;;;  * Every tactic's CALLS are counted, so "never called" and "called, wrote
;;;    nothing" (sp, qed, show ...) are no longer the same line.
;;;  * The exercise set includes the non-proof files that RUN PROOFS at load
;;;    (structure-library/subtype-laws and the like), not only proof files.
;;;  * A re-run file that redefines a wrapped name gets the wrapper back.

(define km-dir (string-append *prover-dir* "reference/"))
(define km-static (call-with-input-file (string-append km-dir "kernel-map-static.sexp") read))
(define (km-sec name) (cadr (assq name km-static)))
(define km-env user-initial-environment)

(define km-kernel-table (km-sec 'kernel))
(define (km-closure-name? s) (char=? #\< (string-ref (symbol->string s) 0)))
(define km-named-kernel (filter (lambda (e) (not (km-closure-name? (car e)))) km-kernel-table))
(define (km-static-tags entry) (let ((e (assq entry km-kernel-table))) (if e (caddr e) '())))

(define km-higher-order-skip '(quietly orelse repeat))
(define km-tactic-names
  (filter (lambda (t) (not (memq t km-higher-order-skip))) (map car (km-sec 'tactics))))

;;; ---------------------------------------------------------------- state
(define *km-kstack* '())
(define *km-tstack* '())
(define *km-edge*  (make-equal-hash-table))
(define *km-entry* (make-equal-hash-table))
(define *km-tagmap* (make-equal-hash-table))
(define *km-inconsistent* (make-equal-hash-table))
(define *km-unattributed* (make-equal-hash-table))
(define *km-calls* (make-equal-hash-table))      ; tactic -> invocations
(define *km-writes* 0)
(define *km-redeclares-skipped* 0)
(define *km-rewraps* 0)
(define (km-bump! tbl key) (hash-table-update!/default tbl key (lambda (n) (+ n 1)) 0))
(define (km-count tbl) (length (hash-table-keys tbl)))

;;; ---------------------------------------------------------------- wrapping
(define *km-wrappers* (make-strong-eqv-hash-table))   ; name -> (make . wrapper)

(define (km-rebind! name make)
  (if (environment-bound? km-env name)
      (let ((orig (environment-lookup km-env name)))
        (if (procedure? orig)
            (let ((w (make orig)))
              (environment-assign! km-env name w)
              (hash-table-set! *km-wrappers* name (cons make w))
              #t)
            #f))
      #f))

;;; after each re-run file: anything it redefined gets its wrapper back
(define (km-rewrap-all!)
  (hash-table-walk *km-wrappers*
    (lambda (name mw)
      (let ((cur (environment-lookup km-env name)))
        (if (and (procedure? cur) (not (eq? cur (cdr mw))))
            (let ((w ((car mw) cur)))
              (set! *km-rewraps* (+ *km-rewraps* 1))
              (environment-assign! km-env name w)
              (hash-table-set! *km-wrappers* name (cons (car mw) w))))))))

(define (km-kernel-frame name)
  (lambda (orig)
    (lambda args (fluid-let ((*km-kstack* (cons name *km-kstack*))) (apply orig args)))))

(define (km-tactic-frame label)
  (lambda (orig)
    (lambda args
      (km-bump! *km-calls* label)
      (fluid-let ((*km-tstack* (cons label *km-tstack*))) (apply orig args)))))

(define (km-macete-entry name)
  (case name
    ((cartesian-decompose) '<macete:cartesian-decompose>)
    ((tuple-equality-decompose) '<macete:tuple-equality-decompose>)
    (else '<elementary-macete>)))

(km-rebind! 'lookup-macete
  (lambda (orig)
    (lambda (name)
      (let ((m (orig name)))
        (if (procedure? m)
            (let ((entry (km-macete-entry name)))
              (lambda args (fluid-let ((*km-kstack* (cons entry *km-kstack*))) (apply m args))))
            m)))))

(km-rebind! 'dg-apply-rule!
  (lambda (orig)
    (lambda (dg rule hyps concl)
      (set! *km-writes* (+ *km-writes* 1))
      (let ((tag (rule-tag-head rule)))
        (if (null? *km-kstack*)
            (km-bump! *km-unattributed* (cons tag (delete-duplicates *km-tstack* eq?)))
            (let ((entry (car *km-kstack*)))
              (km-bump! *km-entry* entry)
              (km-bump! *km-tagmap* (cons tag entry))
              (if (not (memq tag (km-static-tags entry)))
                  (km-bump! *km-inconsistent* (cons tag entry)))
              (for-each (lambda (t) (km-bump! *km-edge* (cons t entry)))
                        (delete-duplicates *km-tstack* eq?)))))
      (orig dg rule hyps concl))))

;;; re-declaring an existing instance: a no-op, not an error
(km-rebind! 'declare-instance!
  (lambda (orig)
    (lambda args
      (let ((r (call-with-current-continuation
                (lambda (k)
                  (with-exception-handler
                   (lambda (e) (k (cons 'km-caught e)))
                   (lambda () (cons 'km-ok (apply orig args))))))))
        (cond ((eq? (car r) 'km-ok) (cdr r))
              ((and (condition? (cdr r))
                    (string-search-forward "already taken" (condition/report-string (cdr r)) 0))
               (set! *km-redeclares-skipped* (+ *km-redeclares-skipped* 1))
               'km-already-declared)
              (else (error (if (condition? (cdr r)) (condition/report-string (cdr r)) (cdr r)))))))))

(define km-wrapped-kernel
  (filter (lambda (e) (km-rebind! (car e) (km-kernel-frame (car e)))) km-named-kernel))
(define km-wrapped-tactics
  (append
   (filter (lambda (t) (km-rebind! t (km-tactic-frame t)))
           (filter (lambda (t) (not (memq t '(bc* vlet)))) km-tactic-names))
   (if (and (km-rebind! 'bc*-apply (km-tactic-frame 'bc*))
            (km-rebind! 'bc*-dispatch (km-tactic-frame 'bc*))) '(bc*) '())
   (if (and (km-rebind! 'vlet--match (km-tactic-frame 'vlet))
            (km-rebind! 'vlet--choice! (km-tactic-frame 'vlet))) '(vlet) '())))

(display "\n=== km-dynamic3: wrapped ") (display (length km-wrapped-kernel))
(display " named kernel entries, ") (display (length km-wrapped-tactics)) (display " tactics")
(display "   not wrapped: ")
(write (filter (lambda (t) (not (memq t km-wrapped-tactics))) km-tactic-names)) (newline)

;;; ---------------------------------------------------------------- exercise set
(define (km-forms f)
  (call-with-input-file (string-append *prover-dir* f ".scm")
    (lambda (p) (let loop ((acc '())) (let ((x (read p))) (if (eof-object? x) (reverse acc) (loop (cons x acc))))))))

(define (km-calls-any? x names)      ; does X contain a call to one of NAMES (unquoted)?
  (cond ((not (pair? x)) #f)
        ((eq? (car x) 'quote) #f)
        ((and (symbol? (car x)) (memq (car x) names)) #t)
        (else (let loop ((y x)) (and (pair? y) (or (km-calls-any? (car y) names) (loop (cdr y))))))))

;;; a non-proof file RUNS PROOFS if a top-level non-define form calls sp/qed,
;;; or calls a procedure defined in the same file whose body does
(define (km-runs-proofs? f)
  (let* ((forms (km-forms f))
         (defs  (filter (lambda (form) (and (pair? form) (eq? (car form) 'define) (pair? (cadr form))))
                        forms))
         ;; TRANSITIVE within the file: keep adding local helpers that call any
         ;; known prover until nothing changes.  One level missed
         ;; structure-library/functoriality, whose 17 proofs sit two helpers deep.
         (provers (let fix ((ps '(sp qed)))
                    (let ((more (filter (lambda (d) (and (not (memq (caadr d) ps))
                                                         (km-calls-any? (cddr d) ps)))
                                        defs)))
                      (if (null? more) ps (fix (append (map caadr more) ps)))))))
    (any (lambda (form)
           (and (pair? form)
                (not (memq (car form) '(define define-integrable define-syntax define-record-type)))
                (km-calls-any? form provers)))
         forms)))

(define km-exercise
  (filter (lambda (f) (or (proof-file? f) (km-runs-proofs? f))) *vnb-files*))
(define km-extra-files (filter (lambda (f) (not (proof-file? f))) km-exercise))
(display "exercise set: ") (display (length km-exercise)) (display " files, of which non-proof files that run proofs: ")
(write km-extra-files) (newline)

;;; ---------------------------------------------------------------- run
;;; The inference checker is armed in the band, so the re-proof is checked as
;;; it runs.  Both counters are snapshots around the exercise set: the band
;;; already carries the counts of the build that made it.
(define km-check-on? *dg-check-inferences?*)
(define km-checked-before *dg-checked-count*)
(define km-refusals-before (dg-check-refusal-count))

(define *km-file-results* '())
(define (km-run-file! f)
  (let ((r (call-with-current-continuation
            (lambda (k)
              (with-exception-handler
               (lambda (e) (k (list 'error (if (condition? e) (condition/report-string e) e))))
               (lambda () (prover-load--do f) '(ok)))))))
    (km-rewrap-all!)
    (set! *km-file-results* (cons (cons f r) *km-file-results*))))

(fluid-let ((*vnb-loading* #t))
  (for-each km-run-file! km-exercise))
(set! *km-file-results* (reverse *km-file-results*))

;;; ---------------------------------------------------------------- report
(define (km-alist tbl) (hash-table-fold tbl (lambda (k v acc) (cons (cons k v) acc)) '()))

(call-with-output-file (string-append km-dir "kernel-map-dynamic.sexp")
  (lambda (p)
    (for-each (lambda (l) (display l p) (newline p))
              (list ";;; kernel-map-dynamic.sexp -- the DYNAMIC half of the kernel map: what"
                    ";;; the library actually recorded when it was re-proved with every kernel"
                    ";;; entry point, every proof command and dg-apply-rule! instrumented."
                    ";;; Read with the Scheme reader; these comment lines are skipped."
                    ";;;"
                    ";;; REGENERATE (on a worker, not on the primary):"
                    ";;;     ./prover -b kernel-map-static.scm    < /dev/null"
                    ";;;     ./prover -b kernel-map-trace.scm     < /dev/null   # this file"
                    ";;; The second re-proves the whole library and takes about half an hour."
                    ";;; reference/KERNEL-MAP.md is written from the two together."))
    (write (list (list 'writes *km-writes*)
                 (list 'checking (list (list 'on km-check-on?)
                                       (list 'verified (- *dg-checked-count* km-checked-before))
                                       (list 'refusals (- (dg-check-refusal-count)
                                                          km-refusals-before))
                                       (list 'checkers-registered
                                             (length (registered-rule-checkers)))
                                       (list 'on-trust (trusted-oracle-rules))))
                 (list 'edges (km-alist *km-edge*))
                 (list 'entries (km-alist *km-entry*))
                 (list 'tagmap (km-alist *km-tagmap*))
                 (list 'inconsistent (km-alist *km-inconsistent*))
                 (list 'unattributed (km-alist *km-unattributed*))
                 (list 'calls (km-alist *km-calls*))
                 (list 'files (map (lambda (r) (list (car r) (cadr r))) *km-file-results*))
                 (list 'file-errors (filter (lambda (r) (eq? (cadr r) 'error)) *km-file-results*))
                 (list 'extra-files km-extra-files)
                 (list 'redeclares-skipped *km-redeclares-skipped*)
                 (list 'rewraps *km-rewraps*)
                 (list 'wrapped-tactics km-wrapped-tactics)
                 ;; how many stored proofs the BUILD has, against which the
                 ;; re-proof's `qed' count says what the run covered
                 (list 'results-in-build (length (hash-table-keys *proof-script-table*))))
           p)
    (newline p)))

(display "\n=== kernel-map-dynamic summary\n")
(display "inference checking: ") (display (if km-check-on? "ON" "OFF"))
(display ", ") (display (- *dg-checked-count* km-checked-before)) (display " verified, ")
(display (- (dg-check-refusal-count) km-refusals-before)) (display " refusal(s); ")
(display (length (registered-rule-checkers))) (display " checkers, ")
(display (length (trusted-oracle-rules))) (display " on trust") (newline)
(display "files run: ") (display (length *km-file-results*))
(display "   clean: ") (display (length (filter (lambda (r) (eq? (cadr r) 'ok)) *km-file-results*)))
(display "   errored: ") (display (length (filter (lambda (r) (eq? (cadr r) 'error)) *km-file-results*))) (newline)
(display "graph writes: ") (display *km-writes*) (newline)
(display "entries fired: ") (display (km-count *km-entry*)) (display " of ") (display (length km-kernel-table)) (newline)
(display "UNATTRIBUTED: ") (display (hash-table-fold *km-unattributed* (lambda (k v a) (+ v a)) 0))
(display "   INCONSISTENT: ") (display (hash-table-fold *km-inconsistent* (lambda (k v a) (+ v a)) 0)) (newline)
(display "tactics called: ") (display (km-count *km-calls*))
(display "   redeclares skipped: ") (display *km-redeclares-skipped*)
(display "   wrappers restored: ") (display *km-rewraps*) (newline)
