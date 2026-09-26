;;; certificates.scm -- PROOF CERTIFICATES: a load that runs no proof.
;;;
;;; The user's decision of 2026-09-24 (docs/certificates-2026-09-24.md): the
;;; everyday load installs theorems from CERTIFICATES written by a run that
;;; proved and checked them; the proofs run separately, in the exam
;;; (`VNB_CERTIFIED=off ./prover --build-band').
;;;
;;; THE STORE.  One file per theorem-library (or calculus) proof file,
;;; certificates/<load-list key>.cert, one record per `qed' of the file, in the
;;; order the theorems were installed:
;;;
;;;   (NAME "STATEMENT-HASH" STATEMENT
;;;         (cites (NAME . "HASH") ...)   ; the names the ledger read off the script
;;;         (defs (NAME . "HASH") ...)    ; the defined heads the statement mentions
;;;         (own-oracles VERB ...)        ; the oracles the script called directly
;;;         (bill NAME ...) (oracles VERB ...)   ; what qed announced
;;;         (kernel "KERNEL-HASH") (date "YYYY-MM-DD") (host "..."))
;;;
;;; A HASH is the MD5 of the canonical text of a statement: `write' of the
;;; formula with every counter-minted name (x_1234) relabelled x_#k in order of
;;; first occurrence and every uninterned symbol %gk, so the hash does not depend
;;; on how much was proved before (band-dump.scm relabels the same way).  The
;;; hash of a CITED name is `T'+ the hash of its installed statement, `F'+ the
;;; hash of its functoid definition (params and body) when it is a functoid
;;; macete and no theorem, and "-" when it is neither.
;;;
;;; VALIDITY.  A record is valid in a load when the statement `sp' starts hashes
;;; to its STATEMENT-HASH, every (NAME . HASH) of its cites and defs hashes the
;;; same here, and its kernel hash is this tree's.  The KERNEL HASH is the MD5 of
;;; the source text of the files that may call `dg-apply-rule!'
;;; (*kernel-caller-files*, audit.scm, repeated below because audit.scm loads
;;; long after the first proof; the end of the load checks the two lists agree)
;;; and of the four rule-checker files.  Tactics, the kit and the drivers are not
;;; in the key: every inference they produce is checked by the kernel.
;;;
;;; THE SWITCH.  VNB_CERTIFIED=on | off | strict, read when a load-list proof
;;; file is loaded (default on):
;;;   off     every proof runs (today's loader, one `load' per file); every
;;;           certificate of the canonical tree is rewritten.
;;;   on      a theorem whose record is valid is installed from it and its proof
;;;           skipped; a theorem without one is PROVED and its record written.
;;;   strict  certified theorems are installed, nothing is proved; the theorems
;;;           without a valid certificate are listed and the load exits non-zero.
;;;
;;; THE CERTIFIED LOADER (`cert-load-proof-file!', called by load.scm's
;;; prover-load--file for a contained proof file).  In on / strict mode the file
;;; is read FORM BY FORM from its .scm and each form is `eval'ed in a fresh file
;;; environment, as `load' would.  `sp' hashes its statement and looks it up; on
;;; a valid record it installs the theorem (`install-from-certificate!'), sets
;;; the SKIP STATE and escapes the current top-level form.  While the skip state
;;; is set, a top-level form that errors is swallowed (its output too); `qed'
;;; checks its name against the record and clears the state.  A body (lambda,
;;; define, let, begin, ...) in which `(sp X)' is followed by `(qed N)' is
;;; rewritten before evaluation so that the forms between run only when the
;;; proof is being proved (`cert-proof-running?'), and that `sp' does not escape:
;;; this is what lets a helper called in a loop (`(for-each prove! instances)')
;;; install every instance.  At the end of the file every name of its
;;; certificate must have been installed, no form may have failed outside the
;;; skip state and no `qed' may have failed; otherwise the file is RETRACTED
;;; (every name it installed) and RELOADED in off mode, with a warning naming it
;;; (strict mode lists its theorems as uncovered instead).  A file with no
;;; certificate, or one written under another kernel, loads in off mode at once.
;;;
;;; Structure-library and root files are never certified.  Nothing here writes
;;; an inference: `install-from-certificate!' installs a THEOREM through
;;; `add-theorem!', as `qed' does.

;;; ---------------------------------------------------------------- the switch
(define *cert-mode-override* #f)          ; the suite's controls bind this

(define (cert-mode)
  (or *cert-mode-override*
      (let ((v (get-environment-variable "VNB_CERTIFIED")))
        (cond ((or (not v) (string-null? v) (string=? v "on")) 'on)
              ((string=? v "off") 'off)
              ((string=? v "strict") 'strict)
              (#t (error "VNB_CERTIFIED must be on, off or strict, not" v))))))

;;; *cert-in-load-list* and *vnb-write-certs* are DEFINED IN load.scm, above its
;;; file loop (this file loads inside the loop, so a definition here would reset
;;; them): #t while load.scm loads its list and only then, so a proof file loaded
;;; by anything else (a probe, extend-band's reload, the REPL) is loaded as today
;;; and writes no certificate; the store is written unless VNB_WRITE_CERTS=0.

(define *cert-dir-override* #f)
(define (cert-dir)
  (or *cert-dir-override* (string-append *prover-dir* "certificates/")))

(define (cert-path f) (string-append (cert-dir) f ".cert"))

;;; Where a load-list key's SOURCE is read from in a certified pass (the suite's
;;; fixtures live outside the tree).
(define *cert-src-root-override* #f)
(define (cert-source-path f)
  (string-append (or *cert-src-root-override* *prover-dir*) f ".scm"))

;;; ---------------------------------------------------------------- hashing
(define (cert--hex bv)
  (let loop ((i 0) (acc '()))
    (if (= i (bytevector-length bv))
        (apply string-append (reverse acc))
        (let* ((b (bytevector-u8-ref bv i))
               (s (number->string b 16)))
          (loop (+ i 1) (cons (if (< b 16) (string-append "0" s) s) acc))))))

(define (cert-md5 str) (cert--hex (md5-string str)))

;;; "b_6420" -> "b" ; "x_6454_2" -> "x" ; otherwise #f  (band-dump.scm's rule)
(define (cert--minted-base str)
  (define (strip-one s)
    (let loop ((i (- (string-length s) 1)))
      (cond ((< i 0) #f)
            ((char-numeric? (string-ref s i)) (loop (- i 1)))
            ((and (char=? (string-ref s i) #\_)
                  (< i (- (string-length s) 1))
                  (> i 0))
             (substring s 0 i))
            (#t #f))))
  (let ((once (strip-one str)))
    (and once
         (let loop ((s once))
           (let ((again (strip-one s)))
             (if again (loop again) s))))))

;;; The canonical text of a formula (or of any S-expression of symbols, numbers,
;;; strings, lists).
(define (cert-canon x)
  (let ((seen (make-strong-eqv-hash-table))
        (n 0))
    (define (relabel s)
      (or (hash-table-ref/default seen s #f)
          (let ((new
                 (cond ((uninterned-symbol? s)
                        (set! n (+ n 1))
                        (string->symbol (string-append "%g" (number->string n))))
                       ((cert--minted-base (symbol->string s))
                        => (lambda (base)
                             (set! n (+ n 1))
                             (string->symbol (string-append base "_#" (number->string n)))))
                       (#t s))))
            (hash-table-set! seen s new)
            new)))
    (define (walk y)
      (cond ((symbol? y) (relabel y))
            ((pair? y) (let* ((a (walk (car y))) (d (walk (cdr y)))) (cons a d)))
            ((vector? y) (list->vector (map walk (vector->list y))))
            (#t y)))
    (with-output-to-string (lambda () (write (walk x))))))

(define (cert-statement-hash f) (cert-md5 (cert-canon f)))

;;; The hash a CITED name has in this image.  Memoised per name on the
;;; statement object (a reinstall replaces the object, so the memo cannot go stale).
(define *cert-hash-memo* (make-strong-eqv-hash-table))   ; name -> (formula . hash)
(define (cert-name-hash name)
  (let ((thm (hash-table-ref/default *theorem-table* name #f)))
    (cond (thm (let ((m (hash-table-ref/default *cert-hash-memo* name #f)))
                 (if (and m (eq? (car m) thm))
                     (cdr m)
                     (let ((h (string-append "T" (cert-statement-hash thm))))
                       (hash-table-set! *cert-hash-memo* name (cons thm h))
                       h))))
          ((hash-table-ref/default *functoid-registry* name #f)
           => (lambda (e) (string-append "F" (cert-md5 (cert-canon (list (car e) (cadr e)))))))
          (#t "-"))))

;;; ---------------------------------------------------------------- the kernel hash
(define *cert-kernel-files*
  '("primitive-inferences" "macetes" "library" "arith-eval"
    "structure-library/comm-ring-simplify" "structure-library/ineq-oracle"
    "structure-library/ring-simplify" "structure-library/sos-oracle"
    "rule-checkers-logic" "rule-checkers-schema" "rule-checkers-rewrite"
    "rule-checkers-oracle"))

(define *cert-kernel-hash* #f)            ; computed once per load; the suite binds it

(define (cert-kernel-hash)
  (or *cert-kernel-hash*
      (begin
        (set! *cert-kernel-hash*
              (cert-md5
               (apply string-append
                      (map (lambda (f)
                             (let ((p (string-append *prover-dir* f ".scm")))
                               (string-append f ":"
                                              (if (file-exists? p) (cert--hex (md5-file p)) "absent")
                                              ";")))
                           *cert-kernel-files*))))
        *cert-kernel-hash*)))

;;; End of load: *kernel-caller-files* (audit.scm) must be inside the key.
(define (cert-kernel-files-audit)
  (filter (lambda (f) (not (member f *cert-kernel-files*))) *kernel-caller-files*))

;;; ---------------------------------------------------------------- the date and host
(define (cert--today)
  (let* ((d (local-decoded-time))
         (two (lambda (k) (if (< k 10) (string-append "0" (number->string k)) (number->string k)))))
    (string-append (number->string (decoded-time/year d)) "-"
                   (two (decoded-time/month d)) "-" (two (decoded-time/day d)))))

(define (cert--host)
  (let ((v (get-environment-variable "VNB_HOST")))
    (if (and v (not (string-null? v))) v
        (call-with-current-continuation
         (lambda (k) (with-exception-handler (lambda (e) (k "unknown"))
                       (lambda () (os/hostname))))))))

;;; ---------------------------------------------------------------- records
(define (cert-rec-name r) (car r))
(define (cert-rec-hash r) (cadr r))
(define (cert-rec-statement r) (caddr r))
(define (cert-rec-field r key)
  (let ((e (assq key (cdddr r)))) (if e (cdr e) '())))
(define (cert-rec-field1 r key)
  (let ((v (cert-rec-field r key))) (if (pair? v) (car v) #f)))

;;; The statement `qed' will install for the proof state PS -- cmd-qed's own
;;; computation (proof-commands.scm), repeated: the root's assumptions wrapped
;;; outermost first, destructuring quantifiers expanded.
(define (cert-qed-statement ps)
  (let* ((root (proof-state-root ps))
         (asms (sequent-node-assumptions root))
         (assertion (wff-formula (sequent-node-assertion root)))
         (wrapped (let loop ((rest asms))
                    (if (null? rest) assertion
                        `(FORALL ,(wff-formula (car rest)) ,(loop (cdr rest)))))))
    (expand-destructuring-quantifiers wrapped)))

;;; The defined heads a statement mentions: every symbol that names an installed
;;; theorem or a functoid, other than NAME itself.
(define (cert--defs-of stmt name)
  (let ((acc '()))
    (let walk ((x stmt))
      (cond ((symbol? x)
             (if (and (not (eq? x name)) (not (memq x acc))
                      (or (hash-table-ref/default *theorem-table* x #f)
                          (hash-table-ref/default *functoid-registry* x #f)))
                 (set! acc (cons x acc))))
            ((pair? x) (walk (car x)) (walk (cdr x)))))
    (sort acc (lambda (a b) (string<? (symbol->string a) (symbol->string b))))))

(define (cert--self? c name)
  (or (eq? c name) (eq? (rev-companion-source c) name)))

;;; The record for NAME, just proven (called by qed--guarded after the ledger).
(define (cert-make-record name bill)
  (let* ((stmt (hash-table-ref/default *theorem-table* name #f))
         (cites (filter (lambda (c) (not (cert--self? c name))) *pd-last-citations*)))
    (list name (cert-statement-hash stmt) stmt
          (cons 'cites (map (lambda (c) (cons c (cert-name-hash c))) cites))
          (cons 'defs (map (lambda (c) (cons c (cert-name-hash c))) (cert--defs-of stmt name)))
          (cons 'own-oracles (script-oracles *proof-script*))
          (cons 'bill bill)
          (cons 'oracles (hash-table-ref/default *proof-oracles* name '()))
          (list 'kernel (cert-kernel-hash))
          (list 'date (cert--today))
          (list 'host (cert--host)))))

;;; Why RECORD is not valid here, or #f when it is.
(define (cert-record-invalid-reason rec)
  (cond ((not (equal? (cert-rec-field1 rec 'kernel) (cert-kernel-hash))) "kernel changed")
        (#t
         (let loop ((ps (append (cert-rec-field rec 'cites) (cert-rec-field rec 'defs))))
           (cond ((null? ps) #f)
                 ((not (equal? (cert-name-hash (caar ps)) (cdar ps)))
                  (string-append "statement of " (symbol->string (caar ps)) " changed"))
                 (#t (loop (cdr ps))))))))

;;; ---------------------------------------------------------------- the store
(define (cert--ensure-dir! dir)
  (if (not (file-directory? dir))
      (let ((parent (directory-namestring
                     (->pathname (substring dir 0 (- (string-length dir) 1))))))
        (if (and (> (string-length parent) 1) (not (string=? parent dir)))
            (cert--ensure-dir! parent))
        (if (not (file-directory? dir)) (make-directory dir)))))

;;; -> (header . records), or #f when the file has no certificate.
(define (cert-read-file f)
  (let ((p (cert-path f)))
    (and (file-exists? p)
         (call-with-current-continuation
          (lambda (k)
            (with-exception-handler
             (lambda (e) (k #f))                 ; an unreadable store is no store
             (lambda ()
               (call-with-input-file p
                 (lambda (port)
                   (let ((header (read port)))
                     (if (not (and (pair? header) (eq? (car header) 'vnb-certificate-file)))
                         #f
                         (let loop ((acc '()))
                           (let ((r (read port)))
                             (if (eof-object? r)
                                 (cons header (reverse acc))
                                 (loop (cons r acc))))))))))))))))

(define (cert-write-file! f records)
  (let* ((p (cert-path f))
         (tmp (string-append p ".tmp")))
    (cert--ensure-dir! (directory-namestring (->pathname p)))
    (call-with-output-file tmp
      (lambda (port)
        (write-string ";;; VNB proof certificates for " port)
        (write-string f port)
        (write-string ".scm -- written by a load that proved them; do not edit.\n" port)
        (write (list 'vnb-certificate-file f
                     (list 'kernel (cert-kernel-hash))
                     (list 'date (cert--today))
                     (list 'host (cert--host))
                     (list 'count (length records)))
               port)
        (newline port)
        (for-each (lambda (r) (write r port) (newline port)) records)))
    (rename-file tmp p)
    p))

;;; ---------------------------------------------------------------- session state
(define *certified-theorems* (make-equal-hash-table))   ; name -> (date host)
(define *cert-session-proven* 0)         ; proofs that RAN in this session (load-list files)
(define *cert-session-certified* 0)      ; theorems installed from a certificate
(define *cert-uncovered* '())            ; strict: (name-or-hash . reason), newest first
(define *cert-fallbacks* '())            ; (file . reason), newest first
(define *cert-files-written* 0)
(define *cert-console* #f)               ; the load's real output port

(define (certified-theorem? name) (and (hash-table-ref/default *certified-theorems* name #f) #t))

;;; per file
(define *cert-file* #f)                  ; load-list key of the proof file being loaded
(define *cert-file-mode* 'off)
(define *cert-records* '())              ; ((record . used?) ...) read from the store
(define *cert-new-records* '())          ; the file's records in install order, reversed
(define *cert-changed?* #f)              ; a record was written anew in this pass
(define *cert-skip* #f)                  ; #f | (certified NAME) | (uncovered HASH NAME-or-#f)
(define *cert-escape* #f)                ; aborts the current top-level form
(define *cert-no-escape* #f)             ; set by a rewritten body around its `sp'
(define *cert-loader-error* #f)          ; why the certified pass failed, or #f
(define *cert-installed* '())            ; names installed by this pass (either path)

(define (cert-proof-running?) (not *cert-skip*))

(define (cert--say . parts)
  (let ((port (or *cert-console* (current-output-port))))
    (for-each (lambda (p) (display p port)) parts)
    (newline port)))

;;; ---------------------------------------------------------------- installing
;;; Install NAME : STMT (the statement `sp' computed in THIS load, which hashes
;;; to the record's) from RECORD.  Exactly what cmd-qed and qed--guarded do from
;;; the statement, minus the proof: the theorem through add-theorem!
;;; (install-theorem! mints the -rev companion and stamps both), the name on
;;; *proven-theorem-names*, and the ledger's three tables.  The bill and the
;;; oracles are recomputed from the recorded citations exactly as
;;; record-proof-debt! computes them, so a cited name whose provenance changed
;;; since the exam (proven -> asserted) shows on the bill; the recorded bill is
;;; compared and a difference is printed.  No script, no mint record, no live
;;; trace: the entry in *certified-theorems* is the mark that the proof is absent.
(define (install-from-certificate! rec stmt)
  (let* ((name  (cert-rec-name rec))
         (cites (map car (cert-rec-field rec 'cites))))
    (fluid-let ((*current-provenance* 'certified))
      (add-theorem! *library* name stmt))
    (register-proven-theorem! name)
    (hash-table-set! *proof-citation-graph* name
      (filter (lambda (c) (and (not (eq? c name))
                               (not (eq? (provenance-of c) 'definitional))))
              cites))
    (hash-table-set! *proof-oracles* name
      (let loop ((cs cites) (ors (cert-rec-field rec 'own-oracles)))
        (if (null? cs) ors (loop (cdr cs) (pd-union ors (oracles-of (car cs)))))))
    (let ((bill (let loop ((cs cites) (bill '()))
                  (if (null? cs) bill (loop (cdr cs) (pd-union bill (debt-of (car cs))))))))
      (hash-table-set! *proof-debt* name bill)
      (hash-table-set! *certified-theorems* name
                       (list (or (cert-rec-field1 rec 'date) "?")
                             (or (cert-rec-field1 rec 'host) "?")))
      (set! *cert-session-certified* (+ *cert-session-certified* 1))
      (let ((port (or *cert-console* (current-output-port))))
        (cert--with-output-to-port port
          (lambda ()
            (announce-proof-debt name bill
                                 (string-append "certified (exam "
                                                (or (cert-rec-field1 rec 'date) "?") ")"))
            (if (not (equal? (sort (map symbol->string bill) string<?)
                             (sort (map symbol->string (cert-rec-field rec 'bill)) string<?)))
                (begin (display ";;   (the exam's bill was ")
                       (pd-display-set (cert-rec-field rec 'bill))
                       (display "; a cited name changed provenance since)")
                       (newline))))))
      name)))

(define (cert--with-output-to-port port thunk)
  (parameterize ((current-output-port port)) (thunk)))

;;; ---------------------------------------------------------------- the hooks
;;; interactive.scm calls these through *cert-sp-hook*, *cert-qed-hook* and
;;; *cert-record-hook* (it loads before this file).

;;; End of `sp', with *ps* the fresh proof.  Returns normally when the proof is
;;; to be PROVED; otherwise installs (or, in strict, records) and escapes.
(define (cert--on-sp!)
  (if (and *cert-file* (memq *cert-file-mode* '(on strict)))
      ;; An error in here is the LOADER's, never the proof's: it fails the pass
      ;; (fallback), it is not swallowed by sp's vnb-guard.
      (call-with-current-continuation
       (lambda (k)
         (with-exception-handler
          (lambda (e)
            (set! *cert-loader-error*
                  (or *cert-loader-error*
                      (string-append "certificate install failed: " (cert--msg e))))
            (set! *ps* #f)
            (if *cert-escape* (*cert-escape* 'escaped) (k 'error)))
          cert--on-sp-1!)))))

(define (cert--on-sp-1!)
  (if #t
      (begin
        ;; A new sp ends any skip state: the skipped proof's qed was inside the
        ;; form the escape aborted.
        (cert--close-skip!)
        (let* ((stmt (cert-qed-statement *ps*))
               (h    (cert-statement-hash stmt))
               (cell (find-first (lambda (c) (and (not (cdr c)) (equal? (cert-rec-hash (car c)) h)))
                                 *cert-records*))
               (rec  (and cell (car cell)))
               (why  (if rec (cert-record-invalid-reason rec) "no certificate for this statement")))
          (if cell (set-cdr! cell #t))
          (cond ((not why)
                 (install-from-certificate! rec stmt)
                 (set! *cert-installed* (cons (cert-rec-name rec) *cert-installed*))
                 (set! *cert-new-records* (cons rec *cert-new-records*))
                 (set! *cert-skip* (list 'certified (cert-rec-name rec)))
                 (set! *ps* *cert-finished-ps*)
                 (cert--escape!))
                ((eq? *cert-file-mode* 'strict)
                 (set! *cert-skip* (list 'uncovered h (and rec (cert-rec-name rec)) why))
                 (set! *ps* *cert-finished-ps*)
                 (cert--escape!))
                (#t
                 (if rec
                     (cert--say ";; certificate of " (cert-rec-name rec)
                                " not valid (" why "): proving it")
                     (cert--say ";; no certificate of " *cert-file*
                                " matches the statement this sp starts: proving it"))
                 'prove))))))

;;; WHAT *ps* HOLDS WHILE A PROOF IS SKIPPED: a FINISHED proof with no focus.
;;; A driver very often closes a proof through a helper -- (define (done! n)
;;; (if (proof-done? *ps*) (begin (qed n) (topic! n 'algebra)) (error ...))) --
;;; and with *ps* #f such a helper errors before its qed and, worse, before its
;;; topic!, gloss! or alias! (224 topics were lost that way in the first strict
;;; load).  With this state `proof-done?' answers #t as it would in off mode after
;;; the proof's last step, so the helper reaches its qed (which the hook handles)
;;; and its metadata; every TACTIC still fails at once, on the absent focus,
;;; before it can reach the kernel.  Built once per image, from a two-step proof
;;; (the only inferences this file causes).
(define *cert-finished-ps*
  (let ((ps (start-proof (make-wff '(IMPLIES (IN cert-dummy-x RR) (IN cert-dummy-x RR))))))
    (cmd-direct-inference ps)
    (cmd-assumption ps)
    (if (not (proof-done? ps))
        (error "certificates: the finished placeholder proof did not close"))
    (make-proof-state (proof-state-dg ps) (proof-state-root ps) #f)))

;;; End a skip state whose qed was never evaluated.  An UNCOVERED proof (strict)
;;; is listed by its recorded name, else by its statement hash.
(define (cert--close-skip!)
  (let ((s *cert-skip*))
    (set! *cert-skip* #f)
    (if (and s (eq? (car s) 'uncovered))
        (set! *cert-uncovered*
              (cons (cons (or (caddr s) (string-append "statement " (cadr s)))
                          (string-append *cert-file* ": " (cadddr s)))
                    *cert-uncovered*)))))

(define (cert--escape!)
  (if (and (not *cert-no-escape*) *cert-escape*)
      (*cert-escape* 'escaped)
      'skip))

;;; Top of `qed'.  #t when the qed belongs to a skipped proof (and is handled).
;;; After it the state is (closed NAME): until the next sp, the forms that
;;; follow a skipped proof's qed are the ones that, in off mode, would see the
;;; FINISHED proof in *ps* (a leftover `(display (dk-goal))', a check of the
;;; closed state); here *ps* is #f, so their errors are swallowed too.
(define (cert--on-qed! name)
  (and *cert-file* *cert-skip*
       (let ((s *cert-skip*))
         (set! *cert-skip* #f)
         (case (car s)
           ((certified)
            (if (not (eq? name (cadr s)))
                (set! *cert-loader-error*
                      (or *cert-loader-error*
                          (string-append "qed " (symbol->string name)
                                         " closed the skipped proof of "
                                         (symbol->string (cadr s))))))
            (set! *cert-skip* (list 'closed name))
            #t)
           ((uncovered)
            (set! *cert-uncovered*
                  (cons (cons name (string-append *cert-file* ": " (cadddr s)))
                        *cert-uncovered*))
            (set! *cert-skip* (list 'closed name))
            #t)
           ;; a second qed after a skipped proof's own: in off mode it would install
           ;; the finished proof under another name; here it runs, fails for want of
           ;; a proof, and the qed-failure check sends the file to the fallback
           (else (set! *cert-skip* s) #f)))))

;;; After a qed has installed NAME and announced BILL.
(define (cert--on-record! name bill)
  (set! *cert-session-proven* (+ *cert-session-proven* 1))
  (if *cert-file*
      (begin
        (set! *cert-installed* (cons name *cert-installed*))
        (set! *cert-changed?* #t)
        (set! *cert-new-records* (cons (cert-make-record name bill) *cert-new-records*)))))

(set! *cert-sp-hook* cert--on-sp!)
(set! *cert-qed-hook* cert--on-qed!)
(set! *cert-record-hook* cert--on-record!)

;;; A certified theorem is proven for every purpose that asks: the definedness
;;; certificate's trust test reads provenance through this hook (it lives in
;;; primitive-inferences.scm, which this file does not edit).
(set! *pi-provenance-of*
      (lambda (name)
        (let ((p (provenance-of name)))
          (if (eq? p 'certified) 'proven p))))
(if (not (memq 'certified *provenance-kinds*))
    (set! *provenance-kinds* (append *provenance-kinds* '(certified))))

;;; ---------------------------------------------------------------- the body rewrite
;;; In every BODY (the forms of a lambda, define, let-family, begin, when,
;;; unless, fluid-let) where `(sp X)' is followed, at the same level, by
;;; `(qed N)' with no other sp and no internal define between them, the forms
;;; between become (if (cert-proof-running?) (begin ...)) and the sp becomes
;;; (cert-sp/body X).  Nothing inside a quote is touched.
(define (cert--call? x head) (and (pair? x) (eq? (car x) head) (list? x)))

(define (cert--define-form? x)
  (and (pair? x) (memq (car x) '(define define-syntax define-record-type define-values define-integrable))))

(define (cert--contains-call? x head)
  (cond ((not (pair? x)) #f)
        ((memq (car x) '(quote quasiquote)) #f)
        ((eq? (car x) head) #t)
        (#t (let loop ((l x))
              (cond ((pair? l) (or (cert--contains-call? (car l) head) (loop (cdr l))))
                    (#t #f))))))

;;; The argument E of the one (qed E) inside X when there is exactly one and E is
;;; plain (no sp, qed, set! or define in it); else #f.
(define (cert--qed-arg-in x)
  (let ((found '()))
    (let walk ((y x))
      (cond ((not (pair? y)) 'done)
            ((memq (car y) '(quote quasiquote)) 'done)
            ((and (eq? (car y) 'qed) (list? y) (= (length y) 2))
             (set! found (cons (cadr y) found)))
            (#t (let loop ((l y))
                  (if (pair? l) (begin (walk (car l)) (loop (cdr l))))))))
    (and (= (length found) 1)
         (let ((e (car found)))
           (and (not (cert--contains-call? e 'sp))
                (not (cert--contains-call? e 'qed))
                (not (cert--contains-call? e 'set!))
                (not (cert--contains-call? e 'define))
                e)))))

;;; The forms that follow the qed in the innermost BODY that holds it as an
;;; element -- `(let (...) ... (qed name) (topic! name 'analysis))' gives
;;; ((topic! name 'analysis)) -- so the skipped branch keeps the metadata.  '()
;;; when the qed is not an element of a body (an `if' arm).
(define (cert--qed-tail x)
  (define (body-of y)
    (cond ((not (and (pair? y) (list? y))) #f)
          ((memq (car y) '(quote quasiquote)) #f)
          ((and (memq (car y) '(lambda named-lambda)) (>= (length y) 2)) (cddr y))
          ((and (eq? (car y) 'define) (>= (length y) 2) (pair? (cadr y))) (cddr y))
          ((and (eq? (car y) 'let) (>= (length y) 3) (symbol? (cadr y))) (cdddr y))
          ((and (memq (car y) '(let let* letrec letrec* fluid-let parameterize)) (>= (length y) 2)) (cddr y))
          ((eq? (car y) 'begin) (cdr y))
          ((and (memq (car y) '(when unless)) (>= (length y) 2)) (cddr y))
          (#t #f)))
  (call-with-current-continuation
   (lambda (return)
     (let walk ((y x))
       (if (and (pair? y) (list? y) (not (memq (car y) '(quote quasiquote))))
           (begin
             (let ((b (body-of y)))
               (if b
                   (let find ((l b))
                     (cond ((null? l) 'no)
                           ((cert--call? (car l) 'qed) (return (cdr l)))
                           (#t (find (cdr l)))))))
             (for-each walk y))))
     '())))

;;; The file's own helpers that close a proof: a top-level (define (H ...) ...)
;;; whose body calls qed, directly or through another such helper.
(define *cert-qed-helpers* '())
(define (cert-qed-helpers forms)
  (let loop ((known '()))
    (let ((more (filter-map
                 (lambda (f)
                   (and (pair? f) (eq? (car f) 'define) (pair? (cdr f)) (pair? (cadr f))
                        (symbol? (car (cadr f)))
                        (not (memq (car (cadr f)) known))
                        (or (cert--contains-call? (cddr f) 'qed)
                            (any (lambda (h) (cert--contains-call? (cddr f) h)) known))
                        (car (cadr f))))
                 forms)))
      (if (null? more) known (loop (append more known))))))

;;; The file's own helpers that OPEN a proof (a define whose body calls sp or
;;; another opener, and never qed: a helper that both opens and closes is a
;;; self-contained proof and is neither).
(define *cert-sp-helpers* '())
(define (cert-sp-helpers forms)
  (let ((closers (cert-qed-helpers forms)))
    (let loop ((known '()))
      (let ((more (filter-map
                   (lambda (f)
                     (and (pair? f) (eq? (car f) 'define) (pair? (cdr f)) (pair? (cadr f))
                          (symbol? (car (cadr f)))
                          (not (memq (car (cadr f)) known))
                          (not (memq (car (cadr f)) closers))
                          (not (cert--contains-call? (cddr f) 'qed))
                          (or (cert--contains-call? (cddr f) 'sp)
                              (any (lambda (h) (cert--contains-call? (cddr f) h)) known))
                          (car (cadr f))))
                   forms)))
        (if (null? more) known (loop (append more known)))))))

(define (cert--opener? x)
  (and (pair? x) (list? x)
       (or (and (eq? (car x) 'sp) (= (length x) 2))
           (memq (car x) *cert-sp-helpers*))))

(define (cert--contains-opener? x)
  (or (cert--contains-call? x 'sp)
      (any (lambda (h) (cert--contains-call? x h)) *cert-sp-helpers*)))

(define (cert--qed-helper-call? x)
  (and (pair? x) (memq (car x) *cert-qed-helpers*) #t))

;;; the opener as it runs in a rewritten body: its sp does not escape
(define (cert--opener-form x)
  (if (eq? (car x) 'sp)
      `(cert-sp/body ,(cadr x))
      `(cert-no-escape (lambda () ,x))))

(define (cert-no-escape thunk)
  (fluid-let ((*cert-no-escape* #t)) (thunk)))

;;; A BODY: find each OPENER -- (sp X), or a call of an opening helper -- and
;;; the proof steps after it up to its CLOSER: (qed E); an element containing
;;; the qed (kept when the proof runs, replaced by (begin (qed E) <what follows
;;; the qed in its body>) when it was skipped); or a call of a closing helper
;;; (kept: with the finished placeholder in *ps* it reaches its qed and its
;;; metadata).  Without a closer the steps run up to the next opener or the end
;;; of the body (an `open!' helper).  The steps become
;;; (if (cert-proof-running?) (begin ...)); the opener does not escape.  A body
;;; whose steps hold an internal define is left alone (the sp then escapes the
;;; top-level form, and the end-of-file check decides).
(define (cert--rewrite-seq xs)
  (let ((xs (map cert-rewrite xs)))
    (define (steps mid) (if (null? mid) '() (list `(if (cert-proof-running?) (begin ,@(reverse mid))))))
    (let loop ((xs xs) (acc '()))
      (cond ((null? xs) (reverse acc))
            ((cert--opener? (car xs))
             (let ((op (car xs)))
               (let scan ((ys (cdr xs)) (mid '()))
                 (cond ((any cert--define-form? mid) (loop (cdr xs) (cons op acc)))
                       ((or (null? ys) (cert--opener? (car ys)))
                        (loop ys (append (steps mid) (list (cert--opener-form op)) acc)))
                       ((cert--call? (car ys) 'qed)
                        (loop ys (append (steps mid) (list (cert--opener-form op)) acc)))
                       ((cert--qed-helper-call? (car ys))
                        (loop ys (append (steps mid) (list (cert--opener-form op)) acc)))
                       ((and (not (cert--contains-opener? (car ys)))
                             (cert--qed-arg-in (car ys)))
                        => (lambda (e)
                             (loop (cdr ys)
                                   (append (list `(if (cert-proof-running?) ,(car ys)
                                                      (begin (qed ,e) ,@(cert--qed-tail (car ys)))))
                                           (steps mid) (list (cert--opener-form op)) acc))))
                       ((cert--contains-opener? (car ys)) (loop (cdr xs) (cons op acc)))
                       (#t (scan (cdr ys) (cons (car ys) mid)))))))
            (#t (loop (cdr xs) (cons (car xs) acc)))))))

(define (cert-rewrite x)
  (cond ((not (pair? x)) x)
        ((not (list? x)) x)
        ((memq (car x) '(quote quasiquote define-syntax let-syntax letrec-syntax
                                syntax-rules er-macro-transformer rsc-macro-transformer
                                sc-macro-transformer))
         x)
        ((and (memq (car x) '(lambda named-lambda)) (>= (length x) 2))
         (cons* (car x) (cadr x) (cert--rewrite-seq (cddr x))))
        ((and (eq? (car x) 'define) (>= (length x) 2) (pair? (cadr x)))
         (cons* 'define (cadr x) (cert--rewrite-seq (cddr x))))
        ((and (eq? (car x) 'let) (>= (length x) 3) (symbol? (cadr x)))
         (cons* 'let (cadr x) (cert--map-bindings (caddr x)) (cert--rewrite-seq (cdddr x))))
        ((and (memq (car x) '(let let* letrec letrec* fluid-let parameterize let-values let*-values))
              (>= (length x) 2))
         (cons* (car x) (cert--map-bindings (cadr x)) (cert--rewrite-seq (cddr x))))
        ((eq? (car x) 'begin) (cons 'begin (cert--rewrite-seq (cdr x))))
        ((and (memq (car x) '(when unless)) (>= (length x) 2))
         (cons* (car x) (cert-rewrite (cadr x)) (cert--rewrite-seq (cddr x))))
        (#t (map cert-rewrite x))))

(define (cert--map-bindings bs)
  (if (list? bs)
      (map (lambda (b) (if (and (pair? b) (list? b)) (cons (car b) (map cert-rewrite (cdr b))) b)) bs)
      bs))

(define (cert-sp/body w)
  (fluid-let ((*cert-no-escape* #t))
    (sp w)))

;;; ---------------------------------------------------------------- the loader
;;; F is the load-list key, PATH what prover-load--do chose (.com or .scm),
;;; MAKE-ENV builds a fresh file environment.
(define (cert-load-proof-file! f path make-env)
  (let ((mode (if *cert-in-load-list* (cert-mode) 'off))
        (store (and *cert-in-load-list* (cert-read-file f))))
    (cond ((eq? mode 'off) (cert--load-off! f path make-env))
          ((and (eq? mode 'on)
                (or (not store)
                    (not (equal? (let ((k (assq 'kernel (cddr (car store))))) (and k (cadr k)))
                                 (cert-kernel-hash)))))
           ;; nothing in the store can be used: prove the file the fast way
           (cert--load-off! f path make-env))
          (#t (cert--load-certified! f path make-env mode (if store (cdr store) '()))))))

(define (cert--load-off! f path make-env)
  (fluid-let ((*cert-file* (and *cert-in-load-list* f))
              (*cert-file-mode* 'off)
              (*cert-new-records* '())
              (*cert-installed* '())
              (*cert-skip* #f))
    (load path (make-env))
    (if (and *cert-file* *vnb-write-certs*)
        (if (pair? *cert-new-records*)
            (begin (cert-write-file! f (reverse *cert-new-records*))
                   (set! *cert-files-written* (+ *cert-files-written* 1)))
            (if (file-exists? (cert-path f)) (delete-file (cert-path f)))))))

;;; The global lists a failed certified pass must give back.
(define (cert--snapshot)
  (list *vnb-qed-failures* *vnb-qed-holes* *install-duplicates*
        *install-validation-failures* *inert-macetes* *proven-theorem-names*
        *support-theorem-names* (library-axioms *library*)
        *cert-session-proven* *cert-session-certified* *session-log*))

(define (cert--restore! s)
  (set! *vnb-qed-failures* (list-ref s 0))
  (set! *vnb-qed-holes* (list-ref s 1))
  (set! *install-duplicates* (list-ref s 2))
  (set! *install-validation-failures* (list-ref s 3))
  (set! *inert-macetes* (list-ref s 4))
  (set! *proven-theorem-names* (list-ref s 5))
  (set! *support-theorem-names* (list-ref s 6))
  (set-library-axioms! *library* (list-ref s 7))
  (set! *cert-session-proven* (list-ref s 8))
  (set! *cert-session-certified* (list-ref s 9))
  (set! *session-log* (list-ref s 10)))

(define (cert--msg e)
  (if (condition? e) (condition/report-string e)
      (call-with-output-string (lambda (p) (write e p)))))

(define (cert--load-certified! f path make-env mode records)
  (let* ((scm (cert-source-path f))
         (before (hash-table-copy *theorem-table*))
         (snap (cert--snapshot))
         (env (make-env))
         (console (current-output-port))
         (result
          (fluid-let ((*cert-file* f)
                      (*cert-file-mode* mode)
                      (*cert-records* (map (lambda (r) (cons r #f)) records))
                      (*cert-new-records* '())
                      (*cert-changed?* #f)
                      (*cert-installed* '())
                      (*cert-skip* #f)
                      (*cert-loader-error* #f)
                      (*cert-console* console))
            (let ((nfail (length *vnb-qed-failures*)))
              (let ((forms (call-with-input-file scm
                             (lambda (port)
                               (let rd ((acc '()))
                                 (let ((x (read port)))
                                   (if (eof-object? x) (reverse acc) (rd (cons x acc)))))))))
                (fluid-let ((*cert-qed-helpers* (cert-qed-helpers forms))
                            (*cert-sp-helpers* (cert-sp-helpers forms)))
                  ;; the pathname `load' would report for PATH (the .com's base
                  ;; name when it is fresh): *theorem-source*, the functoid,
                  ;; operator and structure registries record it
                  (parameterize ((current-load-pathname (merge-pathnames (->pathname path))))
                    (let loop ((k 1) (forms forms))
                      (let ((form (if (pair? forms) (car forms) (eof-object))))
                        (if (and (not (eof-object? form)) (not *cert-loader-error*))
                            (let* ((skipping *cert-skip*)
                                   (run (lambda ()
                                          (call-with-current-continuation
                                           (lambda (esc)
                                             (fluid-let ((*cert-escape* esc))
                                               (with-exception-handler
                                                (lambda (e) (esc (cons 'cert-error e)))
                                                (lambda () (eval (cert-rewrite form) env) 'ok)))))))
                                   (r (if skipping
                                          (let ((cell #f))
                                            (with-output-to-string (lambda () (set! cell (run))))
                                            cell)
                                          (run))))
                              (if (and (pair? r) (eq? (car r) 'cert-error) (not skipping))
                                  (set! *cert-loader-error*
                                        (string-append "form " (number->string k) " failed: "
                                                       (cert--msg (cdr r)))))
                              (loop (+ k 1) (cdr forms)))))))))
              (cert--close-skip!)
              (if (and (not *cert-loader-error*) (> (length *vnb-qed-failures*) nfail))
                  (set! *cert-loader-error* "a qed failed"))
              (if (not *cert-loader-error*)
                  (let ((missing (filter (lambda (c) (not (memq (cert-rec-name (car c)) *cert-installed*)))
                                         *cert-records*)))
                    (if (pair? missing)
                        (set! *cert-loader-error*
                              (string-append (number->string (length missing))
                                             " certified theorem(s) never reached, first "
                                             (symbol->string (cert-rec-name (car (car missing)))))))))
              (list *cert-loader-error* (reverse *cert-new-records*) *cert-changed?*
                    (map car (filter (lambda (c) (not (memq (cert-rec-name (car c)) *cert-installed*)))
                                     *cert-records*)))))))
    (let ((err (car result)) (recs (cadr result)) (changed? (caddr result)))
      (cond ((not err)
             (if (and *vnb-write-certs* changed?)
                 (begin (cert-write-file! f recs)
                        (set! *cert-files-written* (+ *cert-files-written* 1)))))
            ((eq? mode 'strict)
             (set! *cert-fallbacks* (cons (cons f err) *cert-fallbacks*))
             (cert--say ";VNB certificates: " f " is NOT covered in strict mode -- " err)
             (for-each (lambda (r)
                         (if (not (assq (cert-rec-name r) *cert-uncovered*))
                             (set! *cert-uncovered*
                                   (cons (cons (cert-rec-name r) (string-append f ": " err))
                                         *cert-uncovered*))))
                       (cadddr result)))
            (#t
             (set! *cert-fallbacks* (cons (cons f err) *cert-fallbacks*))
             (cert--say ";VNB certificates: FALLBACK " f " -- " err
                        " -- retracting its theorems and reloading it in off mode")
             (cert--retract-new! before)
             (cert--restore! snap)
             (cert--load-off! f path make-env))))))

;;; Retract every name the failed pass added to the theorem table.
(define (cert--retract-new! before)
  (let ((new '()))
    (hash-table-walk *theorem-table*
      (lambda (n v) (if (not (hash-table-ref/default before n #f)) (set! new (cons n new)))))
    (for-each (lambda (n) (hash-table-delete! *certified-theorems* n)) new)
    (if (pair? new) (xb-retract-names! new 'reload))
    (set! *xb-alias-snapshot* '())
    new))

;;; ---------------------------------------------------------------- reports
;;; "2026-09-24 on worker-02" -- the exams the certified theorems come from.
(define (cert-exam-summary)
  (let ((tally '()))
    (hash-table-walk *certified-theorems*
      (lambda (n dh)
        (let* ((key (string-append (car dh) " on " (cadr dh)))
               (e (assoc key tally)))
          (if e (set-cdr! e (+ (cdr e) 1)) (set! tally (cons (cons key 1) tally))))))
    (let ((srt (sort tally (lambda (a b) (> (cdr a) (cdr b))))))
      (cond ((null? srt) "none")
            ((null? (cdr srt)) (car (car srt)))
            (#t (apply string-append
                       (car (car srt))
                       (map (lambda (e) (string-append "; " (number->string (cdr e)) " of "
                                                       (car e)))
                            (cdr srt))))))))

;;; The load-summary line: the two counts, apart.
(define (report-proof-counts)
  (display ";; proofs: ") (display *cert-session-proven*)
  (display " proven in this session, ") (display *cert-session-certified*)
  (display " certified")
  (if (> *cert-session-certified* 0)
      (begin (display " (exam of ") (display (cert-exam-summary)) (display ")")))
  (display " [VNB_CERTIFIED=") (display (cert-mode)) (display "]")
  (newline)
  (if (> *cert-files-written* 0)
      (begin (display ";; certificates: ") (display *cert-files-written*)
             (display " file(s) written to ") (display (cert-dir)) (newline)))
  (if (pair? *cert-fallbacks*)
      (begin
        (display ";; certificates: ") (display (length *cert-fallbacks*))
        (display " file(s) could not be loaded from their certificates:\n")
        (for-each (lambda (e) (display ";;   ") (display (car e)) (display " -- ")
                          (display (cdr e)) (newline))
                  (reverse *cert-fallbacks*))))
  (let ((bad (cert-kernel-files-audit)))
    (if (pair? bad)
        (begin (display ";; certificates: *kernel-caller-files* names files outside the kernel hash: ")
               (write bad) (newline)
               (error "certificates: the kernel hash does not cover every kernel caller" bad)))))

;;; strict: list the uncovered theorems and exit non-zero.
(define (cert-strict-gate!)
  (if (eq? (cert-mode) 'strict)
      (if (null? *cert-uncovered*)
          (begin (display ";; certificates (strict): ok -- every theorem of the tree installed from its certificate, none proved\n"))
          (begin
            (display ";; certificates (strict): ") (display (length *cert-uncovered*))
            (display " theorem(s) WITHOUT a valid certificate:\n")
            (for-each (lambda (e) (display ";;   ") (display (car e)) (display " -- ")
                              (display (cdr e)) (newline))
                      (reverse *cert-uncovered*))
            (exit 4)))))
