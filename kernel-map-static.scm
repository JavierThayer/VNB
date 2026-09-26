;;; kernel-map-static.scm -- INSTRUMENT, not library; not in load.scm.
;;; Run:  ./prover -b kernel-map-static.scm   (writes reference/kernel-map-static.sexp)
;;; Then: ./prover -b kernel-map-trace.scm    (writes reference/kernel-map-dynamic.sexp)
;;; Built 2026-09-12 to answer: which procedures are the kernel, and which kernel
;;; procedures does each tactic reach.  Report: reference/KERNEL-MAP.md
;;;
;;; 2026-09-20: the results are now KEPT IN THE TREE (reference/*.sexp), the
;;; inference CHECKERS are modelled (rule-checkers-*.scm: the closures
;;; `register-rule-checker!' puts in the checker table are reachable only from
;;; `dg-check-inference!', which dg-apply-rule! runs before it writes anything),
;;; and a computed rule tag spelled `(list 'ineq cert)' is read as the tag
;;; `ineq' -- it used to be recorded as an opaque `computed' tag.
;;;
;;; km-static2.scm -- STATIC half of the kernel map, second version.
;;;
;;; What changed from km-static.scm, and why:
;;;  1. LOAD-TIME vs RUN-TIME.  `(define *current-theory* (make-vnb-base-theory))'
;;;     runs its initializer ONCE, at load.  Referencing the variable later does
;;;     not run it again, so calls inside a data initializer are not edges.
;;;     Procedures passed or stored as VALUES there still are, and anything
;;;     inside a lambda is run-time code.  (The first version had `sp' reaching
;;;     the macete builder through exactly this leak.)
;;;  2. THE MACETE TABLE is the kernel's one indirect door.  Graph writes happen
;;;     inside closures that were put in the table earlier and are fetched and
;;;     called later: the closure `make-elementary-macete' RETURNS, and two
;;;     anonymous `(install-macete! 'NAME (lambda ...))' forms in theory.scm.
;;;     Each becomes a node; the constructor itself is NOT a kernel entry --
;;;     building a closure writes nothing.  Whatever fetches from the table can
;;;     reach them all (conservative; the dynamic run shows which fire).
;;;  3. Every dg-apply-rule! CALL SITE is labelled -- named define or top-level
;;;     form -- so the entry list is exact by construction, not by heuristic.

(define km-out-dir (string-append *prover-dir* "reference/"))

(define (km-forms-of f)
  (call-with-input-file (string-append *prover-dir* f ".scm")
    (lambda (p)
      (let loop ((acc '()))
        (let ((x (read p)))
          (if (eof-object? x) (reverse acc) (loop (cons x acc))))))))

(define km-engine-files (filter (lambda (f) (not (proof-file? f))) *vnb-files*))
(define km-proof-files  (filter proof-file? *vnb-files*))

;;; ---------------------------------------------------------------- walker
;;; MODE is 'run (every free reference counts) or 'load (a load-time
;;; expression: a symbol in OPERATOR position is a call made now, once, and is
;;; not an edge; symbols in argument position may be procedures stored for
;;; later, and are).  Entering a lambda switches to 'run.
(define *km-tags* '())

(define (km-params p)
  (cond ((symbol? p) (list p))
        ((pair? p) (append (km-params (car p)) (km-params (cdr p))))
        (else '())))
(define (km-bname b) (if (pair? b) (car b) b))
(define (km-binit b) (and (pair? b) (pair? (cdr b)) (cadr b)))

(define (km-add! out s) (hash-table-set! out s #t))

(define (km-body body bound0 out mode)
  (let* ((forms (if (list? body) body '()))
         (inner (append-map (lambda (f)
                              (if (and (pair? f) (eq? (car f) 'define))
                                  (let ((t (cadr f))) (list (if (pair? t) (car t) t)))
                                  '()))
                            forms))
         (bound (append inner bound0)))
    (for-each (lambda (f)
                (if (and (pair? f) (eq? (car f) 'define))
                    (let ((t (cadr f)))
                      (if (pair? t)
                          (km-body (cddr f) (append (km-params (cdr t)) bound) out 'run)
                          (if (pair? (cddr f)) (km-walk (caddr f) bound out mode))))
                    (km-walk f bound out mode)))
              forms)))

(define (km-list x bound out mode)
  (let loop ((y x))
    (cond ((pair? y) (km-walk (car y) bound out mode) (loop (cdr y)))
          ((symbol? y) (km-walk y bound out mode)))))

(define (km-qq x bound out mode depth)
  (cond ((not (pair? x)) 'datum)
        ((and (memq (car x) '(unquote unquote-splicing)) (pair? (cdr x)))
         (if (= depth 1) (km-walk (cadr x) bound out mode)
             (km-qq (cadr x) bound out mode (- depth 1))))
        ((and (eq? (car x) 'quasiquote) (pair? (cdr x)))
         (km-qq (cadr x) bound out mode (+ depth 1)))
        (else (let loop ((y x))
                (if (pair? y) (begin (km-qq (car y) bound out mode depth) (loop (cdr y))))))))

;;; The RULE argument of a dg-apply-rule! call site, reduced to its tag HEAD --
;;; the name that appears in the inference node.  Four shapes occur:
;;;   'forall-elim                       a quoted symbol
;;;   `(macete ,name ,source ,repl)      a quasiquoted list (macetes.scm)
;;;   (list 'ineq cert)                  a built list (ineq-oracle, sos-oracle)
;;;   anything else                      recorded as computed, and reported
(define (km-tag-of t)
  (cond ((and (pair? t) (eq? (car t) 'quote)) (cadr t))
        ((and (pair? t) (eq? (car t) 'quasiquote) (pair? (cadr t))) (car (cadr t)))
        ((and (pair? t) (eq? (car t) 'list) (pair? (cdr t))
              (pair? (cadr t)) (eq? (car (cadr t)) 'quote))
         (cadr (cadr t)))
        (else (list 'computed t))))

(define (km-binds! bs bound out mode)
  (for-each (lambda (b) (let ((i (km-binit b))) (if i (km-walk i bound out mode)))) bs))

(define (km-walk x bound out mode)
  (cond
    ((symbol? x) (if (not (memq x bound)) (km-add! out x)))
    ((not (pair? x)) 'datum)
    (else
     (let ((h (car x)))
       (if (and (eq? h 'dg-apply-rule!) (pair? (cdr x)) (pair? (cddr x)))
           (set! *km-tags* (cons (km-tag-of (caddr x)) *km-tags*)))
       (cond
         ((not (symbol? h)) (km-list x bound out mode))
         ((memq h bound) (km-list x bound out mode))
         ((eq? h 'quote) 'datum)
         ((eq? h 'quasiquote) (km-qq (cadr x) bound out mode 1))
         ((memq h '(lambda named-lambda))
          (km-body (cddr x) (append (km-params (cadr x)) bound) out 'run))
         ((eq? h 'let)
          (if (symbol? (cadr x))
              (let ((bs (caddr x)))
                (km-binds! bs bound out mode)
                (km-body (cdddr x) (append (map km-bname bs) (list (cadr x)) bound) out mode))
              (let ((bs (cadr x)))
                (km-binds! bs bound out mode)
                (km-body (cddr x) (append (map km-bname bs) bound) out mode))))
         ((eq? h 'let*)
          (let loop ((bs (cadr x)) (bd bound))
            (if (null? bs)
                (km-body (cddr x) bd out mode)
                (begin (let ((i (km-binit (car bs)))) (if i (km-walk i bd out mode)))
                       (loop (cdr bs) (cons (km-bname (car bs)) bd))))))
         ((memq h '(letrec letrec*))
          (let ((bd (append (map km-bname (cadr x)) bound)))
            (km-binds! (cadr x) bd out mode)
            (km-body (cddr x) bd out mode)))
         ((memq h '(let-values let*-values))
          (let ((names (append-map (lambda (b) (km-params (car b))) (cadr x))))
            (for-each (lambda (b) (km-walk (cadr b) bound out mode)) (cadr x))
            (km-body (cddr x) (append names bound) out mode)))
         ((eq? h 'do)
          (let* ((specs (cadr x)) (bd (append (map car specs) bound)))
            (for-each (lambda (s) (km-walk (cadr s) bound out mode)
                        (if (pair? (cddr s)) (km-walk (caddr s) bd out mode)))
                      specs)
            (km-list (caddr x) bd out mode)
            (km-body (cdddr x) bd out mode)))
         ((eq? h 'guard)
          (let ((var (car (cadr x))))
            (for-each (lambda (c) (km-list c (cons var bound) out mode)) (cdr (cadr x)))
            (km-body (cddr x) bound out mode)))
         ((eq? h 'case)
          (km-walk (cadr x) bound out mode)
          (for-each (lambda (cl) (if (pair? cl) (km-list (cdr cl) bound out mode))) (cddr x)))
         ((eq? h 'fluid-let)
          (km-binds! (cadr x) bound out mode)
          (km-body (cddr x) bound out mode))
         ((eq? h 'define)
          (let ((t (cadr x)))
            (if (pair? t)
                (km-body (cddr x) (append (km-params (cdr t)) bound) out 'run)
                (if (pair? (cddr x)) (km-walk (caddr x) bound out mode)))))
         ((eq? h 'bc*)
          (if (eq? mode 'run)
              (begin (km-add! out 'bc*-apply) (km-add! out 'bc*-dispatch)))
          (if (pair? (cdr x)) (km-walk (cadr x) bound out mode))
          (if (and (pair? (cdr x)) (pair? (cddr x)))
              (begin
                (for-each (lambda (b) (if (and (pair? b) (pair? (cdr b))) (km-walk (cadr b) bound out mode)))
                          (caddr x))
                (km-list (cdddr x) bound out mode))))
         ((eq? h 'vlet)
          (if (eq? mode 'run)
              (begin (km-add! out 'vlet--match) (km-add! out 'vlet--choice!))))
         ((memq h '(declare-structure define-record-type declare define-syntax
                    let-syntax letrec-syntax syntax-rules the-environment))
          'opaque)
         ;; a generic application
         ((eq? mode 'load)
          (let loop ((y (cdr x)))              ; operator skipped: a call made at load
            (cond ((pair? y) (km-walk (car y) bound out mode) (loop (cdr y)))
                  ((symbol? y) (km-walk y bound out mode)))))
         (else (km-list x bound out mode)))))))

;;; ---------------------------------------------------------------- nodes
;;; node -> list of (origin refs tags)
(define *km-defs* (make-strong-eqv-hash-table))
(define (km-add-def! name origin refs tags)
  (hash-table-update!/default *km-defs* name (lambda (l) (cons (list origin refs tags) l)) '()))

(define (km-scan! form bound mode)          ; -> (refs . tags)
  (let ((out (make-strong-eqv-hash-table)))
    (set! *km-tags* '())
    (km-walk form bound out mode)
    (cons (hash-table-keys out) *km-tags*)))

(define (km-define! form file)
  (let* ((t (cadr form))
         (name (if (pair? t) (car t) t))
         (out (make-strong-eqv-hash-table)))
    (set! *km-tags* '())
    (if (pair? t)
        (km-body (cddr form) (append (km-params (cdr t)) (list name)) out 'run)
        (if (pair? (cddr form)) (km-walk (caddr form) '() out 'load)))
    (km-add-def! name file (hash-table-keys out) *km-tags*)))

(define (km-record-type! form file)
  (let ((ctor (caddr form)) (pred (cadddr form)) (fields (cddddr form)))
    (if (pair? ctor) (km-add-def! (car ctor) file '() '()))
    (if (symbol? pred) (km-add-def! pred file '() '()))
    (for-each (lambda (fs) (if (pair? fs)
                               (for-each (lambda (n) (if (symbol? n) (km-add-def! n file '() '())))
                                         (cdr fs))))
              fields)))

(define *km-macete-nodes* '())            ; the closures the macete table can hand out
(define *km-checker-nodes* '())           ; the closures the CHECKER table can hand out
(define *km-toplevel-stampers* '())       ; any other top-level form that writes the graph

(define (km-top! form file i)
  (cond
    ((not (pair? form)) 'skip)
    ((memq (car form) '(define define-integrable)) (km-define! form file))
    ((eq? (car form) 'define-record-type) (km-record-type! form file))
    ((eq? (car form) 'begin)
     (for-each (lambda (f) (km-top! f file i)) (cdr form)))
    ((and (eq? (car form) 'set!) (symbol? (cadr form)) (pair? (cddr form)))
     (let ((r (km-scan! (caddr form) '() 'load)))
       (km-add-def! (cadr form) (string-append file " [set!]") (car r) (cdr r))))
    ;; (install-macete! 'NAME PROC) -- a closure put in the macete table at load
    ((and (eq? (car form) 'install-macete!) (pair? (cdr form)) (pair? (cddr form)))
     (let* ((nm (let ((q (cadr form))) (if (and (pair? q) (eq? (car q) 'quote)) (cadr q) q)))
            (node (string->symbol (string-append "<macete:" (write-to-string nm) ">")))
            (r (km-scan! (caddr form) '() 'load)))
       (km-add-def! node (string-append file " [install-macete!]") (car r) (cdr r))
       (set! *km-macete-nodes* (cons node *km-macete-nodes*))))
    ;; (register-rule-checker! 'NAME PROC) -- a closure put in the CHECKER table
    ;; at load.  PROC is scanned in `run' mode: it is a value stored for later,
    ;; so the head of `(chk-if-rule #t)' is an edge, not a call made now.
    ((and (eq? (car form) 'register-rule-checker!) (pair? (cdr form)) (pair? (cddr form)))
     (let* ((nm (let ((q (cadr form))) (if (and (pair? q) (eq? (car q) 'quote)) (cadr q) q)))
            (node (string->symbol (string-append "<checker:" (write-to-string nm) ">")))
            (r (km-scan! (caddr form) '() 'run)))
       (km-add-def! node (string-append file " [register-rule-checker!]") (car r) (cdr r))
       (set! *km-checker-nodes* (cons node *km-checker-nodes*))))
    (else
     ;; any other top-level form: only interesting if it writes the graph
     (let ((r (km-scan! form '() 'load)))
       (if (pair? (cdr r))
           (let ((node (string->symbol (string-append "<toplevel:" file ":" (number->string i) ">"))))
             (km-add-def! node file (car r) (cdr r))
             (set! *km-toplevel-stampers* (cons node *km-toplevel-stampers*))))))))

(for-each (lambda (f)
            (let loop ((fs (km-forms-of f)) (i 0))
              (if (pair? fs) (begin (km-top! (car fs) f i) (loop (cdr fs) (+ i 1))))))
          km-engine-files)

;;; THE ELEMENTARY MACETE CLOSURE.  make-elementary-macete's graph write sits
;;; inside the lambda it returns; model that lambda as its own node.
(let ((d (hash-table-ref *km-defs* 'make-elementary-macete (lambda () '()))))
  (km-add-def! '<elementary-macete> "macetes [closure returned by make-elementary-macete]"
               (append-map cadr d) (append-map caddr d))
  (set! *km-macete-nodes* (cons '<elementary-macete> *km-macete-nodes*)))

(define (km-def? s) (hash-table-contains? *km-defs* s))
(define km-def-names (hash-table-keys *km-defs*))

;;; edges
(define *km-edges* (make-strong-eqv-hash-table))
(for-each
 (lambda (n)
   (let ((acc (make-strong-eqv-hash-table)))
     (for-each (lambda (d) (for-each (lambda (r) (if (km-def? r) (hash-table-set! acc r #t))) (cadr d)))
               (hash-table-ref *km-defs* n (lambda () '())))
     ;; THE MACETE TABLE'S ONE DOOR.  The only code that fetches a closure out
     ;; of the table AND CALLS IT is lookup-macete, reached via apply-macete!.
     ;; Every other reference to *macete-table* inserts (install-macete!),
     ;; deletes (structures.scm) or tests for existence (resolve-macete-name,
     ;; vnb--hyp-unfold-name) -- audited 2026-09-12.  Inserting a closure runs
     ;; nothing, so only lookup-macete reaches the closures.
     (if (eq? n 'lookup-macete)
         (for-each (lambda (m) (hash-table-set! acc m #t)) *km-macete-nodes*))
     (hash-table-set! *km-edges* n (hash-table-keys acc))))
 km-def-names)

;;; THE CHECKER TABLE'S ONE DOOR, kept OUT of the edge table above.
;;; `dg-check-inference!' is the only code that fetches a checker out of
;;; `*rule-checkers*' and calls it; every other reference registers one
;;; (register-rule-checker!) or reads the key list (rule-checker-for,
;;; registered-rule-checkers).  It is a separate relation because a check is
;;; not a step: it runs before anything is written, and its verdict either
;;; lets the write happen or stops it.  Following it from a proof command
;;; would say that every command reaches every entry point, since every entry
;;; point calls dg-apply-rule! and dg-apply-rule! checks -- true of the CODE
;;; and useless as a bound on what a command can record.  So the command table
;;; walks the edges alone, and the TRUSTED BASE walks the edges plus this door.
(define (km-edges-of n) (hash-table-ref/default *km-edges* n '()))
(define (km-edges/checkers n)
  (if (eq? n 'dg-check-inference!)
      (append *km-checker-nodes* (km-edges-of n))
      (km-edges-of n)))

;;; THE POST-COMMAND HOOK, likewise a relation of its own.  `vnb--run!' runs
;;; `*owed-leaf-hook*' after any command that changed the proof, on the leaves
;;; that command left owed; driver-kit sets it to `dk-discharge-owed!', which
;;; closes each by citation.  So the hook's reach belongs to EVERY command, and
;;; charging it to each one separately would print the same twenty entry points
;;; against `ass' as against `minimize!' and hide what each command itself
;;; does.  The command table is therefore measured without it, and the hook's
;;; own reach is reported once, as its own row.
(define km-post-command-hooks '(*owed-leaf-hook*))
(define (km-edges/no-hook n)
  (if (memq n km-post-command-hooks) '() (km-edges-of n)))

;;; ---------------------------------------------------------------- (a)
(define (km-writes-graph? n)
  (any (lambda (d) (memq 'dg-apply-rule! (cadr d))) (hash-table-ref *km-defs* n (lambda () '()))))

(define (km-sym<? a b) (string<? (symbol->string a) (symbol->string b)))

(define km-kernel
  (sort (filter (lambda (n) (and (not (memq n '(dg-apply-rule! make-elementary-macete)))
                                 (km-writes-graph? n)))
                km-def-names)
        km-sym<?))

(define (km-tags-of k)
  (delete-duplicates (append-map caddr (hash-table-ref *km-defs* k (lambda () '()))) equal?))
(define (km-origin-of n) (car (car (hash-table-ref *km-defs* n (lambda () '(("?")))))))

(define (km-reach* starts edges-of)
  (let ((seen (make-strong-eqv-hash-table)))
    (let loop ((todo starts))
      (if (pair? todo)
          (let ((n (car todo)))
            (if (hash-table-contains? seen n)
                (loop (cdr todo))
                (begin (hash-table-set! seen n #t)
                       (loop (append (edges-of n) (cdr todo))))))))
    (hash-table-keys seen)))

(define (km-reach starts) (km-reach* starts km-edges-of))

;;; THE TRUSTED CODE BASE.  What is reachable from the entry points, TOGETHER
;;; WITH what `dg-apply-rule!' itself now runs: since 2026-09-20 it verifies
;;; every inference before writing it, so the checker closures and everything
;;; they call decide whether an inference is accepted and belong in the count.
(define km-tcb (km-reach* (cons 'dg-apply-rule! km-kernel) km-edges/checkers))

;;; What a CHECKER can reach that is itself an entry point.  A checker runs
;;; inside the write point, so anything of this kind is worth naming: the
;;; expected answer is the rewriting closures, which the rewrite checker
;;; consults to find out what a macete name denotes.
(define km-checker-entry-reach
  (sort (filter (lambda (n) (memq n km-kernel))
                (km-reach* *km-checker-nodes* km-edges/checkers))
        km-sym<?))

(define (km-tcb-by-file)
  (let ((tbl (make-equal-hash-table)))
    (for-each (lambda (n)
                (let* ((o (km-origin-of n))
                       (f (let ((i (string-search-forward " [" o 0)))
                            (if i (substring o 0 i) o))))
                  (hash-table-update!/default tbl f (lambda (k) (+ k 1)) 0)))
              km-tcb)
    (sort (hash-table->alist tbl) (lambda (a b) (> (cdr a) (cdr b))))))

;;; ---------------------------------------------------------------- (b)
(define km-registry-tactics
  (delete-duplicates
   (append (append-map (lambda (g) (map car (cdr g))) *tactic-help*)
           (map car *tactic-kind*)
           '(prop contra push-not-h in-rr ass-all slot slot-h use-em
             obtain-at use-at eps-part choose choose-pos))
   eq?))

(define km-surface-commands
  (filter (lambda (n)
            (and (not (memq n '(vnb--run! record-cmd! replay--surface! apply-recorded-cmd!)))
                 (any (lambda (d) (or (memq 'vnb--run! (cadr d)) (memq 'record-cmd! (cadr d))))
                      (hash-table-ref *km-defs* n (lambda () '())))))
          km-def-names))

(define km-tactics
  (sort (delete-duplicates (append km-registry-tactics km-surface-commands) eq?) km-sym<?))

(define (km-starts t)
  (cond ((eq? t 'bc*) '(bc*-apply bc*-dispatch))
        ((eq? t 'vlet) '(vlet--match vlet--choice!))
        (else (list t))))

(define (km-tactic-kernel t)
  (sort (filter (lambda (n) (memq n km-kernel))
                (km-reach* (km-starts t) km-edges/no-hook))
        km-sym<?))

;;; The entry points each post-command hook reaches, and so the entry points
;;; every command reaches through it.
(define km-hook-reach
  (map (lambda (h)
         (list h
               (sort (filter (lambda (n) (memq n km-kernel))
                             (km-reach* (km-edges-of h) km-edges-of))
                     km-sym<?)))
       km-post-command-hooks))

;;; ---------------------------------------------------------------- proof files
(define km-proof-file-bypass
  (append-map
   (lambda (f)
     (let ((out (make-strong-eqv-hash-table)))
       (for-each (lambda (form) (set! *km-tags* '()) (km-walk form '() out 'run)) (km-forms-of f))
       (let ((hits (filter (lambda (s)
                             (let ((str (symbol->string s)))
                               (or (eq? s 'dg-apply-rule!)
                                   (and (string-prefix? "pi-" str) (string-suffix? "!" str) (km-def? s))
                                   (and (string-prefix? "cmd-" str) (km-def? s)))))
                           (hash-table-keys out))))
         (if (null? hits) '() (list (cons f hits))))))
   km-proof-files))

;;; ---------------------------------------------------------------- out
(define (km-save! name header datum)
  (call-with-output-file (string-append km-out-dir name)
    (lambda (p)
      (for-each (lambda (l) (display l p) (newline p)) header)
      (write datum p) (newline p))))

(km-save! "kernel-map-static.sexp"
  (list ";;; kernel-map-static.sexp -- the STATIC half of the kernel map: what the"
        ";;; source says about which procedures may record an inference, which"
        ";;; operations each may record, and what each proof command can reach."
        ";;; Read with the Scheme reader; these comment lines are skipped."
        ";;;"
        ";;; REGENERATE (on a worker, not on the primary):"
        ";;;     ./prover -b kernel-map-static.scm    < /dev/null   # this file"
        ";;;     ./prover -b kernel-map-trace.scm     < /dev/null   # the dynamic half"
        ";;; The second re-proves the whole library and takes about half an hour."
        ";;; reference/KERNEL-MAP.md is written from the two together.")
  (list (list 'kernel (map (lambda (k) (list k (km-origin-of k) (km-tags-of k))) km-kernel))
        (list 'tactics (map (lambda (t) (list t (km-tactic-kernel t))) km-tactics))
        (list 'registry-tactics km-registry-tactics)
        (list 'surface-commands km-surface-commands)
        (list 'tactic-kinds *tactic-kind*)
        (list 'macete-nodes *km-macete-nodes*)
        (list 'checker-nodes (sort *km-checker-nodes* km-sym<?))
        (list 'checker-entry-reach km-checker-entry-reach)
        (list 'post-command-hooks km-hook-reach)
        (list 'toplevel-stampers *km-toplevel-stampers*)
        (list 'tcb (map (lambda (n) (list n (km-origin-of n))) km-tcb))
        (list 'tcb-by-file (km-tcb-by-file))
        (list 'call-sites (kernel-callers-census))
        (list 'caller-files *kernel-caller-files*)
        (list 'counts (list (list 'definitions (length km-def-names))
                            (list 'loaded-files (length *vnb-files*))
                            (list 'engine-files (length km-engine-files))
                            (list 'proof-files (length km-proof-files))))
        (list 'proof-file-bypass km-proof-file-bypass)))

(display "\n=== kernel-map-static summary\n")
(display "definitions: ") (display (length km-def-names)) (newline)
(display "kernel entry points: ") (display (length km-kernel)) (newline)
(display "call sites: ")
(display (apply + (map cadr (kernel-callers-census))))
(display " in ") (display (length (kernel-callers-census))) (display " file(s)") (newline)
(display "checker closures modelled: ") (display (length *km-checker-nodes*)) (newline)
(display "macete-table closures modelled: ") (write *km-macete-nodes*) (newline)
(display "other top-level forms that write the graph: ") (write *km-toplevel-stampers*) (newline)
(display "TCB: ") (display (length km-tcb)) (newline)
(display "tactics: ") (display (length km-tactics)) (newline)
(display "proof files that bypass the tactics: ") (display (length km-proof-file-bypass)) (newline)
(display "TCB by file: ") (write (km-tcb-by-file)) (newline)
(display "entry points reachable from a CHECKER: ") (write km-checker-entry-reach) (newline)
(display "post-command hooks: ") (write km-hook-reach) (newline)
(let ((computed (filter (lambda (t) (and (pair? t) (eq? (car t) 'computed)))
                        (append-map km-tags-of km-kernel))))
  (display "tags the reader could not resolve: ")
  (if (null? computed) (display "none") (write computed))
  (newline))
(display "kernel entries by origin:\n")
(for-each (lambda (k) (display "  ") (display k) (display "   ") (display (km-origin-of k))
            (display "   ") (write (km-tags-of k)) (newline))
          km-kernel)
