;;; functoid-gate.scm -- the def-functoid DEFINITION LOG and the load-end gate on
;;; the functoid hypotheses H1-H4 and H6 (W2C, META item 2, 2026-11-10).
;;;
;;; Loaded right after structures.scm (load.scm, *vnb-files*), so the log is armed
;;; before any file defines a functoid; the gate runs in run-load-end! (so a cold
;;; load, a certified build and extend-band all run it).  It defines procedures, arms
;;; the log once, and touches no kernel table: the wrapped `def-functoid' calls the
;;; original unchanged.  Not a kernel-key file (certificates.scm, *cert-kernel-files*).
;;;
;;; The hypotheses are those of the hand-written functoid argument
;;; (meta-report, functoid-argument.tex, s. "The hypotheses the map needs").

;;; -----------------------------------------------------------------------
;;; THE DEF-FUNCTOID DEFINITION LOG -- what the load-end functoid-hypotheses gate
;;; (below) reads for H2 and H3.
;;;
;;; *functoid-registry* (structures.scm) keeps ONE entry per head and
;;; `def-functoid' overwrites it silently, so the final registry can say neither
;;; in which ORDER the heads were defined (H2: a body mentions only heads defined
;;; BEFORE its own) nor whether a head was defined TWICE (H3).  The log records
;;; each call as it happens.  It is armed once, right after structures.scm has
;;; loaded and before any file defines a functoid, by wrapping the global
;;; `def-functoid' (every caller, the generated ones of structures.scm included,
;;; reaches it through that binding); the wrapper computes its record, calls the
;;; original unchanged, and pushes the record only when the original returned.
;;; Nothing the original does is altered: the log is read by the gate only.
;;;
;;; A record (newest first in *functoid-def-log*) is a list
;;;   (SEQ NAME PVARS BODY PATH UNDEFINED REDEF OLD SNAPSHOT)
;;;   UNDEFINED  the symbols of BODY, parameters excepted, that were neither a
;;;              defined head (fg--defined-head-now?) nor a registered constant at the
;;;              moment of the call; the gate reports those that are either at the
;;;              end of the load (so an accessor, a structure predicate or a
;;;              def-constant introduced after F is caught, not only a definition);
;;;   REDEF      #f, `identical' (same parameters and body as the entry it
;;;              replaces: the extend-band reload of an unchanged form) or `changed';
;;;   OLD        the replaced registry entry, or #f;
;;;   SNAPSHOT   for a `changed' redefinition only: ((THEOREM . FORMULA) ...), every
;;;              installed theorem whose statement mentions NAME directly or through
;;;              the definitions in force at that moment; the gate reports each one
;;;              still installed with the SAME formula object at the end.
;;; The log is a fluid: the suite's controls bind it around a planted definition.
(define *functoid-def-log* '())
(define *functoid-def-seq* 0)
(define *functoid-def-log-armed?* #f)

(define (fg--symbols e)                  ; the distinct symbols of an expression
  (let ((acc '()))
    (let walk ((e e))
      (cond ((symbol? e) (if (not (memq e acc)) (set! acc (cons e acc))))
            ((pair? e) (walk (car e)) (walk (cdr e)))
            ((functoid? e)
             (for-each (lambda (b) (walk (car b)) (walk (cdr b))) (functoid-bindings e))
             (walk (functoid-body e)))
            (#t #f)))
    acc))

;;; A DEFINED HEAD, as certificates.scm reads one (cert--defined-head?), minus a
;;; theorem whose name merely coincides: a def-functoid, a library-definitions
;;; head, or a theorem NAMED like the head with provenance `definitional'.
(define (fg--defined-head-now? s)
  (and (symbol? s)
       (or (and (hash-table-ref/default *functoid-registry* s #f) #t)
           (and (assq s (library-definitions *library*)) #t)
           (and (hash-table-ref/default *theorem-table* s #f)
                (eq? (provenance-of s) 'definitional)))))

;;; The definition objects of a head now: a functoid's body, a library entry's
;;; axiom statements (installed statement preferred), a definitional theorem's
;;; statement.  Used for the redefinition snapshot only.
(define (fg--definitions-now s)
  (let ((reg (hash-table-ref/default *functoid-registry* s #f))
        (ld  (assq s (library-definitions *library*))))
    (append (if reg (list (cadr reg)) '())
            (if ld
                (map (lambda (ax)
                       (if (pair? ax)
                           (or (and (symbol? (car ax))
                                    (hash-table-ref/default *theorem-table* (car ax) #f))
                               (cdr ax))
                           ax))
                     (cdr ld))
                '())
            (if (and (not reg) (not ld)
                     (eq? (provenance-of s) 'definitional)
                     (hash-table-ref/default *theorem-table* s #f))
                (list (hash-table-ref/default *theorem-table* s #f))
                '()))))

;;; Does FORMULA mention NAME, directly or through the definitions in force?
;;; MEMO: head -> #t / #f / 'visiting (cycle-safe: a cycle answers #f on the
;;; back edge, which is what the other members' own walks then decide).
(define (fg--mentions-through? formula name memo)
  (let mentions ((f formula))
    (fg--any-symbol (lambda (s)
                  (or (eq? s name)
                      (and (fg--defined-head-now? s)
                           (let ((m (hash-table-ref/default memo s 'unknown)))
                             (cond ((eq? m 'unknown)
                                    (hash-table-set! memo s 'visiting)
                                    (let ((r (let loop ((ds (fg--definitions-now s)))
                                               (and (pair? ds)
                                                    (or (mentions (car ds)) (loop (cdr ds)))))))
                                      (hash-table-set! memo s r)
                                      r))
                                   ((eq? m 'visiting) #f)
                                   (#t m))))))
                (fg--symbols (if (wff? f) (wff-formula f) f)))))

(define (fg--any-symbol pred syms)
  (and (pair? syms) (or (pred (car syms)) (fg--any-symbol pred (cdr syms)))))

(define (fg--log-record name params body path)
  (let* ((pvars (if (pair? params) params (list params)))
         (old   (hash-table-ref/default *functoid-registry* name #f))
         (redef (and old (if (and (equal? (car old) pvars) (equal? (cadr old) body))
                             'identical
                             'changed)))
         (undef (filter (lambda (s) (and (not (memq s pvars)) (not (fg--defined-head-now? s))
                                         (not (constant-head? s))))
                        (fg--symbols body)))
         (snap  (if (eq? redef 'changed)
                    (let ((memo (make-strong-eqv-hash-table)) (acc '()))
                      (hash-table-walk *theorem-table*
                        (lambda (tn f)
                          (if (fg--mentions-through? f name memo)
                              (set! acc (cons (cons tn f) acc)))))
                      acc)
                    '())))
    (set! *functoid-def-seq* (+ *functoid-def-seq* 1))
    (list *functoid-def-seq* name pvars body path undef redef old snap)))

(define (functoid-def-log-arm!)
  (if (not *functoid-def-log-armed?*)
      (let ((orig def-functoid))
        (set! def-functoid
              (lambda (name params body)
                (let ((rec (and (symbol? name) (not (null? params))
                                (fg--log-record name params body (safe-load-pathname)))))
                  (let ((v (orig name params body)))
                    (if rec (set! *functoid-def-log* (cons rec *functoid-def-log*)))
                    v))))
        (set! *functoid-def-log-armed?* #t))))

;;; -----------------------------------------------------------------------
;;; THE FUNCTOID HYPOTHESES GATE -- H1-H4 and H6 of the
;;; functoid argument (meta-report, functoid-argument.tex, s. "The hypotheses the
;;; map needs").  The gate itself reports; FATAL in a strict load since 2026-11-19
;;; (FGATE: backlog zero) through functoid-hypotheses-enforce! below.
;;;
;;;   H1  the parameters of a def-functoid are distinct symbols;
;;;   H2  b_F mentions only heads defined before F (no recursion, direct or mutual);
;;;   H3  one registry entry per head in an image, and no theorem stated under an
;;;       earlier entry survives a redefinition;
;;;   H4  the free variables of b_F are among its parameters;
;;;   H6  no head is both a def-functoid and a library-definitions head.
;;;
;;; WHAT IS READ.  The final *functoid-registry* (one entry per head: params, body,
;;; source), the library-definitions alist, the theorem table, and the DEFINITION
;;; LOG above (*functoid-def-log*), which records every def-functoid call of
;;; the image in order.  H1 and H4 are checked on every registry entry and on every
;;; logged call (so an entry that was later overwritten is checked too); H6 on the
;;; registry.  H2 has three parts: direct recursion (F among the symbols of b_F) and
;;; mutual recursion (F on a cycle of the graph "head -> the defined heads its
;;; definition mentions") are read off the final tables and need no log; a FORWARD
;;; reference (b_F mentions a head that was not yet defined when F was) needs the
;;; log, and without one (an image built before the log existed) it is approximated
;;; by the load order of the FILES holding the two definitions.  H3 needs the log
;;; and is not checkable without it.
;;;
;;; A DEFINED HEAD is what certificates.scm calls one, minus a proven theorem whose
;;; name coincides: a def-functoid, a library-definitions head, or a theorem named
;;; like the head with provenance `definitional'.  Primitives, structure accessors,
;;; structure predicates and registered constants without a definition are not.
;;;
;;; The optional arguments replace the registry (an alist ((NAME PVARS BODY PATH) ..)),
;;; the log and the definitions alist: the suite's controls plant one violation each.
;;; Returns a list of violations (H KIND NAME DETAIL), H in H1 H2 H3 H4 H6.

(define (fha--live-registry)
  (map (lambda (k) (cons k (hash-table-ref/default *functoid-registry* k #f)))
       (sort (hash-table-keys *functoid-registry*)
             (lambda (a b) (string<? (symbol->string a) (symbol->string b))))))

(define (fha--live-log) *functoid-def-log*)

(define fha--symbols fg--symbols)

(define (fha--raw f) (if (wff? f) (wff-formula f) f))

;;; log record accessors: (SEQ NAME PVARS BODY PATH UNDEFINED REDEF OLD SNAPSHOT)
(define (fha-rec-seq r) (list-ref r 0))
(define (fha-rec-name r) (list-ref r 1))
(define (fha-rec-pvars r) (list-ref r 2))
(define (fha-rec-body r) (list-ref r 3))
(define (fha-rec-path r) (list-ref r 4))
(define (fha-rec-undefined r) (list-ref r 5))
(define (fha-rec-redef r) (list-ref r 6))
(define (fha-rec-snapshot r) (list-ref r 8))

(define (fha--file-key p)                 ; "structure-library/foo", or #f
  (and p
       (let* ((s (if (string? p) p (->namestring p)))
              (d *prover-dir*)
              (s (if (string-prefix? d s) (substring s (string-length d) (string-length s)) s)))
         (let loop ((exts '(".scm" ".com" ".bin")))
           (cond ((null? exts) s)
                 ((string-suffix? (car exts) s)
                  (substring s 0 (- (string-length s) (string-length (car exts)))))
                 (#t (loop (cdr exts))))))))

(define (fha--file-index)                 ; file key -> position in *vnb-files*
  (let ((t (make-equal-hash-table)) (i 0))
    (for-each (lambda (f) (if (string? f) (begin (hash-table-set! t f i) (set! i (+ i 1)))))
              (call-with-current-continuation
                (lambda (k) (with-exception-handler (lambda (c) (k '())) (lambda () *vnb-files*)))))
    t))

;;; A declared structure species (a key of *structure-table*, structures.scm), read as a
;;; class constant by H4.  Not a registered constant: that would make it head-only.
(define (fha--structure-species? v)
  (and (symbol? v)
       (hash-table-ref/default *structure-table* v #f)
       #t))

(define (functoid-hypotheses-audit #!optional reg log defs)
  (let* ((reg  (if (default-object? reg) (fha--live-registry) reg))
         (log  (if (default-object? log) (fha--live-log) log))
         (defs (if (default-object? defs) (library-definitions *library*) defs))
         (regt (let ((t (make-strong-eqv-hash-table)))
                 (for-each (lambda (e) (hash-table-set! t (car e) (cdr e))) reg) t))
         (deft (let ((t (make-strong-eqv-hash-table)))
                 (for-each (lambda (e) (if (and (pair? e) (not (hash-table-ref/default t (car e) #f)))
                                           (hash-table-set! t (car e) e)))
                           defs)
                 t))
         (out  '()))
    (define (note! v) (if (not (member v out)) (set! out (cons v out))))
    (define (defined-head? s)
      (and (symbol? s)
           (or (and (hash-table-ref/default regt s #f) #t)
               (and (hash-table-ref/default deft s #f) #t)
               (and (hash-table-ref/default *theorem-table* s #f)
                    (eq? (provenance-of s) 'definitional)))))
    ;; the definition objects of a defined head, and the heads they mention
    (define (definitions s)
      (let ((r (hash-table-ref/default regt s #f))
            (l (hash-table-ref/default deft s #f)))
        (cond (r (list (cadr r)))
              (l (map (lambda (ax)
                        (if (pair? ax)
                            (or (and (symbol? (car ax)) (hash-table-ref/default *theorem-table* (car ax) #f))
                                (cdr ax))
                            ax))
                      (cdr l)))
              ((hash-table-ref/default *theorem-table* s #f) => list)
              (#t '()))))
    (define (successors s)                ; defined heads a definition of s mentions, s excepted
      (let ((acc '()))
        (for-each (lambda (d)
                    (for-each (lambda (x)
                                (if (and (not (eq? x s)) (defined-head? x) (not (memq x acc)))
                                    (set! acc (cons x acc))))
                              (fha--symbols (fha--raw d))))
                  (definitions s))
        acc))
    (define (def-file s)
      (let ((r (hash-table-ref/default regt s #f))
            (l (hash-table-ref/default deft s #f)))
        (fha--file-key
          (cond (r (and (pair? (cddr r)) (caddr r)))
                ((and l (pair? (cdr l)) (pair? (cadr l)) (symbol? (car (cadr l))))
                 (hash-table-ref/default *theorem-source* (car (cadr l)) #f))
                (#t (hash-table-ref/default *theorem-source* s #f))))))
    (define (check-h1 name pvars where)
      (cond ((not (list? pvars)) (note! (list 'H1 'not-a-list name pvars)))
            ((not (every symbol? pvars)) (note! (list 'H1 'not-symbols name pvars)))
            ((let dup ((ps pvars)) (and (pair? ps) (or (memq (car ps) (cdr ps)) (dup (cdr ps)))))
             (note! (list 'H1 'repeated name pvars)))))
    (define (check-h4 name pvars body)
      ;; a registered constant or a class name cannot be bound (constant-binder-audit,
      ;; fatal), a declared structure species is a class constant of its class axiom
      ;; (STRUCTURE-class, e.g. DIRECTED-SET in PTWISE-NET-LIMITS), and a defined head is a
      ;; constant of the tables read, so none of them is a variable of the body; every
      ;; other free symbol is
      (let ((fv (filter (lambda (v) (and (symbol? v) (not (memq v pvars)) (not (constant-head? v))
                                         (not (memq v *class-name-constants*))
                                         (not (fha--structure-species? v))
                                         (not (defined-head? v))
                                         (not (memq v '(TRUTH FALSITY)))))
                        (free-vars body))))
        (if (pair? fv) (note! (list 'H4 'free name fv)))))
    ;; H1, H4 on the registry and on every logged call; H2 direct recursion
    (for-each (lambda (e)
                (let ((name (car e)) (pvars (cadr e)) (body (caddr e)))
                  (check-h1 name pvars 'registry)
                  (check-h4 name (if (list? pvars) pvars '()) body)
                  (if (memq name (fha--symbols body)) (note! (list 'H2 'recursion name name)))
                  ;; H6
                  (if (hash-table-ref/default deft name #f) (note! (list 'H6 'both name #f)))))
              reg)
    (for-each (lambda (r)
                (check-h1 (fha-rec-name r) (fha-rec-pvars r) 'log)
                (check-h4 (fha-rec-name r) (if (list? (fha-rec-pvars r)) (fha-rec-pvars r) '())
                          (fha-rec-body r)))
              log)
    ;; H2 mutual recursion: Tarjan's SCCs over the defined-head graph from the functoids
    (let ((index (make-strong-eqv-hash-table)) (low (make-strong-eqv-hash-table))
          (on (make-strong-eqv-hash-table)) (stack '()) (n 0))
      (define (visit v)
        (hash-table-set! index v n) (hash-table-set! low v n) (set! n (+ n 1))
        (set! stack (cons v stack)) (hash-table-set! on v #t)
        (for-each (lambda (w)
                    (cond ((not (hash-table-ref/default index w #f))
                           (visit w)
                           (hash-table-set! low v (min (hash-table-ref low v (lambda () 0))
                                                       (hash-table-ref low w (lambda () 0)))))
                          ((hash-table-ref/default on w #f)
                           (hash-table-set! low v (min (hash-table-ref low v (lambda () 0))
                                                       (hash-table-ref index w (lambda () 0)))))))
                  (successors v))
        (if (= (hash-table-ref low v (lambda () -1)) (hash-table-ref index v (lambda () -2)))
            (let pop ((comp '()))
              (let ((w (car stack)))
                (set! stack (cdr stack)) (hash-table-delete! on w)
                (if (eq? w v)
                    (let ((comp (cons w comp)))
                      (if (pair? (cdr comp))
                          (for-each (lambda (x)
                                      (if (hash-table-ref/default regt x #f)
                                          (note! (list 'H2 'mutual x comp))))
                                    comp)))
                    (pop (cons w comp)))))))
      (for-each (lambda (e) (if (not (hash-table-ref/default index (car e) #f)) (visit (car e)))) reg))
    ;; H2 forward references: from the log, else by file order
    (if (pair? log)
        (for-each (lambda (r)
                    (for-each (lambda (s)
                                (if (and (not (eq? s (fha-rec-name r)))
                                         (or (defined-head? s) (constant-head? s)))
                                    (note! (list 'H2 'forward (fha-rec-name r) s))))
                              (fha-rec-undefined r)))
                  log)
        (let ((fidx (fha--file-index)))
          (for-each (lambda (e)
                      (let* ((name (car e))
                             (fi (hash-table-ref/default fidx (def-file name) #f)))
                        (if fi
                            (for-each (lambda (s)
                                        (if (and (not (eq? s name)) (defined-head? s))
                                            (let ((gi (hash-table-ref/default fidx (def-file s) #f)))
                                              (if (and gi (> gi fi))
                                                  (note! (list 'H2 'forward-by-file name s))))))
                                      (fha--symbols (caddr e))))))
                    reg)))
    ;; H3: a changed redefinition, and the theorems stated under the old entry that survive
    (for-each (lambda (r)
                (if (eq? (fha-rec-redef r) 'changed)
                    (begin
                      (note! (list 'H3 'redefined (fha-rec-name r) (fha--file-key (fha-rec-path r))))
                      (for-each (lambda (tf)
                                  (if (eq? (hash-table-ref/default *theorem-table* (car tf) #f) (cdr tf))
                                      (note! (list 'H3 'survivor (fha-rec-name r) (car tf)))))
                                (fha-rec-snapshot r)))))
              log)
    (reverse out)))

(define (fha--item v)
  (let ((kind (cadr v)) (name (caddr v)) (d (cadddr v)))
    (case kind
      ((repeated not-symbols not-a-list) (string-append (symbol->string name) " " (write-to-string d)))
      ((recursion) (string-append (symbol->string name) " (recursion)"))
      ((mutual) (string-append (symbol->string name) " (cycle " (write-to-string d) ")"))
      ((forward forward-by-file) (string-append (symbol->string name) " -> " (symbol->string d)
                                                (if (eq? kind 'forward-by-file) " (by file)" "")))
      ((redefined) (string-append (symbol->string name) " (redefined in " (write-to-string d) ")"))
      ((survivor) (string-append (symbol->string name) ": " (symbol->string d) " survives"))
      ((free) (string-append (symbol->string name) " free=" (write-to-string d)))
      ((both) (symbol->string name))
      (else (write-to-string v)))))

(define *functoid-hypotheses-show* 8)

;;; The load-end gate: one line per hypothesis.  Returns ((H . count) ...).
(define (functoid-hypotheses-gate! #!optional reg log defs)
  (let* ((log  (if (default-object? log) (fha--live-log) log))
         (vs   (if (default-object? reg)
                   (functoid-hypotheses-audit (fha--live-registry) log
                                              (if (default-object? defs) (library-definitions *library*) defs))
                   (functoid-hypotheses-audit reg log (if (default-object? defs) (library-definitions *library*) defs))))
         (titles '((H1 . "parameters are distinct symbols")
                   (H2 . "body mentions only heads defined before")
                   (H3 . "one entry per head, no survivor of a redefinition")
                   (H4 . "body's free variables among the parameters")
                   (H6 . "no head both a def-functoid and a library definition"))))
    (display ";; functoid-hypotheses gate: ")
    (if (pair? log)
        (begin (display (length log)) (display " def-functoid call(s) in the definition log, ")
               (display (length (filter (lambda (r) (eq? (fha-rec-redef r) 'identical)) log)))
               (display " identical redefinition(s)\n"))
        (display "NO definition log in this image: H2 forward references by file order, H3 not checkable\n"))
    (map (lambda (tt)
           (let* ((h (car tt))
                  (hs (filter (lambda (v) (eq? (car v) h)) vs))
                  (k (length hs)))
             (display ";; functoid-hypotheses ") (display h) (display " (") (display (cdr tt)) (display "): ")
             (cond ((and (eq? h 'H3) (not (pair? log))) (display "not checkable (no log)"))
                   ((= k 0) (display "ok"))
                   (#t (display k) (display " violation(s): ")
                       (let loop ((xs hs) (i 0))
                         (cond ((null? xs))
                               ((>= i *functoid-hypotheses-show*)
                                (display " ... (+") (display (- k i)) (display " more)"))
                               (#t (if (> i 0) (display "; "))
                                   (display (fha--item (car xs)))
                                   (loop (cdr xs) (+ i 1)))))))
             (newline)
             (cons h k)))
         titles)))

;;; THE FATAL FORM (FGATE, 2026-11-19).  The backlog reached zero with the two repairs of
;;; that day (dual-space.scm moved after numeric-instances in load.scm, H2; a declared
;;; structure species such as DIRECTED-SET read by H4 as a class constant, H4), so every hypothesis the gate
;;; reads goes fatal at once, as the other gates do once their backlog is zero.  FATAL? #t
;;; raises after the report when any hypothesis has a violation; FATAL? #f reports only.
;;; run-load-end! (load.scm) passes #t in a strict load and #f under keep-going.  H3 without
;;; a definition log counts 0 (not checkable is not a violation).  The optional arguments
;;; are those of the gate (the suite's controls).  Returns the counts, as the gate does.
(define (functoid-hypotheses-enforce! fatal? #!optional reg log defs)
  (let* ((counts (cond ((default-object? reg) (functoid-hypotheses-gate!))
                       ((default-object? log) (functoid-hypotheses-gate! reg))
                       ((default-object? defs) (functoid-hypotheses-gate! reg log))
                       (#t (functoid-hypotheses-gate! reg log defs))))
         (bad (filter (lambda (c) (> (cdr c) 0)) counts)))
    (if (pair? bad)
        (begin
          (display ";; functoid-hypotheses gate: ")
          (display (apply + (map cdr bad))) (display " violation(s) of ")
          (write (map car bad))
          (display (if fatal? " (FATAL)\n" " (reported under keep-going)\n"))
          (if fatal?
              (error "functoid-hypotheses gate: a def-functoid violates the hypotheses of the functoid argument; see the report above"
                     bad))))
    counts))

;;; Arm the log now: def-functoid exists (structures.scm has loaded) and no file
;;; after structures.scm has defined a functoid yet.
(functoid-def-log-arm!)
