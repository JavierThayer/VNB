;;; libraries.scm -- THE LIBRARIES (the user, notes-61, 2026-10-06: "start thinking of
;;; libraries; users interested in Analysis might not be interested in strands").
;;;
;;; A LIBRARY is a declared set of theorem-library/ and structure-library/ files with
;;; declared IMPORTS, read from libraries.sexp (the table is hand-kept; the load list
;;; stays as it is, the libraries interleave in it).  This file gives the table an API
;;; and the GATE:
;;;
;;;   (library-of-file "theorem-library/foo")   -> a library name, 'exempt or #f
;;;   (library-of-name 'thm)                    -> the library of the file that states it
;;;   (library-imports* 'analysis)              -> the import closure, itself included
;;;   (library-citation-violations)             -> ((name lib cited cited-lib) ...)
;;;   (library-head-violations)                 -> ((name lib head head-lib) ...)
;;;   (library-gate!)                           -> prints the report; the counts
;;;
;;; THE RULE: a theorem of library L cites only theorems of L and of L's import closure,
;;; and its statement uses only vocabulary (functoids, defined heads, structures)
;;; defined there.  The citations come from the LIVE graph (`proof-citations-of',
;;; proof-debt.scm: certified theorems included); the vocabulary from the statement's
;;; applied heads.  A violation is a lemma sitting in the wrong file -- the first run
;;; found list lemmas inside matrix and polynomial files -- or a file assigned to the
;;; wrong library.  Warn-only while the backlog is being worked down; the gate goes
;;; fatal in a strict load once it is zero, on the connective-arity precedent.
;;;
;;; Loads late (after proof-reader, which owns `proof-reader--heads').

(define *library-table-path* "libraries.sexp")
(define *libraries* '())                       ; ((name title about imports files) ...) in table order
(define *library-exempt-files* '())
;;; CROSS-CUTTING files (the `cross-cutting' form): a file whose theorems belong to
;;; several libraries -- the generated hom laws of every structure, the views, a
;;; rake batch mixing areas.  A proven or asserted theorem of such a file is placed
;;; by its VOCABULARY: the JOIN of the libraries of its statement's heads (the
;;; smallest library whose import closure holds them all), falling back on the file's
;;; nominal library.  Its definitions stay with the file.
(define *library-cross-cutting-files* '())
(define *library-of-file* (make-equal-hash-table))   ; "theorem-library/foo" -> name | exempt
(define *library--placement-memo* (make-equal-hash-table))  ; cross-cutting theorem -> its join

(define (library--table-file)
  (string-append *prover-dir* *library-table-path*))

(define (library--field form key default)
  (let ((e (assq key (cddr form))))
    (if e (cdr e) default)))

(define (read-libraries-table!)
  (set! *libraries* '())
  (set! *library-exempt-files* '())
  (set! *library-cross-cutting-files* '())
  (hash-table-clear! *library--placement-memo*)
  (hash-table-clear! *library-of-file*)
  (let ((path (library--table-file)))
    (if (file-exists? path)
        (let ((forms (call-with-input-file path
                       (lambda (p)
                         (let loop ((acc '()))
                           (let ((f (read p)))
                             (if (eof-object? f) (reverse acc) (loop (cons f acc)))))))))
          (for-each
            (lambda (form)
              (cond ((and (pair? form) (eq? (car form) 'library))
                     (let* ((name  (cadr form))
                            (title (let ((t (library--field form 'title '()))) (if (pair? t) (car t) (symbol->string name))))
                            (about (let ((a (library--field form 'about '()))) (if (pair? a) (car a) "")))
                            (imports (library--field form 'imports '()))
                            (files (library--field form 'files '())))
                       (set! *libraries* (append *libraries* (list (list name title about imports files))))
                       (for-each (lambda (f) (hash-table-set! *library-of-file* f name)) files)))
                    ((and (pair? form) (eq? (car form) 'cross-cutting))
                     (set! *library-cross-cutting-files*
                           (append *library-cross-cutting-files* (cdr form))))
                    ((and (pair? form) (eq? (car form) 'exempt))
                     (set! *library-exempt-files* (append *library-exempt-files* (cdr form)))
                     (for-each (lambda (f) (hash-table-set! *library-of-file* f 'exempt)) (cdr form)))
                    (else #f)))
            forms)
          (length *libraries*))
        (begin (display ";; libraries: no table at ") (display path) (newline) 0))))

(define (library-names) (map car *libraries*))
(define (library-record name) (assq name *libraries*))
(define (library-title name) (let ((r (library-record name))) (if r (cadr r) (symbol->string name))))
(define (library-about name) (let ((r (library-record name))) (if r (caddr r) "")))
(define (library-imports name) (let ((r (library-record name))) (if r (cadddr r) '())))
(define (library-files name) (let ((r (library-record name))) (if r (car (cddddr r)) '())))

;;; the import closure of NAME, NAME included
(define (library-imports* name)
  (let loop ((todo (list name)) (seen '()))
    (cond ((null? todo) (reverse seen))
          ((memq (car todo) seen) (loop (cdr todo) seen))
          (else (loop (append (cdr todo) (library-imports (car todo)))
                      (cons (car todo) seen))))))

;;; the table's order, which is a topological order of the imports
(define (library-order-index lib)
  (let loop ((ls (library-names)) (i 0))
    (cond ((null? ls) 1000) ((eq? (car ls) lib) i) (else (loop (cdr ls) (+ i 1))))))

;;; the smallest library whose closure holds every one of LIBS; when none does, the
;;; last of LIBS in table order (and the gate will say so through the citations)
(define (library-join libs)
  (let ((libs (filter (lambda (l) (and l (symbol? l) (not (eq? l 'exempt)))) libs)))
    (cond ((null? libs) #f)
          (else
           (let ((cands (filter (lambda (c)
                                  (let ((cl (library-imports* c)))
                                    (every (lambda (l) (memq l cl)) libs)))
                                (library-names))))
             (if (pair? cands)
                 (car (sort cands (lambda (a b) (< (length (library-imports* a))
                                                   (length (library-imports* b))))))
                 (car (sort libs (lambda (a b) (> (library-order-index a)
                                                  (library-order-index b)))))))))))

(define (library-cross-cutting? rel)
  (and rel (member rel *library-cross-cutting-files*) #t))

;;; "theorem-library/foo" from a pathname or a string with any prefix / type
(define (library-rel-of-path p)
  (and p
       (let* ((s   (if (string? p) p (->namestring p)))
              (dir *prover-dir*)
              (n   (string-length dir))
              (s   (if (and (>= (string-length s) n) (string=? (string-head s n) dir))
                       (string-tail s n) s))
              (s   (cond ((string-suffix? ".scm" s) (string-head s (- (string-length s) 4)))
                         ((string-suffix? ".com" s) (string-head s (- (string-length s) 4)))
                         (else s))))
         s)))

(define (library-of-file rel)
  (and rel (hash-table-ref/default *library-of-file* rel #f)))

(define (library-of-path p)
  (library-of-file (library-rel-of-path p)))

;;; the library of a theorem, functoid or structure NAME, through the file that
;;; installed it; #f when nothing records a file (REPL installs, the generators).  A
;;; proven or asserted theorem of a CROSS-CUTTING file is placed by its vocabulary
;;; (`library-join' over its heads); a definition always stays with its file.
(define (library-of-name name)
  (let* ((src (hash-table-ref/default *theorem-source* name #f))
         (rel (and src (library-rel-of-path src))))
    (cond (rel
           (let ((nominal (library-of-file rel)))
             (if (and (library-cross-cutting? rel)
                      (memq (provenance-of name) '(proven certified asserted)))
                 ;; core is the FLOOR of the join: a head that resolves to no library is
                 ;; primitive vocabulary (sets, NN, ORD, the number classes), which is core's;
                 ;; a theorem of a shared file stated in primitives alone is a core theorem,
                 ;; whatever the file's nominal library (ord-segment-insert in a finsum batch).
                 ;; ... and by what the PROOF uses: the join takes the citations' libraries too
                 ;; (zz-add-cancel in `cancellation' says NN and ZZ and cites zz-is-ring: algebra).
                 ;; Memoised: the citation graph is walked once per name per load.
                 (or (hash-table-ref/default *library--placement-memo* name #f)
                     (let* ((f (hash-table-ref/default *theorem-table* name #f))
                            (lib (or (and f (library-join
                                             (cons 'core
                                                   (append (map library-of-head (proof-reader--heads f))
                                                           (map library-of-name (proof-citations-of name))))))
                                     nominal)))
                       (hash-table-set! *library--placement-memo* name lib)
                       lib))
                 nominal)))
          ((hash-table-ref/default *functoid-registry* name #f)
           => (lambda (reg) (and (pair? (cddr reg)) (library-of-path (caddr reg)))))
          (else #f))))

;;; the library owning an applied HEAD of a statement: a functoid, a def-predicate /
;;; def-constant head (through its first defining axiom), a structure predicate IS-X
;;; or the structure's class predicate; #f for a primitive, an accessor or a variable
(define (library-of-head h)
  (cond ((not (symbol? h)) #f)
        ((and (not (lookup-view-as h)) (hash-table-ref/default *functoid-registry* h #f))
         => (lambda (reg) (and (pair? (cddr reg)) (library-of-path (caddr reg)))))
        ((assq h (library-definitions *library*))
         => (lambda (e) (and (pair? (cdr e)) (library-of-name (car (cadr e))))))
        (else (library--structure-head-library h))))

;;; the source file of a declared structure X -- a shape (`*structure-table*') or a
;;; refinement (`same-shape-as', `*definitional-structure-table*'); #f when X is neither
(define (library--structure-source x)
  (let ((sd (lookup-structure x)))
    (if sd
        (structure-def-source-file sd)
        (let ((dsd (lookup-definitional-structure x)))
          (and dsd (definitional-structure-source-file dsd))))))

;;; IS-X, HOM-X and X-CLASS name the structure X: its file's library, else #f
(define (library--structure-head-library h)
  (let* ((str (symbol->string h))
         (n (string-length str))
         (x (cond ((and (> n 3) (string-ci=? (substring str 0 3) "is-"))
                   (string->symbol (substring str 3 n)))
                  ((and (> n 4) (string-ci=? (substring str 0 4) "hom-"))
                   (string->symbol (substring str 4 n)))
                  ((and (> n 6) (string-ci=? (substring str (- n 6) n) "-class"))
                   (string->symbol (substring str 0 (- n 6))))
                  (else #f)))
         (src (and x (library--structure-source x))))
    (and src (library-of-path src))))

(define (library--exempt-or-generated? name)
  (or (rev-companion-source name)
      (view-specialized-source name)
      (eq? (library-of-name name) 'exempt)))

;;; every theorem-library/ or structure-library/ entry of the load list with no library
(define (library-unassigned-files)
  (filter (lambda (f)
            (and (string? f)
                 (or (string-prefix? "theorem-library/" f) (string-prefix? "structure-library/" f))
                 (not (library-of-file f))))
          *vnb-files*))

;;; table entries that the load list does not name
(define (library-stale-files)
  (filter (lambda (f) (not (member f *vnb-files*)))
          (append (apply append (map library-files (library-names))) *library-exempt-files*)))

;;; the citations of NAME that leave its import closure: ((name lib cited cited-lib) ...)
(define (library-violations-of name)
  (let ((lib (library-of-name name)))
    (if (or (not lib) (eq? lib 'exempt) (library--exempt-or-generated? name))
        '()
        (let ((ok (library-imports* lib)))
          (let loop ((cs (proof-citations-of name)) (acc '()))
            (if (null? cs)
                (reverse acc)
                (let ((m (library-of-name (car cs))))
                  (loop (cdr cs)
                        (if (and m (not (eq? m 'exempt)) (not (memq m ok)))
                            (cons (list name lib (car cs) m) acc)
                            acc)))))))))

(define (library-citation-violations)
  (let ((out '()))
    (for-each (lambda (n)
                (when (memq (provenance-of n) '(proven certified))
                  (set! out (append (library-violations-of n) out))))
              (hash-table-keys *theorem-table*))
    out))

;;; the applied heads of NAME's statement whose definition lives outside its closure
(define (library-head-violations-of name)
  (let ((lib (library-of-name name))
        (f   (hash-table-ref/default *theorem-table* name #f))
        (rel (library-rel-of-path (hash-table-ref/default *theorem-source* name #f))))
    (if (or (not lib) (eq? lib 'exempt) (not f) (library--exempt-or-generated? name)
            (library-cross-cutting? rel))          ; placed by its heads: nothing to check
        '()
        (let ((ok (library-imports* lib)))
          (let loop ((hs (proof-reader--heads f)) (acc '()))
            (if (null? hs)
                (reverse acc)
                (let ((m (library-of-head (car hs))))
                  (loop (cdr hs)
                        (if (and m (not (eq? m 'exempt)) (not (memq m ok))
                                 (not (assq (car hs) acc)))
                            (cons (list name lib (car hs) m) acc)
                            acc)))))))))

(define (library-head-violations)
  (let ((out '()))
    (for-each (lambda (n) (set! out (append (library-head-violations-of n) out)))
              (hash-table-keys *theorem-table*))
    out))

;;; group violations by (lib . other-lib), one line per pair with up to 8 examples
(define (library--report-violations vs what)
  (let ((pairs '()))
    (for-each (lambda (v)
                (let* ((key (cons (cadr v) (cadddr v)))
                       (e (assoc key pairs)))
                  (if e (set-cdr! e (cons v (cdr e)))
                      (set! pairs (cons (list key v) pairs)))))
              vs)
    (for-each
      (lambda (e)
        (display ";;   ") (display (caar e)) (display " -> ") (display (cdar e))
        (display ": ") (display (length (cdr e))) (display " ") (display what) (display "  e.g. ")
        (let loop ((xs (reverse (cdr e))) (k 0))
          (when (and (pair? xs) (< k 8))
            (display (car (car xs))) (display " uses ") (display (caddr (car xs)))
            (when (and (pair? (cdr xs)) (< k 7)) (display "; "))
            (loop (cdr xs) (+ k 1))))
        (newline))
      (sort pairs (lambda (a b) (> (length (cdr a)) (length (cdr b))))))))

;;; THE GATE.  Warn-only; returns (citation-count . head-count).
(define (library-gate!)
  (read-libraries-table!)
  (let* ((unassigned (library-unassigned-files))
         (stale (library-stale-files))
         (cv (library-citation-violations))
         (hv (library-head-violations))
         (nfiles (apply + (map (lambda (l) (length (library-files l))) (library-names)))))
    (display ";; library-gate: ") (display (length (library-names))) (display " libraries (")
    (display (library-names)) (display "); ") (display nfiles) (display " files assigned, ")
    (display (length *library-exempt-files*)) (display " exempt, ")
    (display (length unassigned)) (display " unassigned, ") (display (length stale)) (display " stale; ")
    (display (length cv)) (display " citation violation(s), ")
    (display (length hv)) (display " vocabulary violation(s)") (newline)
    ;; the cross-cutting files: how many theorems each library received from them
    (let ((shared (make-equal-hash-table)))
      (for-each (lambda (n)
                  (let ((rel (library-rel-of-path (hash-table-ref/default *theorem-source* n #f))))
                    (when (and (library-cross-cutting? rel)
                               (memq (provenance-of n) '(proven certified asserted))
                               (not (library--exempt-or-generated? n)))
                      (hash-table-update!/default shared (library-of-name n) (lambda (k) (+ k 1)) 0))))
                (hash-table-keys *theorem-table*))
      (when (pair? *library-cross-cutting-files*)
        (display ";;   ") (display (length *library-cross-cutting-files*))
        (display " cross-cutting file(s); their theorems placed by vocabulary: ")
        (display (sort (hash-table->alist shared)
                       (lambda (a b) (< (library-order-index (car a)) (library-order-index (car b))))))
        (newline)))
    (when (pair? unassigned)
      (display ";;   UNASSIGNED (add to libraries.sexp): ") (write unassigned) (newline))
    (when (pair? stale)
      (display ";;   stale table entries (not in the load list): ") (write stale) (newline))
    (when (pair? cv) (library--report-violations cv "citation(s)"))
    (when (pair? hv) (library--report-violations hv "head(s)"))
    (cons (length cv) (length hv))))
