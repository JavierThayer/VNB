;;; operators.scm -- ONE table, keyed by head symbol.
;;;
;;;   head -> (kind arity params tex english noun article prec infix? file)
;;;
;;; WHY THIS FILE EXISTS.  Everything a renderer needs to know about a head
;;; symbol was, until now, in four places and known at none of them:
;;;
;;;   *english-sort* / *english-pred*  (wff-english.scm)  -- 29 entries, by hand
;;;   *tex-binop-table* / *tex-special-table* / ...       -- four alists, by hand
;;;   *constant-registry*              (expressions.scm)  -- kind tag only, no arity
;;;   op-defn-class                    (interactive.scm)  -- RE-DERIVES the kind by
;;;       pattern-matching the shape of the defining axiom, because the kind was
;;;       known at `def-predicate' time and thrown away.
;;;
;;; `def-predicate' and `def-functoid' know the name, the kind, the parameters
;;; (hence the arity) and the file.  They now say so, here, at definition time.
;;; What they cannot know is the NOTATION -- how a human writes and reads the
;;; thing -- so that is declared next to the definition with `notation!':
;;;
;;;   (def-predicate 'IS-EUCLIDEAN-RING '(a) '(AND ...))
;;;   (notation! 'IS-EUCLIDEAN-RING 'noun "Euclidean ring" 'article "a")
;;;
;;; and `IS-EUCLIDEAN-RING(a)' then reads as "a is a Euclidean ring" in the
;;; proof reader, as a qualifier ("for every Euclidean ring a") under a
;;; quantifier, and as \operatorname{is-euclidean-ring}(a) in TeX.
;;;
;;; Read by expr->tex (tex-output), wff->english (wff-english),
;;; describe-structure and write-operators-md (interactive).
;;;
;;; Loads after `expressions' (for register-constant!) and before `theory',
;;; `structures' and the structure library, which populate it.

;;; -----------------------------------------------------------------------
;;; The table.  Like *pss-categories* and *tactic-help*: a hash table, keyed by
;;; the LOWERCASE symbol (the reader and MIT Scheme both fold -- see CLAUDE.md).

(define *operators* (make-equal-hash-table))

;;; A head need not be a symbol: `((MUL s) x y)' applies a COMPOUND head (a
;;; structure accessor applied to the structure).  Those have no table entry --
;;; return #f rather than dying in symbol->string.
(define (op-key s)
  (and (symbol? s) (string->symbol (string-downcase (symbol->string s)))))

;;; slots: kind arity params tex english noun article prec infix? file
(define-record-type operator
  (make-operator kind arity params tex english noun article prec infix? file)
  operator?
  (kind    operator-kind    set-operator-kind!)      ; predicate|functoid|function|primitive
  (arity   operator-arity   set-operator-arity!)     ; integer, or #f if variadic
  (params  operator-params  set-operator-params!)    ; the definition's parameter names
  (tex     operator-tex     set-operator-tex!)       ; template string, or #f
  (english operator-english set-operator-english!)   ; template string / procedure / #f
  (noun    operator-noun    set-operator-noun!)      ; unary sorts: "Euclidean ring"
  (article operator-article set-operator-article!)   ; "a" / "an" / "" (reads as adjective)
  (prec    operator-prec    set-operator-prec!)      ; binding power, #f = application
  (infix?  operator-infix?  set-operator-infix?!)
  (file    operator-file    set-operator-file!))

(define (operator-ref name)
  (let ((k (op-key name)))
    (and k (hash-table-ref/default *operators* k #f))))

(define (operator-names)
  (sort (hash-table-keys *operators*)
        (lambda (a b) (string<? (symbol->string a) (symbol->string b)))))

;;; Called BY THE DEFINITION POINT (def-predicate, def-functoid, ...).  Records
;;; what it knows; leaves the notation slots empty for `notation!'.  Re-declaring
;;; a head updates the structural slots and KEEPS any notation already declared.
(define (register-operator! name kind params)
  (let* ((k   (or (op-key name) (error "register-operator!: not a symbol" name)))
         (ps  (cond ((not params) '()) ((pair? params) params) (else (list params))))
         (old (hash-table-ref/default *operators* k #f)))
    (if old
        (begin (set-operator-kind! old kind)
               (set-operator-arity! old (length ps))
               (set-operator-params! old ps)
               (if (not (operator-file old)) (set-operator-file! old (safe-load-pathname))))
        (hash-table-set! *operators* k
          (make-operator kind (length ps) ps #f #f #f #f #f #f (safe-load-pathname))))
    name))

;;; Declare the NOTATION of a head.  Keyword-style, so a call names only what it
;;; has to say:
;;;   (notation! 'IS-EUCLIDEAN-RING 'noun "Euclidean ring" 'article "a")
;;;   (notation! '+ 'tex "$1 + $2" 'english "$1 plus $2" 'prec 60 'infix? #t)
;;; Templates are strings with $1 .. $9 placeholders for the arguments; `english'
;;; may instead be a procedure (list of argument strings -> string) for the cases
;;; a template cannot reach.  Declaring notation for an unregistered head (a
;;; primitive like `=' or `IN', which no def-* introduces) registers it as such.
(define (notation! name . kvs)
  (let ((entry (or (operator-ref name)
                   (begin (register-operator! name 'primitive #f)
                          (operator-ref name)))))
    (let loop ((kvs kvs))
      (cond
        ((null? kvs) name)
        ((null? (cdr kvs)) (error "notation!: odd keyword list for" name))
        (else
         (let ((key (car kvs)) (val (cadr kvs)))
           (case key
             ((tex)     (set-operator-tex! entry val))
             ((english) (set-operator-english! entry val))
             ((noun)    (set-operator-noun! entry val))
             ((article) (set-operator-article! entry val))
             ((prec)    (set-operator-prec! entry val))
             ((infix?)  (set-operator-infix?! entry val))
             ((arity)   (set-operator-arity! entry val))
             ((kind)    (set-operator-kind! entry val))
             (else (error "notation!: unknown key" key "for" name)))
           (loop (cddr kvs))))))))

;;; -----------------------------------------------------------------------
;;; Templates.  "$1 is at most $2" + ("x" "y") -> "x is at most y".
;;; Returns #f when the head has no template of that kind, so every caller can
;;; fall back to its own default (prefix application) unchanged.

(define (op--fill template args)
  (let ((n (string-length template)))
    (let loop ((i 0) (acc '()))
      (cond
        ((>= i n) (apply string-append (reverse acc)))
        ((and (char=? (string-ref template i) #\$)
              (< (+ i 1) n)
              (char-numeric? (string-ref template (+ i 1))))
         (let ((k (- (char->digit (string-ref template (+ i 1)) 10) 1)))
           (loop (+ i 2)
                 (cons (if (and (>= k 0) (< k (length args))) (list-ref args k) "?")
                       acc))))
        (else (loop (+ i 1) (cons (string (string-ref template i)) acc)))))))

;;; Render (head a1 ... an) given the already-rendered ARGS.  #f if the head has
;;; no such notation.
(define (operator-render-tex head args)
  (let ((e (operator-ref head)))
    (and e (operator-tex e) (op--fill (operator-tex e) args))))

(define (operator-render-english head args)
  (let* ((e (operator-ref head))
         (t (and e (operator-english e))))
    (cond ((not t) #f)
          ((procedure? t) (t args))
          ((string? t) (op--fill t args))
          (else #f))))

;;; Unary SORT: a head that reads as "x is a <noun>", and folds into a
;;; quantifier as "<noun> x".  (The English of IS-EUCLIDEAN-RING.)
(define (operator-sort head)
  (let ((e (operator-ref head)))
    (and e (operator-noun e)
         (cons (operator-noun e) (or (operator-article e) "a")))))

;;; -----------------------------------------------------------------------
;;; REPL surface.  Prints AND returns (the house rule).

(define (operators #!optional kind)
  (let* ((all (map (lambda (n) (cons n (operator-ref n))) (operator-names)))
         (sel (if (default-object? kind)
                  all
                  (filter (lambda (p) (eq? (operator-kind (cdr p)) kind)) all))))
    (display ";; ") (display (length sel)) (display " operator(s)")
    (if (not (default-object? kind)) (begin (display " of kind ") (display kind)))
    (display ":\n")
    (for-each
      (lambda (p)
        (let ((n (car p)) (e (cdr p)))
          (display "  ") (display n)
          (display "/") (display (or (operator-arity e) '?))
          (display "  ") (display (operator-kind e))
          (if (operator-noun e)
              (begin (display "  \"is ")
                     (if (not (string=? (or (operator-article e) "") ""))
                         (begin (display (operator-article e)) (display " ")))
                     (display (operator-noun e)) (display "\"")))
          (if (operator-english e)
              (if (string? (operator-english e))
                  (begin (display "  english=") (write (operator-english e)))
                  (display "  english=<proc>")))
          (if (operator-tex e) (begin (display "  tex=") (write (operator-tex e))))
          (newline)))
      sel)
    sel))

(define (op--file-string e)
  (let ((f (operator-file e)))
    (and f (let ((str (if (string? f) f (->namestring f))))
             ;; show it relative to the prover dir -- the absolute path is noise
             (let ((i (string-search-forward "prover/" str 0)))
               (if i (string-tail str (+ i 7)) str))))))

;;; Where an ACCESSOR lives: which structure declares it, at which slot, and so
;;; what (ACC s) unfolds to.  The accessor macete is literally (ACC s) -> (NTH k s).
(define (op--accessor-sites name)
  (let ((k (op-key name)) (hits '()))
    (hash-table-walk *structure-table*
      (lambda (sname sd)
        (let loop ((slots (structure-def-slots sd)) (i 1))
          (cond ((null? slots) #t)
                ((eq? (op-key (caar slots)) k)
                 (set! hits (cons (list sname i (car slots)) hits)))
                (else (loop (cdr slots) (+ i 1)))))))
    (sort hits (lambda (a b) (string<? (symbol->string (car a)) (symbol->string (car b)))))))

;;; The formula a PREDICATE is defined by: its own axiom, or its -def axiom
;;; (the (same-shape-as ...) refinements install is-NAME-def).
(define (op--theorem-opt name)
  ;; lookup-theorem ERRORS on an unknown name; the table lookup does not.
  (hash-table-ref/default *theorem-table* name #f))

(define (op--predicate-definition name)
  (or (op--theorem-opt (op-key name))
      (op--theorem-opt (symbol-append (op-key name) '-def))))

(define (op--line label str)
  (display ";;   ") (display label) (display str) (newline))

(define (describe-operator name)
  (let ((e (operator-ref name)))
    (cond
      ((not e)
       (display ";; no operator named ") (display name)
       (display " -- (operators) lists them all") (newline)
       #f)
      (else
       (let* ((k    (op-key name))
              (kind (operator-kind e)))
         (display ";; ") (display k)
         (display " : ") (display kind)
         (display ", arity ") (display (or (operator-arity e) '?))
         (newline)
         (if (pair? (operator-params e))
             (op--line "params:   " (with-output-to-string
                                      (lambda () (write (operator-params e))))))

         ;; --- what it MEANS ---------------------------------------------
         (case kind
           ((accessor)
            (for-each
              (lambda (site)
                (let* ((sname (car site)) (idx (cadr site)) (slot (caddr site))
                       (skind (cadr slot)))
                  (op--line "slot:     "
                            (string-append (number->string idx) " of "
                                           (symbol->string sname)
                                           " (" (symbol->string skind)
                                           (if (eq? skind 'op)
                                               (string-append " "
                                                 (expression->string (caddr slot))
                                                 " -> "
                                                 (expression->string (cadddr slot)))
                                               "")
                                           ")"))
                  (op--line "unfolds:  "
                            (string-append (symbol->string k) "(s) = nth("
                                           (number->string idx) ", s)"))))
              (op--accessor-sites k)))
           ((functoid)
            (let ((reg (hash-table-ref/default *functoid-registry* k #f)))
              (if reg
                  (op--line "unfolds:  "
                            (string-append
                              (expression->string (cons k (car reg)))
                              " = " (expression->string (cadr reg)))))))
           ((predicate)
            (let ((f (op--predicate-definition k)))
              (if f (op--line "defn:     " (expression->string f)))))
           (else #f))

         ;; --- how it READS ----------------------------------------------
         (if (operator-noun e)
             (op--line "reads:    "
                       (string-append "x is "
                                      (if (string=? (or (operator-article e) "") "")
                                          "" (string-append (operator-article e) " "))
                                      (operator-noun e))))
         (if (operator-english e)
             (op--line "english:  " (if (string? (operator-english e))
                                        (operator-english e)
                                        "<procedure>")))
         (if (operator-tex e) (op--line "tex:      " (operator-tex e)))
         (if (not (or (operator-noun e) (operator-english e) (operator-tex e)))
             (op--line "notation: "
                       (string-append "none declared -- (notation! '"
                                      (symbol->string k)
                                      " 'english \"...\") beside its definition")))
         (let ((f (op--file-string e)))
           (if f (op--line "defined:  " f)))
         e)))))

;;; The worklist: every head with no notation declared, so filling the table in
;;; is a checklist and not a scan.  Prints AND returns.
(define (operators-undeclared #!optional kind)
  (let* ((bare (filter (lambda (n)
                         (let ((e (operator-ref n)))
                           (and (not (operator-noun e))
                                (not (operator-english e))
                                (not (operator-tex e))
                                (or (default-object? kind)
                                    (eq? (operator-kind e) kind)))))
                       (operator-names)))
         (of (lambda (kd) (filter (lambda (n) (eq? (operator-kind (operator-ref n)) kd))
                                  bare))))
    (display ";; ") (display (length bare))
    (display " head(s) with no notation declared")
    (if (not (default-object? kind)) (begin (display " of kind ") (display kind)))
    (display ":\n")
    (for-each
      (lambda (kd)
        (let ((ns (if (default-object? kind) (of kd) (if (eq? kd kind) bare '()))))
          (when (pair? ns)
            (display ";;   ") (display kd) (display " (") (display (length ns)) (display "):")
            (for-each (lambda (n) (display " ") (display n)) ns)
            (newline))))
      '(predicate functoid accessor function primitive))
    bare))

;;; Print the record as something a human can read -- it is a REPL return value.
(define-print-method operator?
  (standard-print-method
    (lambda (e) (string-append "operator " (symbol->string (operator-kind e))))
    (lambda (e) (list (or (operator-arity e) '?)))))   ; get-parts returns a LIST

;;; -----------------------------------------------------------------------
;;; PRIMITIVE VOCABULARY.
;;;
;;; The heads no `def-*' introduces: the logical and set-theoretic primitives,
;;; and the order relations.  Everything else declares its notation beside its
;;; own definition -- that is the point of the table.  (These were
;;; `def-english-pred!' calls buried in wff-english.scm.)

(notation! 'in       'kind 'primitive 'arity 2 'english "$1 is in $2")
(notation! 'subset   'kind 'primitive 'arity 2 'english "$1 is a subset of $2")
(notation! '=        'kind 'primitive 'arity 2 'english "$1 equals $2")
(notation! '==       'kind 'primitive 'arity 2 'english "$1 is identical to $2")
(notation! '<=       'kind 'primitive 'arity 2 'english "$1 is at most $2")
(notation! '<        'kind 'primitive 'arity 2 'english "$1 is less than $2")
(notation! '>=       'kind 'primitive 'arity 2 'english "$1 is at least $2")
(notation! '>        'kind 'primitive 'arity 2 'english "$1 is greater than $2")
