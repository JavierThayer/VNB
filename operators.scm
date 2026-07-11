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
               (if (not (operator-file old)) (set-operator-file! old (current-load-pathname))))
        (hash-table-set! *operators* k
          (make-operator kind (length ps) ps #f #f #f #f #f #f (current-load-pathname))))
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

(define (describe-operator name)
  (let ((e (operator-ref name)))
    (cond
      ((not e) (display ";; no operator named ") (display name) (newline) #f)
      (else
       (display ";; ") (display (op-key name))
       (display " : ") (display (operator-kind e))
       (display ", arity ") (display (or (operator-arity e) '?)) (newline)
       (if (pair? (operator-params e))
           (begin (display ";;   params:  ") (display (operator-params e)) (newline)))
       (if (operator-noun e)
           (begin (display ";;   reads:   x is ")
                  (if (not (string=? (or (operator-article e) "") ""))
                      (begin (display (operator-article e)) (display " ")))
                  (display (operator-noun e)) (newline)))
       (if (operator-english e)
           (begin (display ";;   english: ")
                  (if (string? (operator-english e))
                      (display (operator-english e))
                      (display "<procedure>"))
                  (newline)))
       (if (operator-tex e)
           (begin (display ";;   tex:     ") (display (operator-tex e)) (newline)))
       (if (operator-file e)
           (begin (display ";;   defined: ") (display (operator-file e)) (newline)))
       e))))

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
