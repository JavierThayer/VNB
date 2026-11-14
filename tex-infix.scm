;;; tex-infix.scm -- THE OPTIONAL INFIX LAYER for the TeX printer (printer side).
;;;
;;; The user's idea, 2026-11-12, started on his word 2026-11-14: an applied structure
;;; operation `((ADD K) a b)' prints `a +_{K} b' instead of `add(K)(a, b)', on an explicit
;;; switch, with the reading conventions stated as data.  The existing printer is NOT
;;; changed: tex-output.scm carries one default-off hook (`*tex-infix?*',
;;; `tex--infix-render') and, while the switch is off, prints exactly what it printed before.
;;;
;;; What the layer recognises (`*tex-infix-ops*'): an accessor of a declared structure,
;;; applied to a structure term S, then to its arguments.  S is read THROUGH views: a
;;; `def-functor' view `(NORMED-FIELD-AS-COMMUTATIVE-RING K)' is written K, since the view's
;;; slots are K's slots.  The subscript is S, dropped when the conventions say so.
;;;
;;;   ((ADD S) a b)    a +_S b          ((VADD S) u v)   u +_S v
;;;   ((MUL S) a b)    a \times_S b     ((OPR S) a b)    a \cdot_S b
;;;   ((ACT S) c v)    c \cdot_S v      (not associative: c(dv) keeps its parentheses)
;;;   ((NEG S) a)      -_S a            ((VNEG S) v)     -_S v
;;;   ((INV S) a)      a^{-1}_S         ((MUL-INV S) a)  a^{-1}_S
;;;   ((VMUL S) x y)   x \times_S y      ((VSTAR S) x), ((ISTAR S) x)   x^*_S
;;;   (ZERO S) 0_S   (ONE S) 1_S   (VZERO S) 0_S   (IDEN S) e_S   (VONE S) 1_S
;;;   ((FNRM S) a)     |a|_S            ((VNRM S) v), ((NRM S) v)   ||v||_S
;;;   ((IP S) u v)     <u, v>_S
;;;
;;; FAITHFUL: no rewriting.  `a + (-b)' prints `a +_S -_S b', never `a - b'; every term
;;; the plain printer would show is still there, only the notation changes.  Parentheses
;;; follow precedence (+ 10 < x, . 20 < unary - 30 < ^{-1} 40); a chain of ONE associative
;;; operation of ONE structure nested to the LEFT drops its parentheses ((a + b) + c is
;;; a + b + c); nested to the right it keeps them, so an associativity law still shows.
;;;
;;; CONVENTIONS (`*tex-infix-conventions*', a list, like a typing block):
;;;   (auto)                 drop the subscript when ONE structure is in play in the
;;;                          formula being printed and it is a VARIABLE (the default);
;;;                          its constants 0_S 1_S e_S keep theirs if a numeral occurs
;;;   (drop S ...)           drop the subscript of these structure terms
;;;   (keep)                 always write subscripts (turns `auto' off)
;;;   (symbol HEAD "tex")    write HEAD's operation with this symbol
;;; "the formula being printed" is the term given to the outermost `expr->tex' call; a
;;; display broken over rows is scanned row by row.
;;;
;;; The switch: `(tex-infix! #t)' / `(tex-infix! #f)'; `(with-tex-infix CONV THUNK)' for one
;;; printout; `(infix-tex X)' is the TeX of a formula or a theorem NAME with the layer on.

(define *tex-infix-conventions* '((auto)))

;;; --- THE TABLE (2026-11-14, the user: "make the optional layer an editable table") -------
;;;
;;; The operations, their TeX and the default conventions are DATA: notation/infix.tbl in the
;;; tree, then ~/.vnb-infix.tbl, the user's, read after it (a row there replaces the shipped row
;;; of the same head; `off HEAD' removes one).  The format is described at the head of
;;; notation/infix.tbl.  A changed file is re-read at the next printout with the layer on
;;; (`tex-infix--ensure-table!'), or at once by (tex-infix-reload!).  A reload with ANY row in
;;; error changes nothing: the errors are listed with file and line and the table in force stays.
;;;
;;; In memory an entry is (HEAD KIND TEX PREC ASSOC?), TEX a string for infix / prefix / postfix
;;; / const, (OPEN . CLOSE) for outfix, (PRE MID POST) for bracket.

(define *tex-infix-ops* '())
(define *tex-infix-macros* '())          ; ((NAME NARGS BODY) ...), NAME with its backslash
(define *tex-infix-table-stamp* '())     ; ((FILE . MTIME-OR-#F) ...) of the last good read

(define (tex-infix--shipped-file) (string-append *prover-dir* "notation/infix.tbl"))
(define *tex-infix-user-file* "~/.vnb-infix.tbl")
(define (tex-infix--files)
  (list (tex-infix--shipped-file) (->namestring (merge-pathnames *tex-infix-user-file*))))

(define (tex-infix--arity kind)
  (case kind ((infix bracket) 2) ((prefix postfix outfix) 1) ((const) 0) (else -1)))

;; the first N blank-separated fields of LINE and the rest (trimmed), or #f when fewer than N
(define (tex-infix--fields line n)
  (let ((len (string-length line)))
    (define (skip i) (if (and (< i len) (char-whitespace? (string-ref line i))) (skip (+ i 1)) i))
    (define (word i) (if (and (< i len) (not (char-whitespace? (string-ref line i)))) (word (+ i 1)) i))
    (let loop ((i (skip 0)) (k 0) (acc '()))
      (if (= k n)
          (append (reverse acc) (list (string-trim (substring line i len))))
          (let ((e (word i)))
            (if (= e i) #f (loop (skip e) (+ k 1) (cons (substring line i e) acc))))))))

;; "#1" / "#2" split of a template; #f when the placeholders are not there exactly once, in order
(define (tex-infix--split-template tex holes)
  (let* ((p1 (string-search-forward "#1" tex 0))
         (p2 (string-search-forward "#2" tex 0)))
    ;; the search from AT is done on the substring: MIT 12's string-search-forward with a
    ;; non-zero third argument raised "not in the correct range" on a string long enough
    ;; (found by the first test, 2026-11-14)
    (define (from pat at)
      (let ((k (string-search-forward pat (substring tex at (string-length tex)) 0)))
        (and k (+ at k))))
    (define (once? pat at) (and at (not (from pat (+ at 2)))))
    (case holes
      ((1) (and (once? "#1" p1) (not p2)
                (cons (substring tex 0 p1) (substring tex (+ p1 2) (string-length tex)))))
      ((2) (and (once? "#1" p1) (once? "#2" p2) (< p1 p2)
                (list (substring tex 0 p1) (substring tex (+ p1 2) p2)
                      (substring tex (+ p2 2) (string-length tex)))))
      (else #f))))

;; one line -> (op . ENTRY) | (macro . (NAME NARGS BODY)) | (off . HEAD) | (convention . C)
;;           | #f (blank or comment) | (error . MESSAGE)
(define (tex-infix--parse-line line)
  (let ((f (tex-infix--fields line 1)))
    (cond
      ((or (not f) (string-null? (car f)) (char=? (string-ref (car f) 0) #\;)) #f)
      (else
       (let ((kw (string->symbol (string-downcase (car f)))))
         (case kw
           ((infix prefix postfix const outfix bracket)
            (let ((g (tex-infix--fields line 4)))
              (if (not g)
                  (cons 'error "a row wants KIND HEAD PREC ASSOC TEX")
                  (let ((head (string->symbol (string-downcase (list-ref g 1))))
                        (prec (string->number (list-ref g 2)))
                        (assoc (list-ref g 3))
                        (tex (list-ref g 4)))
                    (cond
                      ((not (and prec (exact-nonnegative-integer? prec)))
                       (cons 'error (string-append "PREC is not a whole number: " (list-ref g 2))))
                      ((not (member assoc '("assoc" "-")))
                       (cons 'error (string-append "ASSOC must be `assoc' or `-', not " assoc)))
                      ((string-null? tex) (cons 'error "no TeX after ASSOC"))
                      (else
                       (let ((t (case kw
                                  ((outfix) (tex-infix--split-template tex 1))
                                  ((bracket) (tex-infix--split-template tex 2))
                                  (else (and (not (string-search-forward "#" tex 0)) tex)))))
                         (if (not t)
                             (cons 'error
                                   (case kw
                                     ((outfix) "an outfix TeX wants #1 exactly once: \\norm{#1}")
                                     ((bracket) "a bracket TeX wants #1 then #2, once each")
                                     (else "only outfix and bracket TeX may hold #")))
                             (cons 'op (list head kw t prec (string=? assoc "assoc")))))))))))
           ((macro)
            (let ((g (tex-infix--fields line 4)))
              (cond
                ((not g) (cons 'error "a macro row wants macro \\NAME NARGS - BODY"))
                ((not (and (> (string-length (list-ref g 1)) 1)
                           (char=? (string-ref (list-ref g 1) 0) #\\)))
                 (cons 'error (string-append "a macro name starts with a backslash: " (list-ref g 1))))
                ((not (let ((n (string->number (list-ref g 2)))) (and n (exact-nonnegative-integer? n) (<= n 9))))
                 (cons 'error (string-append "NARGS must be 0 to 9, not " (list-ref g 2))))
                ((string-null? (list-ref g 4)) (cons 'error "a macro without a body"))
                (else (cons 'macro (list (list-ref g 1) (string->number (list-ref g 2)) (list-ref g 4)))))))
           ((off)
            (let ((g (tex-infix--fields line 2)))
              (if (and g (string-null? (list-ref g 2)))
                  (cons 'off (string->symbol (string-downcase (list-ref g 1))))
                  (cons 'error "an off row is: off HEAD"))))
           ((convention)
            (let* ((rest (cadr (tex-infix--fields line 1)))
                   (words (map (lambda (w) (string->symbol (string-downcase w)))
                               (burst-string rest char-set:whitespace #t))))
              (if (and (pair? words) (memq (car words) '(auto keep drop))
                       (or (eq? (car words) 'drop) (null? (cdr words))))
                  (cons 'convention words)
                  (cons 'error "a convention row is: convention auto | keep | drop S ..."))))
           (else (cons 'error (string-append "unknown row kind: " (car f))))))))))

;; FILE -> (ITEMS . ERRORS), ITEMS in file order, each ERROR "file:line: message"
(define (tex-infix--read-file file)
  (call-with-input-file file
    (lambda (port)
      (let loop ((n 1) (items '()) (errs '()))
        (let ((line (read-line port)))
          (if (eof-object? line)
              (cons (reverse items) (reverse errs))
              (let ((r (tex-infix--parse-line line)))
                (cond ((not r) (loop (+ n 1) items errs))
                      ((eq? (car r) 'error)
                       (loop (+ n 1) items
                             (cons (string-append file ":" (number->string n) ": " (cdr r)) errs)))
                      (else (loop (+ n 1) (cons r items) errs))))))))))

(define (tex-infix--stamp)
  (map (lambda (f) (cons f (and (file-exists? f) (file-modification-time f)))) (tex-infix--files)))

;; read both files; on success install and return a one-line summary, else print the errors,
;; change nothing, return #f
(define (tex-infix-reload!)
  (let* ((files (filter file-exists? (tex-infix--files)))
         (reads (map tex-infix--read-file files))
         (errs (append-map cdr reads)))
    (cond
      ((not (member (tex-infix--shipped-file) files))
       (display ";; infix table: ") (display (tex-infix--shipped-file))
       (display " is missing; the table in force is kept") (newline) #f)
      ((pair? errs)
       (display ";; infix table NOT reloaded (the table in force is kept):") (newline)
       (for-each (lambda (e) (display ";;   ") (display e) (newline)) errs)
       #f)
      (else
       (let loop ((rs reads) (ops '()) (macs '()) (conv #f))
         (if (pair? rs)
             (let item ((xs (car (car rs))) (ops ops) (macs macs) (fconv '()))
               (if (null? xs)
                   (loop (cdr rs) ops macs (if (pair? fconv) (reverse fconv) conv))
                   (let ((x (car xs)))
                     (case (car x)
                       ((op) (item (cdr xs)
                                   (append (del-assq (car (cdr x)) ops) (list (cdr x))) macs fconv))
                       ((off) (item (cdr xs) (del-assq (cdr x) ops) macs fconv))
                       ((macro) (item (cdr xs) ops
                                      (append (filter (lambda (m) (not (string=? (car m) (car (cdr x))))) macs)
                                              (list (cdr x)))
                                      fconv))
                       ((convention) (item (cdr xs) ops macs (cons (cdr x) fconv)))
                       (else (item (cdr xs) ops macs fconv))))))
             (begin
               (set! *tex-infix-ops* ops)
               (set! *tex-infix-macros* macs)
               (set! *tex-infix-conventions* (or conv '((auto))))
               (set! *tex-infix-table-stamp* (tex-infix--stamp))
               (string-append ";; infix table: " (number->string (length ops)) " operations, "
                              (number->string (length macs)) " macros, from "
                              (apply string-append
                                     (cdr (append-map (lambda (f) (list " + " f)) files)))))))))))

;; the same, as one string (for the Emacs menu): the summary, or the errors
(define (tex-infix-reload-report)
  (let* ((r #f)
         (out (with-output-to-string (lambda () (set! r (tex-infix-reload!))))))
    (if r r out)))

;; re-read when a table file changed since the last good read (called by the switch and the
;; one-printout entries, never per term)
(define (tex-infix--ensure-table!)
  (if (not (equal? (tex-infix--stamp) *tex-infix-table-stamp*))
      (let ((r (tex-infix-reload!)))
        (if r (begin (display r) (newline)))
        ;; a failed read is not retried until a file changes again
        (if (not r) (set! *tex-infix-table-stamp* (tex-infix--stamp)))))
  *tex-infix-ops*)

;; the \providecommand lines of the table's macros, for every preamble VNB writes
(define (tex-infix-preamble-macros)
  (apply string-append
         (map (lambda (m)
                (string-append "\\providecommand{" (car m) "}"
                               (if (> (cadr m) 0) (string-append "[" (number->string (cadr m)) "]") "")
                               "{" (caddr m) "}\n"))
              *tex-infix-macros*)))

;; the shipped table is read when this file loads; an error in it stops the load
(let ((r (tex-infix-reload!)))
  (if (not r) (error "tex-infix: the shipped table notation/infix.tbl does not read")))

;; the relations a layer term may stand on either side of, with their separators
(define *tex-infix-relations* '(= < <= > >= in))

;;; --- recognising a term ------------------------------------------------

;; *view-as-table* is structures.scm's (load.scm:122, long before this file).  It is read
;; directly: the first version tested `environment-bound?' in system-global-environment, but the
;; root files load into the REPL's environment, so the test was false and no view was stripped
;; (the suite caught it, 2026-11-14; the band probe had loaded this file elsewhere).
(define (tex-infix--view? head)
  (and (symbol? head)
       (hash-table-ref/default *view-as-table* head #f)
       #t))

;; the structure term, read through views
(define (tex-infix--strip-views s)
  (if (and (pair? s) (pair? (cdr s)) (null? (cddr s)) (tex-infix--view? (car s)))
      (tex-infix--strip-views (cadr s))
      s))

;; a node: (ENTRY STRUCT ARGS) when E is an applied structure operation, else #f
(define (tex-infix--node e)
  (and (pair? e)
       (let ((h (car e)))
         (cond
           ;; ((HEAD S) a ...)
           ((and (pair? h) (symbol? (car h)) (pair? (cdr h)) (null? (cddr h))
                 (assq (car h) *tex-infix-ops*))
            => (lambda (ent)
                 (and (= (length (cdr e)) (tex-infix--arity (cadr ent)))
                      (list ent (tex-infix--strip-views (cadr h)) (cdr e)))))
           ;; (CONST S)
           ((and (symbol? h) (pair? (cdr e)) (null? (cddr e))
                 (assq h *tex-infix-ops*))
            => (lambda (ent)
                 (and (eq? (cadr ent) 'const)
                      (list ent (tex-infix--strip-views (cadr e)) '()))))
           (else #f)))))

(define (tex-infix--node-prec n) (cadddr (car n)))

;; every structure term the layer would subscript, in E
(define (tex-infix--structures e)
  (let walk ((e e) (acc '()))
    (cond ((not (pair? e)) acc)
          (else
           (let* ((n (tex-infix--node e))
                  (acc (if (and n (not (member (cadr n) acc))) (cons (cadr n) acc) acc)))
             (let loop ((xs (if n (caddr n) e)) (acc acc))
               (if (pair? xs) (loop (cdr xs) (walk (car xs) acc)) acc)))))))

;;; --- conventions --------------------------------------------------------

(define (tex-infix--conv key)
  (let loop ((cs *tex-infix-conventions*) (acc '()))
    (cond ((null? cs) (reverse acc))
          ((and (pair? (car cs)) (eq? (caar cs) key)) (loop (cdr cs) (cons (car cs) acc)))
          (else (loop (cdr cs) acc)))))

(define *tex-infix-scope-drop* 'unset)   ; the structures whose subscript is dropped, this formula

;; `auto' drops the subscript of the ONE structure in play only when it is a VARIABLE (a
;; symbol that is not a registered constant): `zero(zz-ring) = 0' must not read `0 = 0'.
;; And when the formula holds a numeral, the CONSTANTS (0_S, 1_S, e_S) keep their subscript
;; even under `auto', so 0_K never reads as the number 0; an explicit (drop S) drops all.
(define *tex-infix-scope-auto* '())      ; the structures dropped by `auto', this formula
(define *tex-infix-scope-numeral?* #f)   ; does this formula hold a numeral?

(define (tex-infix--variable-structure? s)
  (and (symbol? s) (not (hash-table-ref/default *constant-registry* s #f))))

(define (tex-infix--has-numeral? e)
  (cond ((number? e) #t)
        ((pair? e) (or (tex-infix--has-numeral? (car e)) (tex-infix--has-numeral? (cdr e))))
        (else #f)))

(define (tex-infix--scope-for e)
  (let ((auto? (and (pair? (tex-infix--conv 'auto)) (null? (tex-infix--conv 'keep)))))
    (if auto?
        (let ((ss (tex-infix--structures e)))
          (if (and (pair? ss) (null? (cdr ss)) (tex-infix--variable-structure? (car ss)))
              (list (car ss))
              '()))
        '())))

(define (tex-infix--sub s #!optional const?)
  (if (or (member s *tex-infix-scope-drop*)
          (and (member s *tex-infix-scope-auto*)
               (not (and (not (default-object? const?)) const? *tex-infix-scope-numeral?*))))
      ""
      (string-append "_{" (fluid-let ((*tex-infix-bare?* #t)) (expr->tex s)) "}")))

(define (tex-infix--symbol ent)
  (let ((over (assq (car ent) (map cdr (tex-infix--conv 'symbol)))))
    (if over (cadr over) (caddr ent))))

;;; --- rendering ----------------------------------------------------------

;; a child in a position that needs precedence MIN; SAME is the parent when the child may
;; flatten into it (same associative head, same structure)
(define (tex-infix--child c min parent)
  (let ((n (tex-infix--node c)))
    (cond
      ((not n)
       ;; a term of the plain printer: its own infix forms carry their own parentheses;
       ;; a bare unary minus binds like a prefix operation
       (let ((s (fluid-let ((*tex-infix-bare?* #f)) (expr->tex c))))
         (if (and (pair? c) (eq? (car c) '-) (= (length c) 2) (> min 30))
             (string-append "(" s ")")
             s)))
      ((and parent (eq? (car (car n)) (car (car parent))) (equal? (cadr n) (cadr parent))
            (eq? (cadr (car n)) 'infix) (pair? (cddddr (car n))) (car (cddddr (car n))))
       (tex-infix--show n #t))
      ((>= (tex-infix--node-prec n) min) (tex-infix--show n #t))
      (else (string-append "(" (tex-infix--show n #t) ")")))))

;; N rendered; BARE says whether it needs no parentheses of its own
(define (tex-infix--show n bare)
  (let* ((ent (car n)) (kind (cadr ent)) (prec (cadddr ent)) (args (caddr n))
         (sub (tex-infix--sub (cadr n) (eq? kind 'const))) (sym (tex-infix--symbol ent)))
    (case kind
      ((infix)
       ;; an operand of equal precedence keeps its parentheses unless it FLATTENS: the LEFT
       ;; operand, same associative head, same structure -- (a + b) + c is a + b + c, read
       ;; left to right, while a + (b + c) keeps its parentheses, so associativity itself
       ;; still reads as a law (the first probe printed `a . b . c = a . b . c')
       (let* ((assoc? (and (pair? (cddddr ent)) (car (cddddr ent))))
              (min (+ prec 1))
              (par (and assoc? n))
              (s (string-append (tex-infix--child (car args) min par)
                                " " sym sub " "
                                (tex-infix--child (cadr args) min #f))))
         (if bare s (string-append "(" s ")"))))
      ((prefix)
       (string-append sym sub " " (tex-infix--child (car args) prec #f)))
      ((postfix)
       ;; the operand in braces: a subscripted operand (e_g) would otherwise give the
       ;; double subscript e_g^{-1}_g
       (string-append "{" (tex-infix--child (car args) (+ prec 1) #f) "}" sym sub))
      ((const) (string-append sym sub))
      ((outfix)
       (string-append (car sym) (tex-infix--child (car args) 0 #f) (cdr sym) sub))
      ((bracket)
       (string-append (car sym) (tex-infix--child (car args) 0 #f) (cadr sym)
                      (tex-infix--child (cadr args) 0 #f) (caddr sym) sub))
      (else (error "tex-infix: unknown kind" kind)))))

;; a relation with a layer term on a side: the sides need no parentheses
(define (tex-infix--relation e bare)
  (and (pair? e) (memq (car e) *tex-infix-relations*) (= (length e) 3)
       (or (tex-infix--node (cadr e)) (tex-infix--node (caddr e)))
       (let ((s (string-append (tex-infix--child (cadr e) 0 #f)
                               (cdr (assq (car e) *tex-binop-table*))
                               (tex-infix--child (caddr e) 0 #f))))
         (if bare s (string-append "(" s ")")))))

(define (tex-infix--render e0 plain)
  (define (go bare)
    (let ((n (tex-infix--node e0)))
      (cond (n (tex-infix--show n (or bare (>= (tex-infix--node-prec n) 30))))
            ((tex-infix--relation e0 bare) => (lambda (s) s))
            (else (plain e0)))))
  (let ((bare *tex-infix-bare?*))
    (fluid-let ((*tex-infix-bare?* #f))
      (if (eq? *tex-infix-scope-drop* 'unset)
          ;; the outermost call: the formula being printed; fix its conventions
          (fluid-let ((*tex-infix-scope-drop* (apply append (map cdr (tex-infix--conv 'drop))))
                      (*tex-infix-scope-auto* (tex-infix--scope-for e0))
                      (*tex-infix-scope-numeral?* (tex-infix--has-numeral? e0)))
            (go #t))
          (go bare)))))

(set! tex--infix-render tex-infix--render)
(set! tex--preamble-macros tex-infix-preamble-macros)

;;; --- the switch -----------------------------------------------------------

(define (tex-infix! on?)
  (if on? (tex-infix--ensure-table!))
  (set! *tex-infix?* (and on? #t))
  *tex-infix?*)

(define (tex-infix-conventions! conv)
  (set! *tex-infix-conventions* conv)
  conv)

(define (with-tex-infix conv thunk)
  (tex-infix--ensure-table!)
  (fluid-let ((*tex-infix?* #t)
              (*tex-infix-conventions* (if (default-object? conv) *tex-infix-conventions* conv)))
    (thunk)))

;; the TeX of a formula (S-expression or wff) or of a theorem NAME, with the layer on
(define (infix-tex x)
  (let* ((f (if (symbol? x) (lookup-theorem x) x))
         (f (if (wff? f) (wff-formula f) f)))
    (with-tex-infix *tex-infix-conventions* (lambda () (expr->tex-top f)))))
