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

;; (HEAD KIND TEX PREC [ASSOC?])  -- KIND: infix prefix postfix const circ bracket
(define *tex-infix-ops*
  '((add      infix   "+"        10 #t)
    (vadd     infix   "+"        10 #t)
    (mul      infix   "\\times"  20 #t)
    (opr      infix   "\\cdot"   20 #t)
    (vmul     infix   "\\times"  20 #t)
    (act      infix   "\\cdot"   20 #f)
    (neg      prefix  "-"        30)
    (vneg     prefix  "-"        30)
    (inv      postfix "^{-1}"    40)
    (mul-inv  postfix "^{-1}"    40)
    (vstar    postfix "^{*}"     40)
    (istar    postfix "^{*}"     40)
    (zero     const   "0"       100)
    (one      const   "1"       100)
    (vzero    const   "0"       100)
    (iden     const   "e"       100)
    (vone     const   "1"       100)
    (fnrm     circ    ("\\lvert " . " \\rvert")   100)
    ;; a norm is OUTFIX, through the macro \norm{.} = \left\lVert #1 \right\rVert (the user,
    ;; 2026-11-14); every preamble VNB writes carries it as a \providecommand
    (vnrm     circ    ("\\norm{" . "}")   100)
    (nrm      circ    ("\\norm{" . "}")   100)
    (ip       bracket ("\\langle " . " \\rangle") 100)))

(define (tex-infix--arity kind)
  (case kind ((infix bracket) 2) ((prefix postfix circ) 1) ((const) 0) (else -1)))

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
      ((circ)
       (string-append (car sym) (tex-infix--child (car args) 0 #f) (cdr sym) sub))
      ((bracket)
       (string-append (car sym) (tex-infix--child (car args) 0 #f) ", "
                      (tex-infix--child (cadr args) 0 #f) (cdr sym) sub))
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

;;; --- the switch -----------------------------------------------------------

(define (tex-infix! on?)
  (set! *tex-infix?* (and on? #t))
  *tex-infix?*)

(define (tex-infix-conventions! conv)
  (set! *tex-infix-conventions* conv)
  conv)

(define (with-tex-infix conv thunk)
  (fluid-let ((*tex-infix?* #t)
              (*tex-infix-conventions* (if (default-object? conv) *tex-infix-conventions* conv)))
    (thunk)))

;; the TeX of a formula (S-expression or wff) or of a theorem NAME, with the layer on
(define (infix-tex x)
  (let* ((f (if (symbol? x) (lookup-theorem x) x))
         (f (if (wff? f) (wff-formula f) f)))
    (with-tex-infix *tex-infix-conventions* (lambda () (expr->tex-top f)))))
