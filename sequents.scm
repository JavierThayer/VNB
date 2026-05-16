;;; sequents.scm -- sequents over <wff> objects
;;;
;;; A SEQUENT is a pair (assumptions . assertion) where
;;;   assumptions  is a list of <wff>  (the hypotheses)
;;;   assertion    is a <wff>          (the goal)
;;;
;;; Written as:  A1 ... An => B
;;;
;;; All formula-level operations (subst, alpha-equiv, etc.) work on raw
;;; S-expressions extracted via wff-formula.  The context operations here
;;; compare wff objects by theory name + alpha-equivalence.

;;; -----------------------------------------------------------------------
;;; Sequents

(define-record-type <sequent>
  (make-sequent assumptions assertion)
  sequent?
  (assumptions sequent-assumptions)
  (assertion   sequent-assertion))

(define (sequent->string s)
  (let ((asms (sequent-assumptions s))
        (goal (sequent-assertion s)))
    (string-append
     (if (null? asms)
         "()"
         (let loop ((fs asms) (acc ""))
           (if (null? fs)
               (substring acc 0 (- (string-length acc) 2))
               (loop (cdr fs)
                     (string-append acc (wff->string (car fs)) ", ")))))
     "  =>  "
     (wff->string goal))))

;;; -----------------------------------------------------------------------
;;; Context operations on lists of <wff>

(define (context-contains? asms formula-wff)
  (any (lambda (a) (wff-equiv? a formula-wff)) asms))

(define (context-add-assumption asms formula-wff)
  (if (context-contains? asms formula-wff)
      asms
      (cons formula-wff asms)))

(define (context-remove-assumption asms formula-wff)
  (filter (lambda (a) (not (wff-equiv? a formula-wff))) asms))

(define (context-union asms1 asms2)
  (fold-left context-add-assumption asms1 asms2))

;;; -----------------------------------------------------------------------
;;; Printing helpers
;;;
;;; Printing rules:
;;;   forall/forsome  ->  forall([x, y in A, z], body)  with binding detection
;;;   (LIST a b c)    ->  [a, b, c]
;;;   and or iff      ->  n-ary infix, precedence-based parens
;;;   implies         ->  right-assoc infix
;;;   in = == <=      ->  binary infix (comparison)
;;;   + *             ->  n-ary infix
;;;   - (binary)      ->  left-assoc infix
;;;   - (unary)       ->  prefix, tight
;;;   power ^         ->  right-assoc infix, tight
;;;   not(P) and everything else -> f(x, y, z) functional notation
;;;
;;; Parentheses are added only when needed by precedence:
;;;   implies=0  iff=1  or=2  and=3  cmp=4  +/-=5  */recip=6  ^/unary=7
;;;   Quantifiers and function calls are self-delimiting (no extra parens).

;;; Join strings with a separator.
(define (str-join strs sep)
  (if (null? strs)
      ""
      (let loop ((rest (cdr strs)) (acc (car strs)))
        (if (null? rest)
            acc
            (loop (cdr rest) (string-append acc sep (car rest)))))))

;;; Precedence of compound expressions.  Atoms and self-delimiting forms
;;; return 9 (highest — never need outer parens).
(define (op-prec head)
  (cond
    ((eq?  head 'implies)           0)
    ((eq?  head 'iff)               1)
    ((eq?  head 'or)                2)
    ((eq?  head 'and)               3)
    ((memq head '(in = == <=))      4)
    ((memq head '(+ -))             5)
    ((memq head '(* recip))         6)
    ((memq head '(power))           7)
    (else                           9)))

;;; Wrap s in parens when this expression's precedence is below min-prec.
(define (paren-if s this-prec min-prec)
  (if (< this-prec min-prec)
      (string-append "(" s ")")
      s))

;;; Quantifier binding detection (unchanged logic, forward-declared below).
(define (forall-detect-binding x body)
  (if (and (pair? body) (eq? (car body) 'implies)
           (= (length body) 3)
           (pair? (cadr body)) (eq? (car (cadr body)) 'in)
           (= (length (cadr body)) 3)
           (eq? (cadr (cadr body)) x))
      (cons (list 'in x (caddr (cadr body))) (caddr body))
      (cons (list x) body)))

(define (forsome-detect-binding x body)
  (if (and (pair? body) (eq? (car body) 'and)
           (= (length body) 3)
           (pair? (cadr body)) (eq? (car (cadr body)) 'in)
           (= (length (cadr body)) 3)
           (eq? (cadr (cadr body)) x))
      (cons (list 'in x (caddr (cadr body))) (caddr body))
      (cons (list x) body)))

(define (collect-quant-bindings q e)
  (let loop ((cur e) (bindings '()))
    (if (and (pair? cur) (eq? (car cur) q)
             (= (length cur) 3) (symbol? (cadr cur)))
        (let* ((x         (cadr cur))
               (body      (caddr cur))
               (p         (if (eq? q 'forall)
                              (forall-detect-binding x body)
                              (forsome-detect-binding x body)))
               (binding   (car p))
               (remaining (cdr p)))
          (loop remaining (cons binding bindings)))
        (cons (reverse bindings) cur))))

;;; Internal precedence-aware printer.
;;; min-prec: the minimum precedence this expression must have to avoid
;;; being wrapped in an extra pair of parens by the caller.
(define (expr->str e min-prec)
  (cond
    ((symbol? e) (symbol->string e))
    ((number? e) (with-output-to-string (lambda () (write e))))
    ;; Functoid record: lambda([x in A, y in B], body)
    ((functoid? e)
     (let* ((bindings (functoid-bindings e))
            (bstrs    (map (lambda (b)
                             (string-append (symbol->string (car b))
                                            " in "
                                            (expr->str (cdr b) 0)))
                           bindings))
            (kind-str (symbol->string (functoid-kind e))))
       (string-append kind-str "([" (str-join bstrs ", ") "], "
                      (expr->str (functoid-body e) 0) ")")))
    ((pair? e)
     (let ((head (car e))
           (args (cdr e)))
       (cond
         ;; Quantifiers: forall([x, y in A], body) — self-delimiting
         ((and (memq head '(forall forsome))
               (= (length e) 3) (symbol? (cadr e)))
          (let* ((result   (collect-quant-bindings head e))
                 (bindings (car result))
                 (body     (cdr result)))
            (string-append (symbol->string head)
                           "([" (print-binding-list bindings) "], "
                           (expr->str body 0) ")")))
         ;; (LIST a b c) -> [a, b, c] — self-delimiting
         ((eq? head 'list)
          (string-append "[" (str-join (map (lambda (a) (expr->str a 0)) args) ", ") "]"))
         ;; N-ary: and or iff + *  (associative; each arg at same prec)
         ((and (memq head '(and or iff + *)) (>= (length e) 3))
          (let* ((p   (op-prec head))
                 (sep (string-append " " (symbol->string head) " "))
                 (s   (str-join (map (lambda (a) (expr->str a p)) args) sep)))
            (paren-if s p min-prec)))
         ;; implies: right-associative; left arg needs p+1, right needs p
         ((and (eq? head 'implies) (= (length e) 3))
          (let* ((p 0)
                 (s (string-append (expr->str (cadr e) (+ p 1))
                                   " implies "
                                   (expr->str (caddr e) p))))
            (paren-if s p min-prec)))
         ;; Binary comparison: in subset = == <=  (non-associative; both args at p)
         ((and (memq head '(in subset SUBSET = == <=)) (= (length e) 3))
          (let* ((p (op-prec head))
                 (s (string-append (expr->str (cadr e) p)
                                   " " (symbol->string head) " "
                                   (expr->str (caddr e) p))))
            (paren-if s p min-prec)))
         ;; Binary -: left-associative; left at p, right at p+1
         ((and (eq? head '-) (= (length e) 3))
          (let* ((p 5)
                 (s (string-append (expr->str (cadr e) p)
                                   " - "
                                   (expr->str (caddr e) (+ p 1)))))
            (paren-if s p min-prec)))
         ;; Unary -: tight prefix
         ((and (eq? head '-) (= (length e) 2))
          (let* ((p 7)
                 (s (string-append "-" (expr->str (cadr e) p))))
            (paren-if s p min-prec)))
         ;; power: right-associative; left at p+1, right at p
         ((and (eq? head 'power) (= (length e) 3))
          (let* ((p 7)
                 (s (string-append (expr->str (cadr e) (+ p 1))
                                   " ^ "
                                   (expr->str (caddr e) p))))
            (paren-if s p min-prec)))
         ;; (MAKE-SET (list a b c)) -> {a, b, c}
         ((and (eq? head 'MAKE-SET) (= (length e) 2)
               (pair? (cadr e)) (eq? (car (cadr e)) 'list))
          (let ((elems (cdr (cadr e))))
            (string-append "{"
                           (str-join (map (lambda (a) (expr->str a 0)) elems) ", ")
                           "}")))
         ;; (PAIR a a) -> {a}  /  (PAIR a b) -> {a, b}
         ((and (eq? head 'PAIR) (= (length e) 3))
          (if (equal? (cadr e) (caddr e))
              (string-append "{" (expr->str (cadr e) 0) "}")
              (string-append "{" (expr->str (cadr e) 0) ", " (expr->str (caddr e) 0) "}")))
         ;; (SEP x A p) -> {x in A: p}
         ((and (eq? head 'SEP) (= (length e) 4))
          (string-append "{" (symbol->string (cadr e))
                         " in " (expr->str (caddr e) 0)
                         ": " (expr->str (cadddr e) 0) "}"))
         ;; (COMP x p) -> {x | p}
         ((and (eq? head 'COMP) (= (length e) 3))
          (string-append "{" (symbol->string (cadr e))
                         " | " (expr->str (caddr e) 0) "}"))
         ;; (apply-functoid <ftd> arg ...) -> lambda([...], body)(arg, ...)
         ((eq? head 'apply-functoid)
          (string-append (expr->str (car args) 0)
                         "("
                         (str-join (map (lambda (a) (expr->str a 0)) (cdr args)) ", ")
                         ")"))
         ;; Compound head: ((f x) a b) -> (f(x))(a, b) — self-delimiting
         ((pair? head)
          (let ((head-str (string-append "(" (expr->str head 0) ")")))
            (if (null? args)
                head-str
                (string-append head-str
                               "("
                               (str-join (map (lambda (a) (expr->str a 0)) args) ", ")
                               ")"))))
         ;; Everything else: f(x, y, z) — self-delimiting
         (else
          (if (null? args)
              (symbol->string head)
              (string-append (symbol->string head)
                             "("
                             (str-join (map (lambda (a) (expr->str a 0)) args) ", ")
                             ")"))))))
    (else (with-output-to-string (lambda () (write e))))))

(define (print-binding spec)
  (cond
    ;; (var) or (var1 var2 ...) — unrestricted, all symbols
    ((and (pair? spec) (not (null? spec))
          (all-symbols? spec) (not (eq? (car spec) 'in)))
     (str-join (map symbol->string spec) ", "))
    ;; (in var A)
    ((and (pair? spec) (= (length spec) 3)
          (eq? (car spec) 'in) (symbol? (cadr spec)))
     (string-append (symbol->string (cadr spec))
                    " in "
                    (expr->str (caddr spec) 0)))
    (else (expr->str spec 0))))

(define (print-binding-list specs)
  (str-join (map print-binding specs) ", "))

;;; Public interface: expression->string prints at top-level (no outer parens).
(define (expression->string e) (expr->str e 0))

;;; wff->string: format a wff as a quoted formula string.
;;; The double-quote delimiters signal "this is a formula, not Scheme code."
(define (wff->string w)
  (string-append "\"" (expr->str (wff-formula w) 0) "\""))

;;; Install custom REPL printers.
;;; simple-unparser-method calls write on each list element, so a plain string
;;; gets the "..." delimiters for free — signalling "formula text, not Scheme data".
(set-record-type-unparser-method! <wff>
  (simple-unparser-method 'wff
    (lambda (w) (list (expression->string (wff-formula w))))))

(set-record-type-unparser-method! <sequent>
  (simple-unparser-method 'sequent
    (lambda (s)
      (list (string-append
             (if (null? (sequent-assumptions s))
                 "()"
                 (str-join (map (lambda (a) (expression->string (wff-formula a)))
                                (sequent-assumptions s))
                           ", "))
             "  =>  "
             (expression->string (wff-formula (sequent-assertion s))))))))

(define (any pred lst)
  (cond ((null? lst) #f)
        ((pred (car lst)) #t)
        (else (any pred (cdr lst)))))

(define (fold-left f init lst)
  (if (null? lst)
      init
      (fold-left f (f init (car lst)) (cdr lst))))
