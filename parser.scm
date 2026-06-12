;;; parser.scm — VNB string expression parser
;;;
;;; String syntax (precedence low to high):
;;;   implies   A implies B                      (IMPLIES A B)    binary, right-assoc
;;;   iff       A iff B iff C                    (IFF A (IFF B C)) binary, right-assoc
;;;   or        A or B or C                      (OR A (OR B C))   binary, right-assoc
;;;   and       A and B and C                    (AND A (AND B C)) binary, right-assoc
;;;   cmp       x in A,  x=y,  x==y,  x<=y      binary
;;;   add       x + y + z,  x - y               (+ x y z) n-ary / (- x y) binary
;;;   mul       x * y * z,  x / y               (* x y z) n-ary / (* x (recip y))
;;;   pow       x ^ y                            (power x y) binary right-assoc
;;;   unary     -x                               (- x)
;;;   primary   atom  f(a,b,c)  [a,b,c]  (expr)
;;;             {a,b,c}                          (MAKE-SET [a,b,c]) sugar
;;;             {x in A: p}                      (SEP x A p)
;;;             set_of(a,b,c)                    same expansion as {a,b,c}
;;;             not(P)                           (NOT P)   via funsym
;;;             forall([bindings], body)         (FORALL (bindings) body)
;;;             forsome([bindings], body)        (FORSOME (bindings) body)
;;;
;;; Binding forms inside forall/forsome([...], ...):
;;;   x              ->  (x)                  unrestricted
;;;   x in A         ->  (IN x A)             restricted
;;;   [a,b,c] in A   ->  (IN (LIST a b c) A)  tuple destructuring
;;;
;;; All identifiers are case-folded to lowercase (MIT Scheme convention).

;;; -----------------------------------------------------------------------
;;; Tokenizer

(define (vnb-tokenize str)
  (let* ((vec (list->vector (string->list str)))
         (len (vector-length vec))
         (pos 0))

    (define (peek-ch) (if (< pos len) (vector-ref vec pos) #f))
    (define (adv-ch)  (let ((c (peek-ch))) (set! pos (+ pos 1)) c))

    (define (skip-ws)
      (let lp ()
        (let ((c (peek-ch)))
          (when (and c (char-whitespace? c)) (adv-ch) (lp)))))

    (define (ident-cont? c)
      (and c (or (char-alphabetic? c) (char-numeric? c)
                 (char=? c #\-) (char=? c #\_) (char=? c #\?))))

    (define (op-ch? c)
      (and c (memv c '(#\+ #\- #\* #\/ #\^ #\< #\= #\!))))

    (define (read-ident first-ch)
      (let lp ((acc (list first-ch)))
        (if (ident-cont? (peek-ch))
            (lp (cons (adv-ch) acc))
            (let ((sym (string->symbol
                        (string-downcase (list->string (reverse acc))))))
              (if (eqv? (peek-ch) #\()
                  (cons 'funsym sym)
                  (cons 'sym    sym))))))

    (define (read-op first-ch)
      (let lp ((acc (list first-ch)))
        (if (op-ch? (peek-ch))
            (lp (cons (adv-ch) acc))
            (cons 'sym (string->symbol (list->string (reverse acc)))))))

    (define (read-num first-ch)
      ;; Read digits/decimal, then try to extend to a complex literal.
      ;; Handles: 3i, 2+3i, 2-3i, 1.5+2.3i, 0+i (pure imaginary), etc.
      ;; +/- that is not part of a complex literal is left for the operator tokenizer.
      (let lp ((acc (list first-ch)))
        (let ((c (peek-ch)))
          (if (and c (or (char-numeric? c) (char=? c #\.)))
              (lp (cons (adv-ch) acc))
              (let* ((base-str (list->string (reverse acc)))
                     (saved    pos)
                     ;; Try optional sign (+/-)
                     (sign     (and c (or (char=? c #\+) (char=? c #\-)) (adv-ch)))
                     ;; Try imaginary digits (may be empty: 2+i, 0+i)
                     (imag     (let rd ((ia '()))
                                 (let ((ic (peek-ch)))
                                   (if (and ic (or (char-numeric? ic) (char=? ic #\.)))
                                       (rd (cons (adv-ch) ia))
                                       (reverse ia)))))
                     (next     (peek-ch)))
                ;; Success when next char is 'i' not followed by ident-cont
                (if (and next (char=? next #\i))
                    (begin
                      (adv-ch)
                      (if (ident-cont? (peek-ch))
                          ;; 'i' continues an identifier -- back out entirely
                          (begin (set! pos saved) (cons 'num (string->number base-str)))
                          ;; Build complex string and parse.
                          ;; R7RS grammar has no bare "3i"; pure imaginary needs "+3i".
                          (let* ((imag-str (list->string imag))
                                 (full (if sign
                                           (string-append base-str (string sign) imag-str "i")
                                           (string-append "+" base-str imag-str "i")))
                                 (n    (string->number full)))
                            (if n
                                (cons 'num n)
                                (begin (set! pos saved)
                                       (cons 'num (string->number base-str)))))))
                    ;; No 'i' found -- restore and return plain number
                    (begin (set! pos saved)
                           (cons 'num (string->number base-str)))))))))

    (let collect ()
      (skip-ws)
      (let ((c (peek-ch)))
        (if (not c)
            '()
            (cond
              ((char=? c #\() (adv-ch) (let ((r (collect))) (cons 'lparen   r)))
              ((char=? c #\)) (adv-ch) (let ((r (collect))) (cons 'rparen   r)))
              ((char=? c #\[) (adv-ch) (let ((r (collect))) (cons 'lbracket r)))
              ((char=? c #\]) (adv-ch) (let ((r (collect))) (cons 'rbracket r)))
              ((char=? c #\{) (adv-ch) (let ((r (collect))) (cons 'lbrace   r)))
              ((char=? c #\}) (adv-ch) (let ((r (collect))) (cons 'rbrace   r)))
              ((char=? c #\:) (adv-ch) (let ((r (collect))) (cons 'colon    r)))
              ((char=? c #\|) (adv-ch) (let ((r (collect))) (cons 'pipe     r)))
              ((char=? c #\,) (adv-ch) (let ((r (collect))) (cons 'comma    r)))
              ((char-alphabetic? c)
               (adv-ch)
               (let* ((tok (read-ident c)) (rest (collect))) (cons tok rest)))
              ((op-ch? c)
               (adv-ch)
               (let* ((tok (read-op c))    (rest (collect))) (cons tok rest)))
              ((char-numeric? c)
               (adv-ch)
               (let* ((tok (read-num c))   (rest (collect))) (cons tok rest)))
              ((char=? c #\%)
               ;; %i -> exact imaginary unit (+i)
               ;; %pi, %e -> formal constant symbols (not floats)
               (adv-ch)
               (let lp ((acc '()))
                 (if (ident-cont? (peek-ch))
                     (lp (cons (adv-ch) acc))
                     (let* ((name (list->string (reverse acc)))
                            (rest (collect)))
                       (cond
                         ((string=? name "i")
                          (cons (cons 'num +i) rest))
                         ((string=? name "pi")
                          (cons (cons 'sym 'pi) rest))
                         ((string=? name "e")
                          (cons (cons 'sym 'e) rest))
                         (else (error "vnb-tokenize: unknown %constant"
                                      name "in" str)))))))
              (else (error "vnb-tokenize: unexpected character"
                           (string c) "in" str))))))))

;;; -----------------------------------------------------------------------
;;; Parser state (module-level to avoid deeply-nested closures)

(define *p-toks* '#())
(define *p-pos*   0)

(define (p-peek)
  (if (< *p-pos* (vector-length *p-toks*))
      (vector-ref *p-toks* *p-pos*)
      'eof))

(define (p-adv)
  (let ((t (p-peek)))
    (set! *p-pos* (+ *p-pos* 1))
    t))

(define (p-expect! tok)
  (let ((t (p-adv)))
    (unless (equal? t tok)
      (error "vnb-parse: expected" tok "got" t))))

(define (p-peek-sym? s)
  (let ((t (p-peek)))
    (and (pair? t) (eq? (car t) 'sym) (eq? (cdr t) s))))

;;; -----------------------------------------------------------------------
;;; Parse functions (top-level, share state via *p-toks* / *p-pos*)

;; IMPLIES — binary, right-associative (lowest precedence)
(define (p-parse-implies)
  (let ((left (p-parse-iff)))
    (if (p-peek-sym? 'implies)
        (begin (p-adv) (list 'implies left (p-parse-implies)))
        left)))

;; IFF — binary, right-associative.  Surface `a iff b iff c' folds to the
;; binary right-nested (iff a (iff b c)), the one conjunction/biconditional
;; shape the validator (make-wff) and the whole theorem corpus speak.  (The
;; parser used to build a flat n-ary node here, but make-wff rejects n-ary
;; IFF/OR/AND on arity, so n-ary was dead on arrival -- a surface `a and b and
;; c' could not be constructed at all.  Right-fold matches implies and makes a
;; typed chain indistinguishable from a hand-written nested one.)
(define (p-parse-iff)
  (let ((left (p-parse-or)))
    (if (p-peek-sym? 'iff)
        (begin (p-adv) (list 'iff left (p-parse-iff)))
        left)))

;; OR — binary, right-associative (see p-parse-iff).
(define (p-parse-or)
  (let ((left (p-parse-and)))
    (if (p-peek-sym? 'or)
        (begin (p-adv) (list 'or left (p-parse-or)))
        left)))

;; AND — binary, right-associative (see p-parse-iff).
(define (p-parse-and)
  (let ((left (p-parse-cmp)))
    (if (p-peek-sym? 'and)
        (begin (p-adv) (list 'and left (p-parse-and)))
        left)))

;; CMP — binary: in subset = == <=
(define (p-parse-cmp)
  (let ((left (p-parse-add)))
    (let ((t (p-peek)))
      (if (and (pair? t) (eq? (car t) 'sym)
               (memq (cdr t) '(in subset = == <=)))
          (let* ((op    (cdr (p-adv)))
                 (right (p-parse-add)))
            (list op left right))
          left))))

;; ADD — n-ary +, binary -
(define (p-parse-add)
  (let loop ((left (p-parse-mul)))
    (let ((t (p-peek)))
      (cond
        ((and (pair? t) (eq? (car t) 'sym) (eq? (cdr t) '+))
         (p-adv)
         (let* ((right (p-parse-mul))
                (node  (if (and (pair? left) (eq? (car left) '+))
                           (append left (list right))
                           (list '+ left right))))
           (loop node)))
        ((and (pair? t) (eq? (car t) 'sym) (eq? (cdr t) '-))
         (p-adv)
         (let* ((right (p-parse-mul)))
           (loop (list '- left right))))
        (else left)))))

;; MUL — n-ary *, division sugar x/y -> (* x (recip y))
(define (p-parse-mul)
  (let loop ((left (p-parse-unary)))
    (let ((t (p-peek)))
      (cond
        ((and (pair? t) (eq? (car t) 'sym) (eq? (cdr t) '*))
         (p-adv)
         (let* ((right (p-parse-unary))
                (node  (if (and (pair? left) (eq? (car left) '*))
                           (append left (list right))
                           (list '* left right))))
           (loop node)))
        ((and (pair? t) (eq? (car t) 'sym) (eq? (cdr t) '/))
         (p-adv)
         (let* ((right (p-parse-unary)))
           (loop (list '* left (list 'recip right)))))
        (else left)))))

;; UNARY — prefix -  (lower precedence than pow: -x^2 = -(x^2))
(define (p-parse-unary)
  (if (p-peek-sym? '-)
      (begin (p-adv) (list '- (p-parse-unary)))
      (p-parse-pow)))

;; POW — binary ^, right-associative
(define (p-parse-pow)
  (let ((base (p-parse-primary)))
    (if (p-peek-sym? '^)
        (begin (p-adv) (list 'power base (p-parse-pow)))
        base)))

;; ARGLIST — comma-separated expressions for f(...)
(define (p-parse-arglist)
  (if (eq? (p-peek) 'rparen)
      '()
      (let* ((first (p-parse-implies))
             (rest  (let lp ()
                      (if (eq? (p-peek) 'comma)
                          (begin (p-adv)
                                 (let* ((e (p-parse-implies)) (more (lp)))
                                   (cons e more)))
                          '()))))
        (cons first rest))))

;; BRACKET-LIST — [a,b,c] -> (LIST a b c); already consumed [
(define (p-parse-bracket-list)
  (if (eq? (p-peek) 'rbracket)
      (begin (p-adv) (list 'list))
      (let* ((first (p-parse-implies))
             (rest  (let lp ()
                      (cond
                        ((eq? (p-peek) 'rbracket) (p-adv) '())
                        ((eq? (p-peek) 'comma)
                         (p-adv)
                         (let* ((e (p-parse-implies)) (more (lp)))
                           (cons e more)))
                        (else (error "vnb-parse: expected ] or , in list"
                                     (p-peek)))))))
        (cons 'list (cons first rest)))))

;; SYM-LIST — comma-separated symbols inside [...]; consumes closing ]
(define (p-parse-sym-list)
  (if (eq? (p-peek) 'rbracket)
      (begin (p-adv) '())
      (let* ((first (if (and (pair? (p-peek)) (eq? (car (p-peek)) 'sym))
                        (cdr (p-adv))
                        (error "vnb-parse: expected symbol in tuple binding, got"
                               (p-peek))))
             (rest  (let lp ()
                      (cond
                        ((eq? (p-peek) 'rbracket) (p-adv) '())
                        ((eq? (p-peek) 'comma)
                         (p-adv)
                         (let* ((s    (if (and (pair? (p-peek))
                                               (eq? (car (p-peek)) 'sym))
                                         (cdr (p-adv))
                                         (error "vnb-parse: expected symbol"
                                                (p-peek))))
                                (more (lp)))
                           (cons s more)))
                        (else (error "vnb-parse: expected ] or , in tuple"
                                     (p-peek)))))))
        (cons first rest))))

;; ONE BINDING — x | x in A | [syms] in A
(define (p-parse-one-binding)
  (cond
    ((eq? (p-peek) 'lbracket)
     (p-adv)
     (let* ((syms (p-parse-sym-list)))
       (unless (p-peek-sym? 'in)
         (error "vnb-parse: expected 'in' after tuple binding, got" (p-peek)))
       (p-adv)
       (let* ((class (p-parse-implies)))
         (list 'in (cons 'list syms) class))))
    ((and (pair? (p-peek)) (eq? (car (p-peek)) 'sym))
     (let* ((sym (cdr (p-adv))))
       (if (p-peek-sym? 'in)
           (begin (p-adv)
                  (let* ((class (p-parse-implies)))
                    (list 'in sym class)))
           (list sym))))
    (else (error "vnb-parse: expected binding, got" (p-peek)))))

;; BINDING-LIST — comma-separated bindings; consumes closing ]
(define (p-parse-binding-list)
  (if (eq? (p-peek) 'rbracket)
      (begin (p-adv) '())
      (let* ((first (p-parse-one-binding))
             (rest  (let lp ()
                      (cond
                        ((eq? (p-peek) 'rbracket) (p-adv) '())
                        ((eq? (p-peek) 'comma)
                         (p-adv)
                         (let* ((b (p-parse-one-binding)) (more (lp)))
                           (cons b more)))
                        (else (error "vnb-parse: expected ] or , in binding list, got"
                                     (p-peek)))))))
        (cons first rest))))

;; QUANTIFIER — funsym already consumed; parse ([bindings], body)
(define (p-parse-quantifier q)
  (p-expect! 'lparen)
  (p-expect! 'lbracket)
  (let* ((bindings (p-parse-binding-list)))
    (p-expect! 'comma)
    (let* ((body (p-parse-implies)))
      (p-expect! 'rparen)
      (list q bindings body))))

;; FUNCTOID — lambda or lambdoid; parse ([bindings], body) -> <functoid> record
(define (p-parse-functoid kind)
  (p-expect! 'lparen)
  (p-expect! 'lbracket)
  (let* ((bindings (p-parse-binding-list)))
    (p-expect! 'comma)
    (let* ((body (p-parse-implies)))
      (p-expect! 'rparen)
      ;; Convert binding specs: (in var dom) -> (var . dom) ; (var) -> (var . CLASS)
      (let ((bpairs (map (lambda (spec)
                           (if (and (pair? spec) (eq? (car spec) 'in)
                                    (symbol? (cadr spec)))
                               (cons (cadr spec) (caddr spec))
                               (error "vnb-parse: lambda binding must be 'x in A'" spec)))
                         bindings)))
        (make-functoid kind bpairs body)))))

;; Expand set_of(e1 ... en) / {e1,...,en} into (MAKE-SET (LIST e1 ... en)).
;;   {}       -> (MAKE-SET (LIST))          empty set
;;   {a}      -> (MAKE-SET (LIST a))        singleton
;;   {a,b,c}  -> (MAKE-SET (LIST a b c))    general case
(define (expand-set-of elems)
  `(MAKE-SET ,(cons 'list elems)))

;; BRACE-EXPR — {}, {a,b,c}, {x in A: p}, {x in A | p}, or {x | p}; already consumed {
(define (p-parse-brace)
  ;; {} -> (MAKE-SET (LIST))  i.e. the empty set
  (if (eq? (p-peek) 'rbrace)
      (begin (p-adv) (expand-set-of '()))
      (let* ((first (p-parse-implies)))
        (cond
          ((memq (p-peek) '(colon pipe))
           (let* ((sep (p-adv))
                  (pred (p-parse-implies)))
             (p-expect! 'rbrace)
             (cond
               ;; {x in A: p} or {x in A | p}  ->  (SEP x A p)
               ((and (pair? first) (memq (car first) '(in IN)) (symbol? (cadr first)))
                `(SEP ,(cadr first) ,(caddr first) ,pred))
               ;; {x | p}  ->  (COMP x p)
               ((and (eq? sep 'pipe) (symbol? first))
                `(COMP ,first ,pred))
               (else
                (error "vnb-parse: expected 'x in A' or bare variable before separator"
                       first)))))
          ;; {a, b, c}  ->  (MAKE-SET (LIST a b c))
          (else
           (let* ((rest (let lp ()
                          (cond
                            ((eq? (p-peek) 'rbrace) (p-adv) '())
                            ((eq? (p-peek) 'comma)
                             (p-adv)
                             (let* ((e (p-parse-implies)) (more (lp)))
                               (cons e more)))
                            (else (error "vnb-parse: expected } or , in set literal"
                                         (p-peek)))))))
             (expand-set-of (cons first rest))))))))

;; POSTFIX-APPLY — if the next token is '(' after a primary, parse application.
;; A <functoid> primary becomes (apply-functoid <ftd> arg...).
(define (p-maybe-apply primary)
  (if (eq? (p-peek) 'lparen)
      (begin
        (p-adv)
        (let* ((args (p-parse-arglist)))
          (p-expect! 'rparen)
          (let ((result (if (functoid? primary)
                            (apply make-apply-functoid primary args)
                            (cons primary args))))
            ;; Support chained application: f(x)(y)
            (p-maybe-apply result))))
      primary))

;; PRIMARY — atoms, function calls, brackets, grouped parens
(define (p-parse-primary)
  (let ((t (p-peek)))
    (cond
      ((eq? t 'lparen)
       (p-adv)
       (let* ((e (p-parse-implies)))
         (p-expect! 'rparen)
         (p-maybe-apply e)))
      ((eq? t 'lbracket)
       (p-adv)
       (p-parse-bracket-list))
      ((eq? t 'lbrace)
       (p-adv)
       (p-parse-brace))
      ((and (pair? t) (eq? (car t) 'funsym))
       (p-adv)
       (let ((sym (cdr t)))
         (cond
           ((or (eq? sym 'forall) (eq? sym 'forsome))
            (p-parse-quantifier sym))
           ((or (eq? sym 'lambda) (eq? sym 'lambdoid))
            (p-maybe-apply (p-parse-functoid sym)))
           ((eq? sym 'set_of)
            (p-expect! 'lparen)
            (let* ((args (p-parse-arglist)))
              (p-expect! 'rparen)
              (expand-set-of args)))
           (else
            (p-expect! 'lparen)
            (let* ((args (p-parse-arglist)))
              (p-expect! 'rparen)
              (p-maybe-apply (cons sym args)))))))
      ((and (pair? t) (eq? (car t) 'sym))
       (p-adv) (cdr t))
      ((and (pair? t) (eq? (car t) 'num))
       (p-adv) (cdr t))
      (else (error "vnb-parse: unexpected token" t)))))

;;; -----------------------------------------------------------------------
;;; Top-level entry

(define (vnb-parse-tokens tokens)
  (set! *p-toks* (list->vector tokens))
  (set! *p-pos*  0)
  (let ((result (p-parse-implies)))
    (unless (eq? (p-peek) 'eof)
      (error "vnb-parse: trailing tokens after" result (p-peek)))
    result))

;;; -----------------------------------------------------------------------
;;; Public interface

(define (parse-string str)
  (vnb-guard (lambda () (vnb-parse-tokens (vnb-tokenize str)))))

(define (make-wff-from-string str)
  (vnb-guard (lambda () (make-wff (vnb-parse-tokens (vnb-tokenize str))))))
