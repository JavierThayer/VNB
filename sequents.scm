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

;;; Render assumptions and goal WITHOUT the surrounding quotes that
;;; wff->string adds.  The quotes used to signal "this is the string to
;;; paste into (bc \"...\")", but they clutter the Focus-Workspace display
;;; and confused the prompt; tactic commands now accept bare formulas (and
;;; assumption numbers), so the quotes are no longer needed here.
(define (sequent-wff->string w)
  (expression->string (wff-formula w)))

;;; THE PRESENTATION DIAL'S HOOK.  #f until presentation.scm sets it, and #f
;;; again whenever the dial sits at r1 -- so the default path below is the one
;;; that has always run and r1 output is untouched, which is what lets the
;;; round-trip gate go on meaning what it means.  A hook rather than a
;;; redefinition of `sequent->string' in the later file: silently shadowing a
;;; core procedure from downstream is exactly how `calc' disappeared
;;; (interactive.scm), and clobber-guard cannot see it -- it fires when a
;;; procedure is rebound to a NON-procedure.
(define *presentation-hook* #f)

(define (sequent->string s)
  (or (and *presentation-hook* (*presentation-hook* s))
      (sequent->string-r1 s)))

(define (sequent->string-r1 s)
  (let ((asms (sequent-assumptions s))
        (goal (sequent-assertion s)))
    (string-append
     (if (null? asms)
         "()"
         (let loop ((fs asms) (acc ""))
           (if (null? fs)
               (substring acc 0 (- (string-length acc) 2))
               (loop (cdr fs)
                     (string-append acc (sequent-wff->string (car fs)) ", ")))))
     "  =>  "
     (sequent-wff->string goal))))

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
;;;   (PAIR a b)      ->  pair(a, b)   -- NOT {a, b}, which is MAKE-SET
;;;   a head spelled from operator characters (/) -> (/)(a, b)
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
    ((memq head '(in = == <= <))    4)
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
;;; num-leaf->string renders a numeric leaf for display.  Reals go through
;;; the standard writer; non-real (complex) numbers are rendered in a+bi
;;; surface form using "i" rather than MIT Scheme's "+...i" spelling, so the
;;; display matches the %i input notation (e.g. +3i -> "3i", 2+3i -> "2+3i",
;;; -i -> "-i", 2-i -> "2-i").
(define (num-leaf->string n)
  (define (w x) (with-output-to-string (lambda () (write x))))
  (if (real? n)
      (w n)
      (let* ((r (real-part n))
             (m (imag-part n))
             ;; imaginary coefficient: 1 -> "", -1 -> "-", else the number
             (mag (cond ((= m  1) "")
                        ((= m -1) "-")
                        (else (w m))))
             (imag (string-append mag "i")))
        (if (zero? r)
            ;; A PURE imaginary must still begin with something the tokenizer
            ;; will start a NUMBER on.  `i' and `-i' do not: read-num begins on
            ;; a digit, so `i' is an IDENTIFIER and `-i' is unary minus applied
            ;; to one.  (IN +i CC) therefore printed `i in cc' and read back as
            ;; (IN i CC) -- a statement about a free variable, silently.  `1i'
            ;; and `0-i' are numeric literals and read back as themselves.
            (if (> m 0)
                (string-append (if (= m 1) "1" (w m)) "i")   ; 1i, 3i
                (string-append "0" imag))                    ; 0-i, 0-3i
            (if (> m 0)
                (string-append (w r) "+" imag)         ; r+i, r+3i
                (string-append (w r) imag))))))        ; mag carries the sign: r-i, r-3i

;;; ---- case-distinct ($) display + accessor-head capitalization ----
;;; Two display-only conventions, both keyed so the underlying (folded) symbols
;;; are never disturbed:
;;;   * a $-prefixed symbol ($x) prints as its uppercased body (X) -- a
;;;     case-distinct variable that dodges the X/x fold clash;
;;;   * an accessor symbol registered in *accessor-display* prints under its
;;;     declared capitalization, but ONLY in HEAD position (so the carrier
;;;     accessor x in x(s) shows as X while a bare element variable x stays x).
(define *accessor-display* (make-strong-eqv-hash-table))

(define (sym->display-leaf s)             ; variables / standalone symbols
  (let ((nm (symbol->string s)))
    (if (and (> (string-length nm) 0) (char=? (string-ref nm 0) #\$))
        (string-upcase (substring nm 1 (string-length nm)))
        nm)))

(define (sym->display-head s)             ; application heads (accessors etc.)
  (or (hash-table-ref/default *accessor-display* s #f)
      (sym->display-leaf s)))

;;; A symbol spelled ENTIRELY from the tokenizer's operator characters
;;; (parser.scm's op-ch?).  read-op consumes such a run into a single `sym'
;;; token and never into the `funsym' that a bare `head(' produces, so such a
;;; head cannot be printed in the ordinary application syntax `head(a, b)'.
(define (op-spelled-symbol? s)
  (let* ((n (symbol->string s)) (len (string-length n)))
    (and (> len 0)
         (let loop ((i 0))
           (or (= i len)
               (and (memv (string-ref n i) '(#\+ #\- #\* #\/ #\^ #\< #\= #\!))
                    (loop (+ i 1))))))))

;;; min-prec: the minimum precedence this expression must have to avoid
;;; being wrapped in an extra pair of parens by the caller.
(define (expr->str e min-prec)
  (cond
    ((symbol? e) (sym->display-leaf e))
    ((number? e) (num-leaf->string e))
    ;; Functoid record: lambdoid([x in A, y in B], body)
    ((functoid? e)
     (let* ((bindings (functoid-bindings e))
            (bstrs    (map (lambda (b)
                             (string-append (sym->display-leaf (car b))
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
         ;; and or iff -- the parser reads these RIGHT-associatively (p-parse-and
         ;; and friends), so only the RIGHT operand may be spliced without
         ;; parentheses.  A LEFT-nested (and (and A B) C) printed flat would
         ;; re-parse as (and A (and B C)) -- a different S-expression, hence
         ;; not `equal?', hence not matched by `ass'.  Left args therefore go at
         ;; p+1 and take parens when their own head is at p.
         ((and (memq head '(and or iff)) (>= (length e) 3))
          (let* ((p    (op-prec head))
                 (sep  (string-append " " (symbol->string head) " "))
                 (last (- (length args) 1))
                 (s    (str-join
                        (map (lambda (a i) (expr->str a (if (= i last) p (+ p 1))))
                             args (iota (length args)))
                        sep)))
            (paren-if s p min-prec)))
         ;; + and * -- the parser reads a chain of these into ONE FLAT n-ary node
         ;; (p-parse-add / p-parse-mul), so a flat node of any arity splices with
         ;; no parentheses, but a nested SAME-HEAD child is a distinct term and
         ;; must be parenthesised or the printed form re-parses to the flat node.
         ;; This is display honesty, not prettiness: the extra parens are exactly
         ;; the places where the stored term is not the flat one.
         ((and (memq head '(+ *)) (>= (length e) 3))
          (let* ((p   (op-prec head))
                 (sep (string-append " " (symbol->string head) " "))
                 (s   (str-join
                       (map (lambda (a)
                              (expr->str a (if (and (pair? a) (eq? (car a) head))
                                               (+ p 1)
                                               p)))
                            args)
                       sep)))
            (paren-if s p min-prec)))
         ;; implies: right-associative; left arg needs p+1, right needs p
         ((and (eq? head 'implies) (= (length e) 3))
          (let* ((p 0)
                 (s (string-append (expr->str (cadr e) (+ p 1))
                                   " implies "
                                   (expr->str (caddr e) p))))
            (paren-if s p min-prec)))
         ;; Binary comparison: in subset = == <= <  (non-associative; both args at p)
         ((and (memq head '(in subset SUBSET = == <= <)) (= (length e) 3))
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
         ;;
         ;; The RIGHT operand goes at p only when it is itself a `power' (that
         ;; is the right-associativity).  Everything else goes at p+1, and the
         ;; one term that difference catches is a unary minus, whose precedence
         ;; is also 7: `x ^ -n' printed without parentheses, and p-parse-pow
         ;; parses its right operand as a PRIMARY, not as a unary -- so the
         ;; string died with "trailing tokens after (power x -)".  `x ^ (-n)'
         ;; reads back as (POWER x (- n)).
         ((and (eq? head 'power) (= (length e) 3))
          (let* ((p 7)
                 (rt (caddr e))
                 (s (string-append (expr->str (cadr e) (+ p 1))
                                   " ^ "
                                   (expr->str rt (if (and (pair? rt) (eq? (car rt) 'power))
                                                     p
                                                     (+ p 1))))))
            (paren-if s p min-prec)))
         ;; (MAKE-SET (list a b c)) -> {a, b, c}
         ((and (eq? head 'MAKE-SET) (= (length e) 2)
               (pair? (cadr e)) (eq? (car (cadr e)) 'list))
          (let ((elems (cdr (cadr e))))
            (string-append "{"
                           (str-join (map (lambda (a) (expr->str a 0)) elems) ", ")
                           "}")))
         ;; PAIR has NO branch here, and that is the fix (2026-08-24).  It used
         ;; to print (PAIR a b) as `{a, b}' and (PAIR a a) as `{a}' -- the
         ;; surface syntax of MAKE-SET, a DIFFERENT primitive (`{a, b}' reads
         ;; back as (MAKE-SET (LIST a b)), library.scm's make-set-membership,
         ;; not the pairing axiom).  48 installed formulas printed as a term
         ;; they were not, and a user retyping one got a formula `ass' would
         ;; not match.  PAIR now falls through to the generic application arm
         ;; and prints `pair(a, b)', which reads back as itself.
         ;; (SEP x A p) -> {x in A: p}
         ((and (eq? head 'SEP) (= (length e) 4))
          (string-append "{" (sym->display-leaf (cadr e))
                         " in " (expr->str (caddr e) 0)
                         ": " (expr->str (cadddr e) 0) "}"))
         ;; (COMP x p) -> {x | p}
         ((and (eq? head 'COMP) (= (length e) 3))
          (string-append "{" (sym->display-leaf (cadr e))
                         " | " (expr->str (caddr e) 0) "}"))
         ;; (apply-functoid <ftd> arg ...) -> lambdoid([...], body)(arg, ...)
         ((eq? head 'apply-functoid)
          (string-append (expr->str (car args) 0)
                         "("
                         (str-join (map (lambda (a) (expr->str a 0)) (cdr args)) ", ")
                         ")"))
         ;; A head spelled from operator characters -- `/' is the only one in
         ;; the tree -- prints with its head PARENTHESISED: `(/)(t, 1 + t)'.
         ;; That is not decoration.  `/(t, 1 + t)', which the generic arm below
         ;; produced, dies in the parser ("trailing tokens after / lparen"),
         ;; because read-op makes `/' an operator token and only a funsym can
         ;; head an application.  The parenthesised form IS readable:
         ;; p-parse-primary's lparen branch hands the bare symbol to
         ;; p-maybe-apply, so `(/)(t, 1 + t)' is (/ t (+ 1 t)) exactly.
         ;;
         ;; The pretty alternative is deliberately NOT taken.  `t / (1 + t)'
         ;; parses -- to (* t (recip (+ 1 t))), because infix `/' is SUGAR in
         ;; p-parse-mul and builds no `/' node at all.  Printing the sugar
         ;; would hand the user a string that reads back as a different
         ;; S-expression, silently, `ass' and `rfl' being syntactic.  The ugly
         ;; form is the honest one, and its ugliness is information: a `/' head
         ;; has no ordinary surface spelling.
         ((and (symbol? head) (op-spelled-symbol? head))
          (string-append "(" (symbol->string head) ")("
                         (str-join (map (lambda (a) (expr->str a 0)) args) ", ")
                         ")"))
         ;; Compound head: ((f x) a b) -> (f(x))(a, b) — self-delimiting
         ;;
         ;; A NULLARY application prints with its parentheses: (f) is `f()',
         ;; NOT `f'.  It used to print as the bare head, which made the term
         ;; (f) and the symbol f indistinguishable on the surface -- so
         ;; `(= (f) f)' displayed as `f = f' while `rfl' refused it, the two
         ;; sides being different S-expressions.  The parser and validate-wff!
         ;; now reject nullary applications outright, so this arm should be
         ;; unreachable for anything a user typed; it stays honest for a raw
         ;; S-expression handed straight to the printer.
         ((pair? head)
          (let ((head-str (string-append "(" (expr->str head 0) ")")))
            (string-append head-str
                           "("
                           (str-join (map (lambda (a) (expr->str a 0)) args) ", ")
                           ")")))
         ;; Everything else: f(x, y, z) — self-delimiting
         (else
          (string-append (sym->display-head head)
                         "("
                         (str-join (map (lambda (a) (expr->str a 0)) args) ", ")
                         ")")))))
    (else (with-output-to-string (lambda () (write e))))))

(define (print-binding spec)
  (cond
    ;; (var) or (var1 var2 ...) — unrestricted, all symbols
    ((and (pair? spec) (not (null? spec))
          (all-symbols? spec) (not (eq? (car spec) 'in)))
     (str-join (map sym->display-leaf spec) ", "))
    ;; (in var A)
    ((and (pair? spec) (= (length spec) 3)
          (eq? (car spec) 'in) (symbol? (cadr spec)))
     (string-append (sym->display-leaf (cadr spec))
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
;;; The number MIT prints in #[wff 16 ...] is its OBJECT hash -- per-object
;;; identity, handed out by the printer on demand.  Two wffs built from the same
;;; text always get different ones, which makes the printed form useless for the
;;; question a reader actually asks of two formulas on screen: are these the same
;;; thing?  So the wff's own digest is printed beside it (`h' + hex).  Equal
;;; digests mean alpha-equivalent up to a collision -- `wff-equiv?' is the exact
;;; test -- and DIFFERENT digests mean genuinely different formulas.
(define *wff-print-digest?* #t)

(set-record-type-unparser-method! <wff>
  (simple-unparser-method 'wff
    (lambda (w)
      (if *wff-print-digest?*
          (list (string->symbol
                 (string-append "h" (number->string (wff-hash w) 16)))
                (expression->string (wff-formula w)))
          (list (expression->string (wff-formula w)))))))

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
