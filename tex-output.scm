;;; tex-output.scm -- render VNB s-expression formulas as LaTeX math.
;;;
;;; Public entry points:
;;;   (expr->tex sexpr)            -> string of LaTeX math
;;;   (formula-tex name)           -> standalone TeX document for theorem NAME
;;;   (write-formula-tex name path) -> writes a .tex file at PATH
;;;
;;; Used by Emacs' vnb-view-as-pdf to render a single PSS / library entry
;;; as an inline PDF via pdflatex + doc-view.

;;; --- string helpers --------------------------------------------------

(define (tex--string-join strs sep)
  (cond ((null? strs) "")
        ((null? (cdr strs)) (car strs))
        (else (string-append (car strs) sep
                             (tex--string-join (cdr strs) sep)))))

;;; Escape characters that are special inside \mathsf{...} / \mathit{...}.
;;; Identifiers in VNB are letters/digits/hyphen/underscore; underscore
;;; would be parsed as subscript-marker in math mode, hyphen would render
;;; as a wide minus.  We escape both.
(define (tex--escape-ident s)
  (let loop ((chars (string->list s)) (acc '()))
    (cond ((null? chars) (list->string (reverse acc)))
          ((char=? (car chars) #\_)
           (loop (cdr chars) (cons #\_ (cons #\\ acc))))
          ((char=? (car chars) #\-)
           ;; render hyphen as a tight "-" via {-} so it's not stretched
           (loop (cdr chars) (append '(#\} #\- #\{) acc)))
          (else
           (loop (cdr chars) (cons (car chars) acc))))))

;;; Operator identifiers render via \operatorname (upright, correctly spaced).
;;; Inside \operatorname a bare `-' is a minus sign and `_' a subscript marker,
;;; so a hyphenated name like comb-kk needs \text{-} to keep a real hyphen.
(define (tex--escape-op-ident s)
  (apply string-append
         (map (lambda (c)
                (cond ((char=? c #\_) "\\_")
                      ((char=? c #\-) "\\text{-}")
                      ((char=? c #\#) "\\#")
                      (else (string c))))
              (string->list s))))

(define (tex--operatorname name)
  (string-append "\\operatorname{" (tex--escape-op-ident name) "}"))

;;; --- symbol tables ---------------------------------------------------
;;;
;;; All keys are stored in case-folded (lower-case) form because MIT
;;; Scheme's reader case-folds at read time.  So `'NN' here is really
;;; the symbol nn, which matches what appears in stored formulas.

(define *tex-atom-table*
  '((nn        . "\\mathbb{N}")
    (rr        . "\\mathbb{R}")
    (qq        . "\\mathbb{Q}")
    (zz        . "\\mathbb{Z}")
    (cc        . "\\mathbb{C}")
    (ord       . "\\mathrm{Ord}")
    (set       . "\\mathbf{Set}")
    (empty-set . "\\emptyset")
    (true      . "\\top")
    (false     . "\\bot")))

;;; Multi-character symbols that should render as their Greek letter.
(define *tex-greek-table*
  '((alpha . "\\alpha") (beta . "\\beta") (gamma . "\\gamma")
    (delta . "\\delta") (epsilon . "\\varepsilon") (eta . "\\eta")
    (theta . "\\theta") (iota . "\\iota") (kappa . "\\kappa")
    (lambda . "\\lambda") (mu . "\\mu") (nu . "\\nu") (xi . "\\xi")
    (pi . "\\pi") (rho . "\\rho") (sigma . "\\sigma") (tau . "\\tau")
    (phi . "\\varphi") (psi . "\\psi") (chi . "\\chi") (omega . "\\omega")
    (ell . "\\ell")
    (omicron . "o")
    (gamma . "\\gamma") (delta . "\\delta")))

(define *tex-binop-table*
  '((=       . " = ")
    (in      . " \\in ")
    (subset  . " \\subseteq ")
    (<       . " < ")
    (<=      . " \\leq ")
    (>       . " > ")
    (>=      . " \\geq ")
    (+        . " + ")
    (binplus  . " + ")
    (*        . " \\cdot ")
    (bintimes . " \\cdot ")
    (and     . " \\wedge ")
    (or      . " \\vee ")
    (implies . " \\Rightarrow ")
    (iff     . " \\Leftrightarrow ")))

;;; Arithmetic-prefix mode (used only when rendering a PROPOSITION statement):
;;; render the arithmetic operators PREFIX -- +(n, 1), \cdot(a, b) -- rather than
;;; infix, so the statement's arithmetic never competes with / is confused for the
;;; ring operations (which are already prefix, add(r)(x,y)).  A fluid flag so it
;;; scopes to the statement and leaves the proof steps' infix arithmetic alone.
(define *tex-arith-prefix?* #f)
(define *tex-arith-prefix-head*
  '((+ . "+") (binplus . "+") (* . "\\cdot") (bintimes . "\\cdot")
    (- . "-") (binminus . "-")))

;;; Per-operator render rules.  Each entry is (op-name args -> string).
;;; Defined after expr->tex below via a setter so they can call expr->tex
;;; mutually-recursively without forward-reference pain.

(define *tex-special-table* '())

(define (tex--register-special! name fn)
  (set! *tex-special-table*
        (cons (cons name fn) *tex-special-table*)))

;;; --- variable vs operator heuristic ----------------------------------

(define (tex--all-lower-letters? s)
  (let loop ((cs (string->list s)))
    (cond ((null? cs) #t)
          ((or (char-lower-case? (car cs)) (char-numeric? (car cs)))
           (loop (cdr cs)))
          (else #f))))

(define (tex--has-hyphen? s)
  (let loop ((cs (string->list s)))
    (cond ((null? cs) #f)
          ((char=? (car cs) #\-) #t)
          (else (loop (cdr cs))))))

;;; "lm12" -> ("lm" . "12"); #f unless the name is one or more LETTERS followed by
;;; one or more DIGITS and nothing else.
(define (tex--split-trailing-digits name)
  (let* ((n (string-length name))
         (k (let loop ((i n))
              (if (and (> i 0) (char-numeric? (string-ref name (- i 1))))
                  (loop (- i 1))
                  i))))
    (and (> k 0) (< k n)
         (let check ((i 0))
           (cond ((= i k) (cons (string-head name k) (string-tail name k)))
                 ((char-alphabetic? (string-ref name i)) (check (+ i 1)))
                 (else #f))))))

(define (tex--symbol->string s)
  (let* ((name (symbol->string s))
         (atom (assq s *tex-atom-table*))
         (greek (assq s *tex-greek-table*)))
    (cond
      (atom  (cdr atom))
      (greek (cdr greek))
      ;; Hyphenated identifier -> operator (\operatorname).
      ((tex--has-hyphen? name)
       (tex--operatorname name))
      ;; Single character -> bare math identifier (italic by default).
      ((= (string-length name) 1) name)
      ;; LETTERS followed by DIGITS -> the letters with the digits as a SUBSCRIPT
      ;; (2026-09-22, the user: `lm1', `lm2' were set upright as words).  The base
      ;; is rendered by this same procedure, so `x1' is x_1 and `theta2' is
      ;; \theta_2.
      ((tex--split-trailing-digits name)
       => (lambda (parts)
            (string-append (tex--symbol->string (string->symbol (car parts)))
                           "_{" (cdr parts) "}")))
      ;; All lowercase letters + digits -> italic variable identifier.
      ((tex--all-lower-letters? name)
       (string-append "\\mathit{" (tex--escape-ident name) "}"))
      ;; Anything else (mixed case, etc.) -> upright operator.
      (else
       (tex--operatorname name)))))

;;; Render the HEAD of a function application.  A multi-character symbol in
;;; head position is an operator (\operatorname); single-char heads (function
;;; variables) stay italic, and compound heads like (add r) recurse.
(define (tex--head->tex op)
  (if (and (symbol? op)
           (> (string-length (symbol->string op)) 1)
           (not (assq op *tex-atom-table*))
           (not (assq op *tex-greek-table*)))
      (tex--operatorname (symbol->string op))
      (expr->tex op)))

;;; --- typed quantifier sugar ------------------------------------------

;;; (FORALL x (IMPLIES (IN x S) body))  -- typed forall sugar.
(define (tex--typed-forall-parts e)
  (and (pair? e) (eq? (car e) 'forall) (= (length e) 3)
       (let ((var (cadr e)) (sub (caddr e)))
         (and (pair? sub) (eq? (car sub) 'implies) (= (length sub) 3)
              (let ((cnd (cadr sub)) (body (caddr sub)))
                (and (pair? cnd) (eq? (car cnd) 'in) (= (length cnd) 3)
                     (eq? (cadr cnd) var)
                     (list var (caddr cnd) body)))))))

;;; (FORSOME x (AND (IN x S) body))  -- typed exists sugar.
(define (tex--typed-exists-parts e)
  (and (pair? e) (eq? (car e) 'forsome) (= (length e) 3)
       (let ((var (cadr e)) (sub (caddr e)))
         (and (pair? sub) (eq? (car sub) 'and) (= (length sub) 3)
              (let ((cnd (cadr sub)) (body (caddr sub)))
                (and (pair? cnd) (eq? (car cnd) 'in) (= (length cnd) 3)
                     (eq? (cadr cnd) var)
                     (list var (caddr cnd) body)))))))

;;; A maximal run of quantifiers of ONE connective, printed as ONE prefix
;;; (2026-09-23, notes-36 item 1 and the user's follow-up on Prop 1.1):
;;;   forall a. forall b. forall c. B              -> \forall a, b, c.\; B
;;;   forall a in X. forall b in Y. B              -> \forall a \in X, b \in Y.\; B
;;;   forall a in X. forall b in X. B              -> \forall a, b \in X.\; B
;;;   forall x. forall y. x in R => y in R => B    -> \forall x, y \in R.\; B
;;; The last line is the shape every `forall-guarded' statement has (binders
;;; first, the guards as a chain of antecedents), and it reads as the typed
;;; binder list it means.  A guard is ABSORBED into its binder only when it is
;;; literally (IN v S) for a still-unguarded binder v of this run and S mentions
;;; no binder of the run at or after v: the printed binder list scopes left to
;;; right (CLAUDE.md, "Case folding" 4), so `x in seg(n)' with n bound LATER
;;; must stay an antecedent.  A predicate guard (IS-RING(r)) is never absorbed.
;;; Existentials absorb from (AND (IN v S) rest) the same way.  Both printers
;;; (the one-row expr->tex and the row-splitting tex--quant-step) read the run
;;; from here, so they cannot disagree.
(define (tex--quant-kind e)
  (cond ((tex--typed-forall-parts e)
         => (lambda (vsb) (list 'forall (car vsb) (cadr vsb) (caddr vsb))))
        ((tex--typed-exists-parts e)
         => (lambda (vsb) (list 'exists (car vsb) (cadr vsb) (caddr vsb))))
        ((and (pair? e) (eq? (car e) 'forall) (= (length e) 3))
         (list 'forall (cadr e) #f (caddr e)))
        ((and (pair? e) (eq? (car e) 'forsome) (= (length e) 3))
         (list 'exists (cadr e) #f (caddr e)))
        (else #f)))

;;; (IN v S) at the head of BODY's antecedent chain (forall) or conjunction
;;; (exists): (list v S rest), else #f.
(define (tex--guard-of body conn)
  (let ((head (if (eq? conn 'forall) 'implies 'and)))
    (and (pair? body) (eq? (car body) head) (= (length body) 3)
         (let ((g (cadr body)))
           (and (pair? g) (eq? (car g) 'in) (= (length g) 3) (symbol? (cadr g))
                (list (cadr g) (caddr g) (caddr body)))))))

(define (tex--mentions? e sym)
  (cond ((eq? e sym) #t)
        ((pair? e) (or (tex--mentions? (car e) sym) (tex--mentions? (cdr e) sym)))
        (else #f)))

;;; BS is the run's binders, ((var . dom-or-#f) ...) in order.  May guard G's
;;; variable be absorbed?  It must be an unguarded binder of the run, and the
;;; domain must not mention it or any later binder.
(define (tex--absorbable? bs g)
  (let scan ((bs bs))
    (cond ((null? bs) #f)
          ((eq? (car (car bs)) (car g))
           (and (not (cdr (car bs)))
                (let none ((later bs))
                  (or (null? later)
                      (and (not (tex--mentions? (cadr g) (car (car later))))
                           (none (cdr later)))))))
          (else (scan (cdr bs))))))

(define (tex--set-dom bs v dom)
  (map (lambda (b) (if (eq? (car b) v) (cons v dom) b)) bs))

;;; Consecutive binders with the same domain print as one group: "x, y \in S";
;;; an unguarded binder prints bare.
(define (tex--binder-groups bs)
  (let loop ((bs bs) (acc '()))
    (if (null? bs)
        (reverse acc)
        (let* ((dom (cdr (car bs)))
               (take (let grab ((rest bs) (vars '()))
                       (if (and (pair? rest) (equal? (cdr (car rest)) dom))
                           (grab (cdr rest) (cons (car (car rest)) vars))
                           (cons (reverse vars) rest))))
               (vars (car take))
               (rest (cdr take))
               (names (tex--string-join (map expr->tex vars) ", ")))
          (loop rest
                (cons (if dom (string-append names " \\in " (expr->tex dom)) names)
                      acc))))))

;;; Returns (list HEAD-TEX GROUP-TEXS BODY), or #f when E has no quantifier.
(define (tex--quant-run e)
  (let ((first (tex--quant-kind e)))
    (and first
         (let ((conn (car first)))
           (let loop ((k first) (bs '()))
             (let ((bs   (cons (cons (cadr k) (caddr k)) bs))
                   (body (cadddr k))
                   (next (tex--quant-kind (cadddr k))))
               (if (and next (eq? (car next) conn))
                   (loop next bs)
                   (let absorb ((bs (reverse bs)) (body body))
                     (let ((g (tex--guard-of body conn)))
                       (if (and g (tex--absorbable? bs g))
                           (absorb (tex--set-dom bs (car g) (cadr g)) (caddr g))
                           (list (if (eq? conn 'forall) "\\forall " "\\exists ")
                                 (tex--binder-groups bs)
                                 body)))))))))))

;;; --- main render -----------------------------------------------------

(define (expr->tex e)
  (cond
    ((number? e) (number->string e))
    ((symbol? e) (tex--symbol->string e))
    ((string? e)
     (string-append "\\text{``" e "''}"))
    ((pair? e)
     (let ((op (car e)) (args (cdr e)))
       (cond
         ;; quantifiers: a maximal run of one kind on one prefix
         ((tex--quant-run e)
          => (lambda (run)
               (string-append (car run)
                              (tex--string-join (cadr run) ", ")
                              ".\\; " (expr->tex (caddr run)))))
         ;; arithmetic prefix (statement mode): +(n, 1) not (n + 1)
         ((and *tex-arith-prefix?* (assq op *tex-arith-prefix-head*))
          (string-append (cdr (assq op *tex-arith-prefix-head*)) "("
                         (tex--string-join (map expr->tex args) ", ") ")"))
         ;; A TeX template declared with `notation!' beside the definition
         ;; (operators.scm).  It sits ABOVE the two built-in tables, so a head
         ;; that declares its own reading is authoritative -- that is what "the
         ;; ONE table, keyed by head symbol" is supposed to mean, and until
         ;; 2026-08-10 this branch sat below them and no head declared a `tex'
         ;; template at all, so it never fired.  It stays BELOW the
         ;; arithmetic-prefix branch on purpose: that is a MODE (a fluid scoped
         ;; to a proposition statement), not a per-head rule, and a mode
         ;; overrides a declaration.  Prefix application is still the default,
         ;; so this fires only where a head asked for something else.  Tested by
         ;; LOOKING UP the template rather than by calling operator-render-tex:
         ;; that renders the arguments to decide whether it applies, and from
         ;; above the binop table it would do so at every level of every formula
         ;; -- rendering each subterm twice per level, i.e. 2^depth.
         ((let ((e (operator-ref op))) (and e (operator-tex e)))
          => (lambda (tmpl) (op--fill tmpl (map expr->tex args))))
         ;; binary infix (parenthesised; over-paren is acceptable in MVP)
         ((assq op *tex-binop-table*)
          (let ((sep (cdr (assq op *tex-binop-table*))))
            (string-append "(" (tex--string-join (map expr->tex args) sep)
                           ")")))
         ;; specially-rendered operators (NOT, CARD, PAIR, FUN, ...)
         ((assq op *tex-special-table*)
          ((cdr (assq op *tex-special-table*)) args))
         ;; default: application  (f a b c) -> f(a, b, c)
         (else
          (string-append (tex--head->tex op) "("
                         (tex--string-join (map expr->tex args) ", ")
                         ")")))))
    (else
     (string-append "\\text{?}\\{"
                    (with-output-to-string (lambda () (display e)))
                    "\\}"))))

;;; --- register the special operators ---------------------------------

(tex--register-special! 'not
  (lambda (args) (string-append "\\neg " (expr->tex (car args)))))

;; SUBTRACTION.  Not a `*tex-binop-table*' entry, and the reason is the unary
;; case: that table renders by JOINING the args with the separator, so a
;; one-argument `(- x)' would join a single string and come out as `(x)' -- the
;; minus silently gone.  Registered here instead, where the arity is visible.
;; Before 2026-09-05 there was no rule at all and `-' fell through to the
;; generic prefix application, so `a - b' rendered `-(a, b)' in BOTH the
;; statement mode and the proof steps, while its siblings `+' and `*' had infix
;; rules the whole time.  A gap, not a decision.
(tex--register-special! '-
  (lambda (args)
    (cond ((= (length args) 1)
           (string-append "-" (expr->tex (car args))))
          ((= (length args) 2)
           (string-append "(" (expr->tex (car args)) " - "
                          (expr->tex (cadr args)) ")"))
          (else                                  ; n-ary: keep it unambiguous
           (string-append "-(" (tex--string-join (map expr->tex args) ", ") ")")))))

(tex--register-special! 'card
  (lambda (args) (string-append "|" (expr->tex (car args)) "|")))

;; abs is a primitive head (number-systems.scm) and had no rule, so it rendered
;; \operatorname{abs}(x) -- the second defect on the rr-ms-dist slide.  Same
;; bars as CARD, which is the same idea one sort down.
(tex--register-special! 'abs
  (lambda (args) (string-append "\\lvert " (expr->tex (car args)) " \\rvert")))

(tex--register-special! 'ord-segment
  (lambda (args)
    (string-append "\\mathrm{OS}(" (expr->tex (car args)) ")")))

(tex--register-special! 'union
  (lambda (args)
    (string-append "(" (expr->tex (car args)) " \\cup "
                   (expr->tex (cadr args)) ")")))

(tex--register-special! 'intersection
  (lambda (args)
    (string-append "(" (expr->tex (car args)) " \\cap "
                   (expr->tex (cadr args)) ")")))

(tex--register-special! 'pair
  (lambda (args)
    (cond
      ;; (PAIR x x) -- singleton {x}
      ((and (pair? (cdr args)) (equal? (car args) (cadr args)))
       (string-append "\\{" (expr->tex (car args)) "\\}"))
      (else
       (string-append "\\{" (expr->tex (car args)) ", "
                      (expr->tex (cadr args)) "\\}")))))

(tex--register-special! 'list
  (lambda (args)
    (string-append "\\langle "
                   (tex--string-join (map expr->tex args) ", ")
                   " \\rangle")))

(tex--register-special! 'fun
  (lambda (args)
    (cond
      ((= (length args) 2)
       (string-append "(" (expr->tex (car args)) " \\to "
                      (expr->tex (cadr args)) ")"))
      (else
       (string-append "\\mathrm{Fun}("
                      (tex--string-join (map expr->tex args) ", ")
                      ")")))))

(tex--register-special! 'cartesian
  (lambda (args)
    (string-append "(" (expr->tex (car args)) " \\times "
                   (expr->tex (cadr args)) ")")))

(tex--register-special! 'bijection
  (lambda (args)
    (string-append "\\mathrm{Bij}(" (expr->tex (car args)) ", "
                   (expr->tex (cadr args)) ")")))

(tex--register-special! 'inverse-bij
  (lambda (args)
    (string-append (expr->tex (car args)) "^{-1}")))

(tex--register-special! 'succ
  (lambda (args)
    (if *tex-arith-prefix?*         ; statement mode: prefix, no infix "+"
        (string-append "\\operatorname{succ}(" (expr->tex (car args)) ")")
        (string-append "(" (expr->tex (car args)) " + 1)"))))

(tex--register-special! 'succ_ord
  (lambda (args)
    (string-append "(" (expr->tex (car args)) " + 1)")))

(tex--register-special! 'if
  (lambda (args)
    (string-append "\\left(\\text{if }" (expr->tex (car args))
                   "\\text{ then }" (expr->tex (cadr args))
                   "\\text{ else }" (expr->tex (caddr args))
                   "\\right)")))

(tex--register-special! 'vnb-lambda
  ;; (VNB-LAMBDA bspec A body) -- the domain is part of the term, so it is part
  ;; of the rendering: \lambda v \in A.\; body.
  (lambda (args)
    (string-append "(\\lambda " (expr->tex (car args))
                   " \\in " (expr->tex (cadr args)) ".\\; "
                   (expr->tex (caddr args)) ")")))

(tex--register-special! 'sep
  (lambda (args)
    ;; (SEP x A phi)  ->  {x in A : phi}
    (cond
      ((= (length args) 3)
       (string-append "\\{" (expr->tex (car args)) " \\in "
                      (expr->tex (cadr args)) " : "
                      (expr->tex (caddr args)) "\\}"))
      (else
       (string-append "\\mathrm{Sep}("
                      (tex--string-join (map expr->tex args) ", ") ")")))))

(tex--register-special! 'choice
  (lambda (args)
    (string-append "\\varepsilon(" (expr->tex (car args)) ")")))

(tex--register-special! 'iota
  (lambda (args)
    (string-append "\\iota(" (expr->tex (car args)) ")")))

(tex--register-special! 'inf-subsets
  (lambda (args)
    (string-append "\\mathrm{Inf}(" (expr->tex (car args)) ")")))

;;; --- multi-line (display) rendering ----------------------------------
;;;
;;; expr->tex puts everything on one line, which makes deeply-nested
;;; structure laws (e.g. Euclidean division-with-remainder) render far
;;; wider than a window.  expr->tex-display breaks at the top-level
;;; logical skeleton -- a run of quantifiers, an implication, or a top
;;; conjunction/disjunction -- emitting one indented row per piece inside
;;; a left-aligned array.  Leaves below that skeleton stay inline (via
;;; expr->tex), so the breaking is shallow and predictable.

(define (tex--ind n)
  (let loop ((k n) (s "")) (if (<= k 0) s (loop (- k 1) (string-append "\\quad " s)))))

;;; If E begins with a quantifier (typed or plain), return
;;; (cons "prefix-tex" body-expr); else #f.
(define (tex--quant-step e)
  (let ((run (tex--quant-run e)))
    (and run
         (cons (string-append (car run) (tex--string-join (cadr run) ", ") ".")
               (caddr run)))))

;;; A conjunction/disjunction whose one-line render is at most this many
;;; TeX characters stays on a single row; longer ones break across rows.
(define tex--inline-threshold 100)
;;; Source length under which a whole formula is kept on one row by `tex--lines'.
;;; Smaller than the inline threshold: TeX source overstates printed width, but a
;;; row of quantifiers plus body is wider than a bare conjunct.
(define tex--short-row 80)

;;; Flatten a right- or left-nested run of the same operator OP.
(define (tex--flatten-op op e)
  (if (and (pair? e) (eq? (car e) op))
      (apply append (map (lambda (x) (tex--flatten-op op x)) (cdr e)))
      (list e)))

;;; Append SUFFIX to the final string in the non-empty list ROWS.
(define (tex--suffix-last rows suffix)
  (if (null? (cdr rows))
      (list (string-append (car rows) suffix))
      (cons (car rows) (tex--suffix-last (cdr rows) suffix))))

;;; Relations at whose top level a long formula breaks (LHS row, then a
;;; row beginning with the relation symbol).
(define *tex-relation-ops* '(= < <= > >= in subset))

;;; A plain function application (f a b c) -- NOT a quantifier, connective,
;;; relation, infix binop, specially-rendered operator, or a head that declared
;;; its own TeX template.  These are the terms whose argument list we wrap
;;; across rows when they are too wide.
;;;
;;; That last exclusion is easy to forget and was missing until 2026-08-10: this
;;; predicate is the gate on the "long application" branch of tex--lines, which
;;; renders `head(' ITSELF and so never reaches expr->tex's head dispatch.  A
;;; declared head therefore rendered correctly everywhere EXCEPT at the top of a
;;; formula too wide to sit on one line -- which is exactly where a proposition
;;; statement is.  `==' was the specimen: (== a b) gave `(a \simeq b)', while
;;; rr-ms-dist's statement, the same head over wider arguments, still gave
;;; \operatorname{==}(...).  Any table this predicate does not consult is a
;;; rendering rule with a hole in it at full width.
(define (tex--breakable-app? e)
  (and (pair? e)
       (not (tex--quant-step e))
       (not (memq (car e) '(implies and or)))
       (not (memq (car e) *tex-relation-ops*))
       (not (assq (car e) *tex-binop-table*))
       (not (assq (car e) *tex-special-table*))
       (not (let ((entry (operator-ref (car e)))) (and entry (operator-tex entry))))))

;;; Drop the leading indent (tex--ind ind) known to prefix ROW.
(define (tex--drop-ind row ind)
  (let ((n (string-length (tex--ind ind))))
    (if (>= (string-length row) n) (substring row n (string-length row)) row)))

;;; The relation-symbol row(s): RHS rendered at IND, with "relsym\; " spliced
;;; in after the indent of the first RHS row.
(define (tex--rel-rows relsym rhs ind)
  (let ((rl (tex--lines rhs ind)))
    (cons (string-append (tex--ind ind) relsym "\\; " (tex--drop-ind (car rl) ind))
          (cdr rl))))

;;; A rough ON-PAGE width proxy for E, computed from the s-expression (not the
;;; TeX, whose \operatorname{...} markup wildly overcounts).  Used to pack short
;;; arguments onto a shared row instead of giving each its own line.
(define (tex--flat-len e)
  (cond ((number? e) (string-length (number->string e)))
        ((symbol? e) (max 1 (string-length (symbol->string e))))
        ((string? e) (+ 2 (string-length e)))
        ((pair? e)
         (let ((n (length (cdr e))))
           (+ (tex--flat-len (car e)) 2                 ; head + ( )
              (apply + (map tex--flat-len (cdr e)))      ; arguments
              (* 2 (max 0 (- n 1))))))                   ; ", " separators
        (else 4)))

;;; Approximate visual width available on a wrapped row: page columns minus the
;;; indent already consumed (each \quad ~ 2 columns).
(define tex--row-cols 72)
(define (tex--row-avail ind) (max 24 (- tex--row-cols (* 2 ind))))

;;; Wrap an application's argument list.  Short single-line arguments are PACKED
;;; greedily onto shared rows (up to the row width); an argument that is itself
;;; wide breaks onto its own multi-row block via tex--lines.  Every argument is
;;; comma-suffixed except the last, which carries the closing ')'.
(define (tex--arg-rows args ind)
  (let ((prefix (tex--ind ind)) (avail (tex--row-avail ind)))
    (let loop ((as args) (cur #f) (curw 0) (out '()))
      (if (null? as)
          (reverse (if cur (cons (string-append prefix cur) out) out))
          (let* ((a (car as)) (last? (null? (cdr as)))
                 (suffix (if last? ")" ","))
                 (w (tex--flat-len a)))
            (if (> (+ (string-length (expr->tex a)) 0) tex--inline-threshold)
                ;; wide argument: flush the current row, emit its own block
                (let* ((blk (tex--suffix-last (tex--lines a ind) suffix))
                       (out1 (if cur (cons (string-append prefix cur) out) out)))
                  (loop (cdr as) #f 0 (append (reverse blk) out1)))
                ;; short argument: pack onto the current row if it fits
                (let ((piece (string-append (expr->tex a) suffix)))
                  (if (and cur (> (+ curw 2 w) avail))
                      (loop (cdr as) piece w (cons (string-append prefix cur) out))
                      (loop (cdr as)
                            (if cur (string-append cur " " piece) piece)
                            (+ curw (if cur 2 0) w) out)))))))))

;;; Render E as a list of indented TeX row-strings, breaking at the
;;; logical skeleton -- and, when a piece is still wider than the inline
;;; threshold, at a top-level relation, a lambda body, or an application's
;;; argument list (keeping prefix notation).  IND = current indent depth.
(define (tex--lines e ind)
  (let ((qs (tex--quant-step e)))
    (cond
      ;; A formula that fits on one row stays on one row (2026-09-21): a short
      ;; curried implication used to be set one antecedent per row,
      ;;   0 < a =>  /  0 < b =>  /  0 < a b,
      ;; whatever its length.
      ((<= (string-length (expr->tex e)) tex--short-row)
       (list (string-append (tex--ind ind) (expr->tex e))))
      ;; a maximal run of quantifiers collapses onto one row
      (qs
       (let loop ((step qs) (parts '()))
         (let ((next (tex--quant-step (cdr step))))
           (if next
               (loop next (cons (car step) parts))
               (cons (string-append (tex--ind ind)
                       (tex--string-join (reverse (cons (car step) parts)) " "))
                     (tex--lines (cdr step) (+ ind 1)))))))
      ;; implication: antecedent + => , consequent on the next (indented) row
      ;; A LONG antecedent is broken like any other formula (2026-09-21: it used to
      ;; be set on ONE row whatever its length -- an eleven-conjunct hypothesis made
      ;; a row of 1300 characters, and the major-theorems list shrank the whole
      ;; statement to fit it).
      ((and (pair? e) (eq? (car e) 'implies) (= (length e) 3))
       ;; A CURRIED chain  A => (B => (C => D))  keeps its antecedents at ONE
       ;; indentation and indents only the final consequent (2026-09-21: each `=>'
       ;; used to add a level, and a ten-hypothesis theorem became a staircase).
       (let* ((ante (expr->tex (cadr e)))
              (conseq (caddr e))
              (chain? (and (pair? conseq) (eq? (car conseq) 'implies) (= (length conseq) 3)))
              (cind (if chain? ind (+ ind 1))))
         (if (<= (string-length ante) tex--inline-threshold)
             (cons (string-append (tex--ind ind) ante " \\Rightarrow ")
                   (tex--lines conseq cind))
             (append (tex--suffix-last (tex--lines (cadr e) ind) " \\Rightarrow")
                     (tex--lines conseq cind)))))
      ;; and/or: keep short ones inline; break long ones into one operand
      ;; block per (flattened) conjunct, connective trailing all but the last
      ((and (pair? e) (memq (car e) '(and or)) (>= (length e) 2))
       (let ((inline (expr->tex e)))
         (if (<= (string-length inline) tex--inline-threshold)
             (list (string-append (tex--ind ind) inline))
             (let ((conn (if (eq? (car e) 'and) " \\wedge" " \\vee")))
               (let loop ((ps (tex--flatten-op (car e) e)) (out '()))
                 (if (null? ps)
                     out
                     (let ((rows (tex--lines (car ps) ind)))
                       (loop (cdr ps)
                             (append out (if (null? (cdr ps))
                                             rows
                                             (tex--suffix-last rows conn)))))))))))
      ;; top-level relation: LHS block, then a row per RHS starting with the
      ;; relation symbol.  Short ones stay inline.
      ((and (pair? e) (memq (car e) *tex-relation-ops*) (= (length e) 3)
            (> (string-length (expr->tex e)) tex--inline-threshold))
       (append (tex--lines (cadr e) ind)
               (tex--rel-rows (string-trim (cdr (assq (car e) *tex-binop-table*)))
                              (caddr e) ind)))
      ;; long lambda: "(\lambda v.\;" on this row, body indented, ')' trailing.
      ((and (pair? e) (eq? (car e) 'vnb-lambda) (= (length e) 4)
            (> (string-length (expr->tex e)) tex--inline-threshold))
       (cons (string-append (tex--ind ind) "(\\lambda " (expr->tex (cadr e))
                            " \\in " (expr->tex (caddr e)) ".\\;")
             (tex--suffix-last (tex--lines (cadddr e) (+ ind 1)) ")")))
      ;; long application: "head(" merged onto the first argument row (so a short
      ;; leading arg like sum(r, ... stays with the head), remaining args packed.
      ((and (tex--breakable-app? e)
            (> (string-length (expr->tex e)) tex--inline-threshold))
       (let ((rows (tex--arg-rows (cdr e) (+ ind 1)))
             (head (string-append (tex--ind ind) (tex--head->tex (car e)) "(")))
         (if (null? rows)
             (list (string-append head ")"))
             (cons (string-append head (tex--drop-ind (car rows) (+ ind 1)))
                   (cdr rows)))))
      (else (list (string-append (tex--ind ind) (expr->tex e)))))))

;;; Public: render E, breaking long formulas across rows.  A single-row
;;; result is returned bare (no array) so short formulas are unaffected.
(define (expr->tex-display e)
  (let ((lines (tex--lines e 0)))
    (if (null? (cdr lines))
        (car lines)
        (string-append "\\begin{array}{@{}l@{}} "
                       (tex--string-join lines " \\\\ ")
                       " \\end{array}"))))

;;; --- document wrapper -----------------------------------------------

(define (formula-tex-document body-tex name)
  (string-append
    "\\documentclass[border=12pt]{standalone}\n"
    "\\usepackage{amsmath, amssymb}\n"
    "\\usepackage[utf8]{inputenc}\n"
    "\\begin{document}\n"
    "% PSS / theorem name: " name "\n"
    "$\\displaystyle\n"
    body-tex "\n"
    "$\n"
    "\\end{document}\n"))

;;; Look up NAME, with an IS-<NAME> fallback for structure section names
;;; (so e.g. `(formula-tex 'ring)' renders the `is-ring' defining axiom).
;;; Uses hash-table-ref/default directly because `lookup-theorem' throws
;;; on miss -- here we need the silent #f-or-formula form.
;;; Returns (cons resolved-name formula) or #f if nothing matches.
(define (tex--resolve-name name)
  (let ((direct (hash-table-ref/default *theorem-table* name #f)))
    (cond
      (direct (cons name direct))
      (else
       (let* ((is-name (symbol-append 'is- name))
              (is-form (hash-table-ref/default *theorem-table* is-name #f)))
         (cond
           (is-form (cons is-name is-form))
           (else #f)))))))

;;; Produce the standalone-document string for NAME, or throw if it
;;; isn't a known theorem / PSS entry / structure predicate.  Does NOT
;;; touch the filesystem -- safe to call before opening a file.
(define (formula-tex name)
  (let ((r (tex--resolve-name name)))
    (cond
      ((not r)
       (error "tex-output: no such theorem / PSS / IS-X entry" name))
      (else
       (formula-tex-document (expr->tex (cdr r)) (symbol->string (car r)))))))

;;; Write the document to PATH (overwrites).  Returns PATH on success.
;;; The document is built FIRST (so a lookup failure leaves no file
;;; behind for pdflatex to choke on).
(define (write-formula-tex name path)
  (let ((doc (formula-tex name)))      ; throws here on missing name -- safe
    (with-output-to-file path
      (lambda () (display doc)))
    path))

;;; --- live focused-sequent TeX (for the Emacs Focus inline-PNG toggle) ---
;;;
;;; Unlike formula-tex (which renders a NAMED catalog entry), this renders
;;; the FOCUSED sequent of a live proof state PS -- its assumptions and goal
;;; -- as LaTeX MATH strings (no document wrapper; Emacs' vnb-tex--render-one
;;; supplies $\displaystyle ... $ and dvipng).  Output is a Scheme plist that
;;; Emacs `read' consumes directly:
;;;
;;;   (status open count N assumptions ("tex" ...) goal "tex")
;;;   (status done)        ; proof complete
;;;   (status none)        ; no proof in progress
;;;
;;; expr->tex-display breaks long formulas across array rows, which renders
;;; fine inside the displaystyle math dvipng wraps each string in.
(define (sequent-tex-plist ps)
  (cond
    ((not ps)          (list 'status 'none))
    ((proof-done? ps)  (list 'status 'done))
    (else
     (let* ((sqn  (proof-state-focus ps))
            (asms (sequent-node-assumptions sqn))
            (goal (sequent-node-assertion sqn))
            (open (proof-open-goals ps)))
       (list 'status 'open
             'count  (length open)
             'assumptions
               (map (lambda (w) (expr->tex-display (wff-formula w))) asms)
             'goal   (expr->tex-display (wff-formula goal)))))))

;;; Write the focused-sequent plist for the current proof state *ps* to PATH
;;; (overwrites).  `write' escapes the TeX strings as Scheme/Elisp-readable
;;; string literals.  Returns PATH.
(define (write-sequent-tex path)
  (with-output-to-file path
    (lambda () (write (sequent-tex-plist *ps*)) (newline)))
  path)
