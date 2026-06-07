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
    (and     . " \\wedge ")
    (or      . " \\vee ")
    (implies . " \\Rightarrow ")
    (iff     . " \\Leftrightarrow ")))

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

(define (tex--symbol->string s)
  (let* ((name (symbol->string s))
         (atom (assq s *tex-atom-table*))
         (greek (assq s *tex-greek-table*)))
    (cond
      (atom  (cdr atom))
      (greek (cdr greek))
      ;; Hyphenated identifier -> operator (\mathsf with escaped hyphens).
      ((tex--has-hyphen? name)
       (string-append "\\mathsf{" (tex--escape-ident name) "}"))
      ;; Single character -> bare math identifier (italic by default).
      ((= (string-length name) 1) name)
      ;; All lowercase letters + digits -> italic variable identifier.
      ((tex--all-lower-letters? name)
       (string-append "\\mathit{" (tex--escape-ident name) "}"))
      ;; Anything else (mixed case, etc.) -> upright operator.
      (else
       (string-append "\\mathsf{" (tex--escape-ident name) "}")))))

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
         ;; typed quantifier sugar
         ((tex--typed-forall-parts e)
          => (lambda (vsb)
               (string-append "\\forall " (expr->tex (car vsb))
                              " \\in " (expr->tex (cadr vsb))
                              ".\\; " (expr->tex (caddr vsb)))))
         ((tex--typed-exists-parts e)
          => (lambda (vsb)
               (string-append "\\exists " (expr->tex (car vsb))
                              " \\in " (expr->tex (cadr vsb))
                              ".\\; " (expr->tex (caddr vsb)))))
         ;; plain quantifier
         ((memq op '(forall forsome))
          (string-append (if (eq? op 'forall) "\\forall " "\\exists ")
                         (expr->tex (cadr e))
                         ".\\; " (expr->tex (caddr e))))
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
          (string-append (expr->tex op) "("
                         (tex--string-join (map expr->tex args) ", ")
                         ")")))))
    (else
     (string-append "\\text{?}\\{"
                    (with-output-to-string (lambda () (display e)))
                    "\\}"))))

;;; --- register the special operators ---------------------------------

(tex--register-special! 'not
  (lambda (args) (string-append "\\neg " (expr->tex (car args)))))

(tex--register-special! 'card
  (lambda (args) (string-append "|" (expr->tex (car args)) "|")))

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
    (string-append "(" (expr->tex (car args)) " + 1)")))

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
  (lambda (args)
    (string-append "(\\lambda " (expr->tex (car args)) ".\\; "
                   (expr->tex (cadr args)) ")")))

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
  (cond
    ((tex--typed-forall-parts e)
     => (lambda (vsb)
          (cons (string-append "\\forall " (expr->tex (car vsb))
                               " \\in " (expr->tex (cadr vsb)) ".")
                (caddr vsb))))
    ((tex--typed-exists-parts e)
     => (lambda (vsb)
          (cons (string-append "\\exists " (expr->tex (car vsb))
                               " \\in " (expr->tex (cadr vsb)) ".")
                (caddr vsb))))
    ((and (pair? e) (memq (car e) '(forall forsome)) (= (length e) 3))
     (cons (string-append (if (eq? (car e) 'forall) "\\forall " "\\exists ")
                          (expr->tex (cadr e)) ".")
           (caddr e)))
    (else #f)))

;;; A conjunction/disjunction whose one-line render is at most this many
;;; TeX characters stays on a single row; longer ones break across rows.
(define tex--inline-threshold 100)

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

;;; Render E as a list of indented TeX row-strings, breaking at the
;;; logical skeleton.  IND = current indent depth.
(define (tex--lines e ind)
  (let ((qs (tex--quant-step e)))
    (cond
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
      ((and (pair? e) (eq? (car e) 'implies) (= (length e) 3))
       (cons (string-append (tex--ind ind) (expr->tex (cadr e)) " \\Rightarrow ")
             (tex--lines (caddr e) (+ ind 1))))
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
