;;; parts.scm -- accessing the PARTS of a formula by SURFACE syntax.
;;;
;;; Scripts and Scratch-workspace code must never reach into the internal
;;; s-expression of a formula by position ((caddr (cadr f))): that couples the
;;; script to a representation accident and breaks the moment we change one
;;; (the AND-nesting, the +/binplus split, ...).  It is the representation-
;;; independence sin one level down.  This file gives the surface-conforming
;;; alternative: name parts the way the EXTERNAL syntax names them.
;;;
;;; Two entry points:
;;;
;;;   (formula-kind X)         -> a surface symbol naming the top construct
;;;                               ('implication 'conjunction 'equation
;;;                                'universal 'application 'op-application ...).
;;;
;;;   (part X step ...)        -> navigate to a part by a path of SELECTOR
;;;                               steps.  Each step is a symbol (or (sel N)):
;;;       antecedent consequent      (implication)
;;;       lhs rhs  left right        (any binary relation: = == iff in <= subset)
;;;       negand                     (negation)
;;;       conjuncts disjuncts        (-> a LIST, flattening the assoc. spine)
;;;       (conjunct N) (disjunct N)  (the N-th, 1-indexed)
;;;       binder matrix              (quantifier: bound var(s) / scope)
;;;       operator operands          (application; operands de-tuples (LIST..))
;;;       (operand N)                (the N-th operand, 1-indexed)
;;;     A singular step returns a wff; a plural step (conjuncts/disjuncts/
;;;     operands) returns a list of wffs and must be the LAST step.
;;;
;;;   (match PATTERN-STRING X) -> an alist ((?v . wff) ...) of the holes bound,
;;;                               or #f.  The pattern is surface syntax with
;;;                               `?'-sigil holes: "?P implies ?Q", "(mul(r))
;;;                               (?a, ?b)".  Reuses the macete one-way matcher
;;;                               (match-expr) -- NOT a second pattern engine.
;;;
;;; Results are wffs, so they print through the normal verbalizer and round-
;;; trip.  Selectors are total over their declared shape and error otherwise
;;; (the partial-`=' definedness discipline): (part "a=b" 'antecedent) is an
;;; error, not a silent #f.
;;;
;;; Surface contract = flat for the associative connectives (conjuncts flattens
;;; the binary right-spine d23f874 leaves); faithful for native n-ary +/* /
;;; union/intersection/cartesian (operands returns the true list); and the
;;; binary structure-op application ((MUL R) a b) is first-class (operator ->
;;; (MUL R), operands -> (a b)).  A script is insulated from all of it.
;;;
;;; Dependencies: wff.scm (wff-child/wff-formula), parser.scm (parse-string),
;;; macetes.scm (match-expr / *match-var-head*).

;;; -----------------------------------------------------------------------
;;; Coercion: accept a wff, a surface string, or a raw s-expression.

(define (parts->sexp x)
  (cond ((wff? x) (wff-formula x))
        ((string? x) (wff-formula (make-wff-from-string x)))
        ((or (pair? x) (symbol? x) (number? x)) x)
        (else (error "parts: expected a wff, string, or s-expression" x))))

;; A wff to act as the re-wrapping parent (so returned parts are wffs in the
;; same theory).  Raw-sexp input has no wff parent, so parts come back as raw
;; sexps (parts-wrap falls through); pass a wff or string to get wffs back.
(define (parts->parent x)
  (cond ((wff? x) x)
        ((string? x) (make-wff-from-string x))
        (else #f)))

(define (parts-wrap parent e)
  (if (wff? parent) (wff-child parent e) e))

;;; -----------------------------------------------------------------------
;;; Surface classification.

;; Heads with a dedicated surface role (everything else that is pair-headed is
;; an application: a predicate/function applied, or a structure op applied).
(define *parts-binary-relations* '(= == IFF IN <= SUBSET subset))

(define (formula-kind x)
  (let ((e (parts->sexp x)))
    (cond
      ((eq? e 'TRUTH) 'truth)
      ((eq? e 'FALSITY) 'falsity)
      ((symbol? e) 'atom)
      ((number? e) 'number)
      ((pair? e)
       (case (car e)
         ((IMPLIES) 'implication)
         ((IFF) 'biconditional)
         ((AND) 'conjunction)
         ((OR) 'disjunction)
         ((NOT) 'negation)
         ((=) 'equation)
         ((==) 'equivalence)
         ((IN) 'membership)
         ((<=) 'inequality)
         ((SUBSET subset) 'subset)
         ((FORALL) 'universal)
         ((FORSOME) 'existential)
         ((IOTA) 'description)
         ((+ *) 'arithmetic)
         ((UNION INTERSECTION CARTESIAN) 'set-construction)
         (else (if (pair? (car e)) 'op-application 'application))))
      (else 'unknown))))

;;; -----------------------------------------------------------------------
;;; Flattening the associative connective spine (robust to either nesting).

(define (flatten-head head e)
  (if (and (pair? e) (eq? (car e) head))
      (append (flatten-head head (cadr e)) (flatten-head head (caddr e)))
      (list e)))

;; Operands of an application, de-tupling a single explicit (LIST ...) argument
;; (the apply-tupling convention ((f) (LIST a b)) = (f a b)).
(define (operands-of e)
  (let ((args (cdr e)))
    (if (and (pair? args) (null? (cdr args))
             (pair? (car args)) (eq? (caar args) 'LIST))
        (cdr (car args))
        args)))

;;; -----------------------------------------------------------------------
;;; One navigation step.  Returns either a single sexp or (list 'PLURAL es...).

(define (parts-need e kinds what)
  (unless (and (pair? e) (memq (car e) kinds))
    (error (string-append "part: " what " expects " (symbol->string (car kinds))
                          ", got") (formula-kind e))))

(define (parts-step e step)
  (cond
    ;; indexed: (operand N) (conjunct N) (disjunct N), 1-indexed
    ((pair? step)
     (let* ((sel (car step)) (n (cadr step))
            (es (case sel
                  ((operand) (parts-need e (list (car e)) "operand")
                             (operands-of e))
                  ((conjunct) (flatten-head 'AND e))
                  ((disjunct) (flatten-head 'OR e))
                  (else (error "part: unknown indexed selector" sel)))))
       (when (or (< n 1) (> n (length es)))
         (error "part: index out of range (1-based)" step (length es)))
       (list-ref es (- n 1))))
    ((eq? step 'antecedent) (parts-need e '(IMPLIES) "antecedent") (cadr e))
    ((eq? step 'consequent) (parts-need e '(IMPLIES) "consequent") (caddr e))
    ((memq step '(lhs left))
     (parts-need e *parts-binary-relations* "lhs") (cadr e))
    ((memq step '(rhs right))
     (parts-need e *parts-binary-relations* "rhs") (caddr e))
    ((eq? step 'negand) (parts-need e '(NOT) "negand") (cadr e))
    ((eq? step 'conjuncts) (cons 'PLURAL (flatten-head 'AND e)))
    ((eq? step 'disjuncts) (cons 'PLURAL (flatten-head 'OR e)))
    ((eq? step 'binder) (parts-need e '(FORALL FORSOME IOTA) "binder") (cadr e))
    ((memq step '(matrix scope body))
     (parts-need e '(FORALL FORSOME IOTA) "matrix") (caddr e))
    ((memq step '(operator op head))
     (unless (and (pair? e) (or (pair? (car e)) (symbol? (car e))))
       (error "part: operator expects an application, got" (formula-kind e)))
     (car e))
    ((memq step '(operands args))
     (unless (pair? e) (error "part: operands expects an application, got" (formula-kind e)))
     (cons 'PLURAL (operands-of e)))
    (else (error "part: unknown selector" step))))

;;; -----------------------------------------------------------------------
;;; The navigator.

(define (part x . steps)
  (let ((parent (parts->parent x)))
    (let loop ((e (parts->sexp x)) (steps steps))
      (if (null? steps)
          (parts-wrap parent e)
          (let ((r (parts-step e (car steps))))
            (cond
              ((and (pair? r) (eq? (car r) 'PLURAL))
               (unless (null? (cdr steps))
                 (error "part: a plural selector must be the last step" (car steps)))
               (map (lambda (s) (parts-wrap parent s)) (cdr r)))
              (else (loop r (cdr steps)))))))))

;;; -----------------------------------------------------------------------
;;; Pattern matching with `?'-sigil holes.

(define (parts-hole? s)
  (and (symbol? s)
       (let ((str (symbol->string s)))
         (and (> (string-length str) 0) (char=? (string-ref str 0) #\?)))))

(define (parts-collect-holes e)
  (cond ((parts-hole? e) (list e))
        ((pair? e) (append (parts-collect-holes (car e)) (parts-collect-holes (cdr e))))
        (else '())))

(define (parts-dedup xs)
  (let loop ((xs xs) (acc '()))
    (cond ((null? xs) (reverse acc))
          ((memq (car xs) acc) (loop (cdr xs) acc))
          (else (loop (cdr xs) (cons (car xs) acc))))))

;; (match "?P implies ?Q" target) -> ((?p . wff) (?q . wff)) | #f.
;; The pattern is parsed RAW (parse-string), not validated as a wff, because a
;; hole stands for an arbitrary sub-formula/term and the template need not be a
;; standalone wff.  But we DO run expand-destructuring-quantifiers on it (the
;; same binder desugaring make-wff applies to the target): parse-string leaves
;; a typed binding as the raw (FORALL ((IN x A)) body), while the target is the
;; desugared (FORALL x (IMPLIES (IN x A) body)) -- without this they would
;; never match.  Holes pass through the desugaring untouched; applied to the
;; target too, it is a no-op (already desugared).  Holes are then matched by
;; the macete one-way matcher.
(define (match pattern-string target)
  (let* ((pat    (expand-destructuring-quantifiers (parse-string pattern-string)))
         (tgt    (expand-destructuring-quantifiers (parts->sexp target)))
         (vars   (parts-dedup (parts-collect-holes pat)))
         (parent (parts->parent target))
         (subst  (fluid-let ((*match-var-head* #t))
                   (match-expr pat tgt vars))))
    (and subst
         (map (lambda (b) (cons (car b) (parts-wrap parent (cdr b)))) subst))))
