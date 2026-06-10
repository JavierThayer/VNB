;;; wff-english.scm -- render a wff as an English sentence.
;;;
;;; Companion to expr->str (sequents.scm, symbolic surface syntax) and
;;; describe-structure (interactive.scm, structures in prose).  This one
;;; verbalizes an arbitrary FORMULA.
;;;
;;; ALTITUDE (the central design choice): verbalize the LOGICAL SKELETON --
;;; quantifiers, connectives, membership/order relations, and IS-X "sort"
;;; predicates -- into prose, but leave atomic mathematical TERMS (arithmetic,
;;; function application like d(x, z)) in SYMBOLIC form via expr->str.  A
;;; theorem is read aloud as e.g.
;;;   "for every x in A, if x is in U then there is some positive real r
;;;    such that B(x, r) is a subset of U"
;;; -- English for the structure, symbols for the algebra.  Pure prose for
;;; d(x, z) <= d(x, y) + d(y, z) would be unreadable, so terms stay symbolic.
;;;
;;; Anything with no English rendering falls back to the symbolic expr->str,
;;; so output is always faithful, never wrong -- just less prosey in spots.
;;;
;;; Entry points:
;;;   (wff->english e)     core: a raw formula sexp -> English string
;;;   (en e)               alias
;;;   (english-of 'name)   verbalize an installed theorem by name

;;; -----------------------------------------------------------------------
;;; Vocabulary.
;;;
;;; Two tables.  *english-sort* holds UNARY "sort" predicates that read as
;;; "<x> is a <phrase>"; storing the bare phrase + article lets the SAME entry
;;; serve both the predication ("eps is a positive real") and the quantifier
;;; QUALIFIER fold ("for every positive real eps").  *english-pred* holds
;;; general predicates (any arity) whose English needs all the arguments
;;; (e.g. is-open(t, V) -> "V is open in t"); these render a predication only,
;;; no qualifier fold.

(define *english-sort* (make-strong-eqv-hash-table))  ; sym -> (phrase . article)
(define *english-pred* (make-strong-eqv-hash-table))  ; sym -> (arity . proc)

(define (sym-lc s) (string->symbol (string-downcase (symbol->string s))))

(define (def-english-sort! sym phrase article)
  (hash-table-set! *english-sort* (sym-lc sym) (cons phrase article)))

(define (def-english-pred! sym arity proc)
  (hash-table-set! *english-pred* (sym-lc sym) (cons arity proc)))

;;; Unary sorts (phrase, article).  Article "" reads as an adjective.
(def-english-sort! 'pos-rr      "positive real"      "a")
(def-english-sort! 'neg-rr      "negative real"      "a")
(def-english-sort! 'nonneg-rr   "nonnegative real"   "a")
(def-english-sort! 'is-metric-space   "metric space"   "a")
(def-english-sort! 'is-group          "group"          "a")
(def-english-sort! 'is-abelian-group  "abelian group"  "an")
(def-english-sort! 'is-semigroup      "semigroup"      "a")
(def-english-sort! 'is-monoid         "monoid"         "a")
(def-english-sort! 'is-ring           "ring"           "a")
(def-english-sort! 'is-commutative-ring "commutative ring" "a")
(def-english-sort! 'is-integral-domain  "integral domain"  "an")
(def-english-sort! 'is-field          "field"          "a")
(def-english-sort! 'is-euclidean-ring "Euclidean ring" "a")
(def-english-sort! 'is-normed-field   "normed field"   "a")
(def-english-sort! 'is-complete       "complete"       "")
(def-english-sort! 'is-cauchy-seq     "Cauchy"         "")

;;; General predicates (arity . proc), proc :: list-of-arg-strings -> string.
(def-english-pred! 'in       2 (lambda (a) (string-append (car a) " is in " (cadr a))))
(def-english-pred! 'subset   2 (lambda (a) (string-append (car a) " is a subset of " (cadr a))))
(def-english-pred! '=        2 (lambda (a) (string-append (car a) " equals " (cadr a))))
(def-english-pred! '==       2 (lambda (a) (string-append (car a) " is identical to " (cadr a))))
(def-english-pred! '<=       2 (lambda (a) (string-append (car a) " is at most " (cadr a))))
(def-english-pred! '<        2 (lambda (a) (string-append (car a) " is less than " (cadr a))))
(def-english-pred! '>=       2 (lambda (a) (string-append (car a) " is at least " (cadr a))))
(def-english-pred! '>        2 (lambda (a) (string-append (car a) " is greater than " (cadr a))))
(def-english-pred! 'is-open   2 (lambda (a) (string-append (cadr a) " is open in " (car a))))
(def-english-pred! 'is-closed 2 (lambda (a) (string-append (cadr a) " is closed in " (car a))))
(def-english-pred! 'is-continuous 3
  (lambda (a) (string-append (caddr a) " is continuous from " (car a) " to " (cadr a))))
(def-english-pred! 'is-continuous-at 4
  (lambda (a) (string-append (caddr a) " is continuous at " (cadddr a))))
(def-english-pred! 'converges-to 3
  (lambda (a) (string-append (cadr a) " converges to " (caddr a) " in " (car a))))

;;; -----------------------------------------------------------------------
;;; Helpers.

;;; A term: render with the symbolic printer.
(define (term->english e) (expr->str e 0))

;;; "is a <phrase>" / "is <phrase>" predication for a unary sort entry.
(define (sort-predication x-str entry)
  (let ((phrase (car entry)) (article (cdr entry)))
    (string-append x-str " is "
                   (if (string=? article "") "" (string-append article " "))
                   phrase)))

;;; Quantifier qualifier for a unary sort entry: "positive real eps".
(define (sort-qualifier v-str entry)
  (string-append (car entry) " " v-str))

;;; Is e a unary application of a recognised sort predicate of variable v?
;;; Returns the sort entry or #f.
(define (sort-of-var e v)
  (and (pair? e) (= (length e) 2) (eq? (cadr e) v) (symbol? (car e))
       (hash-table-ref/default *english-sort* (sym-lc (car e)) #f)))

;;; Render one quantifier binding spec (from collect-quant-bindings) as the
;;; phrase that follows "for every"/"there is some".
(define (binding->english spec)
  (cond
    ;; (in v A) -> "v in A"
    ((and (pair? spec) (= (length spec) 3) (eq? (car spec) 'in) (symbol? (cadr spec)))
     (string-append (symbol->string (cadr spec)) " in " (term->english (caddr spec))))
    ;; (v) or (v1 v2 ...) unrestricted
    ((and (pair? spec) (every symbol? spec))
     (str-join (map symbol->string spec) ", "))
    (else (term->english spec))))

;;; -----------------------------------------------------------------------
;;; Core walker.

(define (wff->english e)
  (formula->english (if (wff? e) (wff-formula e) e)))

(define (en e) (wff->english e))

(define (english-of name)
  (let ((f (hash-table-ref/default *theorem-table* (sym-lc name) #f)))
    (if f (wff->english f)
        (string-append "(no installed theorem named " (symbol->string name) ")"))))

(define (formula->english e)
  (if (not (pair? e))
      (term->english e)
      (let ((h (and (symbol? (car e)) (sym-lc (car e)))))
        (cond
          ((memq h '(forall forsome)) (quantifier->english h e))
          ((and (eq? h 'and) (>= (length e) 3)) (junction->english (cdr e) " and "))
          ((and (eq? h 'or)  (>= (length e) 3)) (junction->english (cdr e) " or "))
          ((and (eq? h 'iff) (= (length e) 3)) (iff->english e))
          ((and (eq? h 'implies) (= (length e) 3)) (implies->english e))
          ((and (eq? h 'not) (= (length e) 2)) (not->english (cadr e)))
          (else (atom->english h e))))))

;;; Conjunction / disjunction: render each operand, join with sep.
(define (junction->english operands sep)
  (str-join (map formula->english operands) sep))

(define (iff->english e)
  (string-append (formula->english (cadr e))
                 " if and only if "
                 (formula->english (caddr e))))

(define (implies->english e)
  (string-append "if " (formula->english (cadr e))
                 ", then " (formula->english (caddr e))))

;;; NOT, with readable special cases for negated relations.
(define (not->english p)
  (if (pair? p)
      (let ((h (and (symbol? (car p)) (sym-lc (car p)))))
        (cond
          ((and (eq? h '=)  (= (length p) 3))
           (string-append (term->english (cadr p)) " is not equal to " (term->english (caddr p))))
          ((and (eq? h 'in) (= (length p) 3))
           (string-append (term->english (cadr p)) " is not in " (term->english (caddr p))))
          (else (string-append "it is not the case that " (formula->english p)))))
      (string-append "it is not the case that " (formula->english p))))

;;; Atomic formula: a recognised predicate, a unary sort, or symbolic fallback.
(define (atom->english h e)
  (let* ((args (cdr e))
         (pred (and h (hash-table-ref/default *english-pred* h #f)))
         (sort (and h (= (length args) 1)
                    (hash-table-ref/default *english-sort* h #f))))
    (cond
      ((and pred (= (car pred) (length args)))
       ((cdr pred) (map term->english args)))
      (sort (sort-predication (term->english (car args)) sort))
      ;; unrecognised: keep it honest -- symbolic surface form.
      (else (term->english e)))))

;;; Quantifiers, with two folds: bounded (x in A, already done by
;;; collect-quant-bindings) and unary-sort qualifier (the "positive real eps"
;;; absorption from a leading IMPLIES/AND antecedent on a single variable).
(define (quantifier->english q e)
  (let* ((result   (collect-quant-bindings q e))
         (bindings (car result))
         (body     (cdr result))
         (lead     (if (eq? q 'forall) "for every " "there is some "))
         (joiner   (if (eq? q 'forall) "" " such that ")))
    ;; Try to absorb a leading sort qualifier when there is exactly one
    ;; unrestricted binding: forall v (implies (P v) rest) and
    ;; forsome v (and (P v) rest), with P a recognised unary sort.
    (let ((fold (and (= (length bindings) 1)
                     (pair? (car bindings)) (= (length (car bindings)) 1)
                     (symbol? (caar bindings))
                     (absorb-sort q (caar bindings) body))))
      (if fold
          (string-append lead (car fold)
                         (if (eq? q 'forall) ", " " such that ")
                         (formula->english (cdr fold)))
          (string-append lead
                         (str-join (map binding->english bindings) ", ")
                         (if (eq? q 'forall) ", " joiner)
                         (formula->english body))))))

;;; If body folds as (op (P v) rest) with op matching q and P a unary sort,
;;; return (qualifier-string . rest); else #f.
(define (absorb-sort q v body)
  (and (pair? body)
       (let ((bh (and (symbol? (car body)) (sym-lc (car body)))))
         (and (= (length body) 3)
              (eq? bh (if (eq? q 'forall) 'implies 'and))
              (let ((entry (sort-of-var (cadr body) v)))
                (and entry
                     (cons (sort-qualifier (symbol->string v) entry)
                           (caddr body))))))))
