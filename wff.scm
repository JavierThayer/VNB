;;; wff.scm -- the <wff> record type (well-formed formula in a theory)
;;;
;;; A <wff> carries its raw S-expression formula, the name of its base
;;; theory, and (optionally) a snapshot of the active local-context stack.
;;;
;;; Inside sequents the contexts list is always empty -- it has been
;;; dissolved into sequent assumptions by start-proof.  The contexts
;;; field is only populated by make-wff at the interactive entry point.

(define-record-type <wff>
  (%make-concrete-wff formula theory contexts)
  concrete-wff?
  (formula   concrete-wff-formula)
  (theory    concrete-wff-theory)
  (contexts  concrete-wff-contexts))

(define wff? concrete-wff?)

(define (wff-formula w)
  (if (concrete-wff? w)
      (concrete-wff-formula w)
      (error "wff-formula: not a wff" w)))

(define (wff-theory w)
  (if (concrete-wff? w)
      (concrete-wff-theory w)
      (error "wff-theory: not a wff" w)))

(define (wff-contexts w)
  (if (concrete-wff? w)
      (concrete-wff-contexts w)
      (error "wff-contexts: not a wff" w)))

;;; Create a wff directly in a named theory with no active contexts.
;;; Used by start-proof and primitive inferences.
(define (wff-in-theory raw-formula theory-name)
  (%make-concrete-wff raw-formula theory-name '()))

;;; Create a derived wff inheriting theory from a parent, with no contexts.
;;; Used inside primitive inferences to wrap subformulas.
(define (wff-child parent raw-formula)
  (%make-concrete-wff raw-formula (wff-theory parent) '()))

;;; Two wffs are equivalent when they share the same theory and their
;;; formulas are alpha-equivalent.  (Kind is implied by the formula
;;; structure, so a kind check would be redundant.)
(define (wff-equiv? w1 w2)
  (and (equal? (wff-theory w1) (wff-theory w2))
       (alpha-equiv? (wff-formula w1) (wff-formula w2))))

;;; wff->sexp: extract the raw S-expression from a wff.
;;; Synonym for wff-formula, provided as a user-facing name.
(define wff->sexp wff-formula)

;;; -----------------------------------------------------------------------
;;; expand-destructuring-quantifiers
;;;
;;; Rewrites surface forms of FORALL/FORSOME:
;;;   (FORALL  (IN var class) body)   =>  (FORALL  var (IMPLIES (IN var class) body))
;;;   (FORSOME (IN var class) body)   =>  (FORSOME var (AND     (IN var class) body))
;;;   (FORALL  (x y ...) body)        =>  (FORALL  x (FORALL  y (... body)))
;;;   (FORSOME (x y ...) body)        =>  (FORSOME x (FORSOME y (... body)))
;;;   (FORALL  x y ... body)          =>  (FORALL  x (FORALL  y (... body)))   [4+ args]
;;;   (FORSOME x y ... body)          =>  (FORSOME x (FORSOME y (... body)))   [4+ args]
;;; Bare-symbol quantifiers are left unchanged.  Called from make-wff
;;; before validate-wff!, so the rest of the system only ever sees the
;;; single-variable form.

(define (all-symbols? lst)
  (or (null? lst)
      (and (symbol? (car lst)) (all-symbols? (cdr lst)))))

;;; Predicates for the binding-list quantifier syntax:
;;;   (FORALL ((b1) (b2) ...) body)
;;; Each bi is one of:
;;;   (var)                — unrestricted single variable
;;;   (IN var A)           — variable restricted to class A
;;;   (IN (LIST sym...) A) — tuple destructuring

(define (binding-spec? b)
  (cond
    ((not (pair? b)) #f)
    ((eq? (car b) 'IN)
     (and (= (length b) 3)
          (or (symbol? (cadr b))
              (and (pair? (cadr b))
                   (eq? (car (cadr b)) 'LIST)
                   (all-symbols? (cdr (cadr b)))))))
    ;; (var) or (var1 var2 ...) — non-empty list of symbols; 'in-headed lists
    ;; are handled above, so a leading 'in here would be a parse error.
    (else (and (not (null? b)) (not (eq? (car b) 'in)) (all-symbols? b)))))

(define (all-binding-specs? lst)
  (and (pair? lst)
       (let loop ((l lst))
         (or (null? l)
             (and (binding-spec? (car l)) (loop (cdr l)))))))

(define (nest-quantifiers q vars body)
  (if (null? vars)
      body
      `(,q ,(car vars) ,(nest-quantifiers q (cdr vars) body))))

(define (expand-destructuring-quantifiers expr)
  (cond
    ((not (pair? expr)) expr)
    (else
     (let ((mapped (cons (car expr)
                         (map expand-destructuring-quantifiers (cdr expr)))))
       (cond
         ;; (FORALL (IN (LIST x1 ... xn) A) body) — tuple destructuring
         ;; Introduces a fresh tuple var t; substitutes xi -> (NTH i t) in body.
         ((and (memq (car mapped) '(FORALL FORSOME))
               (= (length mapped) 3)
               (pair? (cadr mapped))
               (eq? (car (cadr mapped)) 'IN)
               (= (length (cadr mapped)) 3)
               (pair? (cadr (cadr mapped)))
               (eq? (car (cadr (cadr mapped))) 'LIST)
               (all-symbols? (cdr (cadr (cadr mapped)))))
          (let* ((q     (car mapped))
                 (vars  (cdr (cadr (cadr mapped))))
                 (class (caddr (cadr mapped)))
                 (body  (caddr mapped))
                 (t     (fresh-var 't `(dummy ,class ,body ,@vars)))
                 (subst-body
                  (let loop ((vs vars) (i 1) (b body))
                    (if (null? vs)
                        b
                        (loop (cdr vs) (+ i 1)
                              (subst-free (car vs) `(NTH ,i ,t) b))))))
            (case q
              ((FORALL)  `(FORALL  ,t (IMPLIES (IN ,t ,class) ,subst-body)))
              ((FORSOME) `(FORSOME ,t (AND     (IN ,t ,class) ,subst-body))))))
         ;; (FORALL (IN var class) body) — guarded-quantifier sugar
         ((and (memq (car mapped) '(FORALL FORSOME))
               (= (length mapped) 3)
               (pair? (cadr mapped))
               (eq? (car (cadr mapped)) 'IN)
               (= (length (cadr mapped)) 3)
               (symbol? (cadr (cadr mapped))))
          (let ((q     (car mapped))
                (var   (cadr  (cadr mapped)))
                (class (caddr (cadr mapped)))
                (body  (caddr mapped)))
            (case q
              ((FORALL)  `(FORALL  ,var (IMPLIES (IN ,var ,class) ,body)))
              ((FORSOME) `(FORSOME ,var (AND     (IN ,var ,class) ,body))))))
         ;; (FORALL ((b1) (b2) ...) body) — new binding-list syntax.
         ;; Each binding is (var), (sym1 sym2...), (IN var A), or (IN (LIST...) A).
         ((and (memq (car mapped) '(FORALL FORSOME))
               (= (length mapped) 3)
               (pair? (cadr mapped))
               (all-binding-specs? (cadr mapped)))
          (let* ((q     (car mapped))
                 (specs (cadr mapped))
                 (body  (caddr mapped)))
            (let loop ((ss (reverse specs)) (acc body))
              (if (null? ss)
                  acc
                  (let ((b (car ss)))
                    (loop (cdr ss)
                          (cond
                            ;; (var) or (var1 var2 ...) — unrestricted, possibly grouped
                            ;; Note: 'in is a symbol too; exclude it from this branch.
                            ((and (not (null? b)) (all-symbols? b) (not (eq? (car b) 'in)))
                             (let inner ((vs (reverse b)) (a acc))
                               (if (null? vs) a (inner (cdr vs) `(,q ,(car vs) ,a)))))
                            ;; (IN var A) — restricted
                            ((and (= (length b) 3) (eq? (car b) 'IN) (symbol? (cadr b)))
                             (case q
                               ((FORALL)  `(FORALL  ,(cadr b) (IMPLIES (IN ,(cadr b) ,(caddr b)) ,acc)))
                               ((FORSOME) `(FORSOME ,(cadr b) (AND     (IN ,(cadr b) ,(caddr b)) ,acc)))))
                            ;; (IN (LIST sym...) A) — tuple destructuring
                            ((and (= (length b) 3) (eq? (car b) 'IN)
                                  (pair? (cadr b)) (eq? (car (cadr b)) 'LIST))
                             (let* ((vars  (cdr (cadr b)))
                                    (class (caddr b))
                                    (t     (fresh-var 't `(dummy ,class ,acc ,@vars)))
                                    (subst-acc
                                     (let sub ((vs vars) (i 1) (a acc))
                                       (if (null? vs)
                                           a
                                           (sub (cdr vs) (+ i 1)
                                                (subst-free (car vs) `(NTH ,i ,t) a))))))
                               (case q
                                 ((FORALL)  `(FORALL  ,t (IMPLIES (IN ,t ,class) ,subst-acc)))
                                 ((FORSOME) `(FORSOME ,t (AND     (IN ,t ,class) ,subst-acc))))))
                            (else (error "expand-binding-list: bad spec" b q)))))))))
         ;; (FORALL (x y ...) body) — list-of-vars sugar
         ((and (memq (car mapped) '(FORALL FORSOME))
               (= (length mapped) 3)
               (pair? (cadr mapped))
               (all-symbols? (cadr mapped))
               (not (null? (cadr mapped))))
          (nest-quantifiers (car mapped) (cadr mapped) (caddr mapped)))
         ;; (FORALL x y ... body) — variadic sugar (4+ total elements)
         ((and (memq (car mapped) '(FORALL FORSOME))
               (>= (length mapped) 4)
               (all-symbols? (reverse (cdr (reverse (cdr mapped))))))
          (let* ((args  (cdr mapped))
                 (vars  (reverse (cdr (reverse args))))
                 (body  (car (reverse args))))
            (nest-quantifiers (car mapped) vars body)))
         (else mapped))))))

;;; -----------------------------------------------------------------------
;;; validate-wff!: position-typed sanity check
;;;
;;; Walks an S-expression as if it were a wff, ensuring every position
;;; receives an appropriate sub-form.  Numbers in wff positions are
;;; rejected outright.  Term-forming operator heads (CHOICE, UNION, etc.)
;;; in wff position are rejected, and wff-forming heads (AND, FORALL, etc.)
;;; in term position are rejected.  Bare symbols in wff position are
;;; rejected (only TRUTH/FALSITY are valid bare-symbol wffs).  Compound
;;; forms (P arg ...) with an unknown symbol head are accepted as predicate
;;; / function applications.

;;; Term-forming heads: anything that, in wff position with these as the
;;; head, must be rejected ("term-forming operator in wff position" error).
(define *wff-term-form-heads*
  '(UNION INTERSECTION COMPLEMENT-IN CARTESIAN FUN INJECTION IMAGE SEP COMP BIG-UNION POWER
    LIST NTH MAKE-SET LENGTH CHOICE IOTA IF TUPLES
    DOM RES PARTIAL-FUN
    apply-functoid VNB-LAMBDA
    succ_ORD LIMIT-ORD ORD-SEGMENT SUP-ORD ESUP ESUM
    CARD PROD-ORD SUM SUM-SET PROD-SET RING-PROD RING-PROD-N ZERO-RING
    MATRIX SIZE MAT ENTRY INTERVAL MATOF MATMUL
    MATADD MATNEG ZEROMAT IDENTMAT MAT-RING MATUNIT
    ELEM-F ELEM-G ELEM-H SUBMAT
    + - * recip abs conjugate succ exp sin cos
    real-part imag-part magnitude))

(define *wff-only-heads*
  '(NOT AND OR IMPLIES IFF FORALL FORSOME = == IN <= SUBSET subset))

;;; Seed the constant-head registry (expressions.scm) with every kernel
;;; term-forming head, so subst-free / free-vars never mistake one for an
;;; applied function variable.  Structure accessors and defined functions
;;; are registered later, by def-structure and theory-add-definition!.
(for-each (lambda (h) (register-constant! h 'operator))
          *wff-term-form-heads*)

;;; Warn when a binder's variable has the name of a registered operator,
;;; defined function, or functoid: an application (v ...) in the body then
;;; refers to that constant, not the bound variable -- almost always a
;;; mistake.  Accessor names (e.g. carrier `A` vs an element variable `a`)
;;; are deliberately NOT warned: binding `a` as an operand variable while
;;; `A` is a carrier accessor is a routine, correct pattern (the registry
;;; keeps `(CARR m)` meaning the accessor), and the two cannot be told apart
;;; from the S-expression anyway.
(define (warn-binder-shadowing v)
  (let ((kind (constant-head? v)))
    (if (memq kind '(operator defined-fn functoid))
        (begin
          (display ";VNB warning: binder variable ")
          (display v)
          (display " has the name of a registered ") (display kind)
          (display " -- an application (") (display v)
          (display " ...) in its scope refers to that ") (display kind)
          (display ", not the bound variable.")
          (newline)))))

(define (validate-wff! expr)
  ;; term-syms: FREE symbols seen in term position.
  ;; bound-syms: every symbol that appears in any binder anywhere (for warning).
  ;; Within a binder body, the bound variable is checked locally and is
  ;; NOT recorded in the global free sets.
  (let ((term-syms  '())
        (bound-syms '()))

    (define (note-bound! s) (set! bound-syms (cons s bound-syms)))

    ;; bound-env: alist of (sym . 'term) bindings currently in scope.
    ;; All standard binders (FORALL, FORSOME, IOTA, SEP, lambda, lambdoid) bind
    ;; class variables, so the role is uniformly 'term.

    (define (walk-wff e bound-env)
      (cond
        ((number? e)
         (error "make-wff: number in wff position" e))
        ((symbol? e)
         (cond
           ((or (eq? e 'TRUTH) (eq? e 'FALSITY)) #t)
           ((assq e bound-env)
            (error "make-wff: bound class variable used in wff position" e))
           (else
            (error "make-wff: bare symbol in wff position (not a valid wff)" e))))
        ((pair? e)
         (case (car e)
           ((NOT)
            (or (= (length e) 2) (error "make-wff: NOT arity" e))
            (walk-wff (cadr e) bound-env))
           ((AND OR IMPLIES IFF)
            (or (= (length e) 3) (error "make-wff: connective arity" e))
            (walk-wff (cadr e) bound-env)
            (walk-wff (caddr e) bound-env))
           ((= == IN <= SUBSET subset)
            (or (= (length e) 3) (error "make-wff: predicate arity" e))
            (walk-term (cadr e) bound-env)
            (walk-term (caddr e) bound-env))
           ((FORALL FORSOME)
            (or (= (length e) 3) (error "make-wff: quantifier arity" e))
            (or (symbol? (cadr e)) (error "make-wff: bound variable not a symbol" e))
            (note-bound! (cadr e))
            (warn-binder-shadowing (cadr e))
            (walk-wff (caddr e) (cons (cons (cadr e) 'term) bound-env)))
           (else
            (cond
              ((memq (car e) *wff-term-form-heads*)
               (error "make-wff: term-forming operator in wff position" e))
              (else
               ;; Predicate application (P arg ...): args are terms.
               (for-each (lambda (a) (walk-term a bound-env)) (cdr e)))))))
        (else
         (error "make-wff: unrecognized expression in wff position" e))))

    (define (walk-term e bound-env)
      (cond
        ((number? e) #t)
        ((symbol? e)
         (cond
           ((or (eq? e 'TRUTH) (eq? e 'FALSITY))
            (error "make-wff: TRUTH/FALSITY in term position" e))
           ((assq e bound-env)
            ;; Bound class variable used in term position — fine.
            #t)
           (else (set! term-syms (cons e term-syms)))))
        ;; Functoid record: validate each domain and the body
        ((functoid? e)
         (let* ((bindings (functoid-bindings e))
                (bvars    (map car bindings))
                (env*     (fold-left (lambda (env bv)
                                       (note-bound! bv)
                                       (cons (cons bv 'term) env))
                                     bound-env bvars)))
           (for-each (lambda (b) (walk-term (cdr b) bound-env)) bindings)
           (walk-term (functoid-body e) env*)))
        ((pair? e)
         (case (car e)
           ((UNION INTERSECTION)
            ;; n-ary (>= 2 args) per manual ch-expressions: union/intersection
            ;; promised as n-ary constructors; the kernel rules
            ;; pi-union-intro!/pi-union-elim! and pi-intersection-intro!/-elim!
            ;; already handle arbitrary arity.  See REVIEW.md D-6.
            (or (>= (length e) 3) (error "make-wff: union/intersection needs >= 2 args" e))
            (for-each (lambda (a) (walk-term a bound-env)) (cdr e)))
           ((COMPLEMENT-IN)
            ;; Relative complement A \ B; binary.  See REVIEW.md D-6.
            (or (= (length e) 3) (error "make-wff: COMPLEMENT-IN arity" e))
            (walk-term (cadr e) bound-env)
            (walk-term (caddr e) bound-env))
           ((FUN)
            (cond
              ((= (length e) 2)                          ; (FUN A) — domain only
               (walk-term (cadr e) bound-env))
              ((= (length e) 3)                          ; (FUN A B) — domain + codomain
               (walk-term (cadr e) bound-env)
               (walk-term (caddr e) bound-env))
              (else (error "make-wff: FUN takes 1 or 2 arguments" e))))
           ((CHOICE TUPLES MAKE-SET LENGTH)
            (or (= (length e) 2) (error "make-wff: unary term arity" e))
            (walk-term (cadr e) bound-env))
           ((POWER)
            (cond
              ((= (length e) 2) (walk-term (cadr e) bound-env))
              ((= (length e) 3)
               (walk-term (cadr e) bound-env)
               (walk-term (caddr e) bound-env))
              (else (error "make-wff: POWER arity (1 = power set, 2 = exponent)" e))))
           ((CARTESIAN LIST)
            (for-each (lambda (a) (walk-term a bound-env)) (cdr e)))
           ((NTH)
            (or (= (length e) 3) (error "make-wff: NTH arity" e))
            (walk-term (cadr e) bound-env)
            (walk-term (caddr e) bound-env))
           ((SEP)
            (or (= (length e) 4) (error "make-wff: SEP arity" e))
            (or (symbol? (cadr e)) (error "make-wff: SEP bound var not symbol" e))
            (note-bound! (cadr e))
            (let ((env* (cons (cons (cadr e) 'term) bound-env)))
              (walk-term (caddr e) env*)
              (walk-wff  (cadddr e) env*)))
           ((BIG-UNION)
            ;; (BIG-UNION z A body) — body is a term (the set f(z)), unlike SEP.
            (or (= (length e) 4) (error "make-wff: BIG-UNION arity" e))
            (or (symbol? (cadr e)) (error "make-wff: BIG-UNION bound var not symbol" e))
            (note-bound! (cadr e))
            (let ((env* (cons (cons (cadr e) 'term) bound-env)))
              (walk-term (caddr e)  bound-env)   ; A in outer scope
              (walk-term (cadddr e) env*)))      ; body sees bound var
           ((COMP)
            (or (= (length e) 3) (error "make-wff: COMP arity" e))
            (or (symbol? (cadr e)) (error "make-wff: COMP bound var not symbol" e))
            (note-bound! (cadr e))
            (walk-wff (caddr e) (cons (cons (cadr e) 'term) bound-env)))
           ((IOTA)
            (or (= (length e) 3) (error "make-wff: IOTA arity" e))
            (or (symbol? (cadr e)) (error "make-wff: IOTA bound var not symbol" e))
            (note-bound! (cadr e))
            (walk-wff (caddr e) (cons (cons (cadr e) 'term) bound-env)))
           ((IF)
            ;; (IF p a b) — p is a wff (the condition), a/b are terms.
            ;; Non-binding: the branches see the same environment.
            (or (= (length e) 4) (error "make-wff: IF arity" e))
            (walk-wff  (cadr e)   bound-env)
            (walk-term (caddr e)  bound-env)
            (walk-term (cadddr e) bound-env))
           ((VNB-LAMBDA)
            (or (= (length e) 3) (error "make-wff: VNB-LAMBDA arity" e))
            (let ((bvars (vnb-lambda-bvars (cadr e))))
              (for-each (lambda (bv)
                          (or (symbol? bv)
                              (error "make-wff: VNB-LAMBDA bound var not symbol" e))
                          (note-bound! bv))
                        bvars)
              (let ((env* (fold-left (lambda (env bv) (cons (cons bv 'term) env))
                                     bound-env bvars)))
                (walk-term (caddr e) env*))))
           ((apply-functoid)
            ;; (apply-functoid f arg ...) — f is a functoid or term; all are terms
            (or (>= (length e) 3) (error "make-wff: apply-functoid arity" e))
            (for-each (lambda (a) (walk-term a bound-env)) (cdr e)))
           ((+ - * recip abs conjugate succ)
            (for-each (lambda (a) (walk-term a bound-env)) (cdr e)))
           ;; Wff-forming heads in term position are an error.
           ((NOT AND OR IMPLIES IFF FORALL FORSOME = == IN <= SUBSET subset)
            (error "make-wff: wff-forming operator in term position" e))
           (else
            ;; Function application (f arg ...).  If the head is itself a
            ;; pair (e.g. ((MUL m) a b)) it is also a term and must be
            ;; walked, so any free symbol in head position is detected.
            (let ((h (car e)))
              (when (pair? h) (walk-term h bound-env)))
            (for-each (lambda (a) (walk-term a bound-env)) (cdr e)))))
        (else
         (error "make-wff: unrecognized expression in term position" e))))

    ;; Top-level: must be a wff.
    (walk-wff expr '())

    ;; Warning: any name that is both bound somewhere and free elsewhere.
    (let ((warned '()))
      (for-each (lambda (s)
                  (when (and (memq s term-syms) (not (memq s warned)))
                    (display ";; warning: symbol ")
                    (write s)
                    (display " is both bound (in some binder) and free in this formula\n")
                    (set! warned (cons s warned))))
                bound-syms))))
