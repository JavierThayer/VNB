;;; expressions.scm -- FOL expressions over VNB-style set theory
;;;
;;; Syntax (all prefix S-expressions, except <functoid> records):
;;;
;;;   Formulas:
;;;     TRUTH, FALSITY
;;;     (NOT p)
;;;     (AND p q)
;;;     (OR p q)
;;;     (IMPLIES p q)
;;;     (IFF p q)
;;;     (FORALL x p)
;;;     (FORSOME x p)
;;;     (= a b)                            -- strict equality
;;;     (== a b)                           -- quasi-equality
;;;     (IN a b)                           -- membership
;;;     (IS-SET a)                         -- a is a set  (defined: (IN a SET))
;;;
;;;   Class terms:
;;;     symbol                             -- variable or constant
;;;     (UNION A1 A2 ... An)               -- n-ary union (n >= 2)
;;;     (INTERSECTION A1 A2 ... An)        -- n-ary intersection (n >= 2)
;;;     (COMPLEMENT-IN a b)                -- relative complement a \ b
;;;     (CARTESIAN A1 A2 ... An)           -- n-ary Cartesian product (n >= 0)
;;;     (FUN a b)                          -- function space a -> b
;;;     (SEP x a p)                        -- { x in a | p }
;;;     (BIG-UNION z A body)               -- big-union over a family of sets;
;;;                                           z bound in body, A is index class
;;;                                           = union_{z in A} body
;;;     (POWER a)                          -- power set
;;;     (LIST e1 e2 ... en)                -- ordered n-tuple (n >= 0)
;;;     (NTH k e)                          -- k-th component (1-indexed)
;;;     (MAKE-SET L)                       -- set of elements of tuple L; {a,b,c} sugar
;;;     (LENGTH L)                         -- length of tuple L (a natural number)
;;;     (CHOICE A)                         -- primitive choice: an element of A
;;;     (IOTA x p)                         -- definite description: the unique x with p(x)
;;;     <functoid> record                  -- lambda/lambdoid binder (see below)
;;;     (apply-functoid f arg ...)         -- apply a functoid to arguments

;;; -----------------------------------------------------------------------
;;; Functoid record type
;;;
;;; A FUNCTOID is a named tagged structure (not a pure S-expression).
;;; kind     : 'lambda   — domain must be a SET (produces element of FUN)
;;;          : 'lambdoid — domain may be any class
;;; bindings : list of (var . domain-expr) pairs, one per bound variable
;;; body     : body expression (S-expression or containing functoids)
;;;
;;; Application: (apply-functoid f arg1 arg2 ...) where f is a <functoid>
;;; or a term that evaluates to one.  For ordinary (non-functoid) function
;;; application the existing (f arg ...) form is retained.

(define-record-type <functoid>
  (%make-functoid kind bindings body)
  functoid?
  (kind     functoid-kind)      ; 'lambda | 'lambdoid
  (bindings functoid-bindings)  ; ((var . dom) ...)
  (body     functoid-body))

(define (make-functoid kind bindings body)
  (%make-functoid kind bindings body))

(define (apply-functoid-expr? e)
  (and (pair? e) (eq? (car e) 'apply-functoid)))

;;; -----------------------------------------------------------------------
;;; Recognizers

(define (formula? e)
  (or (eq? e 'TRUTH)
      (eq? e 'FALSITY)
      (and (pair? e)
           (case (car e)
             ((NOT)         (and (= (length e) 2) (formula? (cadr e))))
             ((AND OR IMPLIES IFF)
              (and (= (length e) 3) (formula? (cadr e)) (formula? (caddr e))))
             ((FORALL FORSOME)
              (and (= (length e) 3) (symbol? (cadr e)) (formula? (caddr e))))
             ((= == IN)    #t)
             (else #f)))))

(define (term? e)
  (or (symbol? e)
      (number? e)
      (functoid? e)
      (and (pair? e)
           (memq (car e) '(UNION INTERSECTION COMPLEMENT-IN CARTESIAN
                           FUN SEP BIG-UNION POWER
                           LIST NTH MAKE-SET LENGTH CHOICE IOTA IF TUPLES
                           apply-functoid)))))

;;; -----------------------------------------------------------------------
;;; Constructors

(define (make-not p)          `(NOT ,p))
(define (make-and p q)        `(AND ,p ,q))
(define (make-or p q)         `(OR ,p ,q))
(define (make-implies p q)    `(IMPLIES ,p ,q))
(define (make-iff p q)        `(IFF ,p ,q))
(define (make-forall x p)     `(FORALL ,x ,p))
(define (make-forsome x p)    `(FORSOME ,x ,p))
(define (make-= a b)          `(= ,a ,b))
(define (make-in a b)         `(IN ,a ,b))
(define (make-is-set a)       (make-in a 'SET))  ; formula: a ∈ SET
(define (make-set L)          `(MAKE-SET ,L))     ; term: set of elements of tuple L
(define (make-union a b)      `(UNION ,a ,b))
(define (make-intersection a b) `(INTERSECTION ,a ,b))
(define (make-complement-in a b) `(COMPLEMENT-IN ,a ,b))
(define (make-fun a b)        `(FUN ,a ,b))
(define (make-sep x a p)      `(SEP ,x ,a ,p))
(define (make-big-union z a body) `(BIG-UNION ,z ,a ,body))
(define (make-power a)        `(POWER ,a))

;;; N-ary constructors
(define (make-cartesian . sets)  (cons 'CARTESIAN sets))
(define (make-list . elems)      (cons 'LIST elems))
(define (make-nth k e)           `(NTH ,k ,e))

;;; CHOICE / IOTA / IF constructors
(define (make-choice a)  `(CHOICE ,a))
(define (make-iota x p)  `(IOTA ,x ,p))
;;; (IF p a b) — term: a when wff p holds, b otherwise.  Non-binding.
(define (make-if p a b)  `(IF ,p ,a ,b))

;;; Functoid application constructor
(define (make-apply-functoid f . args)
  (cons 'apply-functoid (cons f args)))

;;; TUPLES constructor: finite sequences of elements from a class
(define (make-tuples a)   `(TUPLES ,a))
(define (tuples-arg e)    (cadr e))    ; (TUPLES A) -> A

;;; MAKE-SET constructor: set of elements of a tuple
(define (make-set-arg e)  (cadr e))    ; (MAKE-SET L) -> L

;;; LENGTH constructor: number of elements in a tuple
(define (make-length a)   `(LENGTH ,a))
(define (length-arg e)    (cadr e))    ; (LENGTH L) -> L

;;; Accessors
(define (connective e)       (car e))
(define (not-body e)         (cadr e))
(define (binary-left e)      (cadr e))
(define (binary-right e)     (caddr e))
(define (quantifier-var e)   (cadr e))
(define (quantifier-body e)  (caddr e))

;;; Application terms  (f a1 ... an): operator head + 1-indexed arguments.
;;; opr / arg replace ad-hoc (car ...) / (cadr ...) pawing when tearing apart a
;;; function application -- e.g. for ((act s) z x):  (opr e) = (act s),
;;; (arg e) = z (the first argument), (arg-ref e 2) = x, (args e) = (z x).
(define (opr e)         (car e))         ; operator / head
(define (args e)        (cdr e))         ; argument list
(define (arg-ref e k)   (list-ref e k))  ; k-th argument, 1-indexed (pos 0 = opr)
(define (arg e)         (arg-ref e 1))   ; first argument

;;; For LIST and CARTESIAN: the arguments are (cdr expr)
(define (list-elems e)        (cdr e))   ; (LIST a b c) -> (a b c)
(define (cartesian-sets e)    (cdr e))   ; (CARTESIAN A B C) -> (A B C)
(define (nth-index e)         (cadr e))  ; (NTH k x) -> k
(define (nth-expr e)          (caddr e)) ; (NTH k x) -> x

;;; -----------------------------------------------------------------------
;;; VNB-LAMBDA binding spec
;;;
;;; The symbolic form (VNB-LAMBDA <bind-spec> body) admits two shapes:
;;;   <bind-spec> = symbol            -- single binder
;;;               | (LIST x y z ...)  -- multi-var binder
;;; Used in raw S-expression axioms (algebraic.scm RING-PROD body, complex.scm
;;; CC-RING/CC-MS, sequences.scm sum-left-scalar) where the parser is not run.
;;; The parsed user-string form `lambda([x in nn], body)` becomes a <functoid>
;;; record instead and is handled separately above.

(define (vnb-lambda-bvars bind-spec)
  (cond ((symbol? bind-spec) (list bind-spec))
        ((and (pair? bind-spec) (eq? (car bind-spec) 'LIST))
         (cdr bind-spec))
        (else
         (error "vnb-lambda-bvars: malformed binding spec" bind-spec))))

;;; -----------------------------------------------------------------------
;;; Free variables

(define (free-vars expr)
  (cond
    ((symbol? expr) (list expr))
    ((number? expr) '())
    ((eq? expr 'TRUTH)   '())
    ((eq? expr 'FALSITY) '())
    ((functoid? expr)
     ;; Free in domains (outer scope) + free in body minus bound vars
     (let* ((bindings (functoid-bindings expr))
            (bvars    (map car bindings))
            (dom-fvs  (fold-vars (map (lambda (b) (free-vars (cdr b))) bindings)))
            (body-fvs (fold-left (lambda (vs bv) (remove bv vs))
                                  (free-vars (functoid-body expr))
                                  bvars)))
       (union-vars dom-fvs body-fvs)))
    ((pair? expr)
     (case (car expr)
       ((NOT CHOICE TUPLES MAKE-SET LENGTH)
        (free-vars (cadr expr)))
       ((POWER)
        ;; arity 2: power set; arity 3: exponentiation
        (fold-vars (map free-vars (cdr expr))))
       ((IF)
        ;; (IF p a b) — p a wff, a/b terms; non-binding, recurse into all three
        (fold-vars (map free-vars (cdr expr))))
       ((AND OR IMPLIES IFF = == IN COMPLEMENT-IN)
        (union-vars (free-vars (cadr expr)) (free-vars (caddr expr))))
       ((FUN)
        ;; arity 2: (FUN A) — unary domain-only;
        ;; arity 3: (FUN A B) — binary domain+codomain.
        (fold-vars (map free-vars (cdr expr))))
       ((FORALL FORSOME IOTA)
        (remove (cadr expr) (free-vars (caddr expr))))
       ((SEP)
        (union-vars (free-vars (caddr expr))
                    (remove (cadr expr) (free-vars (cadddr expr)))))
       ((BIG-UNION)
        ;; (BIG-UNION z A body) — z bound in body, free in A
        (union-vars (free-vars (caddr expr))
                    (remove (cadr expr) (free-vars (cadddr expr)))))
       ((VNB-LAMBDA)
        ;; (VNB-LAMBDA bind-spec body) — bind-spec hides its names in body.
        (let ((bvars (vnb-lambda-bvars (cadr expr))))
          (fold-left (lambda (vs bv) (remove bv vs))
                     (free-vars (caddr expr))
                     bvars)))
       ;; N-ary: CARTESIAN, LIST, UNION, INTERSECTION — union over all arguments
       ((CARTESIAN LIST UNION INTERSECTION)
        (fold-vars (map free-vars (cdr expr))))
       ;; NTH: (NTH k e) — k is a number (no vars), recurse into e
       ((NTH)
        (free-vars (caddr expr)))
       (else
        ;; General compound (h arg ...).  A compound head is collected.
        ;; A symbol head is free iff it is NOT a registered constant: an
        ;; applied function variable (f x) has f free; an operator/accessor
        ;; application (MUL m), (succ n) does not.  The constant-head
        ;; registry breaks the case-fold tie between accessor `A` and a
        ;; bound variable `a`.
        (let ((h (car expr)))
          (fold-vars (cons (cond ((pair? h) (free-vars h))
                                 ((and (symbol? h) (not (constant-head? h)))
                                  (list h))
                                 (else '()))
                           (map free-vars (cdr expr))))))))
    (else '())))

(define (fold-vars var-lists)
  (if (null? var-lists)
      '()
      (union-vars (car var-lists) (fold-vars (cdr var-lists)))))

(define (union-vars xs ys)
  (cond ((null? xs) ys)
        ((member (car xs) ys) (union-vars (cdr xs) ys))
        (else (cons (car xs) (union-vars (cdr xs) ys)))))

(define (remove x lst)
  (filter (lambda (y) (not (eq? y x))) lst))

;;; -----------------------------------------------------------------------
;;; Constant-head registry
;;;
;;; A symbol at the head of a compound term (h arg ...) is either a
;;; CONSTANT -- a kernel operator, a structure accessor, a defined
;;; function/constant, a functoid, or a predicate -- or a VARIABLE: a
;;; function-valued bound variable applied to arguments.  subst-free and
;;; free-vars must tell them apart: a constant head is never a free
;;; variable and is never substituted; a variable head is both.
;;;
;;; Every constant head is registered here with a kind tag; any unregistered
;;; symbol is treated as a variable.  Populated at load time by: wff.scm
;;; (kernel operators), def-structure (accessors), theory-add-definition!
;;; (defined functions), def-functoid (functoids), def-predicate.
;;;
;;; Because the reader case-folds symbols, a bound variable whose name
;;; coincides with a registered constant cannot be applied as a function
;;; (the head reads as the constant).  warn-binder-shadowing warns on that.
;;;
;;; kind in {operator accessor defined-fn functoid predicate}

(define *constant-registry* (make-equal-hash-table))

(define (register-constant! sym kind)
  (if (symbol? sym)
      (hash-table-set! *constant-registry* sym kind))
  sym)

;;; Returns the kind of sym if it is a registered constant head, else #f.
(define (constant-head? sym)
  (and (symbol? sym)
       (hash-table-ref/default *constant-registry* sym #f)))

;;; -----------------------------------------------------------------------
;;; Substitution

(define (subst-free x replacement expr)
  (cond
    ((symbol? expr)
     (if (eq? expr x) replacement expr))
    ((number? expr) expr)
    ((eq? expr 'TRUTH)   'TRUTH)
    ((eq? expr 'FALSITY) 'FALSITY)
    ((functoid? expr)
     (let* ((bindings (functoid-bindings expr))
            (bvars    (map car bindings))
            ;; Always substitute x in domain expressions (outer scope)
            (new-doms (map (lambda (b)
                             (cons (car b) (subst-free x replacement (cdr b))))
                           bindings)))
       (if (member x bvars)
           ;; x is bound: leave body alone
           (make-functoid (functoid-kind expr) new-doms (functoid-body expr))
           ;; x is free in body: rename any bvar that occurs free in replacement
           (let* ((repl-fvs  (free-vars replacement))
                  (fresh-map (filter (lambda (x) x)
                               (map (lambda (bv)
                                      (and (member bv repl-fvs)
                                           (cons bv (fresh-var bv (functoid-body expr) replacement))))
                                    bvars)))
                  ;; Rename captures in body
                  (body* (fold-left (lambda (b pair)
                                      (subst-free (car pair) (cdr pair) b))
                                    (functoid-body expr)
                                    fresh-map))
                  ;; Update bvars to their possibly-renamed versions
                  (new-bvars (map (lambda (bv)
                                    (let ((r (assq bv fresh-map)))
                                      (if r (cdr r) bv)))
                                  bvars))
                  (new-body  (subst-free x replacement body*)))
             (make-functoid (functoid-kind expr)
                            (map cons new-bvars (map cdr new-doms))
                            new-body)))))
    ((pair? expr)
     (case (car expr)
       ((NOT CHOICE TUPLES MAKE-SET LENGTH)
        (list (car expr) (subst-free x replacement (cadr expr))))
       ((POWER)
        ;; arity 2 = power set, arity 3 = exponentiation; recurse into all args
        (cons (car expr)
              (map (lambda (a) (subst-free x replacement a)) (cdr expr))))
       ((IF)
        ;; (IF p a b) — non-binding; recurse into condition and both branches
        (cons 'IF (map (lambda (a) (subst-free x replacement a)) (cdr expr))))
       ((AND OR IMPLIES IFF = == IN COMPLEMENT-IN)
        (list (car expr)
              (subst-free x replacement (cadr expr))
              (subst-free x replacement (caddr expr))))
       ((FUN)
        ;; arity 2: (FUN A); arity 3: (FUN A B); recurse into all args
        (cons (car expr)
              (map (lambda (a) (subst-free x replacement a)) (cdr expr))))
       ((FORALL FORSOME IOTA)
        (let ((bv   (cadr expr))
              (body (caddr expr)))
          (cond
            ((eq? bv x) expr)
            ((member bv (free-vars replacement))
             (let ((fresh (fresh-var bv body replacement)))
               (list (car expr) fresh
                     (subst-free x replacement (subst-free bv fresh body)))))
            (else
             (list (car expr) bv (subst-free x replacement body))))))
       ((SEP)
        (let ((bv (cadr expr)) (a (caddr expr)) (p (cadddr expr)))
          (cond
            ((eq? bv x)
             `(SEP ,bv ,(subst-free x replacement a) ,p))
            ((member bv (free-vars replacement))
             (let ((fresh (fresh-var bv p replacement)))
               `(SEP ,fresh
                     ,(subst-free x replacement a)
                     ,(subst-free x replacement (subst-free bv fresh p)))))
            (else
             `(SEP ,bv
                   ,(subst-free x replacement a)
                   ,(subst-free x replacement p))))))
       ((BIG-UNION)
        ;; (BIG-UNION z A body) — z bound in body, free in A.  Mirrors SEP.
        (let ((bv (cadr expr)) (a (caddr expr)) (body (cadddr expr)))
          (cond
            ((eq? bv x)
             `(BIG-UNION ,bv ,(subst-free x replacement a) ,body))
            ((member bv (free-vars replacement))
             (let ((fresh (fresh-var bv body replacement)))
               `(BIG-UNION ,fresh
                           ,(subst-free x replacement a)
                           ,(subst-free x replacement (subst-free bv fresh body)))))
            (else
             `(BIG-UNION ,bv
                         ,(subst-free x replacement a)
                         ,(subst-free x replacement body))))))
       ((VNB-LAMBDA)
        ;; (VNB-LAMBDA bind-spec body); rename clashing bvars to avoid capture.
        (let* ((bind-spec (cadr expr))
               (body      (caddr expr))
               (bvars     (vnb-lambda-bvars bind-spec)))
          (cond
            ((member x bvars) expr)            ; x is bound — leave alone
            (else
             (let* ((repl-fvs  (free-vars replacement))
                    (clashing  (filter (lambda (bv) (member bv repl-fvs)) bvars))
                    (rename    (map (lambda (bv) (cons bv (fresh-var bv body replacement)))
                                    clashing))
                    (body*     (fold-left (lambda (b pair)
                                            (subst-free (car pair) (cdr pair) b))
                                          body rename))
                    (new-bvars (map (lambda (bv)
                                      (let ((r (assq bv rename)))
                                        (if r (cdr r) bv)))
                                    bvars))
                    (new-bind  (if (symbol? bind-spec)
                                   (car new-bvars)
                                   (cons 'LIST new-bvars))))
               (list 'VNB-LAMBDA new-bind
                     (subst-free x replacement body*)))))))
       ;; N-ary: recurse into every argument
       ((CARTESIAN LIST UNION INTERSECTION)
        (cons (car expr)
              (map (lambda (arg) (subst-free x replacement arg)) (cdr expr))))
       ;; NTH: (NTH k e) — leave k alone, recurse into e
       ((NTH)
        `(NTH ,(cadr expr) ,(subst-free x replacement (caddr expr))))
       (else
        ;; General compound (h arg ...).  A compound head is substituted
        ;; into so ((MUL m) a b) instantiates `m`.  A symbol head is
        ;; substituted iff it is the variable x AND not a registered
        ;; constant: an applied function variable (x arg) becomes
        ;; (replacement arg); an operator/accessor head (MUL m), (A m) is
        ;; passed through.  The registry breaks the accessor/variable
        ;; case-fold tie.
        (let ((h (car expr)))
          (cons (cond ((pair? h) (subst-free x replacement h))
                      ((and (symbol? h) (eq? h x) (not (constant-head? h)))
                       replacement)
                      (else h))
                (map (lambda (arg) (subst-free x replacement arg))
                     (cdr expr)))))))
    (else expr)))

;;; (REVIEW.md G-8) MONOTONICITY INVARIANT for *fresh-counter*:
;;; The counter is incremented on every call and is NEVER reset.  This
;;; monotonicity is the implicit safety net behind S-6/S-14: even if a
;;; caller forgets to pass an avoid-expr, the counter alone makes
;;; cross-call name reuse vanishingly unlikely.  Snapshot/restore
;;; testing fixtures, REPL state resets, or any code that rolls the
;;; counter backwards would break this guarantee silently.  Do NOT
;;; reset it under any circumstance.
(define *fresh-counter* 0)

;;; (fresh-var hint . avoid-exprs)
;;;   Returns a fresh symbol whose name is `<hint>_<n>` where n is taken from
;;;   the global counter (which always advances).  The candidate is rejected
;;;   if it appears in (free-vars e) for ANY expression e in avoid-exprs.
;;;   Pass every expression that the fresh name must not collide with —
;;;   typically the body, plus the substitution's replacement (subst-free) or
;;;   the surrounding sequent's assumptions and goal (eigenvariable rules).
;;;
;;;   The global counter is monotonic and is the *only* defense against
;;;   accidental name re-use across calls; do NOT reset it.
(define (fresh-var hint . avoid-exprs)
  (let ((forbidden (apply append (map free-vars avoid-exprs))))
    (let loop ((n *fresh-counter*))
      (set! *fresh-counter* (+ *fresh-counter* 1))
      (let ((candidate (string->symbol
                        (string-append (symbol->string hint) "_"
                                       (number->string n)))))
        (if (member candidate forbidden)
            (loop (+ n 1))
            candidate)))))

;;; -----------------------------------------------------------------------
;;; Alpha-equivalence

(define (alpha-equiv? e1 e2)
  (alpha-equiv-under? e1 e2 '()))

(define (alpha-equiv-under? e1 e2 env)
  (cond
    ;; Functoid records
    ((and (functoid? e1) (functoid? e2))
     (let ((b1 (functoid-bindings e1)) (b2 (functoid-bindings e2)))
       (and (eq? (functoid-kind e1) (functoid-kind e2))
            (= (length b1) (length b2))
            ;; Domain expressions (outer scope, no new bindings)
            (let loop-doms ((bl1 b1) (bl2 b2))
              (or (null? bl1)
                  (and (alpha-equiv-under? (cdar bl1) (cdar bl2) env)
                       (loop-doms (cdr bl1) (cdr bl2)))))
            ;; Body with binding vars renamed
            (let* ((vars1 (map car b1))
                   (vars2 (map car b2))
                   (env*  (append (map cons vars1 vars2) env)))
              (alpha-equiv-under? (functoid-body e1) (functoid-body e2) env*)))))
    ((or (functoid? e1) (functoid? e2)) #f)
    ((symbol? e1)
     (let ((mapped (assq e1 env)))
       (if mapped
           (eq? (cdr mapped) e2)
           (and (symbol? e2) (eq? e1 e2)))))
    ((number? e1)
     (and (number? e2) (= e1 e2)))
    ((and (eq? e1 'TRUTH)   (eq? e2 'TRUTH))   #t)
    ((and (eq? e1 'FALSITY) (eq? e2 'FALSITY)) #t)
    ((and (pair? e1) (pair? e2) (eq? (car e1) (car e2)))
     (case (car e1)
       ((NOT CHOICE TUPLES MAKE-SET LENGTH)
        (alpha-equiv-under? (cadr e1) (cadr e2) env))
       ((POWER)
        (and (= (length e1) (length e2))
             (let loop ((a1 (cdr e1)) (a2 (cdr e2)))
               (or (null? a1)
                   (and (alpha-equiv-under? (car a1) (car a2) env)
                        (loop (cdr a1) (cdr a2)))))))
       ((IF)
        ;; (IF p a b) — non-binding; componentwise
        (and (alpha-equiv-under? (cadr e1)   (cadr e2)   env)
             (alpha-equiv-under? (caddr e1)  (caddr e2)  env)
             (alpha-equiv-under? (cadddr e1) (cadddr e2) env)))
       ((AND OR IMPLIES IFF = == IN COMPLEMENT-IN)
        (and (alpha-equiv-under? (cadr e1)  (cadr e2)  env)
             (alpha-equiv-under? (caddr e1) (caddr e2) env)))
       ((FUN)
        ;; arity 2 or 3 — same length and pairwise alpha-equiv
        (and (= (length e1) (length e2))
             (let loop ((a1 (cdr e1)) (a2 (cdr e2)))
               (or (null? a1)
                   (and (alpha-equiv-under? (car a1) (car a2) env)
                        (loop (cdr a1) (cdr a2)))))))
       ((FORALL FORSOME IOTA)
        (alpha-equiv-under? (caddr e1) (caddr e2)
                            (cons (cons (cadr e1) (cadr e2)) env)))
       ((SEP)
        (and (alpha-equiv-under? (caddr e1) (caddr e2) env)
             (alpha-equiv-under? (cadddr e1) (cadddr e2)
                                 (cons (cons (cadr e1) (cadr e2)) env))))
       ((BIG-UNION)
        (and (alpha-equiv-under? (caddr e1) (caddr e2) env)
             (alpha-equiv-under? (cadddr e1) (cadddr e2)
                                 (cons (cons (cadr e1) (cadr e2)) env))))
       ((VNB-LAMBDA)
        ;; Multi-var binder; allow cross-shape comparison via vnb-lambda-bvars.
        (let ((bv1 (vnb-lambda-bvars (cadr e1)))
              (bv2 (vnb-lambda-bvars (cadr e2))))
          (and (= (length bv1) (length bv2))
               (alpha-equiv-under? (caddr e1) (caddr e2)
                                   (append (map cons bv1 bv2) env)))))
       ;; N-ary: componentwise, same length required
       ((CARTESIAN LIST UNION INTERSECTION)
        (and (= (length e1) (length e2))
             (let loop ((a1 (cdr e1)) (a2 (cdr e2)))
               (or (null? a1)
                   (and (alpha-equiv-under? (car a1) (car a2) env)
                        (loop (cdr a1) (cdr a2)))))))
       ;; NTH: index must match, recurse into expression
       ((NTH)
        (and (equal? (cadr e1) (cadr e2))
             (alpha-equiv-under? (caddr e1) (caddr e2) env)))
       (else
        ;; apply-functoid and general compound: pairwise alpha-equiv args
        ;; For apply-functoid, cadr is a <functoid>; handled by functoid? branch above
        (and (= (length e1) (length e2))
             (let loop ((a1 (cdr e1)) (a2 (cdr e2)))
               (or (null? a1)
                   (and (alpha-equiv-under? (car a1) (car a2) env)
                        (loop (cdr a1) (cdr a2))))))))  )
    ;; Compound (non-symbol) head: e.g. ((MUL m) x y) — eq? on (car) fails
    ;; for separately-allocated pairs, so handle recursively here.
    ((and (pair? e1) (pair? e2))
     (and (alpha-equiv-under? (car e1) (car e2) env)
          (= (length e1) (length e2))
          (let loop ((a1 (cdr e1)) (a2 (cdr e2)))
            (or (null? a1)
                (and (alpha-equiv-under? (car a1) (car a2) env)
                     (loop (cdr a1) (cdr a2)))))))
    (else #f)))
