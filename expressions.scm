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
;;;     <functoid> record                  -- lambdoid binder (see below)
;;;     (apply-functoid f arg ...)         -- apply a functoid to arguments

;;; -----------------------------------------------------------------------
;;; Functoid record type
;;;
;;; A FUNCTOID is a named tagged structure (not a pure S-expression).
;;; kind     : 'lambdoid — domain may be any class.  This is now the ONLY kind.
;;;
;;;            There was a second, 'lambda, documented as "domain must be a SET
;;;            (produces element of FUN)".  Nothing ever enforced that: every
;;;            reader of `functoid-kind' in the tree either PRESERVES it
;;;            (make-functoid with the same kind), COMPARES two for equality
;;;            (match-expr, alpha-equiv-under?) or PRINTS it (expr->str).  So the
;;;            two kinds behaved identically and the field's only observable
;;;            effect was the word printed.  The set-domain lambda a user
;;;            actually wants is `VNB-LAMBDA', which is a set of ordered pairs
;;;            and an element of FUN(A,B) -- a different construct entirely, with
;;;            its own typing rule (lam-t) and its own reduction (lam-b), where a
;;;            functoid reduces by functoid-beta.  The surface spelling `lambda'
;;;            was removed 2026-08-18 (parser.scm) because the unadorned word
;;;            standing for the construct no proof in the library uses, beside
;;;            `vnb-lambda' standing for the one every proof uses, is a
;;;            confusion with no upside.  `make-functoid' now REFUSES the dead
;;;            kind rather than letting it print unparseable syntax.
;;; bindings : list of (var . domain-expr) pairs, one per bound variable
;;; body     : body expression (S-expression or containing functoids)
;;;
;;; Application: (apply-functoid f arg1 arg2 ...) where f is a <functoid>
;;; or a term that evaluates to one.  For ordinary (non-functoid) function
;;; application the existing (f arg ...) form is retained.

(define-record-type <functoid>
  (%make-functoid kind bindings body)
  functoid?
  (kind     functoid-kind)      ; 'lambdoid (the only kind; see above)
  (bindings functoid-bindings)  ; ((var . dom) ...)
  (body     functoid-body))

(define (make-functoid kind bindings body)
  ;; Refuse the retired kind LOUDLY.  A 'lambda record is unreachable from any
  ;; surface input since parser.scm dropped the spelling, but a hand-written
  ;; call could still make one, and `expr->str' prints the kind symbol
  ;; verbatim -- so such a record would print as `lambda([...], ...)', which no
  ;; longer parses.  A round-trip that silently stops round-tripping is worse
  ;; than an error naming the two things the caller might have meant.
  (if (eq? kind 'lambda)
      (error (string-append
              "make-functoid: the 'lambda functoid kind was retired 2026-08-18.  "
              "Use 'lambdoid for a functoid (domain may be a proper class, "
              "reduced by functoid-beta), or build a VNB-LAMBDA for a "
              "set-function (an element of FUN(A,B), typed by lam-t and "
              "reduced by lam-b).")))
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
                           FUN SEP COMP BIG-UNION POWER
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
(define (cartesian-sets e)    (cdr e))   ; (CARTESIAN A B C) -> (CARR B C)
(define (nth-index e)         (cadr e))  ; (NTH k x) -> k
(define (nth-expr e)          (caddr e)) ; (NTH k x) -> x

;;; -----------------------------------------------------------------------
;;; VNB-LAMBDA binding spec
;;;
;;; The symbolic form (VNB-LAMBDA <bind-spec> body) admits two shapes:
;;;   <bind-spec> = symbol            -- single binder
;;;               | (LIST x y z ...)  -- multi-var binder
;;; Used in raw S-expression axioms (algebraic.scm RING-PROD body, complex.scm
;;; CC-NORMED-FIELD/CC-MS, sequences.scm sum-left-scalar) where the parser is not run.
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
       ;; COMP joined this label on 2026-08-15, and it had been missing from
       ;; EVERY walker in the tree: the string `COMP' did not occur in this file
       ;; at all.  `{x | p}' (COMP x p) binds x in p and has precisely the
       ;; FORALL/FORSOME/IOTA shape, but fell through to the general compound
       ;; branch, so
       ;;
       ;;   free-vars  {r | r in a}          reported r FREE  (should be just a)
       ;;   subst-free r:=zz in {r | r in a} gave {zz | zz in a}  -- it rewrote
       ;;                                    the BOUND variable
       ;;   subst-free a:=f(r) in the same   captured: {r | r in f(r)}, no rename
       ;;   alpha-equiv? {r|r in a} {s|s in a}  was #f
       ;;
       ;; Latent, not live: no installed formula in the library contains a COMP
       ;; (measured -- 0 of the theorem table), so nothing in the tree was ever
       ;; walked wrong.  It bit only a user who TYPED `{x | p}', which the parser
       ;; has always accepted and the manual documents.  `validate-wff!' knew
       ;; COMP was a binder all along (wff.scm, "COMP bound var not symbol"),
       ;; which is what made the omission invisible: the form graded clean.
       ;;
       ;; The same one-symbol repair is at the corresponding label in
       ;; subst-free and alpha-equiv-under? below, in match-expr and
       ;; rewrite-expr (macetes.scm), and in replace-term
       ;; (primitive-inferences.scm) -- six sites, all of shape (HEAD var body).
       ((FORALL FORSOME IOTA COMP)
        (remove (cadr expr) (free-vars (caddr expr))))
       ((SEP)
        (union-vars (free-vars (caddr expr))
                    (remove (cadr expr) (free-vars (cadddr expr)))))
       ((BIG-UNION)
        ;; (BIG-UNION z A body) — z bound in body, free in A
        (union-vars (free-vars (caddr expr))
                    (remove (cadr expr) (free-vars (cadddr expr)))))
       ((VNB-LAMBDA)
        ;; (VNB-LAMBDA bind-spec A body) — bind-spec hides its names in body,
        ;; but NOT in the domain A, which lies outside the binder's scope.
        ;; Exactly SEP's and BIG-UNION's shape, and for the same reason: the
        ;; term must DETERMINE its domain.  See docs/lambda-domain.md.
        (let ((bvars (vnb-lambda-bvars (cadr expr))))
          (union-vars (free-vars (caddr expr))
                      (fold-left (lambda (vs bv) (remove bv vs))
                                 (free-vars (cadddr expr))
                                 bvars))))
       ;; N-ary: CARTESIAN, LIST, UNION, INTERSECTION — union over all arguments
       ((CARTESIAN LIST UNION INTERSECTION)
        (fold-vars (map free-vars (cdr expr))))
       ;; NTH has NO special case, and the one it used to have was a kernel
       ;; defect.  It read "k is a number (no vars), recurse into e" and so
       ;; never visited the index -- but ENTRY(M,i,j) is literally
       ;; (NTH j (NTH i M)) with VARIABLE indices, and the primitive axiom
       ;; nth-in-range quantifies over the index it then places there.  The
       ;; index is an ordinary term position; NTH is a registered operator
       ;; head, so the general branch below does exactly the right thing.
       ;; Same repair in subst-free, alpha-equiv-under?, match-expr,
       ;; rewrite-subexpressions and replace-term.  (2026-08-04)
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

;;; Every name BOUND by some already-installed formula, mapped to the first
;;; result that bound it.  Filled at install time (`note-installed-binders!',
;;; called from macetes.scm's install--grade!) and read by register-constant!
;;; immediately below.
(define *installed-binder-names* (make-equal-hash-table))

(define (note-installed-binders! thm-name e)
  (for-each (lambda (p)
              (unless (hash-table-ref/default *installed-binder-names* (car p) #f)
                (hash-table-set! *installed-binder-names* (car p) thm-name)))
            (formula-binder-names e)))

;;; Registering a head that some INSTALLED formula already uses as a bound
;;; variable is the case-fold collision seen from the other side, and it is the
;;; side no gate reported in time.
;;;
;;; `constant-binder-audit' (macetes.scm) sweeps the whole theorem table and is
;;; FATAL -- but it runs at the END of the load, so when `DEG' was registered on
;;; 2026-08-21 by structure-library/poly-degree.scm (load.scm:1023), the `deg'
;;; bound in is-euclidean-ring-def (installed 600 files earlier) began reading as
;;; that constant, and what showed up FIRST was an unrelated proof in
;;; euclidean-ideal-generator-proof.scm failing with "antecedent-inference:
;;; cannot decompose", aborting the load and taking the rest of the library with
;;; it -- 691 lines of log instead of 1187, with the actual cause never printed.
;;; The head registry is scope-blind by design (`free-vars' and `subst-free'
;;; consult it, they do not consult a scope), so the collision is real; only the
;;; REPORTING was late.
;;;
;;; Warn-only, and deliberately: the fatal sweep still runs at the end and is the
;;; gate.  This one exists so that the first thing printed names the constant,
;;; the formula that already binds the name, and the file being loaded.
(define (register-constant! sym kind)
  (when (symbol? sym)
    (let ((owner (hash-table-ref/default *installed-binder-names* sym #f)))
      (when (and owner (not (hash-table-ref/default *constant-registry* sym #f)))
        (display ";VNB warning: register-constant!: ") (display sym)
        (display " is already a BOUND VARIABLE of ") (display owner) (newline)
        (display ";              -- the head registry is scope-blind, so every applied `")
        (display sym) (display "'\n;              inside that formula now reads as this constant.")
        (newline)
        (display ";              Rename the binder (constant-binder-audit will fail at the")
        (newline)
        (display ";              end of this load if you do not).") (newline)))
    (hash-table-set! *constant-registry* sym kind))
  sym)

;;; Returns the kind of sym if it is a registered constant head, else #f.
(define (constant-head? sym)
  (and (symbol? sym)
       (hash-table-ref/default *constant-registry* sym #f)))

;;; -----------------------------------------------------------------------
;;; Substitution
;;;
;;; TWO PRIMITIVES, AND THE SECOND IS NOT THE FIRST ITERATED.
;;;
;;;   subst-free  x t e          -- one variable
;;;   subst-free* ((x . t) ...) e -- MANY variables, SIMULTANEOUSLY
;;;
;;; Applying a binding list with a fold of subst-free is WRONG, and wrong
;;; silently: each substitution exposes whatever it just substituted IN to every
;;; later binding.  Unfolding SPANS -- whose definition has parameters
;;; (md n u sm) -- at
;;;     SPANS(md, k, w, INTERSECTION(sm, SPAN(md, n, BLOCK(u, n, 1))))
;;; binds sm to a term that mentions the CALLER's own `n' and `u'; the pending
;;; n := k and u := w bindings then rewrote them, turning the assumption into one
;;; about SPAN(md, k, BLOCK(w, k, 1)).  No error, no warning: just a different
;;; theorem.  It is latent until an argument term mentions a variable named like
;;; a parameter of the definition being unfolded -- which is exactly what a
;;; recursive construction (a span of a truncation of u) does.
;;;
;;; Every multi-binding substitution in the tree goes through `subst-free*':
;;; macetes.scm (apply-subst -- the macete rewriter), interactive.scm
;;; (bc*--apply-subst -- the bc* closer), suggest.scm (wbc--subst-all).
;;; Iterating subst-free is legitimate ONLY when peeling nested quantifiers one
;;; at a time (proof-commands.scm's cmd-fact, minimize.scm's mz--type-at!),
;;; where each substitution happens under the binders that remain -- there the
;;; later variables are still BOUND, not free, so there is nothing to capture.

(define (subst-free* bindings expr)
  (if (null? bindings)
      expr
      ;; Stage through fresh symbols: nothing a binding substitutes in can be
      ;; seen by another binding, so the result does not depend on the order.
      (let ((tmps (map (lambda (b) (generate-uninterned-symbol 'subst-arg)) bindings)))
        (let stage ((bs bindings) (ts tmps) (e expr))          ; var -> fresh
          (if (null? bs)
              (let fill ((bs bindings) (ts tmps) (e e))        ; fresh -> term
                (if (null? bs)
                    e
                    (fill (cdr bs) (cdr ts) (subst-free (car ts) (cdar bs) e))))
              (stage (cdr bs) (cdr ts) (subst-free (caar bs) (car ts) e)))))))

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
       ((FORALL FORSOME IOTA COMP)
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
        ;; (VNB-LAMBDA bind-spec A body); rename clashing bvars to avoid
        ;; capture in the BODY.  The domain A is outside the binder's scope, so
        ;; x is substituted there unconditionally -- including when x is one of
        ;; the bound variables, exactly as SEP and BIG-UNION do for their A.
        (let* ((bind-spec (cadr expr))
               (dom       (caddr expr))
               (body      (cadddr expr))
               (bvars     (vnb-lambda-bvars bind-spec)))
          (cond
            ((member x bvars)                  ; bound in body, still free in A
             (list 'VNB-LAMBDA bind-spec (subst-free x replacement dom) body))
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
                     (subst-free x replacement dom)
                     (subst-free x replacement body*)))))))
       ;; N-ary: recurse into every argument
       ((CARTESIAN LIST UNION INTERSECTION)
        (cons (car expr)
              (map (lambda (arg) (subst-free x replacement arg)) (cdr expr))))
       ;; NTH: no special case -- the index is substituted into like any other
       ;; argument.  See the comment at free-vars.
       (else
        ;; General compound (h arg ...).  A compound head is substituted
        ;; into so ((MUL m) a b) instantiates `m`.  A symbol head is
        ;; substituted iff it is the variable x AND not a registered
        ;; constant: an applied function variable (x arg) becomes
        ;; (replacement arg); an operator/accessor head (MUL m), (CARR m) is
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

;;; A fresh variable that keeps the HINT ITSELF when nothing forbids it.
;;;
;;; `fresh-var' always appends `_N', which is right for a variable nobody will
;;; ever type -- and wrong for one a reader has to look at all day.  A
;;; destructuring binder over METRIC-SPACE produced `t_1368', and the user's
;;; objection was exactly that: "there should be a way of manually changing them
;;; to some non-conflicting and more mellifluous name."
;;;
;;; So: try the bare hint first.  It is refused if it is free in anything we
;;; were told to avoid, or if it is a REGISTERED CONSTANT -- a binder named like
;;; an accessor reads as the constant in head position, scope-blind, which is
;;; what `constant-binder-audit' exists to make a hard load failure.  Falling
;;; back to `fresh-var' then gives the old numbered form, so this can only
;;; improve a name, never break one.
(define (fresh-var/bare hint . avoid-exprs)
  (let ((forbidden (apply append (map free-vars avoid-exprs))))
    (if (and (symbol? hint)
             (not (member hint forbidden))
             (not (constant-head? hint)))
        hint
        (apply fresh-var hint avoid-exprs))))

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

;;; alpha-equiv? compares RAW S-EXPRESSIONS.  A <wff> is a record wrapping one
;;; (wff.scm), and a record reaches no branch of alpha-equiv-under? -- so
;;; before 2026-08-09 two wffs built from the same text compared #f, silently:
;;;
;;;   (alpha-equiv? (make-wff "forall([x in rr], x = x)")
;;;                 (make-wff "forall([x in rr], x = x)"))   =>  #f
;;;
;;; which is the wrong answer, not a refusal.  Nothing in the library was
;;; affected -- every call site unwraps first (wff-formula, dk-goal-of,
;;; mz--asms, calc--in-ctx?, macetes' local-ctx) -- but a driver author who
;;; passes the wff, and a REPL user checking a hunch, both get a false negative
;;; with no complaint.  So: reject it, and name the procedure that does want
;;; wffs.  Cost is one predicate call per top-level comparison; the recursion
;;; below is untouched.
;;;
;;; `wff?' lives in wff.scm, which loads AFTER this file.  That is fine: the
;;; reference is inside a procedure body and so resolves at call time, and no
;;; alpha-equiv? call can happen before wff.scm is loaded.
(define (alpha-equiv? e1 e2)
  (if (or (wff? e1) (wff? e2))
      (error "alpha-equiv?: expects raw formulas, not <wff> records -- use wff-equiv?, or unwrap with wff-formula"
             e1 e2)
      (alpha-equiv-under? e1 e2 '())))

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
     ;; ENV maps left-hand binders to right-hand binders.  It must be read as a
     ;; BIJECTION, not as a function: with the one-directional reading
     ;;
     ;;   (FORALL x (FORALL y (P x y)))  vs  (FORALL a (FORALL a (P a a)))
     ;;
     ;; env is ((y . a) (x . a)), both x and y map to a, and the two formulas
     ;; compared alpha-EQUAL -- while the same call with the arguments swapped
     ;; answered #f, because a shadowing binder on the RIGHT collapses two
     ;; distinct left variables onto one name and a shadowing binder on the LEFT
     ;; does not.  A relation that is not symmetric is not an equivalence, and
     ;; `ass' closes on this one, `dg-post!' hash-conses on it.  (Found
     ;; 2026-08-21.)  `rassq' finds the FIRST pair whose cdr is e2; for a
     ;; bijection at this depth that pair must be the very pair `assq' found.
     (let ((mapped (assq e1 env)))
       (if mapped
           (and (symbol? e2)
                (eq? (cdr mapped) e2)
                (eq? mapped (rassq e2 env)))
           ;; e1 is free.  It matches an identically-spelled e2 only if that e2
           ;; is itself free -- an e2 that some binder on the right captured is
           ;; a different variable that happens to share the spelling.
           (and (symbol? e2) (eq? e1 e2) (not (rassq e2 env))))))
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
       ((FORALL FORSOME IOTA COMP)
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
        ;; The DOMAIN is compared outside the binder (like SEP's and BIG-UNION's
        ;; A).  This is what makes two lambdas with the same body and different
        ;; domains DISTINCT terms -- the whole point of carrying the domain.
        (let ((bv1 (vnb-lambda-bvars (cadr e1)))
              (bv2 (vnb-lambda-bvars (cadr e2))))
          (and (= (length bv1) (length bv2))
               (alpha-equiv-under? (caddr e1) (caddr e2) env)
               (alpha-equiv-under? (cadddr e1) (cadddr e2)
                                   (append (map cons bv1 bv2) env)))))
       ;; N-ary: componentwise, same length required
       ((CARTESIAN LIST UNION INTERSECTION)
        (and (= (length e1) (length e2))
             (let loop ((a1 (cdr e1)) (a2 (cdr e2)))
               (or (null? a1)
                   (and (alpha-equiv-under? (car a1) (car a2) env)
                        (loop (cdr a1) (cdr a2)))))))
       ;; NTH: no special case.  The old one compared indices with equal?,
       ;; which made (FORALL i ... (NTH i L)) and (FORALL k ... (NTH i L))
       ;; alpha-EQUAL -- a false positive, and `ass' closes on alpha-equality.
       ;; See the comment at free-vars.
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

;;; rassq: the first pair of ALIST whose CDR is eq? to V (the reverse of assq).
(define (rassq v alist)
  (cond ((null? alist) #f)
        ((eq? (cdar alist) v) (car alist))
        (else (rassq v (cdr alist)))))

;;; -----------------------------------------------------------------------
;;; Binder shapes -- the ONE declaration of which heads bind, and where
;;;
;;; Every walker over expressions has to know this, and until 2026-08-15 each
;;; knew it separately: `COMP' was spelled out at five case labels and missing
;;; from all of them, so `free-vars' called its bound variable free and
;;; `subst-free' captured into it, for as long as the head had existed.  The
;;; repair was one symbol at six places -- which is the same defect waiting to
;;; happen again at the seventh.
;;;
;;; This table is that knowledge, written once.  `formula-hash' and
;;; `formula-canon' below read it, and `binder-walker-audit' (audit.scm) checks
;;; at every load that free-vars, subst-free, alpha-equiv? and formula-hash all
;;; agree with it, head by head.  A new binder that is added here and nowhere
;;; else is reported by name at load time instead of being found weeks later.
;;;
;;; The three shapes:
;;;   simple   (H v body)          v scopes over body
;;;   domain   (H v A body)        A is OUTSIDE the binder, body inside
;;;   lambda   (H bspec A body)    bspec is a symbol or (LIST v ...); A outside
(define *binder-shapes*
  '((FORALL . simple) (FORSOME . simple) (IOTA . simple) (COMP . simple)
    (SEP . domain)    (BIG-UNION . domain)
    (VNB-LAMBDA . lambda)))

(define (binder-shape head)
  (and (symbol? head)
       (let ((p (assq head *binder-shapes*)))
         (and p (cdr p)))))

;;; -----------------------------------------------------------------------
;;; formula-hash -- an alpha-INVARIANT fixnum digest of a formula
;;;
;;; The contract, and the only thing anything may rely on:
;;;
;;;   (alpha-equiv? e1 e2)  =>  (= (formula-hash e1) (formula-hash e2))
;;;
;;; The converse does NOT hold: equal hashes mean "compare them properly", not
;;; "equal".  Every caller verifies with alpha-equiv? afterwards, so a collision
;;; costs time and never an answer.
;;;
;;; Bound variables are hashed by de Bruijn INDEX -- the number of binders
;;; between the occurrence and the one that binds it -- so the spelling of a
;;; bound name contributes nothing, while its binding STRUCTURE contributes
;;; everything.  That is what makes the digest alpha-invariant, and it is also
;;; why the shadowing pair above hashes apart: `(P x y)' under two binders gives
;;; indices (1 0) and `(P a a)' under two binders gives (0 0).
;;;
;;; One caveat, stated because the contract above is an implication and this is
;;; where it could fail: two of alpha-equiv-under?'s case labels compare fixed
;;; argument positions WITHOUT checking that the two forms have the same length
;;; ((NOT CHOICE TUPLES MAKE-SET LENGTH) and the binary-connective label), so on
;;; a MALFORMED expression -- (NOT a b) against (NOT a) -- it can answer #t
;;; where the digest, which folds in the length, answers different.  No such
;;; expression survives validate-wff!, and every installed formula in the tree
;;; is graded by it, so this is unreachable from the library; a hand-built
;;; S-expression could reach it.
(define %fh-modulus 1073741789)         ; prime just under 2^30

;;; h < 2^30 and 31*h + x < 2^35, so every intermediate is a fixnum on this
;;; word size and the fix: operators apply.  With the generic ones the digest
;;; walk cost 10 us per library formula against 3 us for a full alpha-equiv?
;;; traversal of the same tree -- the hash of a formula must not cost more than
;;; comparing two of them, or the index gives back what it saves.
(define-integrable (%fh-mix h x)
  (fix:remainder (fix:+ (fix:* h 31) x) %fh-modulus))

;;; MIT's symbol-hash hashes the symbol's NAME STRING on every call, which the
;;; walk does once per symbol OCCURRENCE.  Symbols are interned, the value is
;;; stable, so it is computed once each.  (An address-based eq-hash would be
;;; cheaper still and is not usable: it changes across a GC, and these digests
;;; are cached on <wff> records that outlive one.)
(define %fh-symtab (make-strong-eqv-hash-table))

(define (%fh-sym s)
  (or (hash-table-ref/default %fh-symtab s #f)
      (let ((h (fix:remainder (symbol-hash s) %fh-modulus)))
        (hash-table-set! %fh-symtab s h)
        h)))

;;; Position of V in ENV (innermost binder first), or #f when V is free.
(define (%fh-index v env)
  (let loop ((l env) (i 0))
    (cond ((null? l) #f)
          ((eq? (car l) v) i)
          (else (loop (cdr l) (+ i 1))))))

(define (%fh e env)
  (cond
    ((symbol? e)
     (let ((i (%fh-index e env)))
       (if i
           (%fh-mix 7919 i)                            ; bound: index only
           (%fh-mix 104729 (%fh-sym e)))))
    ((number? e)
     (%fh-mix 15485863 (fix:remainder (string-hash (number->string e)) %fh-modulus)))
    ((functoid? e)
     (let* ((bs   (functoid-bindings e))
            (vars (map car bs))
            (h    (let loop ((l bs) (h (%fh-mix 31337 (%fh-sym (functoid-kind e)))))
                    (if (null? l) h
                        (loop (cdr l) (%fh-mix h (%fh (cdar l) env)))))))
       (%fh-mix (%fh-mix h (length bs))
                (%fh (functoid-body e) (append vars env)))))
    ((pair? e)
     (case (binder-shape (car e))
       ((simple)                                    ; (H v body)
        (%fh-mix (%fh-mix 1000003 (%fh-sym (car e)))
                 (%fh (caddr e) (cons (cadr e) env))))
       ((domain)                                    ; (H v A body)
        (%fh-mix (%fh-mix (%fh-mix 1000033 (%fh-sym (car e)))
                          (%fh (caddr e) env))
                 (%fh (cadddr e) (cons (cadr e) env))))
       ((lambda)                                    ; (H bspec A body)
        (let ((bv (vnb-lambda-bvars (cadr e))))
          ;; The bare-symbol and one-element (LIST v) spellings are the same
          ;; binder -- alpha-equiv-under? compares them across shapes -- so only
          ;; the ARITY of the spec is hashed, never its shape.
          (%fh-mix (%fh-mix (%fh-mix (%fh-mix 1000037 (%fh-sym (car e)))
                                     (length bv))
                            (%fh (caddr e) env))
                   (%fh (cadddr e) (append bv env)))))
       (else
        ;; General compound.  The head is walked like any other position, which
        ;; is what makes ((MUL m) x y) and a bound function variable -- (FORALL f
        ;; (f x)) against (FORALL g (g x)) -- come out right; alpha-equiv-under?
        ;; reaches the same answer by its compound-head branch.
        (let loop ((l e) (h 1000039) (n 0))
          (if (pair? l)
              (loop (cdr l) (%fh-mix h (%fh (car l) env)) (+ n 1))
              (%fh-mix h n))))))
    ((null? e) 12345)
    ((string? e) (%fh-mix 99991 (fix:remainder (string-hash e) %fh-modulus)))
    ((boolean? e) (if e 314159 271828))
    (else (%fh-mix 54321 0))))

(define (formula-hash e)
  (%fh e '()))

;;; Every variable BOUND anywhere in E, as (var . binding-head) pairs, driven by
;;; *binder-shapes* so that a head declared there is known here with no second
;;; edit.  Used by `note-installed-binders!' (above) for the register-constant!
;;; collision warning.
;;;
;;; `wff-constant-binders' (macetes.scm) walks the same binders for the fatal
;;; end-of-load sweep and spells the set out again in its own case labels; it is
;;; a fourth copy and a candidate to fold onto this one.  Left alone here
;;; because it backs a FATAL gate and this change is warn-only.
(define (formula-binder-names e0)
  (let ((e (if (wff? e0) (wff-formula e0) e0))
        (out '()))
    (define (note v h) (if (symbol? v) (set! out (cons (cons v h) out))))
    (let walk ((e e))
      (cond
        ((functoid? e)
         (for-each (lambda (b) (note (car b) 'FUNCTOID) (walk (cdr b)))
                   (functoid-bindings e))
         (walk (functoid-body e)))
        ((pair? e)
         (case (binder-shape (car e))
           ((simple) (note (cadr e) (car e)) (walk (caddr e)))
           ((domain) (walk (caddr e)) (note (cadr e) (car e)) (walk (cadddr e)))
           ((lambda) (walk (caddr e))
                     (for-each (lambda (v) (note v (car e))) (vnb-lambda-bvars (cadr e)))
                     (walk (cadddr e)))
           (else (for-each walk e))))
        (else #t)))
    (reverse out)))

;;; formula-canon -- the same walk, allocating.  Two formulas are alpha-equivalent
;;; exactly when their canonical forms are `equal?', so this is the thing to print
;;; when a digest collision or a suspected mismatch has to be looked at by eye.
;;; Nothing in the prover's inner loop calls it; formula-hash is the fused,
;;; non-allocating version of the same traversal.
(define %canon-bound  (string->uninterned-symbol "bvar"))
(define %canon-binder (string->uninterned-symbol "binder"))

(define (%canon e env)
  (cond
    ((symbol? e)
     (let ((i (%fh-index e env)))
       (if i (list %canon-bound i) e)))
    ((functoid? e)
     (let ((vars (map car (functoid-bindings e))))
       (list %canon-binder 'FUNCTOID (functoid-kind e)
             (map (lambda (b) (%canon (cdr b) env)) (functoid-bindings e))
             (%canon (functoid-body e) (append vars env)))))
    ((pair? e)
     (case (binder-shape (car e))
       ((simple)
        (list (car e) %canon-binder (%canon (caddr e) (cons (cadr e) env))))
       ((domain)
        (list (car e) %canon-binder
              (%canon (caddr e) env)
              (%canon (cadddr e) (cons (cadr e) env))))
       ((lambda)
        (let ((bv (vnb-lambda-bvars (cadr e))))
          (list (car e) (list %canon-binder (length bv))
                (%canon (caddr e) env)
                (%canon (cadddr e) (append bv env)))))
       (else (map (lambda (x) (%canon x env)) e))))
    (else e)))

(define (formula-canon e)
  (%canon e '()))
