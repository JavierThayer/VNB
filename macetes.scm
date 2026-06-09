;;; macetes.scm -- macete mechanism
;;;
;;; A MACETE is a named, composable rewrite strategy.
;;; When a theorem T is installed, an elementary macete is automatically
;;; built from it by extracting a source pattern and replacement pattern
;;; from its logical form (see the table in the IMPS manual, ch. 12).
;;;
;;; Elementary macetes carry LOCAL CONTEXT as they descend into
;;; subexpressions (following Monk 1988).  When entering the consequent
;;; of (IMPLIES A B) the antecedent A is added to the local context; when
;;; entering the right disjunct of (OR A B) the assumption (NOT A) is
;;; added; and so on.  A macete condition that matches a formula already
;;; present in the local context is considered discharged automatically.
;;;
;;; COMPOUND MACETES (constructors):
;;;   - (series m1 m2 ... mn) : apply in sequence
;;;   - (repeat m)            : apply m until no change
;;;   - (try m)               : apply m, but succeed even if m fails
;;;   - (choice m1 m2 ...)    : try each in order, use first that succeeds

;;; -----------------------------------------------------------------------
;;; Macete registry

(define *macete-table* (make-equal-hash-table))

(define (install-macete! name macete)
  (hash-table-set! *macete-table* name macete)
  name)

(define (lookup-macete name)
  (or (hash-table-ref/default *macete-table* name #f)
      (error "lookup-macete: unknown macete" name)))

;;; -----------------------------------------------------------------------
;;; Macete representation
;;;
;;; A macete is a procedure: (macete sqn) -> #t (success) | #f (failure)

(define (macete? x) (procedure? x))

;;; -----------------------------------------------------------------------
;;; Variadic patterns: RESTVAR and the restbound record
;;;
;;; A source pattern may end with (RESTVAR <sym>) in the argument list of a
;;; variadic head (UNION, INTERSECTION, CARTESIAN, LIST, FUN, POWER, or any
;;; general compound).  When the matcher reaches that final position it binds
;;; <sym> to the tail of the expression's argument list -- AS A LIST OF
;;; EXPRESSIONS -- wrapped in a <restbound> record.
;;;
;;; Replacement templates may then use
;;;   (SPLICE <binop> <elt-var> <rest-var> <template>)
;;; to right-fold <binop> over template[elt-var := a_i] for a_i in the list.
;;; See apply-subst / expand-splices below.

(define-record-type <restbound>
  (make-restbound exprs)
  restbound?
  (exprs restbound-exprs))

(define (restvar-pattern? p schema-vars)
  (and (pair? p) (eq? (car p) 'RESTVAR)
       (pair? (cdr p)) (null? (cddr p))
       (symbol? (cadr p))
       (member (cadr p) schema-vars)))

(define (restvar-name p) (cadr p))

;;; Match a parallel pattern/expr argument list.  If the final pattern is
;;; (RESTVAR <sym>) with <sym> a schema-var, bind <sym> to the rest of es as
;;; a <restbound>.  Otherwise lengths must match exactly.
(define (match-list-with-rest ps es schema-vars)
  (let loop ((ps ps) (es es) (acc '()))
    (cond
      ((and (pair? ps)
            (null? (cdr ps))
            (restvar-pattern? (car ps) schema-vars))
       (merge-subst acc
         (list (cons (restvar-name (car ps)) (make-restbound es)))))
      ((and (null? ps) (null? es)) acc)
      ((or  (null? ps) (null? es)) #f)
      (else
       (let ((m (match-expr (car ps) (car es) schema-vars)))
         (and m
              (let ((merged (merge-subst acc m)))
                (and merged (loop (cdr ps) (cdr es) merged)))))))))

;;; -----------------------------------------------------------------------
;;; Pattern matching for elementary macetes

;;; When *match-var-head* is true, a pattern whose head is itself a schema
;;; variable --- (f a ...) --- matches any same-arity application: f is bound
;;; to the expression's head.  bc* sets this (via fluid-let) so it can apply
;;; theorems whose conclusion applies a quantified function, e.g.
;;; fun-apply-type's conclusion (IN (f x) B).  The macete engine never sets
;;; it, so elementary-macete matching is byte-for-byte unchanged.
(define *match-var-head* #f)

(define (match-expr pattern expr schema-vars)
  (cond
    ((and (symbol? pattern) (member pattern schema-vars))
     (list (cons pattern expr)))
    ((symbol? pattern)
     (and (equal? pattern expr) '()))
    ((or (eq? pattern 'TRUTH) (eq? pattern 'FALSITY))
     (and (equal? pattern expr) '()))
    ((number? pattern)
     (and (equal? pattern expr) '()))
    ;; Functoid records: match structurally (same kind, same arity, domains match, body matches)
    ((and (functoid? pattern) (functoid? expr))
     (let ((bp (functoid-bindings pattern)) (be (functoid-bindings expr)))
       (and (eq? (functoid-kind pattern) (functoid-kind expr))
            (= (length bp) (length be))
            (let loop ((bps bp) (bes be) (acc '()))
              (if (null? bps)
                  (let ((bm (match-expr (functoid-body pattern)
                                        (functoid-body expr) schema-vars)))
                    (and bm (merge-subst acc bm)))
                  (let ((dm (match-expr (cdar bps) (cdar bes) schema-vars)))
                    (and dm (eq? (caar bps) (caar bes))
                         (let ((merged (merge-subst acc dm)))
                           (and merged (loop (cdr bps) (cdr bes) merged))))))))))
    ((or (functoid? pattern) (functoid? expr)) #f)
    ;; Variable-headed application (bc* only; see *match-var-head*):
    ;; pattern (f a ...) with f a schema var matches any same-arity
    ;; application, binding f to the expression's head.
    ((and *match-var-head*
          (pair? pattern) (pair? expr)
          (symbol? (car pattern))
          (member (car pattern) schema-vars)
          (= (length pattern) (length expr)))
     (let ((am (match-list-with-rest (cdr pattern) (cdr expr) schema-vars)))
       (and am (merge-subst (list (cons (car pattern) (car expr))) am))))
    ((and (pair? pattern) (pair? expr) (eq? (car pattern) (car expr)))
     (case (car pattern)
       ((NOT CHOICE MAKE-SET LENGTH)
        (match-expr (cadr pattern) (cadr expr) schema-vars))
       ((POWER)
        (match-list-with-rest (cdr pattern) (cdr expr) schema-vars))
       ((AND OR IMPLIES IFF = == IN COMPLEMENT-IN)
        (let ((left  (match-expr (cadr pattern)  (cadr expr)  schema-vars))
              (right (match-expr (caddr pattern) (caddr expr) schema-vars)))
          (and left right (merge-subst left right))))
       ((FUN)
        ;; arity 2: (FUN A); arity 3: (FUN A B); also supports RESTVAR
        (match-list-with-rest (cdr pattern) (cdr expr) schema-vars))
       ((CARTESIAN LIST UNION INTERSECTION)
        (match-list-with-rest (cdr pattern) (cdr expr) schema-vars))
       ((NTH)
        (and (equal? (cadr pattern) (cadr expr))
             (match-expr (caddr pattern) (caddr expr) schema-vars)))
       ((SEP)
        (and (equal? (cadr pattern) (cadr expr))
             (let ((ma (match-expr (caddr pattern)  (caddr expr)  schema-vars))
                   (mp (match-expr (cadddr pattern) (cadddr expr) schema-vars)))
               (and ma mp (merge-subst ma mp)))))
       ((FORALL FORSOME IOTA)
        (and (eq? (cadr pattern) (cadr expr))
             (match-expr (caddr pattern) (caddr expr) schema-vars)))
       (else
        (match-list-with-rest (cdr pattern) (cdr expr) schema-vars))))
    ;; Compound-operator application: pattern ((D s) x y) vs expr
    ;; ((D Se) ae be) -- the operator is itself an application (a structure
    ;; accessor applied to its instance: (D s), (mul r), ...).  The
    ;; schema-var-head arm needs a SYMBOL head and the constant-head arm needs
    ;; eq? heads, so neither fires -- yet this is ordinary first-order
    ;; matching.  Recurse into the operator, then the operands.  This lets bc*
    ;; backchain facts whose conclusion mentions a structure-op application
    ;; ((d s)(x,y), (mul r)(a,b), ...).  Fires ONLY when both heads are pairs,
    ;; so symbol-headed forms and the *match-var-head* gate are untouched.
    ((and (pair? pattern) (pair? expr)
          (pair? (car pattern)) (pair? (car expr))
          (= (length pattern) (length expr)))
     (let ((head-m (match-expr (car pattern) (car expr) schema-vars)))
       (and head-m
            (let ((rest-m (match-list-with-rest (cdr pattern) (cdr expr) schema-vars)))
              (and rest-m (merge-subst head-m rest-m))))))
    (else #f)))

(define (binding-values-equal? v1 v2)
  (cond
    ((and (restbound? v1) (restbound? v2))
     (let ((xs (restbound-exprs v1)) (ys (restbound-exprs v2)))
       (and (= (length xs) (length ys))
            (every (lambda (p) p)
                   (map alpha-equiv? xs ys)))))
    ((or (restbound? v1) (restbound? v2)) #f)
    (else (alpha-equiv? v1 v2))))

(define (merge-subst s1 s2)
  (let loop ((s2 s2) (acc s1))
    (if (null? s2)
        acc
        (let* ((binding (car s2))
               (var (car binding))
               (val (cdr binding))
               (existing (assoc var acc)))
          (cond
            ((not existing) (loop (cdr s2) (cons binding acc)))
            ((binding-values-equal? (cdr existing) val) (loop (cdr s2) acc))
            (else #f))))))

;;; apply-subst now handles two kinds of bindings:
;;;   ordinary  (var . expr)         -- ordinary subst-free
;;;   rest     (var . <restbound>)   -- used by SPLICE expansion below
;;; Ordinary substitutions run first.  Then any SPLICE forms in the result
;;; are expanded using the rest bindings.
(define (apply-subst subst expr)
  (let loop ((bs subst) (ord '()) (rest '()))
    (cond
      ((null? bs)
       (let ((after-ord (fold-left (lambda (e b)
                                     (subst-free (car b) (cdr b) e))
                                   expr
                                   (reverse ord))))
         (if (null? rest)
             after-ord
             (expand-splices after-ord rest))))
      ((restbound? (cdar bs))
       (loop (cdr bs) ord (cons (car bs) rest)))
      (else
       (loop (cdr bs) (cons (car bs) ord) rest)))))

;;; Walk expr, replacing each
;;;   (SPLICE <binop> <elt-var> <rest-var> <template>)
;;; with the right-fold of <binop> over template[elt-var := a_i] for the
;;; expressions a_1 ... a_n bound to <rest-var>.  Requires n >= 1.
;;; Recurses into pairs and into functoid records.
(define (expand-splices expr rest-bindings)
  (cond
    ((functoid? expr)
     (let ((bindings (functoid-bindings expr))
           (body     (functoid-body expr)))
       (make-functoid
         (functoid-kind expr)
         (map (lambda (b)
                (cons (car b) (expand-splices (cdr b) rest-bindings)))
              bindings)
         (expand-splices body rest-bindings))))
    ((not (pair? expr)) expr)
    ((eq? (car expr) 'SPLICE)
     (let ((binop    (cadr expr))
           (elt-var  (caddr expr))
           (rest-var (cadddr expr))
           (template (car (cddddr expr))))
       (let ((b (assq rest-var rest-bindings)))
         (cond
           ((not b)
            (error "expand-splices: rest-var not bound" rest-var))
           (else
            (let ((items (restbound-exprs (cdr b))))
              (cond
                ((null? items)
                 (error "expand-splices: empty rest binding for" rest-var))
                (else
                 (let inner ((xs items))
                   (let ((head (expand-splices
                                 (subst-free elt-var (car xs) template)
                                 rest-bindings)))
                     (if (null? (cdr xs))
                         head
                         (list binop head (inner (cdr xs))))))))))))))
    (else
     (map (lambda (e) (expand-splices e rest-bindings)) expr))))

;;; -----------------------------------------------------------------------
;;; Local-context incrementers (Monk 1988)
;;;
;;; (lc-extend parent-expr child-idx local-ctx) returns a new local-ctx
;;; enriched with assumptions appropriate for descending into the
;;; child-idx-th argument (0-based) of parent-expr.
;;;
;;;   IMPLIES: entering consequent (idx 1) adds the antecedent (flattened)
;;;   AND:     entering right conjunct (idx 1) adds the left conjunct (flattened)
;;;   OR:      entering right disjunct (idx 1) adds (NOT left-disjunct)
;;;   all others: unchanged
;;;
;;; AND formulas in the antecedent are flattened into individual conjuncts
;;; so that each condition can be found by alpha-equivalence matching.

(define (flatten-conjuncts f)
  (if (and (pair? f) (eq? (car f) 'AND))
      (append (flatten-conjuncts (cadr f))
              (flatten-conjuncts (caddr f)))
      (list f)))

(define (lc-extend parent-expr child-idx local-ctx)
  (if (not (pair? parent-expr))
      local-ctx
      (case (car parent-expr)
        ((IMPLIES AND)
         (if (= child-idx 1)
             (append (flatten-conjuncts (cadr parent-expr)) local-ctx)
             local-ctx))
        ((OR)
         ;; (REVIEW.md G-1) Symmetric OR: descending into the LEFT disjunct
         ;; can assume (NOT right), descending into the RIGHT disjunct can
         ;; assume (NOT left).  Previously only the right side received its
         ;; assumption (a completeness gap, not a soundness one).
         (cond
           ((= child-idx 0)
            (cons `(NOT ,(caddr parent-expr)) local-ctx))
           ((= child-idx 1)
            (cons `(NOT ,(cadr parent-expr)) local-ctx))
           (else local-ctx)))
        (else local-ctx))))

;;; When the rewriter descends under a binder that introduces fresh names,
;;; any assumption in local-ctx that mentions one of those names FREE refers
;;; to the OUTER scope's variable; under the binder it would be reinterpreted
;;; as the new bound one, which is unsound.  Drop such assumptions before
;;; descending.  (Alternative: alpha-rename the binder; dropping is simpler
;;; and conservative — at worst a sound rewrite is missed.)
(define (lc-drop-shadowed bvars local-ctx)
  (filter (lambda (a)
            (let ((fvs (free-vars a)))
              (let loop ((bs bvars))
                (cond ((null? bs) #t)
                      ((member (car bs) fvs) #f)
                      (else (loop (cdr bs)))))))
          local-ctx))

;;; -----------------------------------------------------------------------
;;; Condition satisfaction check
;;;
;;; A condition is "held" in a local context if it is TRUTH or is
;;; alpha-equivalent to some formula already in the context.

(define (condition-holds? formula local-ctx)
  (or (equal? formula 'TRUTH)
      (let loop ((ctx local-ctx))
        (cond ((null? ctx) #f)
              ((alpha-equiv? formula (car ctx)) #t)
              (else (loop (cdr ctx)))))))

(define (all-conditions-hold? cond-instances local-ctx)
  (let loop ((cs cond-instances))
    (or (null? cs)
        (and (condition-holds? (car cs) local-ctx)
             (loop (cdr cs))))))

;;; -----------------------------------------------------------------------
;;; Rewriting with local context
;;;
;;; (rewrite-expr pattern replacement schema-vars conditions expr local-ctx)
;;;   -> (new-expr . minor-premises)
;;;
;;; Tries to rewrite expr at the top level: succeeds only if the pattern
;;; matches AND all condition instances are held by local-ctx.  On failure
;;; at the top level, recurses into subexpressions, threading an enriched
;;; local context into each child according to lc-increment.
;;;
;;; minor-premises is currently always '() — conditions not locally
;;; dischargeable cause the rewrite to be skipped at that position.

;;; When *macete-spawn-conditions?* is #t, a top-level match fires EVEN IF its
;;; conditions are not all discharged from local-ctx: the unmet (instantiated)
;;; conditions ride out as minor premises instead of blocking the rewrite.
;;; Default #f preserves the strict all-or-nothing behaviour every goal-side
;;; macete relies on (see the note above: minors are '() under the default).
;;; mac-h (apply-macete-to-assumption!) fluid-lets it #t so a conditional
;;; equivalence can rewrite a hypothesis and SPAWN its side-conditions as
;;; subgoals -- the IMPS macete behaviour.  Sound because the gated macete is a
;;; genuine equivalence (source <=> replacement under the conditions), so
;;; Leibniz congruence applies once the conditions are discharged.
(define *macete-spawn-conditions?* #f)

(define (rewrite-expr pattern replacement schema-vars conditions expr local-ctx)
  (let ((top-match (match-expr pattern expr schema-vars)))
    (if top-match
        (let ((unmet (filter (lambda (c) (not (condition-holds? c local-ctx)))
                             (map (lambda (c) (apply-subst top-match c)) conditions))))
          (if (or (null? unmet) *macete-spawn-conditions?*)
              ;; Fire; unmet conditions become minor premises (empty unless spawning)
              (cons (apply-subst top-match replacement) unmet)
              ;; Conditions unmet and not spawning: recurse into children
              (rewrite-subexpressions pattern replacement schema-vars conditions
                                      expr local-ctx)))
        ;; No top-level match: recurse into children
        (rewrite-subexpressions pattern replacement schema-vars conditions
                                expr local-ctx))))

(define (rewrite-subexpressions pattern replacement schema-vars conditions
                                expr local-ctx)
  (cond
    ;; Atoms and non-pair non-functoid: no children to rewrite
    ((and (not (pair? expr)) (not (functoid? expr)))
     (cons expr '()))
    ;; Functoid record: rewrite domain expressions and body (avoid schema-var capture)
    ((functoid? expr)
     (let* ((bindings (functoid-bindings expr))
            (bvars    (map car bindings))
            ;; Rewrite each domain (outer scope, no new lc)
            (rdoms    (map (lambda (b)
                             (rewrite-expr pattern replacement schema-vars conditions
                                           (cdr b) local-ctx))
                           bindings))
            ;; Rewrite body; skip if any bvar is a schema-var (avoid unsound capture).
            ;; Drop ctx assumptions shadowed by the lambda's bvars before descending.
            (rbody    (if (let lp ((bvs bvars))
                            (and (not (null? bvs))
                                 (or (member (car bvs) schema-vars)
                                     (lp (cdr bvs)))))
                          (cons (functoid-body expr) '())
                          (rewrite-expr pattern replacement schema-vars conditions
                                        (functoid-body expr)
                                        (lc-drop-shadowed bvars local-ctx))))
            (new-bindings (map cons bvars (map car rdoms)))
            (minors   (append (apply append (map cdr rdoms)) (cdr rbody))))
       (cons (make-functoid (functoid-kind expr) new-bindings (car rbody))
             minors)))
    ;; Pair expressions
    (else
     (let ((head (car expr)))
       ;; Helper: rewrite child at index i with the appropriate local context.
       (define (rw-child i child)
         (rewrite-expr pattern replacement schema-vars conditions
                       child
                       (lc-extend expr i local-ctx)))
       (case head
         ((NOT CHOICE MAKE-SET LENGTH)
          (let ((r (rw-child 0 (cadr expr))))
            (cons (list head (car r)) (cdr r))))

         ;; Binary connectives with lc-increment on right child
         ((IMPLIES AND OR)
          (let ((rl (rw-child 0 (cadr expr)))
                (rr (rw-child 1 (caddr expr))))
            (cons (list head (car rl) (car rr))
                  (append (cdr rl) (cdr rr)))))

         ;; Binary predicates/connectives with no lc-increment
         ((IFF = == IN COMPLEMENT-IN)
          (let ((rl (rw-child 0 (cadr expr)))
                (rr (rw-child 1 (caddr expr))))
            (cons (list head (car rl) (car rr))
                  (append (cdr rl) (cdr rr)))))

         ;; FUN: arity 2 (domain only) or arity 3 (domain + codomain)
         ((FUN)
          (let loop ((args (cdr expr)) (new '()) (minors '()))
            (if (null? args)
                (cons (cons head (reverse new)) minors)
                (let ((r (rewrite-expr pattern replacement schema-vars conditions
                                       (car args) local-ctx)))
                  (loop (cdr args)
                        (cons (car r) new)
                        (append minors (cdr r)))))))

         ((POWER)
          (let loop ((args (cdr expr)) (new '()) (minors '()))
            (if (null? args)
                (cons (cons head (reverse new)) minors)
                (let ((r (rewrite-expr pattern replacement schema-vars conditions
                                       (car args) local-ctx)))
                  (loop (cdr args)
                        (cons (car r) new)
                        (append minors (cdr r)))))))

         ((LIST CARTESIAN UNION INTERSECTION)
          (let loop ((args (cdr expr)) (new '()) (minors '()))
            (if (null? args)
                (cons (cons head (reverse new)) minors)
                (let ((r (rewrite-expr pattern replacement schema-vars conditions
                                       (car args) local-ctx)))
                  (loop (cdr args)
                        (cons (car r) new)
                        (append minors (cdr r)))))))

         ((NTH)
          (let ((r (rewrite-expr pattern replacement schema-vars conditions
                                 (caddr expr) local-ctx)))
            (cons `(NTH ,(cadr expr) ,(car r)) (cdr r))))

         ((SEP)
          ;; (SEP x A p) — A is outer scope; p has x bound.  Drop ctx
          ;; assumptions shadowed by x for the body recursion.
          (let* ((bv (cadr expr))
                 (ra (rewrite-expr pattern replacement schema-vars conditions
                                   (caddr expr) local-ctx))
                 (rp (if (member bv schema-vars)
                         (cons (cadddr expr) '())
                         (rewrite-expr pattern replacement schema-vars conditions
                                       (cadddr expr)
                                       (lc-drop-shadowed (list bv) local-ctx)))))
            (cons `(SEP ,bv ,(car ra) ,(car rp))
                  (append (cdr ra) (cdr rp)))))

         ((FORALL FORSOME IOTA)
          ;; Drop ctx assumptions shadowed by bv before descending into body.
          (let ((bv   (cadr expr))
                (body (caddr expr)))
            (if (member bv schema-vars)
                (cons expr '())
                (let ((r (rewrite-expr pattern replacement schema-vars conditions
                                       body
                                       (lc-drop-shadowed (list bv) local-ctx))))
                  (cons (list head bv (car r)) (cdr r))))))

         ((VNB-LAMBDA)
          ;; Symbolic lambda binder: refuse to rewrite under it if any bound
          ;; var coincides with a schema-var (would capture); otherwise recurse
          ;; into the body, dropping ctx assumptions shadowed by the bvars.
          (let* ((bind-spec (cadr expr))
                 (body      (caddr expr))
                 (bvars     (vnb-lambda-bvars bind-spec)))
            (if (let loop ((bs bvars))
                  (cond ((null? bs) #f)
                        ((member (car bs) schema-vars) #t)
                        (else (loop (cdr bs)))))
                (cons expr '())
                (let ((r (rewrite-expr pattern replacement schema-vars conditions
                                       body
                                       (lc-drop-shadowed bvars local-ctx))))
                  (cons (list 'VNB-LAMBDA bind-spec (car r)) (cdr r))))))

         (else
          ;; General compound.  Head may itself be a pair (e.g. ((MUL m) a b))
          ;; — rewrite into it too; symbol heads pass through unchanged.
          (let* ((rh        (if (pair? head)
                                (rewrite-expr pattern replacement schema-vars
                                              conditions head local-ctx)
                                (cons head '())))
                 (new-head  (car rh))
                 (head-mins (cdr rh)))
            (let loop ((args (cdr expr)) (new '()) (minors head-mins))
              (if (null? args)
                  (cons (cons new-head (reverse new)) minors)
                  (let ((r (rewrite-expr pattern replacement schema-vars conditions
                                         (car args) local-ctx)))
                    (loop (cdr args)
                          (cons (car r) new)
                          (append minors (cdr r)))))))))))))

;;; -----------------------------------------------------------------------
;;; Elementary macete: built from a theorem

;;; SOUNDNESS check (REVIEW.md S-10): a schema-var that appears in conditions
;;; or replacement but NOT in the source pattern would be left unbound by the
;;; matcher; condition-holds? would then match against any local-ctx
;;; assumption that coincidentally used the same symbol name.  Returns the
;;; list of rogue vars (empty list = clean).
(define (theorem-rogue-schema-vars schema-vars conditions source replacement)
  (let ((src-fvs   (free-vars source))
        (extra-fvs (apply append
                          (cons (free-vars replacement)
                                (map free-vars conditions)))))
    (filter (lambda (v)
              (and (member v schema-vars)
                   (not (member v src-fvs))))
            extra-fvs)))

;;; Inert macete: never fires.  Returned for theorems whose macete form is
;;; unsound (see S-10) so the THEOREM stays registered in *theorem-table*
;;; and is usable via theorem-assumption + manual instantiation, while the
;;; broken rewrite is silently skipped.
(define (inert-macete) (lambda (sqn) #f))

;;; Log of theorems whose macete form was unsound (S-10) and was therefore
;;; replaced with `inert-macete`.  The theorem itself is still registered in
;;; *theorem-table* and usable via (ta 'name) / backchain / instantiation;
;;; only the rewrite-rule installation is skipped.  Call (display-inert-macetes)
;;; to enumerate.
(define *inert-macetes* '())

;;; Prenex normalization for macete generation.
;;;
;;; strip-foralls peels only LEADING quantifiers.  A theorem whose
;;; rewrite-bearing IFF/= is buried under an IMPLIES or AND --- e.g.
;;;   (FORALL a b (IMPLIES (AND ...) (FORALL x (IFF ...))))
;;; --- hides its FORALL x, so extract-rewrite-patterns never sees the IFF
;;; and falls through to the degenerate (replacement = TRUTH) macete.
;;;
;;; prenex-positive pulls FORALLs occurring in POSITIVE position to the
;;; front.  The transforms are logical equivalences:
;;;   (IMPLIES H (FORALL x P))  ==  (FORALL x (IMPLIES H P))   [x not free in H]
;;;   (AND A (FORALL x P))      ==  (FORALL x (AND A P))       [x not free in A]
;;; A clashing x is alpha-renamed first.  We descend ONLY through positive
;;; positions: the consequent of IMPLIES and both sides of AND.  We do NOT
;;; pull through an IMPLIES antecedent, OR, NOT, or IFF --- a FORALL there is
;;; not in positive position and the pull would be unsound.  Macete-yielding
;;; theorems are universally-quantified implications/iffs, so every buried
;;; FORALL we care about is positive.
(define (prenex-positive f)
  (cond
    ((not (pair? f)) f)
    ((eq? (car f) 'FORALL)
     `(FORALL ,(cadr f) ,(prenex-positive (caddr f))))
    ((eq? (car f) 'IMPLIES)
     (let ((h (cadr f))
           (c (prenex-positive (caddr f))))
       (if (and (pair? c) (eq? (car c) 'FORALL))
           (let* ((x      (cadr c))
                  (body   (caddr c))
                  (clash  (member x (free-vars h)))
                  (x*     (if clash (generate-uninterned-symbol x) x))
                  (body*  (if clash (subst-free x x* body) body)))
             `(FORALL ,x* ,(prenex-positive `(IMPLIES ,h ,body*))))
           `(IMPLIES ,h ,c))))
    ((eq? (car f) 'AND)
     (let ((a (prenex-positive (cadr f)))
           (b (prenex-positive (caddr f))))
       (cond
         ((and (pair? a) (eq? (car a) 'FORALL))
          (let* ((x     (cadr a))
                 (body  (caddr a))
                 (clash (member x (free-vars b)))
                 (x*    (if clash (generate-uninterned-symbol x) x))
                 (body* (if clash (subst-free x x* body) body)))
            `(FORALL ,x* ,(prenex-positive `(AND ,body* ,b)))))
         ((and (pair? b) (eq? (car b) 'FORALL))
          (let* ((x     (cadr b))
                 (body  (caddr b))
                 (clash (member x (free-vars a)))
                 (x*    (if clash (generate-uninterned-symbol x) x))
                 (body* (if clash (subst-free x x* body) body)))
            `(FORALL ,x* ,(prenex-positive `(AND ,a ,body*)))))
         (else `(AND ,a ,b)))))
    (else f)))

(define (theorem->elementary-macete theorem-formula #!optional name)
  (let-values (((schema-vars core)
                (strip-foralls (prenex-positive theorem-formula))))
    (let-values (((conditions source replacement)
                  (extract-rewrite-patterns core)))
      (let ((rogue (theorem-rogue-schema-vars schema-vars conditions
                                              source replacement)))
        (cond
          ((not (null? rogue))
           ;; rogue-var check runs on the original names for a readable report
           (set! *inert-macetes*
             (cons (cons (if (default-object? name) '<anonymous> name) rogue)
                   *inert-macetes*))
           (inert-macete))
          (else
           ;; Gensym the schema variables so they cannot collide with object
           ;; variables in a goal.  The rewriter's binder guards
           ;; (member bv schema-vars) at FORALL/FORSOME/IOTA/SEP/lambda then
           ;; never spuriously refuse to descend just because a goal's bound
           ;; variable happens to share a name with a schema variable.
           (let* ((renaming (map (lambda (v)
                                   (cons v (generate-uninterned-symbol v)))
                                 schema-vars))
                  (rename   (lambda (e)
                              (let loop ((rs renaming) (e e))
                                (if (null? rs)
                                    e
                                    (loop (cdr rs)
                                          (subst-free (caar rs) (cdar rs) e)))))))
             (make-elementary-macete
              (map cdr renaming)
              (map rename conditions)
              (rename source)
              (rename replacement)))))))))

(define (display-inert-macetes)
  (cond
    ((null? *inert-macetes*)
     (display "No inert macetes.\n"))
    (else
     (display ";; ")
     (display (length *inert-macetes*))
     (display " theorem(s) registered as named-only (macete form unsound, S-10):\n")
     (for-each
       (lambda (entry)
         (display ";;   ")
         (display (car entry))
         (display " -- rogue schema vars: ")
         (write (cdr entry))
         (newline))
       (reverse *inert-macetes*)))))

(define (strip-foralls formula)
  (let loop ((f formula) (vars '()))
    (if (and (pair? f) (eq? (car f) 'FORALL))
        (loop (caddr f) (cons (cadr f) vars))
        (values (reverse vars) f))))

(define (extract-rewrite-patterns core)
  (cond
    ((and (pair? core) (eq? (car core) 'IMPLIES))
     (let ((hyp (binary-left core))
           (con (binary-right core)))
       (let ((conditions (flatten-and hyp)))
         (let-values (((s r) (extract-equation con)))
           (values conditions s r)))))
    (else
     (let-values (((s r) (extract-equation core)))
       (values '() s r)))))

(define (flatten-and f)
  (if (and (pair? f) (eq? (car f) 'AND))
      (append (flatten-and (binary-left f))
              (flatten-and (binary-right f)))
      (list f)))

(define (extract-equation f)
  (cond
    ((and (pair? f) (eq? (car f) '=))
     (values (binary-left f) (binary-right f)))
    ((and (pair? f) (eq? (car f) 'IFF))
     (values (binary-left f) (binary-right f)))
    (else
     (values f 'TRUTH))))

(define (make-elementary-macete schema-vars conditions source replacement)
  (lambda (sqn)
    (let* ((asms      (sequent-node-assumptions sqn))
           (goal      (sequent-node-assertion   sqn))
           (g         (wff-formula goal))
           (dg        (sqn-dg sqn))
           ;; Seed the local context with the sequent's current assumptions.
           (local-ctx (map wff-formula asms))
           (result    (rewrite-expr source replacement schema-vars
                                    conditions g local-ctx)))
      (let ((new-g       (car result))
            (minor-prems (cdr result)))
        (if (alpha-equiv? new-g g)
            #f
            (let ((new-subgoals
                   (cons (make-sequent asms (wff-child goal new-g))
                         (map (lambda (mp)
                                (make-sequent asms (wff-child goal mp)))
                              minor-prems))))
              (dg-apply-rule! dg `(macete ,source ,replacement)
                              new-subgoals sqn)))))))

;;; -----------------------------------------------------------------------
;;; Compound macete constructors

(define (macete-series . macetes)
  (lambda (sqn)
    (let loop ((ms macetes))
      (cond
        ((null? ms) #t)
        (else
         (let ((result ((car ms) sqn)))
           (if result
               (loop (cdr ms))
               #f)))))))

(define (macete-repeat macete)
  (lambda (sqn)
    (let loop ((changed #f))
      (let ((result (macete sqn)))
        (if result
            (loop #t)
            changed)))))

(define (macete-try macete)
  (lambda (sqn)
    (macete sqn)
    #t))

(define (macete-choice . macetes)
  (lambda (sqn)
    (let loop ((ms macetes))
      (if (null? ms)
          #f
          (let ((r ((car ms) sqn)))
            (if r r (loop (cdr ms))))))))

;;; -----------------------------------------------------------------------
;;; Install-theorem: registers a theorem and its macete

(define *theorem-table* (make-equal-hash-table))

;;; Names of results established by proof (prove-and-install! / cmd-qed),
;;; as opposed to axioms.  Used by (catalog) to split the registry.
(define *proven-theorem-names* '())

(define (register-proven-theorem! name)
  (unless (memq name *proven-theorem-names*)
    (set! *proven-theorem-names* (cons name *proven-theorem-names*))))

;;; Names of results in the PROOF SUPPORT SET: claimed-provable results
;;; we accept without a mechanical proof in VNB.  They are logically
;;; treated the same as axioms or theorems (usable as assumptions, install
;;; macetes), but tracked separately by (catalog) so the distinction is
;;; visible.  Examples include classical results (e.g. Well-Ordering)
;;; that are too expensive to mechanize and not in active doubt.
(define *support-theorem-names* '())

(define (rev-name-of name)
  (string->symbol (string-append (symbol->string name) "-rev")))

(define (register-support-theorem! name)
  (unless (memq name *support-theorem-names*)
    (set! *support-theorem-names* (cons name *support-theorem-names*)))
  ;; The auto-generated -rev companion is the same fact flipped; if it exists,
  ;; it belongs to the PSS alongside its forward (else it orphans as an
  ;; asserted/not-PSS leaf -- the early "fuzzy border" leak).
  (let ((rev (rev-name-of name)))
    (when (and (hash-table-ref/default *theorem-table* rev #f)
               (not (memq rev *support-theorem-names*)))
      (set! *support-theorem-names* (cons rev *support-theorem-names*)))))

;;; -----------------------------------------------------------------------
;;; WARRANTS -- the grounds on which we accept a statement.
;;;
;;; Any axiom / PSS entry / theorem may carry a WARRANT: a record
;;; (kind . text) saying WHY we are entitled to assert it.  This makes the
;;; library's epistemic status explicit and honest -- "asserted as an axiom"
;;; otherwise hides whether the thing is a deep classical theorem, a
;;; one-line triviality not yet ground out, or a genuine primitive.  Warrant
;;; kinds, weakest to strongest:
;;;
;;;   hand-wave  -- heuristic / plausibility argument; convincing, not rigorous.
;;;   well-known -- a standard textbook fact, asserted without argument.
;;;   reference  -- cites a specific source (named in the text).
;;;   informal   -- a rigorous paper-proof exists (often sketched in the text
;;;                 or the file comment), just not mechanized in VNB.
;;;   proof      -- a machine-checked VNB proof exists.
;;;
;;; A warrant is a promissory note, not a permanent verdict: any weaker kind
;;; may later be discharged into `proof'.  Nothing logical hangs on it -- it
;;; is metadata for review and triage.
(define *warrant-kinds* '(hand-wave well-known reference informal proof))

(define *warrants* (make-equal-hash-table))   ; name -> (kind . text)

(define (register-warrant! name kind text)
  (unless (memq kind *warrant-kinds*)
    (display ";; WARNING: unknown warrant kind ")
    (write kind) (display " for ") (write name)
    (display " -- expected one of ")
    (write *warrant-kinds*) (newline))
  (hash-table-set! *warrants* name (cons kind text))
  ;; Propagate the warrant to the auto-generated -rev companion (same fact,
  ;; flipped), so warranting a forward doesn't leave its reverse unwarranted.
  (let ((rev (rev-name-of name)))
    (when (hash-table-ref/default *theorem-table* rev #f)
      (hash-table-set! *warrants* rev (cons kind text))))
  name)

(define (warrant-of name)
  (hash-table-ref/default *warrants* name #f))

;;; -----------------------------------------------------------------------
;;; Provenance: the epistemic origin of an installed statement, orthogonal
;;; to the support/proven display tags.  Every theorem-table entry gets one,
;;; stamped at install time from the dynamic variable *current-provenance*:
;;;
;;;   primitive    -- a genuine VNB foundational axiom (the trusted base):
;;;                   the make-vnb-base-theory core + theorem-library/axioms.
;;;   definitional -- a conservative definitional extension emitted by a
;;;                   def-/declare- form (IS-X folding, accessor laws, view
;;;                   typing + auto-specializations).  Adds no logical
;;;                   strength: it only names new vocabulary.
;;;   asserted     -- genuine mathematical content accepted WITHOUT a machine
;;;                   proof.  The bare default; the natural home for a warrant.
;;;   proven       -- machine-checked (installed via theory-add-theorem!).
;;;
;;; The def-/declare- forms fluid-let this to 'definitional around their
;;; bodies; the base-theory build and the axioms file fluid-let it to
;;; 'primitive; theory-add-theorem! binds 'proven.  Everything else --
;;; including every hand-written (theory-add-axiom! ...) and (support ...)
;;; in the library files -- falls through to 'asserted.
(define *provenance-kinds* '(primitive definitional asserted proven))

(define *current-provenance* 'asserted)          ; default for bare installs

(define *provenance* (make-equal-hash-table))    ; name -> kind

(define (register-provenance! name kind)
  (hash-table-set! *provenance* name kind)
  name)

(define (provenance-of name)
  (hash-table-ref/default *provenance* name 'asserted))

;;; Binary connectives whose theorems should auto-install a reverse-direction
;;; companion macete:
;;;   IFF -- (P iff Q) is symmetric.
;;;   =   -- (a = b) is symmetric.  Strict equality; both sides defined.
;;;   ==  -- (a == b) is symmetric quasi-equality (both undef OR both equal).
;;; All three are reflexively symmetric, so the flipped formula is a
;;; logical consequence of the original.
(define *symmetric-core-heads* '(IFF = ==))

;;; If the formula's core (under any FORALL prefix and at-most-one IMPLIES)
;;; is one of the symmetric binary forms listed in *symmetric-core-heads*,
;;; return the formula with that form's arguments swapped.  Returns #f if
;;; no such core is found.  Used by install-theorem! to auto-install a
;;; reverse-direction macete name-rev.
(define (flip-symmetric-core-in-formula f)
  (cond
    ((not (pair? f)) #f)
    ((eq? (car f) 'FORALL)
     (let ((flipped (flip-symmetric-core-in-formula (caddr f))))
       (and flipped `(FORALL ,(cadr f) ,flipped))))
    ((eq? (car f) 'IMPLIES)
     (let ((flipped (flip-symmetric-core-in-formula (caddr f))))
       (and flipped `(IMPLIES ,(cadr f) ,flipped))))
    ((memq (car f) *symmetric-core-heads*)
     `(,(car f) ,(caddr f) ,(cadr f)))
    (else #f)))

(define (install-theorem! name formula-or-wff)
  (vnb-guard
    (lambda ()
      (let ((formula (if (wff? formula-or-wff)
                         (wff-formula formula-or-wff)
                         formula-or-wff)))
        (hash-table-set! *theorem-table* name formula)
        (register-provenance! name *current-provenance*)
        (install-macete! name (theorem->elementary-macete formula name))
        ;; Symmetric-core theorems also install a reverse-direction macete.
        (let ((flipped (flip-symmetric-core-in-formula formula)))
          (when flipped
            (let ((rev-name (string->symbol
                             (string-append (symbol->string name) "-rev"))))
              (hash-table-set! *theorem-table* rev-name flipped)
              (register-provenance! rev-name *current-provenance*)
              (install-macete! rev-name
                (theorem->elementary-macete flipped rev-name)))))
        name))))

(define (lookup-theorem name)
  (or (hash-table-ref/default *theorem-table* name #f)
      (error "lookup-theorem: unknown theorem" name)))

;;; -----------------------------------------------------------------------
;;; Apply a named macete to a sequent node

(define (apply-macete! name sqn)
  ((lookup-macete name) sqn))

;;; -----------------------------------------------------------------------
;;; Apply a named macete to a wff, outside any proof.
;;; Returns a new wff if any rewrite fires, or #f if nothing matches.
;;; Uses an empty local context as the seed; lc-extend builds it up
;;; as the rewriter descends into implications, conjunctions, etc.

(define (apply-macete name w)
  (vnb-guard
    (lambda ()
      (let-values (((schema-vars core)
                    (strip-foralls (prenex-positive (lookup-theorem name)))))
        (let-values (((conditions source replacement)
                      (extract-rewrite-patterns core)))
          (let* ((g      (wff-formula w))
                 (result (rewrite-expr source replacement schema-vars
                                       conditions g '()))
                 (new-g  (car result)))
            (if (alpha-equiv? new-g g) #f (wff-child w new-g))))))))

;;; -----------------------------------------------------------------------
;;; Apply a definitional/equational macete to an ASSUMPTION -- the
;;; hypothesis-side dual of apply-macete!.  Where apply-macete! unfolds a
;;; defined predicate in the GOAL, this unfolds it inside a cited assumption,
;;; replacing H by its equivalent body IN PLACE.  Together with `ai` this is
;;; the hypothesis-side counterpart of the goal-side `mac`/`di` pair: it lets
;;; a proof reach the typing conjuncts and quantified payload that were
;;; otherwise locked inside a folded hypothesis.
;;;
;;; SOUNDNESS.  Replacing assumption H by H' is sound exactly when H => H'.
;;; We gate on macete-equivalence?: the macete's core must be a genuine
;;; two-way equivalence (IFF / = / ==, the same class install-theorem! flags
;;; for a -rev companion), so H <=> H' (UNDER the macete's side-conditions)
;;; and the rewrite loses nothing.  Every def-predicate / def-functoid unfold
;;; is an unconditional IFF and qualifies.
;;;
;;; CONDITIONAL equivalences (e.g. preimage-complement, an equation that holds
;;; only when the typing side-conditions do) are supported the IMPS way: the
;;; rewrite fires and each side-condition that is not already discharged from
;;; the assumption context is SPAWNED as a minor-premise subgoal -- never
;;; silently dropped.  Conditions already present among the assumptions are
;;; discharged automatically (local-ctx is seeded with them), so unfolding the
;;; other hypotheses first -- with mac-h -- makes most side-conditions vanish.
;;; The main rewritten sequent is returned FIRST so focus-after-rule keeps the
;;; user on the main line, with the conditions as additional open goals.

(define (macete-equivalence? name)
  (let ((thm (hash-table-ref/default *theorem-table* name #f)))
    (and thm (flip-symmetric-core-in-formula thm) #t)))

;;; The S-10 rogue (undetermined-by-the-match) schema vars of name's
;;; source->replacement rewrite; '() = clean.  mac-h refuses a rewrite with
;;; rogue vars, declining the inert/-rev directions exactly as the goal side
;;; does at install time -- otherwise a var like a codomain `t' present only in
;;; the replacement/conditions would be conjured free.
(define (macete-rogue-vars name)
  (let-values (((schema-vars core)
                (strip-foralls (prenex-positive (lookup-theorem name)))))
    (let-values (((conditions source replacement)
                  (extract-rewrite-patterns core)))
      (let loop ((vs (theorem-rogue-schema-vars schema-vars conditions
                                                source replacement))
                 (seen '()))
        (cond ((null? vs) (reverse seen))
              ((member (car vs) seen) (loop (cdr vs) seen))
              (else (loop (cdr vs) (cons (car vs) seen))))))))

(define (apply-macete-to-assumption! name hyp-formula sqn)
  (and (macete-equivalence? name)
       (null? (macete-rogue-vars name))
       (let* ((asms (sequent-node-assumptions sqn))
              (f    (asms-find asms hyp-formula)))
         (and f
              (let-values (((schema-vars core)
                            (strip-foralls (prenex-positive (lookup-theorem name)))))
                (let-values (((conditions source replacement)
                              (extract-rewrite-patterns core)))
                  (let* ((goal      (sequent-node-assertion sqn))
                         (dg        (sqn-dg sqn))
                         (h         (wff-formula f))
                         (local-ctx (map wff-formula asms))
                         (result    (fluid-let ((*macete-spawn-conditions?* #t))
                                      (rewrite-expr source replacement schema-vars
                                                    conditions h local-ctx)))
                         (new-h     (car result))
                         (minors    (cdr result)))
                    (and (not (alpha-equiv? new-h h))
                         (dg-apply-rule! dg `(macete-hyp ,source ,replacement)
                           (cons (make-sequent
                                  (context-add-assumption
                                   (context-remove-assumption asms f)
                                   (wff-child f new-h))
                                  goal)
                                 (map (lambda (mp)
                                        (make-sequent asms (wff-child goal mp)))
                                      minors))
                           sqn)))))))))
