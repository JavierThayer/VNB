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
    ;; Numeral <-> successor bridge: a pattern (succ P) matches a positive
    ;; integer literal m by treating m as (succ (m-1)) and matching P against
    ;; m-1.  So (succ n)-headed recursion axioms (nth-deriv-succ, mpow-succ,
    ;; power-succ, ...) fire on numerals 1,2,3,... directly, not only on
    ;; syntactic succ-towers -- the numeral<->succ normalizer that makes
    ;; concrete-order recursion dumb-assemblable (scout/mac use this matcher).
    ;; Purely additive: only ADDS valid matches (m really does equal succ(m-1)).
    ((and (pair? pattern) (eq? (car pattern) 'succ)
          (pair? (cdr pattern)) (null? (cddr pattern))
          (integer? expr) (positive? expr))
     (match-expr (cadr pattern) (- expr 1) schema-vars))
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
       ;; NTH: no special case.  The old one demanded the two indices be
       ;; equal?, so a schema variable in index position could never bind and
       ;; no macete about a general index could ever fire.  See free-vars
       ;; (expressions.scm) for the whole defect.  (2026-08-04)
       ((SEP)
        (and (equal? (cadr pattern) (cadr expr))
             (let ((ma (match-expr (caddr pattern)  (caddr expr)  schema-vars))
                   (mp (match-expr (cadddr pattern) (cadddr expr) schema-vars)))
               (and ma mp (merge-subst ma mp)))))
       ((FORALL FORSOME IOTA)
        ;; Alpha-aware: the bound variables need not be the SAME name, only
        ;; alpha-equivalent.  When they differ, rename BOTH to a fresh var
        ;; (avoiding capture of any schema var or free var) and match the
        ;; renamed bodies.  This lets bc*/mac backchain a lemma whose
        ;; conclusion is FORSOME-/FORALL-headed against a goal with a
        ;; differently-named bound variable (e.g. an existence lemma
        ;; (... => FORSOME N. P(N)) closing a goal FORSOME F. P(F)).
        (let ((pv (cadr pattern)) (ev (cadr expr)))
          (cond
            ((eq? pv ev)
             (match-expr (caddr pattern) (caddr expr) schema-vars))
            ;; A schema-var hole in the BINDER position stays unsupported (we
            ;; must not rename a schema var away) -- keep the old non-match.
            ((member pv schema-vars) #f)
            (else
             (let ((z (fresh-var pv (caddr pattern) (caddr expr))))
               (match-expr (subst-free pv z (caddr pattern))
                           (subst-free ev z (caddr expr))
                           schema-vars))))))
       (else
        (match-list-with-rest (cdr pattern) (cdr expr) schema-vars))))
    ;; Compound-operator application: pattern ((DIST s) x y) vs expr
    ;; ((DIST Se) ae be) -- the operator is itself an application (a structure
    ;; accessor applied to its instance: (DIST s), (mul r), ...).  The
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
;;;
;;; THE ORDINARY BINDINGS ARE APPLIED SIMULTANEOUSLY -- `subst-free*'
;;; (expressions.scm), never a fold of subst-free.  See the comment there: a
;;; sequential fold silently rewrote the caller's `n' and `u' INSIDE the term it
;;; had just matched to SPANS' `sm' parameter.
(define (apply-subst subst expr)
  (let loop ((bs subst) (ord '()) (rest '()))
    (cond
      ((null? bs)
       (let ((after-ord (subst-free* (reverse ord) expr)))
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
;;; A condition is "held" in a local context if it is TRUTH, is
;;; alpha-equivalent to some formula already in the context, or is a true
;;; closed arithmetic sentence.  Numerals and succ-towers are compared in one
;;; canonical form.
;;;
;;; The last two clauses exist because the numeral<->succ bridge in match-expr
;;; is ONE-DIRECTIONAL.  It lets a pattern (DET R (succ n) A) match the goal
;;; DET(r,1,a) with n:=0 -- and then the instantiated conditions come back as
;;; (IN 0 NN), which no one put in the context, and
;;; (IN A (MAT (succ 0) (succ 0) (CARR R))), while the context holds
;;; (IN a (MAT 1 1 (CARR r))).  Alpha-equivalence alone says no to both, so a
;;; definitional recursion axiom keyed on (succ n) was unusable at EVERY
;;; literal size: `mac det-cofactor' on DET(r,1,a) reported "not applicable"
;;; even with both typing hypotheses in context (probed 2026-07-24).
;;;
;;; Neither clause widens what may be believed.  numeral-collapse rewrites
;;; (succ k) to k+1 for a literal k, which is sound for the same reason the
;;; match-expr bridge is -- succ(k) IS k+1 on a numeral -- and succ_ORD
;;; collapses with it, exactly as arith-eval-term already treats the two as one
;;; on ground naturals.  The arithmetic clause defers to arith-eval-formula,
;;; the decision procedure the trusted `arith' rule itself runs, and accepts
;;; only a verdict of #t (never 'UNDEF).

;;; Fold (succ k) / (succ_ORD k) over a literal k to k+1, bottom up.
;;; Non-pairs -- symbols, numbers, functoid records -- are returned as they are.
(define (numeral-collapse e)
  (if (not (pair? e))
      e
      (let ((parts (map numeral-collapse e)))
        (if (and (memq (car parts) '(succ succ_ORD))
                 (pair? (cdr parts))
                 (null? (cddr parts))
                 (exact-nonnegative-integer? (cadr parts)))
            (+ (cadr parts) 1)
            parts))))

(define (condition-holds? formula local-ctx)
  (or (equal? formula 'TRUTH)
      (let loop ((ctx local-ctx))
        (cond ((null? ctx) #f)
              ((alpha-equiv? formula (car ctx)) #t)
              (else (loop (cdr ctx)))))
      ;; Slow path: same search, both sides in numeral-collapsed form.
      (let ((f (numeral-collapse formula)))
        (let loop ((ctx local-ctx))
          (cond ((null? ctx) #f)
                ((alpha-equiv? f (numeral-collapse (car ctx))) #t)
                (else (loop (cdr ctx))))))
      ;; Ground arithmetic: (IN 0 NN), (<= 1 2), ... need no hypothesis.
      (eq? #t (arith-eval-formula (numeral-collapse formula)))))

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

         ;; NTH: no special case -- an occurrence inside the INDEX is rewritten
         ;; like any other argument, by the general compound branch below.
         ;; See free-vars (expressions.scm).  (2026-08-04)

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
                 (dom       (caddr expr))
                 (body      (cadddr expr))
                 (bvars     (vnb-lambda-bvars bind-spec)))
            (if (let loop ((bs bvars))
                  (cond ((null? bs) #f)
                        ((member (car bs) schema-vars) #t)
                        (else (loop (cdr bs)))))
                (cons expr '())
                ;; The DOMAIN is outside the binder, so it is rewritten in the
                ;; ambient local-ctx, like SEP's and BIG-UNION's A.
                (let* ((rd (rewrite-expr pattern replacement schema-vars conditions
                                         dom local-ctx))
                       (r  (rewrite-expr pattern replacement schema-vars conditions
                                         body
                                         (lc-drop-shadowed bvars local-ctx))))
                  (cons (list 'VNB-LAMBDA bind-spec (car rd) (car r))
                        (append (cdr rd) (cdr r)))))))

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

;;; DELIBERATELY named-only.  A different failure from S-10, and the difference
;;; matters: S-10 catches a rewrite that would be UNSOUND, this catches one that
;;; is perfectly sound and ruinous to fire AUTOMATICALLY.
;;;
;;; The motivating case is `app-graph' (theory.scm), which defines application as
;;; the description over the graph.  Its left-hand side is a bare application
;;; `(f x)' with both f and x schema variables, so as a live macete it matches
;;; EVERY application in EVERY goal and rewrites each into an IOTA -- every
;;; `mac' anywhere would detonate.  The theorem is wanted; the automatic rewrite
;;; is not.
;;;
;;; Declare BEFORE the theorem is installed.  A named-only theorem stays fully
;;; usable by name: `ta', `fact', backchain, manual instantiation.
(define *named-only-macetes* '())

(define (declare-named-only! name reason)
  (set! *named-only-macetes* (cons (cons name reason) *named-only-macetes*))
  ;; the -rev companion (install-theorem! mints one for a symmetric core) must
  ;; be suppressed too, or the reverse direction fires on every IOTA instead.
  (let ((rev (string->symbol (string-append (symbol->string name) "-rev"))))
    (set! *named-only-macetes* (cons (cons rev reason) *named-only-macetes*)))
  name)

(define (named-only-macete? name)
  (and (symbol? name) (assq name *named-only-macetes*)))

(define (display-named-only-macetes)
  (if (null? *named-only-macetes*)
      (display "No named-only macetes.\n")
      (for-each (lambda (e)
                  (display "  ") (display (car e))
                  (display " -- ") (display (cdr e)) (newline))
                (reverse *named-only-macetes*))))

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
          ((and (not (default-object? name)) (named-only-macete? name))
           (inert-macete))               ; sound, but must not fire on its own
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

;; Peel ALL leading IMPLIES antecedents into the condition list, then read the
;; equation.  Handles both the flat shape (IMPLIES (AND c1 c2 ...) (= L R)) and
;; the CURRIED/nested shape (IMPLIES c1 (IMPLIES c2 (IMPLIES c3 (= L R)))) that
;; the `tf' helper produces -- the shape almost every conditional support (all
;; the finsum rearrangement lemmas) is written in.  The old version peeled only
;; ONE IMPLIES, so a curried lemma left source = the inner nested-IMPLIES and
;; replacement = TRUTH: a dead macete that never matched its own LHS, silently
;; forcing those lemmas to be usable only through forward `fact'.  Each peeled
;; antecedent is flatten-and'd so a mixed (IMPLIES (AND a b) (IMPLIES c ...))
;; still splits cleanly.  The extracted conditions become minor premises.
(define (extract-rewrite-patterns core)
  (let loop ((core core) (conditions '()))
    (cond
      ((and (pair? core) (eq? (car core) 'IMPLIES))
       (loop (binary-right core)
             (append conditions (flatten-and (binary-left core)))))
      (else
       (let-values (((s r) (extract-equation core)))
         (values conditions s r))))))

(define (flatten-and f)
  (if (and (pair? f) (eq? (car f) 'AND))
      (append (flatten-and (binary-left f))
              (flatten-and (binary-right f)))
      (list f)))

(define (extract-equation f)
  (cond
    ((and (pair? f) (eq? (car f) '=))
     (values (binary-left f) (binary-right f)))
    ;; quasi-equality rewrites just like = : quasi-equal terms are
    ;; interchangeable (same definedness, same value), so a `==' macete is a
    ;; sound rewrite rule.  Needed since the partial-op DEFINING equations
    ;; (binplus-apply, nary-*, ...) are stated with == (true off-domain too).
    ((and (pair? f) (eq? (car f) '==))
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

;;; name -> the source pathname where it was installed (current-load-pathname at
;;; install time).  Used by the browser topic pages to link each entry to the
;;; .scm file that states/proves it.  #f-valued (REPL installs) entries skipped.
(define *theorem-source* (make-equal-hash-table))

;;; Memo of each lemma's conclusion-fingerprint at the default depth (the key
;;; the backchain-candidate scan recomputes per call).  A lemma's conclusion
;;; never changes once installed, so this turns the hot retrieval loop (scout /
;;; auto-prove sweep, suggest-backchain-candidates) from O(corpus) fingerprint
;;; recomputes per node into O(corpus) hash lookups.  Filled lazily by
;;; `lemma-fingerprint' (interactive.scm); invalidated here on (re)install.
(define *lemma-fingerprint-memo* (make-equal-hash-table))   ; name -> fp

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

;;; -----------------------------------------------------------------------
;;; BOOK REGISTRY -- the sources a `reference' warrant may cite.
;;;
;;; A reference splits into two jobs that were being conflated in the free
;;; text.  A HUMAN citation -- a named/numbered result, edition-stable
;;; ("Lang, Algebra, Prop. II.2.1"), what a person reads and re-finds on any
;;; edition.  And an optional MACHINE anchor -- {book-key, page} -- a tool
;;; resolves against the PDF the user actually holds.  ONE registry carries
;;; both: a short key -> the book's cite name + title (+ edition, + local PDF).
;;;
;;;   (cite-book! 'lang "Lang" "Algebra" "3rd ed." "/home/ubuntu/books/lang.pdf")
;;;   (warrant! 'foo 'reference '(lang "Prop. II.2.1"))       ; human only
;;;   (warrant! 'foo 'reference '(lang "Prop. II.2.1" 87))    ; + page anchor
;;;
;;; DELIBERATELY additive and reversible: a reference locator may still be a
;;; bare STRING (the pre-registry form, 158 legacy entries), in which case it
;;; is the human citation verbatim -- no key, no anchor.  Nothing is migrated;
;;; if the discipline proves unworkable, the registry lifts out cleanly.
(define-record-type <book>
  (make-book bkey name title edition pdf-path)
  book?
  (bkey     book-key)
  (name     book-name)                  ; short cite name, e.g. "Lang"
  (title    book-title)                 ; e.g. "Algebra"
  (edition  book-edition)               ; e.g. "3rd ed."  (NOT in the inline cite)
  (pdf-path book-pdf-path))             ; local PDF, or #f when not yet on disk

(define *books* (make-equal-hash-table))   ; key-symbol -> <book>

(define (register-book! key name title edition pdf-path)
  (define (blank? s) (or (not s) (and (string? s) (string-null? s))))
  (hash-table-set! *books* key
    (make-book key name
               (and (not (blank? title)) title)
               (and (not (blank? edition)) edition)
               (and (not (blank? pdf-path)) pdf-path)))
  key)

(define (book-of key) (hash-table-ref/default *books* key #f))

;;; "Lang, Algebra" -- short name plus title (title dropped if absent).  Falls
;;; back to the bare key string when the book was never registered.
(define (book-cite-name bk key)
  (if bk
      (if (book-title bk)
          (string-append (book-name bk) ", " (book-title bk))
          (book-name bk))
      (symbol->string key)))

;;; Parse a reference locator (as passed to warrant! with kind 'reference).
;;; Returns (values HUMAN-STRING ANCHOR) where ANCHOR is #f or (book-key . page):
;;;   STRING             -- legacy: HUMAN = the string verbatim, ANCHOR = #f.
;;;   (KEY LOCATOR)      -- HUMAN = "<cite-name>, <LOCATOR>", ANCHOR = #f.
;;;   (KEY LOCATOR PAGE) -- additionally ANCHOR = (KEY . PAGE).
;;; An unregistered KEY warns (like an unknown warrant kind) but still renders.
(define (reference-parse loc)
  (cond
    ((string? loc) (values loc #f))
    ((and (pair? loc) (symbol? (car loc)))
     (let* ((key   (car loc))
            (where (and (pair? (cdr loc)) (cadr loc)))
            (page  (and (pair? (cdr loc)) (pair? (cddr loc)) (caddr loc)))
            (bk    (book-of key)))
       (unless bk
         (display ";; WARNING: reference cites unregistered book ")
         (write key) (display " -- register it with (cite-book! ...)") (newline))
       (values (if (and where (not (string-null? where)))
                   (string-append (book-cite-name bk key) ", " where)
                   (book-cite-name bk key))
               (and page (cons key page)))))
    (else
     (display ";; WARNING: malformed reference locator ") (write loc) (newline)
     (values (call-with-output-string (lambda (p) (write loc p))) #f))))

(define *reference-anchors* (make-equal-hash-table))  ; name -> (book-key . page)
(define (reference-anchor-of name)
  (hash-table-ref/default *reference-anchors* name #f))

;;; -----------------------------------------------------------------------
;;; REST-ON GRAPH -- declared logical dependencies of ASSERTED theorems.
;;;
;;; An asserted (e.g. reference-warranted) theorem has no VNB proof, so it is a
;;; LEAF in the proof-citation graph: the cycle checker cannot see that its
;;; TEXTBOOK proof rests on other base theorems, hence cannot catch a circular
;;; reference base.  (rests-on! 'R '(A B)) records that R's cited proof depends
;;; on A and B -- asserted metadata (the machine enforces the declared order is
;;; acyclic; it cannot verify the claim itself).  proof-debt.scm's
;;; proof-citations-of reads this for NON-proven nodes, so the SAME
;;; proof-cycle-check then walks the asserted base too, and a new proof is
;;; non-circular by construction (unreachable from its own declared base).  A
;;; proven node ignores its rests-on (its real proof citations supersede the
;;; declaration).  Undeclared => a sink, exactly as before.  Storage lives here
;;; (loaded early, before any citing file); proof-debt.scm does the walking.
(define *rests-on-graph* (make-equal-hash-table))   ; name -> (dep ...)

(define (register-rests-on! name deps)
  (unless (list? deps)
    (display ";; WARNING: rests-on for ") (write name)
    (display " expects a list of theorem names, got ") (write deps) (newline))
  (hash-table-set! *rests-on-graph* name (if (list? deps) deps '()))
  name)

(define (rests-on-of name)
  (hash-table-ref/default *rests-on-graph* name '()))

(define (rests-on-declared-names)
  (hash-table-keys *rests-on-graph*))

;;; rests-on deps that name no installed theorem -- typo guard, since a mistyped
;;; dep would silently be a sink and weaken the cycle check.  Returns a list of
;;; (declaring-name . bad-dep).  Soft-nudged at load-end (all names installed by
;;; then; a forward reference during load is not yet resolvable, so check late).
(define (rests-on-unknown-deps)
  (let ((bad '()))
    (hash-table-walk *rests-on-graph*
      (lambda (name deps)
        (for-each (lambda (d)
                    (unless (hash-table-ref/default *theorem-table* d #f)
                      (set! bad (cons (cons name d) bad))))
                  deps)))
    (reverse bad)))

(define *warrants* (make-equal-hash-table))   ; name -> (kind . text)

(define (register-warrant! name kind text)
  (unless (memq kind *warrant-kinds*)
    (display ";; WARNING: unknown warrant kind ")
    (write kind) (display " for ") (write name)
    (display " -- expected one of ")
    (write *warrant-kinds*) (newline))
  ;; For 'reference, TEXT may be a structured locator (book-key ...): resolve
  ;; it to the human citation stored/rendered as before, and stash any machine
  ;; anchor separately.  A bare string passes through untouched (legacy form),
  ;; so every existing warrant and every renderer is unaffected.
  (let ((text* text) (anchor #f))
    (when (eq? kind 'reference)
      (call-with-values (lambda () (reference-parse text))
        (lambda (human a) (set! text* human) (set! anchor a))))
    (hash-table-set! *warrants* name (cons kind text*))
    (if anchor
        (hash-table-set! *reference-anchors* name anchor)
        (hash-table-delete! *reference-anchors* name))
    ;; Propagate the warrant to the auto-generated -rev companion (same fact,
    ;; flipped), so warranting a forward doesn't leave its reverse unwarranted.
    (let ((rev (rev-name-of name)))
      (when (hash-table-ref/default *theorem-table* rev #f)
        (hash-table-set! *warrants* rev (cons kind text*))
        (when anchor (hash-table-set! *reference-anchors* rev anchor)))))
  name)

(define (warrant-of name)
  (hash-table-ref/default *warrants* name #f))

;;; -----------------------------------------------------------------------
;;; Case-fold shadowing audit.  The reader case-folds symbols, so a binder pair
;;; differing only in case (FORALL N ... FORSOME n) collapses to the SAME name:
;;; the inner binder then shadows the outer, silently changing the formula
;;; (cluster-point, difference-membership).  After the read, that collision is
;;; ALWAYS "a binder whose variable is already in scope" -- so walking every
;;; installed formula with the kernel's full binder vocabulary and flagging any
;;; in-scope rebinding is a COMPLETE check for the class: zero hits => zero
;;; case-fold collisions in the library.  (def-predicate stores params as outer
;;; FORALL binders, so binder-vs-parameter collisions are covered too.)
;;; Authoritative complement to scan-case-fold.py (source-level, parser-limited).
(define (wff-shadowing-binders e)
  (let ((hits '()))
    (define (bind v scope where)
      (when (memq v scope) (set! hits (cons (list where v) hits)))
      (cons v scope))
    (define (walk e scope)
      (cond
        ((functoid? e)
         (let ((scope* (fold-left (lambda (s b) (bind (car b) s 'FUNCTOID))
                                  scope (functoid-bindings e))))
           (for-each (lambda (b) (walk (cdr b) scope)) (functoid-bindings e))
           (walk (functoid-body e) scope*)))
        ((not (pair? e)) #t)
        (else
         (case (car e)
           ((FORALL FORSOME COMP IOTA)            ; (OP var body)
            (walk (caddr e) (bind (cadr e) scope (car e))))
           ((SEP)                                 ; (SEP var dom body)
            (walk (caddr e) scope)
            (walk (cadddr e) (bind (cadr e) scope 'SEP)))
           ((BIG-UNION)                           ; (BIG-UNION var A body)
            (walk (caddr e) scope)
            (walk (cadddr e) (bind (cadr e) scope 'BIG-UNION)))
           ((VNB-LAMBDA)                          ; (VNB-LAMBDA bspec A body)
            (walk (caddr e) scope)
            (walk (cadddr e)
                  (fold-left (lambda (s v) (bind v s 'VNB-LAMBDA))
                             scope (vnb-lambda-bvars (cadr e)))))
           (else (for-each (lambda (c) (walk c scope)) (cdr e)))))))
    (walk e '())
    (reverse hits)))

;;; Every installed formula whose statement has a shadowing binder.  Returns a
;;; list of (name . shadows); empty = the whole library is collision-free.
(define (case-fold-audit)
  (let ((bad '()))
    (for-each (lambda (name)
                (let* ((f  (lookup-theorem name))
                       (sh (and f (wff-shadowing-binders f))))
                  (when (pair? sh) (set! bad (cons (cons name sh) bad)))))
              (hash-table-keys *theorem-table*))
    (reverse bad)))

;;; -----------------------------------------------------------------------
;;; ACCESSOR-NAMED-BINDER audit.  The constant-head registry is consulted ONLY
;;; in head position and is SCOPE-BLIND: a bound variable whose (case-folded)
;;; name is a registered constant -- an accessor, operator, functoid, predicate
;;; or defined fn -- reads as that constant the instant it appears applied,
;;; (v x) silently becoming the CONSTANT v, not the bound v.  The quantifier
;;; then binds a variable the body never mentions: the formula means something
;;; other than what was written, with no error.  This walker flags every binder
;;; whose variable is a registered constant; constant-binder-audit sweeps the
;;; whole installed library (empty => clean).  Companion to wff-shadowing-binders
;;; (binder-over-binder); together they close the case-fold collision class.
(define (wff-constant-binders e0)
  ;; Coerce: handed a wff RECORD, the walk below (which descends pairs) would
  ;; find no binders and report CLEAN -- a silent false negative in the very
  ;; gate that exists to catch silent hazards.  Take the formula out first.
  (let ((e (if (wff? e0) (wff-formula e0) e0))
        (hits '()))
    (define (chk v where)
      (let ((k (constant-head? v)))
        (when k (set! hits (cons (list where v k) hits)))))
    (define (walk e)
      (cond
        ((functoid? e)
         (for-each (lambda (b) (chk (car b) 'FUNCTOID) (walk (cdr b)))
                   (functoid-bindings e))
         (walk (functoid-body e)))
        ((not (pair? e)) #t)
        (else
         (case (car e)
           ((FORALL FORSOME COMP IOTA) (chk (cadr e) (car e)) (walk (caddr e)))
           ((SEP)       (walk (caddr e)) (chk (cadr e) 'SEP) (walk (cadddr e)))
           ((BIG-UNION) (walk (caddr e)) (chk (cadr e) 'BIG-UNION) (walk (cadddr e)))
           ((VNB-LAMBDA)
            (walk (caddr e))                     ; the domain, outside the binder
            (for-each (lambda (v) (chk v 'VNB-LAMBDA)) (vnb-lambda-bvars (cadr e)))
            (walk (cadddr e)))
           (else (for-each walk (cdr e)))))))
    (walk e)
    (reverse hits)))

(define (constant-binder-audit)
  (let ((bad '()))
    (for-each (lambda (name)
                (let* ((f  (lookup-theorem name))
                       (sh (and f (wff-constant-binders f))))
                  (when (pair? sh) (set! bad (cons (cons name sh) bad)))))
              (hash-table-keys *theorem-table*))
    (reverse bad)))

;;; -----------------------------------------------------------------------
;;; FUNCTOID-BODY binder audit.  case-fold-audit and constant-binder-audit walk
;;; *theorem-table* only.  A def-functoid's body lives in *functoid-registry*
;;; and is NEVER checked -- so a lambda/SEP binder INSIDE the body that
;;; case-folds onto a PARAMETER captures it silently: MONALG-MUL '(A M f g) with
;;; body binder `m' made (OPR M) read as OPR-of-the-summation-point (m===M under
;;; the reader's fold), and the wrong term shipped with a completely clean load
;;; (2026-07-25).  A functoid's parameters scope over its body exactly like outer
;;; FORALL binders, so wrapping the body in a FORALL per parameter turns the
;;; param-vs-body-binder collision into an ordinary in-scope rebinding that
;;; wff-shadowing-binders already detects -- and catches body-binder-over-body-
;;; binder collisions for free.  Returns (name . shadows) per offending functoid;
;;; empty => every functoid body is collision-free.
(define (functoid-binder-audit)
  (let ((bad '()))
    (for-each
     (lambda (name)
       (let ((reg (hash-table-ref/default *functoid-registry* name #f)))
         (when reg
           (let* ((pvars   (car reg))
                  (body    (cadr reg))
                  ;; params as nested outer FORALLs over the body
                  (wrapped (fold-right (lambda (p b) (list 'FORALL p b)) body pvars))
                  (sh      (wff-shadowing-binders wrapped)))
             (when (pair? sh) (set! bad (cons (cons name sh) bad)))))))
     (hash-table-keys *functoid-registry*))
    (reverse bad)))

;;; LOUD, deliberately unpleasant report.  A binder that collides with a
;;; registered constant is a silent soundness hazard; make it impossible to
;;; ignore and unpleasant enough that nobody does it twice.
(define (bang-line) (display "!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!\n"))
(define (shout-constant-binders! bad)
  (newline) (bang-line) (bang-line)
  (display "!!!!!                                                                  !!!!!\n")
  (display "!!!!!     STOP.  A BOUND VARIABLE IS NAMED LIKE A REGISTERED CONSTANT.  !!!!!\n")
  (display "!!!!!     THIS IS A SILENT SOUNDNESS HAZARD.  DO NOT DO THIS.           !!!!!\n")
  (display "!!!!!                                                                  !!!!!\n")
  (display "!!!!!     The head registry is SCOPE-BLIND: wherever your bound var     !!!!!\n")
  (display "!!!!!     appears APPLIED, (v ...) reads as the CONSTANT v, not your    !!!!!\n")
  (display "!!!!!     variable.  Your quantifier then binds a name the body never   !!!!!\n")
  (display "!!!!!     uses.  The formula MEANS SOMETHING ELSE -- with no error.     !!!!!\n")
  (display "!!!!!                                                                  !!!!!\n")
  (display "!!!!!     FIX: RENAME THE BOUND VARIABLE.  (Trailing underscore, or a   !!!!!\n")
  (display "!!!!!     name that is not an accessor/operator/functoid/predicate.)    !!!!!\n")
  (display "!!!!!                                                                  !!!!!\n")
  (bang-line)
  (display "!!!!!     OFFENDERS:                                                    !!!!!\n")
  (for-each
   (lambda (entry)
     (let ((name (car entry)))
       (for-each
        (lambda (hit)
          (display "!!!!!  in `") (display name) (display "' : the ")
          (display (car hit)) (display " binder `") (display (cadr hit))
          (display "' shadows a registered ") (display (caddr hit)) (display ".\n"))
        (cdr entry))))
   bad)
  (bang-line) (bang-line) (newline))

;;; Per-wff loud warning, fired at construction time (make-wff) when the user
;;; builds a formula whose binder is named like a registered constant -- the
;;; interactive counterpart of the load-time constant-binder-audit gate.  `hits'
;;; is the (where var kind) list from wff-constant-binders; non-fatal (returns),
;;; but impossible to miss.
(define (warn-constant-binders! hits)
  (newline) (bang-line)
  (display "!!!!!  RESERVED NAME: a bound variable is named like a registered constant.\n")
  (for-each
   (lambda (hit)
     (display "!!!!!    the ") (display (car hit)) (display " binder `") (display (cadr hit))
     (display "' shadows a registered ") (display (caddr hit)) (display ".\n"))
   hits)
  (display "!!!!!  In head position (") (display (cadr (car hits)))
  (display " ...) reads as the CONSTANT, not your bound variable -- scope-blind.\n")
  (display "!!!!!  RENAME IT (trailing underscore, or a non-accessor/operator/functoid name).\n")
  (bang-line) (newline))

;;; -----------------------------------------------------------------------
;;; Classic-name discovery.  Theorems carry terse internal names (rolle, mvt,
;;; extreme-value-max); humans look them up by their textbook names ("Rolle's
;;; theorem", "intermediate value theorem").  (alias! 'name "Classic Name" ...)
;;; records the human names; (find-theorem "rolle") searches the internal name,
;;; the warrant prose, AND the aliases, case-insensitively, and prints matches.
(define *theorem-aliases* (make-equal-hash-table))   ; name -> list of name strings
(define (alias! name . strs)
  (hash-table-set! *theorem-aliases* name
                   (append (hash-table-ref/default *theorem-aliases* name '()) strs)))
(define (aliases-of name) (hash-table-ref/default *theorem-aliases* name '()))

(define (find-theorem pattern)
  ;; Accept a SYMBOL too -- every other proof-surface command takes a quoted
  ;; symbol ((mac 'poly), (fact 'thm)), so (find-theorem 'foo) is the natural
  ;; call; string-downcase on a symbol used to type-crash the REPL rudely.
  (let* ((pattern (if (symbol? pattern) (symbol->string pattern) pattern))
         (pat   (string-downcase pattern))
         (names (sort (hash-table-keys *theorem-table*)
                      (lambda (a b) (string<? (symbol->string a) (symbol->string b)))))
         (hit?  (lambda (n)
                  (let ((nm (string-downcase (symbol->string n)))
                        (w  (warrant-of n)))
                    (or (substring? pat nm)
                        (and w (substring? pat (string-downcase (cdr w))))
                        ;; find-first, not any-pred: any-pred is defined in
                        ;; driver-kit.scm, 110 files later.
                        (find-first (lambda (s) (substring? pat (string-downcase s)))
                                    (aliases-of n))))))
         ;; one record per hit: an alist carrying EVERYTHING printed, so a
         ;; caller can consume the result, not just read the side-effect.
         (records (map (lambda (n)
                         (list (cons 'name      n)
                               (cons 'aliases   (aliases-of n))
                               (cons 'warrant   (warrant-of n))      ; (kind . text) or #f
                               (cons 'statement (lookup-theorem n))))
                       (filter hit? names))))
    (if (null? records)
        (begin (display ";; find-theorem: no match for \"") (display pattern) (display "\"")
               (newline))
        (for-each
         (lambda (r)
           (let ((n (cdr (assq 'name r))) (al (cdr (assq 'aliases r))) (w (cdr (assq 'warrant r))))
             (display ";; ") (display n)
             (when (pair? al) (display "  (") (display (car al)) (display ")"))
             (when w (display "  [") (display (car w)) (display "]"))
             (newline)
             (display ";;     ") (display (expression->string (cdr (assq 'statement r)))) (newline)))
         records))
    records))

;;; -----------------------------------------------------------------------
;;; Glosses: a plain-English rendition of a support's STATEMENT (what the
;;; formula says, in words), distinct from its WARRANT (why we accept it).
;;; Only the deeply-nested multi-line supports carry one -- the short ones
;;; read fine as formulas.  Metadata for review/PSS.md, like warrants.
(define *glosses* (make-equal-hash-table))   ; name -> text

(define (register-gloss! name text)
  (hash-table-set! *glosses* name text)
  ;; Propagate to the -rev companion (same statement, flipped) so a glossed
  ;; forward does not leave its reverse bare -- mirrors register-warrant!.
  (let ((rev (rev-name-of name)))
    (when (hash-table-ref/default *theorem-table* rev #f)
      (hash-table-set! *glosses* rev text)))
  name)

(define (gloss-of name)
  (hash-table-ref/default *glosses* name #f))

;;; DISCIPLINE (soft, going forward): a reference-warranted entry SHOULD carry
;;; a gloss! -- the plain-English statement is what makes the base searchable
;;; by content rather than by symbol soup.  Returns the reference-warranted
;;; names with no gloss, sorted.  Soft-nudged (count only) in load.scm; never a
;;; gate.  The 158 legacy computational lemmas are grandfathered, not migrated.
(define (reference-warrants-without-gloss)
  (let ((bad '()))
    (hash-table-walk *warrants*
      (lambda (name w)
        (when (and (eq? (car w) 'reference) (not (gloss-of name)))
          (set! bad (cons name bad)))))
    ;; Drop auto-installed -rev companions: they inherit the forward's warrant
    ;; and gloss and are not independent entries (collapse-rev-names loads later,
    ;; in interactive.scm, but this runs at load-end when it is present).
    (sort (collapse-rev-names bad)
          (lambda (a b) (string<? (symbol->string a) (symbol->string b))))))

;;; -----------------------------------------------------------------------
;;; UNVERIFIED `proof' WARRANTS.
;;;
;;; The kind `proof' asserts that "a machine-checked VNB proof exists" (see
;;; *warrant-kinds* above).  On a fact whose provenance is `proven' that is
;;; redundant but true.  On an ASSERTED fact it is a claim about something
;;; outside the loaded library, and nothing checks it.
;;;
;;; `warrant-invariant' (load.scm) asks this question already but excludes
;;; *support-theorem-names*, i.e. the PSS -- and the PSS is where every such
;;; entry actually lives.  This is the complement, so between them the two
;;; cover the warrant table.
;;;
;;; Two returns, because the two populations are not equally bad:
;;;   named   -- the text names a .scm file, so the claim is at least AUDITABLE:
;;;              load that file and see whether it still reaches its qed.
;;;   unnamed -- the text is the derivation written out in prose.  There is no
;;;              file to check, so `proof' here means "somebody believed this
;;;              would go through", which is what `informal' is for.
;;;
;;; Measured 2026-08-02: 49 entries, 5 named / 44 unnamed; of the 5 named, two
;;; (continuous-implies-open-preimage, gauge-is-degree) no longer reached their
;;; qed -- both drivers still search for the pre-rename accessors `x(s)'/`a(s)'.
;;; Soft-nudged (count only) in load.scm; never a gate.
(define (proof-warrants-unproven)
  (define (names-a-file? text)
    (and (string? text)
         (or (string-search-forward ".scm" text 0)
             (string-search-forward "theorem-library" text 0)
             (string-search-forward "calculus/" text 0))))
  (let ((named '()) (unnamed '()))
    (hash-table-walk *warrants*
      (lambda (name w)
        (when (and (eq? (car w) 'proof)
                   (not (eq? (provenance-of name) 'proven)))
          (if (names-a-file? (cdr w))
              (set! named (cons name named))
              (set! unnamed (cons name unnamed))))))
    (let ((srt (lambda (l)
                 (sort (collapse-rev-names l)
                       (lambda (a b) (string<? (symbol->string a)
                                               (symbol->string b)))))))
      (list (srt named) (srt unnamed)))))

;;; -----------------------------------------------------------------------
;;; Categories: which KIND of PSS fact this is -- and, as an intake
;;; discipline, WHY it is asserted rather than proven (see each title's
;;; "why not grind" rationale in PSS.md).  Orthogonal to warrant (why we
;;; accept it) and gloss (what it says).  The canonical ordered list drives
;;; both the category! validity check and the section order in write-pss-md.
(define *pss-category-order*
  '((plumbing      . "Plumbing & typing")
    (inequalities  . "Inequalities & order")
    (combinatorial . "Combinatorial constructions")
    (analysis      . "Real analysis: limits, series, completeness")
    (algebra       . "Algebraic & ring-structure facts")
    (topology      . "Metric topology & continuity")
    (constructions . "Metric-space constructions")
    (set-quotient  . "Set & quotient constructions")))

(define (pss-category-title cat)
  (cond ((assq cat *pss-category-order*) => cdr) (else #f)))

(define *pss-categories* (make-equal-hash-table))   ; name -> category symbol

(define (register-category! name cat)
  (if (not (pss-category-title cat))
      (begin
        (display ";; WARNING: unknown PSS category ") (write cat)
        (display " for ") (write name) (display " -- expected one of ")
        (write (map car *pss-category-order*)) (newline))
      (begin
        (hash-table-set! *pss-categories* name cat)
        ;; Propagate to the -rev companion, like warrants/glosses.
        (let ((rev (rev-name-of name)))
          (when (hash-table-ref/default *theorem-table* rev #f)
            (hash-table-set! *pss-categories* rev cat)))))
  name)

(define (category-of name)
  (hash-table-ref/default *pss-categories* name #f))

;;; Soft-nudge support: the PSS support names (collapsed of -rev) with no
;;; category yet.  load.scm reports the count; categorisation is a discipline,
;;; not a soundness gate, so this never fails the build.
(define (uncategorized-pss-names)
  (filter (lambda (n) (not (category-of n)))
          (collapse-rev-names
           (filter (lambda (n) (memq n *support-theorem-names*))
                   (hash-table-keys *theorem-table*)))))

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
  ;; Propagate to the auto-generated -rev companion -- the SAME FACT flipped,
  ;; installed by install-theorem! rather than written by an author, so it has
  ;; no provenance of its own to defend.  This mirrors register-warrant!, which
  ;; has propagated for exactly this reason.
  ;;
  ;; Without it, a RE-STAMP BY NAME silently moves only the forward direction.
  ;; install-theorem! stamps both from *current-provenance* at install time, so
  ;; a file that installs its facts and re-stamps them afterwards -- ring.scm
  ;; does precisely that for the eleven IS-RING projections (ring.scm:139) --
  ;; left nine companions behind: ring-mul-assoc `definitional', and
  ;; ring-mul-assoc-rev `asserted' with no warrant, i.e. trust: none.  A proof
  ;; that happened to rewrite right-to-left then paid debt the left-to-right
  ;; direction did not, for the same fact.
  (let ((rev (rev-name-of name)))
    (when (hash-table-ref/default *theorem-table* rev #f)
      (hash-table-set! *provenance* rev kind)))
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

;;; -----------------------------------------------------------------------
;;; THE INSTALL-TIME GRADING GATE  (2026-08-04)
;;;
;;; `support' and `theory-add-axiom!' install a raw S-expression: they never run
;;; it past `make-wff', which is the only thing in the tree that grades a formula.
;;; That door produced the flat-conjunction defect (2026-07-28) -- a `(AND a b c)'
;;; the kernel reads with binary-left/right, silently DROPPING the third conjunct,
;;; so the installed fact did not say what it appeared to say -- and it is the
;;; same door behind the free-variable and unregistered-head defects.  Rather
;;; than a fourth after-the-fact audit, grade every formula AS IT IS INSTALLED.
;;;
;;; WARN-ONLY, and it records: a failure names a fact that is already in the
;;; library, so raising here would strand every later file.  `connective-arity-audit'
;;; (load.scm) remains the fatal gate for the one defect known to be always wrong.
;;;
;;; WHAT IT DOES NOT CATCH, so nobody reads more into a clean line than it says:
;;; `validate-wff!' grades SHAPE -- arity, and wff-vs-term position.  A free
;;; variable is well-formed (that is `free-variable-audit'), and so is an applied
;;; head nobody registered (that is `head-registry-sweep').  Three gates, three
;;; defects, one door.
;;;
;;; The four variadic macete schemas (union-decompose, intersection-decompose and
;;; their -rev) are exempt BY SHAPE, not by name: `(UNION (RESTVAR AS))' and
;;; `(SPLICE OR e AS ...)' are the engine's variadic syntax (macetes.scm:42), not
;;; first-order wffs, and make-wff rightly refuses them.
(define *install-validation-failures* '())   ; ((name message file) ...)

(define (install--variadic-schema? e)
  (cond ((pair? e) (or (memq (car e) '(RESTVAR SPLICE))
                       (any install--variadic-schema? e)))
        (else #f)))

(define (install--grade! name formula)
  (unless (install--variadic-schema? formula)
    (let ((why (call-with-current-continuation
                 (lambda (k)
                   (bind-condition-handler (list condition-type:error)
                     (lambda (c) (k (condition/report-string c)))
                     (lambda () (validate-wff! formula) #f))))))
      (when why
        (set! *install-validation-failures*
              (cons (list name why (safe-load-pathname))
                    *install-validation-failures*))
        (display ";VNB warning: install-theorem! -- ") (display name)
        (display " does not pass make-wff's grading:\n;              ")
        (display why) (newline)))))

;;; ((name message file) ...), install order.  Empty is the good case.
(define (install-validation-failures)
  (reverse *install-validation-failures*))

(define (install-theorem! name formula-or-wff)
  (vnb-guard
    (lambda ()
      (let ((formula (if (wff? formula-or-wff)
                         (wff-formula formula-or-wff)
                         formula-or-wff)))
        (install--grade! name formula)
        (hash-table-set! *theorem-table* name formula)
        (hash-table-delete! *lemma-fingerprint-memo* name)   ; stale on reinstall
        (let ((src (safe-load-pathname)))   ; #f at the REPL; qed installs interactively
          (when src (hash-table-set! *theorem-source* name src)))
        (register-provenance! name *current-provenance*)
        (install-macete! name (theorem->elementary-macete formula name))
        ;; Symmetric-core theorems also install a reverse-direction macete.
        (let ((flipped (flip-symmetric-core-in-formula formula)))
          (when flipped
            (let ((rev-name (string->symbol
                             (string-append (symbol->string name) "-rev"))))
              (hash-table-set! *theorem-table* rev-name flipped)
              (hash-table-delete! *lemma-fingerprint-memo* rev-name)
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
