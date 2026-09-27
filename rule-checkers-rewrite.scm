;;; rule-checkers-rewrite.scm -- checkers for the four `rewrite' kernel operations
;;;
;;;     macete                     rewrite the GOAL by an installed macete
;;;     macete-hyp                 rewrite an ASSUMPTION by one
;;;     cartesian-decompose        (IN x (CARTESIAN A_1..A_n)) -> its existential chain
;;;     tuple-equality-decompose   (= (LIST a_i) (LIST b_i)) -> the conjunction of components
;;;
;;; A checker VERIFIES a finished inference.  It is handed the rule tag, the
;;; hypothesis sequents in the order they were handed over, and the conclusion
;;; sequent, and answers #t (accept) or a STRING saying why it refuses.  It does
;;; not rebuild the inference: it states the rule as a relation between the
;;; conclusion and the hypotheses and tests that relation.  Nothing here calls
;;; `rewrite-expr', `rewrite-by-proc', `match-expr', `apply-subst',
;;; `condition-holds?', `lc-extend', `lc-drop-shadowed' or any macete closure;
;;; the matching, the substitution, the local context and the condition test are
;;; written again from the rule.
;;;
;;; WHAT IS TAKEN FROM THE BUILDER, DELIBERATELY.  `extract-rewrite-patterns'
;;; (with `strip-foralls' and `prenex-positive', which are one reading with it)
;;; is what DEFINES the rewrite rule a theorem denotes: how a statement is read
;;; as (conditions, L, R) is not a fact about the inference but the meaning of
;;; the word "macete", so the checker reads it the same way rather than
;;; inventing a second reading.  `arith-eval-formula' is used for the ground
;;; arithmetic side of a condition; it is a trusted oracle in its own right
;;; (batch 10-D's territory), not a re-implementation of anything here.
;;;
;;; ASSUMPTION LISTS ARE COMPARED AS SETS UP TO ALPHA-EQUIVALENCE.  The order of
;;; a sequent's hypotheses carries no meaning at this level, and a duplicate
;;; cannot arise (`context-add-assumption' declines one), so "the same
;;; assumptions" means: every formula on each side is alpha-equivalent to one on
;;; the other.
;;;
;;; THE RULE TAGS.  Since 2026-09-20 (batch 10-C) the two macete tags carry the
;;; NAME of the macete that fired:
;;;     (macete     NAME SOURCE REPLACEMENT)
;;;     (macete-hyp NAME SOURCE REPLACEMENT)
;;; Without the name a checker has nothing to check against: L -> R alone is an
;;; instance of nothing in particular.  SOURCE and REPLACEMENT are kept (the
;;; proof-rules certificate prints them) and are CROSS-CHECKED here against the
;;; patterns NAME really denotes, so the tag cannot disagree with the library.
;;;
;;; WHAT NAME MEANS.  Four kinds of macete reach `dg-apply-rule!', and the
;;; licence of each is read from the place that defines it:
;;;   * a THEOREM's macete (install-theorem!) -- the installed statement, read
;;;     by extract-rewrite-patterns.  This covers the instance-value macetes
;;;     (ZZ-RING@MUL and friends), which declare-instance! installs as theorems.
;;;   * an ACCESSOR's macete (install-accessor-macete!) -- *accessor-index*
;;;     says the slot, and the rule is (ACC s) -> (NTH k s).
;;;   * a FUNCTOID's unfold (def-functoid) -- *functoid-registry* holds the
;;;     parameters and the body, and the rule is (F p1..pn) -> body.
;;;   * a FUNCTOR PROJECTION `F@ACC' (install-functor-projections!) -- F's
;;;     functoid body is a literal LIST and ACC's slot index picks the component.
;;; Those three registries live in structures.scm, which loads AFTER this file;
;;; the references are resolved at call time, and nothing calls a checker before
;;; the first proof.  A macete built outside install-macete! records the name
;;; `<anonymous>' and is refused (only the S-10 fixture in test-suite.scm builds
;;; one, and it is inert: it never reaches dg-apply-rule!).
;;;
;;; THE LOCAL CONTEXT is recomputed here from the conclusion's assumptions and
;;; the path to the rewritten position, by the rules Monk (1988) states:
;;;   * entering the right conjunct of (AND A B) one may assume A, and entering
;;;     the left one may assume B;
;;;   * entering the consequent of (IMPLIES A B) one may assume A;
;;;   * entering either disjunct of (OR A B) one may assume the negation of the
;;;     other;
;;;   * entering the scope of a binder, every assumption mentioning the bound
;;;     variable FREE must be dropped: under the binder that name denotes
;;;     something else.
;;; Conjunctions are flattened so that each conjunct can discharge a condition
;;; on its own.  The last clause is the soundness-bearing one, and it is applied
;;; here to EVERY binder the expression layer has -- FORALL, FORSOME, IOTA,
;;; COMP, SEP's body, BIG-UNION's body, VNB-LAMBDA's body and a functoid
;;; record's body -- independently of which of them the rewriter happens to
;;; know about.
;;;
;;; NOT CHECKED HERE, and said so on purpose: that the rewrite is the one the
;;; engine WOULD have made.  A checker's business is that the step is licensed,
;;; not that it is the step some procedure computes.  Where the local-context
;;; rules above are more generous than the rewriter's (the left conjunct of an
;;; AND, the left disjunct of an OR), the extra generosity is sound and only
;;; means the checker declines to refuse a step the engine will not take.

;;; -----------------------------------------------------------------------
;;; Sequent access, and assumption sets up to alpha

;;; A hypothesis is handed over as a raw <sequent>; the conclusion may arrive as
;;; a <sequent> or as the graph's <sequent-node>.  Both are read here.
(define (rkw--asms s)
  (cond ((sequent? s) (sequent-assumptions s))
        (else (sequent-node-assumptions s))))

(define (rkw--goal s)
  (cond ((sequent? s) (sequent-assertion s))
        (else (sequent-node-assertion s))))

(define (rkw--asm-formulas s) (map wff-formula (rkw--asms s)))

(define (rkw--goal-formula s) (wff-formula (rkw--goal s)))

(define (rkw--in-set? f fs)
  (let loop ((fs fs))
    (cond ((null? fs) #f)
          ((alpha-equiv? f (car fs)) #t)
          (else (loop (cdr fs))))))

;;; The formulas of FS1 that no formula of FS2 is alpha-equivalent to.
(define (rkw--set-minus fs1 fs2)
  (filter (lambda (f) (not (rkw--in-set? f fs2))) fs1))

(define (rkw--same-assumptions? fs1 fs2)
  (and (null? (rkw--set-minus fs1 fs2))
       (null? (rkw--set-minus fs2 fs1))))

;;; -----------------------------------------------------------------------
;;; One-way matching of a macete pattern against an expression
;;;
;;; A SUBSTITUTION is an alist.  An ordinary entry is (var . expr).  A VARIADIC
;;; entry, from a pattern ending in (RESTVAR v), is (var RKW-REST e1 ... en):
;;; v stands for the tail of an argument list.
;;;
;;; The matcher is a SEARCH.  Nothing is believed on its word: every use below
;;; instantiates the pattern with the substitution it returns and demands the
;;; result be alpha-equivalent to the expression it claimed to match.  A bug in
;;; the matcher can therefore only cost a refusal, never an acceptance.

(define (rkw--rest? v) (and (pair? v) (eq? (car v) 'RKW-REST)))
(define (rkw--rest-exprs v) (cdr v))

(define (rkw--restvar? p svars)
  (and (pair? p) (eq? (car p) 'RESTVAR)
       (pair? (cdr p)) (null? (cddr p))
       (symbol? (cadr p))
       (memq (cadr p) svars)))

(define (rkw--value-equal? v1 v2)
  (cond ((and (rkw--rest? v1) (rkw--rest? v2))
         (let loop ((xs (rkw--rest-exprs v1)) (ys (rkw--rest-exprs v2)))
           (cond ((and (null? xs) (null? ys)) #t)
                 ((or (null? xs) (null? ys)) #f)
                 ((alpha-equiv? (car xs) (car ys)) (loop (cdr xs) (cdr ys)))
                 (else #f))))
        ((or (rkw--rest? v1) (rkw--rest? v2)) #f)
        (else (alpha-equiv? v1 v2))))

(define (rkw--merge s1 s2)
  (let loop ((s2 s2) (acc s1))
    (cond ((null? s2) acc)
          (else
           (let* ((b (car s2))
                  (old (assq (car b) acc)))
             (cond ((not old) (loop (cdr s2) (cons b acc)))
                   ((rkw--value-equal? (cdr old) (cdr b)) (loop (cdr s2) acc))
                   (else #f)))))))

(define (rkw--match-args ps es svars acc)
  (cond
    ((and (pair? ps) (null? (cdr ps)) (rkw--restvar? (car ps) svars))
     (rkw--merge acc (list (cons (cadr (car ps)) (cons 'RKW-REST es)))))
    ((and (null? ps) (null? es)) acc)
    ((or (null? ps) (null? es)) #f)
    (else
     (let ((m (rkw--match (car ps) (car es) svars)))
       (and m
            (let ((merged (rkw--merge acc m)))
              (and merged (rkw--match-args (cdr ps) (cdr es) svars merged))))))))

(define (rkw--match pat expr svars)
  (cond
    ((and (symbol? pat) (memq pat svars)) (list (cons pat expr)))
    ((symbol? pat) (and (eq? pat expr) '()))
    ((number? pat) (and (eqv? pat expr) '()))
    ;; THE NUMERAL <-> SUCCESSOR BRIDGE (see the section of that name below for
    ;; the fact that licenses it): a pattern (succ P) matches a positive exact
    ;; integer literal m by matching P against m-1.  Only `succ', never
    ;; `succ_ORD'; never 0, never a negative, never an inexact or non-integer
    ;; literal; and only under the head `succ' -- any other head meets a
    ;; literal as an ordinary non-match.
    ((and (pair? pat) (eq? (car pat) 'succ)
          (pair? (cdr pat)) (null? (cddr pat))
          (exact-integer? expr) (positive? expr))
     (rkw--match (cadr pat) (- expr 1) svars))
    ((and (functoid? pat) (functoid? expr))
     (let ((bp (functoid-bindings pat)) (be (functoid-bindings expr)))
       (and (eq? (functoid-kind pat) (functoid-kind expr))
            (= (length bp) (length be))
            (let loop ((bps bp) (bes be) (acc '()))
              (cond
                ((null? bps)
                 (let ((bm (rkw--match (functoid-body pat) (functoid-body expr) svars)))
                   (and bm (rkw--merge acc bm))))
                ((not (eq? (caar bps) (caar bes))) #f)
                (else
                 (let ((dm (rkw--match (cdar bps) (cdar bes) svars)))
                   (and dm
                        (let ((merged (rkw--merge acc dm)))
                          (and merged (loop (cdr bps) (cdr bes) merged)))))))))))
    ((or (functoid? pat) (functoid? expr)) #f)
    ((and (pair? pat) (pair? expr) (list? pat) (list? expr))
     (cond
       ;; single-variable binders: alpha-aware
       ((and (memq (car pat) '(FORALL FORSOME IOTA COMP))
             (eq? (car pat) (car expr))
             (= 3 (length pat)) (= 3 (length expr)))
        (let ((pv (cadr pat)) (ev (cadr expr)))
          (cond
            ((eq? pv ev) (rkw--match (caddr pat) (caddr expr) svars))
            ((memq pv svars) #f)               ; a schema var in binder position
            (else
             ;; An UNINTERNED symbol, not `fresh-var': fresh-var bumps
             ;; *fresh-counter*, and a checker must leave no trace on the state a
             ;; proof's eigenvariable names and its printed page depend on.
             (let ((z (generate-uninterned-symbol pv)))
               (rkw--match (subst-free pv z (caddr pat))
                           (subst-free ev z (caddr expr))
                           svars))))))
       ;; The domain-carrying binders (SEP, BIG-UNION, VNB-LAMBDA).  Their
       ;; binder position is matched by the arm below, positionally -- which for
       ;; a plain symbol IS equality, and is what the kernel's matcher does.
       ;; What must never happen is a SCHEMA VARIABLE there: it would bind to the
       ;; expression's BOUND variable, and the replacement would carry it out of
       ;; its scope.  The kernel's `match-expr' refuses that since 2026-09-20
       ;; (batch 11-C); this refuses it too, so the checker cannot bless it.
       ((and (memq (car pat) '(SEP BIG-UNION VNB-LAMBDA))
             (eq? (car pat) (car expr))
             (= 4 (length pat)) (= 4 (length expr))
             (chk-any (lambda (v) (memq v svars))
                      (if (symbol? (cadr pat)) (list (cadr pat)) (cdr (cadr pat)))))
        #f)
       ((and (symbol? (car pat)) (eq? (car pat) (car expr)))
        (rkw--match-args (cdr pat) (cdr expr) svars '()))
       ((and (pair? (car pat)) (pair? (car expr)))
        (let ((hm (rkw--match (car pat) (car expr) svars)))
          (and hm (rkw--match-args (cdr pat) (cdr expr) svars hm))))
       (else #f)))
    (else #f)))

;; The checker's own matcher: its binder vocabulary, declared for
;; binder-walker-audit (expressions.scm: declare-binder-walker!).
(declare-binder-walker! 'rkw--match
                        '(FORALL FORSOME IOTA COMP SEP BIG-UNION VNB-LAMBDA))

;;; -----------------------------------------------------------------------
;;; Instantiating a pattern
;;;
;;; Ordinary bindings are applied SIMULTANEOUSLY (subst-free*, the capture-
;;; avoiding multi-binding substitution of expressions.scm).  A variadic
;;; binding is consumed in two places: a (RESTVAR v) tail in a SOURCE pattern
;;; splices the bound list into the argument list, and a
;;; (SPLICE binop elt-var rest-var template) in a REPLACEMENT right-folds binop
;;; over the template instantiated at each bound expression.

(define (rkw--expand-restvars e rest)
  (cond
    ((functoid? e)
     (make-functoid (functoid-kind e)
                    (map (lambda (b) (cons (car b) (rkw--expand-restvars (cdr b) rest)))
                         (functoid-bindings e))
                    (rkw--expand-restvars (functoid-body e) rest)))
    ((not (list? e)) e)
    ((null? e) e)
    (else
     (let loop ((xs e) (acc '()))
       (cond
         ((null? xs) (reverse acc))
         ((and (null? (cdr xs)) (pair? (car xs)) (eq? (caar xs) 'RESTVAR)
               (pair? (cdar xs)) (assq (cadr (car xs)) rest))
          => (lambda (b)
               (append (reverse acc) (rkw--rest-exprs (cdr b)))))
         (else (loop (cdr xs) (cons (rkw--expand-restvars (car xs) rest) acc))))))))

(define (rkw--expand-splices e rest)
  (cond
    ((functoid? e)
     (make-functoid (functoid-kind e)
                    (map (lambda (b) (cons (car b) (rkw--expand-splices (cdr b) rest)))
                         (functoid-bindings e))
                    (rkw--expand-splices (functoid-body e) rest)))
    ((not (pair? e)) e)
    ((eq? (car e) 'SPLICE)
     (let* ((binop    (cadr e))
            (elt-var  (caddr e))
            (rest-var (cadddr e))
            (template (car (cddddr e)))
            (b        (assq rest-var rest)))
       (if (not b)
           e                                   ; unbound: leave it, the check fails
           (let ((items (rkw--rest-exprs (cdr b))))
             (if (null? items)
                 e
                 (let inner ((xs items))
                   (let ((head (rkw--expand-splices
                                (subst-free elt-var (car xs) template) rest)))
                     (if (null? (cdr xs))
                         head
                         (list binop head (inner (cdr xs)))))))))))
    (else (map (lambda (x) (rkw--expand-splices x rest)) e))))

(define (rkw--inst sub e)
  (let ((ord  (filter (lambda (b) (not (rkw--rest? (cdr b)))) sub))
        (rest (filter (lambda (b) (rkw--rest? (cdr b))) sub)))
    (let* ((e1 (if (null? rest) e (rkw--expand-restvars e rest)))
           (e2 (subst-free* ord e1)))
      (if (null? rest) e2 (rkw--expand-splices e2 rest)))))

;;; -----------------------------------------------------------------------
;;; THE NUMERAL <-> SUCCESSOR BRIDGE, and what licenses it
;;;
;;; A numeral and a successor tower are the SAME TERM of this theory: for a
;;; natural number n, `succ n = n + 1'.  The fact is `nn-succ-plus-one'
;;; (proven, theorem-library/nn-parity-proof.scm:181, from the definitional
;;; `nn-add-succ' and `nn-add-zero'), and the trusted `arith' oracle already
;;; identifies the two -- `arith-eval-term' (arith-eval.scm:87) evaluates
;;; `(succ k)' on a ground natural to k+1.  Applied from `succ 0 = 0 + 1 = 1'
;;; upwards it gives, for every literal m > 0, `succ (m-1) = m'.
;;;
;;; So it is part of what a macete INSTANCE means here, not a convenience: the
;;; rewriter's matcher (match-expr, macetes.scm:108) lets a pattern `(succ P)'
;;; match a positive integer literal m by matching P against m-1, which is how
;;; `nth-deriv-succ', `mpow-succ' and `power-succ' fire on 1, 2, 3 at all.  The
;;; checker therefore does two things with the same fact:
;;;   * its matcher has the bridge (one clause, below), and
;;;   * its INSTANCE TEST compares modulo the bridge -- `sigma L' comes back
;;;     reading `(nth-deriv f (succ 0))' where the goal reads `(nth-deriv f 1)',
;;;     and those are one term.  Without the second half the first is useless:
;;;     the match succeeds and the re-verification then rejects it.  (That was
;;;     the refusal of `nth-deriv-one' in the first switch-ON cold load.)
;;;
;;; TWO COLLAPSES, deliberately different:
;;;   rkw--succ-collapse     folds `succ' only.  Used for the instance test,
;;;                          because `succ' alone is what the rewriter's matcher
;;;                          bridges; `succ_ORD' is deliberately NOT bridged
;;;                          there, and the checker does not widen the kernel.
;;;   rkw--numeral-collapse  folds `succ' AND `succ_ORD'.  Used for the
;;;                          condition test, because that is exactly what
;;;                          `condition-holds?' (macetes.scm:392) does.
;;; Both are STRICTER than `match-expr' in one way, on purpose: they require an
;;; EXACT integer.  Numerals in this library are exact rationals, `succ' off NN
;;; is uninterpreted, and an inexact `1.' is not a numeral of this theory; if
;;; that ever costs a refusal it is a finding, not a silent pass.

;;; Fold (succ k) on an exact non-negative literal k to k+1, bottom up.
(define (rkw--succ-collapse e)
  (cond
    ((not (list? e)) e)
    ((null? e) e)
    (else
     (let ((parts (map rkw--succ-collapse e)))
       (if (and (eq? (car parts) 'succ)
                (pair? (cdr parts)) (null? (cddr parts))
                (exact-nonnegative-integer? (cadr parts)))
           (+ (cadr parts) 1)
           parts)))))

;;; Alpha-equivalence of a pattern INSTANCE with the term it claims to be.
;;; Plain alpha first (much the commonest case and much the cheapest), then
;;; again with both sides succ-collapsed.
(define (rkw--instance-equiv? a b)
  (or (alpha-equiv? a b)
      (alpha-equiv? (rkw--succ-collapse a) (rkw--succ-collapse b))))

;;; -----------------------------------------------------------------------
;;; Conditions

;;; (succ k) / (succ_ORD k) on a literal k folds to k+1, bottom up -- the one
;;; canonical form in which a condition instance coming out of the numeral<->succ
;;; bridge is compared with a context formula written with a numeral.
(define (rkw--numeral-collapse e)
  (cond
    ((not (list? e)) e)
    ((null? e) e)
    (else
     (let ((parts (map rkw--numeral-collapse e)))
       (if (and (memq (car parts) '(succ succ_ORD))
                (pair? (cdr parts)) (null? (cddr parts))
                (exact-nonnegative-integer? (cadr parts)))
           (+ (cadr parts) 1)
           parts)))))

(define (rkw--flatten-and f)
  (if (and (pair? f) (eq? (car f) 'AND) (list? f) (= 3 (length f)))
      (append (rkw--flatten-and (cadr f)) (rkw--flatten-and (caddr f)))
      (list f)))

(define (rkw--flatten-ctx fs) (apply append (map rkw--flatten-and fs)))

;;; A condition instance is discharged when it is TRUTH, when the local context
;;; holds it (directly, or with both sides numeral-collapsed), when it is a true
;;; ground arithmetic sentence, or when it was SPAWNED as a minor-premise
;;; subgoal of this very inference.
(define (rkw--condition-discharged? c ctx minor-goals)
  (or (eq? c 'TRUTH)
      (rkw--in-set? c ctx)
      (let ((cc (rkw--numeral-collapse c)))
        (let loop ((fs ctx))
          (cond ((null? fs) #f)
                ((alpha-equiv? cc (rkw--numeral-collapse (car fs))) #t)
                (else (loop (cdr fs))))))
      (eq? #t (arith-eval-formula (rkw--numeral-collapse c)))
      (rkw--in-set? c minor-goals)))

;;; -----------------------------------------------------------------------
;;; The local context along a path

;;; `free-vars' of a context formula, memoised on the formula OBJECT.  A context
;;; is carried by the same objects from step to step, and the shadowing test
;;; below asks for its free variables at every binder the walk descends through;
;;; without this the checker re-walks the whole context at every binder of every
;;; rewrite.  The table is key-weak, so it holds nothing alive.
(define *rkw--fv-memo* (make-key-weak-eqv-hash-table))

(define (rkw--free-vars f)
  (if (not (pair? f))
      (free-vars f)
      (let ((hit (hash-table-ref/default *rkw--fv-memo* f 'rkw-miss)))
        (if (eq? hit 'rkw-miss)
            (let ((v (free-vars f))) (hash-table-set! *rkw--fv-memo* f v) v)
            hit))))

(define (rkw--drop-shadowed bvars ctx)
  (filter (lambda (f)
            (let ((fvs (rkw--free-vars f)))
              (let loop ((bs bvars))
                (cond ((null? bs) #t)
                      ((memq (car bs) fvs) #f)
                      (else (loop (cdr bs)))))))
          ctx))

;;; -----------------------------------------------------------------------
;;; The parallel walk
;;;
;;; (rkw--walk A B explain ctx) compares the conclusion's formula A with the
;;; hypothesis' formula B.  Where they agree there is nothing to justify.  Where
;;; they differ, EXPLAIN is asked whether the pair is a licensed rewrite at that
;;; position, given the local context; if it is not, the walk descends, and if it
;;; cannot descend the inference is refused.
;;;
;;; EXPLAIN : (lambda (a b ctx) -> #t | string | 'no).  'no means "not a rewrite
;;; here, try deeper"; a string is a licensed shape whose SIDE CONDITION failed
;;; and is reported as is.
;;;
;;; Returns #t, or a string naming the position and the reason.

(define (rkw--explained? r) (eq? r #t))

(define (rkw--walk a b explain ctx)
  (cond
    ((equal? a b) #t)                     ; the common case, and much the cheapest
    ((alpha-equiv? a b) #t)
    (else
     (let ((here (explain a b ctx)))
       (cond
         ((eq? here #t) #t)
         ((string? here) here)
         (else (rkw--descend a b explain ctx)))))))

(define (rkw--walk-list as bs explain ctxs)
  (let loop ((as as) (bs bs) (ctxs ctxs))
    (cond ((null? as) #t)
          (else
           (let ((r (rkw--walk (car as) (car bs) explain (car ctxs))))
             (if (eq? r #t) (loop (cdr as) (cdr bs) (cdr ctxs)) r))))))

(define (rkw--shape-refusal a b)
  (string-append "the goal changed at a position that is not a licensed rewrite: "
                 (rkw--brief a) "  became  " (rkw--brief b)))

(define (rkw--brief e)
  (let ((s (call-with-output-string (lambda (p) (write e p)))))
    (if (> (string-length s) 160) (string-append (substring s 0 157) "...") s)))

(define (rkw--descend a b explain ctx)
  (cond
    ((and (functoid? a) (functoid? b)
          (eq? (functoid-kind a) (functoid-kind b))
          (= (length (functoid-bindings a)) (length (functoid-bindings b)))
          (equal? (map car (functoid-bindings a)) (map car (functoid-bindings b))))
     (let* ((bvars (map car (functoid-bindings a)))
            (inner (rkw--drop-shadowed bvars ctx))
            (doms  (rkw--walk-list (map cdr (functoid-bindings a))
                                   (map cdr (functoid-bindings b))
                                   explain
                                   (map (lambda (x) ctx) (functoid-bindings a)))))
       (if (eq? doms #t)
           (rkw--walk (functoid-body a) (functoid-body b) explain inner)
           doms)))
    ((or (functoid? a) (functoid? b)) (rkw--shape-refusal a b))
    ((not (and (pair? a) (pair? b) (list? a) (list? b)
               (= (length a) (length b))))
     (rkw--shape-refusal a b))
    ;; OPERATOR POSITION.  An application whose operator is itself a term --
    ;; ((MONALG-NEG a m f) x), ((MUL r) a b) -- may be rewritten IN THE
    ;; OPERATOR: the rewriter descends into a pair head like any other
    ;; subexpression, and so does this walk.  The operator is a term, so it
    ;; carries the ambient local context.
    ((not (and (symbol? (car a)) (eq? (car a) (car b))))
     (let ((r (rkw--walk (car a) (car b) explain ctx)))
       (if (eq? r #t)
           (rkw--walk-list (cdr a) (cdr b) explain
                           (map (lambda (x) ctx) (cdr a)))
           r)))
    (else
     (case (car a)
       ((IMPLIES)
        (rkw--walk-list (cdr a) (cdr b) explain
                        (list ctx (append (rkw--flatten-and (cadr a)) ctx))))
       ((AND)
        (rkw--walk-list (cdr a) (cdr b) explain
                        (list (append (rkw--flatten-and (caddr a)) ctx)
                              (append (rkw--flatten-and (cadr a))  ctx))))
       ((OR)
        (rkw--walk-list (cdr a) (cdr b) explain
                        (list (cons `(NOT ,(caddr a)) ctx)
                              (cons `(NOT ,(cadr a))  ctx))))
       ((FORALL FORSOME IOTA COMP)
        (if (not (eq? (cadr a) (cadr b)))
            (let ((z (generate-uninterned-symbol (cadr a))))
              (rkw--walk (subst-free (cadr a) z (caddr a))
                         (subst-free (cadr b) z (caddr b))
                         explain (rkw--drop-shadowed (list (cadr a) (cadr b)) ctx)))
            (rkw--walk (caddr a) (caddr b) explain
                       (rkw--drop-shadowed (list (cadr a)) ctx))))
       ((SEP BIG-UNION)
        ;; (SEP x A p) / (BIG-UNION x A body): A is outside the binder, the
        ;; third argument is under it.  BIG-UNION is a binder the rewriter's own
        ;; descent does not recognise; the checker treats it as one regardless.
        (if (not (eq? (cadr a) (cadr b)))
            (rkw--shape-refusal a b)
            (let ((r (rkw--walk (caddr a) (caddr b) explain ctx)))
              (if (eq? r #t)
                  (rkw--walk (cadddr a) (cadddr b) explain
                             (rkw--drop-shadowed (list (cadr a)) ctx))
                  r))))
       ((VNB-LAMBDA)
        (if (not (equal? (cadr a) (cadr b)))
            (rkw--shape-refusal a b)
            (let ((r (rkw--walk (caddr a) (caddr b) explain ctx)))
              (if (eq? r #t)
                  (rkw--walk (cadddr a) (cadddr b) explain
                             (rkw--drop-shadowed (vnb-lambda-bvars (cadr a)) ctx))
                  r))))
       (else
        ;; Every other head -- connectives with no increment, predicates, terms,
        ;; and an application whose operator is itself an application.
        (rkw--walk-list (cdr a) (cdr b) explain
                        (map (lambda (x) ctx) (cdr a))))))))

;; The local-context walk -- the one that found the BIG-UNION hole in the
;; rewriter, by knowing a binder the rewriter did not.
(declare-binder-walker! 'rkw--walk
                        '(FORALL FORSOME IOTA COMP SEP BIG-UNION VNB-LAMBDA))

;;; -----------------------------------------------------------------------
;;; What a macete NAME denotes
;;;
;;; Returns (SVARS CONDITIONS SOURCE REPLACEMENT KIND) or #f.

(define (rkw--functor-projection-def name)
  (let* ((s (symbol->string name))
         (i (string-search-forward "@" s 0)))
    (and i
         (let ((fn  (string->symbol (substring s 0 i)))
               (acc (string->symbol (substring s (+ i 1) (string-length s)))))
           (let ((reg (hash-table-ref/default *functoid-registry* fn #f))
                 (ai  (hash-table-ref/default *accessor-index* acc #f)))
             (and reg ai
                  (let ((pvars (car reg)) (body (cadr reg)) (k (car ai)))
                    (and (= 1 (length pvars))
                         (pair? body) (list? body) (eq? (car body) 'LIST)
                         (exact-nonnegative-integer? k) (> k 0)
                         (< k (length body))
                         (list pvars '()
                               (list acc (cons fn pvars))
                               (list-ref body k)
                               'functor-projection)))))))))

;;; A memo, because every macete step asks this question and reading a statement
;;; as a rewrite rule is not free.  Keyed by name AND by the statement object the
;;; answer was computed from, so a theorem re-installed under the same name (the
;;; library does re-install, and install-theorem! warns about it) invalidates its
;;; own entry instead of being answered from a stale reading.
(define *rkw--def-memo* (make-strong-eqv-hash-table))

;;; 2026-09-27 (the user's decision, after the certificate agent's finding): the key
;;; used to be the THEOREM object alone, which is #f for a functoid, an accessor or
;;; a functor projection -- so a functoid REDEFINED in the same image (an extend-band
;;; reload) went on being checked against its old body.  The witness is now the
;;; object the answer was computed FROM, whatever table it came from.
(define (rkw--definition-witness name thm0)
  (or thm0
      (hash-table-ref/default *functoid-registry* name #f)
      (hash-table-ref/default *accessor-index* name #f)
      (let* ((s (symbol->string name))
             (i (string-search-forward "@" s 0)))
        (and i
             (cons (hash-table-ref/default *functoid-registry*
                                           (string->symbol (substring s 0 i)) #f)
                   (hash-table-ref/default *accessor-index*
                                           (string->symbol (substring s (+ i 1) (string-length s))) #f))))
      'none))

(define (rkw--witness-same? a b)
  (or (eq? a b)
      (and (pair? a) (pair? b) (eq? (car a) (car b)) (eq? (cdr a) (cdr b)))))

(define (rkw--macete-definition name)
  (let* ((thm0 (and (symbol? name)
                    (hash-table-ref/default *theorem-table* name #f)))
         (w    (and (symbol? name) (rkw--definition-witness name thm0)))
         (hit  (hash-table-ref/default *rkw--def-memo* name #f)))
    (if (and hit (rkw--witness-same? (car hit) w))
        (cdr hit)
        (let ((d (rkw--macete-definition/compute name thm0)))
          (hash-table-set! *rkw--def-memo* name (cons w d))
          d))))

(define (rkw--macete-definition/compute name thm)
  (and (symbol? name)
       (not (eq? name '<anonymous>))
       (begin
         (cond
           (thm
            (call-with-values (lambda () (strip-foralls (prenex-positive thm)))
              (lambda (svars core)
                (call-with-values (lambda () (extract-rewrite-patterns core))
                  (lambda (conds src rep) (list svars conds src rep 'theorem))))))
           ((hash-table-ref/default *functoid-registry* name #f)
            => (lambda (reg)
                 (let ((pvars (car reg)) (body (cadr reg)))
                   (list pvars '() (cons name pvars) body 'functoid))))
           ((hash-table-ref/default *accessor-index* name #f)
            => (lambda (e)
                 (list '(svar) '() (list name 'svar) (list 'NTH (car e) 'svar)
                       'accessor)))
           (else (rkw--functor-projection-def name))))))

;;; The tag's own SOURCE / REPLACEMENT must be the ones NAME denotes, up to the
;;; renaming of schema variables that theorem->elementary-macete performs.  One
;;; match settles it: the definition's source must match the tag's source, and
;;; the same substitution must carry the definition's replacement onto the tag's.
;;;
;;; EXCEPTION, stated rather than hidden: a VARIADIC rule -- one whose source
;;; ends in (RESTVAR v) and whose replacement uses (SPLICE ...) -- is not an
;;; ordinary first-order pattern, and matching one variadic pattern against
;;; another does not mean what matching two terms means.  The two such rules in
;;; the tree (union-decompose, intersection-decompose) get no cross-check; the
;;; rewrite itself is still checked against the definition's patterns below,
;;; which is where the soundness lies.
(define (rkw--variadic? e)
  (cond ((functoid? e) (or (rkw--variadic? (functoid-body e))
                           (rkw--variadic? (map cdr (functoid-bindings e)))))
        ((not (pair? e)) #f)
        ((memq (car e) '(RESTVAR SPLICE)) #t)
        (else (let loop ((xs e))
                (cond ((not (pair? xs)) #f)
                      ((rkw--variadic? (car xs)) #t)
                      (else (loop (cdr xs))))))))

(define (rkw--tag-agrees-with-definition? def tag-src tag-rep)
  (let ((svars (car def)) (src (caddr def)) (rep (cadddr def)))
    (or (rkw--variadic? src) (rkw--variadic? rep)
        (let ((sub (rkw--match src tag-src svars)))
          (and sub
               (rkw--instance-equiv? (rkw--inst sub src) tag-src)
               (rkw--instance-equiv? (rkw--inst sub rep) tag-rep))))))

;;; -----------------------------------------------------------------------
;;; The explain procedure for a macete
;;;
;;; At a position where the two formulas differ, the pair (a, b) is licensed
;;; when there is a substitution sigma of the macete's schema variables with
;;;     sigma(L) = a   and   sigma(R) = b   (up to alpha)
;;; and every sigma(C) for C a condition of the macete is discharged: held in
;;; the LOCAL CONTEXT of that position, or spawned as a minor premise of this
;;; inference.

(define (rkw--macete-explainer def minor-goals)
  (let ((svars (car def)) (conds (cadr def)) (src (caddr def)) (rep (cadddr def)))
    (lambda (a b ctx)
      (let ((sub (rkw--match src a svars)))
        (cond
          ((not sub) 'no)
          ((not (rkw--instance-equiv? (rkw--inst sub src) a)) 'no)
          ((not (rkw--instance-equiv? (rkw--inst sub rep) b)) 'no)
          (else
           (let loop ((cs conds))
             (cond
               ((null? cs) #t)
               (else
                (let ((ci (rkw--inst sub (car cs))))
                  (if (rkw--condition-discharged? ci ctx minor-goals)
                      (loop (cdr cs))
                      (string-append
                       "the macete fired at " (rkw--brief a)
                       " but its condition " (rkw--brief ci)
                       " is neither in the local context of that position nor a"
                       " minor premise of the step")))))))))) ))

;;; -----------------------------------------------------------------------
;;; macete -- the GOAL side
;;;
;;; RELATION.  For a conclusion Gamma => G and a tag (macete N L R):
;;;   N denotes a rewrite rule (conditions, L0, R0); the tag's L, R are that
;;;   rule's patterns.  The first hypothesis is Gamma => G', where G' is G with
;;;   SOME occurrences of instances of L0 replaced by the corresponding
;;;   instances of R0, each instance's conditions holding in the local context
;;;   of its position or appearing among the remaining hypotheses (which are
;;;   Gamma => C, the minor premises `macm' spawns).  Every hypothesis carries
;;;   the same assumptions as the conclusion.

(define (rkw--check-macete rule hyps concl)
  (cond
    ((not (and (list? rule) (= 4 (length rule))))
     "the macete tag must be (macete NAME SOURCE REPLACEMENT)")
    ((null? hyps) "a macete inference has at least one hypothesis")
    (else
     (let* ((name  (cadr rule))
            (def   (rkw--macete-definition name))
            (casms (rkw--asm-formulas concl))
            (main  (car hyps))
            (minors (cdr hyps)))
       (cond
         ((not def)
          (string-append "no installed theorem, functoid, accessor or functor"
                         " projection is named " (rkw--brief name)
                         " -- nothing licenses this rewrite"))
         ((not (rkw--tag-agrees-with-definition? def (caddr rule) (cadddr rule)))
          (string-append "the tag's source/replacement are not the patterns "
                         (rkw--brief name) " denotes"))
         ((not (rkw--same-assumptions? casms (rkw--asm-formulas main)))
          "the rewritten sequent does not carry the conclusion's assumptions")
         ((let loop ((ms minors))
            (cond ((null? ms) #f)
                  ((rkw--same-assumptions? casms (rkw--asm-formulas (car ms)))
                   (loop (cdr ms)))
                  (else "a minor premise does not carry the conclusion's assumptions")))
          => (lambda (why) why))
         (else
          (let ((r (rkw--walk (rkw--goal-formula concl)
                              (rkw--goal-formula main)
                              (rkw--macete-explainer def (map rkw--goal-formula minors))
                              ;; flattened ONCE, here: every extension the walk
                              ;; makes is flattened as it is made.
                              (rkw--flatten-ctx casms))))
            (if (eq? r #t) #t r))))))))

;;; -----------------------------------------------------------------------
;;; macete-hyp -- the ASSUMPTION side
;;;
;;; RELATION.  For a conclusion Gamma => G and a tag (macete-hyp N L R): the
;;; first hypothesis is (Gamma - H + H') => G, where H is one assumption of
;;; Gamma and H' is H rewritten by N exactly as on the goal side.  The goal is
;;; untouched.  The local context is seeded with ALL of Gamma, H included: H
;;; entails each of its own conjuncts, and the rewrite replaces H by something
;;; equivalent to it under the discharged conditions, so nothing is lost.  The
;;; remaining hypotheses are Gamma => C, the conditions the rewrite could not
;;; discharge.
;;;
;;; The step is sound because the macete's core is an equivalence under its
;;; conditions (apply-macete-to-assumption! fires only for an IFF / = / == core,
;;; and a degenerate core -- replacement TRUTH -- is the theorem's own assertion,
;;; hence equivalent to TRUTH under the same conditions), so Gamma proves every
;;; formula of Gamma - H + H'.

(define (rkw--check-macete-hyp rule hyps concl)
  (cond
    ((not (and (list? rule) (= 4 (length rule))))
     "the macete-hyp tag must be (macete-hyp NAME SOURCE REPLACEMENT)")
    ((null? hyps) "a macete-hyp inference has at least one hypothesis")
    (else
     (let* ((name   (cadr rule))
            (def    (rkw--macete-definition name))
            (casms  (rkw--asm-formulas concl))
            (main   (car hyps))
            (minors (cdr hyps))
            (masms  (rkw--asm-formulas main))
            (removed (rkw--set-minus casms masms))
            (added   (rkw--set-minus masms casms)))
       (cond
         ((not def)
          (string-append "no installed theorem, functoid, accessor or functor"
                         " projection is named " (rkw--brief name)
                         " -- nothing licenses this rewrite"))
         ((not (rkw--tag-agrees-with-definition? def (caddr rule) (cadddr rule)))
          (string-append "the tag's source/replacement are not the patterns "
                         (rkw--brief name) " denotes"))
         ((not (alpha-equiv? (rkw--goal-formula concl) (rkw--goal-formula main)))
          "macete-hyp must leave the goal unchanged")
         ((not (= 1 (length removed)))
          (string-append "macete-hyp must replace exactly ONE assumption; "
                         (number->string (length removed)) " left the context"))
         ((> (length added) 1)
          (string-append "macete-hyp must add at most one assumption; "
                         (number->string (length added)) " appeared"))
         ((let loop ((ms minors))
            (cond ((null? ms) #f)
                  ((rkw--same-assumptions? casms (rkw--asm-formulas (car ms)))
                   (loop (cdr ms)))
                  (else "a minor premise does not carry the conclusion's assumptions")))
          => (lambda (why) why))
         (else
          (let* ((h        (car removed))
                 (explain  (rkw--macete-explainer def (map rkw--goal-formula minors)))
                 ;; H' is the assumption that appeared; when the rewritten form
                 ;; was already in the context nothing appeared, and any
                 ;; assumption of the new context may play that part.
                 (candidates (if (null? added) masms added))
                 (ctx0     (rkw--flatten-ctx casms))
                 (reasons  '()))
            (let loop ((cs candidates))
              (cond
                ((null? cs)
                 (string-append
                  "no assumption of the hypothesis is " (rkw--brief h)
                  " rewritten by " (rkw--brief name)
                  (if (null? reasons) "" (string-append " -- " (car reasons)))))
                (else
                 (let ((r (rkw--walk h (car cs) explain ctx0)))
                   (if (eq? r #t)
                       #t
                       (begin (set! reasons (append reasons (list r)))
                              (loop (cdr cs)))))))))))))))

;;; -----------------------------------------------------------------------
;;; cartesian-decompose
;;;
;;; RELATION.  One hypothesis, same assumptions, same goal except that SOME
;;; occurrences of
;;;     (IN x (CARTESIAN A_1 ... A_n))          n >= 1
;;; are replaced by
;;;     (FORSOME v_1 (AND (IN v_1 A_1) ... (FORSOME v_n (AND (IN v_n A_n)
;;;                                           (= x (LIST v_1 ... v_n)))) ...))
;;; with the v_i pairwise distinct and none of them free in x or in any A_j.
;;; That freshness is the whole side condition: a v_i occurring free in x or in
;;; an A_j would be CAPTURED by the FORSOME, and the replacement would say
;;; something else.  (A v_i clashing with a binder further out is harmless: the
;;; only way such a name can reach inside is through x or the A_j.)
;;;
;;; The rule is the membership schema of the cartesian product, one instance per
;;; arity, and is on the primitive shelf (library.scm).  The checker confirms the
;;; instance, not the schema.

(define (rkw--cartesian-shape? x classes b)
  (let loop ((cs classes) (e b) (vars '()))
    (cond
      ((null? cs)
       (and (list? e) (= 3 (length e)) (eq? (car e) '=)
            (equal? (cadr e) x)
            (let ((l (caddr e)))
              (and (pair? l) (list? l) (eq? (car l) 'LIST)
                   (equal? (cdr l) (reverse vars))))
            (let* ((vs (reverse vars))
                   (bad (append (free-vars x)
                                (apply append (map free-vars classes)))))
              (and (= (length vs) (length (delete-duplicates vs eq?)))
                   (let check ((vs vs))
                     (cond ((null? vs) #t)
                           ((memq (car vs) bad) #f)
                           (else (check (cdr vs)))))))))
      ((and (list? e) (= 3 (length e)) (eq? (car e) 'FORSOME)
            (let ((body (caddr e)))
              (and (list? body) (= 3 (length body)) (eq? (car body) 'AND)
                   (let ((m (cadr body)))
                     (and (list? m) (= 3 (length m)) (eq? (car m) 'IN)
                          (eq? (cadr m) (cadr e))
                          (equal? (caddr m) (car cs)))))))
       (loop (cdr cs) (caddr (caddr e)) (cons (cadr e) vars)))
      (else #f))))

(define (rkw--cartesian-explainer a b ctx)
  (if (and (list? a) (= 3 (length a)) (eq? (car a) 'IN)
           (let ((prod (caddr a)))
             (and (list? prod) (eq? (car prod) 'CARTESIAN) (pair? (cdr prod)))))
      (if (rkw--cartesian-shape? (cadr a) (cdr (caddr a)) b)
          #t
          (string-append "cartesian-decompose rewrote " (rkw--brief a)
                         " into something that is not its membership schema"
                         " with fresh, uncaptured witnesses: " (rkw--brief b)))
      'no))

(define (rkw--check-one-hypothesis-rewrite tag hyps concl explain)
  (cond
    ((not (= 1 (length hyps)))
     (string-append (symbol->string tag) " has exactly one hypothesis"))
    ((not (rkw--same-assumptions? (rkw--asm-formulas concl)
                                  (rkw--asm-formulas (car hyps))))
     (string-append (symbol->string tag)
                    " must not change the assumptions"))
    (else
     (let ((r (rkw--walk (rkw--goal-formula concl) (rkw--goal-formula (car hyps))
                         explain (rkw--asm-formulas concl))))
       (if (eq? r #t) #t r)))))

(define (rkw--check-cartesian-decompose rule hyps concl)
  (rkw--check-one-hypothesis-rewrite 'cartesian-decompose hyps concl
                                     rkw--cartesian-explainer))

;;; -----------------------------------------------------------------------
;;; tuple-equality-decompose
;;;
;;; RELATION.  One hypothesis, same assumptions, same goal except that SOME
;;; occurrences of (= (LIST a_1..a_n) (LIST b_1..b_n)) -- both sides LIST forms
;;; of the SAME length -- are replaced by the right-nested conjunction of the
;;; component equations, with n = 0 giving TRUTH and n = 1 giving (= a_1 b_1).
;;; The conjunction is rebuilt here and compared.

(define (rkw--tuple-conjunction as bs)
  (cond
    ((null? as) 'TRUTH)
    ((null? (cdr as)) `(= ,(car as) ,(car bs)))
    (else `(AND (= ,(car as) ,(car bs))
                ,(rkw--tuple-conjunction (cdr as) (cdr bs))))))

(define (rkw--tuple-explainer a b ctx)
  (if (and (list? a) (= 3 (length a)) (eq? (car a) '=)
           (list? (cadr a)) (pair? (cadr a)) (eq? (car (cadr a)) 'LIST)
           (list? (caddr a)) (pair? (caddr a)) (eq? (car (caddr a)) 'LIST)
           (= (length (cadr a)) (length (caddr a))))
      (if (alpha-equiv? b (rkw--tuple-conjunction (cdr (cadr a)) (cdr (caddr a))))
          #t
          (string-append "tuple-equality-decompose rewrote " (rkw--brief a)
                         " into something other than the conjunction of its"
                         " component equations: " (rkw--brief b)))
      'no))

(define (rkw--check-tuple-equality-decompose rule hyps concl)
  (rkw--check-one-hypothesis-rewrite 'tuple-equality-decompose hyps concl
                                     rkw--tuple-explainer))

;;; -----------------------------------------------------------------------
;;; Registration

(register-rule-checker! 'macete                   rkw--check-macete)
(register-rule-checker! 'macete-hyp               rkw--check-macete-hyp)
(register-rule-checker! 'cartesian-decompose      rkw--check-cartesian-decompose)
(register-rule-checker! 'tuple-equality-decompose rkw--check-tuple-equality-decompose)
