;;; rule-checkers-logic.scm -- the 42 `logic' kernel operations, CHECKED.
;;;
;;; Batch 10-A, 2026-09-20.  `dg-apply-rule!' (deduction-graphs.scm) is the one
;;; write point of the deduction graph; with *dg-check-inferences?* ON it calls
;;; the checker registered for the rule's tag head before anything is written.
;;; A checker VERIFIES A FINISHED INFERENCE: it is handed the conclusion sequent
;;; and the hypothesis sequents and answers whether they stand in the relation
;;; the named rule prescribes.  It does not rebuild the inference -- it neither
;;; calls nor copies the pi-* procedure that built the hypotheses, and uses only
;;; the expression layer (expressions.scm, wff.scm, sequents.scm) plus the
;;; one-way matcher below, which is what FINDS a term the rule left implicit
;;; (the t of forall-elim, the witness of forsome-intro, the eigenvariables of
;;; forall-intro).
;;;
;;; CONVENTIONS, all three of them binding on the other three checker files,
;;; which load after this one and use its helpers:
;;;
;;;   1. ASSUMPTION LISTS ARE COMPARED AS SETS, up to alpha-equivalence.  A
;;;      sequent's assumptions are a list only because a list is what a context
;;;      is stored in; `context-add-assumption' already refuses a duplicate and
;;;      `context-remove-assumption' drops every alpha-copy, so order and
;;;      multiplicity carry no meaning here and no checker may rely on them.
;;;   2. A rule that ADDS a formula is checked as a SET UNION, not as "the
;;;      hypothesis has one more formula".  When the formula a rule adds is
;;;      already in the context, the builder adds nothing, and the set union
;;;      then says exactly the same thing.
;;;   3. Refusal is a STRING, and the string names what failed.  A refusal
;;;      during a load is a finding to be read, never something to silence.
;;;
;;; WHAT THIS BATCH DOES NOT CHECK, deliberately and by policy:
;;;
;;;   * THE DEFINEDNESS CERTIFICATE.  `forall-elim' owes the side sequent
;;;     (= t t) exactly when `pi--defined?' declines to certify t
;;;     (docs/definedness-instantiation-2026-09-18.md).  That certificate is a
;;;     POLICY about when an obligation may be skipped, not a rule of logic:
;;;     instantiating a universal at a term is sound in LUTINS as soon as the
;;;     term denotes, and the owed sequent is how VNB discharges that.  So the
;;;     checker accepted the side sequent present OR absent, and re-checked
;;;     nothing about which it was.  SUPERSEDED 2026-09-24 for forall-elim (see
;;;     the checker): the side sequent must be  t = t  for the instantiation
;;;     term, and its absence needs the certificate, part re-decided here and
;;;     part re-run through `pi--defined?'.  `reflexivity' is still `t = t'
;;;     with a definedness condition the checker does not re-derive.
;;;   * TRUST.  A checker says the inference has the shape the rule licenses.
;;;     It says nothing about the trust tier of the theorems cited; that is the
;;;     ledger's job (proof-debt.scm).

;;; =======================================================================
;;; SHARED HELPERS  (the other three rule-checkers-*.scm files use these)
;;; =======================================================================

(define (chk-every pred lst)
  (cond ((null? lst) #t)
        ((pred (car lst)) (chk-every pred (cdr lst)))
        (else #f)))

(define (chk-any pred lst)
  (cond ((null? lst) #f)
        ((pred (car lst)) #t)
        (else (chk-any pred (cdr lst)))))

(define (chk-every2 pred l1 l2)
  (cond ((and (null? l1) (null? l2)) #t)
        ((or (null? l1) (null? l2)) #f)
        ((pred (car l1) (car l2)) (chk-every2 pred (cdr l1) (cdr l2)))
        (else #f)))

(define (chk-find pred lst)
  (cond ((null? lst) #f)
        ((pred (car lst)) (car lst))
        (else (chk-find pred (cdr lst)))))

;;; Two raw formulas, the same up to alpha.  The `eq?' arm is not an
;;; optimisation of a rare case: the builders cons a new context out of the
;;; very wff objects the old one held, so most comparisons are pointer-equal.
(define (chk-same? a b)
  (or (eq? a b) (alpha-equiv? a b)))

(define (chk-mem? f fs)
  (chk-any (lambda (g) (chk-same? f g)) fs))

(define (chk-subset? fs gs)
  (chk-every (lambda (f) (chk-mem? f gs)) fs))

(define (chk-set=? fs gs)
  (and (chk-subset? fs gs) (chk-subset? gs fs)))

;;; The raw formulas of a sequent's assumptions, and its raw goal.
(define (chk-asms s) (map wff-formula (sequent-assumptions s)))
(define (chk-goal s) (wff-formula (sequent-assertion s)))

;;; Set difference and union, up to alpha.
(define (chk-minus fs gs)
  (filter (lambda (f) (not (chk-mem? f gs))) fs))

(define (chk-union fs gs)
  (append fs (filter (lambda (g) (not (chk-mem? g fs))) gs)))

;;; The relations between two contexts that the rules actually use.
(define (chk-ctx=? hyp concl)            ; context unchanged
  (chk-set=? (chk-asms hyp) (chk-asms concl)))

(define (chk-ctx+? hyp concl extras)     ; context gains EXTRAS (a raw list)
  (chk-set=? (chk-asms hyp) (chk-union (chk-asms concl) extras)))

(define (chk-ctx-+? hyp concl removed added)   ; loses REMOVED, gains ADDED
  (chk-set=? (chk-asms hyp)
             (chk-union (chk-minus (chk-asms concl) removed) added)))

;;; The formulas the hypothesis context has and the conclusion context has not.
;;; When a rule's added formula was already in the context this is EMPTY, so a
;;; checker that must find that formula looks in the conclusion context too --
;;; `chk-added-candidates'.
(define (chk-added hyp concl)
  (chk-minus (chk-asms hyp) (chk-asms concl)))

(define (chk-added-candidates hyp concl)
  (let ((delta (chk-added hyp concl)))
    (if (null? delta) (chk-asms concl) delta)))

;;; A hypothesis that adds NOTHING to the context and keeps the goal makes the
;;; inference sound whatever the rule names: the conclusion is that hypothesis,
;;; or a weakening of it.  Several rules reach this case -- the formula they
;;; would add is already in the context, and `context-add-assumption' then adds
;;; nothing -- and it is worth naming, because the search for "which formula
;;; was added" has nothing to find there and would scan the whole theorem table
;;; (theorem-assumption) or every universal in the context (forall-elim) for
;;; nothing.  The checkers below take it as a fast ACCEPT.
(define (chk-adds-nothing? hyp concl)
  (and (chk-goal=? hyp concl)
       (chk-subset? (chk-asms hyp) (chk-asms concl))))

(define (chk-goal=? hyp concl)
  (chk-same? (chk-goal hyp) (chk-goal concl)))

(define (chk-arity? hyps n) (= (length hyps) n))

;;; Free variables of a whole context.
(define (chk-ctx-free-vars fs)
  (apply append (map free-vars fs)))

;;; -----------------------------------------------------------------------
;;; ONE-WAY MATCHING
;;;
;;; (chk-match pvars pattern instance) returns an alist ((pvar . term) ...)
;;; such that pattern with those substitutions is alpha-equivalent to instance,
;;; or #f.  PVARS is the list of holes.  A hole not reached by the walk simply
;;; does not appear in the result (the rule is then vacuous in that variable).
;;;
;;; It is a MATCHER, not a unifier: only the pattern has holes.  Binders are
;;; matched up to renaming exactly as `alpha-equiv-under?' does, and a hole may
;;; not be filled by a term mentioning a variable bound INSIDE the pattern --
;;; that is the condition that makes "the instance is p[x := t] for some t"
;;; mean what it says.
;;;
;;; An empty result is '(), which is not #f, so the caller tests with `and'.

(define (chk-match pvars pattern instance)
  (chk-match-under pvars pattern instance '() '()))

(define (chk-match-ext pvars pattern instance bnds)
  (and bnds (chk-match-under pvars pattern instance '() bnds)))

;;; Does E mention, free, any variable bound on the INSTANCE side of ENV?
(define (chk-escapes? e env)
  (and (pair? env)
       (let ((fvs (free-vars e)))
         (chk-any (lambda (p) (memq (cdr p) fvs)) env))))

(define (chk-match-under pvars pat inst env bnds)
  (cond
    ((not bnds) #f)
    ;; a HOLE, unless a binder of the pattern has shadowed it
    ((and (symbol? pat) (memq pat pvars) (not (assq pat env)))
     (let ((prev (assq pat bnds)))
       (cond (prev (and (chk-same? (cdr prev) inst) bnds))
             ((chk-escapes? inst env) #f)
             (else (cons (cons pat inst) bnds)))))
    ((symbol? pat)
     (let ((m (assq pat env)))
       (if m
           (and (symbol? inst) (eq? (cdr m) inst) (eq? m (rassq inst env)) bnds)
           (and (symbol? inst) (eq? pat inst) (not (rassq inst env)) bnds))))
    ((number? pat) (and (number? inst) (number? pat) (= pat inst) bnds))
    ((functoid? pat)
     (and (functoid? inst)
          (eq? (functoid-kind pat) (functoid-kind inst))
          (= (length (functoid-bindings pat)) (length (functoid-bindings inst)))
          (let loop ((b1 (functoid-bindings pat))
                     (b2 (functoid-bindings inst))
                     (b  bnds))
            (if (null? b1)
                (chk-match-under
                 pvars (functoid-body pat) (functoid-body inst)
                 (append (map cons
                              (map car (functoid-bindings pat))
                              (map car (functoid-bindings inst)))
                         env)
                 b)
                (loop (cdr b1) (cdr b2)
                      (chk-match-under pvars (cdar b1) (cdar b2) env b))))))
    ((functoid? inst) #f)
    ((not (pair? pat)) (and (equal? pat inst) bnds))
    ((not (pair? inst)) #f)
    ;; the binder forms: (H v body) and (H v domain body), domain OUTSIDE
    ((and (memq (car pat) '(FORALL FORSOME IOTA COMP))
          (= (length pat) 3) (eq? (car inst) (car pat)) (= (length inst) 3))
     (chk-match-under pvars (caddr pat) (caddr inst)
                      (cons (cons (cadr pat) (cadr inst)) env) bnds))
    ((and (memq (car pat) '(SEP BIG-UNION VNB-LAMBDA))
          (= (length pat) 4) (eq? (car inst) (car pat)) (= (length inst) 4))
     (let ((b (chk-match-under pvars (caddr pat) (caddr inst) env bnds))
           (v1 (cadr pat)) (v2 (cadr inst)))
       (and b
            (let ((vs1 (if (symbol? v1) (list v1) (cdr v1)))
                  (vs2 (if (symbol? v2) (list v2) (cdr v2))))
              (and (= (length vs1) (length vs2))
                   (chk-match-under pvars (cadddr pat) (cadddr inst)
                                    (append (map cons vs1 vs2) env) b))))))
    ;; any other application / connective: element by element, the HEAD too
    (else
     (and (= (length pat) (length inst))
          (let loop ((ps pat) (is inst) (b bnds))
            (if (null? ps)
                b
                (let ((b2 (chk-match-under pvars (car ps) (car is) env b)))
                  (and b2 (loop (cdr ps) (cdr is) b2)))))))))

(define (chk-bound pvar bnds)
  (let ((p (assq pvar bnds))) (and p (cdr p))))

;; The instance matcher's binder vocabulary, declared for binder-walker-audit
;; (expressions.scm: declare-binder-walker!).
(declare-binder-walker! 'chk-match-under
                        '(FORALL FORSOME IOTA COMP SEP BIG-UNION VNB-LAMBDA))

;;; -----------------------------------------------------------------------
;;; TWO RELATIONS ON EXPRESSIONS, used by several checkers.

;;; (chk-replaced? g g2 s t): G2 is G with SOME occurrences of S replaced by T,
;;; and NO replaced occurrence is CAPTURED.  Verified by walking both in
;;; parallel: where they differ, the pair must be (s, t).  Binder heads are
;;; allowed to differ in the bound NAME, since a capture-avoiding substitution
;;; renames them.
;;;
;;; THE CAPTURE TEST (2026-09-24, gap 1 of the checker-vs-builder reading).  The
;;; walk carries BOUND, the variables bound by the binders enclosing the current
;;; position (named as G2 names them, i.e. after any renaming).  A position where
;;; (s, t) is accepted must have no free variable of S and no free variable of T
;;; in BOUND: otherwise the occurrence of s there is not the s of the equation
;;; (s mentions a variable the binder rebinds), or the t written there is not the
;;; t of the equation (the binder captures a variable of t).  Without it,
;;;   x = 0 in context, goal  forall x. x = 0,  hypothesis  forall x. 0 = 0
;;; was ACCEPTED, and FALSITY followed.  The test reads the binder chain of the
;;; conclusion / hypothesis pair; it does not call the builder's replace-term.
(define (chk-replaced? g g2 s t)
  (chk-replaced-under? g g2 s t '()))

(define (chk-repl-uncaptured? s t bound)
  (or (null? bound)
      (and (not (chk-any (lambda (v) (memq v bound)) (free-vars s)))
           (not (chk-any (lambda (v) (memq v bound)) (free-vars t))))))

;;; The parts of a binder form: (bvars domain-or-#f body), or #f.  The DOMAIN of
;;; SEP / BIG-UNION / VNB-LAMBDA is outside the binder.
(define (chk-repl-binder-parts e)
  (cond
    ((and (memq (car e) '(FORALL FORSOME IOTA COMP)) (= (length e) 3)
          (symbol? (cadr e)))
     (list (list (cadr e)) #f (caddr e)))
    ((and (memq (car e) '(SEP BIG-UNION)) (= (length e) 4) (symbol? (cadr e)))
     (list (list (cadr e)) (caddr e) (cadddr e)))
    ((and (eq? (car e) 'VNB-LAMBDA) (= (length e) 4)
          (or (symbol? (cadr e))
              (and (pair? (cadr e)) (eq? (car (cadr e)) 'LIST) (list? (cadr e))
                   (chk-every symbol? (cdr (cadr e))))))
     (list (if (symbol? (cadr e)) (list (cadr e)) (cdr (cadr e)))
           (caddr e) (cadddr e)))
    (else #f)))

;;; Body B1 bound by BV1, re-expressed with G2's names BV2.  #f when the
;;; renaming is not a legitimate one (a new name free in B1, or two new names
;;; spelled alike).
(define (chk-repl-rename bv1 bv2 b1)
  (cond
    ((equal? bv1 bv2) b1)
    ((not (= (length bv1) (length bv2))) #f)
    ((let loop ((l bv2))
       (and (pair? l) (or (memq (car l) (cdr l)) (loop (cdr l)))))
     #f)
    ((chk-any (lambda (p) (and (not (eq? (car p) (cdr p)))
                               (memq (cdr p) (free-vars b1))))
              (map cons bv1 bv2))
     #f)
    (else (subst-free* (map cons bv1 bv2) b1))))

(define (chk-replaced-under? g g2 s t bound)
  (cond
    ((chk-same? g g2) #t)
    ((and (chk-same? g s) (chk-same? g2 t)) (chk-repl-uncaptured? s t bound))
    ((functoid? g)
     (and (functoid? g2)
          (eq? (functoid-kind g) (functoid-kind g2))
          (= (length (functoid-bindings g)) (length (functoid-bindings g2)))
          ;; the domains are outside the binder
          (chk-every2 (lambda (b1 b2) (chk-replaced-under? (cdr b1) (cdr b2) s t bound))
                      (functoid-bindings g) (functoid-bindings g2))
          (let* ((bv1 (map car (functoid-bindings g)))
                 (bv2 (map car (functoid-bindings g2)))
                 (b1  (chk-repl-rename bv1 bv2 (functoid-body g))))
            (and b1
                 (chk-replaced-under? b1 (functoid-body g2) s t (append bv2 bound))))))
    ((or (not (pair? g)) (not (pair? g2))) #f)
    ((not (list? g)) #f)
    ((not (list? g2)) #f)
    ((and (eq? (car g) (car g2)) (= (length g) (length g2))
          (chk-repl-binder-parts g))
     => (lambda (p1)
          (let ((p2 (chk-repl-binder-parts g2)))
            (and p2
                 (eq? (symbol? (cadr g)) (symbol? (cadr g2)))
                 (or (not (cadr p1))
                     (chk-replaced-under? (cadr p1) (cadr p2) s t bound))
                 ;; a binder whose bound name the substitution renamed
                 ;; (subst-free is capture-avoiding): compare G's body under
                 ;; G2's names, and bind those names for the capture test
                 (let ((b1 (chk-repl-rename (car p1) (car p2) (caddr p1))))
                   (and b1
                        (chk-replaced-under? b1 (caddr p2) s t
                                             (append (car p2) bound))))))))
    (else
     (and (= (length g) (length g2))
          (chk-every2 (lambda (a b) (chk-replaced-under? a b s t bound)) g g2)))))

(declare-binder-walker! 'chk-replaced-under?
                        '(FORALL FORSOME IOTA COMP SEP BIG-UNION VNB-LAMBDA))
;;; (chk-contracts? e e2 redex? contract): E2 is E with SOME redexes contracted,
;;; possibly nested and repeatedly.  REDEX? recognises a redex, CONTRACT
;;; performs ONE contraction.  This is how the reduction rules (nth-reduce,
;;; length-reduce, functoid-beta, and 10-B's beta rules) are checked without
;;; calling the kernel's reducer: the contraction is written here, and the
;;; relation tested is "some licensed contractions were performed", which is
;;; weaker than "the normal form was reached" and therefore sound.
(define (chk-contracts? e e2 redex? contract)
  (chk-contracts-d? e e2 redex? contract 0))

(define (chk-contracts-d? e e2 redex? contract depth)
  (cond
    ((> depth 400) #f)
    ((chk-same? e e2) #t)
    ((and (pair? e) (redex? e)
          (chk-contracts-d? (contract e) e2 redex? contract (+ depth 1))) #t)
    ((or (not (pair? e)) (not (pair? e2))) #f)
    ((or (not (list? e)) (not (list? e2))) #f)
    ((not (= (length e) (length e2))) #f)
    (else (chk-every2 (lambda (a b) (chk-contracts-d? a b redex? contract (+ depth 1)))
                      e e2))))

;;; -----------------------------------------------------------------------
;;; THE THEOREM TABLE, BY STATEMENT.
;;;
;;; `theorem-assumption' adds the installed formula of a NAME the tag does not
;;; carry, so the checker searches the table by statement.  The fast path is an
;;; IDENTITY lookup -- `pi-theorem-assumption!' hands over the table's own
;;; S-expression, so the object itself is the key, and an eqv table is hashed by
;;; pointer, which is what keeps the index cheap to rebuild (it is rebuilt
;;; whenever the table has grown, and every qed grows it).  An `equal?' index
;;; would hash the whole formula tree on every insertion and cost the load tens
;;; of seconds.  The slow path is a full alpha-equivalence scan, for a statement
;;; that reached the context as a rebuilt copy.
;;;
;;; REPORTED, per the brief: the tag was NOT extended to carry the name.  The
;;; statement is what the rule is about -- the name is a handle on it -- and a
;;; tag change would have touched the ledger, the page emitter and the proof
;;; printers, which are 10-C's territory for the macete tag alone.
(define *chk-theorem-index* #f)
(define *chk-theorem-index-size* -1)

(define (chk-theorem-index)
  (let ((n (hash-table/count *theorem-table*)))
    (if (or (not *chk-theorem-index*) (not (= n *chk-theorem-index-size*)))
        (let ((t (make-strong-eqv-hash-table)))
          (hash-table-walk *theorem-table*
            (lambda (name stmt) (hash-table-set! t stmt name)))
          (set! *chk-theorem-index* t)
          (set! *chk-theorem-index-size* n))))
  *chk-theorem-index*)

(define (chk-installed-theorem-name f)
  (or (hash-table-ref/default (chk-theorem-index) f #f)
      (call-with-current-continuation
       (lambda (k)
         (hash-table-walk *theorem-table*
           (lambda (name stmt) (if (chk-same? stmt f) (k name))))
         #f))))

;;; =======================================================================
;;; THE 42 CHECKERS
;;;
;;; Each entry says, in one line, the relation it enforces between the
;;; conclusion sequent  Gamma => G  and the hypothesis sequents.
;;; =======================================================================

;;; --- introduction rules on the GOAL ------------------------------------

;;; and-intro: G = (AND p q); two hypotheses, same context, goals p and q.
(register-rule-checker! 'and-intro
  (lambda (rule hyps concl)
    (let ((g (chk-goal concl)))
      (cond ((not (and (pair? g) (eq? (car g) 'AND) (= (length g) 3)))
             "the goal is not a binary AND")
            ((not (chk-arity? hyps 2)) "and-intro takes exactly two hypotheses")
            ((not (and (chk-ctx=? (car hyps) concl) (chk-ctx=? (cadr hyps) concl)))
             "and-intro may not change the context")
            ((not (chk-same? (chk-goal (car hyps)) (binary-left g)))
             "the first hypothesis is not the left conjunct")
            ((not (chk-same? (chk-goal (cadr hyps)) (binary-right g)))
             "the second hypothesis is not the right conjunct")
            (else #t)))))

;;; or-intro-left: G = (OR p q); one hypothesis, same context, goal p.
(register-rule-checker! 'or-intro-left
  (lambda (rule hyps concl)
    (let ((g (chk-goal concl)))
      (cond ((not (and (pair? g) (eq? (car g) 'OR) (= (length g) 3)))
             "the goal is not a binary OR")
            ((not (chk-arity? hyps 1)) "or-intro-left takes one hypothesis")
            ((not (chk-ctx=? (car hyps) concl)) "the context changed")
            ((not (chk-same? (chk-goal (car hyps)) (binary-left g)))
             "the hypothesis is not the LEFT disjunct")
            (else #t)))))

;;; or-intro-right: G = (OR p q); one hypothesis, same context, goal q.
(register-rule-checker! 'or-intro-right
  (lambda (rule hyps concl)
    (let ((g (chk-goal concl)))
      (cond ((not (and (pair? g) (eq? (car g) 'OR) (= (length g) 3)))
             "the goal is not a binary OR")
            ((not (chk-arity? hyps 1)) "or-intro-right takes one hypothesis")
            ((not (chk-ctx=? (car hyps) concl)) "the context changed")
            ((not (chk-same? (chk-goal (car hyps)) (binary-right g)))
             "the hypothesis is not the RIGHT disjunct")
            (else #t)))))

;;; implies-intro: G = (IMPLIES p q); one hypothesis, context gains p, goal q.
(register-rule-checker! 'implies-intro
  (lambda (rule hyps concl)
    (let ((g (chk-goal concl)))
      (cond ((not (and (pair? g) (eq? (car g) 'IMPLIES) (= (length g) 3)))
             "the goal is not an IMPLIES")
            ((not (chk-arity? hyps 1)) "implies-intro takes one hypothesis")
            ((not (chk-ctx+? (car hyps) concl (list (binary-left g))))
             "the context must gain the ANTECEDENT and nothing else")
            ((not (chk-same? (chk-goal (car hyps)) (binary-right g)))
             "the hypothesis goal is not the consequent")
            (else #t)))))

;;; not-intro: G = (NOT p); one hypothesis, context gains p, goal FALSITY.
(register-rule-checker! 'not-intro
  (lambda (rule hyps concl)
    (let ((g (chk-goal concl)))
      (cond ((not (and (pair? g) (eq? (car g) 'NOT) (= (length g) 2)))
             "the goal is not a NOT")
            ((not (chk-arity? hyps 1)) "not-intro takes one hypothesis")
            ((not (chk-ctx+? (car hyps) concl (list (not-body g))))
             "the context must gain exactly the negated formula")
            ((not (eq? (chk-goal (car hyps)) 'FALSITY))
             "the hypothesis goal must be FALSITY")
            (else #t)))))

;;; iff-intro: G = (IFF p q); two hypotheses, ctx+p => q and ctx+q => p.
(register-rule-checker! 'iff-intro
  (lambda (rule hyps concl)
    (let ((g (chk-goal concl)))
      (cond ((not (and (pair? g) (eq? (car g) 'IFF) (= (length g) 3)))
             "the goal is not an IFF")
            ((not (chk-arity? hyps 2)) "iff-intro takes exactly two hypotheses")
            ((not (and (chk-ctx+? (car hyps) concl (list (binary-left g)))
                       (chk-same? (chk-goal (car hyps)) (binary-right g))))
             "the first hypothesis is not  ctx, p => q")
            ((not (and (chk-ctx+? (cadr hyps) concl (list (binary-right g)))
                       (chk-same? (chk-goal (cadr hyps)) (binary-left g))))
             "the second hypothesis is not  ctx, q => p")
            (else #t)))))

;;; forall-intro: THE EIGENVARIABLE RULE.
;;;
;;; G is a chain of universals.  The hypothesis is the body of that chain at
;;; eigenvariables y_1 ... y_k, with every guard  (IN y_i A_i)  that the chain
;;; carried moved into the context and nothing else moved.  Each y_i must be a
;;; SYMBOL that is free neither in the context, nor in the formula still being
;;; generalised at that step, nor in a guard already collected -- which is the
;;; eigenvariable condition, and the only thing that makes the rule sound.
;;;
;;; The y_i are FOUND, never minted: the chain is stripped to a pattern with one
;;; hole per universal, the holes are filled by matching the pattern's guards
;;; against the formulas the context gained and its body against the hypothesis
;;; goal, and the forward walk then re-imposes the side condition at each step.
;;; k is taken as large as possible and then decremented, because a shorter
;;; chain is a sound inference too.
(define (chk-forall-strip g k)
  ;; Strip K leading universals, replacing each bound name by a fresh hole.
  ;; Returns (holes guard-patterns body-pattern) or #f.
  (let loop ((cur g) (i 0) (holes '()) (guards '()))
    (if (= i k)
        (list (reverse holes) (reverse guards) cur)
        (and (pair? cur) (eq? (car cur) 'FORALL) (= (length cur) 3)
             (let* ((x    (quantifier-var cur))
                    (hole (string->symbol
                           (string-append "chk-hole-" (number->string i))))
                    (body (subst-free x hole (quantifier-body cur))))
               (if (and (pair? body) (eq? (car body) 'IMPLIES) (= (length body) 3)
                        (pair? (binary-left body))
                        (eq? (car (binary-left body)) 'IN)
                        (= (length (binary-left body)) 3)
                        (eq? (cadr (binary-left body)) hole))
                   (loop (binary-right body) (+ i 1) (cons hole holes)
                         (cons (binary-left body) guards))
                   (loop body (+ i 1) (cons hole holes) guards)))))))

(define (chk-forall-depth g)
  (let loop ((cur g) (n 0))
    (if (and (pair? cur) (eq? (car cur) 'FORALL) (= (length cur) 3))
        (let ((body (quantifier-body cur)))
          (loop (if (and (pair? body) (eq? (car body) 'IMPLIES) (= (length body) 3)
                         (pair? (binary-left body))
                         (eq? (car (binary-left body)) 'IN)
                         (= (length (binary-left body)) 3)
                         (eq? (cadr (binary-left body)) (quantifier-var cur)))
                    (binary-right body)
                    body)
                (+ n 1)))
        n)))

;;; Fill the holes: the guards against DELTA (in order), then the body against
;;; the hypothesis goal.
(define (chk-forall-fill holes guards body-pat hyp-goal delta)
  (let loop ((gs guards) (left delta) (bnds '()))
    (if (null? gs)
        (let ((b (chk-match-ext holes body-pat hyp-goal bnds)))
          (and b (null? left) b))
        (let try ((cands left) (skipped '()))
          (and (pair? cands)
               (let ((b (chk-match-ext holes (car gs) (car cands) bnds)))
                 (if b
                     (or (loop (cdr gs) (append (reverse skipped) (cdr cands)) b)
                         (try (cdr cands) (cons (car cands) skipped)))
                     (try (cdr cands) (cons (car cands) skipped)))))))))

;;; The forward walk that re-imposes the eigenvariable condition.
(define (chk-forall-eigen-ok? g k ys ctx)
  (let ((ctx-fvs (chk-ctx-free-vars ctx)))
    (let loop ((cur g) (i 0) (avoid ctx-fvs) (guards '()))
      (if (= i k)
          (list cur (reverse guards))
          (and (pair? cur) (eq? (car cur) 'FORALL)
               (let ((y (list-ref ys i))
                     (x (quantifier-var cur)))
                 (and (symbol? y)
                      (not (memq y avoid))
                      (not (memq y (free-vars cur)))
                      (let ((body (subst-free x y (quantifier-body cur))))
                        (if (and (pair? body) (eq? (car body) 'IMPLIES)
                                 (= (length body) 3)
                                 (pair? (binary-left body))
                                 (eq? (car (binary-left body)) 'IN)
                                 (= (length (binary-left body)) 3)
                                 (eq? (cadr (binary-left body)) y))
                            (loop (binary-right body) (+ i 1)
                                  (append (free-vars (binary-left body)) avoid)
                                  (cons (binary-left body) guards))
                            ;; an UNGUARDED eigenvariable does not enter the
                            ;; context, so it is not added to AVOID (2026-09-24,
                            ;; item 4): a later y equal to it is refused by the
                            ;; free-in-CUR test above exactly when the body still
                            ;; mentions it.  Adding it refused the sound inference
                            ;; the kernel makes on  forall x. forall x. B, where
                            ;; the outer x is vacuous and `di' keeps x twice.
                            (loop body (+ i 1) avoid guards))))))))))

(define (chk-forall-intro-at g k hyp concl)
  (let ((strip (chk-forall-strip g k)))
    (and strip
         (let* ((holes  (car strip))
                (guards (cadr strip))
                (bodyp  (caddr strip))
                (delta  (chk-added hyp concl))
                (bnds   (chk-forall-fill holes guards bodyp (chk-goal hyp) delta)))
           (and bnds
                ;; a hole the pattern never reached is vacuous: name it after
                ;; the bound variable, which the forward walk then accepts.
                (let* ((ys (let fill ((hs holes) (i 0) (acc '()))
                             (if (null? hs)
                                 (reverse acc)
                                 (fill (cdr hs) (+ i 1)
                                       (cons (or (chk-bound (car hs) bnds)
                                                 (chk-vacuous-name g i))
                                             acc)))))
                       (fw (chk-forall-eigen-ok? g k ys (chk-asms concl))))
                  (and fw
                       (chk-same? (car fw) (chk-goal hyp))
                       (chk-ctx+? hyp concl (cadr fw)))))))))

;;; The bound name at depth I of a universal chain (the eigenvariable the
;;; kernel keeps when it does not clash), used only for a hole the match never
;;; reached -- a variable the body does not mention, where the rule is vacuous.
(define (chk-vacuous-name g i)
  (let loop ((cur g) (n 0))
    (cond ((not (and (pair? cur) (eq? (car cur) 'FORALL) (= (length cur) 3))) 'chk-vacuous)
          ((= n i) (quantifier-var cur))
          (else
           (let ((body (quantifier-body cur)))
             (loop (if (and (pair? body) (eq? (car body) 'IMPLIES) (= (length body) 3)
                            (pair? (binary-left body))
                            (eq? (car (binary-left body)) 'IN)
                            (= (length (binary-left body)) 3)
                            (eq? (cadr (binary-left body)) (quantifier-var cur)))
                       (binary-right body)
                       body)
                   (+ n 1)))))))

(register-rule-checker! 'forall-intro
  (lambda (rule hyps concl)
    (let ((g (chk-goal concl)))
      (cond
        ((not (and (pair? g) (eq? (car g) 'FORALL) (= (length g) 3)))
         "the goal is not a FORALL")
        ((not (chk-arity? hyps 1)) "forall-intro takes one hypothesis")
        ((not (chk-subset? (chk-asms concl) (chk-asms (car hyps))))
         "forall-intro may not DROP an assumption")
        (else
         (let ((hyp (car hyps)))
           (let loop ((k (chk-forall-depth g)))
             (cond ((< k 1)
                    "no eigenvariable reading of the hypothesis: it is not the body of the universal chain at variables fresh for the context")
                   ((chk-forall-intro-at g k hyp concl) #t)
                   (else (loop (- k 1)))))))))))

;;; forsome-intro: G = (FORSOME x p); one hypothesis, same context, whose goal
;;; is p[x := t] for SOME term t (found by matching).
(register-rule-checker! 'forsome-intro
  (lambda (rule hyps concl)
    (let ((g (chk-goal concl)))
      (cond
        ((not (and (pair? g) (eq? (car g) 'FORSOME) (= (length g) 3)))
         "the goal is not a FORSOME")
        ((not (chk-arity? hyps 1)) "forsome-intro takes one hypothesis")
        ((not (chk-ctx=? (car hyps) concl)) "the context changed")
        ((not (chk-match (list (quantifier-var g))
                         (quantifier-body g) (chk-goal (car hyps))))
         "the hypothesis goal is not an INSTANCE of the existential's body")
        (else #t)))))

;;; truth-intro: G = TRUTH; no hypotheses.  (Unreachable: no tactic calls it.)
(register-rule-checker! 'truth-intro
  (lambda (rule hyps concl)
    (cond ((not (eq? (chk-goal concl) 'TRUTH)) "the goal is not TRUTH")
          ((not (null? hyps)) "truth-intro takes no hypotheses")
          (else #t))))

;;; --- elimination rules on the CONTEXT ----------------------------------

;;; and-elim: some (AND p q) in the context is replaced by p and q.
(register-rule-checker! 'and-elim
  (lambda (rule hyps concl)
    (if (not (chk-arity? hyps 1))
        "and-elim takes one hypothesis"
        (let ((hyp (car hyps)))
          (if (not (chk-goal=? hyp concl))
              "and-elim may not change the goal"
              (if (chk-any
                   (lambda (f)
                     (and (pair? f) (eq? (car f) 'AND) (= (length f) 3)
                          (chk-ctx-+? hyp concl (list f)
                                      (list (binary-left f) (binary-right f)))))
                   (chk-asms concl))
                  #t
                  "no conjunction in the context was replaced by its two conjuncts"))))))

;;; or-elim: some (OR p q) in the context is replaced, in two branches, by p
;;; and by q; the goal is the same in both.
(register-rule-checker! 'or-elim
  (lambda (rule hyps concl)
    (if (not (chk-arity? hyps 2))
        "or-elim takes exactly two hypotheses"
        (let ((h1 (car hyps)) (h2 (cadr hyps)))
          (if (not (and (chk-goal=? h1 concl) (chk-goal=? h2 concl)))
              "or-elim may not change the goal"
              (if (chk-any
                   (lambda (f)
                     (and (pair? f) (eq? (car f) 'OR) (= (length f) 3)
                          (chk-ctx-+? h1 concl (list f) (list (binary-left f)))
                          (chk-ctx-+? h2 concl (list f) (list (binary-right f)))))
                   (chk-asms concl))
                  #t
                  "no disjunction in the context was split into its two branches"))))))

;;; not-elim: the context holds both (NOT p) and p, so it is contradictory and
;;; the goal is closed outright.  No hypotheses.
(register-rule-checker! 'not-elim
  (lambda (rule hyps concl)
    (let ((asms (chk-asms concl)))
      (cond ((not (null? hyps)) "not-elim takes no hypotheses")
            ((chk-any (lambda (f)
                        (and (pair? f) (eq? (car f) 'NOT) (= (length f) 2)
                             (chk-mem? (not-body f) asms)))
                      asms)
             #t)
            (else "the context holds no pair  p, NOT p")))))

;;; iff-elim: some (IFF p q) in the context is replaced by its two implications.
(register-rule-checker! 'iff-elim
  (lambda (rule hyps concl)
    (if (not (chk-arity? hyps 1))
        "iff-elim takes one hypothesis"
        (let ((hyp (car hyps)))
          (if (not (chk-goal=? hyp concl))
              "iff-elim may not change the goal"
              (if (chk-any
                   (lambda (f)
                     (and (pair? f) (eq? (car f) 'IFF) (= (length f) 3)
                          (chk-ctx-+? hyp concl (list f)
                                      (list (list 'IMPLIES (binary-left f) (binary-right f))
                                            (list 'IMPLIES (binary-right f) (binary-left f))))))
                   (chk-asms concl))
                  #t
                  "no biconditional in the context became its two implications"))))))

;;; forsome-elim: some (FORSOME x p) in the context is replaced by p[x := y]
;;; for an eigenvariable y free nowhere else -- not in the rest of the context,
;;; not in the goal, not in the existential itself.
(register-rule-checker! 'forsome-elim
  (lambda (rule hyps concl)
    (if (not (chk-arity? hyps 1))
        "forsome-elim takes one hypothesis"
        (let ((hyp (car hyps)))
          (if (not (chk-goal=? hyp concl))
              "forsome-elim may not change the goal"
              (let ((asms (chk-asms concl)))
                (if (chk-adds-nothing? hyp concl)
                    #t             ; the instance was already in the context
                (if (chk-any
                     (lambda (f)
                       (and (pair? f) (eq? (car f) 'FORSOME) (= (length f) 3)
                            (let* ((x    (quantifier-var f))
                                   (body (quantifier-body f))
                                   (rest (chk-minus asms (list f)))
                                   (delta (chk-added hyp concl)))
                              (chk-any
                               (lambda (inst)
                                 (let ((b (chk-match (list x) body inst)))
                                   (and b
                                        (let ((y (chk-bound x b)))
                                          (and (or (not y) (symbol? y))
                                               (or (not y)
                                                   (and (not (memq y (chk-ctx-free-vars rest)))
                                                        (not (memq y (free-vars (chk-goal concl))))
                                                        (not (memq y (free-vars f)))))
                                               (chk-ctx-+? hyp concl (list f) (list inst)))))))
                               delta))))
                     asms)
                    #t
                    "no existential in the context was opened at a fresh eigenvariable"))))))))

;;; forall-elim: some (FORALL x p) in the context yields p[x := t] for a term t
;;; (found by matching), which the context gains.
;;;
;;; THE DEFINEDNESS OBLIGATION (2026-09-24, gap 3).  LUTINS instantiation is
;;; forall x. p, t defined |- p[t].  The builder either posts the side sequent
;;; Gamma => t = t, or posts none because its certificate `pi--defined?'
;;; accepted t.  Until this date the checker accepted a side sequent  u = u  for
;;; ANY u, and accepted its absence unconditionally.  Now:
;;;   * the side sequent, when present, must be  t = t  for the t the conclusion
;;;     was instantiated at (read off by matching p against the instance);
;;;   * when absent, t must be certified by `chk-elim-certified?' below.
;;; When x does not occur in p the instance does not depend on t, and nothing is
;;; demanded of it (the class universe is nonempty).  When the instance was
;;; already in the context (`chk-adds-nothing?') the inference adds nothing and
;;; is accepted whatever the side sequent says.
(define (chk-elim-outside-binders? t e)
  ;; T occurs in E at a position no binder encloses.  Written here, not
  ;; borrowed: a functoid record counts as a binder throughout (conservative).
  (cond
    ((chk-same? e t) #t)
    ((functoid? e) #f)
    ((not (pair? e)) #f)
    ((not (list? e)) #f)
    ((memq (car e) '(FORALL FORSOME IOTA COMP)) #f)
    ((and (memq (car e) '(SEP BIG-UNION VNB-LAMBDA)) (= (length e) 4))
     (chk-elim-outside-binders? t (caddr e)))
    (else (chk-any (lambda (x) (chk-elim-outside-binders? t x)) e))))

(declare-binder-walker! 'chk-elim-outside-binders?
                        '(FORALL FORSOME IOTA COMP SEP BIG-UNION VNB-LAMBDA))

;;; Is T certified defined in the context of CONCL?  The cases, in order:
;;;   RE-DECIDED HERE, independently of the builder:
;;;   (a) T is an atom: a variable, an atomic constant or a numeral;
;;;   (b) the context holds  T in _,  T = _  or  _ = T  (typed or equated);
;;;   (c) T occurs outside every binder in an atomic hypothesis  IN, =, <=, <
;;;       (these relations are strict: an undefined argument makes them false).
;;;   ACCEPTED ON THE BUILDER'S WORD: every other case of the certificate --
;;;   ground arithmetic, total class constructors on certified arguments,
;;;   SEP / BIG-UNION / VNB-LAMBDA over a certified domain, COMP, NTH of a
;;;   literal LIST, arithmetic on number-typed arguments, LENGTH of a tuple-typed
;;;   term, accessors and applied operations of a structure in context, the
;;;   application of a context-typed function, functoid instances, and the
;;;   unfolding of predicate hypotheses.  For these the checker calls the
;;;   builder's own certificate `pi--defined?' (primitive-inferences.scm) on the
;;;   conclusion's context: it re-runs the decision rather than trusting that it
;;;   was made, so an instantiation that skipped it is still refused, but the
;;;   decision procedure itself is shared with the builder and is trusted.
(define (chk-elim-certified? concl t)
  (let ((asms (chk-asms concl)))
    (or (not (pair? t))                                          ; (a)
        (chk-any (lambda (f)                                     ; (b)
                   (and (pair? f) (= (length f) 3)
                        (or (and (eq? (car f) 'IN) (chk-same? (cadr f) t))
                            (and (eq? (car f) '=)
                                 (or (chk-same? (cadr f) t) (chk-same? (caddr f) t))))))
                 asms)
        (chk-any (lambda (f)                                     ; (c)
                   (and (pair? f) (memq (car f) '(IN = <= <)) (= (length f) 3)
                        (or (chk-elim-outside-binders? t (cadr f))
                            (chk-elim-outside-binders? t (caddr f)))))
                 asms)
        (and (pi--defined? (sequent-assumptions concl) t 0) #t))))  ; builder's word

(register-rule-checker! 'forall-elim
  (lambda (rule hyps concl)
    (cond
      ((not (or (chk-arity? hyps 1) (chk-arity? hyps 2)))
       "forall-elim takes one hypothesis, or two with the owed definedness sequent")
      ((not (chk-goal=? (car hyps) concl)) "forall-elim may not change the goal")
      ((and (chk-arity? hyps 2)
            (let ((side (chk-goal (cadr hyps))))
              (not (and (pair? side) (eq? (car side) '=) (= (length side) 3)
                        (chk-same? (binary-left side) (binary-right side))
                        (chk-ctx=? (cadr hyps) concl)))))
       "the second hypothesis is not the owed definedness sequent  Gamma => t = t")
      ((chk-adds-nothing? (car hyps) concl) #t)   ; the instance was already there
      (else
       (let* ((asms  (chk-asms concl))
              (hyp   (car hyps))
              (delta (chk-added hyp concl))
              (side  (and (chk-arity? hyps 2) (binary-left (chk-goal (cadr hyps)))))
              (instance-seen #f)
              (ok
               (chk-any
                (lambda (f)
                  (and (pair? f) (eq? (car f) 'FORALL) (= (length f) 3)
                       (chk-any
                        (lambda (inst)
                          (let ((b (chk-match (list (quantifier-var f))
                                              (quantifier-body f) inst)))
                            (and b
                                 (chk-ctx+? hyp concl (list inst))
                                 (begin (set! instance-seen #t) #t)
                                 (let ((t (chk-bound (quantifier-var f) b)))
                                   (or (not t)            ; x not in p: vacuous
                                       (if side
                                           (chk-same? side t)
                                           (chk-elim-certified? concl t)))))))
                        delta)))
                asms)))
         (cond
           (ok #t)
           ((not instance-seen)
            "the context gained no INSTANCE of any universal it holds")
           (side
            "the owed definedness sequent is not  t = t  for the term t the universal was instantiated at")
           (else
            "the instantiation term is not certified defined in the context, and no definedness sequent  t = t  is owed")))))))

;;; --- the discharging rules ---------------------------------------------

;;; assumption: the goal is TRUTH, or is in the context.  No hypotheses.
(register-rule-checker! 'assumption
  (lambda (rule hyps concl)
    (cond ((not (null? hyps)) "assumption takes no hypotheses")
          ((eq? (chk-goal concl) 'TRUTH) #t)
          ((chk-mem? (chk-goal concl) (chk-asms concl)) #t)
          (else "the goal is neither TRUTH nor an assumption of the context"))))

;;; theorem-assumption: the context gains the INSTALLED STATEMENT of some
;;; theorem (searched for in *theorem-table* by statement); the goal is
;;; unchanged.  This is the soundness boundary the kernel already guards by
;;; taking a NAME rather than a formula; the checker confirms the formula that
;;; arrived is one the table holds.
(register-rule-checker! 'theorem-assumption
  (lambda (rule hyps concl)
    (cond
      ((not (chk-arity? hyps 1)) "theorem-assumption takes one hypothesis")
      ((not (chk-goal=? (car hyps) concl)) "theorem-assumption may not change the goal")
      (else
       (let ((hyp (car hyps)))
         (if (chk-adds-nothing? hyp concl)
             #t                          ; the statement was already in the context
             (if (chk-any (lambda (f)
                            (and (chk-installed-theorem-name f)
                                 (chk-ctx+? hyp concl (list f))))
                          (chk-added hyp concl))
                 #t
                 "the formula the context gained is not the statement of any installed theorem")))))))

;;; cut: Gamma => L  and  Gamma, L => G.
(register-rule-checker! 'cut
  (lambda (rule hyps concl)
    (if (not (chk-arity? hyps 2))
        "cut takes exactly two hypotheses"
        (let* ((h1 (car hyps)) (h2 (cadr hyps)) (lemma (chk-goal h1)))
          (cond ((not (chk-ctx=? h1 concl))
                 "the lemma branch must run in the same context")
                ((not (chk-goal=? h2 concl)) "the main branch changed the goal")
                ((not (chk-ctx+? h2 concl (list lemma)))
                 "the main branch's context is not the old one plus the lemma")
                (else #t))))))

;;; weakening: the hypothesis context is INCLUDED in the conclusion's and the
;;; goal is the same.  Dropping assumptions is sound whatever is dropped.
(register-rule-checker! 'weakening
  (lambda (rule hyps concl)
    (cond ((not (chk-arity? hyps 1)) "weakening takes one hypothesis")
          ((not (chk-goal=? (car hyps) concl)) "weakening may not change the goal")
          ((not (chk-subset? (chk-asms (car hyps)) (chk-asms concl)))
           "weakening ADDED an assumption")
          (else #t))))

;;; detach: the context holds (IMPLIES p q) and p, and gains q.
(register-rule-checker! 'detach
  (lambda (rule hyps concl)
    (if (not (chk-arity? hyps 1))
        "detach takes one hypothesis"
        (let ((hyp (car hyps)) (asms (chk-asms concl)))
          (if (not (chk-goal=? hyp concl))
              "detach may not change the goal"
              (if (chk-any
                   (lambda (f)
                     (and (pair? f) (eq? (car f) 'IMPLIES) (= (length f) 3)
                          (chk-mem? (binary-left f) asms)
                          (chk-ctx+? hyp concl (list (binary-right f)))))
                   asms)
                  #t
                  "no context implication has its antecedent in the context and its consequent added"))))))

;;; backchain: the context holds (IMPLIES p G); the goal becomes p.
(register-rule-checker! 'backchain
  (lambda (rule hyps concl)
    (if (not (chk-arity? hyps 1))
        "backchain takes one hypothesis"
        (let ((hyp (car hyps)) (g (chk-goal concl)))
          (if (not (chk-ctx=? hyp concl))
              "backchain may not change the context"
              (if (chk-any
                   (lambda (f)
                     (and (pair? f) (eq? (car f) 'IMPLIES) (= (length f) 3)
                          (chk-same? (binary-right f) g)
                          (chk-same? (binary-left f) (chk-goal hyp))))
                   (chk-asms concl))
                  #t
                  "no context implication has the goal as its consequent and the hypothesis goal as its antecedent"))))))

;;; proof-by-contradiction: the context gains (NOT G) and the goal is FALSITY.
(register-rule-checker! 'proof-by-contradiction
  (lambda (rule hyps concl)
    (cond ((not (chk-arity? hyps 1)) "proof-by-contradiction takes one hypothesis")
          ((not (eq? (chk-goal (car hyps)) 'FALSITY))
           "the hypothesis goal must be FALSITY")
          ((not (chk-ctx+? (car hyps) concl (list (make-not (chk-goal concl)))))
           "the context must gain exactly the NEGATION of the goal")
          (else #t))))

;;; contraposition: the context holds (IMPLIES p q), the goal is (NOT p), and
;;; the hypothesis goal is (NOT q).  (Unreachable: pi-contraposit! has no caller.)
(register-rule-checker! 'contraposition
  (lambda (rule hyps concl)
    (let ((g (chk-goal concl)))
      (cond
        ((not (chk-arity? hyps 1)) "contraposition takes one hypothesis")
        ((not (and (pair? g) (eq? (car g) 'NOT) (= (length g) 2)))
         "the goal is not a NOT")
        ((not (chk-ctx=? (car hyps) concl)) "the context changed")
        ((chk-any (lambda (f)
                    (and (pair? f) (eq? (car f) 'IMPLIES) (= (length f) 3)
                         (chk-same? (binary-left f) (not-body g))
                         (chk-same? (chk-goal (car hyps))
                                    (make-not (binary-right f)))))
                  (chk-asms concl))
         #t)
        (else "no context implication has the negated goal as its antecedent")))))

;;; --- equality ----------------------------------------------------------

;;; eq-subst: the context holds s = t or s == t (in either orientation, under
;;; either head); the hypothesis goal is the goal with SOME occurrences of s
;;; replaced by t, and differs from it.
(register-rule-checker! 'eq-subst
  (lambda (rule hyps concl)
    (if (not (chk-arity? hyps 1))
        "eq-subst takes one hypothesis"
        (let* ((hyp (car hyps))
               (g   (chk-goal concl))
               (g2  (chk-goal hyp)))
          (cond
            ((not (chk-ctx=? hyp concl)) "eq-subst may not change the context")
            ((chk-same? g g2) "eq-subst changed nothing")
            ((chk-any
              (lambda (f)
                (and (pair? f) (memq (car f) '(= ==)) (= (length f) 3)
                     (or (chk-replaced? g g2 (binary-left f) (binary-right f))
                         (chk-replaced? g g2 (binary-right f) (binary-left f)))))
              (chk-asms concl))
             #t)
            (else "the new goal is not the old one rewritten by a context equation"))))))

;;; reflexivity: the goal is TRUTH, or (= u v) with u and v the same term.
;;; The DEFINEDNESS side condition is policy, not a rule of logic, and is not
;;; re-checked here (see the header).
(register-rule-checker! 'reflexivity
  (lambda (rule hyps concl)
    (let ((g (chk-goal concl)))
      (cond ((not (null? hyps)) "reflexivity takes no hypotheses")
            ((eq? g 'TRUTH) #t)
            ((and (pair? g) (eq? (car g) '=) (= (length g) 3)
                  (chk-same? (binary-left g) (binary-right g)))
             #t)
            (else "the goal is not  t = t  for one and the same t")))))

;;; quasi-reflexivity: the goal is (== u v) with u and v the same term.
(register-rule-checker! 'quasi-reflexivity
  (lambda (rule hyps concl)
    (let ((g (chk-goal concl)))
      (cond ((not (null? hyps)) "quasi-reflexivity takes no hypotheses")
            ((and (pair? g) (eq? (car g) '==) (= (length g) 3)
                  (chk-same? (binary-left g) (binary-right g)))
             #t)
            (else "the goal is not  t == t  for one and the same t")))))

;;; --- conditional terms -------------------------------------------------

;;; if-true:  branch 1 proves the condition p; branch 2 keeps the goal and
;;; gains the equation (= (IF p a b) a).  The IF term is read off that equation.
(define (chk-if-rule true?)
  (lambda (rule hyps concl)
    (if (not (chk-arity? hyps 2))
        "the IF rules take exactly two hypotheses"
        (let* ((h1 (car hyps)) (h2 (cadr hyps))
               (cond-goal (chk-goal h1)))
          (cond
            ((not (chk-ctx=? h1 concl)) "the condition branch changed the context")
            ((not (chk-goal=? h2 concl)) "the main branch changed the goal")
            ((and (not true?)
                  (not (and (pair? cond-goal) (eq? (car cond-goal) 'NOT)
                            (= (length cond-goal) 2))))
             "if-false must post the NEGATED condition")
            ((chk-adds-nothing? h2 concl) #t)  ; the equation was already there
            (else
             (let ((p (if true? cond-goal (not-body cond-goal))))
               (if (chk-any
                    (lambda (e)
                      (and (pair? e) (eq? (car e) '=) (= (length e) 3)
                           (let ((lhs (binary-left e)))
                             (and (pair? lhs) (eq? (car lhs) 'IF) (= (length lhs) 4)
                                  (chk-same? (cadr lhs) p)
                                  (chk-same? (binary-right e)
                                             (if true? (caddr lhs) (cadddr lhs)))
                                  (chk-ctx+? h2 concl (list e))))))
                    (chk-added h2 concl))
                   #t
                   "the main branch did not gain the IF equation for the branch proved"))))))))

(register-rule-checker! 'if-true  (chk-if-rule #t))
(register-rule-checker! 'if-false (chk-if-rule #f))

;;; --- the structure eliminators -----------------------------------------

;;; cartesian-intro: goal (IN (LIST e1..en) (CARTESIAN A1..An)); one hypothesis
;;; per component, same context, goal (IN e_i A_i).
(register-rule-checker! 'cartesian-intro
  (lambda (rule hyps concl)
    (let ((g (chk-goal concl)))
      (if (not (and (pair? g) (eq? (car g) 'IN) (= (length g) 3)
                    (pair? (cadr g)) (eq? (car (cadr g)) 'LIST)
                    (pair? (caddr g)) (eq? (car (caddr g)) 'CARTESIAN)))
          "the goal is not  [e1..en] in CARTESIAN(A1..An)"
          (let ((elems (cdr (cadr g))) (sets (cdr (caddr g))))
            (cond
              ((not (= (length elems) (length sets)))
               "the tuple and the product have different lengths")
              ((not (chk-arity? hyps (length elems)))
               "one hypothesis per component is required")
              ((not (chk-every2
                     (lambda (h pair)
                       (and (chk-ctx=? h concl)
                            (chk-same? (chk-goal h)
                                       (list 'IN (car pair) (cdr pair)))))
                     hyps (map cons elems sets)))
               "a hypothesis is not the membership of its component")
              (else #t)))))))

;;; cartesian-elim (k): the context holds [e1..en] in CARTESIAN(A1..An) and
;;; gains (IN e_k A_k); the membership itself stays.
(register-rule-checker! 'cartesian-elim
  (lambda (rule hyps concl)
    (if (not (and (pair? rule) (= (length rule) 2) (exact-integer? (cadr rule))))
        "the cartesian-elim tag must carry the index"
        (let ((k (cadr rule)))
          (if (not (chk-arity? hyps 1))
              "cartesian-elim takes one hypothesis"
              (let ((hyp (car hyps)))
                (if (not (chk-goal=? hyp concl))
                    "cartesian-elim may not change the goal"
                    (if (chk-any
                         (lambda (f)
                           (and (pair? f) (eq? (car f) 'IN) (= (length f) 3)
                                (pair? (cadr f)) (eq? (car (cadr f)) 'LIST)
                                (pair? (caddr f)) (eq? (car (caddr f)) 'CARTESIAN)
                                (let ((elems (cdr (cadr f))) (sets (cdr (caddr f))))
                                  (and (= (length elems) (length sets))
                                       (<= 1 k) (<= k (length elems))
                                       (chk-ctx+? hyp concl
                                                  (list (list 'IN
                                                              (list-ref elems (- k 1))
                                                              (list-ref sets (- k 1)))))))))
                         (chk-asms concl))
                        #t
                        "no CARTESIAN membership in the context yields the component added"))))))))

;;; tuples-intro: goal (IN (LIST e1..en) (TUPLES A)); one hypothesis (IN e_i A)
;;; per component (none at all for the empty tuple, which closes the node).
(register-rule-checker! 'tuples-intro
  (lambda (rule hyps concl)
    (let ((g (chk-goal concl)))
      (if (not (and (pair? g) (eq? (car g) 'IN) (= (length g) 3)
                    (pair? (cadr g)) (eq? (car (cadr g)) 'LIST)
                    (pair? (caddr g)) (eq? (car (caddr g)) 'TUPLES)
                    (= (length (caddr g)) 2)))
          "the goal is not  [e1..en] in TUPLES(A)"
          (let ((elems (cdr (cadr g))) (a (cadr (caddr g))))
            (cond
              ((not (chk-arity? hyps (length elems)))
               "one hypothesis per component is required")
              ((not (chk-every2 (lambda (h e)
                                  (and (chk-ctx=? h concl)
                                       (chk-same? (chk-goal h) (list 'IN e a))))
                                hyps elems))
               "a hypothesis is not the membership of its component in A")
              (else #t)))))))

;;; tuples-elim (k): the context holds [e1..en] in TUPLES(A) and gains
;;; (IN e_k A).
(register-rule-checker! 'tuples-elim
  (lambda (rule hyps concl)
    (if (not (and (pair? rule) (= (length rule) 2) (exact-integer? (cadr rule))))
        "the tuples-elim tag must carry the index"
        (let ((k (cadr rule)))
          (if (not (chk-arity? hyps 1))
              "tuples-elim takes one hypothesis"
              (let ((hyp (car hyps)))
                (if (not (chk-goal=? hyp concl))
                    "tuples-elim may not change the goal"
                    (if (chk-any
                         (lambda (f)
                           (and (pair? f) (eq? (car f) 'IN) (= (length f) 3)
                                (pair? (cadr f)) (eq? (car (cadr f)) 'LIST)
                                (pair? (caddr f)) (eq? (car (caddr f)) 'TUPLES)
                                (= (length (caddr f)) 2)
                                (let ((elems (cdr (cadr f))))
                                  (and (<= 1 k) (<= k (length elems))
                                       (chk-ctx+? hyp concl
                                                  (list (list 'IN (list-ref elems (- k 1))
                                                              (cadr (caddr f)))))))))
                         (chk-asms concl))
                        #t
                        "no TUPLES membership in the context yields the component added"))))))))

;;; union-intro (k): goal (IN x (UNION S1..Sn)); one hypothesis (IN x S_k).
(register-rule-checker! 'union-intro
  (lambda (rule hyps concl)
    (let ((g (chk-goal concl)))
      (cond
        ((not (and (pair? rule) (= (length rule) 2) (exact-integer? (cadr rule))))
         "the union-intro tag must carry the index")
        ((not (and (pair? g) (eq? (car g) 'IN) (= (length g) 3)
                   (pair? (caddr g)) (eq? (car (caddr g)) 'UNION)))
         "the goal is not a UNION membership")
        ((not (chk-arity? hyps 1)) "union-intro takes one hypothesis")
        (else
         (let ((k (cadr rule)) (sets (cdr (caddr g))))
           (cond ((not (and (<= 1 k) (<= k (length sets))))
                  "the index is out of range")
                 ((not (chk-ctx=? (car hyps) concl)) "the context changed")
                 ((not (chk-same? (chk-goal (car hyps))
                                  (list 'IN (cadr g) (list-ref sets (- k 1)))))
                  "the hypothesis is not membership in the k-th set")
                 (else #t))))))))

;;; union-elim: the context holds (IN x (UNION S1..Sn)); it is replaced, in one
;;; branch per set, by (IN x S_i); the goal is the same in every branch.
(register-rule-checker! 'union-elim
  (lambda (rule hyps concl)
    (if (chk-any
         (lambda (f)
           (and (pair? f) (eq? (car f) 'IN) (= (length f) 3)
                (pair? (caddr f)) (eq? (car (caddr f)) 'UNION)
                (let ((sets (cdr (caddr f))) (x (cadr f)))
                  (and (= (length hyps) (length sets))
                       (chk-every2
                        (lambda (h s)
                          (and (chk-goal=? h concl)
                               (chk-ctx-+? h concl (list f) (list (list 'IN x s)))))
                        hyps sets)))))
         (chk-asms concl))
        #t
        "no UNION membership in the context was split into one branch per set")))

;;; intersection-intro: goal (IN x (INTERSECTION S1..Sn)); one hypothesis
;;; (IN x S_i) per set.
(register-rule-checker! 'intersection-intro
  (lambda (rule hyps concl)
    (let ((g (chk-goal concl)))
      (if (not (and (pair? g) (eq? (car g) 'IN) (= (length g) 3)
                    (pair? (caddr g)) (eq? (car (caddr g)) 'INTERSECTION)))
          "the goal is not an INTERSECTION membership"
          (let ((sets (cdr (caddr g))) (x (cadr g)))
            (cond
              ((not (chk-arity? hyps (length sets)))
               "one hypothesis per set is required")
              ((not (chk-every2 (lambda (h s)
                                  (and (chk-ctx=? h concl)
                                       (chk-same? (chk-goal h) (list 'IN x s))))
                                hyps sets))
               "a hypothesis is not membership in its set")
              (else #t)))))))

;;; intersection-elim (k): the context holds (IN x (INTERSECTION S1..Sn)) and
;;; gains (IN x S_k).
(register-rule-checker! 'intersection-elim
  (lambda (rule hyps concl)
    (if (not (and (pair? rule) (= (length rule) 2) (exact-integer? (cadr rule))))
        "the intersection-elim tag must carry the index"
        (let ((k (cadr rule)))
          (if (not (chk-arity? hyps 1))
              "intersection-elim takes one hypothesis"
              (let ((hyp (car hyps)))
                (if (not (chk-goal=? hyp concl))
                    "intersection-elim may not change the goal"
                    (if (chk-any
                         (lambda (f)
                           (and (pair? f) (eq? (car f) 'IN) (= (length f) 3)
                                (pair? (caddr f)) (eq? (car (caddr f)) 'INTERSECTION)
                                (let ((sets (cdr (caddr f))))
                                  (and (<= 1 k) (<= k (length sets))
                                       (chk-ctx+? hyp concl
                                                  (list (list 'IN (cadr f)
                                                              (list-ref sets (- k 1)))))))))
                         (chk-asms concl))
                        #t
                        "no INTERSECTION membership in the context yields the component added"))))))))

;;; --- the reduction rules -----------------------------------------------
;;; Each is checked by CONTRACTING INDEPENDENTLY: the contraction is written
;;; here, in three lines, and the relation tested is that the new goal is the
;;; old one with some licensed redexes contracted.  Nothing of the kernel's
;;; reducer is called.

;;; nth-reduce: (NTH k (LIST a1..an)) -> a_k, anywhere in the goal.
(define (chk-nth-redex? e)
  (and (pair? e) (eq? (car e) 'NTH) (= (length e) 3)
       (exact-integer? (cadr e))
       (pair? (caddr e)) (eq? (car (caddr e)) 'LIST)
       (<= 1 (cadr e)) (<= (cadr e) (length (cdr (caddr e))))))

(define (chk-nth-contract e)
  (list-ref (cdr (caddr e)) (- (cadr e) 1)))

(register-rule-checker! 'nth-reduce
  (lambda (rule hyps concl)
    (cond ((not (chk-arity? hyps 1)) "nth-reduce takes one hypothesis")
          ((not (chk-ctx=? (car hyps) concl)) "nth-reduce may not change the context")
          ((chk-same? (chk-goal (car hyps)) (chk-goal concl)) "nth-reduce changed nothing")
          ((chk-contracts? (chk-goal concl) (chk-goal (car hyps))
                           chk-nth-redex? chk-nth-contract) #t)
          (else "the new goal is not the old one with NTH-of-a-literal-LIST redexes contracted"))))

;;; length-reduce: (LENGTH (LIST a1..an)) -> n, anywhere in the goal.
(define (chk-length-redex? e)
  (and (pair? e) (eq? (car e) 'LENGTH) (= (length e) 2)
       (pair? (cadr e)) (eq? (car (cadr e)) 'LIST)))

(define (chk-length-contract e) (length (cdr (cadr e))))

(register-rule-checker! 'length-reduce
  (lambda (rule hyps concl)
    (cond ((not (chk-arity? hyps 1)) "length-reduce takes one hypothesis")
          ((not (chk-ctx=? (car hyps) concl)) "length-reduce may not change the context")
          ((chk-same? (chk-goal (car hyps)) (chk-goal concl)) "length-reduce changed nothing")
          ((chk-contracts? (chk-goal concl) (chk-goal (car hyps))
                           chk-length-redex? chk-length-contract) #t)
          (else "the new goal is not the old one with LENGTH-of-a-literal-LIST redexes contracted"))))

;;; functoid-beta: (apply-functoid <lambdoid> v1..vn) -> body[x_i := v_i],
;;; a PARALLEL substitution, anywhere in the goal.
(define (chk-functoid-redex? e)
  (and (pair? e) (eq? (car e) 'apply-functoid) (>= (length e) 3)
       (functoid? (cadr e))
       (= (length (functoid-bindings (cadr e))) (length (cddr e)))))

(define (chk-functoid-contract e)
  (let ((ftd (cadr e)))
    (subst-free* (map cons (map car (functoid-bindings ftd)) (cddr e))
                 (functoid-body ftd))))

(register-rule-checker! 'functoid-beta
  (lambda (rule hyps concl)
    (cond ((not (chk-arity? hyps 1)) "functoid-beta takes one hypothesis")
          ((not (chk-ctx=? (car hyps) concl)) "functoid-beta may not change the context")
          ((chk-same? (chk-goal (car hyps)) (chk-goal concl)) "functoid-beta changed nothing")
          ((chk-contracts? (chk-goal concl) (chk-goal (car hyps))
                           chk-functoid-redex? chk-functoid-contract) #t)
          (else "the new goal is not the old one with functoid applications contracted"))))

;;; --- the induction schemata --------------------------------------------
;;; These have no choices to make: the hypothesis goals ARE the two (or three)
;;; instances of the schema, and the checker states them from the expression
;;; layer and compares.

;;; nn-induction: goal (FORALL n (IMPLIES (IN n NN) body));
;;;   base  body[n := 0]
;;;   step  (FORALL n (IMPLIES (IN n NN) (IMPLIES body body[n := (succ n)])))
(register-rule-checker! 'nn-induction
  (lambda (rule hyps concl)
    (let ((g (chk-goal concl)))
      (if (not (and (pair? g) (eq? (car g) 'FORALL) (= (length g) 3)
                    (let ((b (quantifier-body g)))
                      (and (pair? b) (eq? (car b) 'IMPLIES) (= (length b) 3)
                           (equal? (binary-left b)
                                   (list 'IN (quantifier-var g) 'NN))))))
          "the goal is not  forall n in NN. body  with n outermost"
          (let* ((n     (quantifier-var g))
                 (inner (binary-right (quantifier-body g)))
                 (base  (subst-free n 0 inner))
                 (step  (list 'FORALL n
                              (list 'IMPLIES (list 'IN n 'NN)
                                    (list 'IMPLIES inner
                                          (subst-free n (list 'succ n) inner))))))
            (cond
              ((not (chk-arity? hyps 2)) "nn-induction takes exactly two hypotheses")
              ((not (and (chk-ctx=? (car hyps) concl) (chk-ctx=? (cadr hyps) concl)))
               "nn-induction may not change the context")
              ((not (chk-same? (chk-goal (car hyps)) base))
               "the first hypothesis is not the BASE case body[n := 0]")
              ((not (chk-same? (chk-goal (cadr hyps)) step))
               "the second hypothesis is not the STEP case")
              (else #t)))))))

;;; The induction hypothesis shared by the two transfinite schemata:
;;;   (FORALL b (IMPLIES (ORD-LT b var) P[var := b]))
;;; B is read off the hypothesis the kernel produced, never minted, and must be
;;; a variable that captures nothing: distinct from VAR and not free in P, in
;;; the goal or in the context.
(define (chk-tfi-beta hypg)
  ;; the bound variable of the IH inside a transfinite-induction hypothesis
  (and (pair? hypg) (eq? (car hypg) 'FORALL) (= (length hypg) 3)
       (let ((b (quantifier-body hypg)))
         (and (pair? b) (eq? (car b) 'IMPLIES) (= (length b) 3)
              (let ((ante (binary-left b)))
                (and (pair? ante) (eq? (car ante) 'AND) (= (length ante) 3)
                     (let ((ih (binary-right ante)))
                       (and (pair? ih) (eq? (car ih) 'FORALL) (= (length ih) 3)
                            (quantifier-var ih)))))))))

(define (chk-tfi-goal-parts g)
  ;; (var . P) for a goal  forall var in ORD. P
  (and (pair? g) (eq? (car g) 'FORALL) (= (length g) 3)
       (let ((b (quantifier-body g)))
         (and (pair? b) (eq? (car b) 'IMPLIES) (= (length b) 3)
              (equal? (binary-left b) (list 'IN (quantifier-var g) 'ORD))
              (cons (quantifier-var g) (binary-right b))))))

(define (chk-tfi-beta-ok? beta var p concl)
  (and (symbol? beta)
       (not (eq? beta var))
       (not (memq beta (free-vars p)))
       (not (memq beta (chk-ctx-free-vars (chk-asms concl))))))

(register-rule-checker! 'transfinite-induction
  (lambda (rule hyps concl)
    (let ((parts (chk-tfi-goal-parts (chk-goal concl))))
      (cond
        ((not parts) "the goal is not  forall var in ORD. P  with var outermost")
        ((not (chk-arity? hyps 1)) "transfinite-induction takes one hypothesis")
        ((not (chk-ctx=? (car hyps) concl)) "the context changed")
        (else
         (let* ((var  (car parts))
                (p    (cdr parts))
                (beta (chk-tfi-beta (chk-goal (car hyps)))))
           (cond
             ((not beta) "the hypothesis does not carry an induction hypothesis")
             ((not (chk-tfi-beta-ok? beta var p concl))
              "the induction variable is not fresh for P and the context")
             ((not (chk-same?
                    (chk-goal (car hyps))
                    (list 'FORALL var
                          (list 'IMPLIES
                                (list 'AND (list 'IN var 'ORD)
                                      (list 'FORALL beta
                                            (list 'IMPLIES (list 'ORD-LT beta var)
                                                  (subst-free var beta p))))
                                p))))
              "the hypothesis is not the strong-induction step for this goal")
             (else #t))))))))

(register-rule-checker! 'transfinite-induction-3cases
  (lambda (rule hyps concl)
    (let ((parts (chk-tfi-goal-parts (chk-goal concl))))
      (cond
        ((not parts) "the goal is not  forall var in ORD. P  with var outermost")
        ((not (chk-arity? hyps 3))
         "transfinite-induction-3cases takes exactly three hypotheses")
        ((not (chk-every (lambda (h) (chk-ctx=? h concl)) hyps))
         "the context changed")
        (else
         (let* ((var  (car parts))
                (p    (cdr parts))
                (beta (chk-tfi-beta (chk-goal (caddr hyps)))))
           (cond
             ((not beta) "the limit case carries no induction hypothesis")
             ((not (chk-tfi-beta-ok? beta var p concl))
              "the induction variable is not fresh for P and the context")
             ((not (chk-same? (chk-goal (car hyps)) (subst-free var 0 p)))
              "the first hypothesis is not the BASE case P[var := 0]")
             ((not (chk-same?
                    (chk-goal (cadr hyps))
                    (list 'FORALL var
                          (list 'IMPLIES (list 'AND (list 'IN var 'ORD) p)
                                (subst-free var (list 'succ_ORD var) p)))))
              "the second hypothesis is not the SUCCESSOR case")
             ((not (chk-same?
                    (chk-goal (caddr hyps))
                    (list 'FORALL var
                          (list 'IMPLIES
                                (list 'AND (list 'LIMIT-ORD var)
                                      (list 'FORALL beta
                                            (list 'IMPLIES (list 'ORD-LT beta var)
                                                  (subst-free var beta p))))
                                p))))
              "the third hypothesis is not the LIMIT case")
             (else #t))))))))

;;; =======================================================================
;;; ARMING
;;;
;;; Called by load.scm after the last checker file and before the first proof,
;;; and by a probe through the shim.  Every head in TRUSTED-HEADS that has no
;;; checker of its own is registered as ACCEPTED ON TRUST and LISTED, so the
;;; switch can already be on while a group of checkers is still being written.
;;; A silent acceptance would be worse than no check at all.
;;;
;;; The list is passed IN rather than read off *kernel-rule-tags*, because
;;; tactics-help.scm (where that table lives) loads two thousand lines of
;;; load.scm later than the arming, long after the first proof.  On a BAND,
;;; where everything is loaded, `dg-check-arm!' reads the table directly.

(define *dg-trusted-rule-heads* '())

(define (trusted-rule-heads) *dg-trusted-rule-heads*)

(define (dg-check-arm!)
  (dg-check-arm-with! (map car *kernel-rule-tags*)))

(define (dg-check-arm-with! trusted-heads)
  (set! *dg-trusted-rule-heads* '())
  (for-each
   (lambda (tag)
     (if (not (rule-checker-for tag))
         (begin
           (set! *dg-trusted-rule-heads* (cons tag *dg-trusted-rule-heads*))
           (register-rule-checker! tag (lambda (rule hyps concl) #t)))))
   trusted-heads)
  (set! *dg-trusted-rule-heads* (reverse *dg-trusted-rule-heads*))
  (set! *dg-check-inferences?* #t)
  (display ";VNB inference checking: ON, ")
  (display (- (length (registered-rule-checkers))
              (length *dg-trusted-rule-heads*)))
  (display " rule(s) checked")
  (if (null? *dg-trusted-rule-heads*)
      (display ", none accepted on trust.")
      (begin
        (display ", ACCEPTED ON TRUST:")
        (for-each (lambda (t) (display " ") (display t)) *dg-trusted-rule-heads*)
        (display ".")))
  (newline))

(define (dg-check-report!)
  (display ";VNB inference checking: ")
  (display *dg-checked-count*)
  (display " inference(s) verified.")
  (newline)
  *dg-checked-count*)
