;;; primitive-inferences.scm -- the primitive inference kernel
;;;
;;; Each primitive inference takes a sequent node and zero or more extra
;;; arguments.  It either succeeds (posting new subgoal nodes and recording
;;; the inference) or returns #f (failure).
;;;
;;; Sequent assumptions are lists of <wff>; the assertion is a <wff>.
;;; Raw S-expression work is done on wff-formula extracts; results are
;;; re-wrapped with wff-child (inheriting theory from the parent wff).
;;;
;;; Formula arguments from the user (cmd-* layer) are raw S-expressions;
;;; lookups in assumptions compare against wff-formula of each entry.

;;; -----------------------------------------------------------------------
;;; Helper: get the graph from a sequent node

(define (sqn-dg sqn) (sequent-node-graph sqn))

;;; -----------------------------------------------------------------------
;;; Helper: find a wff in assumptions by raw-formula alpha-equivalence

(define (asms-find asms raw-formula)
  (let ((normalized (expand-destructuring-quantifiers raw-formula)))
    (find-first (lambda (a) (alpha-equiv? (wff-formula a) normalized)) asms)))

;;; -----------------------------------------------------------------------
;;; Helper: peel a leading chain of FORALL quantifiers (pure raw S-exprs).
;;;
;;; Returns (cons new-raw-goal list-of-newly-added-raw-bounds).
;;; For each FORALL in the chain:
;;;   - Introduces a fresh variable y for the bound variable x.
;;;   - If the substituted body is (IMPLIES (IN y A) inner), records
;;;     (IN y A) as a new bound and continues peeling inner.
;;;   - Otherwise (unbounded) just continues peeling the substituted body.
;;; Stops at the first non-FORALL head.

;;; ambient-avoids is a list of expressions whose free variables the
;;; eigenvariable y must NOT collide with -- typically the sequent's
;;; assumptions and goal.  Previously chosen y's accumulate in `added`
;;; and are also avoided so successive peels never reuse a name.
(define (peel-foralls-raw raw-goal added ambient-avoids)
  (if (and (pair? raw-goal) (eq? (car raw-goal) 'FORALL))
      (let* ((x     (quantifier-var raw-goal))
             (body  (quantifier-body raw-goal))
             ;; Keep the bound name x as the eigenvariable when that is sound,
             ;; instead of always minting x_<n>.  The only side condition for
             ;; forall-intro is that the eigenvariable not already be free in
             ;; the context -- here the assumptions/goal (ambient-avoids) or an
             ;; eigenvariable already introduced earlier in this same di
             ;; (added).  y=x is an IDENTITY substitution on body, so it can
             ;; never capture there; we therefore check x only against that
             ;; context, NOT against body (where x is of course free).  Only
             ;; when x genuinely clashes do we fall back to a fresh x_<n>.
             ;; This keeps variable names stable and predictable across di
             ;; (no gratuitous gensym drift) in the common no-conflict case.
             (avoids (append added ambient-avoids))
             (y     (if (memq x (apply append (map free-vars avoids)))
                        (apply fresh-var x body raw-goal avoids)
                        x))
             (body* (subst-free x y body)))
        (if (and (pair? body*)
                 (eq? (car body*) 'IMPLIES)
                 (pair? (binary-left body*))
                 (eq? (car (binary-left body*)) 'IN)
                 (eq? (cadr (binary-left body*)) y))
            (peel-foralls-raw (binary-right body*)
                              (cons (binary-left body*) added)
                              ambient-avoids)
            (peel-foralls-raw body* added ambient-avoids)))
      (cons raw-goal added)))

;;; -----------------------------------------------------------------------
;;; DIRECT INFERENCE

(define (pi-direct-inference! sqn)
  (let* ((asms  (sequent-node-assumptions sqn))
         (goal  (sequent-node-assertion   sqn))
         (g     (wff-formula goal))
         (dg    (sqn-dg sqn)))
    (and (pair? g)
         (case (car g)

           ((AND)
            (dg-apply-rule! dg 'and-intro
              (list (make-sequent asms (wff-child goal (binary-left  g)))
                    (make-sequent asms (wff-child goal (binary-right g))))
              sqn))

           ((IMPLIES)
            (let ((p (binary-left g)) (q (binary-right g)))
              (dg-apply-rule! dg 'implies-intro
                (list (make-sequent (context-add-assumption asms (wff-child goal p))
                                    (wff-child goal q)))
                sqn)))

           ((IFF)
            (let ((p (binary-left g)) (q (binary-right g)))
              (dg-apply-rule! dg 'iff-intro
                (list (make-sequent (context-add-assumption asms (wff-child goal p))
                                    (wff-child goal q))
                      (make-sequent (context-add-assumption asms (wff-child goal q))
                                    (wff-child goal p)))
                sqn)))

           ((NOT)
            (let ((p (not-body g)))
              (dg-apply-rule! dg 'not-intro
                (list (make-sequent (context-add-assumption asms (wff-child goal p))
                                    (wff-child goal 'FALSITY)))
                sqn)))

           ((FORALL)
            ;; Eigenvariable y must avoid free vars of all asms (in addition
            ;; to the body, accumulated bounds — handled inside peel-foralls).
            (let* ((ambient   (map wff-formula asms))
                   (r         (peel-foralls-raw g '() ambient))
                   (new-g     (car r))
                   (new-bounds (cdr r))
                   (new-asms  (fold-left (lambda (acc raw-b)
                                           (context-add-assumption acc (wff-child goal raw-b)))
                                         asms
                                         new-bounds)))
              (dg-apply-rule! dg 'forall-intro
                (list (make-sequent new-asms (wff-child goal new-g)))
                sqn)))

           (else #f)))))

;;; -----------------------------------------------------------------------
;;; ANTECEDENT INFERENCE

(define (pi-antecedent-inference! sqn formula)
  ;; formula: raw S-expression identifying the assumption to decompose
  (let* ((asms  (sequent-node-assumptions sqn))
         (goal  (sequent-node-assertion   sqn))
         (dg    (sqn-dg sqn))
         (f     (asms-find asms formula)))
    (and f
         (let ((raw-f (wff-formula f)))
           (and (pair? raw-f)
                (case (car raw-f)

                  ((AND)
                   (let ((p (binary-left raw-f)) (q (binary-right raw-f)))
                     (dg-apply-rule! dg 'and-elim
                       (list (make-sequent
                              (context-add-assumption
                               (context-add-assumption
                                (context-remove-assumption asms f)
                                (wff-child f p))
                               (wff-child f q))
                              goal))
                       sqn)))

                  ((OR)
                   (let ((p (binary-left raw-f)) (q (binary-right raw-f))
                         (asms* (context-remove-assumption asms f)))
                     (dg-apply-rule! dg 'or-elim
                       (list (make-sequent (context-add-assumption asms* (wff-child f p)) goal)
                             (make-sequent (context-add-assumption asms* (wff-child f q)) goal))
                       sqn)))

                  ((NOT)
                   (let ((p (not-body raw-f)))
                     (if (context-contains? asms (wff-child f p))
                         (dg-apply-rule! dg 'not-elim '() sqn)
                         #f)))

                  ((FORSOME)
                   ;; Eigenvariable y must avoid free vars of OTHER assumptions
                   ;; and the goal -- otherwise it can collide with a name
                   ;; already in scope and let the user discharge against it.
                   (let* ((x    (quantifier-var  raw-f))
                          (body (quantifier-body raw-f))
                          (asms* (context-remove-assumption asms f))
                          (avoids (cons (wff-formula goal)
                                        (map wff-formula asms*)))
                          (y    (apply fresh-var x body avoids))
                          (inst (subst-free x y body)))
                     (dg-apply-rule! dg 'forsome-elim
                       (list (make-sequent (context-add-assumption asms* (wff-child f inst))
                                           goal))
                       sqn)))

                  ;; IFF-ELIM: from P <-> Q infer both directions.  The
                  ;; hypothesis dual of di's iff-intro on a goal.  Replaces
                  ;; the iff by (IMPLIES P Q) and (IMPLIES Q P), which lets a
                  ;; biconditional assumption (e.g. a conditional iff landed by
                  ;; `fact') be consumed by detach/backchain.  Sound: P<->Q
                  ;; entails (P=>Q) and (Q=>P).
                  ((IFF)
                   (let ((p (binary-left raw-f)) (q (binary-right raw-f)))
                     (dg-apply-rule! dg 'iff-elim
                       (list (make-sequent
                              (context-add-assumption
                               (context-add-assumption
                                (context-remove-assumption asms f)
                                (wff-child f (list 'IMPLIES p q)))
                               (wff-child f (list 'IMPLIES q p)))
                              goal))
                       sqn)))

                  (else #f)))))))

;;; -----------------------------------------------------------------------
;;; WEAKENING

(define (pi-weaken! sqn formula)
  ;; formula: raw S-expression
  (let* ((asms (sequent-node-assumptions sqn))
         (goal (sequent-node-assertion   sqn))
         (dg   (sqn-dg sqn))
         (f    (asms-find asms formula)))
    (if f
        (dg-apply-rule! dg 'weakening
          (list (make-sequent (context-remove-assumption asms f) goal))
          sqn)
        #f)))

;;; -----------------------------------------------------------------------
;;; CUT (lemma introduction)

(define (pi-cut! sqn lemma)
  ;; lemma: raw S-expression -- validate before wrapping so a malformed
  ;; lemma is rejected at the kernel boundary (was previously accepted and
  ;; would surface as confusing errors deep inside subsequent rules).
  (validate-wff! lemma)
  (let* ((asms      (sequent-node-assumptions sqn))
         (goal      (sequent-node-assertion   sqn))
         (dg        (sqn-dg sqn))
         (lemma-wff (wff-child goal lemma)))
    (dg-apply-rule! dg 'cut
      (list (make-sequent asms lemma-wff)
            (make-sequent (context-add-assumption asms lemma-wff) goal))
      sqn)))

;;; -----------------------------------------------------------------------
;;; UNIVERSAL INSTANTIATION

;;; DEFINEDNESS AUDIT (2026-09-18, measurement only, no rule changes).  LUTINS
;;; universal instantiation is  forall x. p,  t defined  |-  p[t]; VNB's
;;; forall-elim below takes the term with NO definedness obligation, so
;;; (forall a. a = a) instantiated at recip(0) closes recip(0) = recip(0)
;;; (rake batch P's finding).  Before changing the rule, COUNT: every
;;; instantiation whose term is neither syntactically defined
;;; (term-self-defined?) nor certified by a context assumption
;;; (asm-establishes-defined?) is tallied by head under *def-audit-hits*.
;;; load.scm prints the tally at the end when VNB_DEF_AUDIT is set.
(define *def-audit-hits*  (make-equal-hash-table))   ; head -> count
;;; The side sequents forall-elim OWES, newest first (a bounded list): the
;;; surface hook (interactive.scm vnb--run!) discharges exactly these and never
;;; a `(= t t)' goal a driver posted itself.
(define *pi-owed-nodes* '())
(define (pi--note-owed! nodes)
  (if (and (pair? nodes) (pair? (cdr nodes)))
      (set! *pi-owed-nodes*
            (let ((l (cons (cadr nodes) *pi-owed-nodes*)))
              (if (> (length l) 400) (list-head l 400) l))))
  nodes)
(define *def-audit-total* 0)
(define *def-audit-uncert* 0)
(define *def-audit-terms* '())
(define (def-audit-note! asms term)
  ;; Returns #t when the instantiation OWES the side sequent (= term term)
  ;; (LUTINS forall-elim, 2026-09-18): neither the syntactic test nor the
  ;; context certifies the term.  Also tallies, for VNB_DEF_AUDIT.
  (set! *def-audit-total* (+ *def-audit-total* 1))
  (if (pi--defined? asms term 0)
      #f
      (let ((k (if (pair? term) (car term) 'ATOM)))
        (set! *def-audit-uncert* (+ *def-audit-uncert* 1))
        (set! *def-audit-terms*
              (cons (cons term (map (lambda (a) (let ((f (wff-formula a)))
                                                  (if (pair? f) (car f) f)))
                                    asms))
                    *def-audit-terms*))
        (hash-table-set! *def-audit-hits* k
          (+ 1 (hash-table-ref/default *def-audit-hits* k 0)))
        #t)))


(define (pi-instantiate! sqn forall-formula term)
  ;; forall-formula: raw S-expression
  (let* ((asms (sequent-node-assumptions sqn))
         (goal (sequent-node-assertion   sqn))
         (dg   (sqn-dg sqn))
         (f    (asms-find asms forall-formula)))
    (and f
         (let ((raw-f (wff-formula f)))
           (and (pair? raw-f) (eq? (car raw-f) 'FORALL)
                (let* ((x    (quantifier-var  raw-f))
                       (body (quantifier-body raw-f))
                       (inst (subst-free x term body)))
                  ;; Re-validate the substituted body: catches the case where
                  ;; `term` is malformed and would yield a junk new wff.
                  (validate-wff! inst)
                  ;; LUTINS universal instantiation (2026-09-18):  forall x. p,
                  ;; t defined  |-  p[t].  When the context does not certify the
                  ;; term, the rule OWES the side sequent (= t t); the main
                  ;; child comes first, as lambda-beta posts its obligations.
                  (pi--note-owed!
                   (dg-apply-rule! dg 'forall-elim
                     (cons (make-sequent (context-add-assumption asms (wff-child f inst)) goal)
                           (if (def-audit-note! asms term)
                               (list (make-sequent asms (wff-child goal (list '= term term))))
                               '()))
                     sqn))))))))

;;; pi-spec!: instantiate a registered theorem THM-NAME at TERMS (positionally,
;;; one per leading FORALL), landing the fully-instantiated body as an
;;; assumption.  It chains theorem-assumption + forall-elim over the LIVE wff
;;; OBJECTS it builds rather than re-finding each intermediate via asms-find/
;;; alpha-equiv?.  subst-free is capture-avoiding, so a term that mentions the
;;; theorem's own bound-variable names is handled (the binders get renamed; the
;;; terms still apply positionally).  NB: asms-find/alpha-equiv? DO handle
;;; VNB-LAMBDA-bearing formulas (tested), and (fact ...) instantiates such
;;; theorems correctly too -- this is a more direct mechanism, not a fix for a
;;; defect in the alpha-equivalence path.
(define (pi-spec! sqn thm-name terms)
  (let ((S (hash-table-ref/default *theorem-table* thm-name #f)))
    (and S
      (let* ((goal  (sequent-node-assertion sqn))
             (dg    (sqn-dg sqn))
             (S-wff (wff-child goal S))
             (sqn1  (car (dg-apply-rule! dg 'theorem-assumption
                          (list (make-sequent
                                 (context-add-assumption (sequent-node-assumptions sqn) S-wff)
                                 goal))
                          sqn))))
        (let loop ((cur sqn1) (uwff S-wff) (ts terms))
          (if (null? ts)
              (list cur)
              (let ((raw (wff-formula uwff)))
                (if (and (pair? raw) (eq? (car raw) 'FORALL))
                    (let* ((x     (quantifier-var  raw))
                           (body  (quantifier-body raw))
                           (inst  (subst-free x (car ts) body))
                           (child (wff-child uwff inst)))
                      (validate-wff! inst)
                      ;; the same owed side sequent as pi-instantiate! (2026-09-18)
                      (loop (car (pi--note-owed!
                                  (dg-apply-rule! dg 'forall-elim
                                   (cons (make-sequent
                                          (context-add-assumption (sequent-node-assumptions cur) child)
                                          goal)
                                         (if (def-audit-note! (sequent-node-assumptions cur) (car ts))
                                             (list (make-sequent (sequent-node-assumptions cur)
                                                                 (wff-child goal (list '= (car ts) (car ts)))))
                                             '()))
                                   cur)))
                            child (cdr ts)))
                    (error "spec: more terms than leading universals in" thm-name)))))))))

;;; -----------------------------------------------------------------------
;;; EXISTENTIAL INTRODUCTION

(define (pi-exists-witness! sqn term)
  (let* ((asms (sequent-node-assumptions sqn))
         (goal (sequent-node-assertion   sqn))
         (g    (wff-formula goal))
         (dg   (sqn-dg sqn)))
    (and (pair? g) (eq? (car g) 'FORSOME)
         (let* ((x    (quantifier-var  g))
                (body (quantifier-body g))
                (sub  (subst-free x term body)))
           (validate-wff! sub)  ; reject malformed witness terms early
           (dg-apply-rule! dg 'forsome-intro
             (list (make-sequent asms (wff-child goal sub)))
             sqn)))))

;;; -----------------------------------------------------------------------
;;; ASSUMPTION (axiom discharge)

(define (pi-assumption! sqn)
  (let* ((asms (sequent-node-assumptions sqn))
         (goal (sequent-node-assertion   sqn))
         (g    (wff-formula goal))
         (dg   (sqn-dg sqn)))
    (if (or (eq? g 'TRUTH)
            (context-contains? asms goal))
        (dg-apply-rule! dg 'assumption '() sqn)
        #f)))

;;; -----------------------------------------------------------------------
;;; OR INTRODUCTION

(define (pi-or-intro-left! sqn)
  (let* ((asms (sequent-node-assumptions sqn))
         (goal (sequent-node-assertion   sqn))
         (g    (wff-formula goal))
         (dg   (sqn-dg sqn)))
    (and (pair? g) (eq? (car g) 'OR)
         (dg-apply-rule! dg 'or-intro-left
           (list (make-sequent asms (wff-child goal (binary-left g))))
           sqn))))

(define (pi-or-intro-right! sqn)
  (let* ((asms (sequent-node-assumptions sqn))
         (goal (sequent-node-assertion   sqn))
         (g    (wff-formula goal))
         (dg   (sqn-dg sqn)))
    (and (pair? g) (eq? (car g) 'OR)
         (dg-apply-rule! dg 'or-intro-right
           (list (make-sequent asms (wff-child goal (binary-right g))))
           sqn))))

;;; TRUTH introduction

(define (pi-truth! sqn)
  (let ((goal (sequent-node-assertion sqn))
        (dg   (sqn-dg sqn)))
    (if (eq? (wff-formula goal) 'TRUTH)
        (dg-apply-rule! dg 'truth-intro '() sqn)
        #f)))

;;; -----------------------------------------------------------------------
;;; BACKCHAIN

(define (pi-backchain! sqn implies-formula)
  ;; implies-formula: raw S-expression
  (let* ((asms (sequent-node-assumptions sqn))
         (goal (sequent-node-assertion   sqn))
         (g    (wff-formula goal))
         (dg   (sqn-dg sqn))
         (f    (asms-find asms implies-formula)))
    (and f
         (let ((raw-f (wff-formula f)))
           (and (pair? raw-f) (eq? (car raw-f) 'IMPLIES)
                (alpha-equiv? (binary-right raw-f) g)
                (dg-apply-rule! dg 'backchain
                  (list (make-sequent asms (wff-child f (binary-left raw-f))))
                  sqn))))))

;;; -----------------------------------------------------------------------
;;; DETACH  (forward modus ponens)
;;;
;;; From an in-context (IMPLIES A B) whose antecedent A is ALSO in context,
;;; add B to the context.  Sound: A and A=>B entail B, so the new assumption
;;; is derivable and adding it preserves the sequent's validity.  The forward
;;; dual of BACKCHAIN -- it grows the CONTEXT (forward) rather than the goal
;;; (backward), which is what assembling from `IS-X(s) => law' theorems needs.
(define (pi-detach! sqn implies-formula)
  ;; implies-formula: raw S-expression of the in-context implication
  (let* ((asms (sequent-node-assumptions sqn))
         (goal (sequent-node-assertion   sqn))
         (dg   (sqn-dg sqn))
         (f    (asms-find asms implies-formula)))
    (and f
         (let ((raw-f (wff-formula f)))
           (and (pair? raw-f) (eq? (car raw-f) 'IMPLIES)
                (context-contains? asms (wff-child f (binary-left raw-f)))
                (dg-apply-rule! dg 'detach
                  (list (make-sequent
                         (context-add-assumption asms (wff-child f (binary-right raw-f)))
                         goal))
                  sqn))))))

;;; -----------------------------------------------------------------------
;;; CONTRAPOSITION

(define (pi-contraposit! sqn implies-formula)
  ;; implies-formula: raw S-expression
  (let* ((asms (sequent-node-assumptions sqn))
         (goal (sequent-node-assertion   sqn))
         (g    (wff-formula goal))
         (dg   (sqn-dg sqn))
         (f    (asms-find asms implies-formula)))
    (and f
         (let ((raw-f (wff-formula f)))
           (and (pair? raw-f) (eq? (car raw-f) 'IMPLIES)
                (pair? g)     (eq? (car g)     'NOT)
                (alpha-equiv? (binary-left raw-f) (not-body g))
                (dg-apply-rule! dg 'contraposition
                  (list (make-sequent asms (wff-child goal (make-not (binary-right raw-f)))))
                  sqn))))))

;;; -----------------------------------------------------------------------
;;; EQUALITY SUBSTITUTION  (Leibniz / indiscernibility of identicals)
;;;
;;; The substitution schema  s = t  /\  P[t]  =>  P[s]  for an arbitrary
;;; formula context P.  Realised as a primitive inference because P ranges
;;; over all contexts (it cannot be a first-order axiom).  To prove a goal
;;; P[s] when  s = t  is among the assumptions, the rule rewrites every
;;; occurrence of s to t, leaving the single subgoal P[t].
;;;
;;; Sound for VNB's partial equality: s = t already entails s = s and
;;; t = t (both defined), so substituting t for s never replaces a defined
;;; term by a possibly-undefined one.

;;; replace-term: structurally replace every occurrence of the term `old`
;;; in `expr` with `new`.  When `old` is a symbol this is the
;;; capture-avoiding free-variable substitution subst-free.  For a compound
;;; `old`, a capture guard skips any binder whose bound variable is free in
;;; `old` or `new` (such a subtree cannot be rewritten without renaming).

(define (replace-term old new expr)
  (if (symbol? old)
      (subst-free old new expr)
      (let* ((danger  (append (free-vars old) (free-vars new)))
             (captures? (lambda (bvars)
                          (not (null? (filter (lambda (bv) (memq bv danger))
                                              bvars))))))
        (let walk ((e expr))
          (cond
            ((alpha-equiv? e old) new)
            ((functoid? e)
             (if (captures? (map car (functoid-bindings e)))
                 e
                 (make-functoid
                  (functoid-kind e)
                  (map (lambda (b) (cons (car b) (walk (cdr b))))
                       (functoid-bindings e))
                  (walk (functoid-body e)))))
            ((not (pair? e)) e)
            (else
             (case (car e)
               ((FORALL FORSOME IOTA COMP)
                (if (memq (cadr e) danger)
                    e
                    (list (car e) (cadr e) (walk (caddr e)))))
               ((SEP BIG-UNION)
                (if (memq (cadr e) danger)
                    e
                    (list (car e) (cadr e) (walk (caddr e)) (walk (cadddr e)))))
               ((VNB-LAMBDA)
                ;; (VNB-LAMBDA bspec A body): A is outside the binder, so it is
                ;; walked even when the bound vars capture -- mirrors SEP/BIG-UNION.
                (if (captures? (vnb-lambda-bvars (cadr e)))
                    (list 'VNB-LAMBDA (cadr e) (walk (caddr e)) (cadddr e))
                    (list 'VNB-LAMBDA (cadr e) (walk (caddr e)) (walk (cadddr e)))))
               ;; NTH: no special case -- the index is walked like any other
               ;; argument, so eq-subst can rewrite a term occurring there.
               ;; See free-vars (expressions.scm).  (2026-08-04)
               ;;
               ;; The HEAD is walked too (2026-09-16).  Until then this branch
               ;; was (cons (car e) (map walk (cdr e))): a compound head --
               ;; ((VADD md) x y), an applied VNB-LAMBDA, ((f (g r)) r) -- was
               ;; never visited, so a rewrite of a term occurring only there
               ;; was a no-op, and one occurring both there and in an argument
               ;; rewrote the argument ALONE, silently.  Substituting equals
               ;; for equals in an operator term is ordinary Leibniz
               ;; substitution (subst-free already does it for variables);
               ;; the binder cases above still guard capture when the head is
               ;; itself a binder.  A symbol head is returned unchanged:
               ;; `old' is compound here, so the alpha-equiv? test above
               ;; cannot match a symbol.  Probe:
               ;; scratchpad/mx/subst-head-probe.scm (before/after logs beside it).
               (else
                (cons (walk (car e)) (map walk (cdr e)))))))))))

;; The capture guard above is only as good as this list (expressions.scm:
;; declare-binder-walker!): a binder missing from it is a binder eq-subst would
;; rewrite straight through.
(declare-binder-walker! 'replace-term
                        '(FORALL FORSOME IOTA COMP SEP BIG-UNION VNB-LAMBDA))

;;; pi-eq-subst!: eq-formula is a raw (= s t) OR (== s t).  The (quasi-)equality
;;; must appear in the assumptions in either orientation and under either head;
;;; the goal is rewritten s -> t.  Quasi-equal terms are interchangeable (a
;;; congruence: same definedness, equal where defined), so == licenses the
;;; substitution exactly as = does -- needed since the partial-op recursion/
;;; bridge facts are now stated with ==.
(define (pi-eq-subst! sqn eq-formula)
  (and (pair? eq-formula) (memq (car eq-formula) '(= ==))
       (let* ((asms (sequent-node-assumptions sqn))
              (goal (sequent-node-assertion   sqn))
              (dg   (sqn-dg sqn))
              (s    (binary-left  eq-formula))
              (t    (binary-right eq-formula)))
         (and (or (asms-find asms `(= ,s ,t))
                  (asms-find asms `(= ,t ,s))
                  (asms-find asms `(== ,s ,t))
                  (asms-find asms `(== ,t ,s)))
              (let* ((g     (wff-formula goal))
                     (new-g (replace-term s t g)))
                (and (not (alpha-equiv? new-g g))
                     (begin
                       (validate-wff! new-g)
                       (dg-apply-rule! dg 'eq-subst
                         (list (make-sequent asms (wff-child goal new-g)))
                         sqn))))))))

;;; -----------------------------------------------------------------------
;;; CONDITIONAL TERM REDUCTION  --  (IF p a b)
;;;
;;; (IF p a b) is the term equal to a when the wff p holds, b otherwise.
;;; Its defining equations are schematic in p (a wff), and VNB has no
;;; quantification over wffs, so they cannot be plain axioms.  They are
;;; kernel rules instead, each cut-shaped:
;;;
;;;   pi-if-true!  spawns p       as a subgoal; the other branch gains the
;;;                assumption (= (IF p a b) a).
;;;   pi-if-false! spawns (NOT p) as a subgoal; the other branch gains the
;;;                assumption (= (IF p a b) b).
;;;
;;; Soundness: in every model, p => IF(p,a,b) = a and (NOT p) => IF(p,a,b)
;;; = b, so once the condition is proved the equation is a valid assumption.

(define (pi-if-true! sqn if-term)
  ;; if-term: a raw (IF p a b).
  (or (and (pair? if-term) (eq? (car if-term) 'IF) (= (length if-term) 4))
      (error "pi-if-true!: not an IF term" if-term))
  (let* ((asms (sequent-node-assumptions sqn))
         (goal (sequent-node-assertion   sqn))
         (dg   (sqn-dg sqn))
         (p    (cadr  if-term))
         (a    (caddr if-term))
         (eqn  (make-= if-term a)))
    (validate-wff! p)
    (validate-wff! eqn)
    (dg-apply-rule! dg 'if-true
      (list (make-sequent asms (wff-child goal p))
            (make-sequent (context-add-assumption asms (wff-child goal eqn))
                          goal))
      sqn)))

(define (pi-if-false! sqn if-term)
  ;; if-term: a raw (IF p a b).
  (or (and (pair? if-term) (eq? (car if-term) 'IF) (= (length if-term) 4))
      (error "pi-if-false!: not an IF term" if-term))
  (let* ((asms (sequent-node-assumptions sqn))
         (goal (sequent-node-assertion   sqn))
         (dg   (sqn-dg sqn))
         (p    (cadr   if-term))
         (b    (cadddr if-term))
         (notp (make-not p))
         (eqn  (make-= if-term b)))
    (validate-wff! notp)
    (validate-wff! eqn)
    (dg-apply-rule! dg 'if-false
      (list (make-sequent asms (wff-child goal notp))
            (make-sequent (context-add-assumption asms (wff-child goal eqn))
                          goal))
      sqn)))

;;; -----------------------------------------------------------------------
;;; REFLEXIVITY

;;; Class constructors that are TOTAL over classes (defined on ANY arguments,
;;; set or not -- theory.scm): so a tree built from them over defined args is
;;; defined.  Conservative whitelist; extend only with genuinely-total ops.
(define *total-term-heads*
  '(UNION INTERSECTION COMPLEMENT-IN CARTESIAN LIST PAIR
    ;; 2026-09-18 (the user's policy, docs/definedness-instantiation-2026-09-18.md
    ;; section 4a): a CLASS TERM denotes whenever its arguments do.  These are
    ;; the primitive comprehension constructors; the binder forms SEP / COMP /
    ;; BIG-UNION and every functoid whose body is built from them are handled
    ;; by `term-self-defined?' below.  NOT here, and never: CHOICE, IOTA,
    ;; function application, and the IOTA-bodied constructors (MATOF and its
    ;; family) -- CHOICE([]) may or may not denote, and nothing may assume it.
    POWER IMAGE SINGLETON TUPLES FUN succ succ_ORD
    ORD-SEGMENT INJECTION BIJECTION MATRIX MAKE-SET PARTIAL-FUN DOM RES SQN))

;;; The registered body / parameters of a def-functoid (structures.scm's
;;; *functoid-registry* holds (params body path)), or #f.  Read at call time;
;;; the registry is defined by a later file.
(define (pi--functoid-body name)
  (let ((e (hash-table-ref/default *functoid-registry* name #f)))
    (and e (pair? e) (pair? (cdr e)) (cadr e))))
(define (pi--functoid-params name)
  (let ((e (hash-table-ref/default *functoid-registry* name #f)))
    (and e (pair? e) (car e))))

;;; Is a functoid BODY, read with its parameters as variables, a class term
;;; that denotes whenever those parameters do?  Total heads, the binder forms
;;; (whose DOMAIN must be so), and nested functoids (their own body and their
;;; actual arguments), to a fixed depth.  Anything else -- IOTA, CHOICE,
;;; MATOF, an application -- is not.
(define (pi--body-shape-total? body depth)
  (cond
    ((> depth 8) #f)
    ((not (pair? body)) #t)
    ((memq (car body) '(SEP BIG-UNION VNB-LAMBDA))
     (and (= (length body) 4) (pi--body-shape-total? (caddr body) depth)))
    ((eq? (car body) 'COMP) #t)
    ((memq (car body) *total-term-heads*)
     (every (lambda (a) (pi--body-shape-total? a depth)) (cdr body)))
    ((and (symbol? (car body)) (pi--functoid-body (car body)))
     => (lambda (b)
          (and (every (lambda (a) (pi--body-shape-total? a depth)) (cdr body))
               (pi--body-shape-total? b (+ depth 1)))))
    (else #f)))

;;; arith-eval-term raises on some symbolic shapes ((^ 2 k): "The object #f,
;;; passed as an argument to exact?" -- found 2026-09-18 by the definedness
;;; audit); a certificate test must never raise, so guard it.
(define (pi--arith-number? t)
  (call-with-current-continuation
   (lambda (k)
     (with-exception-handler
      (lambda (e) (k #f))
      (lambda () (let ((v (arith-eval-term t))) (and v (number? v) #t)))))))

;;; Is t SYNTACTICALLY GUARANTEED defined?  SOUND: returns #t only for
;;; certainly-defined t, so closing (= t t) by reflexivity stays sound under
;;; the partial-equality reading ((= t t) IS the definedness predicate).
;;;   - an atom: a variable ranges over defined classes; a numeral/constant is
;;;     defined;
;;;   - a ground arithmetic term that arith-eval reduces to a number;
;;;   - a total class-constructor applied to defined args.
;;; A PARTIAL operation (+ * - / on non-ground args, function application
;;; f(x), IOTA, structure ops, set-builders) is NOT certified -- definedness
;;; there needs a proof (e.g. via (IN t S)), so reflexivity refuses.  This is
;;; what rejects the unsound (= (+ bongo bongo) (+ bongo bongo)).  When t is
;;; genuinely undefined or its definedness is not established, use (qrfl):
;;; (== t t) holds unconditionally.
(define (term-self-defined? t)
  (cond
    ((not (pair? t)) #t)
    ((pi--arith-number? t) #t)
    ((and (memq (car t) *total-term-heads*)
          (every term-self-defined? (cdr t))) #t)
    ;; the binder comprehensions denote when their DOMAIN does (4a); COMP always
    ((and (memq (car t) '(SEP BIG-UNION)) (= (length t) 4))
     (term-self-defined? (caddr t)))
    ((eq? (car t) 'COMP) #t)
    ;; a def-functoid whose body is a class term of that kind, on defined args
    ((and (symbol? (car t)) (pi--functoid-body (car t)))
     => (lambda (b)
          (and (every term-self-defined? (cdr t))
               (pi--body-shape-total? b 0))))
    ;; A VNB-LAMBDA DENOTES WHENEVER ITS DOMAIN DOES (2026-08-30, the user's
    ;; call).  (VNB-LAMBDA bind-spec A body) is the set of ordered pairs
    ;; {(x, body) : x in A} -- its GRAPH -- so it is an object as soon as A is
    ;; one, and the BODY's definedness is irrelevant: where the body is
    ;; undefined the graph simply has no pair there.  A lambda whose body is
    ;; nowhere defined is the EMPTY function, which is a perfectly good object
    ;; and merely fails to be total.
    ;;
    ;; DEFINEDNESS IS NOT SETHOOD, and that is what makes this safe.  Measured:
    ;; `ORD = ORD' closes while `ORD in SET' does not -- a proper class is a
    ;; defined term that is not a set.  So a lambda over a proper-class domain
    ;; denotes a proper CLASS; it is defined, and it is still in no FUN, because
    ;; membership there goes through `lam-t', which demands `A in SET' and
    ;; pointwise typing and is untouched by this clause.  The standing
    ;; must-not-prove entry `lam x in ORD. x  is in FUN(ORD,ORD)' therefore
    ;; still refuses.
    ;;
    ;; WHY IT WAS NEEDED.  Nothing in the theory characterised VNB-LAMBDA at all
    ;; -- zero installed formulas mention it, and its whole meaning came from
    ;; the two kernel rules lam-t and lam-b.  So the only route to "this lambda
    ;; is an object" ran through membership in a FUN, i.e. through TOTALITY, and
    ;; a tuple with a lambda in it could not be shown defined even when every
    ;; component provably was.  That blocked every `law "scal(s) = <closed
    ;; tuple>"' pinning law -- which is how it surfaced: the RR normed-vector-
    ;; space witness discharged 20 of its 21 obligations and stuck on
    ;; `scal(s) = scal(s)'.  The proper fix is to say what a lambda IS; this is
    ;; the definedness half of that, and the companion graph axiom
    ;;     z in VNB-LAMBDA(x, A, body)  iff  forsome x in A. z = LIST(x, body)
    ;; is the other half and is NOT added here (it wants `declare-named-only!',
    ;; being a bare IN-characterisation that would fire on every goal).
    ((and (eq? (car t) 'VNB-LAMBDA) (= (length t) 4))
     (term-self-defined? (caddr t)))
    (else #f)))

;;; Does some assumption WITNESS that t is defined?  (IN t S) gives t in a
;;; class, hence defined; a strict (= t _)/(= _ t) asserts t defined too.  (A
;;; == fact does NOT -- both sides may be undefined.)  Sound basis for closing
;;; (= t t) when t is defined in context though not syntactically (e.g. a
;;; function application f(x) that an earlier step typed via fun-apply-type).
(define (asm-establishes-defined? asms t)
  (or (let loop ((as asms))
        (and (pair? as)
             (let ((f (wff-formula (car as))))
               (if (and (pair? f)
                        (or (and (eq? (car f) 'IN) (= (length f) 3)
                                 (alpha-equiv? (cadr f) t))
                            (and (eq? (car f) '=) (= (length f) 3)
                                 (or (alpha-equiv? (cadr f) t)
                                     (alpha-equiv? (caddr f) t)))))
                   #t
                   (loop (cdr as))))))
      (pi--accessor-certified? asms t)))

;;; Policy 4b (2026-09-18): a STRUCTURE HYPOTHESIS certifies its accessors.
;;; (ACC s) with `IS-X s' in the context, where ACC is a slot of the declared
;;; structure X, denotes: the predicate's defining IFF types every slot.  Also
;;; (ACC (V r)) where V is a view functoid whose body is a LIST of accessor
;;; applications: the k-th component, at the actual argument, must itself be
;;; certified (recursively, through the same two tests).
(define (pi--accessor-certified? asms t)
  (and (pair? t) (= (length t) 2) (symbol? (car t))
       (let ((acc (car t)) (arg (cadr t)))
         (or
          (let loop ((as asms))
            (and (pair? as)
                 (let ((f (wff-formula (car as))))
                   (or (and (pair? f) (= (length f) 2) (symbol? (car f))
                            (alpha-equiv? (cadr f) arg)
                            (let ((nm (symbol->string (car f))))
                              (and (> (string-length nm) 3)
                                   (string-ci=? (substring nm 0 3) "is-")
                                   (let ((sd (lookup-structure
                                              (string->symbol (substring nm 3 (string-length nm))))))
                                     (and sd (memq acc (structure-slot-names sd)) #t)))))
                       (loop (cdr as))))))
          (and (pair? arg) (symbol? (car arg))
               (let ((body (pi--functoid-body (car arg)))
                     (params (pi--functoid-params (car arg)))
                     (ix (hash-table-ref/default *accessor-index* acc #f)))
                 (and body ix (pair? body) (eq? (car body) 'LIST)
                      (list? params) (= (length params) 1) (= (length (cdr arg)) 1)
                      (integer? (car ix)) (<= 1 (car ix) (length (cdr body)))
                      (let ((comp (list-ref (cdr body) (- (car ix) 1))))
                        (and (pair? comp) (= (length comp) 2) (symbol? (car comp))
                             (eq? (cadr comp) (car params))
                             (let ((inst (list (car comp) (cadr arg))))
                               (or (term-self-defined? inst)
                                   (asm-establishes-defined? asms inst))))))))))))


;;; ---------------------------------------------------------------------
;;; THE DEFINEDNESS CERTIFICATE, v2 (2026-09-18).  One recursive test that
;;; sees the CONTEXT at every node, per docs/definedness-instantiation-
;;; 2026-09-18.md sections 4a/4b: an atom; a ground number; a term the context
;;; types (IN t X) or equates (= t _); a total constructor on certified
;;; arguments; a comprehension whose domain is certified; NTH k of a LIST (or of
;;; a functoid whose body is one); arithmetic on number-typed arguments (the
;;; number systems are closed under + - * min max abs succ); an accessor of a
;;; structure the context has (IS-X s, or s in X, through the definitional
;;; parent chain); an applied structure OPERATION on arguments typed in its
;;; declared domain; an application of a function the context types (IN f
;;; (FUN D _)) at arguments typed in D; and a functoid whose body, at the
;;; actual arguments, is certified.  NOT certified, ever: CHOICE, IOTA, an
;;; untyped application, the IOTA-bodied constructors.
;;; `every' in this tree is 2-ary (deduction-graphs.scm); a two-list walk
(define (pi--every2 pred l1 l2)
  (or (null? l1) (null? l2)
      (and (pred (car l1) (car l2)) (pi--every2 pred (cdr l1) (cdr l2)))))
(define *pi-number-classes* '(RR ZZ NN QQ CC))
(define *pi-arith-total-heads* '(+ - * min max abs succ ^))   ; ^ : power-closed-at (x in RR, n in NN)

(define (pi--in-context? asms a X)
  (let loop ((as asms))
    (and (pair? as)
         (let ((f (wff-formula (car as))))
           (or (and (pair? f) (eq? (car f) 'IN) (= (length f) 3)
                    (alpha-equiv? (cadr f) a) (alpha-equiv? (caddr f) X))
               (loop (cdr as)))))))

(define (pi--number-typed? asms a)
  (or (pi--arith-number? a)
      (let loop ((as asms))
        (and (pair? as)
             (let ((f (wff-formula (car as))))
               (or (and (pair? f) (= (length f) 3) (eq? (car f) 'IN)
                        (memq (caddr f) *pi-number-classes*)
                        (alpha-equiv? (cadr f) a))
                   (and (pair? f) (= (length f) 2) (eq? (car f) 'POS-RR)
                        (alpha-equiv? (cadr f) a))
                   (loop (cdr as))))))))

;;; 'IS-X or the class name X  ->  the DECLARED structure-def, through the
;;; definitional parent chain (IS-COMMUTATIVE-RING -> RING), or #f.
(define (pi--structure-def-for sym)
  (let* ((nm   (symbol->string sym))
         (base (if (and (> (string-length nm) 3)
                        (string-ci=? (substring nm 0 3) "is-"))
                   (string->symbol (substring nm 3 (string-length nm)))
                   sym)))
    (let loop ((x base) (depth 0))
      (and x (symbol? x) (< depth 8)
           (or (lookup-structure x)
               (let ((d (hash-table-ref/default *definitional-structure-table* x #f)))
                 (and d (loop (definitional-structure-parent d) (+ depth 1)))))))))

;;; The structure-def some hypothesis IS-X s / s in X gives for the term s.
(define (pi--structure-hyp asms s)
  (let loop ((as asms))
    (and (pair? as)
         (let ((f (wff-formula (car as))))
           (or (and (pair? f) (= (length f) 2) (symbol? (car f))
                    (alpha-equiv? (cadr f) s)
                    (pi--structure-def-for (car f)))
               (and (pair? f) (= (length f) 3) (eq? (car f) 'IN) (symbol? (caddr f))
                    (alpha-equiv? (cadr f) s)
                    (pi--structure-def-for (caddr f)))
               (loop (cdr as)))))))

;;; A domain symbol of a slot spec: an accessor name means (ACC s); anything
;;; else is a global class (RR, NN, ...).
(define (pi--slot-domain-term sd s d)
  (if (and (symbol? d) (memq d (structure-slot-names sd))) (list d s) d))

(define (pi--functoid-instance t)
  (let ((body (pi--functoid-body (car t))) (params (pi--functoid-params (car t))))
    (and body (list? params) (= (length params) (length (cdr t)))
         (every symbol? params)
         (subst-free* (map cons params (cdr t)) body))))

(define (pi--fun-typed-app? asms f args)
  (let loop ((as asms))
    (and (pair? as)
         (let ((h (wff-formula (car as))))
           (or (and (pair? h) (eq? (car h) 'IN) (= (length h) 3)
                    (alpha-equiv? (cadr h) f)
                    (pair? (caddr h)) (eq? (car (caddr h)) 'FUN) (pair? (cdr (caddr h)))
                    (let ((D (cadr (caddr h))))
                      (cond ((= (length args) 1) (pi--in-context? asms (car args) D))
                            ((and (pair? D) (eq? (car D) 'CARTESIAN)
                                  (= (length (cdr D)) (length args)))
                             (pi--every2 (lambda (a d) (pi--in-context? asms a d)) args (cdr D)))
                            (else (pi--in-context? asms (cons 'LIST args) D)))))
               (loop (cdr as)))))))

(define (pi--class-of-tuples? X depth)
  (cond
    ((> depth 8) #f)
    ((not (pair? X)) #f)
    ((eq? (car X) 'TUPLES) #t)
    ((eq? (car X) 'MATRIX) #t)          ; primitive: TUPLES(TUPLES X) with equal rows
    ((and (eq? (car X) 'SEP) (= (length X) 4)) (pi--class-of-tuples? (caddr X) depth))
    ((and (symbol? (car X)) (pi--functoid-instance X))
     => (lambda (b) (pi--class-of-tuples? b (+ depth 1))))
    (else #f)))
(define (pi--typed-in-tuples? asms t)
  (let loop ((as asms))
    (and (pair? as)
         (let ((f (wff-formula (car as))))
           (or (and (pair? f) (eq? (car f) 'IN) (= (length f) 3)
                    (alpha-equiv? (cadr f) t)
                    (pi--class-of-tuples? (caddr f) 0))
               (loop (cdr as)))))))

;;; STRICTNESS (2026-09-18): IN, =, <=, < are strict relations and every total
;;; constructor is strict in its arguments (the manual: "undefinedness
;;; propagates through all operations"), so a term occurring OUTSIDE any binder
;;; in a true atomic hypothesis of those shapes denotes.  `f in FUN(NN, PTS s)'
;;; certifies PTS(s); `t(j) subset t(k)' does not (SUBSET is not primitive here).
(define (pi--subterm-outside-binders? t e)
  (cond
    ((alpha-equiv? e t) #t)
    ((not (pair? e)) #f)
    ((memq (car e) '(FORALL FORSOME IOTA COMP)) #f)
    ((and (memq (car e) '(SEP BIG-UNION VNB-LAMBDA)) (= (length e) 4))
     (pi--subterm-outside-binders? t (caddr e)))      ; only the DOMAIN is outside
    ;; every position, the HEAD included: application is strict in its operator
    (else (any (lambda (x) (pi--subterm-outside-binders? t x)) e))))
(declare-binder-walker! 'pi--subterm-outside-binders?
                        '(FORALL FORSOME IOTA COMP SEP BIG-UNION VNB-LAMBDA))

(define (pi--strict-hyp-certifies? asms t)
  (let loop ((as asms))
    (and (pair? as)
         (let ((f (wff-formula (car as))))
           (or (and (pair? f) (memq (car f) '(IN = <= <)) (= (length f) 3)
                    (or (pi--subterm-outside-binders? t (cadr f))
                        (pi--subterm-outside-binders? t (caddr f))))
               (loop (cdr as)))))))

;;; A def-predicate HYPOTHESIS certifies what its defining body's conjuncts
;;; certify (2026-09-18, rake repair D4: IS-ANTIDERIVABLE(s(k), a, b) has
;;; `s(k) in FUN(RR,RR)' one unfold and one FORSOME down; IS-NOETHERIAN(m) has
;;; IS-MODULE(m), which types VEC(m)).  The defining IFF is the theorem-table
;;; entry under the predicate's own name (def-predicate, structures.scm).
(define *pi-connectives* '(IN = <= < NOT AND OR IMPLIES IFF FORALL FORSOME TRUTH FALSITY))
(define (pi--and-conjuncts b)
  (if (and (pair? b) (eq? (car b) 'AND) (= (length b) 3))
      (append (pi--and-conjuncts (cadr b)) (pi--and-conjuncts (caddr b)))
      (list b)))
;;; TWO GUARDS (2026-09-20, audit 13-E; both defects were live on the band).
;;; (1) The body's leading FORSOMEs are stripped, and the witness used to come
;;; back FREE under its binder's own name: with `odd(n)' in the context, the
;;; conjunct `k in ZZ' of odd's body certified `2 * k' for the CONTEXT's k, an
;;; unrelated and untyped variable, and `rfl' closed `2 * k = 2 * k'.  Each
;;; stripped binder is now replaced by a fresh uninterned symbol, which no term
;;; of the context can contain; a conjunct about the parameters certifies as
;;; before.  (2) The entry is read from the theorem table BY NAME: an ASSERTED
;;; statement under a predicate's name certified, and the proof billed nothing.
;;; Only a definitional, primitive or proven entry is read.
;;; `provenance-of' (macetes.scm) loads after this file; macetes.scm stores it in
;;; the hook below.  While the hook is unset nothing is certified by this route.
(define *pi-provenance-of* #f)
(define (pi--pred-def-trusted? name)
  (and *pi-provenance-of*
       (memq (*pi-provenance-of* name) '(definitional primitive proven))
       #t))
(define (pi--pred-def-conjuncts f)
  (let ((def (and (pi--pred-def-trusted? (car f))
                  (hash-table-ref/default *theorem-table* (car f) #f))))
    (and def (pair? def)
         (let loop ((e def) (args (cdr f)) (binds '()))
           (cond ((and (pair? e) (eq? (car e) 'FORALL) (pair? args))
                  (loop (caddr e) (cdr args) (cons (cons (cadr e) (car args)) binds)))
                 ((and (pair? e) (eq? (car e) 'IFF) (null? args)
                       (pair? (cadr e)) (eq? (car (cadr e)) (car f)))
                  (let strip ((b (subst-free* binds (caddr e))))
                    (if (and (pair? b) (eq? (car b) 'FORSOME) (= (length b) 3))
                        (if (symbol? (cadr b))
                            (strip (subst-free* (list (cons (cadr b) (generate-uninterned-symbol)))
                                                (caddr b)))
                            '())            ; a binder that is not a plain variable: certify nothing
                        (pi--and-conjuncts b))))
                 (else #f))))))
(define (pi--raw-conjuncts-certify? cs t depth)
  (any (lambda (c)
         (and (pair? c) (symbol? (car c))
              (or (and (memq (car c) '(IN = <= <)) (= (length c) 3)
                       (or (pi--subterm-outside-binders? t (cadr c))
                           (pi--subterm-outside-binders? t (caddr c))))
                  (and (= (length c) 2) (pi--structure-def-for (car c))
                       (or (alpha-equiv? (cadr c) t)
                           (and (pair? t) (= (length t) 2) (symbol? (car t))
                                (alpha-equiv? (cadr c) (cadr t))
                                (memq (car t) (structure-slot-names (pi--structure-def-for (car c))))
                                #t)))
                  (and (< depth 3) (not (memq (car c) *pi-connectives*))
                       (let ((cs2 (pi--pred-def-conjuncts c)))
                         (and cs2 (pi--raw-conjuncts-certify? cs2 t (+ depth 1))))))))
       cs))
(define (pi--via-pred-hyps? asms t)
  (let loop ((as asms))
    (and (pair? as)
         (let ((f (wff-formula (car as))))
           (or (and (pair? f) (symbol? (car f)) (not (memq (car f) *pi-connectives*))
                    (let ((cs (pi--pred-def-conjuncts f)))
                      (and cs (pi--raw-conjuncts-certify? cs t 0))))
               (loop (cdr as)))))))

(define (pi--defined? asms t depth)
  (cond
    ((> depth 8) #f)
    ((not (pair? t)) #t)
    ((pi--arith-number? t) #t)
    ((asm-establishes-defined? asms t) #t)
    ((pi--strict-hyp-certifies? asms t) #t)
    ;; a structure hypothesis ON the term (IS-METRIC-SPACE (ms n)) certifies it:
    ;; the predicate's IFF types the tuple's every slot, so the tuple denotes
    ((pi--structure-hyp asms t) #t)
    ((and (symbol? (car t)) (memq (car t) *total-term-heads*))
     (every (lambda (a) (pi--defined? asms a depth)) (cdr t)))
    ((and (memq (car t) '(SEP BIG-UNION VNB-LAMBDA)) (= (length t) 4))
     (pi--defined? asms (caddr t) depth))
    ((eq? (car t) 'COMP) #t)
    ((and (eq? (car t) 'NTH) (= (length t) 3) (exact-integer? (cadr t))
          (pair? (caddr t)) (eq? (car (caddr t)) 'LIST)
          (<= 1 (cadr t) (length (cdr (caddr t)))))
     (pi--defined? asms (list-ref (cdr (caddr t)) (- (cadr t) 1)) depth))
    ((and (eq? (car t) 'NTH) (= (length t) 3) (exact-integer? (cadr t))
          (pair? (caddr t)) (symbol? (car (caddr t))) (pi--functoid-instance (caddr t)))
     => (lambda (b) (pi--defined? asms (list 'NTH (cadr t) b) (+ depth 1))))
    ((and (symbol? (car t)) (memq (car t) *pi-arith-total-heads*)
          (every (lambda (a) (pi--number-typed? asms a)) (cdr t))) #t)
    ;; LENGTH t for a t the context types in a class of TUPLES (through SEP
    ;; domains and functoid bodies: MAT -> MATRIX -> TUPLES)
    ((and (eq? (car t) 'LENGTH) (= (length t) 2)
          (pi--typed-in-tuples? asms (cadr t))) #t)
    ;; accessor (ACC s) under a structure hypothesis on s
    ((and (symbol? (car t)) (= (length t) 2)
          (let ((sd (pi--structure-hyp asms (cadr t))))
            (and sd (memq (car t) (structure-slot-names sd)) #t))) #t)
    ;; applied structure operation ((ACC s) a1 ... an) on arguments in its domain
    ((and (pair? (car t)) (= (length (car t)) 2) (symbol? (car (car t)))
          (let* ((acc (car (car t))) (s (cadr (car t)))
                 (sd (pi--structure-hyp asms s))
                 (spec (and sd (assq acc (structure-def-slots sd)))))
            (and spec (eq? (cadr spec) 'op) (pair? (cddr spec))
                 (let ((dom (caddr spec)) (args (cdr t)))
                   (cond ((and (pair? dom) (eq? (car dom) 'CARTESIAN)
                               (= (length (cdr dom)) (length args)))
                          (pi--every2 (lambda (a d) (pi--in-context? asms a (pi--slot-domain-term sd s d)))
                                      args (cdr dom)))
                         ((= (length args) 1)
                          (pi--in-context? asms (car args) (pi--slot-domain-term sd s dom)))
                         (else #f)))))) #t)
    ;; an application of a function the context types
    ((and (pair? (cdr t)) (pi--fun-typed-app? asms (car t) (cdr t))) #t)
    ;; a functoid: certified arguments and a certified instantiated body
    ((and (symbol? (car t)) (pi--functoid-instance t))
     => (lambda (b) (pi--defined? asms b (+ depth 1))))
    ;; last, since it unfolds every predicate hypothesis in the context
    ((pi--via-pred-hyps? asms t) #t)
    (else #f)))

(define (pi-reflexivity! sqn)
  (let* ((goal (sequent-node-assertion sqn))
         (g    (wff-formula goal))
         (dg   (sqn-dg sqn)))
    (if (or (eq? g 'TRUTH)
            (and (pair? g) (eq? (car g) '=)
                 (alpha-equiv? (cadr g) (caddr g))
                 ;; definedness guard: t = t only when t is defined -- either
                 ;; SYNTACTICALLY (variable/ground/total-op tree) or witnessed
                 ;; by a context assumption (IN t _)/(= t _).
                 (pi--defined? (sequent-node-assumptions sqn) (cadr g) 0)))
        (dg-apply-rule! dg 'reflexivity '() sqn)
        #f)))

;;; QUASI-REFLEXIVITY

(define (pi-quasi-reflexivity! sqn)
  (let* ((goal (sequent-node-assertion sqn))
         (g    (wff-formula goal))
         (dg   (sqn-dg sqn)))
    (if (and (pair? g) (eq? (car g) '==)
             (alpha-equiv? (cadr g) (caddr g)))
        (dg-apply-rule! dg 'quasi-reflexivity '() sqn)
        #f)))

;;; PROOF BY CONTRADICTION

(define (pi-proof-by-contradiction! sqn)
  (let* ((asms (sequent-node-assumptions sqn))
         (goal (sequent-node-assertion   sqn))
         (g    (wff-formula goal))
         (dg   (sqn-dg sqn)))
    (dg-apply-rule! dg 'proof-by-contradiction
      (list (make-sequent (context-add-assumption asms (wff-child goal (make-not g)))
                          (wff-child goal 'FALSITY)))
      sqn)))

;;; THEOREM ASSUMPTION
;;;
;;; The kernel takes a theorem NAME and looks up the formula in the global
;;; *theorem-table* itself; this is the soundness boundary.  An earlier
;;; version accepted an arbitrary raw S-expression, which let a caller
;;; bypassing the cmd-* layer introduce (NOT TRUTH) and derive FALSITY.
(define (pi-theorem-assumption! sqn theorem-name)
  (let* ((asms    (sequent-node-assumptions sqn))
         (goal    (sequent-node-assertion   sqn))
         (dg      (sqn-dg sqn))
         (formula (hash-table-ref/default *theorem-table* theorem-name #f)))
    (if formula
        (dg-apply-rule! dg 'theorem-assumption
          (list (make-sequent
                 (context-add-assumption asms (wff-child goal formula))
                 goal))
          sqn)
        #f)))

;;; -----------------------------------------------------------------------
;;; CARTESIAN PRODUCT MEMBERSHIP

(define (pi-cartesian-intro! sqn)
  (let* ((asms (sequent-node-assumptions sqn))
         (goal (sequent-node-assertion   sqn))
         (g    (wff-formula goal))
         (dg   (sqn-dg sqn)))
    (and (pair? g) (eq? (car g) 'IN)
         (let ((tuple (cadr g)) (prod (caddr g)))
           (and (pair? tuple) (eq? (car tuple) 'LIST)
                (pair? prod)  (eq? (car prod)  'CARTESIAN)
                (let ((elems (cdr tuple)) (sets (cdr prod)))
                  (and (= (length elems) (length sets))
                       (dg-apply-rule! dg 'cartesian-intro
                         (map (lambda (elem sset)
                                (make-sequent asms (wff-child goal `(IN ,elem ,sset))))
                              elems sets)
                         sqn))))))))

(define (pi-cartesian-elim! sqn membership-formula k)
  ;; membership-formula: raw S-expression
  (let* ((asms (sequent-node-assumptions sqn))
         (goal (sequent-node-assertion   sqn))
         (dg   (sqn-dg sqn))
         (f    (asms-find asms membership-formula)))
    (and f
         (let ((raw-f (wff-formula f)))
           (and (pair? raw-f) (eq? (car raw-f) 'IN)
                (let ((tuple (cadr raw-f)) (prod (caddr raw-f)))
                  (and (pair? tuple) (eq? (car tuple) 'LIST)
                       (pair? prod)  (eq? (car prod)  'CARTESIAN)
                       (let ((elems (cdr tuple)) (sets (cdr prod)))
                         ;; Length must match: a tuple of length n in a
                         ;; CARTESIAN product of length m != n is malformed
                         ;; in this kernel.  Refuse rather than risk
                         ;; list-ref errors or vacuous discharge.
                         (and (= (length elems) (length sets))
                              (integer? k) (>= k 1) (<= k (length elems))
                              (let ((elem-k (list-ref elems (- k 1)))
                                    (set-k  (list-ref sets  (- k 1))))
                                (dg-apply-rule! dg `(cartesian-elim ,k)
                                  (list (make-sequent
                                          (context-add-assumption asms (wff-child f `(IN ,elem-k ,set-k)))
                                          goal))
                                  sqn)))))))))))

;;; TUPLES INTRO / ELIM

(define (pi-tuples-intro! sqn)
  (let* ((asms (sequent-node-assumptions sqn))
         (goal (sequent-node-assertion   sqn))
         (g    (wff-formula goal))
         (dg   (sqn-dg sqn)))
    (and (pair? g) (eq? (car g) 'IN)
         (let ((tuple       (cadr g))
               (tuples-expr (caddr g)))
           (and (pair? tuple)       (eq? (car tuple)       'LIST)
                (pair? tuples-expr) (eq? (car tuples-expr) 'TUPLES)
                (= (length tuples-expr) 2)
                (let ((elems (cdr tuple))
                      (A     (cadr tuples-expr)))
                  (dg-apply-rule! dg 'tuples-intro
                    (map (lambda (elem)
                           (make-sequent asms (wff-child goal `(IN ,elem ,A))))
                         elems)
                    sqn)))))))

(define (pi-tuples-elim! sqn membership-formula k)
  (let* ((asms (sequent-node-assumptions sqn))
         (goal (sequent-node-assertion   sqn))
         (dg   (sqn-dg sqn))
         (f    (asms-find asms membership-formula)))
    (and f
         (let ((raw-f (wff-formula f)))
           (and (pair? raw-f) (eq? (car raw-f) 'IN)
                (let ((tuple       (cadr raw-f))
                      (tuples-expr (caddr raw-f)))
                  (and (pair? tuple)       (eq? (car tuple)       'LIST)
                       (pair? tuples-expr) (eq? (car tuples-expr) 'TUPLES)
                       (= (length tuples-expr) 2)
                       (let ((elems (cdr tuple))
                             (A     (cadr tuples-expr)))
                         (and (integer? k) (>= k 1) (<= k (length elems))
                              (let ((elem-k (list-ref elems (- k 1))))
                                (dg-apply-rule! dg `(tuples-elim ,k)
                                  (list (make-sequent
                                          (context-add-assumption asms
                                            (wff-child f `(IN ,elem-k ,A)))
                                          goal))
                                  sqn)))))))))))

;;; NTH REDUCTION

(define (pi-nth-reduce! sqn)
  (let* ((asms (sequent-node-assumptions sqn))
         (goal (sequent-node-assertion   sqn))
         (g    (wff-formula goal))
         (dg   (sqn-dg sqn)))
    (let ((new-g (reduce-nth-in-expr g)))
      (if (alpha-equiv? new-g g)
          #f
          (dg-apply-rule! dg 'nth-reduce
            (list (make-sequent asms (wff-child goal new-g)))
            sqn)))))

(define (reduce-nth-in-expr expr)
  (cond
    ((not (pair? expr)) expr)
    ((and (eq? (car expr) 'NTH)
          (integer? (cadr expr))
          (pair? (caddr expr))
          (eq? (car (caddr expr)) 'LIST))
     (let ((k    (cadr expr))
           (args (cdr (caddr expr))))
       (if (and (>= k 1) (<= k (length args)))
           (list-ref args (- k 1))
           (error "nth-reduce: index out of range" k (length args)))))
    (else
     (cons (reduce-nth-in-expr (car expr))
           (map reduce-nth-in-expr (cdr expr))))))

;;; -----------------------------------------------------------------------
;;; LENGTH REDUCTION -- the dual of NTH reduction.
;;;
;;; (LENGTH (LIST t_1 ... t_n))  ->  n
;;;
;;; SOUND without a definedness guard, on exactly the same footing as NTH
;;; reduction (reduce-nth-in-expr, above): a literal LIST is a total spine
;;; (LIST is a total constructor -- theory.scm / *total-term-heads*), so its
;;; length is the structural count n regardless of whether the ELEMENTS are
;;; defined.  LENGTH counts slots, not values -- just as (NTH 1 (LIST (1/0) 2))
;;; reduces to (1/0) irrespective of its definedness, (LENGTH (LIST (1/0) 2))
;;; reduces to 2.  (The empty case agrees with the length-of-empty axiom.)
;;; Rewrites every such subterm, anywhere in the expression tree.
(define (reduce-length-in-expr expr)
  (cond
    ((not (pair? expr)) expr)
    ((and (eq? (car expr) 'LENGTH)
          (pair? (cadr expr))
          (eq? (car (cadr expr)) 'LIST))
     (length (cdr (cadr expr))))
    (else
     (cons (reduce-length-in-expr (car expr))
           (map reduce-length-in-expr (cdr expr))))))

(define (pi-length-reduce! sqn)
  (let* ((asms (sequent-node-assumptions sqn))
         (goal (sequent-node-assertion   sqn))
         (g    (wff-formula goal))
         (dg   (sqn-dg sqn)))
    (let ((new-g (reduce-length-in-expr g)))
      (if (alpha-equiv? new-g g)
          #f
          (dg-apply-rule! dg 'length-reduce
            (list (make-sequent asms (wff-child goal new-g)))
            sqn)))))

;;; -----------------------------------------------------------------------
;;; FUNCTOID BETA REDUCTION
;;;
;;; (apply-functoid <functoid> v1 v2 ...) reduces by substituting each
;;; binding variable with the corresponding argument.

(define (pi-functoid-beta! sqn)
  (let* ((asms (sequent-node-assumptions sqn))
         (goal (sequent-node-assertion   sqn))
         (g    (wff-formula goal))
         (dg   (sqn-dg sqn)))
    (let ((new-g (reduce-functoid-in-expr g)))
      (if (alpha-equiv? new-g g)
          #f
          (dg-apply-rule! dg 'functoid-beta
            (list (make-sequent asms (wff-child goal new-g)))
            sqn)))))

(define (reduce-functoid-in-expr expr)
  (cond
    ((functoid? expr) expr)
    ((not (pair? expr)) expr)
    ;; (apply-functoid <functoid> v1 v2 ...) -> body[x1:=v1, x2:=v2, ...]
    ((and (eq? (car expr) 'apply-functoid)
          (>= (length expr) 3)
          (functoid? (cadr expr)))
     ;; Beta reduction must be PARALLEL substitution: with sequential subst,
     ;; reducing f = (lambda (x y) (LIST x y)) on args (y 0) would give
     ;; (LIST 0 0) instead of (LIST y 0).  Make it parallel by first
     ;; renaming every bvar to a globally-fresh name (chosen to avoid the
     ;; body and ALL args), then substituting fresh -> arg in any order.
     (let* ((ftd      (cadr expr))
            (bindings (functoid-bindings ftd))
            (args     (cddr expr))
            (body     (functoid-body ftd)))
       (if (not (= (length bindings) (length args)))
           expr  ; arity mismatch: leave alone
           (let* ((bvars        (map car bindings))
                  (avoids       (cons body args))
                  (fresh-names  (map (lambda (bv)
                                       (apply fresh-var bv avoids))
                                     bvars))
                  (body-renamed (fold-left
                                 (lambda (b pair)
                                   (subst-free (car pair) (cdr pair) b))
                                 body
                                 (map cons bvars fresh-names)))
                  (reduced      (fold-left
                                 (lambda (b pair)
                                   (subst-free (car pair)
                                               (reduce-functoid-in-expr (cdr pair))
                                               b))
                                 body-renamed
                                 (map cons fresh-names args))))
             (reduce-functoid-in-expr reduced)))))
    ;; Recurse into sub-expressions
    (else
     (cons (car expr)
           (map reduce-functoid-in-expr (cdr expr))))))

;;; -----------------------------------------------------------------------
;;; UNION MEMBERSHIP

(define (pi-union-intro! sqn k)
  (let* ((asms (sequent-node-assumptions sqn))
         (goal (sequent-node-assertion   sqn))
         (g    (wff-formula goal))
         (dg   (sqn-dg sqn)))
    (and (pair? g) (eq? (car g) 'IN)
         (let ((x (cadr g)) (prod (caddr g)))
           (and (pair? prod) (eq? (car prod) 'UNION)
                (let ((sets (cdr prod)))
                  (and (integer? k) (>= k 1) (<= k (length sets))
                       (dg-apply-rule! dg `(union-intro ,k)
                         (list (make-sequent asms (wff-child goal `(IN ,x ,(list-ref sets (- k 1))))))
                         sqn))))))))

(define (pi-union-elim! sqn membership-formula)
  ;; membership-formula: raw S-expression
  (let* ((asms (sequent-node-assumptions sqn))
         (goal (sequent-node-assertion   sqn))
         (dg   (sqn-dg sqn))
         (f    (asms-find asms membership-formula)))
    (and f
         (let ((raw-f (wff-formula f)))
           (and (pair? raw-f) (eq? (car raw-f) 'IN)
                (let ((x (cadr raw-f)) (prod (caddr raw-f)))
                  (and (pair? prod) (eq? (car prod) 'UNION)
                       (let* ((sets    (cdr prod))
                              (asms*   (context-remove-assumption asms f))
                              (branches (map (lambda (sset)
                                              (make-sequent
                                               (context-add-assumption asms* (wff-child f `(IN ,x ,sset)))
                                               goal))
                                            sets)))
                         (dg-apply-rule! dg 'union-elim branches sqn)))))))))

;;; -----------------------------------------------------------------------
;;; TRANSFINITE INDUCTION
;;;
;;; Strong (complete) induction form.
;;; Goal:    (FORALL var (IMPLIES (IN var ORD) P))
;;; Subgoal: (FORALL var (IMPLIES (AND (IN var ORD)
;;;                                    (FORALL beta (IMPLIES (ORD-LT beta var) P[var:=beta])))
;;;                                P))

(define (pi-tfi! sqn)
  (let* ((asms (sequent-node-assumptions sqn))
         (goal (sequent-node-assertion   sqn))
         (g    (wff-formula goal))
         (dg   (sqn-dg sqn)))
    (and (pair? g) (eq? (car g) 'FORALL)
         (let ((var  (quantifier-var  g))
               (body (quantifier-body g)))
           (and (pair? body) (eq? (car body) 'IMPLIES)
                (let ((hyp (binary-left  body))
                      (P   (binary-right body)))
                  (and (pair? hyp)
                       (eq? (car  hyp) 'IN)
                       (symbol? (cadr hyp))
                       (eq? (cadr  hyp) var)
                       (eq? (caddr hyp) 'ORD)
                       (let* ((avoids (cons var (cons (wff-formula goal)
                                                      (map wff-formula asms))))
                              (beta   (apply fresh-var 'beta P avoids))
                              (P-beta (subst-free var beta P))
                              (IH     `(FORALL ,beta (IMPLIES (ORD-LT ,beta ,var) ,P-beta)))
                              (new-g  `(FORALL ,var (IMPLIES (AND (IN ,var ORD) ,IH) ,P))))
                         (dg-apply-rule! dg 'transfinite-induction
                           (list (make-sequent asms (wff-child goal new-g)))
                           sqn)))))))))

;;; Three-case transfinite induction.
;;; Goal:    (FORALL var (IMPLIES (IN var ORD) P))
;;; Subgoals:
;;;   (1) P[var := 0]                                                (base)
;;;   (2) (FORALL var (IMPLIES (AND (IN var ORD) P) P[var := (succ_ORD var)]))  (successor)
;;;   (3) (FORALL var (IMPLIES (AND (LIMIT-ORD var)                  (limit)
;;;                                 (FORALL beta (IMPLIES (ORD-LT beta var) P[var:=beta])))
;;;                             P))

(define (pi-tfi3! sqn)
  (let* ((asms (sequent-node-assumptions sqn))
         (goal (sequent-node-assertion   sqn))
         (g    (wff-formula goal))
         (dg   (sqn-dg sqn)))
    (and (pair? g) (eq? (car g) 'FORALL)
         (let ((var  (quantifier-var  g))
               (body (quantifier-body g)))
           (and (pair? body) (eq? (car body) 'IMPLIES)
                (let ((hyp (binary-left  body))
                      (P   (binary-right body)))
                  (and (pair? hyp)
                       (eq? (car  hyp) 'IN)
                       (symbol? (cadr hyp))
                       (eq? (cadr  hyp) var)
                       (eq? (caddr hyp) 'ORD)
                       (let* ((avoids    (cons var (cons (wff-formula goal)
                                                          (map wff-formula asms))))
                              (beta      (apply fresh-var 'beta P avoids))
                              (P-zero    (subst-free var 0 P))
                              (P-succ    (subst-free var `(succ_ORD ,var) P))
                              (P-beta    (subst-free var beta P))
                              (IH-limit  `(FORALL ,beta (IMPLIES (ORD-LT ,beta ,var) ,P-beta)))
                              (base-goal P-zero)
                              (succ-goal `(FORALL ,var (IMPLIES (AND (IN ,var ORD) ,P) ,P-succ)))
                              (lim-goal  `(FORALL ,var (IMPLIES
                                                          (AND (LIMIT-ORD ,var) ,IH-limit)
                                                          ,P))))
                         (dg-apply-rule! dg 'transfinite-induction-3cases
                           (list (make-sequent asms (wff-child goal base-goal))
                                 (make-sequent asms (wff-child goal succ-goal))
                                 (make-sequent asms (wff-child goal lim-goal)))
                           sqn)))))))))

;;; -----------------------------------------------------------------------
;;; NN INDUCTION
;;;
;;; Goal must be (FORALL n (IMPLIES (IN n NN) body)).
;;; Splits into two subgoals:
;;;   base: body[n := 0]
;;;   step: (FORALL n (IMPLIES (IN n NN) (IMPLIES body body[n := (succ n)])))

(define (pi-nn-induction! sqn)
  (let* ((asms (sequent-node-assumptions sqn))
         (goal (sequent-node-assertion   sqn))
         (g    (wff-formula goal))
         (dg   (sqn-dg sqn)))
    (and (pair? g) (eq? (car g) 'FORALL)
         (let* ((n    (quantifier-var  g))
                (body (quantifier-body g)))
           (and (pair? body) (eq? (car body) 'IMPLIES)
                (let ((ante  (binary-left  body))
                      (inner (binary-right body)))
                  (and (pair? ante) (= (length ante) 3)
                       (eq? (car ante) 'IN)
                       (eq? (cadr ante) n)
                       (eq? (caddr ante) 'NN)
                       (let* ((base-g  (subst-free n 0 inner))
                              (inner-s (subst-free n `(succ ,n) inner))
                              (step-g  `(FORALL ,n
                                           (IMPLIES (IN ,n NN)
                                                    (IMPLIES ,inner ,inner-s)))))
                         (dg-apply-rule! dg 'nn-induction
                           (list (make-sequent asms (wff-child goal base-g))
                                 (make-sequent asms (wff-child goal step-g)))
                           sqn)))))))))

;;; -----------------------------------------------------------------------
;;; INTERSECTION MEMBERSHIP

(define (pi-intersection-intro! sqn)
  (let* ((asms (sequent-node-assumptions sqn))
         (goal (sequent-node-assertion   sqn))
         (g    (wff-formula goal))
         (dg   (sqn-dg sqn)))
    (and (pair? g) (eq? (car g) 'IN)
         (let ((x (cadr g)) (prod (caddr g)))
           (and (pair? prod) (eq? (car prod) 'INTERSECTION)
                (let ((sets (cdr prod)))
                  (dg-apply-rule! dg 'intersection-intro
                    (map (lambda (sset) (make-sequent asms (wff-child goal `(IN ,x ,sset)))) sets)
                    sqn)))))))

(define (pi-intersection-elim! sqn membership-formula k)
  ;; membership-formula: raw S-expression
  (let* ((asms (sequent-node-assumptions sqn))
         (goal (sequent-node-assertion   sqn))
         (dg   (sqn-dg sqn))
         (f    (asms-find asms membership-formula)))
    (and f
         (let ((raw-f (wff-formula f)))
           (and (pair? raw-f) (eq? (car raw-f) 'IN)
                (let ((x (cadr raw-f)) (prod (caddr raw-f)))
                  (and (pair? prod) (eq? (car prod) 'INTERSECTION)
                       (let ((sets (cdr prod)))
                         (and (integer? k) (>= k 1) (<= k (length sets))
                              (dg-apply-rule! dg `(intersection-elim ,k)
                                (list (make-sequent
                                        (context-add-assumption asms (wff-child f `(IN ,x ,(list-ref sets (- k 1)))))
                                        goal))
                                sqn))))))))))

;;; -----------------------------------------------------------------------
;;; D-7: SEPARATION (SEP), COMPREHENSION (COMP), IOTA, VNB-LAMBDA
;;;
;;; These constructors carry a SCHEMA in the body formula `p`/`body`, which
;;; cannot be expressed cleanly as a first-order axiom (the body would need
;;; to be a higher-order variable).  We characterise them at the kernel
;;; level instead.  See REVIEW.md D-7.

;;; -----------------------------------------------------------------------
;;; SEPARATION: SEP(x, A, p) = { x in A | p }
;;;
;;; pi-sep-sethood!:  goal (IN (SEP x A p) SET)  =>  subgoal (IN A SET)
;;; pi-sep-mem-intro!: goal (IN y (SEP x A p))   =>  subgoals (IN y A) and p[x:=y]
;;; pi-sep-mem-elim!: assumption (IN y (SEP x A p)) =>  context gains
;;;                   (IN y A) and p[x:=y]; assumption is removed.

(define (pi-sep-sethood! sqn)
  (let* ((asms (sequent-node-assumptions sqn))
         (goal (sequent-node-assertion   sqn))
         (g    (wff-formula goal))
         (dg   (sqn-dg sqn)))
    (and (pair? g) (eq? (car g) 'IN) (eq? (caddr g) 'SET)
         (let ((subj (cadr g)))
           (and (pair? subj) (eq? (car subj) 'SEP) (= (length subj) 4)
                (let ((A (caddr subj)))
                  (dg-apply-rule! dg 'sep-sethood
                    (list (make-sequent asms (wff-child goal `(IN ,A SET))))
                    sqn)))))))

(define (pi-sep-mem-intro! sqn)
  (let* ((asms (sequent-node-assumptions sqn))
         (goal (sequent-node-assertion   sqn))
         (g    (wff-formula goal))
         (dg   (sqn-dg sqn)))
    (and (pair? g) (eq? (car g) 'IN)
         (let ((y (cadr g)) (subj (caddr g)))
           (and (pair? subj) (eq? (car subj) 'SEP) (= (length subj) 4)
                (let ((x (cadr subj)) (A (caddr subj)) (p (cadddr subj)))
                  (dg-apply-rule! dg 'sep-mem-intro
                    (list (make-sequent asms (wff-child goal `(IN ,y ,A)))
                          (make-sequent asms (wff-child goal (subst-free x y p))))
                    sqn)))))))

(define (pi-sep-mem-elim! sqn membership-formula)
  (let* ((asms (sequent-node-assumptions sqn))
         (goal (sequent-node-assertion   sqn))
         (dg   (sqn-dg sqn))
         (f    (asms-find asms membership-formula)))
    (and f
         (let ((raw-f (wff-formula f)))
           (and (pair? raw-f) (eq? (car raw-f) 'IN)
                (let ((y (cadr raw-f)) (subj (caddr raw-f)))
                  (and (pair? subj) (eq? (car subj) 'SEP) (= (length subj) 4)
                       (let* ((x (cadr subj)) (A (caddr subj)) (p (cadddr subj))
                              (asms*  (context-remove-assumption asms f))
                              (asms** (context-add-assumption asms* (wff-child f `(IN ,y ,A))))
                              (asms***(context-add-assumption asms** (wff-child f (subst-free x y p)))))
                         (dg-apply-rule! dg 'sep-mem-elim
                           (list (make-sequent asms*** goal))
                           sqn)))))))))

;;; -----------------------------------------------------------------------
;;; COMPREHENSION: COMP(x, p) = { x | p }
;;;
;;; Members of any class are sets, so y in COMP(x,p) iff y in SET and p[x:=y].
;;;
;;; pi-comp-mem-intro!: goal (IN y (COMP x p))  =>  subgoals (IN y SET) and p[x:=y]
;;; pi-comp-mem-elim!:  assumption (IN y (COMP x p)) =>  context gains
;;;                     (IN y SET) and p[x:=y]; assumption is removed.

(define (pi-comp-mem-intro! sqn)
  (let* ((asms (sequent-node-assumptions sqn))
         (goal (sequent-node-assertion   sqn))
         (g    (wff-formula goal))
         (dg   (sqn-dg sqn)))
    (and (pair? g) (eq? (car g) 'IN)
         (let ((y (cadr g)) (subj (caddr g)))
           (and (pair? subj) (eq? (car subj) 'COMP) (= (length subj) 3)
                (let ((x (cadr subj)) (p (caddr subj)))
                  (dg-apply-rule! dg 'comp-mem-intro
                    (list (make-sequent asms (wff-child goal `(IN ,y SET)))
                          (make-sequent asms (wff-child goal (subst-free x y p))))
                    sqn)))))))

(define (pi-comp-mem-elim! sqn membership-formula)
  (let* ((asms (sequent-node-assumptions sqn))
         (goal (sequent-node-assertion   sqn))
         (dg   (sqn-dg sqn))
         (f    (asms-find asms membership-formula)))
    (and f
         (let ((raw-f (wff-formula f)))
           (and (pair? raw-f) (eq? (car raw-f) 'IN)
                (let ((y (cadr raw-f)) (subj (caddr raw-f)))
                  (and (pair? subj) (eq? (car subj) 'COMP) (= (length subj) 3)
                       (let* ((x (cadr subj)) (p (caddr subj))
                              (asms*  (context-remove-assumption asms f))
                              (asms** (context-add-assumption asms* (wff-child f `(IN ,y SET))))
                              (asms***(context-add-assumption asms** (wff-child f (subst-free x y p)))))
                         (dg-apply-rule! dg 'comp-mem-elim
                           (list (make-sequent asms*** goal))
                           sqn)))))))))

;;; -----------------------------------------------------------------------
;;; BIG-UNION: union over a family of sets.
;;;
;;; (BIG-UNION z A body) = union_{z in A} body  =  { x : exists z in A. x in body }
;;;
;;; The body is a class schema (z free in body), so as with SEP/COMP this
;;; cannot be a clean first-order axiom and lives at the kernel level.
;;;
;;; pi-big-union-sethood!:  goal (IN (BIG-UNION z A body) SET)
;;;                         =>  subgoals (IN A SET)
;;;                                  and (FORALL z (IMPLIES (IN z A) (IN body SET)))
;;; pi-big-union-mem-intro! sqn w:  goal (IN x (BIG-UNION z A body))
;;;                         =>  subgoals (IN w A) and (IN x body[z := w])
;;; pi-big-union-mem-elim! sqn f:  assumption (IN x (BIG-UNION z A body))
;;;                         =>  eigenvariable e; gains (IN e A) and
;;;                             (IN x body[z := e]); assumption removed.

(define (pi-big-union-sethood! sqn)
  (let* ((asms (sequent-node-assumptions sqn))
         (goal (sequent-node-assertion   sqn))
         (g    (wff-formula goal))
         (dg   (sqn-dg sqn)))
    (and (pair? g) (eq? (car g) 'IN) (eq? (caddr g) 'SET)
         (let ((subj (cadr g)))
           (and (pair? subj) (eq? (car subj) 'BIG-UNION) (= (length subj) 4)
                (let* ((z    (cadr subj))
                       (A    (caddr subj))
                       (body (cadddr subj))
                       ;; Rename z to a fresh name to avoid clashing with anything
                       ;; in A, the assumptions, or the goal.
                       (avoids (cons body (cons A (cons (wff-formula goal)
                                                        (map wff-formula asms)))))
                       (z*    (apply fresh-var z avoids))
                       (body* (subst-free z z* body))
                       (sethood `(FORALL ,z* (IMPLIES (IN ,z* ,A) (IN ,body* SET)))))
                  (dg-apply-rule! dg 'big-union-sethood
                    (list (make-sequent asms (wff-child goal `(IN ,A SET)))
                          (make-sequent asms (wff-child goal sethood)))
                    sqn)))))))

(define (pi-big-union-mem-intro! sqn witness)
  (let* ((asms (sequent-node-assumptions sqn))
         (goal (sequent-node-assertion   sqn))
         (g    (wff-formula goal))
         (dg   (sqn-dg sqn)))
    (and (pair? g) (eq? (car g) 'IN)
         (let ((x (cadr g)) (subj (caddr g)))
           (and (pair? subj) (eq? (car subj) 'BIG-UNION) (= (length subj) 4)
                (let* ((z    (cadr subj))
                       (A    (caddr subj))
                       (body (cadddr subj))
                       (body-w (subst-free z witness body))
                       (mem-x  `(IN ,x ,body-w)))
                  (validate-wff! mem-x)   ; reject malformed witness early
                  (dg-apply-rule! dg 'big-union-mem-intro
                    (list (make-sequent asms (wff-child goal `(IN ,witness ,A)))
                          (make-sequent asms (wff-child goal mem-x)))
                    sqn)))))))

(define (pi-big-union-mem-elim! sqn membership-formula)
  (let* ((asms (sequent-node-assumptions sqn))
         (goal (sequent-node-assertion   sqn))
         (dg   (sqn-dg sqn))
         (f    (asms-find asms membership-formula)))
    (and f
         (let ((raw-f (wff-formula f)))
           (and (pair? raw-f) (eq? (car raw-f) 'IN)
                (let ((x (cadr raw-f)) (subj (caddr raw-f)))
                  (and (pair? subj) (eq? (car subj) 'BIG-UNION) (= (length subj) 4)
                       (let* ((z    (cadr subj))
                              (A    (caddr subj))
                              (body (cadddr subj))
                              (asms* (context-remove-assumption asms f))
                              ;; Eigenvariable must avoid other assumptions, goal,
                              ;; A, body, x.
                              (avoids (cons (wff-formula goal)
                                            (cons A (cons body (cons x
                                              (map wff-formula asms*))))))
                              (e     (apply fresh-var z avoids))
                              (body-e (subst-free z e body))
                              (asms**  (context-add-assumption asms* (wff-child f `(IN ,e ,A))))
                              (asms*** (context-add-assumption asms** (wff-child f `(IN ,x ,body-e)))))
                         (dg-apply-rule! dg 'big-union-mem-elim
                           (list (make-sequent asms*** goal))
                           sqn)))))))))

;;; -----------------------------------------------------------------------
;;; IOTA: definite description (IOTA x p) = the unique x with p(x).
;;;
;;; pi-iota-def! takes an IOTA term as input and posts two subgoals:
;;;   (1) FORSOME-UNIQUE x p  --  the existence-and-uniqueness obligation,
;;;       written explicitly as (FORSOME x (AND p (FORALL y (IMPLIES p[x:=y] (= x y)))))
;;;   (2) the original goal with the defining property p[x := (IOTA x p)]
;;;       added as an assumption, so the user can use it.

(define (pi-iota-def! sqn iota-term)
  (let* ((asms (sequent-node-assumptions sqn))
         (goal (sequent-node-assertion   sqn))
         (dg   (sqn-dg sqn)))
    (and (pair? iota-term) (eq? (car iota-term) 'IOTA) (= (length iota-term) 3)
         (symbol? (cadr iota-term))
         (let* ((x (cadr iota-term))
                (p (caddr iota-term))
                (avoids (cons (wff-formula goal)
                              (cons iota-term (map wff-formula asms))))
                (y      (apply fresh-var x p avoids))
                (p-y    (subst-free x y p))
                (uniq   `(FORALL ,y (IMPLIES ,p-y (= ,x ,y))))
                (exuniq `(FORSOME ,x (AND ,p ,uniq)))
                (defprop (subst-free x iota-term p)))
           (validate-wff! exuniq)
           (validate-wff! defprop)
           (dg-apply-rule! dg 'iota-def
             (list (make-sequent asms (wff-child goal exuniq))
                   (make-sequent (context-add-assumption asms (wff-child goal defprop))
                                 goal))
             sqn)))))

;;; -----------------------------------------------------------------------
;;; IOTA, THE OTHER DIRECTION: a description that DENOTES satisfies its
;;; property.  (pi-iota-in-elim!, tactic `iota-e'.)
;;;
;;;     context establishes (IOTA x p) defined
;;;     ---------------------------------------
;;;     context gains  p[x := (IOTA x p)]
;;;
;;; ADDED 2026-09-15 ON THE USER'S DECISION.  It enlarges the trusted base, so
;;; the argument is written here rather than assumed.
;;;
;;; WHY IT WAS MISSING AND WHAT IT COST.  `iota-def' above runs ONE way: post
;;; the existence-and-uniqueness obligation, then grant the defining property.
;;; Nothing let a proof go the other way -- from "this description denotes" to
;;; "so it satisfies its property".  That gap blocked the vector Taylor arc:
;;; TAYLOR-DIFFERENTIABLE-V's continuity conjunct says every NTH-DERIV-V is a
;;; total map into VEC(m), i.e. that the IOTA `DERIV-V(m, f^(k-1), x)' DENOTES
;;; everywhere, which IS the differentiability `gof-nth-deriv' needs -- and the
;;; kernel could not use it.
;;;
;;; WHY IT IS SOUND, on VNB's own reading of partiality.  `=' is the definedness
;;; predicate and atomic formulas are STRICT, so a true `(IN t X)' entails that
;;; t denotes.  The kernel already commits to exactly that: pi-reflexivity!
;;; closes `t = t' when the context carries `(IN t _)' or `(= t _)', by
;;; asm-establishes-defined? (:627).  So this rule adds no new reading of
;;; definedness -- it REUSES that predicate, which is why it calls it rather
;;; than testing the assumption shape itself; the two cannot drift apart.
;;; Given that (IOTA x p) denotes, it denotes THE unique x satisfying p -- that
;;; is what a definite description means, and it is the same semantics
;;; `iota-def' already relies on when it grants defprop after existence and
;;; uniqueness are proved.  The difference is only in what discharges the
;;; obligation: there a proof, here the context.
;;;
;;; WHAT IT DOES NOT LICENSE: nothing about an IOTA the context says nothing
;;; about.  With no definedness witness the rule declines (returns #f) -- it
;;; never assumes denotation, which is the whole point of a partial logic.
(define (pi-iota-in-elim! sqn iota-term)
  (let* ((asms (sequent-node-assumptions sqn))
         (goal (sequent-node-assertion   sqn))
         (dg   (sqn-dg sqn)))
    (and (pair? iota-term) (eq? (car iota-term) 'IOTA) (= (length iota-term) 3)
         (symbol? (cadr iota-term))
         ;; the ONLY premise: the context says this description denotes.
         (asm-establishes-defined? asms iota-term)
         (let* ((x       (cadr iota-term))
                (p       (caddr iota-term))
                (defprop (subst-free x iota-term p)))
           (validate-wff! defprop)
           (dg-apply-rule! dg 'iota-in-elim
             (list (make-sequent (context-add-assumption asms (wff-child goal defprop))
                                 goal))
             sqn)))))

;;; -----------------------------------------------------------------------
;;; VNB-LAMBDA: typing and beta reduction (symbolic form).
;;;
;;; pi-lambda-type!: goal (IN (VNB-LAMBDA <bind-spec> A body) (FUN A B))
;;;                  =>  TWO subgoals:
;;;                        (IN A SET)
;;;                        (FORALL x (IMPLIES (IN x A) (IN body B)))
;;;
;;; UNSOUND UNTIL 2026-08-02, in two independent ways, both now closed.
;;;
;;; (1) The lambda did not carry a domain, so the rule's A was free to vary over
;;;     one and the same term: the subgoal `forall x in A. body in B' is a
;;;     tautology for the identity, so (VNB-LAMBDA x x) was certified into
;;;     FUN(A,A) for EVERY A.  fun-domain-apply-def says a member of FUN(A) is
;;;     defined EXACTLY on A, so two domains for one term is a contradiction:
;;;     taking A = NN and A = EMPTY-SET proved (IN 0 EMPTY-SET) modulo 0.
;;;     Closed by requiring the term to DECLARE its domain and matching it
;;;     against the FUN's -- the same discipline SEP and BIG-UNION already had.
;;;
;;; (2) Membership in FUN(A,B) implies sethood (membership-implies-sethood), and
;;;     a class function on a proper-class domain is a proper class.  The rule
;;;     had no sethood obligation, so it certified (VNB-LAMBDA x ORD x) into
;;;     FUN(ORD,ORD) with ORD a proper class (burali-forti).  Closed by the
;;;     (IN A SET) subgoal.  NOTE this half is NOT fixed by (1): the domain
;;;     being declared says nothing about its being a set.
;;;
;;; The typing subgoal comes FIRST so the focus lands where the pre-existing
;;; drivers expect it; the sethood subgoal is the one they must now also close
;;; (rr-is-set / nn-is-set are primitive, interval-in-set is a PSS support).
;;; See docs/lambda-domain.md.
;;;
;;;   Multi-binder shape (VNB-LAMBDA (LIST x1 ... xn) A body):
;;;     A is then the CARTESIAN product and B the codomain; still not handled
;;;     here.  Carrying the domain is what makes that case tractable at all --
;;;     it is the blocker on IS-METRIC-SPACE(RR-MS), whose DIST is a two-binder
;;;     lambda -- but it is deliberately left for a separate change.
;;;
;;; pi-lambda-beta!: rewrite ((VNB-LAMBDA <bind-spec> body) arg ...) anywhere
;;;                  in the goal to body[bvars := args] (parallel substitution).

;;; The pointwise typing subgoal for a binder spec.  ONE subgoal either way:
;;;
;;;   single binder   forall x. x in A => body in B
;;;   binder LIST     forall x_1 ... x_n. x_1 in A_1 => ... => x_n in A_n
;;;                                       => body in B
;;;
;;; MULTI-BINDER, added 2026-08-14.  The rule required `(symbol? (cadr subj))',
;;; so a lambda of two variables could be written and could not be typed --
;;; while `pi--binder-scope' in this same file already reads a binder list
;;; componentwise against a CARTESIAN domain, and `reduce-lambda-in-expr' already
;;; beta-reduces such a lambda applied to n arguments.  The reading was decided;
;;; only the typing rule had not been told.  So this is not a new commitment:
;;; it makes lambda-type agree with lambda-beta, which is the condition under
;;; which the two rules are about the same object.
;;;
;;; The domain must be CARTESIAN of exactly n factors.  That is what makes the
;;; componentwise quantification equivalent to quantifying over the product: an
;;; element of CARTESIAN(A_1..A_n) IS a tuple of members (cartesian-decompose),
;;; and `apply-tupling-n' (axioms.scm) equates (f a_1 .. a_n) with (f [a_1..a_n]),
;;; so the function this term denotes on the product is exactly the one whose
;;; value at a tuple is the body.  A binder list against a non-CARTESIAN domain,
;;; or a length mismatch, is REFUSED rather than guessed at.
(define (pi--lambda-type-subgoal bind-spec A body B avoid-base)
  (cond
    ((symbol? bind-spec)
     (let* ((x*    (apply fresh-var bind-spec avoid-base))
            (body* (subst-free bind-spec x* body)))
       `(FORALL ,x* (IMPLIES (IN ,x* ,A) (IN ,body* ,B)))))
    ((and (pair? bind-spec) (eq? (car bind-spec) 'LIST)
          (pair? A) (eq? (car A) 'CARTESIAN)
          (= (length (cdr bind-spec)) (length (cdr A)))
          (pair? (cdr bind-spec)))
     (let ((doms (cdr A)))
       ;; freshen the binders left to right, substituting as we go, then wrap
       ;; the typed body in one guarded FORALL per component
       ;; NB `bod', not `b': MIT folds symbols, so a loop variable named `b'
       ;; IS the parameter `B' -- the codomain -- and the innermost subgoal came
       ;; out as (IN body body).  The case-fold trap, inside a patch to the file
       ;; whose header warns about it.
       (let loop ((vs (cdr bind-spec)) (fresh '()) (bod body))
         (if (null? vs)
             (let build ((fs (reverse fresh)) (ds doms))
               (if (null? fs)
                   `(IN ,bod ,B)
                   `(FORALL ,(car fs)
                      (IMPLIES (IN ,(car fs) ,(car ds))
                               ,(build (cdr fs) (cdr ds))))))
             (let* ((v*   (apply fresh-var (car vs) (append fresh avoid-base)))
                    (bod* (subst-free (car vs) v* bod)))
               (loop (cdr vs) (cons v* fresh) bod*))))))
    (else #f)))

(define (pi-lambda-type! sqn)
  (let* ((asms (sequent-node-assumptions sqn))
         (goal (sequent-node-assertion   sqn))
         (g    (wff-formula goal))
         (dg   (sqn-dg sqn)))
    (and (pair? g) (eq? (car g) 'IN)
         (let ((subj (cadr g)) (cls (caddr g)))
           (and (pair? subj) (eq? (car subj) 'VNB-LAMBDA) (= (length subj) 4)
                (pair? cls) (eq? (car cls) 'FUN) (= (length cls) 3)
                ;; THE SOUNDNESS CONDITION: the domain the term declares must be
                ;; the domain the FUN claims.  Without it one term types into
                ;; FUN(A,B) for every A -- see the header.
                (alpha-equiv? (caddr subj) (cadr cls))
                (let* ((A    (cadr cls))
                       (body (cadddr subj))
                       (B    (caddr cls))
                       (avoids (cons body (cons A (cons B (map wff-formula asms)))))
                       (sub-goal (pi--lambda-type-subgoal (cadr subj) A body B avoids))
                       (set-goal `(IN ,A SET)))
                  (and sub-goal
                       (dg-apply-rule! dg 'lambda-type
                         (list (make-sequent asms (wff-child goal sub-goal))
                               (make-sequent asms (wff-child goal set-goal)))
                         sqn))))))))

(define (pi-lambda-beta! sqn)
  (let* ((asms (sequent-node-assumptions sqn))
         (goal (sequent-node-assertion   sqn))
         (g    (wff-formula goal))
         (dg   (sqn-dg sqn)))
    (let* ((owed '())
           (new-g (reduce-lambda-in-expr/guard
                    g (lambda (args A scope bvars)
                        (or (pi--beta-licensed?
                              (append scope (pi--unshadowed bvars asms)) args A)
                            (let ((ob (pi--beta-obligation args A)))
                              ;; an obligation naming a variable bound where the
                              ;; redex sits would be read in the parent's context,
                              ;; about another variable: refuse the redex instead
                              (and (not (pi--mentions-any? bvars ob))
                                   (begin
                                     (if *lambda-beta-emit-obligations?*
                                         (set! owed (cons ob owed))
                                         (begin
                                           (display ";VNB BETA-GUARD (not enforced): args=")
                                           (write args) (display " A=") (write A) (newline)))
                                     #t))))))))
      (if (alpha-equiv? new-g g)
          #f
          ;; Main subgoal plus one (IN u A) obligation per redex whose licence
          ;; was not evident -- sep-mem-intro's discipline, not a refusal.
          (dg-apply-rule! dg 'lambda-beta
            (cons (make-sequent asms (wff-child goal new-g))
                  (map (lambda (o) (make-sequent asms (wff-child goal o)))
                       (reverse owed)))
            sqn)))))

;;; pi-lambda-beta-hyp!: the same reduction, on a cited ASSUMPTION.
;;;
;;; `mac' has `mac-h'; `lam-b' had nothing, and the gap is not cosmetic.  A `fact'
;;; that instantiates a theorem's function variable at a lambda LANDS the applied
;;; lambda in the context -- union-of-opens-open at the identity family g := \x.x
;;; lands IS-OPEN(md, BIG-UNION(i, fam, (\x.x)(i))) -- and with only a goal-side
;;; beta the proof must detour: cut the beta-equation, lam-b IT, subst it into the
;;; goal.  (metric-top-proof.scm did exactly that.)  Here the assumption is simply
;;; reduced in place.
;;;
;;; Sound for the same reason lambda-beta is: the new assumption is beta-equal to
;;; the old one, so the context is unchanged as a set of propositions.  It cites
;;; nothing, so it adds no debt (proof-debt bills the *citing* verbs).
(define (pi-lambda-beta-hyp! sqn hyp-formula)
  (let* ((asms (sequent-node-assumptions sqn))
         (goal (sequent-node-assertion   sqn))
         (dg   (sqn-dg sqn))
         (f    (asms-find asms hyp-formula)))
    (and f
         (let* ((h     (wff-formula f))
                (owed '())
                (new-h (reduce-lambda-in-expr/guard
                         h (lambda (args A scope bvars)
                             (or (pi--beta-licensed?
                                   (append scope (pi--unshadowed bvars asms)) args A)
                                 (let ((ob (pi--beta-obligation args A)))
                                   (and (not (pi--mentions-any? bvars ob))
                                        (begin
                                          (if *lambda-beta-emit-obligations?*
                                              (set! owed (cons ob owed))
                                              (begin
                                                (display ";VNB BETA-GUARD (not enforced): args=")
                                                (write args) (display " A=") (write A) (newline)))
                                          #t))))))))
           (and (not (alpha-equiv? new-h h))
                (dg-apply-rule! dg 'lambda-beta-hyp
                  (cons (make-sequent
                          (context-add-assumption
                            (context-remove-assumption asms f)
                            (wff-child f new-h))
                          goal)
                        (map (lambda (o) (make-sequent asms (wff-child f o)))
                             (reverse owed)))
                  sqn))))))

;;; pi--beta-licensed?: may this redex fire?
;;;
;;; (VNB-LAMBDA x A b) is the function with domain A, so (lam u) is DEFINED only
;;; for u in A -- fun-domain-apply-def says exactly that once the lambda is typed.
;;; Reducing off-domain therefore proves defined a term the theory calls
;;; undefined: with A = EMPTY-SET it gives (= ((VNB-LAMBDA x EMPTY-SET 0) 0) 0)
;;; modulo 0, against empty-set-has-no-members.  That is the 2026-08-02 lambda
;;; unsoundness surviving in the APPLICATION rule after it was closed in the
;;; TYPING rule.  So beta must see the membership.  (scratchpad/lambda-beta-guard.scm)
;;;
;;; A licence is EVIDENT when the membership is in the context or in the scope
;;; the walker threaded down (enclosing guarded universals, and the domain of
;;; any enclosing VNB-LAMBDA / SEP / BIG-UNION binder).  Evident licences leave
;;; the leaf structure exactly as it was, so a licensed reduction costs nothing.
;;;
;;; ENFORCING since 2026-08-03.  When the licence is not evident the redex still
;;; FIRES -- refusing is a dead end for a driver, an obligation is a path -- but
;;; it OWES (IN u A) as an extra subgoal, sep-mem-intro's discipline.  So an
;;; off-domain reduction no longer proves anything: the exploit shape
;;;   (= ((VNB-LAMBDA x EMPTY-SET 0) 0) 0)     [the 2026-08-02 unsoundness,
;;;                                             surviving in the APPLICATION
;;;                                             rule after the TYPING rule was
;;;                                             closed by carrying the domain]
;;; now owes (IN 0 EMPTY-SET), which is the false thing itself, and the leaf
;;; stays open.  Control: scratchpad/beta-guard-control.scm, three cases --
;;; unlicensed owes, licensed does not, exploit owes.  Run it after touching
;;; this code: a guard that never fires is indistinguishable from a clean tree.
;;;
;;; #f restores the old REPORT mode -- fires and merely prints the redex.  It is
;;; unsound, and it exists only because it was how the worklist was collected:
;;; a whole load yields the whole list, where an enforcing guard yields the
;;; first entry and a broken proof.  Use it to survey, never to ship.  The
;;; survey it produced ran 39 -> 0 on 2026-08-03; the "it stalls the load"
;;; note that stood here was a symptom of those 39, not a property of
;;; enforcement -- with nothing unlicensed, nothing is emitted and the load is
;;; the same 47 s it always was.
(define *lambda-beta-emit-obligations?* #t)   ; sound; see the note above

;;; The obligation a redex owes when its licence is not evident: (IN u A), or
;;; (IN (LIST u1..un) A) for the multi-binder form.
(define (pi--beta-obligation args A)
  (if (= (length args) 1)
      (list 'IN (car args) A)
      (list 'IN (cons 'LIST args) A)))

(define (pi--beta-licensed? asms args A)
  (define (mem? a dom)
    (let ((want (list 'IN a dom)))
      (let loop ((w asms))
        (cond ((null? w) #f)
              ;; asms are wff objects; scope entries are raw formulas
              ((alpha-equiv? (let ((e (car w))) (if (wff? e) (wff-formula e) e))
                             want) #t)
              (else (loop (cdr w)))))))
  ;; componentwise against a CARTESIAN domain: (IN a_i d_i) for every factor.
  (define (componentwise as ds)
    (let loop ((as as) (ds ds))
      (or (null? as)
          (and (mem? (car as) (car ds)) (loop (cdr as) (cdr ds))))))
  (define (cartesian-of? A n)
    (and (pair? A) (eq? (car A) 'CARTESIAN) (= (length (cdr A)) n)))
  (cond ((= (length args) 1)
         (or (mem? (car args) A)
             ;; The TUPLED spelling: one argument that is itself a (LIST a b),
             ;; which is how a fubini-style summand applies a 2-binder lambda
             ;; -- (FF (LIST c j)), triple-entry-proof.scm:55.  Licensed by the
             ;; same componentwise membership as the multi-argument spelling;
             ;; refusing it here while accepting `(FF c j)' would be a
             ;; distinction in the SYNTAX of the application, not in what is
             ;; being reduced.
             (let ((u (car args)))
               (and (pair? u) (eq? (car u) 'LIST)
                    (cartesian-of? A (length (cdr u)))
                    (componentwise (cdr u) (cdr A))))))
        ;; multi-binder: the domain is the CARTESIAN of the factor domains, so
        ;; componentwise membership licenses the tuple.
        ((cartesian-of? A (length args)) (componentwise args (cdr A)))
        (else (mem? (cons 'LIST args) A))))

;;; reduce-lambda-in-expr: parallel beta reduction of any
;;; ((VNB-LAMBDA <bind-spec> A body) arg ...) anywhere in expr.
;;; Single- and multi-binder forms both supported.  Recurses into all subterms.
;;;
;;; `ok?' decides per redex whether it may fire, as (ok? args A).  The bare
;;; one-argument entry point keeps the unguarded behaviour and is for pure TERM
;;; manipulation (the test suite); the kernel rules below always pass a guard.
(define (reduce-lambda-in-expr expr)
  (reduce-lambda-in-expr/guard expr (lambda (args A scope bvars) #t)))

(define (reduce-lambda-in-expr/guard expr ok?)
  (reduce-lambda-in-expr/scope expr ok? '() '()))

;;; `scope' carries the memberships that hold WHERE THE REDEX SITS, gathered from
;;; enclosing guarded universals.  Without this the guard sees only the context
;;; and refuses redexes under `forall u in A. ... (lam u) ...' -- where u's
;;; membership is a guard IN THE GOAL, not an assumption.  That shape is the
;;; normal one: a driver that unfolds a law and beta-reduces before introducing
;;; the binders (mat-ring-proof's mr-rops does exactly this) has every membership
;;; available and none of them in the context.
;;; The memberships a lambda BINDER contributes inside its own body.  Inside
;;; (VNB-LAMBDA x A body) the variable x ranges over A -- that is what carrying
;;; the domain MEANS, and it is the reading pi-lambda-type! already takes when it
;;; reduces (IN lam (FUN A B)) to (FORALL x (IMPLIES (IN x A) (IN body B))).
;;; Multi-binder: the domain is a CARTESIAN, so componentwise.
;;;
;;; What this licenses is reduction UNDER a binder, which needs congruence:
;;; (VNB-LAMBDA x A b1) and (VNB-LAMBDA x A b2) are the same term when b1 = b2
;;; for every x in A.  Under the graph reading of the lambda -- the reading the
;;; domain-carrying repair is built on, and the one lam-t enforces -- that is
;;; immediate, since the two terms then have the same graph.  It is NOT an extra
;;; axiom about arbitrary function equality: the domains must be the same term,
;;; because `mem?' below matches the membership formula up to alpha only.
(define (pi--binder-scope bind-spec A)
  (cond ((symbol? bind-spec) (list (list 'IN bind-spec A)))
        ((and (pair? bind-spec) (eq? (car bind-spec) 'LIST)
              (pair? A) (eq? (car A) 'CARTESIAN)
              (= (length (cdr bind-spec)) (length (cdr A))))
         (map (lambda (v d) (list 'IN v d)) (cdr bind-spec) (cdr A)))
        (else '())))

;;; THE SHADOWING RULE (2026-09-20, batch 11-C).  `scope' and the sequent's
;;; ASSUMPTIONS both speak about the variables in scope AT THE ROOT of the
;;; formula.  Under a binder that re-binds one of those names the same formula
;;; is about a DIFFERENT variable and may license nothing there.  Until this was
;;; written the walker carried both straight through every binder, and
;;;
;;;   forall u in NN. forall u in ZZ. (lambda z_ in NN. z_)(u) = u
;;;
;;; -- FALSE, the lambda being undefined at u = -1 -- beta-reduced to
;;; `u = u' on the strength of the OUTER guard, closed by `rfl', and installed
;;; `modulo 0' with inference checking on; FALSITY followed in twenty lines
;;; (scratchpad/binder-gate/exploit-falsity.scm).  It is the BIG-UNION
;;; local-context hole of the same morning, one storey down, in a kernel rule.
;;;
;;; `bvars' is the list of variables bound between the root and the point the
;;; walk has reached.  Going down, the scope entries they shadow are dropped;
;;; at the licence test the guard drops the ASSUMPTIONS they shadow (see
;;; pi-lambda-beta!).  The OBLIGATION obeys the same rule: `(IN u A)' posted in
;;; the parent's context, with `u' bound HERE, is not the proposition the redex
;;; owes -- it is a formula about the outer `u', which an assumption of that
;;; name would then discharge.  Such a redex is left UNREDUCED instead.
(define (pi--bspec-vars bs)
  (cond ((symbol? bs) (list bs))
        ((and (pair? bs) (eq? (car bs) 'LIST)) (filter symbol? (cdr bs)))
        (else '())))

(define (pi--mentions-any? vars e)
  (and (pair? vars)
       (let ((fvs (free-vars e)))
         (any (lambda (v) (memq v fvs)) vars))))

;;; The formulas of FS that say nothing about a variable bound at the point of
;;; use.  FS may hold raw formulas (scope) or wff records (assumptions).
(define (pi--unshadowed bvars fs)
  (if (null? bvars)
      fs
      (filter (lambda (f)
                (not (pi--mentions-any? bvars (if (wff? f) (wff-formula f) f))))
              fs)))

(define (reduce-lambda-in-expr/scope expr ok? scope bvars)
  (define (reduce-lambda-in-expr e) (reduce-lambda-in-expr/scope e ok? scope bvars))
  ;; Descending under a binder: drop what its variables shadow, add what they grant.
  (define (reduce-under vs extra e)
    (reduce-lambda-in-expr/scope e ok?
                                 (append extra (pi--unshadowed vs scope))
                                 (append vs bvars)))
  ;; the body of (VNB-LAMBDA bs A .) is walked with bs's memberships added
  (define (reduce-in-body bs A e)
    (reduce-under (pi--bspec-vars bs) (pi--binder-scope bs A) e))
  (define (ok?* args A) (ok? args A scope bvars))
  (cond
    ;; (FORALL v (IMPLIES (IN v A) body)) -- v's membership holds inside body.
    ((and (pair? expr) (eq? (car expr) 'FORALL) (= (length expr) 3)
          (pair? (caddr expr)) (eq? (car (caddr expr)) 'IMPLIES)
          (= (length (caddr expr)) 3)
          (let ((h (cadr (caddr expr))))
            (and (pair? h) (eq? (car h) 'IN) (eq? (cadr h) (cadr expr)))))
     (let* ((v    (cadr expr))
            (imp  (caddr expr))
            (hyp  (cadr imp))
            (body (caddr imp)))
       ;; the guard and the body are BOTH under the binder: v shadows there.
       (list 'FORALL v
             (list 'IMPLIES (reduce-under (list v) '() hyp)
                   (reduce-under (list v) (list hyp) body)))))
    ((not (pair? expr)) expr)
    ;; ((VNB-LAMBDA x body) arg)  — single-binder, single-arg.
    ((and (pair? (car expr))
          (eq? (caar expr) 'VNB-LAMBDA)
          (= (length (car expr)) 4)
          (symbol? (cadar expr))
          (= (length expr) 2))
     (let* ((x    (cadar expr))
            (A    (caddr (car expr)))
            (body (reduce-in-body (cadar expr) (caddr (car expr))
                                  (cadddr (car expr))))
            (arg  (reduce-lambda-in-expr (cadr expr))))
       (if (ok?* (list arg) A)
           (subst-free x arg body)
           ;; not licensed: leave the redex alone, but still normalise inside it
           (list (list 'VNB-LAMBDA x A body) arg))))
    ;; ((VNB-LAMBDA (LIST x1 ... xn) body) arg1 ... argn)  — multi-binder, parallel.
    ((and (pair? (car expr))
          (eq? (caar expr) 'VNB-LAMBDA)
          (= (length (car expr)) 4)
          (pair? (cadar expr))
          (eq? (car (cadar expr)) 'LIST)
          (= (length (cdr (cadar expr))) (length (cdr expr))))
     (let* ((bvars  (cdr (cadar expr)))
            (body   (reduce-in-body (cadar expr) (caddr (car expr))
                                    (cadddr (car expr))))
            (args   (map reduce-lambda-in-expr (cdr expr)))
            (avoids (cons body args))
            (fresh  (map (lambda (bv) (apply fresh-var bv avoids)) bvars))
            ;; First rename bvars -> fresh; then substitute fresh -> args.
            ;; Freshness guarantees no later subst rewrites an earlier insertion.
            (renamed (fold-left (lambda (b pair)
                                  (subst-free (car pair) (cdr pair) b))
                                body
                                (map cons bvars fresh)))
            (final   (fold-left (lambda (b pair)
                                  (subst-free (car pair) (cdr pair) b))
                                renamed
                                (map cons fresh args))))
       (if (ok?* args (caddr (car expr)))
           final
           (cons (list 'VNB-LAMBDA (cadar expr) (caddr (car expr)) body) args))))
    ;; The domain-carrying binders, all of shape (H v A body) with A OUTSIDE the
    ;; binder's scope (SEP, BIG-UNION, VNB-LAMBDA -- whatever *binder-shapes*
    ;; declares `domain' or `lambda'): a lambda sitting in the goal as a term
    ;; rather than in operator position, a separation, an indexed union.  Inside
    ;; the body the bound variable is in A, so a redex there is licensed by that.
    ;; Each is extensional over its domain -- {v in A : p}, UNION_{v in A} b and
    ;; the lambda's graph all depend on the body only through its values on A --
    ;; so reducing under the binder leaves the same term.  Without this case the
    ;; walker descends through the generic branch below and drops the membership
    ;; on the floor.  DRIVEN FROM *binder-shapes* since 2026-09-20: a binder
    ;; declared there and forgotten here is what `binder-walker-audit' now fails
    ;; on, and this walker has no second list to forget it in.
    ((and (symbol? (car expr)) (memq (binder-shape (car expr)) '(domain lambda))
          (= (length expr) 4))
     (list (car expr) (cadr expr)
           (reduce-lambda-in-expr (caddr expr))
           (reduce-in-body (cadr expr) (caddr expr) (cadddr expr))))
    ;; The simple binders (H v body): an UNGUARDED FORALL, FORSOME, IOTA, COMP.
    ;; They grant nothing, but they SHADOW, and until 2026-09-20 they were not
    ;; here at all -- the generic branch below carried the outer scope and the
    ;; context under them.  See THE SHADOWING RULE above.
    ((and (symbol? (car expr)) (eq? 'simple (binder-shape (car expr)))
          (= (length expr) 3) (symbol? (cadr expr)))
     (list (car expr) (cadr expr)
           (reduce-under (list (cadr expr)) '() (caddr expr))))
    (else
     (cons (reduce-lambda-in-expr (car expr))
           (map reduce-lambda-in-expr (cdr expr))))))

;; No second list: the walker asks `binder-shape' (expressions.scm) which heads
;; bind and with what shape, so a binder added to *binder-shapes* is handled
;; here with no edit -- and shadows the scope and the context, as it must.
(declare-binder-walker! 'reduce-lambda-in-expr/scope 'from-binder-shapes)
