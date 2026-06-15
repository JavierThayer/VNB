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
             (y     (apply fresh-var x body raw-goal
                           (append added ambient-avoids)))
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
                  (dg-apply-rule! dg 'forall-elim
                    (list (make-sequent (context-add-assumption asms (wff-child f inst)) goal))
                    sqn)))))))

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
               ((FORALL FORSOME IOTA)
                (if (memq (cadr e) danger)
                    e
                    (list (car e) (cadr e) (walk (caddr e)))))
               ((SEP BIG-UNION)
                (if (memq (cadr e) danger)
                    e
                    (list (car e) (cadr e) (walk (caddr e)) (walk (cadddr e)))))
               ((VNB-LAMBDA)
                (if (captures? (vnb-lambda-bvars (cadr e)))
                    e
                    (list 'VNB-LAMBDA (cadr e) (walk (caddr e)))))
               ((NTH)
                (list 'NTH (cadr e) (walk (caddr e))))
               (else
                (cons (car e) (map walk (cdr e)))))))))))

;;; pi-eq-subst!: eq-formula is a raw (= s t).  The equality must appear in
;;; the assumptions in either orientation; the goal is rewritten s -> t.
(define (pi-eq-subst! sqn eq-formula)
  (and (pair? eq-formula) (eq? (car eq-formula) '=)
       (let* ((asms (sequent-node-assumptions sqn))
              (goal (sequent-node-assertion   sqn))
              (dg   (sqn-dg sqn))
              (s    (binary-left  eq-formula))
              (t    (binary-right eq-formula)))
         (and (or (asms-find asms `(= ,s ,t))
                  (asms-find asms `(= ,t ,s)))
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

(define (pi-reflexivity! sqn)
  (let* ((goal (sequent-node-assertion sqn))
         (g    (wff-formula goal))
         (dg   (sqn-dg sqn)))
    (if (or (eq? g 'TRUTH)
            (and (pair? g) (eq? (car g) '=)
                 (alpha-equiv? (cadr g) (caddr g))))
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
;;;                                    (FORALL beta (IMPLIES (<_ORD beta var) P[var:=beta])))
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
                              (IH     `(FORALL ,beta (IMPLIES (<_ORD ,beta ,var) ,P-beta)))
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
;;;                                 (FORALL beta (IMPLIES (<_ORD beta var) P[var:=beta])))
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
                              (IH-limit  `(FORALL ,beta (IMPLIES (<_ORD ,beta ,var) ,P-beta)))
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
;;; VNB-LAMBDA: typing and beta reduction (symbolic form).
;;;
;;; pi-lambda-type!: goal (IN (VNB-LAMBDA <bind-spec> body) (FUN A B))
;;;                  =>  subgoal asserting body has type B for each bvar in A.
;;;   Single-binder shape: (FORALL x (IMPLIES (IN x A) (IN body B)))
;;;   Multi-binder shape (VNB-LAMBDA (LIST x1 ... xn) body):
;;;     codomain is (FUN (CARTESIAN A1 ... An) B); not handled here — for now
;;;     only single-binder lambdas use this rule.
;;;
;;; pi-lambda-beta!: rewrite ((VNB-LAMBDA <bind-spec> body) arg ...) anywhere
;;;                  in the goal to body[bvars := args] (parallel substitution).

(define (pi-lambda-type! sqn)
  (let* ((asms (sequent-node-assumptions sqn))
         (goal (sequent-node-assertion   sqn))
         (g    (wff-formula goal))
         (dg   (sqn-dg sqn)))
    (and (pair? g) (eq? (car g) 'IN)
         (let ((subj (cadr g)) (cls (caddr g)))
           (and (pair? subj) (eq? (car subj) 'VNB-LAMBDA) (= (length subj) 3)
                (symbol? (cadr subj))
                (pair? cls) (eq? (car cls) 'FUN) (= (length cls) 3)
                (let* ((x    (cadr subj))
                       (body (caddr subj))
                       (A    (cadr cls))
                       (B    (caddr cls))
                       ;; Rename x to a fresh name to avoid clashing with
                       ;; anything in A, B, asms, or the goal.
                       (avoids (cons body (cons A (cons B (map wff-formula asms)))))
                       (x*   (apply fresh-var x avoids))
                       (body*(subst-free x x* body))
                       (sub-goal `(FORALL ,x* (IMPLIES (IN ,x* ,A) (IN ,body* ,B)))))
                  (dg-apply-rule! dg 'lambda-type
                    (list (make-sequent asms (wff-child goal sub-goal)))
                    sqn)))))))

(define (pi-lambda-beta! sqn)
  (let* ((asms (sequent-node-assumptions sqn))
         (goal (sequent-node-assertion   sqn))
         (g    (wff-formula goal))
         (dg   (sqn-dg sqn)))
    (let ((new-g (reduce-lambda-in-expr g)))
      (if (alpha-equiv? new-g g)
          #f
          (dg-apply-rule! dg 'lambda-beta
            (list (make-sequent asms (wff-child goal new-g)))
            sqn)))))

;;; reduce-lambda-in-expr: parallel beta reduction of any
;;; ((VNB-LAMBDA <bind-spec> body) arg ...) anywhere in expr.
;;; Single- and multi-binder forms both supported.  Recurses into all subterms.
(define (reduce-lambda-in-expr expr)
  (cond
    ((not (pair? expr)) expr)
    ;; ((VNB-LAMBDA x body) arg)  — single-binder, single-arg.
    ((and (pair? (car expr))
          (eq? (caar expr) 'VNB-LAMBDA)
          (= (length (car expr)) 3)
          (symbol? (cadar expr))
          (= (length expr) 2))
     (let ((x    (cadar expr))
           (body (caddar expr))
           (arg  (reduce-lambda-in-expr (cadr expr))))
       (subst-free x arg (reduce-lambda-in-expr body))))
    ;; ((VNB-LAMBDA (LIST x1 ... xn) body) arg1 ... argn)  — multi-binder, parallel.
    ((and (pair? (car expr))
          (eq? (caar expr) 'VNB-LAMBDA)
          (= (length (car expr)) 3)
          (pair? (cadar expr))
          (eq? (car (cadar expr)) 'LIST)
          (= (length (cdr (cadar expr))) (length (cdr expr))))
     (let* ((bvars  (cdr (cadar expr)))
            (body   (reduce-lambda-in-expr (caddar expr)))
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
       final))
    (else
     (cons (reduce-lambda-in-expr (car expr))
           (map reduce-lambda-in-expr (cdr expr))))))
