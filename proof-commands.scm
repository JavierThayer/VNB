;;; proof-commands.scm -- higher-level proof commands (tactics)
;;;
;;; These are built on top of primitive inferences and operate on the
;;; current "focus" sequent node in a deduction graph.
;;;
;;; A PROOF STATE is a deduction graph plus a current focus sequent node.

(define-record-type <proof-state>
  (make-proof-state dg root focus)
  proof-state?
  (dg    proof-state-dg)
  (root  proof-state-root)
  (focus proof-state-focus set-proof-state-focus!))

(define (start-proof wic)
  (let* ((theory  (wff-theory wic))
         (ctxs    (wff-contexts wic))
         (asms    (map (lambda (ctx)
                         (wff-in-theory (local-context-binding ctx) theory))
                       ctxs))
         (assert  (wff-in-theory (wff-formula wic) theory))
         (dg      (make-deduction-graph))
         (sqn     (dg-post! dg (make-sequent asms assert))))
    (make-proof-state dg sqn sqn)))

(define (proof-done? ps)
  (dg-proved? (proof-state-dg ps) (proof-state-root ps)))

(define (proof-open-goals ps)
  (dg-ungrounded-nodes (proof-state-dg ps)))

(define (focus-on ps sqn)
  (set-proof-state-focus! ps sqn)
  ps)

(define (focus-on-first-open ps)
  (let ((open (proof-open-goals ps)))
    (if (null? open)
        ps
        (focus-on ps (car open)))))

;;; -----------------------------------------------------------------------
;;; Soft-failure warning type.
;;;
;;; cmd-* functions return a <vnb-warning> instead of signalling an error
;;; when a primitive inference cannot apply to the current goal.
;;; Interactive short forms display the message and leave *ps* unchanged.

(define-record-type <vnb-warning>
  (make-vnb-warning message)
  vnb-warning?
  (message vnb-warning-message))

(define (vnb--goal-str sqn)
  (expression->string (wff-formula (sequent-node-assertion sqn))))

(define (vnb--warn msg str)
  (make-vnb-warning (string-append msg ": " str)))

;;; -----------------------------------------------------------------------
;;; Command wrappers
;;;
;;; Each command applies a primitive inference to the focus node,
;;; then advances the focus to the first ungrounded new subgoal.
;;; If the inference produces no new subgoals, we move to any remaining open goal.

(define (focus-after-rule ps hyp-nodes)
  ;; Focus on the first ungrounded node among the new subgoals,
  ;; or fall back to any remaining open goal.
  (let ((open-new (filter (lambda (sqn) (not (sequent-node-grounded? sqn)))
                          hyp-nodes)))
    (if (not (null? open-new))
        (focus-on ps (car open-new))
        (focus-on-first-open ps))))

(define-syntax define-cmd
  (syntax-rules ()
    ((_ name (ps . args) body ...)
     (define (name ps . args)
       (let ((result (begin body ...)))
         (if result
             (focus-after-rule ps result)
             (focus-on-first-open ps)))))))

(define (cmd-direct-inference ps)
  (let* ((sqn (proof-state-focus ps))
         (r   (pi-direct-inference! sqn)))
    (if r (focus-after-rule ps r)
        (vnb--warn "direct-inference: cannot decompose" (vnb--goal-str sqn)))))

(define (cmd-antecedent-inference ps formula)
  (let* ((sqn (proof-state-focus ps))
         (r   (pi-antecedent-inference! sqn formula)))
    (if r (focus-after-rule ps r)
        (vnb--warn "antecedent-inference: cannot decompose"
                   (expression->string formula)))))

(define (cmd-assumption ps)
  (let* ((sqn (proof-state-focus ps))
         (r   (pi-assumption! sqn)))
    (if r (focus-after-rule ps r)
        (vnb--warn "assumption: goal not in context" (vnb--goal-str sqn)))))

(define (cmd-cut ps lemma)
  (let* ((sqn (proof-state-focus ps))
         (r   (pi-cut! sqn lemma)))
    (focus-after-rule ps r)))

(define (cmd-if-true ps if-term)
  (let* ((sqn (proof-state-focus ps))
         (r   (pi-if-true! sqn if-term)))
    (focus-after-rule ps r)))

(define (cmd-if-false ps if-term)
  (let* ((sqn (proof-state-focus ps))
         (r   (pi-if-false! sqn if-term)))
    (focus-after-rule ps r)))

(define (cmd-instantiate ps forall-formula term)
  (let* ((sqn (proof-state-focus ps))
         (r   (pi-instantiate! sqn forall-formula term)))
    (if r (focus-after-rule ps r)
        (vnb--warn "instantiate: formula not in context or not universal"
                   (expression->string forall-formula)))))

(define (cmd-exists-witness ps term)
  (let* ((sqn (proof-state-focus ps))
         (r   (pi-exists-witness! sqn term)))
    (if r (focus-after-rule ps r)
        (vnb--warn "exists-witness: goal is not existential" (vnb--goal-str sqn)))))

(define (cmd-weaken ps formula)
  (let* ((sqn (proof-state-focus ps))
         (r   (pi-weaken! sqn formula)))
    (if r (focus-after-rule ps r)
        (vnb--warn "weaken: formula not in context" (expression->string formula)))))

(define (cmd-backchain ps implies-formula)
  (let* ((sqn (proof-state-focus ps))
         (r   (pi-backchain! sqn implies-formula)))
    (if r (focus-after-rule ps r)
        (vnb--warn "backchain: no matching implication"
                   (expression->string implies-formula)))))

(define (cmd-detach ps implies-formula)
  (let* ((sqn (proof-state-focus ps))
         (r   (pi-detach! sqn implies-formula)))
    (if r (focus-after-rule ps r)
        (vnb--warn "detach: need an in-context (IMPLIES A B) whose A is in context"
                   (expression->string implies-formula)))))

;;; fact -- forward APPLICATION of a theorem.  Bring the named theorem into
;;; context, instantiate its leading universals with the given terms, and
;;; auto-detach every antecedent already present in context, landing the
;;; consequent as a new assumption.  Handles INTERLEAVED forall/implies (e.g.
;;; forall s. IS-X(s) => forall a. a in A(s) => P), consuming an arg per
;;; forall and detaching each implies whose antecedent is in context.  This is
;;; the forward-assembly workhorse: a theorem becomes a usable fact in one call,
;;; instead of a ta + inst* + cut/backchain hand-chain.
(define (cmd-fact ps thm-name args)
  (let ((f0 (and (symbol? thm-name)
                 (hash-table-ref/default *theorem-table* thm-name #f))))
    (if (not f0)
        (vnb--warn "fact: unknown theorem"
                   (if (symbol? thm-name) (symbol->string thm-name) "(not a symbol)"))
        (let ((ps1 (cmd-theorem-assumption ps thm-name)))
          (if (vnb-warning? ps1) ps1
              (let loop ((ps ps1) (formula f0) (args args))
                (cond
                  ((vnb-warning? ps) ps)
                  ((and (pair? formula) (eq? (car formula) 'FORALL) (pair? args))
                   (let* ((x    (quantifier-var formula))
                          (body (quantifier-body formula))
                          (ps2  (cmd-instantiate ps formula (car args))))
                     (if (vnb-warning? ps2) ps2
                         (loop ps2 (subst-free x (car args) body) (cdr args)))))
                  ((and (pair? formula) (eq? (car formula) 'IMPLIES)
                        (asms-find (sequent-node-assumptions (proof-state-focus ps))
                                   (binary-left formula)))
                   (let ((ps2 (cmd-detach ps formula)))
                     (if (vnb-warning? ps2) ps2
                         (loop ps2 (binary-right formula) args))))
                  (else ps))))))))

(define (cmd-apply-macete ps macete-name)
  (let* ((sqn (proof-state-focus ps))
         (r   (apply-macete! macete-name sqn)))
    (if r (focus-after-rule ps r)
        (vnb--warn "apply-macete: macete not applicable"
                   (symbol->string macete-name)))))

(define (cmd-apply-macete-to-assumption ps macete-name hyp-formula)
  (let ((sqn (proof-state-focus ps)))
    (cond
      ((not (hash-table-ref/default *theorem-table* macete-name #f))
       (vnb--warn "mac-h: unknown theorem/macete" (symbol->string macete-name)))
      ((not (macete-equivalence? macete-name))
       (vnb--warn (string-append
                   "mac-h: " (symbol->string macete-name)
                   " is not an equivalence (its core must be IFF, =, or ==); "
                   "a one-directional rule cannot rewrite an assumption")
                  (symbol->string macete-name)))
      ((not (null? (macete-rogue-vars macete-name)))
       (vnb--warn (string-append
                   "mac-h: " (symbol->string macete-name)
                   " has schema var(s) undetermined by the match (S-10) "
                   (call-with-output-string
                    (lambda (port) (write (macete-rogue-vars macete-name) port)))
                   " -- refusing, as the goal side does for this -rev direction")
                  (symbol->string macete-name)))
      (else
       (let ((r (apply-macete-to-assumption! macete-name hyp-formula sqn)))
         (if r
             (begin
               (let ((minors (- (length r) 1)))
                 (when (> minors 0)
                   (display ";; mac-h: ") (display macete-name)
                   (display " applied; ") (display minors)
                   (display " side-condition(s) spawned as subgoal(s)")
                   (display " -- main line stays in focus.\n")))
               (focus-after-rule ps r))
             (vnb--warn (string-append
                         "mac-h: " (symbol->string macete-name)
                         " does not occur in the cited assumption")
                        (expression->string hyp-formula))))))))

(define (cmd-or-intro-left ps)
  (let* ((sqn (proof-state-focus ps))
         (r   (pi-or-intro-left! sqn)))
    (if r (focus-after-rule ps r)
        (vnb--warn "or-intro-left: goal is not a disjunction" (vnb--goal-str sqn)))))

(define (cmd-or-intro-right ps)
  (let* ((sqn (proof-state-focus ps))
         (r   (pi-or-intro-right! sqn)))
    (if r (focus-after-rule ps r)
        (vnb--warn "or-intro-right: goal is not a disjunction" (vnb--goal-str sqn)))))

(define (cmd-arith ps)
  (let* ((sqn (proof-state-focus ps))
         (r   (pi-arith! sqn)))
    (if r (focus-after-rule ps r)
        (vnb--warn "arith: goal is not a true closed arithmetic sentence"
                   (vnb--goal-str sqn)))))

(define (cmd-reflexivity ps)
  (let* ((sqn (proof-state-focus ps))
         (r   (pi-reflexivity! sqn)))
    (if r (focus-after-rule ps r)
        (vnb--warn "reflexivity: goal is not (= a a)" (vnb--goal-str sqn)))))

(define (cmd-quasi-reflexivity ps)
  (let* ((sqn (proof-state-focus ps))
         (r   (pi-quasi-reflexivity! sqn)))
    (if r (focus-after-rule ps r)
        (vnb--warn "quasi-reflexivity: goal is not (== a a)" (vnb--goal-str sqn)))))

(define (cmd-eq-subst ps eq-formula)
  (let* ((sqn (proof-state-focus ps))
         (r   (pi-eq-subst! sqn eq-formula)))
    (if r (focus-after-rule ps r)
        (vnb--warn "eq-subst: equality not in context, or nothing to rewrite"
                   (expression->string eq-formula)))))

(define (cmd-proof-by-contradiction ps)
  (let* ((sqn (proof-state-focus ps))
         (r   (pi-proof-by-contradiction! sqn)))
    (focus-after-rule ps r)))

(define (cmd-theorem-assumption ps theorem-name)
  (let* ((sqn (proof-state-focus ps))
         (r   (pi-theorem-assumption! sqn theorem-name)))
    (if r
        (focus-after-rule ps r)
        (vnb--warn "theorem-assumption: unknown theorem"
                   (symbol->string theorem-name)))))

;;; -----------------------------------------------------------------------
;;; QED: install a completed proof as a named theorem in the current
;;; theory.
;;;
;;; The root sequent's assumptions (which came from contexts active when
;;; start-proof ran) must be DISCHARGED before installation; otherwise a
;;; theorem proved as Gamma |- phi would be installed as the bare phi,
;;; usable in any context.  We discharge by wrapping phi in (FORALL <bind> _)
;;; for each assumption, outermost first; expand-destructuring-quantifiers
;;; then converts (FORALL (IN x A) B) to (FORALL x (IMPLIES (IN x A) B)),
;;; giving the standard universal closure.

(define (cmd-qed ps name)
  (unless (proof-done? ps)
    (error "qed: proof is not complete; cannot install" name))
  (let* ((root      (proof-state-root ps))
         (asms      (sequent-node-assumptions root))
         (assertion (wff-formula (sequent-node-assertion root)))
         (wrapped   (let loop ((rest asms))
                      (if (null? rest)
                          assertion
                          `(FORALL ,(wff-formula (car rest))
                                   ,(loop (cdr rest))))))
         (formula   (expand-destructuring-quantifiers wrapped)))
    (theory-add-theorem! *current-theory* name formula)
    (register-proven-theorem! name)
    (when (not (null? asms))
      (display "qed: discharged ")
      (display (length asms))
      (display " context assumption(s).\n"))
    name))

;;; -----------------------------------------------------------------------
;;; Meta-level wff substitution.
;;;
;;; (subst-wff '((x . term-x) (y . term-y) ...) wff-or-raw)
;;;   Applies capture-avoiding substitutions to the raw formula of a wff
;;;   and returns a new <wff> (re-validated).  This is a source-level
;;;   rewrite, not a logical inference; after substitution you must reprove.

(define (subst-wff substitution wic-or-formula)
  (let* ((src (if (wff? wic-or-formula)
                  (wff-formula wic-or-formula)
                  wic-or-formula))
         (subs (map (lambda (pair)
                      (cons (car pair)
                            (if (wff? (cdr pair))
                                (wff-formula (cdr pair))
                                (cdr pair))))
                    substitution))
         (result (let loop ((ss subs) (e src))
                   (if (null? ss)
                       e
                       (loop (cdr ss)
                             (subst-free (caar ss) (cdar ss) e))))))
    (make-wff result)))

;;; -----------------------------------------------------------------------
;;; Display helpers

(define (print-proof-state ps)
  (if (proof-done? ps)
      (display "Proof complete.\n")
      (begin
        (let ((open (proof-open-goals ps)))
          (display (string-append
                    (number->string (length open))
                    " open goal(s).\n"))
          (display "Focus:\n  ")
          (display (sequent-node->string (proof-state-focus ps)))
          (newline)
          (when (> (length open) 1)
            (display "Other open goals:\n")
            (for-each (lambda (sqn)
                        (when (not (eq? sqn (proof-state-focus ps)))
                          (display "  ")
                          (display (sequent-node->string sqn))
                          (newline)))
                      open))))))

;;; -----------------------------------------------------------------------
;;; Convenience macro for writing proof scripts

;;; (with-proof goal-formula body ...)
;;; body is a sequence of commands that return a proof-state.
;;; Returns the final proof-state.

(define-syntax with-proof
  (syntax-rules ()
    ((_ goal cmd ...)
     (let ((ps (start-proof (make-wff (quote goal)))))
       (let* ((ps (cmd ps)) ...)
         (if (proof-done? ps)
             (begin (display "QED\n") ps)
             (begin (print-proof-state ps) ps)))))))

;;; -----------------------------------------------------------------------
;;; Commands for n-ary constructors

(define (cmd-cartesian-intro ps)
  (let* ((sqn (proof-state-focus ps))
         (r   (pi-cartesian-intro! sqn)))
    (if r (focus-after-rule ps r)
        (vnb--warn "cartesian-intro: goal is not a LIST-in-CARTESIAN membership"
                   (vnb--goal-str sqn)))))

(define (cmd-cartesian-elim ps membership-formula k)
  (let* ((sqn (proof-state-focus ps))
         (r   (pi-cartesian-elim! sqn membership-formula k)))
    (if r (focus-after-rule ps r)
        (vnb--warn "cartesian-elim: formula not found or index out of range"
                   (string-append (expression->string membership-formula)
                                  " index " (number->string k))))))

(define (cmd-tuples-intro ps)
  (let* ((sqn (proof-state-focus ps))
         (r   (pi-tuples-intro! sqn)))
    (if r (focus-after-rule ps r)
        (vnb--warn "tuples-intro: goal is not a LIST-in-TUPLES membership"
                   (vnb--goal-str sqn)))))

(define (cmd-tuples-elim ps membership-formula k)
  (let* ((sqn (proof-state-focus ps))
         (r   (pi-tuples-elim! sqn membership-formula k)))
    (if r (focus-after-rule ps r)
        (vnb--warn "tuples-elim: formula not found or index out of range"
                   (string-append (expression->string membership-formula)
                                  " index " (number->string k))))))

(define (cmd-nth-reduce ps)
  (let* ((sqn (proof-state-focus ps))
         (r   (pi-nth-reduce! sqn)))
    (if r (focus-after-rule ps r)
        (vnb--warn "nth-reduce: no reducible (NTH k (LIST ...)) in goal"
                   (vnb--goal-str sqn)))))

(define (cmd-functoid-beta ps)
  (let* ((sqn (proof-state-focus ps))
         (r   (pi-functoid-beta! sqn)))
    (if r (focus-after-rule ps r)
        (vnb--warn "functoid-beta: no reducible (apply-functoid f v ...) in goal"
                   (vnb--goal-str sqn)))))

(define (cmd-union-intro ps k)
  (let* ((sqn (proof-state-focus ps))
         (r   (pi-union-intro! sqn k)))
    (if r (focus-after-rule ps r)
        (vnb--warn "union-intro: goal is not an IN-UNION membership"
                   (vnb--goal-str sqn)))))

(define (cmd-union-elim ps membership-formula)
  (let* ((sqn (proof-state-focus ps))
         (r   (pi-union-elim! sqn membership-formula)))
    (if r (focus-after-rule ps r)
        (vnb--warn "union-elim: formula not found"
                   (expression->string membership-formula)))))

(define (cmd-tfi ps)
  (let* ((sqn (proof-state-focus ps))
         (r   (pi-tfi! sqn)))
    (if r (focus-after-rule ps r)
        (vnb--warn "tfi: goal is not (FORALL var (IMPLIES (IN var ORD) P))"
                   (vnb--goal-str sqn)))))

(define (cmd-tfi3 ps)
  (let* ((sqn (proof-state-focus ps))
         (r   (pi-tfi3! sqn)))
    (if r (focus-after-rule ps r)
        (vnb--warn "tfi3: goal is not (FORALL var (IMPLIES (IN var ORD) P))"
                   (vnb--goal-str sqn)))))

(define (cmd-intersection-intro ps)
  (let* ((sqn (proof-state-focus ps))
         (r   (pi-intersection-intro! sqn)))
    (if r (focus-after-rule ps r)
        (vnb--warn "intersection-intro: goal is not an IN-INTERSECTION membership"
                   (vnb--goal-str sqn)))))

(define (cmd-intersection-elim ps membership-formula k)
  (let* ((sqn (proof-state-focus ps))
         (r   (pi-intersection-elim! sqn membership-formula k)))
    (if r (focus-after-rule ps r)
        (vnb--warn "intersection-elim: formula not found or index out of range"
                   (string-append (expression->string membership-formula)
                                  " index " (number->string k))))))

;;; -----------------------------------------------------------------------
;;; Ring-simplify command
;;;
;;; (cmd-nn-induction ps) applies NN induction to a goal (FORALL n (IMPLIES (IN n NN) P)).
;;; Produces two subgoals: base case P[n:=0] and step case (FORALL n (IMPLIES (IN n NN) (IMPLIES P P[n:=succ(n)]))).

(define (cmd-nn-induction ps)
  (let* ((sqn (proof-state-focus ps))
         (r   (pi-nn-induction! sqn)))
    (if r (focus-after-rule ps r)
        (vnb--warn "nn-induction: goal must be (forall n (implies (in n nn) ...))"
                   (vnb--goal-str sqn)))))

;;; (cmd-ring-simplify ps) closes a goal of the form (= e1 e2) by reducing
;;; both sides to their normal form in the free associative ZZ-algebra.
;;; Symbols not reducible by arith-eval-term are treated as generators
;;; automatically — no variable list needed.

(define (cmd-ring-simplify ps)
  (let* ((sqn (proof-state-focus ps))
         (r   (pi-ring-simplify! sqn)))
    (if r (focus-after-rule ps r)
        (vnb--warn "ring-simplify: goal is not a provable ring identity"
                   (vnb--goal-str sqn)))))

;;; (cmd-comm-ring-simplify ps) closes a goal (= e1 e2) by reducing both sides
;;; to their sum-of-monomials normal form in the free COMMUTATIVE ring
;;; ZZ[generators] (so x*y = y*x closes, unlike the non-commutative rs).
(define (cmd-comm-ring-simplify ps)
  (let* ((sqn (proof-state-focus ps))
         (r   (pi-comm-ring-simplify! sqn)))
    (if r (focus-after-rule ps r)
        (vnb--warn "comm-ring-simplify: goal is not a provable commutative-ring identity"
                   (vnb--goal-str sqn)))))

;;; (cmd-ineq ps idxs) closes a linear-inequality goal over RR from the
;;; assumptions named (1-based) in idxs, via the Fourier-Motzkin/Farkas oracle.
(define (cmd-ineq ps idxs)
  (let* ((sqn (proof-state-focus ps))
         (r   (pi-ineq! sqn idxs)))
    (if r (focus-after-rule ps r)
        (vnb--warn "ineq: goal not a linear-RR consequence of the named assumptions"
                   (vnb--goal-str sqn)))))

;;; -----------------------------------------------------------------------
;;; D-7 commands: SEP / COMP / IOTA / VNB-LAMBDA characterizations
;;; (REVIEW.md D-7).  Skeletal: schemas in the body formula are handled
;;; at the kernel level rather than as first-order axioms.

(define (cmd-sep-sethood ps)
  (let* ((sqn (proof-state-focus ps))
         (r   (pi-sep-sethood! sqn)))
    (if r (focus-after-rule ps r)
        (vnb--warn "sep-sethood: goal is not (IN (SEP x A p) SET)"
                   (vnb--goal-str sqn)))))

(define (cmd-sep-mem-intro ps)
  (let* ((sqn (proof-state-focus ps))
         (r   (pi-sep-mem-intro! sqn)))
    (if r (focus-after-rule ps r)
        (vnb--warn "sep-mem-intro: goal is not (IN y (SEP x A p))"
                   (vnb--goal-str sqn)))))

(define (cmd-sep-mem-elim ps membership-formula)
  (let* ((sqn (proof-state-focus ps))
         (r   (pi-sep-mem-elim! sqn membership-formula)))
    (if r (focus-after-rule ps r)
        (vnb--warn "sep-mem-elim: assumption not found or not (IN y (SEP x A p))"
                   (expression->string membership-formula)))))

(define (cmd-comp-mem-intro ps)
  (let* ((sqn (proof-state-focus ps))
         (r   (pi-comp-mem-intro! sqn)))
    (if r (focus-after-rule ps r)
        (vnb--warn "comp-mem-intro: goal is not (IN y (COMP x p))"
                   (vnb--goal-str sqn)))))

(define (cmd-comp-mem-elim ps membership-formula)
  (let* ((sqn (proof-state-focus ps))
         (r   (pi-comp-mem-elim! sqn membership-formula)))
    (if r (focus-after-rule ps r)
        (vnb--warn "comp-mem-elim: assumption not found or not (IN y (COMP x p))"
                   (expression->string membership-formula)))))

(define (cmd-iota-def ps iota-term)
  (let* ((sqn (proof-state-focus ps))
         (r   (pi-iota-def! sqn iota-term)))
    (if r (focus-after-rule ps r)
        (vnb--warn "iota-def: argument is not an (IOTA x p) term"
                   (expression->string iota-term)))))

(define (cmd-big-union-sethood ps)
  (let* ((sqn (proof-state-focus ps))
         (r   (pi-big-union-sethood! sqn)))
    (if r (focus-after-rule ps r)
        (vnb--warn "big-union-sethood: goal is not (IN (BIG-UNION z A body) SET)"
                   (vnb--goal-str sqn)))))

(define (cmd-big-union-mem-intro ps witness)
  (let* ((sqn (proof-state-focus ps))
         (r   (pi-big-union-mem-intro! sqn witness)))
    (if r (focus-after-rule ps r)
        (vnb--warn "big-union-mem-intro: goal is not (IN x (BIG-UNION z A body))"
                   (vnb--goal-str sqn)))))

(define (cmd-big-union-mem-elim ps membership-formula)
  (let* ((sqn (proof-state-focus ps))
         (r   (pi-big-union-mem-elim! sqn membership-formula)))
    (if r (focus-after-rule ps r)
        (vnb--warn "big-union-mem-elim: assumption not found or not (IN x (BIG-UNION z A body))"
                   (expression->string membership-formula)))))

(define (cmd-lambda-type ps)
  (let* ((sqn (proof-state-focus ps))
         (r   (pi-lambda-type! sqn)))
    (if r (focus-after-rule ps r)
        (vnb--warn "lambda-type: goal is not (IN (VNB-LAMBDA x body) (FUN A B))"
                   (vnb--goal-str sqn)))))

(define (cmd-lambda-beta ps)
  (let* ((sqn (proof-state-focus ps))
         (r   (pi-lambda-beta! sqn)))
    (if r (focus-after-rule ps r)
        (vnb--warn "lambda-beta: no reducible ((VNB-LAMBDA x body) arg ...) in goal"
                   (vnb--goal-str sqn)))))
