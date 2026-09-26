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

;;; The root sequent has NO assumptions.  It used to inherit one per active
;;; local context (contexts.scm); that facility was removed on 2026-07-29, so
;;; a proof now begins from the bare goal and every hypothesis arrives through
;;; an inference.  cmd-qed's discharge loop over root assumptions is kept: it
;;; is now vacuous, and it is the guard REVIEW.md S-2 asked for.
(define (start-proof wic)
  (let* ((theory  (wff-library wic))
         (asms    '())
         (assert  (wff-in-library (wff-formula wic) theory))
         (dg      (make-deduction-graph))
         (sqn     (dg-post! dg (make-sequent asms assert))))
    (make-proof-state dg sqn sqn)))

(define (proof-done? ps)
  (dg-proved? (proof-state-dg ps) (proof-state-root ps)))

(define (proof-open-goals ps)
  (dg-ungrounded-nodes (proof-state-dg ps)))

;;; The nodes you can actually WORK ON: ungrounded AND with no in-arrow, i.e.
;;; no rule has fired on them yet.
;;;
;;; `proof-open-goals' is every ungrounded node, which INCLUDES each justified
;;; ancestor still waiting on its children.  Reporting that as the open-goal
;;; count is why the Focus panel says "13 open goals" over a proof with one
;;; real leaf: the other twelve are the cut/backchain/di scaffolding, several
;;; of them printing the same assertion, and a user reasonably reads the list
;;; as twelve things left to prove.  Worse, `focus' indexed that list, so
;;; (focus n) could select an already-justified node and a following tactic
;;; would build a SECOND justification for it.
;;;
;;; Both notions are needed -- the trace and the TeX output want every
;;; ungrounded node -- so this is a second accessor rather than a change to the
;;; first.  driver-kit's `proof-leaves' is this function on *ps*; several proof
;;; files had already hand-written the filter, which is what a missing accessor
;;; looks like.
(define (proof-open-leaves ps)
  (filter (lambda (sqn) (null? (sequent-node-in-arrows sqn)))
          (dg-ungrounded-nodes (proof-state-dg ps))))

(define (focus-on ps sqn)
  (set-proof-state-focus! ps sqn)
  ps)

;;; Prefer a real LEAF: after a rule fires, the node it fired on is ungrounded
;;; but justified, and landing focus there is how a driver ends up "working on"
;;; a node whose children are the actual obligations.  Falls back to the old
;;; behaviour if there is no leaf, so nothing loses its focus entirely.
(define (focus-on-first-open ps)
  (let ((leaves (proof-open-leaves ps)))
    (cond ((pair? leaves) (focus-on ps (car leaves)))
          (else (let ((open (proof-open-goals ps)))
                  (if (null? open) ps (focus-on ps (car open))))))))

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

(define (cmd-spec ps thm-name terms)
  (let* ((sqn (proof-state-focus ps))
         (r   (pi-spec! sqn thm-name terms)))
    (if r (focus-after-rule ps r)
        (vnb--warn "spec: unknown theorem (or too many terms)"
                   (if (symbol? thm-name) (symbol->string thm-name) "")))))

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
;;; forall s. IS-X(s) => forall a. a in CARR(s) => P), consuming an arg per
;;; forall and detaching each implies whose antecedent is in context.  This is
;;; the forward-assembly workhorse: a theorem becomes a usable fact in one call,
;;; instead of a ta + inst* + cut/backchain hand-chain.
;;; Discharge a GROUND arithmetic antecedent by PROVING it, instead of demanding
;;; it in context.
;;;
;;; `(IN 2 NN)' was a hole you could lose an afternoon in.  `arith' DECIDES it
;;; (arith-membership-check, arith-eval.scm), but `fact'/`inst+' only auto-detach
;;; a guard that is literally an assumption -- so a theorem guarded on (IN 2 NN)
;;; went inert, and the driver had to hand-cut the typing of every numeral it
;;; touched.  There is no axiom to add here (a `support' per numeral is exactly
;;; the bulk this project refuses); the machine can already prove the thing.
;;;
;;; So: cut the antecedent, close the side goal with the `arith' rule, come back
;;; to the main branch with it in context.  Every step is a kernel rule
;;; (`cut', `arith-ground'), so this carries NO debt -- it is a composite, not a
;;; new trusted surface.  Returns the new proof-state, or #f if the antecedent is
;;; not a decidable ground truth (in which case the caller stops peeling, exactly
;;; as before).
;;;
;;; Only ever called when asms-find has ALREADY missed: cutting a formula that is
;;; in context up to alpha is a silent self-loop (dg-post! hash-conses by
;;; alpha-equivalence), and that guard is the caller's `in-ctx' test.
(define (pc--land-ground-antecedent ps ante)
  (and (eq? #t (arith-eval-formula ante))
       (let* ((sqn (proof-state-focus ps))
              (r   (pi-cut! sqn ante)))
         (and r
              (let* ((side (car  r))            ; side goal: ante itself
                     (main (cadr r))            ; main branch: ante in context
                     (ps1  (cmd-arith (focus-on ps side))))
                (and (not (vnb-warning? ps1))
                     (focus-on ps1 main)))))))

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
                  ;; One binder at a time, and that is CORRECT here: each
                  ;; subst-free runs under the binders that remain, so the
                  ;; variables still to be instantiated are bound, not free, and
                  ;; there is nothing for a later argument to capture.  This is
                  ;; the one shape in which iterating subst-free is legitimate;
                  ;; a substitution LIST must use subst-free* (expressions.scm).
                  ((and (pair? formula) (eq? (car formula) 'FORALL) (pair? args))
                   (let* ((x    (quantifier-var formula))
                          (body (quantifier-body formula))
                          (ps2  (cmd-instantiate ps formula (car args))))
                     (if (vnb-warning? ps2) ps2
                         (loop ps2 (subst-free x (car args) body) (cdr args)))))
                  ;; A guard is dischargeable two ways: it is already an
                  ;; assumption, or it is a ground arithmetic truth we can prove
                  ;; on the spot (see pc--land-ground-antecedent).  Anything else
                  ;; stops the peel and we keep what we have -- as before.
                  ((and (pair? formula) (eq? (car formula) 'IMPLIES))
                   (let* ((ante   (binary-left formula))
                          (in-ctx (asms-find
                                    (sequent-node-assumptions (proof-state-focus ps))
                                    ante))
                          (ps*    (if in-ctx ps (pc--land-ground-antecedent ps ante))))
                     (if (not ps*)
                         ps
                         (let ((ps2 (cmd-detach ps* formula)))
                           (if (vnb-warning? ps2) ps2
                               (loop ps2 (binary-right formula) args))))))
                  (else ps))))))))

;;; inst+ -- instantiate an IN-CONTEXT universal at TERM, then discharge any
;;; in-context guards by forward detach, landing the specialised consequent.
;;; The hypothesis-side analogue of `fact' (which assembles a THEOREM): here the
;;; universal is already an assumption (e.g. a metric axiom exposed by grind),
;;; and we want body[term] usable in one ply.  inst alone would leave a guarded
;;; (IMPLIES (IN term DOM) P) the parameterless alphabet can't consume; inst+
;;; detaches each guard whose antecedent is already in context, peeling the
;;; nest until the consequent is atomic / a fresh universal.  scout's
;;; witness-choosing lane (vnb--scout-inst-candidates) emits these.  A failed
;;; instantiate propagates; a guard we cannot detach just stops the peel and we
;;; keep the (still-useful) instantiated body -- both stay sound, every step is
;;; a real kernel rule.
(define (cmd-inst+ ps forall-formula term)
  (let ((p1 (cmd-instantiate ps forall-formula term)))
    (if (or (vnb-warning? p1) (vnb-error? p1))
        p1
        (let loop ((ps p1)
                   (body (subst-free (quantifier-var forall-formula) term
                                     (quantifier-body forall-formula))))
          (if (and (pair? body) (eq? (car body) 'IMPLIES))
              ;; in context, or provable ground arithmetic -- same two ways as
              ;; cmd-fact; a guard that is neither stops the peel.
              (let* ((ante   (binary-left body))
                     (in-ctx (asms-find (sequent-node-assumptions (proof-state-focus ps))
                                        ante))
                     (ps*    (if in-ctx ps (pc--land-ground-antecedent ps ante))))
                (if (not ps*)
                    ps
                    (let ((p2 (cmd-detach ps* body)))
                      (if (or (vnb-warning? p2) (vnb-error? p2))
                          ps
                          (loop p2 (binary-right body))))))
              ps)))))

;; Resolve the name the user typed to a macete that actually exists.  A
;; def-FUNCTOID installs its unfold under its plain name (so `mac poly' works),
;; but declare-structure / def-predicate install a predicate's unfold under
;; NAME-def -- so a user who types `(mac 'is-commutative-ring)' hit an
;; "unknown macete" and, in Emacs, a bare #f.  Fall back to NAME-def when the
;; plain name has no macete but NAME-def does; the unfold is exactly what was
;; meant.  Returns the resolved name, or #f if neither exists.
(define (resolve-macete-name name)
  (cond ((hash-table-ref/default *macete-table* name #f) name)
        (else
         (let ((def (string->symbol (string-append (symbol->string name) "-def"))))
           (and (hash-table-ref/default *macete-table* def #f) def)))))

(define (cmd-apply-macete ps macete-name)
  (let* ((sqn      (proof-state-focus ps))
         (resolved (resolve-macete-name macete-name)))
    (when (and resolved (not (eq? resolved macete-name)))
      (vnb--warn (string-append "apply-macete: no macete `"
                                (symbol->string macete-name) "'; using `"
                                (symbol->string resolved) "' (the definitional unfold)")
                 (symbol->string resolved)))
    (if (not resolved)
        (vnb--warn (string-append "apply-macete: no macete named `"
                                  (symbol->string macete-name)
                                  "' (nor `" (symbol->string macete-name)
                                  "-def').  (find-theorem '" (symbol->string macete-name)
                                  ") to search.")
                   (symbol->string macete-name))
    (let ((r (apply-macete! resolved sqn)))
    (cond
      (r (focus-after-rule ps r))
      ;; An AMBIGUOUS accessor has no reduction, on purpose: its name sits at a
      ;; different slot in two structures, so no single (NTH k) rewrite is right
      ;; (structures.scm, register-accessor-index!).  Say so -- "not applicable"
      ;; would send the reader hunting for a malformed goal.
      ((accessor-ambiguous? macete-name)
       (vnb--warn
         (string-append
           "apply-macete: `" (symbol->string macete-name)
           "' is an AMBIGUOUS accessor -- it names a different slot in different "
           "structures, so it has no (NTH k) reduction.  See (accessor-index-audit).")
         (symbol->string macete-name)))
      (else
       (vnb--warn "apply-macete: macete not applicable"
                  (symbol->string macete-name))))))))

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
        ;; Two different refusals, and until 2026-09-18 one message for both.  When
        ;; the goal IS (= a a), the rule declined because `a' is not certified
        ;; DEFINED (pi--defined?): `=' is strict, so t = t says that t denotes.  The
        ;; old text -- "goal is not (= a a)", printed above two identical sides --
        ;; cost three rake agents a run each.
        (let ((g (wff-formula (sequent-node-assertion sqn))))
          (if (and (pair? g) (eq? (car g) '=) (pair? (cdr g)) (pair? (cddr g))
                   (alpha-equiv? (cadr g) (caddr g)))
              (vnb--warn (string-append
                          "reflexivity: the two sides are the same term, but it is not "
                          "certified DEFINED -- `=' is strict.  Land its typing first "
                          "(a `fact'/`have!' of (IN t _) or an equation t = _), or use "
                          "`qrfl' if the goal may be stated with ==")
                         (vnb--goal-str sqn))
              (vnb--warn "reflexivity: goal is not (= a a)" (vnb--goal-str sqn)))))))

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

;;; HOLE MODE (2026-09-18).  Under a keep-going load (load.scm sets
;;; *vnb-qed-hole-mode?*), a proof that does not complete is NOT an error: its
;;; statement is installed as an ASSERTED hole, the open goals are printed, and
;;; the name goes on *vnb-qed-holes*.  Citers then load, so ONE load lists every
;;; root failure instead of one per cascade.  A band built this way is for
;;; repair work only; load.scm says so at the end.
(define *vnb-qed-hole-mode?*                 ; same switch as load.scm's keep-going mode
  (let ((v (get-environment-variable "VNB_KEEP_GOING")))
    (and v (not (string-null? v)) #t)))
(define *vnb-qed-holes* '())              ; (name . open-goal-strings), newest first

(define (cmd-qed ps name)
  (if (not (proof-done? ps))
      (if *vnb-qed-hole-mode?*
          (let ((goals (map (lambda (l)
                              (let ((str (expression->string (wff-formula (sequent-node-assertion l)))))
                                (if (> (string-length str) 160) (string-head str 160) str)))
                            (proof-open-leaves ps))))
            (display ";; KEEP-GOING HOLE: ") (display name) (display " -- ")
            (display (length goals)) (display " open leaf(s):\n")
            (for-each (lambda (g) (display ";;     ") (display g) (newline)) goals)
            (set! *vnb-qed-holes* (cons (cons name goals) *vnb-qed-holes*)))
          (error "qed: proof is not complete; cannot install" name)))
  ;; A COMPLETE proof of a name that an earlier keep-going pass left as a hole
  ;; (a repair probed on a keep-going band) closes the hole: drop the entry, or
  ;; qed--guarded goes on announcing "HOLE -- installed ASSERTED" for a proof
  ;; that is grounded (found by a repair agent, batch 21, 2026-09-23).
  (if (proof-done? ps)
      (set! *vnb-qed-holes* (del-assq name *vnb-qed-holes*)))
  (let* ((root      (proof-state-root ps))
         (asms      (sequent-node-assumptions root))
         (assertion (wff-formula (sequent-node-assertion root)))
         (wrapped   (let loop ((rest asms))
                      (if (null? rest)
                          assertion
                          `(FORALL ,(wff-formula (car rest))
                                   ,(loop (cdr rest))))))
         (formula   (expand-destructuring-quantifiers wrapped)))
    (if (proof-done? ps)
        ;; THE ONE PLACE THAT SAYS `proven': the root sequent is grounded (checked above and
        ;; again here), so the statement has a deduction graph behind it.
        (begin (fluid-let ((*current-provenance* 'proven))
                 (add-theorem! *library* name formula))
               (register-proven-theorem! name))
        (fluid-let ((*current-provenance* 'asserted))
          (add-theorem! *library* name formula)))
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
        (let ((open (proof-open-leaves ps)))
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

(define (cmd-length-reduce ps)
  (let* ((sqn (proof-state-focus ps))
         (r   (pi-length-reduce! sqn)))
    (if r (focus-after-rule ps r)
        (vnb--warn "length-reduce: no reducible (LENGTH (LIST ...)) in goal"
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

;;; (cmd-cring-simp ps [target]) -- IN-FORMULA commutative-ring simplification.
;;; Rewrite a commutative-ring SUBTERM e of the goal to its canonical form e',
;;; in place (e.g. turn (x+y)^2 inside a larger goal into x^2 + 2*x*y + y^2).
;;;
;;; Proof-grade and adds NO new kernel rule -- it composes three existing sound
;;; primitives:
;;;   1. (cut (= e e'))     spawns the equality as a lemma + a main branch that
;;;                         gains (= e e') as an assumption;
;;;   2. crs on the lemma   discharges (= e e') -- warrant (1) [the normal-form
;;;                         theorem] and warrant (2) [crs certifies every SOURCE
;;;                         generator of e, including cancelled ones, is a
;;;                         carrier element], so the lemma holds;
;;;   3. (eq-subst (= e e')) Leibniz-rewrites e -> e' in the main goal.
;;; Warrant (2) is pre-checked here (ring-vars-ok? over e's source generators)
;;; so an unprovable case is refused cleanly, BEFORE the graph is mutated,
;;; naming the generators the user must type first (post-di they already are).
(define (cmd-cring-simp ps . opt)
  (let* ((target (and (pair? opt) (car opt)))
         (sqn    (proof-state-focus ps))
         (asms   (sequent-node-assumptions sqn))
         (goal   (wff-formula (sequent-node-assertion sqn)))
         (redex  (find-cring-redex goal target)))
    (cond
      ((not redex)
       (vnb--warn "simp: no commutative-ring subterm to simplify"
                  (vnb--goal-str sqn)))
      (else
       (let* ((e       (car redex))
              (e*      (cadr redex))
              (surface (caddr redex))
              (R       (cadddr redex))
              ;; warrant (2): every SOURCE generator of e (incl. cancelled)
              ;; must be a certified carrier element, on the matching surface.
              (gens    (if (eq? surface 'concrete)
                           (cring-redex-source-generators e)
                           (dedup-equal (cring-source-generators e R))))
              (certified?
               (lambda (g) (if (eq? surface 'concrete)
                               (ring-vars-ok?  (list g)   '() asms)
                               (cring-vars-ok? (list g) R '() asms))))
              (bad (filter (lambda (g) (not (certified? g))) gens)))
         (if (pair? bad)
             (vnb--warn
              "simp: subterm generators not known to be ring elements (type them first)"
              (str-join (map expression->string bad) ", "))
             (let* ((eq         (list '= e e*))
                    (children   (pi-cut! sqn eq))
                    (lemma-node (car children))
                    (main-node  (cadr children)))
               ;; discharge (= e e') by crs -- guaranteed: equal normal forms
               ;; (e' = normalize e) and generators certified above.
               (pi-comm-ring-simplify! lemma-node)
               ;; rewrite e -> e' in the main goal, then focus the result.
               (pi-eq-subst! main-node eq)
               (focus-on-first-open ps))))))))

;;; (cmd-ineq ps idxs) closes a linear-inequality goal over RR from the
;;; assumptions named (1-based) in idxs, via the Fourier-Motzkin/Farkas oracle.
(define (cmd-ineq ps idxs)
  (let* ((sqn (proof-state-focus ps))
         (r   (pi-ineq! sqn idxs)))
    (if r (focus-after-rule ps r)
        (vnb--warn "ineq: goal not a linear-RR consequence of the named assumptions"
                   (vnb--goal-str sqn)))))

;;; (cmd-sos ps cert-args) closes a nonstrict polynomial inequality a <= b over
;;; RR by the supplied sum-of-squares certificate (the nonlinear companion of
;;; ineq).  cert-args are surface-string or s-expr terms c_i; the goal closes
;;; when b - a is a nonnegative rational combination of the squares c_i^2.
(define (cmd-sos ps cert-args)
  (if (null? cert-args)
      (begin (sos-print-usage) ps)       ; bare (sos): explain, leave the state unchanged
      (let* ((sqn   (proof-state-focus ps))
             (certs (map ->raw-formula cert-args))
             (r     (pi-sos! sqn certs)))
        (if r (focus-after-rule ps r)
            (vnb--warn "sos: goal is not a <= over RR closed by the given squares as a nonnegative certificate"
                       (vnb--goal-str sqn))))))

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

;;; The context-side twin of cmd-iota-def: no obligation is posted, because the
;;; context is what discharges it.  Two ways to fail and they are different, so
;;; the warnings are different: not an IOTA term at all, or an IOTA the context
;;; does not establish as denoting (the usual case -- land the `(IN <iota> X)'
;;; typing first).
(define (cmd-iota-in-elim ps iota-term)
  (let* ((sqn (proof-state-focus ps))
         (r   (pi-iota-in-elim! sqn iota-term)))
    (cond
      (r (focus-after-rule ps r))
      ((not (and (pair? iota-term) (eq? (car iota-term) 'IOTA)))
       (vnb--warn "iota-in-elim: argument is not an (IOTA x p) term"
                  (expression->string iota-term)))
      (else
       (vnb--warn (string-append
                   "iota-in-elim: nothing in the context establishes that this"
                   " description denotes -- land (IN <the iota term> X) or an"
                   " equation naming it, then try again")
                  (expression->string iota-term))))))

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

;;; lam-b's hypothesis-side twin -- what mac-h is to mac.  Cites nothing, so it
;;; adds no debt; the assumption is replaced by its beta-equal.
(define (cmd-lambda-beta-hyp ps hyp-formula)
  (let* ((sqn (proof-state-focus ps))
         (r   (pi-lambda-beta-hyp! sqn hyp-formula)))
    (cond
      (r (focus-after-rule ps r))
      ((not (asms-find (sequent-node-assumptions sqn) hyp-formula))
       (vnb--warn "lam-b-h: no such assumption in context"
                  (expression->string hyp-formula)))
      (else
       (vnb--warn "lam-b-h: no reducible ((VNB-LAMBDA x body) arg ...) in that assumption"
                  (expression->string hyp-formula))))))
