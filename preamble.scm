;;; preamble.scm -- rule-based drivers a human can edit (notes-45, batch 41, 2026-09-28),
;;; and the older clause pipeline (2026-08-21).
;;;
;;; TWO COMMANDS SHARE THE NAME, told apart by the argument:
;;;
;;;   (preamble)                  the RULE ENGINE (below, prefix `pa-'): the rules of
;;;   (preamble 'NAME)            preambles/default.pre (or ~/.vnb-preamble.pre when it
;;;   (preamble "path.pre")       exists, or preambles/NAME.pre, or the file named) are
;;;                               applied to the FOCUS leaf, one committed firing at a time.
;;;   (preamble '(induct) ...)    a clause LIST: the 2026-08-21 pipeline, now also
;;;                               reachable as (preamble-clauses '(induct) ...).
;;;
;;; The design is docs/preambles-2026-09-28.md; its "Built (phase 1, batch 41)" section
;;; is the walkthrough.  The rest of this header, down to the pipeline's code, is the
;;; pipeline's own.
;;;
;;; ---------------------------------------------------------------------------------
;;; THE CLAUSE PIPELINE (2026-08-21) -- a STRATEGY, executed.
;;;
;;; The user has asked for this three times in different words, most recently
;;; 2026-08-21: "I'm still longing for a bridge from `preamble' to a sequence of
;;; steps to close a proof."  The preamble they wrote out, for the series
;;; triangle inequality, was:
;;;
;;;     (a) Use induction
;;;     (b) For the base case and induction unfold the definitions of abs
;;;     (c) for inequalities, whenever the Farkas-FUBA decision doesn't work,
;;;         introduce intermediate terms using subadditivity of +
;;;
;;; Three lines of mathematical intent, and the fifteen tactic calls that
;;; realise them are mechanical given the intent.  This is the bridge:
;;;
;;;     (preamble '(induct)
;;;               '(unfold series-partial-sum-zero series-partial-sum-succ)
;;;               '(instantiate)
;;;               '(close))
;;;
;;; WHAT IT IS NOT.  Not a search, not an oracle, and not a new kind of trust.
;;; It drives `ni', `di', `mac', `inst+' and the closers -- each of which
;;; records itself -- so a proof it drives bills exactly what those citations
;;; bill, and the RECORDED SCRIPT is the ordinary step-by-step proof.  It also
;;; RETURNS the step list, so the sequence can be pasted into a file: a library
;;; theorem must not depend on this file (it loads with the copilot, long after
;;; theorem-library), and the whole point is that you keep the steps, not the
;;; preamble.
;;;
;;; THE WORK LIST IS LEAVES, NOT THE FOCUS, and that is the substance.  A single
;;; `(induct)' opens two goals that want the SAME treatment, and every driver in
;;; this tree that handles them writes the treatment out twice.  `preamble' runs
;;; the clause list against each open leaf in turn.  A leaf that closes
;;; disappears; a leaf that stalls is REPORTED, with the clause that stalled it
;;; and the goal it stalled on -- never silently left behind, because a
;;; composite that half-succeeds and says nothing is the worst failure mode in
;;; this tree.
;;;
;;; ORDER IS THE CONTENT.  `(induct)' must precede `(peel)': `di' is greedy, one
;;; call takes the whole leading FORALL/IMPLIES prefix, `ni' tests the goal's
;;; literal shape, and there is no undo -- so a peel before an induct destroys
;;; the induction.  Writing the clauses in order is how the user states that
;;; discipline, and the machine then keeps it.
;;;
;;; THE CLAUSES
;;;
;;;   (induct)              `ni' if the goal shape admits it.  Opens two leaves.
;;;   (peel)                `di' until the goal's head stops changing.
;;;   (unfold NAME ...)     `mac' each named theorem on the goal.  A macete that
;;;                         does not apply is skipped, not an error: the same
;;;                         clause list runs against a base case and a step
;;;                         case, and the recurrence applies only to one.
;;;   (instantiate [T ...]) With terms: `inst+' every universal assumption at
;;;                         them.  Without: at every free variable of the goal
;;;                         that the context types.  Either way a landing still
;;;                         headed IMPLIES is REJECTED and rolled back -- that
;;;                         is the signature of an instantiation at the wrong
;;;                         argument, and it is why this probes.
;;;   (close)               The closers, in order, first one that closes wins:
;;;                         ass, rfl, arith, crs, prop, contra, supply.
;;;
;;; Loads after `contra' and `ineq-supply' -- it drives `prop', `contra' and
;;; `supply' -- and so after `suggest'.  Nothing in structure-library or
;;; theorem-library may use it.

;;; -----------------------------------------------------------------------
;;; Plumbing

(define *preamble-max-peel* 12)
(define *preamble-max-inst* 24)

;;; The goal of the focus, or #f.
(define (pre--goal)
  (and *ps* (not (proof-done? *ps*))
       (wff-formula (sequent-node-assertion (proof-state-focus *ps*)))))

(define (pre--asms)
  (if (and *ps* (not (proof-done? *ps*)))
      (map wff-formula (sequent-node-assumptions (proof-state-focus *ps*)))
      '()))

;;; Run THUNK with output suppressed but ERRORS still caught and returned.
;;; `quietly' silences vnb-guard as well as `show', which turns an error into a
;;; silent no-op -- the trap CLAUDE.md records.  So the guard goes OUTSIDE.
(define (pre--try thunk)
  (vnb-guard (lambda () (quietly thunk))))

(define (pre--fired? r) (not (or (vnb-error? r) (vnb-warning? r))))

;;; Is LEAF still open?
(define (pre--open? leaf) (and (memq leaf (proof-leaves)) #t))

;;; -----------------------------------------------------------------------
;;; The clauses.  Each takes the clause form, runs on the CURRENT focus, and
;;; returns a list of the step forms it committed (empty = did nothing).

(define (pre--induct clause)
  (let ((before (length (proof-leaves))))
    (if (pre--fired? (pre--try (lambda () (ni))))
        (if (> (length (proof-leaves)) before) '((ni)) '())
        '())))

;;; `di' until the goal's HEAD stops changing.  Counting di's is not a way to
;;; land on a chosen goal (CLAUDE.md); looping on progress is.
(define (pre--peel clause)
  (let loop ((n 0) (out '()))
    (let ((g (pre--goal)))
      (if (or (>= n *preamble-max-peel*)
              (not (pair? g))
              (not (memq (car g) '(FORALL IMPLIES))))
          (reverse out)
          (let ((r (pre--try (lambda () (di)))))
            (if (and (pre--fired? r) (not (equal? g (pre--goal))))
                (loop (+ n 1) (cons '(di) out))
                (reverse out)))))))

(define (pre--unfold clause)
  (let loop ((ns (cdr clause)) (out '()))
    (if (null? ns)
        (reverse out)
        (let* ((g (pre--goal))
               (r (pre--try (lambda () (mac (car ns))))))
          (loop (cdr ns)
                (if (and (pre--fired? r) (not (equal? g (pre--goal))))
                    (cons (list 'mac (list 'quote (car ns))) out)
                    out))))))

;;; A universally quantified assumption, by index.
(define (pre--universal-indices)
  (let loop ((l (pre--asms)) (i 1) (out '()))
    (cond ((null? l) (reverse out))
          ((and (pair? (car l)) (eq? (caar l) 'FORALL))
           (loop (cdr l) (+ i 1) (cons i out)))
          (else (loop (cdr l) (+ i 1) out)))))

;;; The terms to instantiate at: the clause's own, or the goal's free variables
;;; that the context types.  A variable with no typing is not a witness the
;;; instantiation can use.
(define (pre--inst-terms clause)
  (if (pair? (cdr clause))
      (cdr clause)
      (let ((asms (pre--asms)))
        (filter (lambda (v)
                  (any-pred (lambda (a)
                              (and (pair? a) (memq (car a) '(IN in))
                                   (= (length a) 3) (eq? (cadr a) v)))
                            asms))
                (free-vars (or (pre--goal) '()))))))

;;; `inst+' at (IDX, TERM), committed only if the landing is USABLE.
;;;
;;; The rejection rule is the inst lane's: a landing still headed IMPLIES means
;;; the instantiation went to a theorem at the wrong argument -- it is not an
;;; error, it lands something true and unusable, and every later step then runs
;;; against a hypothesis that never arrived.  So this rehearses on a scratch
;;; state and commits only what lands an atom.
(define (pre--inst-useful? idx term)
  (let ((scratch (vnb--scratch-state)))
    (and scratch
         (eq? 'good
              (vnb--probing scratch
                (lambda ()
                  (let* ((before (map wff-formula
                                      (sequent-node-assumptions
                                       (proof-state-focus scratch))))
                         (r (pre--try (lambda () (inst+ idx term)))))
                    (if (not (pre--fired? r))
                        'bad
                        (let ((new (filter
                                    (lambda (f)
                                      (not (any-pred (lambda (b) (alpha-equiv? b f))
                                                     before)))
                                    (map wff-formula
                                         (sequent-node-assumptions
                                          (proof-state-focus scratch))))))
                          (if (any-pred (lambda (f)
                                          (not (and (pair? f) (eq? (car f) 'IMPLIES))))
                                        new)
                              'good
                              'bad))))))))))

(define (pre--instantiate clause)
  (let ((terms (pre--inst-terms clause))
        (out '()) (n 0))
    (for-each
     (lambda (term)
       (for-each
        (lambda (idx)
          (when (and (< n *preamble-max-inst*)
                     (pre--inst-useful? idx term))
            (set! n (+ n 1))
            (if (pre--fired? (pre--try (lambda () (inst+ idx term))))
                (set! out (cons (list 'inst+ idx (pre--quote term)) out)))))
        (pre--universal-indices)))
     terms)
    (reverse out)))

(define (pre--quote t) (if (or (symbol? t) (pair? t)) (list 'quote t) t))

;;; The closers, in the order a hand proof tries them: the cheap syntactic ones
;;; first, the deciding ones next, the composite last.
(define *preamble-closers*
  '((ass) (rfl) (arith) (crs) (prop) (contra) (supply)))

(define (pre--close clause)
  (let ((leaf (and *ps* (not (proof-done? *ps*)) (proof-state-focus *ps*))))
    (let loop ((cs *preamble-closers*))
      (cond ((null? cs) '())
            ((not (pre--open? leaf)) '())
            (else
             (let ((r (pre--try (lambda () (eval (car cs) user-initial-environment)))))
               (if (and (pre--fired? r) (not (pre--open? leaf)))
                   (list (car cs))
                   (loop (cdr cs)))))))))

(define (pre--run-clause clause)
  (case (car clause)
    ((induct)      (pre--induct clause))
    ((peel)        (pre--peel clause))
    ((unfold)      (pre--unfold clause))
    ((instantiate) (pre--instantiate clause))
    ((close)       (pre--close clause))
    (else (error "preamble: unknown clause -- expected one of induct, peel, unfold, instantiate, close" clause))))

;;; -----------------------------------------------------------------------
;;; The driver

(define *preamble-max-jobs* 64)

;;; A leaf born at clause k continues at clause k+1 -- it does NOT restart the
;;; list.  That is the whole termination argument, and it was learned the hard
;;; way: the induction STEP goal, `forall k in nn. IH => P(succ k)', is itself an
;;; NN-guarded universal, so an `(induct)' clause re-applied to the leaves it had
;;; just created fired `ni' again, and again, and the first run of this file did
;;; not terminate.  Restarting the clause list on a child is also wrong on the
;;; merits: the clauses are a PIPELINE, in an order the user chose, and a child
;;; is downstream of the clause that made it.
(define (preamble-clauses . clauses)
  (cond
   ((or (not *ps*) (proof-done? *ps*))
    (display ";; preamble: no open goal.") (newline) '())
   ((null? clauses)
    (error "preamble-clauses: no clauses -- expected e.g. (preamble-clauses '(induct) '(close))"))
   (else
    (let ((queue   (list (cons (proof-state-focus *ps*) clauses)))
          (steps   '())
          (stalled '())
          (jobs    0))
      (let next-job ()
        (when (and (pair? queue) (< jobs *preamble-max-jobs*))
          (let ((leaf (car (car queue)))
                (cs   (cdr (car queue))))
            (set! queue (cdr queue))
            (set! jobs (+ jobs 1))
            (when (pre--open? leaf)
              ;; A FOCUS STEP, whenever more than one leaf is open.  Without it
              ;; the emitted list is not a script: the steps for the two leaves
              ;; an induction opens interleave, and replayed flat they run
              ;; against whichever leaf the engine left in focus.  Measured
              ;; 2026-08-21 -- the first version of this file printed a
              ;; ten-step list that closed the goal here and did NOT close it
              ;; when pasted back.
              ;;
              ;; `dk-focus-goal!' (driver-kit.scm:805) takes a FRAGMENT of the
              ;; printed goal and already errors on no match and on an ambiguous
              ;; one, which is the discipline this wants; the whole goal text is
              ;; the most specific fragment available.  It lives in driver-kit,
              ;; so a proof file can cite it without citing the copilot.
              (if (pair? (cdr (proof-leaves)))
                  (set! steps
                        (append steps
                                (list (list 'dk-focus-goal!
                                            (expression->string
                                             (pre--goal-of-leaf leaf)))))))
              (let clause-loop ((cs cs))
                (cond
                 ((not (pre--open? leaf)) #t)          ; closed: done with it
                 ((null? cs)
                  (set! stalled (cons leaf stalled)))  ; clauses exhausted, still open
                 (else
                  (set-proof-state-focus! *ps* leaf)
                  (let* ((before (proof-leaves))
                         (got    (pre--run-clause (car cs)))
                         (fresh  (filter (lambda (l) (not (memq l before)))
                                         (proof-leaves))))
                    (set! steps (append steps got))
                    ;; children inherit the REST of the list
                    (for-each (lambda (l)
                                (set! queue (append queue (list (cons l (cdr cs))))))
                              fresh)
                    (clause-loop (cdr cs)))))))
            (next-job))))
      (if (>= jobs *preamble-max-jobs*)
          (begin
            (display ";; preamble: stopped at the ")
            (display *preamble-max-jobs*)
            (display "-leaf cap -- raise *preamble-max-jobs* if that was not a runaway.")
            (newline)))
      (pre--report steps (reverse stalled))
      steps))))

(define (pre--goal-of-leaf leaf)
  (wff-formula (sequent-node-assertion leaf)))

(define (pre--report steps stalled)
  (newline)
  (display ";; preamble: ") (display (length steps))
  (display " step(s) committed") (newline)
  (for-each (lambda (s) (display ";;   ") (vnb--write-form s) (newline)) steps)
  (cond
   ((null? stalled)
    (display ";; preamble: every leaf closed.  Paste the steps above into the")
    (newline)
    (display ";;   proof file -- a library theorem must not cite this file.")
    (newline))
   (else
    (display ";; preamble: ") (display (length stalled))
    (display " leaf(leaves) STILL OPEN -- the clause list did not reach them:")
    (newline)
    (for-each (lambda (l)
                (display ";;   ") (display (expression->string (pre--goal-of-leaf l)))
                (newline))
              stalled)
    (display ";;   (what-now) on each says what the panel would try next.")
    (newline))))

;;; =================================================================================
;;; THE RULE ENGINE (batch 41, 2026-09-28; notes-45; docs/preambles-2026-09-28.md).
;;;
;;; A RULE FILE is a sequence of S-expressions read by `read' (so it folds case exactly as
;;; the tree does), one per rule:
;;;
;;;   (rule NAME
;;;     (goal  PATTERN)          required; matched against the focus goal
;;;     (with  PATTERN)          zero or more; each matches SOME assumption
;;;     (guard GUARD ...)        zero or more guards, all must hold
;;;     (do    FORM)             required; a surface-command form, or (preamble NAME)
;;;     (probe WHAT)             optional: grounded | progress (default) | changed | (lands F)
;;;     (side  HOW))             only with (do (cut F)): preamble-or-owed (default) | owed
;;;
;;; PATTERNS are written in the RAW S-expression syntax the goals have (what `make-wff'
;;; of a quoted form holds, and what (dk-goal) returns): (forall ?x (implies (in ?x ?c)
;;; ?body)), (= ?p ?q), (in ?t (sep ?v ?a ?p)).  One syntax, not two: the concrete string
;;; syntax is not accepted in a rule file.  A SCHEMA VARIABLE is a symbol whose name
;;; begins with `?'.  Matching is the rewriter's first-order matcher `match-expr'
;;; (macetes.scm), lifted:
;;;   * to a SEQUENT: the goal pattern first, then each `with' pattern against the
;;;     assumptions in context order, the bindings shared (a variable bound by the goal
;;;     must match the same term, up to alpha, in an assumption); the with patterns are
;;;     matched with BACKTRACKING (a later pattern that fails sends the earlier one to its
;;;     next matching assumption), and the guards are tested on the complete binding;
;;;   * to BINDERS: a literal bound variable in a pattern matches a goal binder up to
;;;     alpha (match-expr renames both sides to a fresh name); a SCHEMA VARIABLE in binder
;;;     position -- (forall ?x ...), (sep ?v ?a ?p), (vnb-lambda ?v ?d ?b) -- binds to the
;;;     goal's bound-variable NAME, and its occurrences in the body must then be that
;;;     name.  match-expr refuses a schema variable there (a rewrite would carry the bound
;;;     variable out of scope); a rule only FIRES a tactic on the matched goal, so the
;;;     binding is harmless here, and the matcher below handles those nodes itself.
;;;
;;; GUARDS (each argument a pattern term, schema variables substituted):
;;;   (typed T C)          (IN T C) is in context up to alpha, or (IN T K) is, with K on the
;;;                        inclusion chain below C (in-rr's table: NN ZZ QQ RR CC, CCINT ->
;;;                        RR, INTERVAL -> NN).  Read off the CONTEXT, not the definedness
;;;                        certificate pi--defined? (which answers another question).
;;;   (head T SYM)         T is an application headed SYM (or is the atom SYM)
;;;   (closed T)           every free symbol of T is a registered constant or a class name
;;;   (not-in-context F)   F is not an assumption, up to alpha
;;;   (one-of T S1 S2 ...) T is one of the symbols
;;;   (occurs PAT T)       some subterm of T matches PAT (binds PAT's variables)
;;;   (unfolds T ?M)       T's head has a definitional macete (resolve-macete-name: NAME or
;;;                        NAME-def); binds ?M to it
;;;
;;; THE ACTION.  The `do' form with each schema variable replaced by its binding: in an
;;; evaluated position ?x becomes (quote VALUE), inside a quoted datum it becomes VALUE, so
;;; (fact 'thm ?t) and (cut '(in ?t zz)) both read as typed.  It is evaluated in
;;; user-initial-environment, where every tactic lives.  (preamble NAME) runs another rule
;;; file on the focus, as ONE firing.  A rule adds NO trust: the form is ordinary surface
;;; commands, each checked by the kernel, each RECORDED AS ITSELF -- the preamble records
;;; no step of its own, so the page of a proof it drove is the steps, and replays with no
;;; rule file present.
;;;
;;; THE COMMIT RULE.  A rule is TRIED when its patterns and guards match the focus.  It is
;;; run first on a SCRATCH copy of the focus sequent (vnb--scratch-state under
;;; vnb--probing, as what-now does); when its probe holds there, it is run on the live
;;; proof inside a transaction (dk--transaction) and the probe is tested again on the live
;;; outcome; the firing is COMMITTED only when both hold, and otherwise every effect of
;;; the live run is rolled back (graph, focus, script, mints, trace, undo stack).  The
;;; probe, on the leaf L the rule was tried on:
;;;   grounded   L is grounded.
;;;   changed    L is grounded, or the proof moved: L is no longer an open leaf, or new
;;;              leaves appeared -- except when the one resulting focus has L's goal and
;;;              L's assumptions again (churn).
;;;   progress   grounded, or (changed AND the number of open leaves did not grow).
;;;   (lands F)  changed, and F (substituted) is an assumption of the resulting focus.
;;; The loop tries the rules in FILE ORDER and commits the first that passes; the ones that
;;; matched and failed their probe are REJECTED (reported, nothing kept).  After a commit
;;; it restarts on the new focus, confined to the leaves that did not exist when it began
;;; (a leaf that was already open elsewhere is never touched); it stops when the proof or
;;; the starting leaf's subtree is done, when no rule commits on the focus, or at
;;; *preamble-cap* committed firings.  A rule whose matching or action RAISES is named in
;;; the report and skipped, never fatal.
;;;
;;; THE TENTATIVE CUT.  A rule (do (cut F)) (side preamble-or-owed): the cut is made; the
;;; SAME rule list, without its cut rules (depth one), is run on the side leaf F inside a
;;; transaction; if that grounds F the steps are kept (a lemma proven in place), else they
;;; are rolled back and F is left OPEN and reported by name as OWED (sketch's outcome 2).
;;; `owed' skips the attempt.  The focus returns to the main branch.  No support is ever
;;; installed: putting F in the PSS is the user's command on that leaf.
;;;
;;; PHASE 2 ENTRY POINT (the postamble's attribution replay): `preamble-propose' and
;;; `preamble-attribute' match a rule list against a (goal, assumptions) pair and compare
;;; the instantiated actions with a recorded step WITHOUT running anything and without
;;; reading *ps*.
;;; =================================================================================

(define *preamble-cap* 40)
(define *preamble-default-file* (string-append *prover-dir* "preambles/default.pre"))
(define *preamble-user-file* "~/.vnb-preamble.pre")

;;; ---------------------------------------------------------------------------------
;;; Rules

(define-record-type <pa-rule>
  (pa--make-rule name goal withs guards action probe side)
  pa-rule?
  (name   pa-rule-name)
  (goal   pa-rule-goal)
  (withs  pa-rule-withs)
  (guards pa-rule-guards)
  (action pa-rule-action)
  (probe  pa-rule-probe)
  (side   pa-rule-side))

(define (pa--svar? x)
  (and (symbol? x)
       (let ((s (symbol->string x)))
         (and (> (string-length s) 1) (char=? (string-ref s 0) #\?)))))

(define (pa--svars pat)
  (let walk ((x pat) (acc '()))
    (cond ((pa--svar? x) (if (memq x acc) acc (cons x acc)))
          ((pair? x) (walk (cdr x) (walk (car x) acc)))
          (#t acc))))

(define *pa-guard-arities*
  '((typed 2 2) (head 2 2) (closed 1 1) (not-in-context 1 1) (one-of 2 99)
    (occurs 2 2) (unfolds 2 2)))

;;; One form -> (ok . rule) or (err . message).  The message names the rule.
(define (pa--parse-rule form k)
  (let* ((nm   (and (pair? form) (pair? (cdr form)) (cadr form)))
         (tag  (if (symbol? nm)
                   (symbol->string nm)
                   (string-append "#" (number->string k))))
         (bad  (lambda (msg) (cons 'err (string-append "rule " tag ": " msg)))))
    (cond
      ((not (and (pair? form) (eq? (car form) 'rule)))
       (bad "not a (rule NAME clause ...) form"))
      ((not (symbol? nm)) (bad "the name is not a symbol"))
      ((not (list? form)) (bad "not a proper list"))
      (#t
       (let loop ((cs (cddr form)) (goal #f) (withs '()) (guards '()) (action #f)
                  (probe 'progress) (side #f))
         (cond
           ((null? cs)
            (cond ((not goal) (bad "no (goal PATTERN) clause"))
                  ((not action) (bad "no (do FORM) or (ask TEXT) clause"))
                  ((and side (not (and (pair? action) (eq? (car action) 'cut)
                                       (= (length action) 2))))
                   (bad "a (side ...) clause needs the action (cut F)"))
                  (#t (cons 'ok (pa--make-rule nm goal (reverse withs) (reverse guards)
                                               action probe side)))))
           (#t
            (let ((c (car cs)))
              (if (not (and (pair? c) (symbol? (car c)) (list? c)))
                  (bad (string-append "a clause is not a list headed by a symbol: "
                                      (write-to-string c)))
                  (case (car c)
                    ((goal)
                     (cond (goal (bad "two (goal ...) clauses"))
                           ((not (= (length c) 2)) (bad "(goal PATTERN) takes one pattern"))
                           (#t (loop (cdr cs) (cadr c) withs guards action probe side))))
                    ((with)
                     (if (null? (cdr c))
                         (bad "(with) needs a pattern")
                         (loop (cdr cs) goal (append (reverse (cdr c)) withs) guards action
                               probe side)))
                    ((guard)
                     (let ((badg (find (lambda (g)
                                         (let ((ar (and (pair? g) (assq (car g) *pa-guard-arities*))))
                                           (not (and ar (list? g)
                                                     (<= (cadr ar) (length (cdr g)) (caddr ar))))))
                                       (cdr c))))
                       (if badg
                           (bad (string-append "unknown or malformed guard "
                                               (write-to-string badg)
                                               " (known: typed head closed not-in-context"
                                               " one-of occurs unfolds)"))
                           (loop (cdr cs) goal withs (append (reverse (cdr c)) guards)
                                 action probe side))))
                    ;; (ask TEXT): the rule kind for a step no rule can take -- a witness, the
                    ;; choice of a lemma, an estimate (the user, 2026-10-01: "ask the user for
                    ;; advice").  When it matches, the loop STOPS and the report carries the
                    ;; advice beside the goal it applies to; nothing is run.
                    ((ask)
                     (cond (action (bad "two action clauses ((do ...) / (ask ...))"))
                           ((not (and (= (length c) 2) (string? (cadr c))))
                            (bad "(ask TEXT) takes one string"))
                           (#t (loop (cdr cs) goal withs guards (list 'ask (cadr c)) probe side))))
                    ((do)
                     (cond (action (bad "two action clauses ((do ...) / (ask ...))"))
                           ((not (and (= (length c) 2) (pair? (cadr c))))
                            (bad "(do FORM) takes one form"))
                           (#t (loop (cdr cs) goal withs guards (cadr c) probe side))))
                    ((probe)
                     (let ((p (and (= (length c) 2) (cadr c))))
                       (if (or (memq p '(grounded progress changed))
                               (and (pair? p) (eq? (car p) 'lands) (= (length p) 2)))
                           (loop (cdr cs) goal withs guards action p side)
                           (bad (string-append "unknown probe " (write-to-string (cdr c))
                                               " (known: grounded progress changed (lands F))")))))
                    ((side)
                     (let ((h (and (= (length c) 2) (cadr c))))
                       (if (memq h '(preamble-or-owed owed))
                           (loop (cdr cs) goal withs guards action probe h)
                           (bad "(side HOW): HOW is preamble-or-owed or owed"))))
                    (else (bad (string-append "unknown clause (" (symbol->string (car c))
                                              " ...)")))))))))))))

;;; Parse a list of forms.  -> (values rules errors); a malformed rule is left out and
;;; its message kept.  A cut rule with no side clause gets the default.
(define (pa-parse-rules forms)
  (let loop ((fs forms) (k 1) (rules '()) (errs '()))
    (if (null? fs)
        (values (reverse rules) (reverse errs))
        (let ((r (pa--parse-rule (car fs) k)))
          (if (eq? (car r) 'ok)
              (let* ((ru (cdr r))
                     (ru (if (and (not (pa-rule-side ru)) (pair? (pa-rule-action ru))
                                  (eq? (car (pa-rule-action ru)) 'cut))
                             (pa--make-rule (pa-rule-name ru) (pa-rule-goal ru) (pa-rule-withs ru)
                                            (pa-rule-guards ru) (pa-rule-action ru)
                                            (pa-rule-probe ru) 'preamble-or-owed)
                             ru)))
                (loop (cdr fs) (+ k 1) (cons ru rules) errs))
              (loop (cdr fs) (+ k 1) rules (cons (cdr r) errs)))))))

;;; Read a rule file.  -> (rules errors) or (#f message) when the file cannot be read.
(define (pa-read-rule-file path)
  (cond
    ((not (file-exists? path)) (list #f (string-append "no such rule file: " path)))
    (#t
     (let ((forms (call-with-current-continuation
                   (lambda (k)
                     (with-exception-handler
                      (lambda (e)
                        (k (string-append "cannot read " path ": "
                                          (if (condition? e) (condition/report-string e)
                                              (write-to-string e)))))
                      (lambda ()
                        (call-with-input-file path
                          (lambda (port)
                            (let loop ((acc '()))
                              (let ((x (read port)))
                                (if (eof-object? x) (reverse acc) (loop (cons x acc)))))))))))))
       (if (string? forms)
           (list #f forms)
           (call-with-values (lambda () (pa-parse-rules forms))
             (lambda (rules errs) (list rules errs))))))))

;;; Which file: the argument (a symbol names preambles/NAME.pre, a string is a path), else
;;; the user's file when it exists, else the shipped default.
(define (pa--source arg)
  (cond ((string? arg) arg)
        ((symbol? arg) (string-append *prover-dir* "preambles/" (symbol->string arg) ".pre"))
        ((file-exists? *preamble-user-file*) *preamble-user-file*)
        (#t *preamble-default-file*)))

;;; ---------------------------------------------------------------------------------
;;; The matcher (PURE: patterns, terms, a binding alist; no proof state)

(define *pa-binder-heads-3* '(FORALL FORSOME IOTA COMP))        ; (H v body)
(define *pa-binder-heads-4* '(SEP BIG-UNION VNB-LAMBDA))        ; (H v dom body)

(define (pa--replace-sym x from to)
  (cond ((eq? x from) to)
        ((pair? x) (cons (pa--replace-sym (car x) from to) (pa--replace-sym (cdr x) from to)))
        (#t x)))

;;; Does PAT carry a schema variable in binder position anywhere?
(define (pa--binder-svar-in? pat)
  (and (pair? pat)
       (or (and (memq (car pat) (append *pa-binder-heads-3* *pa-binder-heads-4*))
                (pair? (cdr pat)) (pa--svar? (cadr pat)))
           (let loop ((x pat))
             (cond ((pair? x) (or (pa--binder-svar-in? (car x)) (loop (cdr x))))
                   (#t #f))))))

(define (pa--bind b var val) (merge-subst b (list (cons var val))))

;;; Match PAT against EXPR extending the bindings B; #f on failure.
(define (pa-match pat expr b)
  (cond
    ((not b) #f)
    ((not (pa--binder-svar-in? pat))
     (let ((m (match-expr pat expr (pa--svars pat))))
       (and m (merge-subst b m))))
    ;; a schema variable in binder position: bind it to the goal's bound name
    ((and (memq (car pat) (append *pa-binder-heads-3* *pa-binder-heads-4*))
          (pa--svar? (cadr pat)))
     (and (pair? expr) (eq? (car expr) (car pat)) (list? expr) (list? pat)
          (= (length expr) (length pat))
          (let ((ev (cadr expr)) (pv (cadr pat)))
            (let ((b1 (pa--bind b pv ev)))
              (and b1
                   (let loop ((ps (cddr pat)) (es (cddr expr)) (bb b1))
                     (cond ((not bb) #f)
                           ((null? ps) bb)
                           (#t (loop (cdr ps) (cdr es)
                                     (pa-match (pa--replace-sym (car ps) pv ev) (car es) bb))))))))))
    ;; a literal binder above a binder-position schema variable: alpha, as match-expr does
    ((and (memq (car pat) *pa-binder-heads-3*) (pair? (cdr pat)) (symbol? (cadr pat)))
     (and (pair? expr) (eq? (car expr) (car pat)) (list? expr) (= (length expr) 3)
          (let ((pv (cadr pat)) (ev (cadr expr)))
            (if (eq? pv ev)
                (pa-match (caddr pat) (caddr expr) b)
                (let ((z (fresh-var pv (caddr pat) (caddr expr))))
                  (pa-match (subst-free pv z (caddr pat)) (subst-free ev z (caddr expr)) b))))))
    ;; any other node: position by position
    ((and (pair? expr) (list? pat) (list? expr) (= (length pat) (length expr))
          (or (pair? (car pat)) (pa--svar? (car pat)) (eq? (car pat) (car expr))))
     (let loop ((ps pat) (es expr) (bb b))
       (cond ((not bb) #f)
             ((null? ps) bb)
             (#t (loop (cdr ps) (cdr es) (pa-match (car ps) (car es) bb))))))
    (#t #f)))

;;; Substitute bindings into a pattern-term (a datum): every schema variable must be bound.
(define (pa--subst-datum x b)
  (cond ((pa--svar? x)
         (let ((p (assq x b)))
           (if p (cdr p) (error "preamble: the schema variable is not bound by the patterns:" x))))
        ((pair? x) (cons (pa--subst-datum (car x) b) (pa--subst-datum (cdr x) b)))
        (#t x)))

;;; The action form: ?x -> 'VALUE in evaluated positions, VALUE inside a quote.
(define (pa-instantiate-form form b)
  (cond ((pa--svar? form) (list 'quote (pa--subst-datum form b)))
        ((and (pair? form) (eq? (car form) 'quote) (pair? (cdr form)))
         (list 'quote (pa--subst-datum (cadr form) b)))
        ((pair? form) (cons (pa-instantiate-form (car form) b)
                            (pa-instantiate-form (cdr form) b)))
        (#t form)))

(define (pa--alpha-member? f fs) (any (lambda (a) (alpha-equiv? a f)) fs))

(define (pa--head-sym t) (cond ((symbol? t) t) ((and (pair? t) (symbol? (car t))) (car t)) (#t #f)))

(define (pa--typed? t c asms)
  (or (pa--alpha-member? (list 'IN t c) asms)
      (and (symbol? c)
           (any (lambda (a)
                  (and (pair? a) (eq? (car a) 'IN) (= (length a) 3) (equal? (cadr a) t)
                       (let ((h (pa--head-sym (caddr a))))
                         (and h (not (eq? h c))
                              (let ((route (in-rr--inclusion-route h c)))
                                (and route
                                     (every (lambda (thm) (hash-table-ref/default *theorem-table* thm #f))
                                            route)))))))
                asms))))

(define (pa--closed? t)
  (every (lambda (v)
           (or (hash-table-ref/default *constant-registry* v #f)
               (memq v *class-name-constants*)))
         (free-vars t)))

;;; One guard.  -> the (possibly extended) bindings, or #f.
(define (pa--guard g b asms)
  (let ((arg (lambda (x) (pa--subst-datum x b))))
    (case (car g)
      ((typed) (and (pa--typed? (arg (cadr g)) (arg (caddr g)) asms) b))
      ((head) (let ((t (arg (cadr g)))) (and (eq? (pa--head-sym t) (caddr g)) b)))
      ((closed) (and (pa--closed? (arg (cadr g))) b))
      ((not-in-context) (and (not (pa--alpha-member? (arg (cadr g)) asms)) b))
      ((one-of) (and (memq (arg (cadr g)) (cddr g)) b))
      ((occurs)
       (let ((pat (cadr g)) (t (arg (caddr g))))
         ;; NB the tree's `any' (sequents.scm) returns #t, not the value: walk by hand
         (let walk ((x t))
           (or (pa-match pat x b)
               (and (pair? x) (list? x)
                    (let loop ((xs x))
                      (and (pair? xs) (or (walk (car xs)) (loop (cdr xs))))))))))
      ((unfolds)
       (let* ((h (pa--head-sym (arg (cadr g))))
              (m (and h (resolve-macete-name h))))
         (and m (pa--bind b (caddr g) m))))
      (else (error "preamble: unknown guard" g)))))

;;; Match RULE against the sequent (GOAL, ASMS).  -> the bindings, or #f.  PURE.
(define (pa-match-rule rule goal asms)
  (let ((b0 (pa-match (pa-rule-goal rule) goal '())))
    (and b0
         (let try ((ws (pa-rule-withs rule)) (b b0))
           (if (null? ws)
               (let gl ((gs (pa-rule-guards rule)) (bb b))
                 (cond ((not bb) #f) ((null? gs) bb) (#t (gl (cdr gs) (pa--guard (car gs) bb asms)))))
               (let next ((as asms))
                 (and (pair? as)
                      (or (let ((b1 (pa-match (car ws) (car as) b)))
                            (and b1 (try (cdr ws) b1)))
                          (next (cdr as))))))))))

;;; PHASE 2 ENTRY POINTS.  PURE: no *ps*, nothing run.
;;;   (preamble-propose RULES GOAL ASMS)  -> ((name bindings form) ...) for every rule that
;;;                                          matches, in file order; a rule whose matching
;;;                                          raises is left out
;;;   (preamble-attribute RULES GOAL ASMS STEP)
;;;                                       -> (confirmed candidates): the names whose
;;;                                          instantiated action is the recorded STEP (the
;;;                                          script's (cmd . args) with quoted arguments,
;;;                                          compared after unquoting both), and the names
;;;                                          that matched with another action
(define (preamble-propose rules goal asms)
  (filter-map
   (lambda (ru)
     (let ((b (call-with-current-continuation
               (lambda (k) (with-exception-handler (lambda (e) (k #f))
                             (lambda () (pa-match-rule ru goal asms)))))))
       (and b (list (pa-rule-name ru) b (pa-instantiate-form (pa-rule-action ru) b)))))
   rules))

(define (pa--unquote-form f)
  (if (pair? f)
      (cons (car f) (map (lambda (a) (if (and (pair? a) (eq? (car a) 'quote)) (cadr a) a)) (cdr f)))
      f))

(define (preamble-attribute rules goal asms step)
  (let ((props (preamble-propose rules goal asms))
        (want  (pa--unquote-form step)))
    (list (filter-map (lambda (p) (and (equal? (pa--unquote-form (caddr p)) want) (car p))) props)
          (filter-map (lambda (p) (and (not (equal? (pa--unquote-form (caddr p)) want)) (car p))) props))))

;;; ---------------------------------------------------------------------------------
;;; Firing: the scratch probe, the live commit, the outcome of a step

;;; Evaluate FORM; an error comes back as (pa-raised . message), never raised.
(define (pa--eval form)
  (call-with-current-continuation
   (lambda (k)
     (with-exception-handler
      (lambda (e)
        (k (cons 'pa-raised (if (condition? e) (condition/report-string e) (write-to-string e)))))
      (lambda () (eval form user-initial-environment))))))

(define (pa--raised? v) (and (pair? v) (eq? (car v) 'pa-raised)))

;;; Before a step: the focus leaf, the open leaves, its goal and assumptions.
(define (pa--snap)
  (let ((leaf (proof-state-focus *ps*)))
    (list leaf (proof-open-leaves *ps*) (dk-goal-of leaf) (dk-asms-of leaf))))

;;; After a step, against SNAP.  -> alist: grounded changed n-before n-after goal landed new.
(define (pa--outcome snap)
  (let* ((leaf    (car snap))
         (before  (cadr snap))
         (goal0   (caddr snap))
         (asms0   (cadddr snap))
         (done    (proof-done? *ps*))
         (after   (if done '() (proof-open-leaves *ps*)))
         (new     (filter (lambda (l) (not (memq l before))) after))
         (focus   (and (not done) (proof-state-focus *ps*)))
         (goal1   (and focus (dk-goal-of focus)))
         (asms1   (if focus (dk-asms-of focus) '()))
         (landed  (filter (lambda (a) (not (pa--alpha-member? a asms0))) asms1))
         (ground  (or done (sequent-node-grounded? leaf)))
         (open?   (and (memq leaf after) #t))
         (churn   (and (not ground) (= (length new) 1) focus (eq? focus (car new))
                       (alpha-equiv? goal1 goal0) (null? landed)
                       (= (length asms1) (length asms0))))
         (changed (or ground
                      (and (not churn) (or (not open?) (pair? new))))))
    (list (cons 'grounded ground) (cons 'changed changed)
          (cons 'n-before (length before)) (cons 'n-after (length after))
          (cons 'goal goal1) (cons 'landed landed) (cons 'new new) (cons 'focus focus)
          (cons 'asms-before asms0)
          ;; the leaf list emptied while the proof is not grounded: a step produced a
          ;; node outside the leaf list (a cut, have! or fact of a formula already in
          ;; context is a silent self-loop with no main branch -- CLAUDE.md); the first
          ;; postamble met it, 2026-10-02, on a `fact' re-landing an equation
          (cons 'vanished (and (not done) (null? after))))))

(define (pa--get o k) (cdr (assq k o)))

(define (pa--probe-holds? probe o b asms-after)
  (cond ((eq? probe 'grounded) (pa--get o 'grounded))
        ((eq? probe 'changed) (pa--get o 'changed))
        ((eq? probe 'progress)
         (or (pa--get o 'grounded)
             (and (pa--get o 'changed) (<= (pa--get o 'n-after) (pa--get o 'n-before)))))
        ;; (lands F): F is NEW -- absent before the step, present after it.  A step that
        ;; re-lands a formula already in context "changes" the graph (a fact's chain lands
        ;; its intermediate forms again) and, repeated, self-loops: refuse it.
        ((and (pair? probe) (eq? (car probe) 'lands))
         (let ((f (pa--subst-datum (cadr probe) b)))
           (and (pa--get o 'changed)
                (not (pa--alpha-member? f (pa--get o 'asms-before)))
                (pa--alpha-member? f asms-after))))
        (#t #f)))

(define (pa--focus-asms) (if (proof-done? *ps*) '() (dk-asms)))

;;; What the step did, in words.
(define (pa--effect-string o)
  (cond
    ((pa--get o 'grounded) "closed the goal")
    (#t
     (let* ((new (pa--get o 'new)) (landed (pa--get o 'landed)) (goal (pa--get o 'goal))
            (parts
             (append
              (if (> (length new) 1)
                  (list (string-append "opened " (number->string (length new)) " leaves: "
                                       (pa--join (map (lambda (l) (expression->string (dk-goal-of l))) new)
                                                 "; ")))
                  (if goal (list (string-append "goal now " (expression->string goal))) '()))
              (if (pair? landed)
                  (list (string-append "landed " (pa--join (map expression->string landed) ", ")))
                  '()))))
       (if (null? parts) "no visible change" (pa--join parts " -- "))))))

(define (pa--join strs sep)
  (if (null? strs) ""
      (fold-left (lambda (acc s) (string-append acc sep s)) (car strs) (cdr strs))))

;;; A verdict alist's report text (zero-it's), first line only, or #f.
(define (pa--value-note v)
  (and (list? v) (every pair? v) (assq 'report v)
       (let ((r (cdr (assq 'report v))))
         (and (string? r) (> (string-length r) 0)
              (let ((lines (burst-string r #\newline #t)))
                (pa--join (filter (lambda (l) (> (string-length l) 0))
                                  (map (lambda (l) (if (string-prefix? ";; " l) (string-tail l 3) l)) lines))
                          " | "))))))

;;; The engine's state for one (preamble) call, nested runs included.
(define-record-type <pa-state>
  (pa--make-state rules steps fired rejected raised owed asked stop)
  pa-state?
  (rules    pa-state-rules    set-pa-state-rules!)
  (steps    pa-state-steps    set-pa-state-steps!)
  (fired    pa-state-fired    set-pa-state-fired!)      ; newest first: (name form effect goal)
  (rejected pa-state-rejected set-pa-state-rejected!)   ; newest first: (name form reason goal)
  (raised   pa-state-raised   set-pa-state-raised!)     ; newest first: (name message)
  (owed     pa-state-owed     set-pa-state-owed!)       ; newest first: (formula . leaf)
  (asked    pa-state-asked    set-pa-state-asked!)      ; newest first: (name text goal)
  (stop     pa-state-stop     set-pa-state-stop!))

(define (pa--push-fired! st x) (set-pa-state-fired! st (cons x (pa-state-fired st))))
(define (pa--push-rejected! st x)
  (if (not (member x (pa-state-rejected st)))
      (set-pa-state-rejected! st (cons x (pa-state-rejected st)))))
(define (pa--push-raised! st x) (set-pa-state-raised! st (cons x (pa-state-raised st))))

;;; A nested run (a cut's side leaf, a (preamble NAME) action) shares the counters and the
;;; lists of its parent but has its own rules; `pa--sub' makes it and `pa--merge!' folds
;;; its lists back (a rolled-back sub-run's firings are reported as tried, not as fired).
(define (pa--sub st rules)
  (pa--make-state rules (pa-state-steps st) '() '() '() '() '() #f))

(define (pa--merge! st sub kept? #!optional tag)
  (let ((tag (if (default-object? tag) "" tag)))
    (set-pa-state-steps! st (if kept? (pa-state-steps sub) (pa-state-steps st)))
    ;; a rolled-back run's firings are reported as REJECTED: nothing of them was kept
    (if kept?
        (set-pa-state-fired! st
          (append (map (lambda (x) (list (car x) (cadr x) (string-append tag (caddr x)) (cadddr x)))
                       (pa-state-fired sub))
                  (pa-state-fired st)))
        (set-pa-state-rejected! st
          (append (map (lambda (x) (list (car x) (cadr x)
                                         (string-append tag "rolled back, the run did not close it: "
                                                        (caddr x))
                                         (cadddr x)))
                       (pa-state-fired sub))
                  (pa-state-rejected st))))
    (set-pa-state-rejected! st
      (append (map (lambda (x) (list (car x) (cadr x) (string-append tag (caddr x)) (cadddr x)))
                   (pa-state-rejected sub))
              (pa-state-rejected st))))
  (set-pa-state-raised! st (append (pa-state-raised sub) (pa-state-raised st)))
  (set-pa-state-asked! st (append (pa-state-asked sub) (pa-state-asked st)))
  (if kept? (set-pa-state-owed! st (append (pa-state-owed sub) (pa-state-owed st)))))

;;; The thunk that performs an action FORM (a (preamble NAME) form runs a sub-loop).
(define (pa--action-thunk st form)
  (if (and (pair? form) (eq? (car form) 'preamble))
      (let* ((arg (and (pair? (cdr form)) (cadr form)))
             (arg (if (and (pair? arg) (eq? (car arg) 'quote)) (cadr arg) arg))
             (rd  (pa-read-rule-file (pa--source arg))))
        (lambda ()
          (if (not (car rd))
              (cons 'pa-raised (cadr rd))
              (let ((sub (pa--sub st (car rd))))
                (pa--loop! sub)
                (cons 'pa-sub sub)))))
      (lambda () (pa--eval form))))

;;; Try RULE (bindings B, instantiated FORM) on the focus.  -> #t when committed.
(define (pa--fire! st rule b form)
  (let* ((probe (pa-rule-probe rule))
         (goal0 (dk-goal))
         (scratch (vnb--scratch-state))
         (trial (vnb--probing scratch
                  (lambda ()
                    (let* ((snap (pa--snap))
                           (v    ((pa--action-thunk (pa--sub st (pa-state-rules st)) form)))
                           (o    (pa--outcome snap)))
                      (list v o (pa--probe-holds? probe o b (pa--focus-asms)))))))
         (v (car trial)) (o (cadr trial)) (ok (caddr trial)))
    (cond
      ((pa--raised? v)
       (pa--push-raised! st (list (pa-rule-name rule) (cdr v)))
       #f)
      ((not ok)
       (pa--push-rejected! st (list (pa-rule-name rule) form
                                    (pa--reject-reason probe o v) goal0))
       #f)
      (#t
       (let* ((live-o #f) (live-v #f) (committed #f)
              ;; the tactics' own chatter ("ineq: closed by Farkas ...") is not printed:
              ;; the report block says what each firing did
              (chatter
               (with-output-to-string
                 (lambda ()
                   (set! committed
               (dk--transaction
                (lambda ()
                  (let* ((snap (pa--snap))
                         (v    ((pa--action-thunk st form)))
                         (o    (pa--outcome snap)))
                    (set! live-o o) (set! live-v v)
                    (and (not (pa--raised? v))
                         (pa--probe-holds? probe o b (pa--focus-asms)))))))))))
         (cond
           ((and committed (pa--get live-o 'vanished))
            ;; committed by its probe, but the leaf list vanished under it: report it
            (set-pa-state-steps! st (+ (pa-state-steps st) 1))
            (pa--push-fired! st (list (pa-rule-name rule) form
                                      "LEFT NO OPEN LEAF while the proof is not grounded (a self-loop: the step landed a formula already in context)"
                                      goal0))
            #t)
           (committed
            (if (and (pair? live-v) (eq? (car live-v) 'pa-sub))
                (pa--merge! st (cdr live-v) #t
                            (string-append "inside " (write-to-string form) ": ")))
            (set-pa-state-steps! st (+ (pa-state-steps st) 1))
            (pa--push-fired! st (list (pa-rule-name rule) form
                                      (let ((note (pa--value-note live-v)))
                                        (if note
                                            (string-append (pa--effect-string live-o) " [" note "]")
                                            (pa--effect-string live-o)))
                                      goal0))
            #t)
           (#t
            (pa--push-rejected! st (list (pa-rule-name rule) form
                                         (string-append "held on the scratch copy but not on the live proof"
                                                        (if (pa--raised? live-v)
                                                            (string-append " (" (cdr live-v) ")") ""))
                                         goal0))
            #f)))))))

(define (pa--reject-reason probe o v)
  (let ((why (cond ((not (pa--get o 'changed)) "no change")
                   ((eq? probe 'grounded) "did not close the goal")
                   ((eq? probe 'progress)
                    (string-append "the open leaves grew from " (number->string (pa--get o 'n-before))
                                   " to " (number->string (pa--get o 'n-after))))
                   ((pair? probe) (string-append "did not land " (write-to-string (cadr probe))))
                   (#t "probe failed")))
        (note (pa--value-note v)))
    (if note (string-append why " [" note "]") why)))

;;; The tentative cut.  -> #t (a cut is always committed once made).
(define (pa--fire-cut! st rule b form)
  (let* ((f    (pa--subst-datum (let ((a (cadr (pa-rule-action rule))))
                                  (if (and (pair? a) (eq? (car a) 'quote)) (cadr a) a))
                                b))
         (goal0 (dk-goal)))
    (if (pa--alpha-member? f (dk-asms))
        (begin (pa--push-rejected! st (list (pa-rule-name rule) form "the claim is already in context" goal0))
               #f)
        (let* ((side-run #f)
               (new  (dk-opened (lambda () (cut f))))
               (side (any-pred (lambda (s) (alpha-equiv? (dk-goal-of s) f)) new))
               (main (any-pred (lambda (s) (not (eq? s side))) new)))
          (cond
            ((not main)
             (pa--push-raised! st (list (pa-rule-name rule) "cut left no main branch"))
             #f)
            (#t
             (set-pa-state-steps! st (+ (pa-state-steps st) 1))
             (let ((how
                    (cond
                      ((or (not side) (sequent-node-grounded? side)) "the side was already proven")
                      ((eq? (pa-rule-side rule) 'owed)
                       (set-pa-state-owed! st (cons (cons f side) (pa-state-owed st)))
                       "side left OWED (side owed)")
                      (#t
                       (let* ((sub  (pa--sub st (filter (lambda (r) (not (pa-rule-side r)))
                                                       (pa-state-rules st))))
                              (kept (dk--transaction
                                     (lambda ()
                                       (dk-focus! side)
                                       (pa--loop! sub)
                                       (sequent-node-grounded? side)))))
                         (set! side-run (cons sub kept))
                         (if kept
                             (string-append "side proved by the preamble in "
                                            (number->string (length (pa-state-fired sub))) " firing(s)")
                             (begin
                               (set-pa-state-owed! st (cons (cons f side) (pa-state-owed st)))
                               (string-append "side NOT proved, left OWED ("
                                              (or (pa-state-stop sub) "stalled") ")"))))))))
               (if (and (not (sequent-node-grounded? main)) (memq main (proof-open-leaves *ps*))
                        (not (eq? (proof-state-focus *ps*) main)))
                   (dk-focus! main))
               (pa--push-fired! st (list (pa-rule-name rule) form how goal0))
               (if side-run
                   (pa--merge! st (car side-run) (cdr side-run)
                               (string-append "on the side leaf " (expression->string f) ": ")))
               #t)))))))

;;; (pa-ineq!) -- the default preamble's real-comparison action: `ineq' over every context
;;; premise it can use.  Bare (ineq) passes NO premise, and one uncertifiable premise poisons
;;; the call, so the premises are chosen by contra's own filter (contra.scm: order formulas
;;; whose atoms are all certified in RR), after contra's two typing steps (land the NN typings
;;; the context fires, lift them to RR by nn-in-rr).  Every step is a surface command recorded
;;; as itself; the page reads (fact ...) ... (ineq 2 5).  NOT `supply': supply's steps go
;;; through apply-recorded-cmd!, which records nothing, so a proof it closes has a page that
;;; does not replay (batch 41 finding).
(define (pa-ineq!)
  (contra--land-nn-typings!)
  (contra--lift-to-rr!)
  (apply ineq (contra--usable-indices)))

;;; ---------------------------------------------------------------------------------
;;; The loop

;;; One step on the focus: the first matching rule whose probe holds.  -> #t if committed.
(define (pa--step! st)
  (let* ((goal (dk-goal)) (asms (dk-asms)) (matched 0))
    (let loop ((rs (pa-state-rules st)))
      (cond
        ((null? rs)
         (set-pa-state-stop! st
           (if (= matched 0)
               (string-append "no rule matches the goal " (expression->string goal))
               (string-append "every rule that matched was rejected on " (expression->string goal))))
         #f)
        (#t
         (let* ((ru (car rs))
                (b  (call-with-current-continuation
                     (lambda (k)
                       (with-exception-handler
                        (lambda (e)
                          (pa--push-raised! st (list (pa-rule-name ru)
                                                     (if (condition? e) (condition/report-string e)
                                                         (write-to-string e))))
                          (k #f))
                        (lambda ()
                          (let ((bb (pa-match-rule ru goal asms)))
                            ;; the action is instantiated here, inside the handler: an
                            ;; unbound schema variable is this rule's error, not the loop's
                            (and bb (cons bb (pa-instantiate-form (pa-rule-action ru) bb))))))))))
           (if (not b)
               (loop (cdr rs))
               (let ((form (cdr b)) (b (car b)))
                 (set! matched (+ matched 1))
                 (cond
                   ((and (pair? form) (eq? (car form) 'ask))
                    (set-pa-state-asked! st (cons (list (pa-rule-name ru) (cadr form) goal)
                                                  (pa-state-asked st)))
                    (set-pa-state-stop! st (string-append "the rule " (symbol->string (pa-rule-name ru))
                                                          " asks the user: " (cadr form)))
                    'ask)
                   ((if (pa-rule-side ru) (pa--fire-cut! st ru b form) (pa--fire! st ru b form))
                    #t)
                   (#t (loop (cdr rs))))))))))))

;;; Run the rules from the current focus.  The leaves open when it starts (other than the
;;; focus) are never touched; owed side leaves are left alone.  -> the status symbol.
(define (pa--loop! st)
  (let ((home (if (proof-done? *ps*)
                  '()
                  (filter (lambda (l) (not (eq? l (proof-state-focus *ps*)))) (proof-open-leaves *ps*)))))
    (let loop ()
      (let ((work (if (proof-done? *ps*)
                      '()
                      (filter (lambda (l) (and (not (memq l home))
                                               (not (any (lambda (o) (eq? (cdr o) l)) (pa-state-owed st)))))
                              (proof-open-leaves *ps*)))))
        (cond
          ;; the leaf list is empty but the proof is NOT grounded: a step produced a node
          ;; outside the leaf list (a self-loop; see 'vanished in pa--outcome).  Say so,
          ;; never "done".
          ((and (null? work) (not (proof-done? *ps*)) (null? (pa-state-owed st))
                (null? (proof-open-leaves *ps*)))
           (set-pa-state-stop! st "the open-leaf list is empty but the proof is not grounded: a step landed a formula already in context (a self-loop); undo it")
           'broken)
          ((null? work)
           (set-pa-state-stop! st (if (null? (pa-state-owed st))
                                      "done: the goal is proved"
                                      "done up to the owed claims"))
           (if (null? (pa-state-owed st)) 'done 'owed))
          ((>= (pa-state-steps st) *preamble-cap*)
           (set-pa-state-stop! st (string-append "the cap: " (number->string *preamble-cap*)
                                                 " committed firings (*preamble-cap*)"))
           'cap)
          ;; the workspace's time budget (vnb-with-budget, interactive.scm, 2026-09-30):
          ;; stop here, with the report, rather than be escaped from mid-firing
          ((vnb-budget-exhausted?)
           (set-pa-state-stop! st "the time budget ran out (vnb-command-budget in Emacs; the rules fired so far are kept)")
           'budget)
          (#t
           (if (not (memq (proof-state-focus *ps*) work)) (dk-focus! (car work)))
           (let ((r (pa--step! st)))
             (cond ((eq? r 'ask) 'ask)
                   (r (loop))
                   (#t 'stalled)))))))))

;;; ---------------------------------------------------------------------------------
;;; The command

(define (pa--form-string f) (write-to-string f))

(define (pa--report-lines st file errs status)
  (append
   (list (string-append ";; preamble: rules from " file " (" (number->string (length (pa-state-rules st)))
                        " rule(s))"))
   (map (lambda (e) (string-append ";;   MALFORMED  " e " -- left out")) errs)
   (map (lambda (x) (string-append ";;   fired     " (symbol->string (car x)) ": "
                                   (pa--form-string (cadr x)) " -- " (caddr x)))
        (reverse (pa-state-fired st)))
   (map (lambda (x) (string-append ";;   rejected  " (symbol->string (car x)) ": "
                                   (pa--form-string (cadr x)) " on " (expression->string (cadddr x))
                                   " -- " (caddr x)))
        (reverse (pa-state-rejected st)))
   (map (lambda (x) (string-append ";;   RAISED    " (symbol->string (car x)) ": " (cadr x)
                                   " -- skipped"))
        (reverse (pa-state-raised st)))
   (map (lambda (o) (string-append ";;   OWED      " (expression->string (car o))))
        (reverse (pa-state-owed st)))
   (map (lambda (a) (string-append ";;   ASK       " (symbol->string (car a)) ": " (cadr a)
                                   " -- on " (expression->string (caddr a))))
        (reverse (pa-state-asked st)))
   (list (string-append ";; preamble: " (symbol->string status) " after "
                        (number->string (pa-state-steps st)) " firing(s) -- "
                        (or (pa-state-stop st) "")))))

(define (pa--verdict status st file lines)
  (list (cons 'status status)
        (cons 'steps (pa-state-steps st))
        (cons 'fired (reverse (pa-state-fired st)))
        (cons 'rejected (reverse (pa-state-rejected st)))
        (cons 'raised (reverse (pa-state-raised st)))
        (cons 'owed (reverse (map car (pa-state-owed st))))
        (cons 'asked (reverse (pa-state-asked st)))
        (cons 'stop (pa-state-stop st))
        (cons 'file file)
        (cons 'report (pa--join lines "\n"))))

(define (preamble-status v)   (cdr (assq 'status v)))
(define (preamble-steps v)    (cdr (assq 'steps v)))
(define (preamble-fired v)    (cdr (assq 'fired v)))
(define (preamble-rejected v) (cdr (assq 'rejected v)))
(define (preamble-raised v)   (cdr (assq 'raised v)))
(define (preamble-owed v)     (cdr (assq 'owed v)))
(define (preamble-asked v)    (cdr (assq 'asked v)))      ; ((name text goal) ...)
(define (preamble-report v)   (cdr (assq 'report v)))

(define (pa--flush! lines)
  (vnb-report-reset!)
  (for-each vnb-report! lines)
  (unless *vnb-quiet*
    (display ";;VNB-REPORT-BEGIN") (newline)
    (for-each (lambda (l) (display l) (newline)) lines)
    (display ";;VNB-REPORT-END") (newline)))

(define (pa--run arg)
  (let* ((file (pa--source arg))
         (rd   (pa-read-rule-file file)))
    (cond
      ((not (car rd))
       (let ((lines (list (string-append ";; preamble: " (cadr rd) "; nothing done"))))
         (pa--flush! lines)
         (list (cons 'status 'error) (cons 'steps 0) (cons 'fired '()) (cons 'rejected '())
               (cons 'raised '()) (cons 'owed '()) (cons 'asked '()) (cons 'stop (cadr rd)) (cons 'file file)
               (cons 'report (car lines)))))
      ((not (and (proof-state? *ps*) (not (proof-done? *ps*))))
       (let ((lines (list ";; preamble: no open goal; nothing done")))
         (pa--flush! lines)
         (list (cons 'status 'error) (cons 'steps 0) (cons 'fired '()) (cons 'rejected '())
               (cons 'raised '()) (cons 'owed '()) (cons 'asked '()) (cons 'stop "no open goal") (cons 'file file)
               (cons 'report (car lines)))))
      (#t
       (let* ((st     (pa--make-state (car rd) 0 '() '() '() '() '() #f))
              (status (pa--loop! st))
              (lines  (pa--report-lines st file (cadr rd) status)))
         (if (not *vnb-quiet*) (show))
         (pa--flush! lines)
         (pa--verdict status st file lines))))))

;;; THE COMMAND.  A clause list goes to the 2026-08-21 pipeline; anything else is the rule
;;; engine.
(define (preamble . args)
  (if (and (pair? args) (pair? (car args)))
      (apply preamble-clauses args)
      (pa--run (and (pair? args) (car args)))))

;;; The rules of the default source (cached on the file's modification time), for the
;;; what-now lane.  -> the rule list, or '() when the file cannot be read.
(define *pa-lane-cache* #f)       ; (file mtime rules)
(define (pa-lane-rules)
  (let* ((file (pa--source #f))
         (mt   (and (file-exists? file) (file-modification-time file))))
    (if (and *pa-lane-cache* (equal? (car *pa-lane-cache*) file) (equal? (cadr *pa-lane-cache*) mt))
        (caddr *pa-lane-cache*)
        (let* ((rd (pa-read-rule-file file)) (rules (or (car rd) '())))
          (set! *pa-lane-cache* (list file mt rules))
          rules))))
