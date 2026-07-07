;;; interactive.scm -- short-form commands for interactive proof sessions
;;;
;;; Maintains *ps* (current proof state) and provides single-letter wrappers
;;; around the cmd-* proof commands.  Each wrapper records itself in
;;; *proof-script* (so the proof can be saved and replayed later), mutates
;;; *ps*, and calls (show) so the new state is always displayed.
;;;
;;; State output is bracketed by sentinel lines that the Emacs interface
;;; strips from the REPL display and forwards to the proof-state buffer.
;;; Without Emacs the sentinels appear as two comment lines -- ignorable.

(define *ps* #f)

;;; -----------------------------------------------------------------------
;;; Proof-script recording
;;;
;;; *proof-script* accumulates the commands applied since the last (sp).
;;; Each entry is (cmd-name . args).  (qed name) auto-saves the current
;;; script under the given name; (save-proof name) does the same on demand.
;;; (replay-proof name [subst]) re-runs a saved script, optionally with a
;;; capture-avoiding substitution applied to every command argument.

(define *proof-script* '())

;; True while replay-proof is re-running a saved script: suppresses recording
;; so re-execution (incl. orchestrators like bc* that re-run sub-commands)
;; does not corrupt *proof-script*.
(define *replaying?* #f)

;; While bc*-dispatch is committing a hyp-discharge bc*, this holds the QUOTED
;; handler forms (e.g. ((ass) (ass) (ass))) so bc*--attempt can record them as
;; part of the single bc* entry -- (bc* name bindings . forms) -- instead of
;; the handlers landing as separate flattened steps after it.
(define *bc*-handler-forms* '())

(define (record-cmd! name args)
  (unless *replaying?*
    (set! *proof-script* (append *proof-script* (list (cons name args))))))

;; The raw goal formula of the current proof (set by sp), so an emitted script
;; can be wrapped as a standalone (sp (make-wff '...)) ... (qed 'name) block.
(define *current-goal* #f)

;; Completed proofs this session: list of (name goal script), appended at qed.
(define *session-log* '())

;;; -----------------------------------------------------------------------
;;; LIVE proof-trace capture.  proof-tex's first design RE-RUNS the recorded
;;; script (apply-recorded-cmd! under *replaying?*); that breaks for forward-
;;; `fact`-heavy proofs, where the sibling goal nodes `fact' spawns perturb the
;;; open-goal ordering bc*/focus navigate on replay.  Instead we snapshot the
;;; live focus AS THE REAL PROOF RUNS -- every successful surface tactic appends
;;; a record -- so the trace is the genuine state sequence, no replay needed and
;;; nothing to perturb.  proof-tex prefers this capture when it exists.
;;;
;;; A step record is (entry goal asms focus-id open-ids):
;;;   entry    -- the (sym . args) as recorded (its label via proof-tex--cmd-label)
;;;   goal     -- focus assertion formula, or #f when the proof is done
;;;   asms     -- focus assumption formulas (1-indexed, as ai/inst cite them)
;;;   focus-id -- focus node display number, or #f when done
;;;   open-ids -- display numbers of all open goals (proof-tex derives new-ids)
(define *live-trace* '())                          ; reversed records, in-flight proof
(define *proof-live-trace* (make-equal-hash-table)) ; name -> ordered records, at qed

;; Snapshot the current *ps* focus under ENTRY and push onto *live-trace*.
;; Skipped during replay (apply-recorded-cmd! bypasses vnb--run! anyway) and
;; when there is no live proof.
(define (vnb--capture-step! entry)
  (when (and *ps* (not *replaying?*))
    (let ((done (proof-done? *ps*)))
      (set! *live-trace*
        (cons (list entry
                    (and (not done) (wff-formula (sequent-node-assertion (proof-state-focus *ps*))))
                    (if done '() (map wff-formula (sequent-node-assumptions (proof-state-focus *ps*))))
                    (and (not done) (sequent-node-number (proof-state-focus *ps*)))
                    (map sequent-node-number (proof-open-goals *ps*)))
              *live-trace*)))))

;; *fresh-counter* (expressions.scm) value captured at each proof's sp, keyed by
;; proof name at qed.  proof-tex replay restores it so a proof that pins specific
;; eigenvariable names (ai/ew witnesses like `u_4') replays to the SAME names --
;; the global counter is monotonic and would otherwise mint different ones,
;; breaking the recorded witness args.  (Read-only: the replay fluid-lets it and
;; restores, so the monotonic invariant holds outside the replay.)
(define *proof-start-counter* (make-equal-hash-table))
(define *sp-counter-snapshot* 0)

(define *proof-script-table* (make-equal-hash-table))

(define (save-proof name)
  (hash-table-set! *proof-script-table* name *proof-script*)
  name)

(define (lookup-proof name)
  (or (hash-table-ref/default *proof-script-table* name #f)
      (error "lookup-proof: unknown proof script" name)))

;;; Print the current proof state wrapped in sentinel markers.
;; When #t, (show) suppresses the per-step state dump.  Batch harnesses
;; (e.g. scratch-roadtest's `rt') fluid-let this true around a multi-tactic
;; thunk so the run isn't a wall of intermediate goal trees.  NEVER leave it
;; bound during interactive / workspace use: the Emacs repaint depends on the
;; VNB-STATE block this emits.  qed's ledger line uses `display', not `show',
;; so it still prints under quiet.
(define *vnb-quiet* #f)

;; *vnb-loading* is defined at the top of load.scm and held #t for the whole
;; load so the interactive proof scripts in *vnb-files* don't flood the terminal
;; with a per-tactic state dump at startup.  Fallback to #f here so interactive.scm
;; is also loadable standalone.
(if (not (environment-bound? system-global-environment '*vnb-loading*))
    (eval '(define *vnb-loading* #f) system-global-environment))

(define (show)
  (unless (or *vnb-quiet* *vnb-loading*)
    (display ";;VNB-STATE-BEGIN\n")
    (if *ps*
        (print-proof-state *ps*)
        (display "No current proof.  Use (sp (make-wff '(formula))) to start one.\n"))
    (display ";;VNB-STATE-END\n")))

(define (pp w)
  (display (wff->string w))
  (newline))

;;; Evaluate a ground arithmetic term and display the result.
;;; Accepts a string ("2^10") or a raw S-expression ('(POWER 2 10)).
;;; (calc t) -- the calculator tape's evaluator.  Two modes, tried in order:
;;;  (1) GROUND arithmetic: if every symbol reduces, print the number (2+3*5 -> 17).
;;;  (2) SYMBOLIC: otherwise normalise t as a free commutative-ring expression
;;;      and print its canonical sum-of-monomials form ((x+y)*(x+y) - x*y ->
;;;      x^2 + x*y + y^2).  Bare identifiers are generators; remember VNB reads
;;;      `xy' as ONE symbol, so multiplication must be written x*y (or x y).
(define (calc t)
  (vnb-guard
    (lambda ()
      (let* ((raw (if (string? t) (parse-string t) t))
             (v   (arith-eval-term raw)))
        (cond
          (v (display v) (newline) v)
          ((cring-normal-form raw)
           => (lambda (term)
                ;; return the rendered STRING (not the term s-expr) so the
                ;; Emacs tape's ;Value: capture shows x^2 + x*y + y^2, not
                ;; the internal (+ (power x 2) ...) form.
                (let ((s (expression->string term)))
                  (display s) (newline) s)))
          (else
           (error "calc: not a ground or polynomial commutative-ring term" raw)))))))

(define (vnb--require-proof!)
  (unless *ps*
    (error "No current proof.  Use (sp (make-wff-from-string \"...\")) to start one.")))

;;; Convert a formula argument to a raw S-expression.
;;; Accepts either a string (parsed via parse-string) or a raw S-expression.
(define (->raw-formula f)
  (if (string? f) (parse-string f) f))

;;; Resolve a tactic's formula argument, with assumption-by-number support.
;;; A positive exact integer k selects the k-th assumption of the focus
;;; sequent (1-based, matching the numbered Focus-Workspace display), so
;;; `(bc 2)' can stand in for retyping the second assumption's formula.
;;; Anything else is handed to ->raw-formula.  Returns a vnb-warning on an
;;; out-of-range index so vnb--run! reports it cleanly instead of erroring.
;;; Call only inside a vnb--run! thunk (assumes *ps* is set).
(define (->raw-formula/idx f)
  (if (and (integer? f) (exact? f))
      (let* ((asms (sequent-node-assumptions (proof-state-focus *ps*)))
             (n    (length asms)))
        (if (and (>= f 1) (<= f n))
            (wff-formula (list-ref asms (- f 1)))
            (vnb--warn "assumption index out of range"
                       (string-append (number->string f)
                                      " (have 1.." (number->string n) ")"))))
      (->raw-formula f)))

;;; -----------------------------------------------------------------------
;;; Skip-proofs mode.
;;;
;;; When *skip-proofs?* is #t, sp short-circuits: instead of building a
;;; proof state, it stashes the goal formula and (if *skip-proofs-cont* is
;;; bound) invokes the continuation to escape out of the surrounding proof
;;; thunk.  prove-and-install! (proven-theorems.scm) sets up the cont,
;;; runs the thunk, and installs the captured formula as a theorem
;;; without running tactics.  Cuts proven-theorems.scm load time from
;;; minutes to seconds while iterating on unrelated work.
;;;
;;; Enable by setting *skip-proofs?* before loading load.scm, or via the
;;; VNB_SKIP_PROOFS env var (checked once at proven-theorems.scm load).

(define *skip-proofs?* #f)
(define *skip-proofs-captured* #f)
(define *skip-proofs-cont* #f)

(define (skip-proofs!)   (set! *skip-proofs?* #t))
(define (verify-proofs!) (set! *skip-proofs?* #f))

;;; -----------------------------------------------------------------------
;;; Start a proof.  Resets the proof-script accumulator.
;;;
;;; When *skip-proofs?* is set, capture the formula and bail out via
;;; *skip-proofs-cont* (the caller in prove-and-install! installed it).

;; sp accepts what its documentation promises: a wff, a "string" in surface
;; syntax (parsed), or a raw S-expr.  Strings/S-exprs are coerced exactly as the
;; user would by hand -- make-wff-from-string / make-wff -- so (sp "forall(...)")
;; and (sp '(FORALL ...)) both work, not only (sp (make-wff-from-string "...")).
(define (sp wic-in)
  (vnb-guard
    (lambda ()
      (define wic
        (cond ((wff? wic-in) wic-in)
              ((string? wic-in) (make-wff-from-string wic-in))
              ((pair? wic-in) (make-wff wic-in))
              (else (error "sp: expected a wff, a \"string\", or an S-expr" wic-in))))
      (cond
        (*skip-proofs?*
         (set! *skip-proofs-captured* (wff-formula wic))
         (when *skip-proofs-cont*
           (*skip-proofs-cont* 'skipped)))
        (else
         (set! *proof-script* '())
         (set! *current-goal* (wff-formula wic))
         (set! *sp-counter-snapshot* *fresh-counter*)   ; for faithful proof-tex replay
         (set! *ps* (start-proof wic))
         (set! *live-trace* '())                        ; begin a fresh live capture
         (vnb--capture-step! (cons 'sp '()))            ; seed it with the initial goal
         (show))))))

;;; (wff "...") -- short alias for make-wff-from-string, so a goal can be
;;; started from the scratch sheet as (sp (wff "forall([x in nn], x in zz)")).
(define (wff str) (make-wff-from-string str))

;;; -----------------------------------------------------------------------
;;; Ring-expression copilot.  Write commutative-ring goals with ordinary
;;; + * - ^ and have them resolved to the ring's OWN operators.  In an abstract
;;; ring `s' addition is (ADD s), multiplication (MUL s), negation (NEG s), the
;;; unit (ONE s), zero (ZERO s); a LITERAL power x^k expands to k-fold
;;; multiplication (so (crs) can normalize it), a SYMBOLIC power x^n becomes
;;; RING-POWER (ring-power.scm).  You write the algebra; this expands it.
;;;
;;;   (ring-term 's '(* z (+ x y)))      => ((MUL s) z ((ADD s) x y))
;;;   (sp (ring-goal '(x y z) '(= (* z (+ x y)) (+ (* z x) (* z y)))))
;;;       starts:  forall s, is-commutative-ring(s) =>
;;;                  forall x,y,z in a(s).  z*(x+y) = z*x + z*y
;;;   (sp (ring-goal '(x y) '(= (^ (+ x y) 2)
;;;                             (+ (^ x 2) (+ (* x y) (+ (* x y) (^ y 2)))))))
;;;
;;; Heads handled: + and * (n-ary, left-folded into the binary slot); - (unary
;;; negate or binary/n-ary subtract); ^ or expt; constants 0 -> (ZERO s) and
;;; 1 -> (ONE s).  Symbols pass through as ring elements; any other head is kept
;;; with its arguments resolved.  Default ring variable is `s' -- don't reuse it
;;; as an element name, or call ring-goal-in with your own ring symbol.

(define (ring-term--fold op args)
  (cond ((null? args) (error "ring-term: empty + or *"))
        ((null? (cdr args)) (car args))
        (else (let loop ((acc (car args)) (rest (cdr args)))
                (if (null? rest) acc
                    (loop (list op acc (car rest)) (cdr rest)))))))

(define (ring-term--pow s base k)        ; literal k >= 0 -> k-fold MUL
  (cond ((= k 0) (list 'ONE s))
        ((= k 1) base)
        (else (let loop ((i (- k 1)) (acc base))
                (if (= i 0) acc
                    (loop (- i 1) (list (list 'MUL s) acc base)))))))

(define (ring-term s e)
  (cond
    ((eqv? e 0) (list 'ZERO s))
    ((eqv? e 1) (list 'ONE s))
    ((not (pair? e)) e)                  ; symbol / other atom -> ring element
    (else
     (case (car e)
       ((+) (ring-term--fold (list 'ADD s)
              (map (lambda (a) (ring-term s a)) (cdr e))))
       ((*) (ring-term--fold (list 'MUL s)
              (map (lambda (a) (ring-term s a)) (cdr e))))
       ((-) (let ((as (map (lambda (a) (ring-term s a)) (cdr e))))
              (cond ((null? as) (error "ring-term: empty -"))
                    ((null? (cdr as)) (list (list 'NEG s) (car as)))
                    (else (ring-term--fold (list 'ADD s)
                            (cons (car as)
                                  (map (lambda (a) (list (list 'NEG s) a))
                                       (cdr as))))))))
       ((^ expt)
        (let ((base (ring-term s (cadr e))) (ex (caddr e)))
          (if (and (integer? ex) (>= ex 0))
              (ring-term--pow s base ex)            ; literal power -> k-fold MUL
              (list 'RING-POWER s base ex))))        ; symbolic power -> RING-POWER
       (else (cons (car e) (map (lambda (a) (ring-term s a)) (cdr e))))))))

;;; Build a full commutative-ring goal: forall s, is-commutative-ring(s) =>
;;; forall <vars> in a(s). <body>, with the operators in BODY resolved against s.
(define (ring-goal vars body) (ring-goal-in 's vars body))

(define (ring-goal-in s vars body)
  (make-wff
   (list 'FORALL s
     (list 'IMPLIES (list 'IS-COMMUTATIVE-RING s)
       (let loop ((vs vars))
         (if (null? vs)
             (ring-term s body)
             (list 'FORALL (car vs)
               (list 'IMPLIES (list 'IN (car vs) (list 'CARR s))
                 (loop (cdr vs))))))))))

;;; -----------------------------------------------------------------------
;;; Short-form proof commands.
;;;
;;; vnb--run! executes a cmd-* thunk, records and updates *ps* on success,
;;; or displays the warning message and leaves *ps* unchanged on soft failure.

(define (vnb--run! sym args thunk)
  (let ((result (vnb-guard (lambda () (vnb--require-proof!) (thunk)))))
    (cond
      ((vnb-error? result) #f)          ; already displayed by vnb-guard
      ((vnb-warning? result)
       (unless *vnb-quiet*               ; quietly suppresses soft warnings too
         (display ";VNB warning: ")
         (display (vnb-warning-message result))
         (newline)))
      (else
       (record-cmd! sym args)
       (set! *ps* result)
       (vnb--capture-step! (cons sym args))   ; live trace for proof-tex
       (show)))))

(define (di)    (vnb--run! 'di    '()    (lambda () (cmd-direct-inference *ps*))))
(define (pbc)   (vnb--run! 'pbc   '()    (lambda () (cmd-proof-by-contradiction *ps*))))
(define (ass)   (vnb--run! 'ass   '()    (lambda () (cmd-assumption *ps*))))
(define (arith) (vnb--run! 'arith '()    (lambda () (cmd-arith *ps*))))
(define (rs)    (vnb--run! 'rs    '()    (lambda () (cmd-ring-simplify *ps*))))
(define (crs)   (vnb--run! 'crs   '()    (lambda () (cmd-comm-ring-simplify *ps*))))
(define (ineq . idxs) (vnb--run! 'ineq idxs (lambda () (cmd-ineq *ps* idxs))))
(define (sos . certs) (vnb--run! 'sos certs (lambda () (cmd-sos *ps* certs))))
(define (rfl)   (vnb--run! 'rfl   '()    (lambda () (cmd-reflexivity *ps*))))
(define (qrfl)  (vnb--run! 'qrfl  '()    (lambda () (cmd-quasi-reflexivity *ps*))))
(define (oi-l)  (vnb--run! 'oi-l  '()    (lambda () (cmd-or-intro-left *ps*))))
(define (oi-r)  (vnb--run! 'oi-r  '()    (lambda () (cmd-or-intro-right *ps*))))
(define (ci)    (vnb--run! 'ci    '()    (lambda () (cmd-cartesian-intro *ps*))))
(define (ti)    (vnb--run! 'ti    '()    (lambda () (cmd-tuples-intro *ps*))))
(define (nth-r) (vnb--run! 'nth-r '()    (lambda () (cmd-nth-reduce *ps*))))
(define (len-r) (vnb--run! 'len-r '()    (lambda () (cmd-length-reduce *ps*))))
(define (beta)  (vnb--run! 'beta  '()    (lambda () (cmd-functoid-beta *ps*))))
(define (ii)    (vnb--run! 'ii    '()    (lambda () (cmd-intersection-intro *ps*))))
(define (tfi)   (vnb--run! 'tfi   '()    (lambda () (cmd-tfi *ps*))))
(define (tfi3)  (vnb--run! 'tfi3  '()    (lambda () (cmd-tfi3 *ps*))))
(define (ni)    (vnb--run! 'ni    '()    (lambda () (cmd-nn-induction *ps*))))

;;; -----------------------------------------------------------------------
;;; goal-status / refresh-status: one-line proof-state summaries for the
;;; Scratch Workspace, which plunks them as a ;; comment after a command
;;; block (whose Scheme return value is irrelevant -- the side effect on
;;; *ps* is what matters).

(define (goal-status)
  (cond
    ((not *ps*)          "not applicable")
    ((proof-done? *ps*)  "done")
    (else
     (let ((n (length (proof-open-goals *ps*))))
       (string-append (number->string n)
                      (if (= n 1) " open goal" " open goals"))))))

;; Refresh the *VNB State* buffer (via show) and return the summary string.
;; The Scratch Workspace calls this after running a command block under
;; *vnb-quiet*, so the intermediate state dumps don't pollute the captured
;; value; the trailing show updates the State pane exactly once.
(define (refresh-status)
  (show)
  (goal-status))

;;; -----------------------------------------------------------------------
;;; Tacticals.  A proof command reports success by REPLACING *ps* with a
;;; fresh object; both soft and hard failures leave *ps* eq?-identical.  So
;;; "did it make progress?" is exactly (not (eq? *ps* before)).  These ride
;;; that invariant -- a command's Scheme return value is irrelevant.

;; REPEAT t -- run thunk t until it stops changing *ps* (capped at CAP, default
;; 1000).  Returns nothing useful; the resulting proof state is the point.
;; "keep doing di until it stops" is just (repeat di).  Because begin is
;; Scheme's progn, regionifying several commands in the Scratch Workspace and
;; C-j is the explicit-count cousin of this.
(define (repeat thunk #!optional cap)
  (let ((cap (if (default-object? cap) 1000 cap)))
    (let loop ((n 0))
      (when (< n cap)
        (let ((before *ps*))
          (thunk)
          (unless (eq? *ps* before) (loop (+ n 1))))))))

;; ORELSE t1 t2 ... -- run thunks in order, stop at the first that changes
;; *ps*.  Returns #t if one applied, #f if none did.  Compose with repeat:
;;   (repeat (lambda () (orelse di ass)))   ; saturate, closing goals as they fall
(define (orelse . thunks)
  (let loop ((ts thunks))
    (and (pair? ts)
         (let ((before *ps*))
           ((car ts))
           (if (eq? *ps* before) (loop (cdr ts)) #t)))))

;; QUIETLY t -- run thunk t with show output suppressed; returns t's value.
(define (quietly thunk)
  (let ((saved *vnb-quiet*) (saved-g *vnb-guard-quiet*))
    (dynamic-wind
      (lambda () (set! *vnb-quiet* #t) (set! *vnb-guard-quiet* #t))
      thunk
      (lambda () (set! *vnb-quiet* saved) (set! *vnb-guard-quiet* saved-g)))))

;;; -----------------------------------------------------------------------
;;; mac-h* -- SATURATING hypothesis-side unfold.  The repeated ritual
;;;
;;;     (mac-h 'IS-METRIC-SPACE A1) (ai ...) (mac-h 'is-metric A2) (ai ...) ...
;;;
;;; -- "keep unfolding defined predicates in the hypotheses, splitting the
;;; conjunctions they expose, until nothing is left folded" -- collapses to a
;;; single (mac-h*).  Each pass over the focus node's assumptions: split any
;;; AND (the ai), and unfold any assumption whose OUTERMOST head is a defined
;;; predicate with a registered definitional macete (the mac-h, name = head
;;; symbol -- exactly how the by-hand proofs cite them).  Restart the pass
;;; whenever something fires; stop when a full pass is inert.
;;;
;;; It drives the cmd-* layer directly, so the dozen primitive steps record as
;;; ONE (mac-h*) entry -- the trace (and its PDF) shrinks accordingly -- and it
;;; adds no kernel rule: every unfold is the same kernel-checked mac-h, every
;;; split the same ai.  Sound by construction, just terser.

;; Outermost defined-predicate unfold name for assumption formula F (its head
;; symbol, when that head is a registered definitional macete), else #f.
(define (vnb--hyp-unfold-name f)
  (and (pair? f) (symbol? (car f))
       (let ((h (car f)))
         (and (hash-table-ref/default *macete-table* h #f)  ; a registered macete
              (eq? (provenance-of h) 'definitional)          ; that is a definition
              h))))

;; Core: saturate the focus hypotheses, mutating the proof graph in place (as
;; every cmd-* does).  Each pass scans the focus assumptions for one that is
;; foldable -- an AND (split with ai) or an outermost defined predicate (unfold
;; with mac-h) not already tried -- fires it, and restarts the pass so freshly
;; exposed assumptions surface.  A `seen' set of (formula . tag) pairs both
;; breaks loops and guarantees termination.  Returns ps0 if anything fired
;; (success, per the cmd-* contract -- the object is mutated in place), else a
;; vnb-warning so the surface wrapper records no no-op.
(define (cmd-mac-h* ps0)
  (let ((seen '()))
    (define (one-pass)            ; #t iff some assumption genuinely fired
      (let scan ((as (sequent-node-assumptions (proof-state-focus ps0))))
        (and (pair? as)
             (let* ((f   (wff-formula (car as)))
                    ;; The NO-CHOICE hypothesis decompositions: split a
                    ;; conjunction (AND) and skolemize an existential (FORSOME)
                    ;; -- both via antecedent-inference, both deterministic (the
                    ;; FORSOME eigenvariable is fresh) -- plus unfold a defined
                    ;; predicate.  OR is excluded (case-split -> branches, a
                    ;; CHOICE, so it stays out of the normalizer).  Folding
                    ;; FORSOME in here is what lets `grind' collapse the
                    ;; skolemize plies of a forward / quantifier-alternation
                    ;; proof, so search branches only on real choices (the ew
                    ;; witness, the inst term).
                    (tag (cond ((and (pair? f) (eq? (car f) 'AND)) 'AND)
                               ((and (pair? f) (eq? (car f) 'FORSOME)) 'FORSOME)
                               ((vnb--hyp-unfold-name f))
                               (else #f)))
                    (key (and tag (cons f tag))))
               (if (and key (not (member key seen)))
                   (begin
                     (set! seen (cons key seen))
                     (let ((r (if (memq tag '(AND FORSOME))
                                  (cmd-antecedent-inference ps0 f)
                                  (cmd-apply-macete-to-assumption ps0 tag f))))
                       (if (or (vnb-warning? r) (vnb-error? r))
                           (scan (cdr as))    ; this one didn't take; keep looking
                           #t)))              ; fired -> restart the pass
                   (scan (cdr as)))))))
    (let loop ((fired-any #f) (n 0))
      (if (and (< n 500) (one-pass))
          (loop #t (+ n 1))
          (if fired-any ps0
              (vnb--warn "mac-h*"
                "no foldable predicate or conjunction in the hypotheses"))))))

(define (mac-h*) (vnb--run! 'mac-h* '() (lambda () (cmd-mac-h* *ps*))))

;; (grind) -- the deterministic normalizer: saturate the NO-CHOICE moves at the
;; focus.  Repeatedly (a) decompose the goal connective with direct-inference
;; (di -- peels FORALL/IMPLIES/AND/IFF/NOT, introducing binders + hypotheses)
;; and (b) break open the hypotheses with mac-h* (split ANDs, SKOLEMIZE
;; existentials, unfold defined predicates), until neither fires.  None of these
;; involves a lemma CHOICE or a witness/eigenvar CHOICE (skolem vars are fresh),
;; so a search never has to backtrack across grind -- it collapses the whole
;; `di ... di mac-h*' prefix (and the skolemize plies of a forward / quantifier-
;; alternation proof) that bloats proofs into one ply.
;; Mutates in place like every cmd-*; returns ps0 if anything fired else a
;; vnb-warning.  (di auto-advances the focus to the first new subgoal, so grind
;; normalizes that branch; sibling subgoals are left for the caller/search.)
(define (cmd-grind ps0)
  (let loop ((fired-any #f) (n 0))
    (if (>= n 500)
        (if fired-any ps0 (vnb--warn "grind" "step budget exhausted"))
        (let ((d (cmd-direct-inference ps0)))
          (if (not (or (vnb-warning? d) (vnb-error? d)))
              (loop #t (+ n 1))                 ; di fired -> keep going
              (let ((h (cmd-mac-h* ps0)))
                (if (not (or (vnb-warning? h) (vnb-error? h)))
                    (loop #t (+ n 1))           ; mac-h* fired -> keep going
                    (if fired-any ps0           ; neither fired -> done
                        (vnb--warn "grind"
                          "nothing to introduce or break open at the focus")))))))))

(define (grind) (vnb--run! 'grind '() (lambda () (cmd-grind *ps*))))

(define (ai f)
  (vnb--run! 'ai (list f)
             (lambda ()
               (let ((raw (->raw-formula/idx f)))
                 (if (vnb-warning? raw) raw (cmd-antecedent-inference *ps* raw))))))
;; Equality substitution: eq is (= s t); s = t must be in context.
;; Rewrites s -> t throughout the goal (Leibniz schema).
(define (subst eq) (let ((raw (->raw-formula eq)))
                     (vnb--run! 'subst (list raw) (lambda () (cmd-eq-subst *ps* raw)))))
(define (cut f) (let ((raw (->raw-formula f)))
                  (vnb--run! 'cut (list raw) (lambda () (cmd-cut *ps* raw)))))
;; In-formula commutative-ring simplification: rewrite a ring SUBTERM of the
;; goal to canonical form, in place.  (simp) auto-finds the outermost ring
;; subterm; (simp "term") targets a specific one.  Sound by cut+crs+eq-subst;
;; needs the subterm's generators typed in context (usually true post-di).
(define (simp . args)
  (let ((raw (and (pair? args) (->raw-formula (car args)))))
    (vnb--run! 'simp (if raw (list raw) '())
      (lambda () (if raw (cmd-cring-simp *ps* raw) (cmd-cring-simp *ps*))))))

;; to-binary / to-nary -- one-shot surface conversion between the kiddie n-ary
;; +/*/-  and the binary structure operators binplus/bintimes/binneg (which are
;; the (ADD s)/(MUL s)/(NEG s) slots of the number rings ZZ/QQ/RR/CC-RING).
;; Saturating: applies the arity-bridge macetes until none fire.  Unconditional
;; -- the binX-apply / nary-* axioms are definitional, so no typing is needed.
;; to-binary pushes a goal onto the STRUCTURE surface (so a structure-level
;; theorem or macete can match); to-nary brings it back to everyday arithmetic.
;; n-ary arities 2..5 are bridged; longer sums/products need more nary-* axioms.
(define *to-binary-macetes*
  '(nary-plus-5 nary-plus-4 nary-plus-3 nary-plus-2
    nary-times-5 nary-times-4 nary-times-3 nary-times-2
    nary-minus-2 nary-neg-1))
(define *to-nary-macetes* '(binplus-apply bintimes-apply binneg-apply))
(define (to-binary--focus-formula)
  (and *ps* (wff-formula (sequent-node-assertion (proof-state-focus *ps*)))))
;; Saturate the bridge MACETES over the focus goal.  Each (mac m) is recorded
;; (so proof scripts replay) and quiet (warnings suppressed for non-firing
;; macetes); we loop on the GOAL FORMULA changing -- NOT (eq? *ps* ...), which
;; never changes because tactics mutate *ps* in place (repeat/orelse rely on
;; that identity and so silently run once -- a separate latent bug).
(define (to-binary--saturate macetes)
  (vnb--require-proof!)
  (quietly
    (lambda ()
      (let loop ((guard 0))
        (let ((before (to-binary--focus-formula)))
          (for-each mac macetes)
          (when (and (< guard 200)
                     (not (equal? (to-binary--focus-formula) before)))
            (loop (+ guard 1)))))))
  (show))
(define (to-binary) (to-binary--saturate *to-binary-macetes*))
(define (to-nary)   (to-binary--saturate *to-nary-macetes*))

;; (in-rr) -- discharge a goal (IN <arith-term> D) for a ring domain D in
;; {RR,ZZ,QQ,CC}, by structural recursion: to-binary normalizes the n-ary
;; +/-/* surface to binplus/bintimes/binneg, then each application is typed
;; FORWARD via fun-apply-type-c (driven by `fact`, NOT `bc` -- bc on its
;; higher-order conclusion (f x) loops) plus cartesian-intro (ci) for the
;; tupled binary operators.  Function applications (f x) with (IN f (FUN A D))
;; in context are typed too.  No new closure axioms: everything reduces to the
;; operator typings (binplus-in-fun-D ...) + apply-tupling + fun-apply-type-c.
(define (in-rr--goal) (wff-formula (sequent-node-assertion (proof-state-focus *ps*))))
(define (in-rr--focus-goal! raw)
  (let ((s (any-pred (lambda (s) (equal? (wff-formula (sequent-node-assertion s)) raw))
                     (proof-leaves))))
    (and s (set-proof-state-focus! *ps* s) s)))
(define (in-rr--focus-asm! raw)
  (let ((s (any-pred (lambda (s) (any-pred (lambda (w) (equal? (wff-formula w) raw))
                                           (sequent-node-assumptions s)))
                     (proof-leaves))))
    (and s (set-proof-state-focus! *ps* s) s)))
(define (in-rr--in-ctx? raw)
  (any-pred (lambda (w) (equal? (wff-formula w) raw))
            (sequent-node-assumptions (proof-state-focus *ps*))))
(define (in-rr--fun-dom g S)
  (let ((a (any-pred (lambda (w)
                       (let ((wf (wff-formula w)))
                         (and (pair? wf) (eq? (car wf) 'IN) (equal? (cadr wf) g)
                              (pair? (caddr wf)) (eq? (car (caddr wf)) 'FUN)
                              (equal? (caddr (caddr wf)) S))))
                     (sequent-node-assumptions (proof-state-focus *ps*)))))
    (and a (cadr (caddr (wff-formula a))))))
(define (in-rr--op-typ op D)
  (string->symbol (string-append (symbol->string op) "-in-fun-" (symbol->string D))))
(define (in-rr--ensure! t S)               ; land (IN t S) in context, refocus continuation
  (let ((mem (list 'IN t S)))
    (if (in-rr--in-ctx? mem) #t
        (begin (cut mem) (in-rr--focus-goal! mem) (in-rr--close!)
               (in-rr--focus-asm! mem)))))
(define (in-rr--close!)                    ; close current focus goal (IN term S)
  (let* ((g (in-rr--goal)) (term (cadr g)) (S (caddr g)))
    (cond
      ((in-rr--in-ctx? g) (ass))
      ((symbol? term) (ass))
      ((number? term) (ass))
      ((and (pair? term) (eq? (car term) 'binneg))
       (let ((a (cadr term)))
         (in-rr--ensure! a S) (in-rr--focus-goal! g)
         (quietly (lambda () (fact (in-rr--op-typ 'binneg S))
                             (fact 'fun-apply-type-c 'binneg S S a) (ass)))))
      ((and (pair? term) (memq (car term) '(binplus bintimes)))
       (let* ((op (car term)) (a (cadr term)) (b (caddr term))
              (lst (list 'LIST a b)) (tup (list op lst)) (cart (list 'CARTESIAN S S)))
         (fact 'apply-tupling-2 op a b)
         (subst (list '== (list op a b) tup))
         (in-rr--ensure! lst cart) (in-rr--focus-goal! (list 'IN tup S))
         (quietly (lambda () (fact (in-rr--op-typ op S))
                             (fact 'fun-apply-type-c op cart S lst) (ass)))))
      ((and (pair? term) (eq? (car term) 'LIST))
       (ci)
       (for-each (lambda (elt fac)
                   (or (in-rr--focus-goal! (list 'IN elt fac))
                       (error "in-rr: cannot focus component" (list 'IN elt fac)))
                   (in-rr--close!))
                 (cdr term) (cdr S)))
      (else
       (let ((dom (and (pair? term) (= (length term) 2)
                       (in-rr--fun-dom (car term) S))))
         (if dom
             (let ((gfn (car term)) (a (cadr term)))
               (in-rr--ensure! a dom) (in-rr--focus-goal! g)
               (quietly (lambda () (fact 'fun-apply-type-c gfn dom S a) (ass))))
             (ass)))))))
(define (in-rr)
  (vnb--require-proof!)
  (to-binary)
  (in-rr--close!)
  (quietly (lambda () (ass-all)))
  (proof-done? *ps*))
;; Conditional-term reduction: t is an (IF p a b) term.  if-true spawns p
;; as a subgoal; if-false spawns (NOT p).  The other branch gains the
;; equation (= (IF p a b) a) resp. (= (IF p a b) b) as an assumption.
(define (if-true t)  (let ((raw (->raw-formula t)))
                       (vnb--run! 'if-true (list raw)
                                  (lambda () (cmd-if-true *ps* raw)))))
(define (if-false t) (let ((raw (->raw-formula t)))
                       (vnb--run! 'if-false (list raw)
                                  (lambda () (cmd-if-false *ps* raw)))))
(define (ew t)  (let ((raw (->raw-formula t)))
                  (vnb--run! 'ew (list raw) (lambda () (cmd-exists-witness *ps* raw)))))
(define (bc f)
  (vnb--run! 'bc (list f)
             (lambda ()
               (let ((raw (->raw-formula/idx f)))
                 (if (vnb-warning? raw) raw (cmd-backchain *ps* raw))))))
(define (wk f)
  (vnb--run! 'wk (list f)
             (lambda ()
               (let ((raw (->raw-formula/idx f)))
                 (if (vnb-warning? raw) raw (cmd-weaken *ps* raw))))))
(define (ui k)  (vnb--run! 'ui (list k) (lambda () (cmd-union-intro *ps* k))))
(define (ue f)  (let ((raw (->raw-formula f)))
                  (vnb--run! 'ue (list raw) (lambda () (cmd-union-elim *ps* raw)))))

(define (ta n)  (vnb--run! 'ta (list n) (lambda () (cmd-theorem-assumption *ps* n))))
(define (mac n) (vnb--run! 'mac (list n) (lambda () (cmd-apply-macete *ps* n))))

;; macm -- goal-side `mac' that SPAWNS a conditional macete's unmet side
;; conditions as minor-premise subgoals (the IMPS apply-macete-with-minor-
;; premises analogue).  Plain `mac' only fires a conditional rewrite when its
;; conditions ALREADY hold in the local context; macm fires regardless, leaving
;; each unmet condition as a sibling subgoal while the rewritten main line stays
;; in focus.  This is what makes the conditional finsum rearrangement lemmas
;; (finsum-ord-peel / -add-ag / -ring-distrib-left / -reindex-ag / ...) usable
;; as goal rewrites instead of only forward via `fact'.
(define (macm n)
  (vnb--run! 'macm (list n)
             (lambda () (fluid-let ((*macete-spawn-conditions?* #t))
                          (cmd-apply-macete *ps* n)))))

;; detach! -- forward modus ponens: from an in-context (IMPLIES A B) whose A is
;; also in context, leave B in context.  The forward dual of bc.
(define (detach! f)
  (vnb--run! 'detach! (list f)
             (lambda ()
               (let ((raw (->raw-formula/idx f)))
                 (if (vnb-warning? raw) raw (cmd-detach *ps* raw))))))

;; fact -- forward application of a theorem.  (fact 'thm term ...) brings the
;; theorem in, instantiates its leading universals with the terms, and detaches
;; every antecedent already in context, landing the consequent as a hypothesis.
;; The forward-assembly workhorse for structure proofs ("apply this law here").
(define (fact thm . args)
  ;; Parse each instantiation arg so surface-syntax terms work from any
  ;; interactive surface, e.g. (fact 'thm "x(s)") -- ->raw-formula parses a
  ;; string and passes a symbol / s-expression through unchanged, so existing
  ;; (fact 'thm (list 'X s) ...) script calls are unaffected.
  (let ((parsed (map ->raw-formula args)))
    ;; Record the args FLAT -- (fact thm a b c), not (fact thm (a b c)) -- so the
    ;; proof script / proof-tex trace reads as you'd type it and replays as
    ;; (apply fact (cons thm parsed)) = (fact thm a b c).
    (vnb--run! 'fact (cons thm parsed) (lambda () (cmd-fact *ps* thm parsed)))))

;; mac-h -- hypothesis-side `mac`.  Unfold a defined predicate (or apply any
;; unconditional IFF/=/== equivalence macete) inside a cited ASSUMPTION,
;; replacing it by its body in place.  The dual of `mac`; pairs with `ai` the
;; way `mac` pairs with `di`.  n is the macete name, f the assumption to hit.
(define (mac-h n f)
  (vnb--run! 'mac-h (list n f)
             (lambda ()
               (let ((raw (->raw-formula/idx f)))
                 (if (vnb-warning? raw) raw
                     (cmd-apply-macete-to-assumption *ps* n raw))))))

;;; -----------------------------------------------------------------------
;;; bc* -- matching backchain.
;;;
;;;   (bc* 'thm)                  -- conclusion fully determines instantiation
;;;   (bc* 'thm ((v val) ...))    -- supply schema vars the conclusion omits
;;;   (bc* 'thm ((v val) ...) h1 h2 ...)
;;;                               -- run handler hk on the k-th subgoal
;;;
;;; Applies a registered theorem to the current goal by UNIFYING the
;;; theorem's conclusion against the goal, then replaying the
;;; ta / inst / cut / bc idiom automatically.  The theorem's antecedents,
;;; instantiated by the discovered substitution, are left as open subgoals
;;; (the actual mathematical content); the main line closes by assumption.
;;;
;;; The theorem may carry any nesting of leading FORALLs and right-nested
;;; IMPLIES --- FORALL* (IMPLIES A1 (FORALL* (IMPLIES A2 ... C))).  bc* peels
;;; FORALLs and IMPLIES down to the conclusion C and matches C against the
;;; goal.  A schema variable that does not occur in C cannot be discovered
;;; by matching; pass it as ((v val) ...).  The goal itself must not be a
;;; FORALL/IMPLIES bc* would peel past --- it is meant for atomic goals
;;; (memberships, equalities).
;;;
;;; With handlers: bc* refocuses to each subgoal IN TREE ORDER before
;;; running its handler, so subgoal navigation needs no manual refocus!.
;;; The number of handlers must equal the number of antecedents; a handler
;;; that needs several tactics uses (begin ...).  Without handlers, bc*
;;; leaves focus on the first subgoal and returns the subgoal-node list.
;;;
;;; bc* drives the cmd-* layer; it adds no kernel rule, so every proof it
;;; produces is checked by the existing primitive inferences.

;; Peel leading FORALL/IMPLIES; return (values forall-vars conclusion).
(define (bc*--peel f)
  (let loop ((f f) (vars '()))
    (cond
      ((and (pair? f) (eq? (car f) 'FORALL))
       (loop (caddr f) (cons (cadr f) vars)))
      ((and (pair? f) (eq? (car f) 'IMPLIES))
       (loop (caddr f) vars))
      (else (values (reverse vars) f)))))

(define (bc*--last-node)
  (car (reverse (dg-sequent-nodes (proof-state-dg *ps*)))))

;; Merge explicit bindings into the matcher's substitution (matcher wins).
(define (bc*--merge m extra)
  (let loop ((es extra) (acc m))
    (if (null? es)
        acc
        (loop (cdr es)
              (if (assoc (caar es) acc) acc (cons (car es) acc))))))

(define (bc*--commit! result what)
  (cond
    ((vnb-warning? result)
     (error (string-append "bc*: " what " -- " (vnb-warning-message result))))
    ((not (proof-state? result))
     (error (string-append "bc*: " what " produced no proof state")))
    (else (set! *ps* result))))

;; Replay ta + inst/cut/bc down the theorem structure.
;; Returns the list of antecedent subgoal nodes, in tree order.
(define (bc*--drive! name thm subst)
  (bc*--commit! (cmd-theorem-assumption *ps* name) "ta")
  (let loop ((f thm) (goals '()))
    (cond
      ((and (pair? f) (eq? (car f) 'FORALL))
       (let* ((v (cadr f))
              (t (cdr (assoc v subst)))
              (nf (subst-free v t (caddr f))))
         (bc*--commit! (cmd-instantiate *ps* f t) "inst")
         (loop nf goals)))
      ((and (pair? f) (eq? (car f) 'IMPLIES))
       (let ((rest (caddr f)))
         (bc*--commit! (cmd-cut *ps* rest) "cut")
         (let ((b2 (bc*--last-node)))
           (bc*--commit! (cmd-backchain *ps* f) "bc")
           (let ((ant (proof-state-focus *ps*)))   ; the antecedent subgoal
             (set-proof-state-focus! *ps* b2)
             (loop rest (cons ant goals))))))
      (else
       (bc*--commit! (cmd-assumption *ps*) "assumption")
       (reverse goals)))))

;; Match the theorem conclusion against the goal, drive the proof.
;; Returns the subgoal-node list, or #f after displaying a warning.
(define (bc*--attempt name bindings)
  (vnb--require-proof!)
  (let* ((thm  (lookup-theorem name))
         (goal (wff-formula
                (sequent-node-assertion (proof-state-focus *ps*)))))
    (let-values (((svars concl) (bc*--peel thm)))
      ;; *match-var-head* lets the conclusion's variable-headed applications
      ;; (e.g. fun-apply-type's (f x)) match the goal.
      (let ((m (fluid-let ((*match-var-head* #t))
                 (match-expr concl goal svars))))
        (cond
          ((not m)
           (display ";VNB warning: bc*: conclusion of ")
           (display name)
           (display " does not match the goal\n")
           #f)
          (else
           (let* ((subst   (bc*--merge m bindings))
                  (unbound (filter (lambda (v) (not (assoc v subst)))
                                   svars)))
             (cond
               ((not (null? unbound))
                (display ";VNB warning: bc*: undetermined schema var(s) ")
                (write unbound)
                (display " -- supply as ((v val) ...)\n")
                #f)
               (else
                (let ((gs (bc*--drive! name thm subst)))
                  ;; Record name + bindings + any hyp-discharge handler forms as
                  ;; ONE entry: (bc* name bindings . forms).  forms is '() for the
                  ;; bc*-apply path, so this stays (bc* name bindings) there.
                  (record-cmd! 'bc* (cons name (cons bindings *bc*-handler-forms*)))
                  gs))))))))))

;; Run bc* for `name` with `bindings` (alist).  On success returns the list
;; of subgoal nodes (possibly '()); on a soft failure displays a warning and
;; returns #f.
(define (bc*-run! name bindings)
  (if (not (hash-table-ref/default *theorem-table* name #f))
      (begin
        (display ";VNB warning: bc*: unknown theorem ")
        (display name) (newline)
        #f)
      (let ((r (vnb-guard (lambda () (bc*--attempt name bindings)))))
        (if (list? r) r #f))))

;; (bc* 'name) / (bc* 'name ((v val) ...)) : spawn subgoals, focus the first.
(define (bc*-apply name bindings)
  (let ((gs (bc*-run! name bindings)))
    (when (list? gs)
      (when (pair? gs) (set-proof-state-focus! *ps* (car gs)))
      (show))
    gs))

;; (bc* 'name ((v val) ...) h1 h2 ...) : run hk focused on the k-th subgoal.
;; Each handler arrives as a (FORM THUNK) pair from the bc* macro: FORM is the
;; quoted handler syntax (recorded into the bc* entry so the script re-nests),
;; THUNK runs it.  The handler runs with recording suppressed so it does NOT
;; also land as a separate flattened step.
(define (bc*-dispatch name bindings . handlers)
  (let ((forms  (map car  handlers))
        (thunks (map cadr handlers)))
    (fluid-let ((*bc*-handler-forms* forms))
      (let ((gs (bc*-run! name bindings)))   ; records (bc* name bindings . forms)
        (cond
          ((not (list? gs)) #f)              ; soft failure, already reported
          ((not (= (length gs) (length thunks)))
           (display ";VNB warning: bc*: ")
           (write (length thunks))
           (display " handler(s) but ")
           (write (length gs))
           (display " subgoal(s) from ")
           (display name) (newline))
          (else
           (for-each (lambda (g th)
                       (set-proof-state-focus! *ps* g)
                       (fluid-let ((*replaying?* #t)) (th)))
                     gs thunks)
           (show)))))))

;;; -----------------------------------------------------------------------
;;; Front end for an interactive "backchain, then prompt for the schema vars
;;; the match leaves open" command (the Emacs Focus `B' key).
;;;
;;; bc*-undetermined: a PURE query -- report which schema vars bc* on `name'
;;; would leave undetermined against the current focused goal, WITHOUT driving
;;; the proof, mutating *ps*, or printing a warning.  Result is a read-able
;;; sexp the front end dispatches on:
;;;   (ok V ...)   match succeeds; V... = undetermined schema vars ('() = none)
;;;   (no-proof)   no current proof
;;;   (unknown)    no such theorem
;;;   (no-match)   conclusion of `name' does not match the goal
(define (bc*-undetermined name)
  (cond
    ((not *ps*) '(no-proof))
    ((not (hash-table-ref/default *theorem-table* name #f)) '(unknown))
    (else
     (let* ((thm  (lookup-theorem name))
            (goal (wff-formula
                   (sequent-node-assertion (proof-state-focus *ps*)))))
       (let-values (((svars concl) (bc*--peel thm)))
         (let ((m (fluid-let ((*match-var-head* #t))
                    (match-expr concl goal svars))))
           (if (not m)
               '(no-match)
               (cons 'ok
                     (filter (lambda (v) (not (assoc v m))) svars)))))))))

;;; bc*-apply-term-bindings: drive bc* on `name' with bindings given as
;;; (var . term-string) pairs; each string is parsed in VNB surface term
;;; syntax (parse-string).  This is the value-typed entry behind `B': the user
;;; types each undetermined var's value as a term ("RAN(f)", "nn"), never the
;;; ((v 'val)) quoting.  Empty list == plain (bc* 'name).
(define (bc*-apply-term-bindings name str-bindings)
  (bc*-apply name
             (map (lambda (p)
                    (let ((term (parse-string (cdr p))))
                      (when (vnb-warning? term)
                        (error (string-append
                                "bc*: could not parse term for "
                                (symbol->string (car p)) ": " (cdr p))))
                      (cons (car p) term)))
                  str-bindings)))

;;; bc*-reduce-goal!: peel the focus goal to its citeable core by di-ing away
;;; leading FORALL/IMPLIES -- the SAME shape conclusion-fingerprint peels when
;;; the suggester ranks lemmas, so a lemma suggested for the goal's eventual
;;; conclusion can actually be cited.  Stops at the first non-FORALL/IMPLIES
;;; head (AND, =, an atom): never splits a conjunction.  Quiet (no per-step
;;; dumps).  Returns the number of di steps taken (0 = nothing to peel).
(define (bc*-reduce-goal!)
  (vnb--require-proof!)
  (quietly
    (lambda ()
      (define (goal) (wff-formula (sequent-node-assertion (proof-state-focus *ps*))))
      (let loop ((n 0))
        (let ((w (goal)))
          (if (and (pair? w) (memq (car w) '(forall implies)))
              (begin
                (di)
                ;; di mutates *ps* in place, so compare the goal FORMULA, not
                ;; object identity, to detect progress (and avoid a wedge).
                (if (equal? (goal) w) n (loop (+ n 1))))
              n))))))

;;; ----- B+ support: can a citation DECISIVELY close the focus goal? ---------
;;; The dg has no undo, so B+ (the saturating closer) only commits a cite it can
;;; first SEE will land.  These are pure predicates over the current goal --
;;; they match and test membership, never touching the proof state.

;; Apply substitution alist SUBST (((v . val) ...)) to expression E.
(define (bc*--apply-subst subst e)
  (let loop ((s subst) (e e))
    (if (null? s) e
        (loop (cdr s) (subst-free (caar s) (cdar s) e)))))

;; Like bc*--peel but also collect the IMPLIES antecedents.
;; Returns (values schema-vars hyps conclusion).
(define (bc*--peel-full f)
  (let loop ((f f) (vars '()) (hyps '()))
    (cond
      ((and (pair? f) (eq? (car f) 'FORALL))
       (loop (caddr f) (cons (cadr f) vars) hyps))
      ((and (pair? f) (eq? (car f) 'IMPLIES))
       (loop (caddr f) vars (cons (cadr f) hyps)))
      (else (values (reverse vars) (reverse hyps) f)))))

;; bc*-can-close? NAME: is there an instantiation of NAME's schema vars under
;; which its conclusion matches the focus goal AND every hypothesis is already
;; an assumption?  If so return the full binding alist (ready for bc*-apply) --
;; citing it then closes the goal by assumption.  Else #f.  PURE: no mutation.
;; Greedy on hypothesis<->assumption pairing (first consistent assumption wins,
;; no backtracking over that choice) -- enough for the unambiguous cases B+
;; targets; a wrong early pairing just yields #f and B+ tries the next lemma.
(define (bc*-can-close? name)
  (and *ps*
       (hash-table-ref/default *theorem-table* name #f)
       (let* ((thm  (lookup-theorem name))
              (sqn  (proof-state-focus *ps*))
              (goal (wff-formula (sequent-node-assertion sqn)))
              (asms (map wff-formula (sequent-node-assumptions sqn))))
         (let-values (((svars hyps concl) (bc*--peel-full thm)))
           (let ((m (fluid-let ((*match-var-head* #t))
                      (match-expr concl goal svars))))
             (and m
                  (let loop ((hs hyps) (subst m))
                    (if (null? hs)
                        subst                         ; all hyps discharged
                        (let* ((h   (bc*--apply-subst subst (car hs)))
                               (rem (filter (lambda (v) (not (assoc v subst))) svars)))
                          (let try ((as asms))
                            (and (pair? as)
                                 (let ((hm (fluid-let ((*match-var-head* #t))
                                             (match-expr h (car as) rem))))
                                   (or (and hm
                                            (let ((merged (merge-subst subst hm)))
                                              (and merged (loop (cdr hs) merged))))
                                       (try (cdr as)))))))))))))))

;; Turn ((v val) ...) binding clauses into a runtime alist ((v . val) ...).
(define-syntax bc*-binds
  (syntax-rules ()
    ((_) '())
    ((_ (v val) more ...) (cons (cons 'v val) (bc*-binds more ...)))))

(define-syntax bc*
  (syntax-rules ()
    ((_ name)
     (bc*-apply name '()))
    ((_ name (bind ...))
     (bc*-apply name (bc*-binds bind ...)))
    ((_ name (bind ...) handler ...)
     (bc*-dispatch name (bc*-binds bind ...)
                   (list (quote handler) (lambda () handler)) ...))))

;;; -----------------------------------------------------------------------
;;; (ass-all) -- close every open goal dischargeable directly by assumption.
;;;
;;; Order-independent: it sweeps all open goals, closing each one whose goal
;;; is already in its context, and repeats until a sweep closes nothing.
;;; Goals that are not assumption-closable are left untouched.  This sidesteps
;;; the focus-order hazard when a case-split (di on AND, if-true, cut) leaves
;;; several trivial subgoals interleaved with real ones.

(define (ass-all)
  (vnb-guard
   (lambda ()
     (vnb--require-proof!)
     (let sweep ()
       (let ((progressed #f))
         (for-each
          (lambda (g)
            (when (not (sequent-node-grounded? g))
              (set-proof-state-focus! *ps* g)
              (let ((r (cmd-assumption *ps*)))
                (when (proof-state? r)
                  (set! *ps* r)
                  (set! progressed #t)))))
          (dg-ungrounded-nodes (proof-state-dg *ps*)))
         (when progressed (sweep))))
     (show))))

;;; -----------------------------------------------------------------------
;;; (catalog) -- write THEOREMS.md: every installed result, split into
;;; proven theorems / proof support set / axioms, alphabetical, with its
;;; statement.  The library is otherwise a flat hash spread over ~17 source
;;; files with no index.

(define (catalog--line name)
  (display "- `") (display name) (display "` — ")
  (display (expression->string (lookup-theorem name)))
  (let ((w (warrant-of name)))
    (when w (display "  _[warrant: ") (display (car w)) (display "]_")))
  (newline))

;;; (write-pss-md) -- write PSS.md with every (support ...) entry in
;;; alphabetical order, formula pretty-printed in VNB string syntax.
;;; Section headers (### name) make the file navigable with the same
;;; vnb-library-mode machinery that drives STRUCTURE-INDEX.md.
;;; Returns the path written.
(define (write-pss-md)
  (let* ((path (string-append *reference-dir* "PSS.md"))
         ;; collapse-rev-names: omit the auto-installed `-rev' companions (derived
         ;; flips, not independent supports) from the listing, as the catalog does.
         (names (collapse-rev-names
                 (filter (lambda (n) (memq n *support-theorem-names*))
                         (sort (hash-table-keys *theorem-table*)
                               (lambda (a b)
                                 (string<? (symbol->string a)
                                           (symbol->string b))))))))
    (define (render-entry name)
      (display "### ") (display name) (newline) (newline)
      (display "    ")
      (display (expression->string (lookup-theorem name)))
      (newline) (newline)
      (let ((g (gloss-of name)))
        (when g
          (display "*In words:* ") (display g) (newline) (newline)))
      (let ((w (warrant-of name)))
        (when w
          (display "*Warrant (") (display (car w)) (display "):* ")
          (display (cdr w)) (newline) (newline))))
    (with-output-to-file path
      (lambda ()
        (display "# Proof Support Set\n\n")
        (display "Auto-generated by `(write-pss-md)`.  ")
        (display (length names))
        (display " entries — accepted without machine proof, grouped by category.\n\n")
        ;; Sectioned by *pss-category-order*; an entry's category says WHAT KIND
        ;; of fact it is and (the intake discipline) why it is asserted, not proven.
        (for-each
          (lambda (co)
            (let* ((cat   (car co))
                   (title (cdr co))
                   (mem   (filter (lambda (n) (eq? (category-of n) cat)) names)))
              (when (pair? mem)
                (display "## ") (display title)
                (display "  (") (display (length mem)) (display ")\n\n")
                (for-each render-entry mem))))
          *pss-category-order*)
        ;; Anything not yet filed -- visible, not hidden (the soft nudge in print).
        (let ((rest (filter (lambda (n) (not (category-of n))) names)))
          (when (pair? rest)
            (display "## Uncategorized  (") (display (length rest))
            (display ")\n\nNot yet filed under a PSS category -- see `category!`.\n\n")
            (for-each render-entry rest)))))
    path))

;;; (write-definitions-md) -- write DEFINITIONS.md: every constant/predicate
;;; introduced by `def-constant' / `theory-add-definition!' (the authoritative
;;; `theory-definitions' registry that `display-definitions' reads), with its
;;; defining axiom(s) pretty-printed in VNB string syntax.  This is the
;;; concept-level index for term and predicate definitions -- e.g. CAUCHY
;;; sequence, CONVERGES, IS-COMPLETE -- the analogue of STRUCTURE-INDEX.md for
;;; structures.  Section headers (### name) make it navigable and PDF-viewable
;;; with the same vnb-library-mode machinery.  Returns the path written.
(define (definitions--strip-foralls f)
  (if (and (pair? f) (eq? (car f) 'FORALL))
      (definitions--strip-foralls (caddr f))
      f))

(define (definitions--rev-name? n)
  (let ((s (symbol->string n)))
    (and (> (string-length s) 4)
         (string=? "-rev" (substring s (- (string-length s) 4) (string-length s))))))

;;; The hand-written defining axioms: every `definitional'-stamped result that
;;; is a conservative defining `iff'/`==' (so NOT a view-as specialization,
;;; which is `implies'-shaped) and was installed via raw `theory-add-axiom!'
;;; rather than `def-predicate'/`def-constant' (so it never reached the
;;; `theory-definitions' registry the first section walks).  These are the
;;; property predicates (is-associative, ...), membership characterisations
;;; (preimage-membership, ...), the bin* apply laws, ordinal order (ord-lt-iff),
;;; and slot reads -- previously discoverable ONLY by reading source.
;;;
;;; Structure predicates (is-ring, ring-class, ...) are excluded: they live in
;;; STRUCTURE-INDEX.md with their full law bundles, keyed off the structure
;;; registries below, and `-rev' companions are dropped as derived duplicates.
(define (definitions--extra)
  (let* ((registered (map car (theory-definitions *current-theory*)))
         (snames     (append (hash-table-keys *structure-table*)
                             (hash-table-keys *definitional-structure-table*)))
         (struct-excl
          (apply append
                 (map (lambda (s)
                        (let ((ss (symbol->string s)))
                          (list (string->symbol (string-append "is-" ss))
                                (string->symbol (string-append "is-" ss "-def"))
                                (string->symbol (string-append ss "-class")))))
                      snames))))
    (sort
     (filter
      (lambda (n)
        (and (eq? (provenance-of n) 'definitional)
             (not (definitions--rev-name? n))
             (not (memq n registered))
             (not (memq n struct-excl))
             (let* ((m    (definitions--strip-foralls (lookup-theorem n)))
                    (conn (and (pair? m) (car m))))
               (memq conn '(IFF ==)))))
      (hash-table-keys *theorem-table*))
     (lambda (a b) (string<? (symbol->string a) (symbol->string b))))))

(define (write-definitions-md)
  (let* ((path  (string-append *reference-dir* "DEFINITIONS.md"))
         (defs  (sort (theory-definitions *current-theory*)
                      (lambda (a b) (string<? (symbol->string (car a))
                                              (symbol->string (car b))))))
         (extra (definitions--extra)))
    (with-output-to-file path
      (lambda ()
        (display "# VNB definitions\n\n")
        (display "Auto-generated by `(write-definitions-md)`.  ")
        (display (length defs)) (display " `def-constant`/`def-predicate` ")
        (display "definitions plus ") (display (length extra))
        (display " hand-written defining axioms — the whole `definitional`\n")
        (display "ledger of conservative `iff`/`=` definitions, minus the ")
        (display "structure predicates\n(`is-ring`, `ring-class`, …) that live in ")
        (display "`STRUCTURE-INDEX.md` with their law bundles.\n\n")
        (display "Introduced by `def-constant` / `def-predicate` / ")
        (display "`def-by-nn-recursion`; the macete is the definiendum's own ")
        (display "name.  Split by KIND (see `OPERATORS.md` for the full ")
        (display "operator taxonomy) — the recursion group are **functoids**, ")
        (display "NOT constants.\n\n")
        (let* ((render-entry
                (lambda (entry)
                  (display "### ") (display (car entry)) (newline) (newline)
                  (for-each
                    (lambda (ax)
                      (display "    ")
                      (display (expression->string (cdr ax)))
                      (newline) (newline))
                    (cdr entry))))
               (of-class (lambda (cls)
                           (filter (lambda (e)
                                     (eq? cls (op-defn-class (car e) (cdr e))))
                                   defs)))
               (preds (of-class 'predicate))
               (recs  (of-class 'recursive-functoid))
               (rest  (filter (lambda (e)
                                (not (memq (op-defn-class (car e) (cdr e))
                                           '(predicate recursive-functoid))))
                              defs)))
          (display "## Predicates\n\n")
          (display "Proposition-valued: `name(args) <=> body`.\n\n")
          (for-each render-entry preds)
          (display "## Recursively-defined functoids\n\n")
          (display "Defined by primitive recursion on `NN` ")
          (display "(`def-by-nn-recursion`): a `name-zero` base and a ")
          (display "`name-succ` step.  The extra parameters range over a class ")
          (display "(a ring, a monoid, ...), so each is a **functoid**, not a ")
          (display "function.\n\n")
          (for-each render-entry recs)
          (display "## Constants & other defined terms\n\n")
          (display "`def-constant` terms fixed by characterizing axioms.\n\n")
          (for-each render-entry rest))
        (display "## Other definitional axioms\n\n")
        (display "Conservative defining `iff`/`==` axioms installed via ")
        (display "`theory-add-axiom!`, so absent from the `def-*` registry above ")
        (display "but stamped `definitional` in the provenance ledger: property ")
        (display "predicates, membership characterisations, `bin*` apply laws, ")
        (display "ordinal order, slot reads.  Unfold with `(mac 'NAME)` / ")
        (display "`(mac-h 'NAME k)` under the name shown.\n\n")
        (for-each
          (lambda (n)
            (display "### ") (display n) (newline) (newline)
            (display "    ")
            (display (expression->string (lookup-theorem n)))
            (newline) (newline))
          extra)))
    path))

;;; -----------------------------------------------------------------------
;;; (write-functoids-md) -- write FUNCTORS.md: every def-functoid (the unfold-
;;; only constructors that land in NO other index), split by RETURN TYPE into
;;;   * Set- & structure-valued functoids -- body builds a tuple (LIST) or a
;;;     set (SEP, IMAGE, POWER, ...): COMPLETION, QUOTIENT, CHOOSE-SET, ...
;;;     (a syntactic split; only a few -- quotient, completion, ring-prod --
;;;     are the object map of a genuine categorical functor);
;;;   * Value functoids -- body is a TERM that is not a set/tuple: a function
;;;     (VNB-LAMBDA), an element, or a number: DIST-SEQ, EMBED, RING-POWER,
;;;     CHOOSE, ...  A functoid is NEVER proposition-valued (that is a
;;;     predicate); a VNB-LAMBDA body makes it function-VALUED, still a functoid.
;;; def-view-as functoids are excluded (they live in STRUCTURE-INDEX.md).

;; Heads whose application yields a tuple-structure or a set/space.
(define *structure-valued-heads*
  '(LIST SEP IMAGE POWER CARTESIAN UNION INTERSECTION BIG-UNION COMPLEMENT-IN
    INJECTION BIJECTION FUN MAKE-SET))

(define (functoid--head expr)
  (and (pair? expr) (symbol? (car expr)) (car expr)))

;; A body is structure/space-valued if its head is a kernel set/tuple builder,
;; or (one indirection, loop-guarded) another functoid that is itself such.
(define (functoid--structure-valued? body seen)
  (let ((h (functoid--head body)))
    (and h
         (or (memq h *structure-valued-heads*)
             (and (not (memq h seen))
                  (let ((reg (hash-table-ref/default *functoid-registry* h #f)))
                    (and reg
                         (functoid--structure-valued? (cadr reg) (cons h seen)))))))))

(define (write-functoids-md)
  (let* ((path  (string-append *reference-dir* "FUNCTORS.md"))
         (names (sort (filter (lambda (n) (not (lookup-view-as n)))
                              (hash-table-keys *functoid-registry*))
                      (lambda (a b) (string<? (symbol->string a)
                                              (symbol->string b)))))
         (functors (filter (lambda (n)
                             (functoid--structure-valued?
                               (cadr (hash-table-ref *functoid-registry* n #f)) '()))
                           names))
         (helpers  (filter (lambda (n) (not (memq n functors))) names))
         (write-one
          (lambda (n)
            (let* ((reg    (hash-table-ref *functoid-registry* n #f))
                   (params (car reg))
                   (body   (cadr reg)))
              (display "### ") (display n) (newline) (newline)
              (display "    ")
              (display (expression->string (cons n params)))
              (display " := ")
              (display (expression->string body))
              (newline) (newline)))))
    (with-output-to-file path
      (lambda ()
        (display "# VNB functoids\n\n")
        (display "Auto-generated by `(write-functoids-md)`.  ")
        (display (length functors)) (display " set/structure-valued + ")
        (display (length helpers))  (display " value functoids.\n\n")
        (display "Functoids are unfold-only constructors (`def-functoid`): a ")
        (display "macete rewrites `name(args)` to its body.  We write ")
        (display "`name(params) := body` for that defining unfold — `:=` is a ")
        (display "*definitional rewrite* (\"is defined as\"), NOT an object-level ")
        (display "equation; the body is total (it unfolds for any arguments, the ")
        (display "typing/meaning living in the warranted support lemmas).  ")
        (display "They appear in no ")
        (display "other index — `def-constant`/`def-predicate` go to ")
        (display "`DEFINITIONS.md`, `def-structure`/`def-view-as` to ")
        (display "`STRUCTURE-INDEX.md`.  Split below by *return type* (a ")
        (display "syntactic split, NOT a categorical one).\n\n")
        (display "## Set- & structure-valued functoids\n\n")
        (display "Body builds a tuple (`list`) or a set (`sep`, `image`, …).  ")
        (display "A few are the object map of a genuine functor — `quotient` ")
        (display "(setoid ↦ quotient set, with `descend` the morphism map), ")
        (display "`completion`, `ring-prod`, the `*-metric-space` bridges; the ")
        (display "rest (`class`, `ball`, `preimage`, `choose-set`, …) are ")
        (display "set-valued *constructions*, not functors.  `class(s,a)` in ")
        (display "particular is element-indexed: the value `proj(s)(a)` of the ")
        (display "quotient morphism, not a functor.\n\n")
        (for-each write-one functors)
        (display "\n## Value functoids\n\n")
        (display "Body is a **term**, not a set/tuple: a function (`vnb-lambda`), ")
        (display "an element, or a number — distance sequences, embeddings, ")
        (display "ring powers, counts.  A functoid is *never* proposition-valued ")
        (display "(that would be a predicate, see `DEFINITIONS.md`); when the body ")
        (display "is a `vnb-lambda` the functoid is **function-valued** but is ")
        (display "itself still a functoid (its argument ranges over a class).  ")
        (display "For the full operator taxonomy see `OPERATORS.md`.\n\n")
        (for-each write-one helpers)))
    (list path (length functors) (length helpers))))

;;; -----------------------------------------------------------------------
;;; (write-operators-md) -- OPERATORS.md: the OPERATOR CENSUS.
;;;
;;; An OPERATOR is any registered applied head.  This walks the whole
;;; *constant-registry* and classifies each per the VNB taxonomy (notes-21):
;;;
;;;   * FUNCTION   -- an operator f with  forsome A,B in Set. f in FUN(A,B):
;;;     a single set-to-set map.  At the NAMED-HEAD level essentially none
;;;     qualify, because every library constructor takes a structure/class
;;;     argument (a ring R, a set S, ...) so its domain is a proper class.
;;;     Functions live at the TERM level (elements of FUN(A,B)), typically
;;;     produced BY a functoid (VNB-LAMBDA, or a functoid's value).
;;;   * FUNCTOID   -- a term-valued operator that is NOT a function: a
;;;     def-functoid, a def-by-nn-recursion, a def-structure accessor, or a
;;;     kernel head pinned by a characterizing axiom (MATRIX, CARD, ...).
;;;     Its VALUE may itself be a function (COMB-KK(R,x,y,m) in FUN(ZZ,CARR R))
;;;     -- that makes it function-VALUED, still a functoid.
;;;   * PREDICATE  -- a proposition-valued operator (is-*, <, ...): body/char
;;;     axiom is an IFF whose left side is the head applied directly.
;;;   * PRIMITIVE  -- a foundational VNB term-former fixed by the kernel and
;;;     the base set-theory axioms (union, power, sep, +, ...), not a library
;;;     definition.
;;;
;;; Every operator MUST be declared -- by a def-form, a recursion, or a
;;; characterizing axiom.  A registered head with NO declaration is flagged
;;; UNDECLARED: the census exists to make such "mushrooms" visible.
;;;
;;; Returns (list path predicates functoids primitives undeclared) so a caller
;;; can act on the census, not just read it.

;; Foundational VNB term-formers (kernel + base set theory + arithmetic).
;; Everything else registered `operator' is a LIBRARY head, expected to carry
;; a characterizing axiom.
;; FUNCTIONS: operators that DENOTE a set-function -- an element of some FUN(A,B)
;; with A,B sets.  The numeric/analytic operators on RR/CC are functions
;; (exp, sin, cos, sqrt, |.|, Re, Im, conjugate, and the arithmetic
;; +,-,*,recip on RR^k -> RR).  VNB-LAMBDA is the BINDER that constructs a
;; set-function (its lambdoid sibling constructs a functoid; see the prose).
;; This is NOT an arbitrary "numeric base" carve-out: the criterion is uniform --
;; does the operator denote an element of a set FUN(A,B)?
(define *op-function-heads*
  '(+ - * recip abs conjugate succ exp sin cos sqrt rpow
    real-part imag-part magnitude VNB-LAMBDA))

;; Domains for the function heads (standard set-function signatures), so the
;; census can name each one instead of repeating "denotes a set-function".
(define *op-function-domains*
  '((+ . "RR x RR -> RR") (- . "RR x RR -> RR") (* . "RR x RR -> RR")
    (recip . "RR -> RR")  (abs . "RR -> RR")    (sqrt . "RR -> RR")
    (exp . "RR -> RR")    (sin . "RR -> RR")    (cos . "RR -> RR")
    (rpow . "RR x RR -> RR") (succ . "NN -> NN")
    (conjugate . "CC -> CC") (real-part . "CC -> RR")
    (imag-part . "CC -> RR") (magnitude . "CC -> RR")))

;; KERNEL term-formers: the foundational VNB set/tuple builders.  These are
;; FUNCTOIDS (their argument ranges over a proper class -- all sets -- so they
;; are not themselves elements of any set FUN(A,B)), distinguished only by ORIGIN
;; (kernel vs library) -- a metadata tag, NOT a VNB distinction and NOT a
;; separate semantic class.
;; EMPTY-SET is the degenerate case: a nullary constant denoting a set-element.
(define *op-kernel-heads*
  '(SET UNION INTERSECTION COMPLEMENT-IN CARTESIAN FUN INJECTION BIJECTION
    IMAGE SEP COMP BIG-UNION POWER LIST NTH MAKE-SET LENGTH CHOICE IOTA IF
    TUPLES DOM RAN RES PARTIAL-FUN apply-functoid PAIR EMPTY-SET))

;; Strip leading FORALL/FORSOME/IMPLIES down to the operative core formula.
(define (op-core f)
  (cond ((not (pair? f)) f)
        ((memq (car f) '(FORALL FORSOME)) (op-core (caddr f)))
        ((eq? (car f) 'IMPLIES) (op-core (caddr f)))
        (else f)))

;; Does H occur anywhere as an applied head (H ...)?
(define (op-mentions? h expr)
  (cond ((and (pair? expr) (eq? (car expr) h)) #t)
        ((pair? expr) (or (op-mentions? h (car expr)) (op-mentions? h (cdr expr))))
        (else #f)))

;; Characterizing / declaring theorems for head H: every non-`-rev' result
;; whose CONCLUSION mentions H applied.  Sorted so names containing H's own
;; text come first (the read-offs / membership chars), then the rest.
(define (op-char-axioms h)
  (let* ((hs   (symbol->string h))
         (hits (filter (lambda (n)
                         (and (not (definitions--rev-name? n))
                              (op-mentions? h (op-core (lookup-theorem n)))))
                       (hash-table-keys *theorem-table*))))
    (sort hits
          (lambda (a b)
            (let ((amatch (substring? hs (symbol->string a)))
                  (bmatch (substring? hs (symbol->string b))))
              (cond ((and amatch (not bmatch)) #t)
                    ((and bmatch (not amatch)) #f)
                    (else (string<? (symbol->string a) (symbol->string b)))))))))

;; Value-type hint for a functoid: read a codomain off a body or char axiom.
(define (op-valtype-of-body body)
  (let ((h (and (pair? body) (car body))))
    (cond ((eq? h 'VNB-LAMBDA)                         "function-valued")
          ((eq? h 'LIST)                               "tuple/structure-valued")
          ((memq h *structure-valued-heads*)           "set-valued")
          (else #f))))

;; Classify a theory-definitions entry (def-constant / def-*-recursion /
;; def-predicate all land here).  Returns one of 'predicate 'recursive-functoid
;; 'functoid 'constant.
(define (op-defn-class name axs)
  (let* ((axnames (map car axs))
         (has-succ (or (memq (symbol-append name '-succ) axnames)
                       (there-exists? axs
                         (lambda (ax)
                           (let ((c (op-core (cdr ax))))
                             (and (pair? c) (memq (car c) '(= ==))
                                  (pair? (cadr c)) (eq? (car (cadr c)) name)
                                  (op-mentions? 'succ (cadr c))))))))
         (pred? (there-exists? axs
                  (lambda (ax)
                    (let ((c (op-core (cdr ax))))
                      (and (pair? c) (eq? (car c) 'IFF)
                           (pair? (cadr c)) (eq? (car (cadr c)) name)))))))
    (cond (pred?    'predicate)
          (has-succ 'recursive-functoid)
          ((there-exists? axs
             (lambda (ax)
               (let ((c (op-core (cdr ax))))
                 (and (pair? c) (memq (car c) '(= ==))
                      (pair? (cadr c)) (eq? (car (cadr c)) name)
                      (null? (cdr (cadr c)))))))   ; nullary head = a constant
           'constant)
          (else 'functoid))))

;; The census record for one registered head: (name class subkind valtype axs).
(define (op-classify name kind)
  (cond
    ((eq? kind 'accessor)
     (list name 'functoid "structure accessor" "element (slot value)" '()))
    ((eq? kind 'functoid)
     (let* ((reg  (hash-table-ref/default *functoid-registry* name #f))
            (body (and reg (cadr reg)))
            (vt   (and body (op-valtype-of-body body))))
       (list name 'functoid "def-functoid"
             (or vt "element/number-valued") '())))
    ((eq? kind 'defined-fn)
     (let* ((entry (assq name (theory-definitions *current-theory*)))
            (axs   (if entry (cdr entry) '()))
            (cls   (op-defn-class name axs)))
       (list name
             (if (eq? cls 'predicate) 'predicate 'functoid)
             (case cls
               ((predicate)          "def-predicate")
               ((recursive-functoid) "recursively defined (def-by-nn-recursion)")
               ((constant)           "defined constant (def-constant)")
               (else                 "characterized by axioms (def-constant)"))
             (if (eq? cls 'predicate) "proposition" "term")
             (map car axs))))
    ((eq? kind 'operator)
     (cond
       ((eq? name 'VNB-LAMBDA)
        (list name 'function "binder: constructs a set-function" "function" '()))
       ((memq name *op-function-heads*)
        (list name 'function "denotes a set-function (element of FUN(A,B))"
              "set-function" '()))
       ((memq name *op-kernel-heads*)
        (list name 'functoid "kernel term-former" "term" '()))
       (else
        (let ((axs (op-char-axioms name)))
          (if (null? axs)
              (list name 'undeclared "REGISTERED HEAD, NO DECLARATION" "term" '())
              (list name 'functoid "characterized by axiom(s)" "term"
                    (list-head axs (min 8 (length axs)))))))))
    (else
     (list name 'functoid "unknown registry kind" "term" '()))))

(define (op-record-name r) (car r))
(define (op-record-class r) (cadr r))
(define (op-name<? a b) (string<? (symbol->string (car a)) (symbol->string (car b))))

(define (write-operators-md)
  (let* ((path  (string-append *reference-dir* "OPERATORS.md"))
         (heads (sort (filter (lambda (n) (not (lookup-view-as n)))
                              (hash-table-keys *constant-registry*))
                      (lambda (a b) (string<? (symbol->string a)
                                              (symbol->string b)))))
         (records (map (lambda (n) (op-classify n (constant-head? n))) heads))
         (by (lambda (cls) (filter (lambda (r) (eq? (op-record-class r) cls)) records)))
         (fns    (by 'function))
         (preds  (by 'predicate))
         (funcs  (by 'functoid))
         (undecl (by 'undeclared))
         (emit-section
          (lambda (title blurb recs)
            (display "## ") (display title)
            (display "  (") (display (length recs)) (display ")\n\n")
            (display blurb) (display "\n\n")
            (for-each
             (lambda (r)
               (let ((name (car r)) (sub (caddr r)) (vt (cadddr r))
                     (axs  (car (cddddr r))))
                 (display "### `") (display name) (display "`  — ")
                 (display sub)
                 (unless (string=? vt "term") (display " · ") (display vt))
                 (newline) (newline)
                 ;; def-functoid: show the unfolding body inline.
                 (let ((reg (hash-table-ref/default *functoid-registry* name #f)))
                   (when reg
                     (display "    ")
                     (display (expression->string (cons name (car reg))))
                     (display " := ")
                     (display (expression->string (cadr reg)))
                     (newline) (newline)))
                 ;; otherwise cite the declaring axioms.
                 (when (pair? axs)
                   (display "Declared by: ")
                   (for-each (lambda (a) (display "`") (display a) (display "` "))
                             axs)
                   (newline) (newline))))
             (sort recs op-name<?)))))
    (with-output-to-file path
      (lambda ()
        (display "# VNB operator census\n\n")
        (display "Auto-generated by `(write-operators-md)`.  Every registered ")
        (display "operator head, classified per the VNB taxonomy.\n\n")
        (display "An **operator** is a head symbol: a registered name that, ")
        (display "applied to argument terms, forms a compound term (or, when it ")
        (display "is a predicate, a proposition).  Not every head is a symbol.  ")
        (display "Every applied term has a *head* — the expression in operator ")
        (display "position — and that head may itself be a compound term rather ")
        (display "than a name (the function argument of `apply-functoid`, a ")
        (display "variable of function type, a `vnb-lambda` abstraction).  So ")
        (display "*head term* is the general notion and *operator* is the special ")
        (display "case where the head is a symbol.  This census lists the ")
        (display "operators — the symbols.\n\n")
        (display "The VNB universe has SETS (the elements of `SET`), CLASSES, and ")
        (display "further entities about which VNB makes no commitment.  A ")
        (display "term-forming operator is classified by WHAT IT DENOTES:\n")
        (display "- A **function** denotes an element of a set: specifically a ")
        (display "set-function, an element of some `FUN(A, B)` with `A`,`B` sets.  ")
        (display "The numeric and analytic operators are functions: ")
        (display "`exp`, `sin`, `cos`, `sqrt`, `abs`, `conjugate`, `real-part`, ")
        (display "`imag-part`, `magnitude`, and the arithmetic `+ - * recip`.  ")
        (display "`vnb-lambda` is the binder that constructs a set-function.\n")
        (display "- A **functoid** denotes something that is not required to be ")
        (display "an element of `SET`.  This is a large, somewhat amorphous ")
        (display "category: the kernel set- and tuple-builders (`union`, `sep`, ")
        (display "`power`, `fun`, `image`, …) whose arguments range over a proper ")
        (display "class; every library constructor (`matmul`, `mat-ring`, the ")
        (display "structure accessors, …); and the recursively-defined ones.  ")
        (display "Some functoids can be regarded as functions, but a functoid is ")
        (display "not required to be one.  `lambdoid` is the binder that ")
        (display "constructs a functoid — the class-domain sibling of ")
        (display "`vnb-lambda`; `apply-functoid` applies one.  Whether an ")
        (display "operator is a kernel primitive or a library definition is a ")
        (display "matter of ORIGIN, recorded as metadata; it is not a VNB ")
        (display "distinction and carries no semantic weight.  A kernel ")
        (display "set-former is a functoid exactly as a library constructor is.\n")
        (display "- A **predicate** is an operator whose application to argument ")
        (display "terms is a proposition — an entity whose value is either true ")
        (display "or false.  The proposition and its truth value are two separate ")
        (display "things in the mathematical universe: a predicate applied to ")
        (display "terms always denotes a proposition, but the truth value of that ")
        (display "proposition may not be known.\n\n")
        (display "Every operator must be declared (a def-form, a recursion, or a ")
        (display "characterizing axiom).  An **undeclared** head is a defect.\n\n")
        (display (length records)) (display " operators: ")
        (display (length fns))    (display " functions, ")
        (display (length funcs))  (display " functoids, ")
        (display (length preds))  (display " predicates, ")
        (display (length undecl)) (display " undeclared.\n\n")
        (when (pair? undecl)
          (display "> **⚠ Undeclared heads (mushrooms):** ")
          (for-each (lambda (r) (display "`") (display (car r)) (display "` ")) undecl)
          (display "— registered and usable but backed by no def or axiom.\n\n"))
        ;; Functions are terse: one line each, with the domain, not a
        ;; subsection apiece.
        (display "## Functions  (") (display (length fns)) (display ")\n\n")
        (display "Each denotes a set-function — an element of some `FUN(A,B)` ")
        (display "with `A`,`B` sets — with the standard domain shown.\n\n")
        (for-each
         (lambda (r)
           (let ((name (car r)) (dom (assq (car r) *op-function-domains*)))
             (display "- `") (display name) (display "`")
             (cond ((eq? name 'VNB-LAMBDA)
                    (display " is the binder that constructs a set-function."))
                   (dom (display " denotes a function `")
                        (display (cdr dom)) (display "`."))
                   (else (display " denotes a function.")))
             (newline)))
         (sort fns op-name<?))
        (newline)
        (emit-section "Functoids"
          (string-append
           "Term-valued operators that do NOT denote an element of `SET` — the "
           "big amorphous category.  Sub-labelled by how each is declared "
           "(`kernel term-former`; `def-functoid` body; `def-by-nn-recursion`; "
           "structure accessor; or a hand-written characterizing axiom) and, "
           "where known, by value type.  `def-view-as` bridges live in "
           "`STRUCTURE-INDEX.md`; `lambdoid` (the functoid binder) is a "
           "parser-level form, not a registered head.")
          funcs)
        (emit-section "Predicates"
          (string-append
           "Proposition-valued operators.  Their defining axiom is an `iff` on "
           "the applied head.  Full definitions in `DEFINITIONS.md`.")
          preds)
        (when (pair? undecl)
          (emit-section "Undeclared"
            (string-append
             "Registered operator heads with NO def-form and NO characterizing "
             "axiom.  Each is a defect: declare it or retire the head.")
            undecl))))
    (display ";; operators: ") (display (length records))
    (display " (") (display (length fns)) (display " functions, ")
    (display (length funcs)) (display " functoids, ")
    (display (length preds)) (display " predicates, ")
    (display (length undecl)) (display " undeclared) -> ")
    (display path) (newline)
    (list path (length fns) (length preds) (length funcs) (length undecl))))

(define (catalog)
  (let* (;; Drop the auto-installed `-rev' companions (same fact, flipped) -- they
         ;; are derived rewrite directions, not independent results, so listing
         ;; them doubles the catalog.  They stay installed/matchable; only the
         ;; listing omits them, as DEFINITIONS.md and the fingerprint index do.
         (all     (collapse-rev-names
                   (sort (hash-table-keys *theorem-table*)
                         (lambda (a b) (string<? (symbol->string a)
                                                 (symbol->string b))))))
         (proven  (filter (lambda (n) (memq n *proven-theorem-names*)) all))
         (support (filter (lambda (n) (memq n *support-theorem-names*)) all))
         (axioms  (filter (lambda (n)
                            (and (not (memq n *proven-theorem-names*))
                                 (not (memq n *support-theorem-names*))))
                          all))
         ;; Partition the stated-without-proof bucket by provenance.  Only the
         ;; `prim' group are AXIOMS (the fixed base of VNB set theory; schemas
         ;; included, so not finite).  `defn' are definitions, `asrt' are
         ;; assertions (the warrant candidates).  "axiom" is reserved for the
         ;; base -- it is NOT the umbrella for this whole bucket.
         (prim    (filter (lambda (n) (eq? (provenance-of n) 'primitive)) axioms))
         (defn    (filter (lambda (n) (eq? (provenance-of n) 'definitional)) axioms))
         (asrt    (filter (lambda (n) (and (not (memq n prim))
                                           (not (memq n defn)))) axioms))
         (path    (string-append *reference-dir* "THEOREMS.md")))
    (with-output-to-file path
      (lambda ()
        (display "# VNB catalog: theorems, axioms, definitions, assertions\n\n")
        (display "Auto-generated by `(catalog)`.  ")
        (display (length all))    (display " results — ")
        (display (length proven))  (display " proven, ")
        (display (length support)) (display " support (PSS), ")
        (display (length axioms))  (display " stated without proof (")
        (display (length prim))    (display " axioms, ")
        (display (length defn))    (display " definitions, ")
        (display (length asrt))    (display " assertions).\n\n")
        (display "## Proven theorems\n\n")
        (for-each catalog--line proven)
        (display "\n## Proof Support Set\n\n")
        (display "Results we accept without a machine proof in VNB.  ")
        (display "Logically treated as theorems.\n\n")
        (for-each catalog--line support)
        (display "\n## Stated without proof\n\n")
        (display "Not proved in VNB; split by *origin*.  \"Axiom\" is reserved ")
        (display "for the first group — it is NOT the umbrella for this ")
        (display "section.\n\n")
        (display "### Axioms — the fixed VNB base\n\n")
        (display "The foundational axioms of VNB set theory (make-vnb-base-")
        (display "theory core + theorem-library/axioms).  Fixed, though not ")
        (display "finite (separation/replacement are schemas).  Everything ")
        (display "else rests on these.\n\n")
        (display "> **The axioms below are NOT the whole trusted base.**  The ")
        (display "set- & class-formation *schemas* (separation `{x∈A|p}`, ")
        (display "comprehension `{x|p}`, indexed union `⋃_{z∈A}body`) carry a ")
        (display "formula schema in their body and so live in the proof checker ")
        (display "as primitive inference rules, not as formulas in this table.  ")
        (display "They are documented in `KERNEL-RULES.md`, which is the honest ")
        (display "statement of the trusted base: these axioms **plus** the ")
        (display "kernel rules.\n\n")
        (for-each catalog--line prim)
        (display "\n### Definitions — conservative extensions\n\n")
        (display "Emitted by def-/declare- forms (IS-X folding, accessor ")
        (display "laws, view typing).  Name new vocabulary; add no strength.\n\n")
        (for-each catalog--line defn)
        (display "\n### Assertions — accepted without proof\n\n")
        (display "Genuine mathematical content with no machine proof — the ")
        (display "warrant candidates.\n\n")
        (for-each catalog--line asrt)))
    (display ";; catalog: ") (display (length all))
    (display " results (") (display (length proven))
    (display " proven, ") (display (length support))
    (display " support, ") (display (length axioms))
    (display " stated = ") (display (length prim))
    (display " axioms + ") (display (length defn))
    (display " definitions + ") (display (length asrt))
    (display " assertions) -> ") (display path) (newline)
    (let ((dpath (write-definitions-md)))
      (display ";; definitions: ")
      (display (length (theory-definitions *current-theory*)))
      (display " -> ") (display dpath) (newline))
    (let ((fr (write-functoids-md)))
      (display ";; functoids: ")
      (display (cadr fr)) (display " set/structure-valued + ")
      (display (caddr fr)) (display " value -> ")
      (display (car fr)) (newline))
    (write-operators-md)
    (structure-index)
    (fingerprint-index)))

;;; (display-provenance) -- REPL triage of every installed result by its
;;; provenance kind (primitive / definitional / asserted / proven), counts
;;; first, then names.  Provenance is the epistemic origin (see
;;; *current-provenance* in macetes.scm), orthogonal to the support/proven
;;; display tags used by (catalog).
(define (display-provenance)
  (let ((all (sort (hash-table-keys *theorem-table*)
                   (lambda (a b) (string<? (symbol->string a)
                                           (symbol->string b))))))
    (for-each
      (lambda (kind)
        (let ((names (filter (lambda (n) (eq? (provenance-of n) kind)) all)))
          (display ";; ") (display kind) (display ": ")
          (display (length names)) (newline)
          (for-each (lambda (n)
                      (display ";;   ") (display n) (newline))
                    names)))
      *provenance-kinds*)))

;;; -----------------------------------------------------------------------
;;; (macete-index) -- PROTOTYPE retrieval view: bucket every installed result
;;; by the *head symbol of its conclusion* -- the leading operator a goal must
;;; mention for the macete to have any chance of firing.  Read-only: it reads
;;; *theorem-table* and writes MACETE-INDEX.md; it does NOT touch how proofs
;;; run or how macetes match.  This is the first brick of the proof-discovery
;;; direction (head-symbol / discrimination indexing; see the design chat).
;;;
;;; The key is computed the way the engine sees a theorem: prenex-positive +
;;; strip-foralls (the schema vars), then peel leading IMPLIES (follow the
;;; consequent) and a trailing = / IFF (take its LHS).  What remains is the
;;; conclusion; its leftmost atom is the redex head.  For a clean rewrite
;;; (= L R) that is L's operator; for a typing/predicate fact (IN .., IS-X ..)
;;; it is the predicate; for a backchain lemma (IMPLIES .. P) it is P's head.

(define (leftmost-atom e)
  (if (pair? e) (leftmost-atom (car e)) e))

(define (peel-to-conclusion core)
  (cond
    ((and (pair? core) (eq? (car core) 'IMPLIES))
     (peel-to-conclusion (binary-right core)))
    ((and (pair? core) (memq (car core) '(= IFF)))
     (binary-left core))
    (else core)))

(define (macete-redex-head formula)
  (let-values (((vars core) (strip-foralls (prenex-positive formula))))
    (let ((h (leftmost-atom (peel-to-conclusion core))))
      (cond ((memq h vars)     '<schema-var-head>)
            ((not (symbol? h))  '<non-symbol>)
            (else h)))))

;;; Generic relational heads carry little discriminating power on their own
;;; (everything typed lands under IN), so for those we also record the
;;; operator of the SUBJECT (first operand) -- (IN (ESUM g) RR) -> IN / ESUM.
(define *macete-generic-heads* '(IN <= < SUBSET))

(define (macete-subject-head formula)
  (let-values (((vars core) (strip-foralls (prenex-positive formula))))
    (let ((concl (peel-to-conclusion core)))
      (and (pair? concl)
           (memq (car concl) *macete-generic-heads*)
           (pair? (cdr concl))
           (let ((h (leftmost-atom (binary-left concl))))
             (cond ((memq h vars)    '<var>)
                   ((not (symbol? h)) '<non-symbol>)
                   (else h)))))))

(define (bucket-by proc names)
  ;; names -> alist (key . names-in-key), via ref/default + set!
  (let ((tbl (make-equal-hash-table)))
    (for-each
      (lambda (n)
        (let ((k (proc n)))
          (hash-table-set! tbl k (cons n (hash-table-ref/default tbl k '())))))
      names)
    (hash-table->alist tbl)))

(define (sort-syms ss)
  (sort ss (lambda (a b) (string<? (symbol->string a) (symbol->string b)))))

(define (macete-index)
  (let* ((all     (hash-table-keys *theorem-table*))
         (buckets (sort (bucket-by (lambda (n) (macete-redex-head (lookup-theorem n)))
                                   all)
                        (lambda (a b)
                          (let ((la (length (cdr a))) (lb (length (cdr b))))
                            (if (= la lb)
                                (string<? (symbol->string (car a))
                                          (symbol->string (car b)))
                                (> la lb))))))
         (path    (string-append *reference-dir* "MACETE-INDEX.md")))
    (with-output-to-file path
      (lambda ()
        (display "# Macete head-symbol index\n\n")
        (display "Auto-generated by `(macete-index)` -- a PROTOTYPE retrieval view.  ")
        (display "Each installed result is bucketed by the *head symbol of its ")
        (display "conclusion*: the leading operator a goal must mention for the ")
        (display "macete to fire.  A goal about `(ESUM ..)` need only consult the ")
        (display "`ESUM` bucket.  ")
        (display (length all)) (display " results, ")
        (display (length buckets)) (display " buckets.  Read-only: nothing about ")
        (display "matching or proof search changes.\n\n")
        (for-each
          (lambda (b)
            (let ((head  (car b))
                  (names (sort-syms (cdr b))))
              (display "## ") (display head)
              (display "  (") (display (length names)) (display ")\n\n")
              (if (memq head *macete-generic-heads*)
                  ;; secondary split by subject operator
                  (for-each
                    (lambda (sb)
                      (display "- **/ ") (display (car sb)) (display "**: ")
                      (let loop ((ns (sort-syms (cdr sb))) (first #t))
                        (unless (null? ns)
                          (unless first (display ", "))
                          (display "`") (display (car ns)) (display "`")
                          (loop (cdr ns) #f)))
                      (newline))
                    (sort (bucket-by (lambda (n) (or (macete-subject-head (lookup-theorem n))
                                                     '<other>))
                                     names)
                          (lambda (a c) (> (length (cdr a)) (length (cdr c))))))
                  (for-each (lambda (n) (display "- `") (display n) (display "`\n"))
                            names))
              (newline)))
          buckets)))
    (display ";; macete-index: ") (display (length all))
    (display " results in ") (display (length buckets))
    (display " head buckets -> ") (display path) (newline)
    (display ";; biggest: ")
    (for-each (lambda (b)
                (display (car b)) (display "(") (display (length (cdr b))) (display ") "))
              (list-head buckets (min 10 (length buckets))))
    (newline)
    path))

;;; (macetes-on SYM) -- REPL helper: list every macete whose conclusion
;;; *mentions the operator* SYM anywhere (an inverted index over conclusion
;;; operators, not just the head).  This is the lookup you actually want while
;;; hunting a lemma: `(macetes-on 'ESUM)` returns every ESUM fact regardless
;;; of whether it is headed by IN, <=, or =.  Head-keying alone misses these
;;; (the macete-index file shows why -- ESUM facts scatter under in/ and <=/).

;;; All operator symbols occurring anywhere in e (leftmost atom of every
;;; application node), deduped.
(define (operator-symbols e acc)
  (if (pair? e)
      (let* ((h    (leftmost-atom e))
             (acc2 (if (and (symbol? h) (not (memq h acc))) (cons h acc) acc)))
        (fold-left (lambda (a x) (operator-symbols x a)) acc2 e))
      acc))

;;; Strip the leading IMPLIES chain only (keep BOTH sides of a final = / IFF,
;;; so an equational rewrite is indexed by operators on both sides).
(define (peel-implies core)
  (if (and (pair? core) (eq? (car core) 'IMPLIES))
      (peel-implies (binary-right core))
      core))

(define (macete-conclusion-ops formula)
  (let-values (((vars core) (strip-foralls (prenex-positive formula))))
    (filter (lambda (s) (not (memq s vars)))
            (operator-symbols (peel-implies core) '()))))

(define (macetes-on sym)
  (let ((names (sort-syms
                (filter (lambda (n) (memq sym (macete-conclusion-ops (lookup-theorem n))))
                        (hash-table-keys *theorem-table*)))))
    (for-each (lambda (n)
                (display ";;   ") (display n) (display " : ")
                (display (expression->string (lookup-theorem n))) (newline))
              names)
    (display ";; ") (display (length names))
    (display " macete(s) whose conclusion mentions ") (display sym) (newline)))

;;; -----------------------------------------------------------------------
;;; (operator-index) -- the INVERTED / browsing view: BY-OPERATOR.md, one
;;; section per mathematical operator, listing every result whose statement
;;; MENTIONS it anywhere (hypothesis OR conclusion).  Answers "what do I know
;;; about X?" in one lookup -- which the head-keyed MACETE-INDEX.md cannot (a
;;; fact about ESUM is headed by IN/<=, a fact USING Cauchy hides it in a
;;; hypothesis).  Logical glue (AND/OR/IMPLIES/IFF/=/quantifiers) is omitted so
;;; sections are mathematical objects, not connectives.  `### op` headers make
;;; it navigable with the same vnb-library-mode machinery as PSS.md.

(define *operator-index-stoplist*
  '(AND OR IMPLIES IFF NOT FORALL FORSOME = == TRUTH FALSITY))

(define (macete-all-ops formula)
  (let-values (((vars core) (strip-foralls (prenex-positive formula))))
    (filter (lambda (s) (and (not (memq s vars))
                             (not (memq s *operator-index-stoplist*))))
            (operator-symbols core '()))))

(define (operator-index)
  (let ((tbl (make-equal-hash-table))           ; op -> names
        (all (hash-table-keys *theorem-table*)))
    (for-each
      (lambda (n)
        (for-each (lambda (op)
                    (hash-table-set! tbl op
                      (cons n (hash-table-ref/default tbl op '()))))
                  (macete-all-ops (lookup-theorem n))))
      all)
    (let* ((entries (sort (hash-table->alist tbl)
                          (lambda (a b) (string<? (symbol->string (car a))
                                                  (symbol->string (car b))))))
           (path    (string-append *reference-dir* "BY-OPERATOR.md")))
      (with-output-to-file path
        (lambda ()
          (display "# Macete index by operator\n\n")
          (display "Auto-generated by `(operator-index)`.  Inverted / browsing view: ")
          (display "one section per mathematical operator, listing every result whose ")
          (display "statement *mentions* it anywhere (hypothesis or conclusion), so ")
          (display "\"what do I know about X?\" is a single lookup.  Logical glue ")
          (display "(AND/OR/IMPLIES/IFF/=/quantifiers) is omitted.  ")
          (display (length entries)) (display " operators over ")
          (display (length all)) (display " results.  Complements the head-keyed ")
          (display "`MACETE-INDEX.md` (what each macete fires on).\n\n")
          (for-each
            (lambda (e)
              (let ((op (car e)) (names (sort-syms (cdr e))))
                (display "### ") (display op)
                (display "  (") (display (length names)) (display ")\n\n")
                (for-each (lambda (n) (display "- `") (display n) (display "`\n"))
                          names)
                (newline)))
            entries)))
      (display ";; operator-index: ") (display (length entries))
      (display " operators over ") (display (length all))
      (display " results -> ") (display path) (newline)
      path)))

;;; -----------------------------------------------------------------------
;;; CONCLUSION FINGERPRINT -- the depth-bounded structural key of a result's
;;; conclusion: head functor + immediate argument heads, recursively, to a
;;; fixed depth.  Schema variables (the leading universally-quantified vars)
;;; and non-symbol leaves (numerals) collapse to the wildcard `_`; constant
;;; operators (RR, CC, succ, ...) are kept verbatim.  Descends into ALL
;;; arguments -- including BOTH sides of a top `=`/`IFF` -- so no operator in
;;; the conclusion leaks out of the key (unlike macete-redex-head, which keeps
;;; only the head, and macete-subject-head, which descends only into the LEFT
;;; operand of a relation).  This single rule subsumes both.
;;;
;;; Examples (depth 2):
;;;   card-singleton  card({x})=succ(0)        -> (= (card _) (succ _))
;;;   complete-...    converges(s,l)           -> (converges _ _)
;;;   finsum-fubini   ...=finsum(.,finsum(.).) -> (= ... (finsum _ (finsum _ _ _) _))
;;;
;;; A variable-HEADED application (e.g. fun-apply-type's (f x), matched by
;;; bc*'s *match-var-head*) keys with head `_` -- the near-universal bucket.
;;; The key is an s-expr (equal?-hashable); render it with fingerprint->string.

;;; Depth 3 is the empirical knee: it resolves the membership idiom
;;; `iff(in(·, CONTAINER), ...)` (container one level under in under iff) that
;;; depth 2 leaves coiled in one bucket, while depth 4 adds almost nothing.
;;; The residual large buckets at every depth are the shallow algebraic
;;; rearrangement lemmas (= add(·,·) add(·,·)) -- the simplifier's territory,
;;; not the index's.
(define *fingerprint-default-depth* 3)
(define *fingerprint-wild* '_)   ; sentinel leaf, rendered as the dot below

;;; Fingerprint expression E to remaining DEPTH, with VARS the schema-var set.
(define (fingerprint-expr e depth vars)
  (cond
    ((not (pair? e))
     (if (or (memq e vars) (not (symbol? e))) *fingerprint-wild* e))
    ((<= depth 0) *fingerprint-wild*)            ; horizon: collapse subterm
    (else
     (let* ((head (car e))
            (hkey (if (symbol? head)
                      (if (memq head vars) *fingerprint-wild* head)
                      ;; compound head (rare, curried apply): use leftmost atom
                      (let ((a (leftmost-atom head)))
                        (if (or (memq a vars) (not (symbol? a)))
                            *fingerprint-wild* a)))))
       (cons hkey
             (map (lambda (a) (fingerprint-expr a (- depth 1) vars))
                  (cdr e)))))))

;;; The conclusion fingerprint of a (possibly quantified, implicational)
;;; theorem FORMULA: strip leading FORALLs, peel the IMPLIES chain, fingerprint
;;; the whole remaining conclusion (KEEPING a top =/IFF as the head, so both
;;; sides are indexed).  DEPTH defaults to *fingerprint-default-depth*.
(define (conclusion-fingerprint formula . opt-depth)
  (let ((depth (if (pair? opt-depth) (car opt-depth) *fingerprint-default-depth*)))
    (let-values (((vars core) (strip-foralls (prenex-positive formula))))
      (fingerprint-expr (peel-implies core) depth vars))))

;;; Memoized conclusion-fingerprint of an INSTALLED lemma, by name.  The hot
;;; retrieval loop (suggest-backchain-candidates) recomputes lemma fingerprints
;;; per goal per scout node; the lemma's conclusion is fixed, so cache it at the
;;; default depth (the only depth the hot path uses).  Non-default depths fall
;;; through to a fresh compute.  *lemma-fingerprint-memo* (macetes.scm) is
;;; invalidated by install-theorem! when a name is (re)installed.
(define (lemma-fingerprint name depth)
  (if (= depth *fingerprint-default-depth*)
      (or (hash-table-ref/default *lemma-fingerprint-memo* name #f)
          (let ((fp (conclusion-fingerprint (lookup-theorem name) depth)))
            (hash-table-set! *lemma-fingerprint-memo* name fp)
            fp))
      (conclusion-fingerprint (lookup-theorem name) depth)))

;;; Render a fingerprint key as f(a,b,...) with `·` for wildcards.
(define (fingerprint->string key)
  (cond
    ((eq? key *fingerprint-wild*) "·")
    ((symbol? key) (symbol->string key))
    ((pair? key)
     (string-append
       (fingerprint->string (car key))
       "("
       (let loop ((as (cdr key)) (first #t) (acc ""))
         (if (null? as)
             acc
             (loop (cdr as) #f
                   (string-append acc (if first "" ",")
                                  (fingerprint->string (car as))))))
       ")"))
    (else (call-with-output-string (lambda (p) (write key p))))))

;;; REPL helper: show one result's conclusion fingerprint.
(define (fingerprint-of name . opt-depth)
  (let* ((thm (lookup-theorem name))
         (key (apply conclusion-fingerprint thm opt-depth)))
    (display ";;   ") (display name) (display " : ")
    (display (fingerprint->string key)) (newline)
    key))

;;; -----------------------------------------------------------------------
;;; X / X-rev collapse (DISPLAY-ONLY).  install-theorem! (macetes.scm)
;;; auto-installs a reverse-direction companion `NAME-rev' for every
;;; symmetric-core (=/IFF/==) theorem -- same fact, flipped sides.  In
;;; human-facing listings the companion is pure noise (and shows up as the
;;; =-MIRROR of the base's fingerprint, e.g. `=(mul(one(·),·),·)' vs
;;; `=(·,mul(one(·),·))').  We suppress `NAME-rev' wherever its base `NAME'
;;; is present and tag the base `(±)' so the reverse is still discoverable.
;;; The -rev entries stay installed, matchable, and searchable; only the
;;; DISPLAY drops them.

;;; Remove ONE `-rev' segment from NAME and return the resulting symbol, or #f
;;; if NAME has no `-rev' segment.  A segment is `-rev' that is either trailing
;;; (`foo-rev') or infix-before-a-dash (`foo-rev-bar') -- the latter arises
;;; because view-specialization appends its own suffix AFTER the auto-companion
;;; flip, e.g. `abelian-group-mul-comm-rev-normed-ag-as-abelian-group'.
(define (rev-segment-removed name)
  (let* ((s (symbol->string name)) (n (string-length s)))
    (let loop ((i 0))
      (cond
        ((> (+ i 4) n) #f)
        ((and (string=? (substring s i (+ i 4)) "-rev")
              (or (= (+ i 4) n) (char=? (string-ref s (+ i 4)) #\-)))
         (string->symbol (string-append (substring s 0 i) (substring s (+ i 4) n))))
        (else (loop (+ i 1)))))))

;;; #t iff NAME is a `-rev' companion whose de-rev'd base IS installed -- the
;;; ones safe to hide.  (An orphan companion with no base survives.)
(define (suppressed-rev? name)
  (let ((base (rev-segment-removed name)))
    (and base (hash-table-ref/default *theorem-table* base #f) #t)))

;;; Drop suppressed -rev companions from a list of result names.
(define (collapse-rev-names names)
  (filter (lambda (n) (not (suppressed-rev? n))) names))

;;; The set (hash-table base->#t) of base names in NAMES that have at least one
;;; suppressed `-rev' companion -- exactly the bases to tag `(±)'.  Exact: walks
;;; the companions and records the base each de-revs to.
(define (rev-companion-base-set names)
  (let ((tbl (make-equal-hash-table)))
    (for-each (lambda (n)
                (let ((base (rev-segment-removed n)))
                  (when (and base (hash-table-ref/default *theorem-table* base #f))
                    (hash-table-set! tbl base #t))))
              names)
    tbl))

;;; (fingerprint-index) -- write FINGERPRINT-INDEX.md: bucket every installed
;;; result by its depth-N conclusion fingerprint, with X/X-rev companions
;;; collapsed (base tagged `(±)').  Read-only PROTOTYPE, like macete-index;
;;; nothing about matching or proof search changes.  The console summary
;;; reports discrimination quality (singleton buckets / biggest piles).
(define (fingerprint-index . opt-depth)
  (let* ((depth   (if (pair? opt-depth) (car opt-depth) *fingerprint-default-depth*))
         (full    (hash-table-keys *theorem-table*))
         (all     (collapse-rev-names full))
         (folded  (- (length full) (length all)))
         (tagged  (rev-companion-base-set full))
         (buckets (sort (bucket-by
                          (lambda (n)
                            (fingerprint->string
                              (conclusion-fingerprint (lookup-theorem n) depth)))
                          all)
                        (lambda (a b)
                          (let ((la (length (cdr a))) (lb (length (cdr b))))
                            (if (= la lb)
                                (string<? (car a) (car b))
                                (> la lb))))))
         (singles (length (filter (lambda (b) (= 1 (length (cdr b)))) buckets)))
         (path    (string-append *reference-dir* "FINGERPRINT-INDEX.md")))
    (with-output-to-file path
      (lambda ()
        (display "# Conclusion fingerprint index\n\n")
        (display "Auto-generated by `(fingerprint-index)` -- a PROTOTYPE retrieval view.  ")
        (display "Each installed result is bucketed by the depth-") (display depth)
        (display " *structural fingerprint* of its conclusion: head functor + ")
        (display "immediate argument heads, recursively, with `·` for schema ")
        (display "variables and numerals.  Both sides of a top `=`/`IFF` are kept, ")
        (display "so the key is the redex skeleton the matcher fires on.  ")
        (display (length all)) (display " results, ")
        (display (length buckets)) (display " buckets (")
        (display singles) (display " singletons); ")
        (display folded) (display " `-rev` companions folded into their base ")
        (display "(tagged `(±)`).  Read-only.\n\n")
        (for-each
          (lambda (b)
            (let ((key (car b)) (names (sort-syms (cdr b))))
              (display "### `") (display key) (display "`")
              (display "  (") (display (length names)) (display ")\n\n")
              (for-each (lambda (n)
                          (display "- `") (display n) (display "`")
                          (when (hash-table-ref/default tagged n #f) (display " (±)"))
                          (newline))
                        names)
              (newline)))
          buckets)))
    (display ";; fingerprint-index: ") (display (length all))
    (display " results in ") (display (length buckets))
    (display " fingerprint buckets (") (display singles)
    (display " singletons, ") (display folded)
    (display " -rev folded) -> ") (display path) (newline)
    (display ";; biggest: ")
    (for-each (lambda (b)
                (display "`") (display (car b)) (display "`(")
                (display (length (cdr b))) (display ") "))
              (list-head buckets (min 12 (length buckets))))
    (newline)
    path))

;;; -----------------------------------------------------------------------
;;; (structure-index) -- write STRUCTURE-INDEX.md: a navigable, structure-
;;; grouped view of the library.  For each structure registered in
;;; *structure-table* and each view in *view-as-table*, emit a section with
;;; its IS-X axiom statement, its named theorems, and the views into/out of
;;; it.  Called automatically by (catalog).

;;; Section anchor for a structure name: lower-case-kebab.
(define (struct-index--anchor name)
  (string-downcase (symbol->string name)))

;;; Does theorem-formula match (FORALL s (IMPLIES (IS-X s) P)) for given
;;; IS-X predicate?  Reuses the existing helper from structures.scm.
(define (struct-index--theorem-for? formula is-pred)
  (and (generic-for-struct? formula is-pred) #t))

;;; Names of theorems whose top-level shape is forall s. IS-X(s) ⟹ P[s].
(define (struct-index--theorems-for-struct struct-name all-theorem-names)
  (let ((is-pred (symbol-append 'IS- struct-name)))
    (filter (lambda (n)
              (and (not (eq? n is-pred))           ; skip the IS-X axiom itself
                   (not (eq? n (symbol-append struct-name '-class)))
                   (struct-index--theorem-for?
                     (hash-table-ref/default *theorem-table* n #f) is-pred)))
            all-theorem-names)))

;;; Views with target = struct-name.
(define (struct-index--views-into struct-name)
  (filter (lambda (v) (eq? (view-as-target-struct (lookup-view-as v))
                           struct-name))
          (hash-table-keys *view-as-table*)))

;;; Views with source = struct-name.
(define (struct-index--views-from struct-name)
  (filter (lambda (v) (eq? (view-as-source-struct (lookup-view-as v))
                           struct-name))
          (hash-table-keys *view-as-table*)))

;;; Deduped list of source structures with at least one view into struct-name.
(define (struct-index--unique-sources-into struct-name)
  (let loop ((vs (struct-index--views-into struct-name))
             (acc '()))
    (cond ((null? vs) (reverse acc))
          (else
           (let ((src (view-as-source-struct (lookup-view-as (car vs)))))
             (if (memq src acc)
                 (loop (cdr vs) acc)
                 (loop (cdr vs) (cons src acc))))))))

;;; Emit a compact-comma list using display-item for each element.
(define (struct-index--emit-comma items display-item)
  (let loop ((items items) (first? #t))
    (cond ((null? items) #t)
          (else
           (unless first? (display ", "))
           (display-item (car items))
           (loop (cdr items) #f)))))

;;; Emit the "Graph topology" adjacency-list section.  For each target
;;; structure with at least one incoming view, prints a single line
;;;     - [`target`](#anchor) ← `src1`, `src2`, ...
;;; The trailing paragraph lists structures with no incoming views
;;; ("graph sources"), so the reader can spot leaves at a glance.
(define (struct-index--emit-topology all-struct)
  (let* ((with-in   (filter (lambda (s) (not (null? (struct-index--views-into s))))
                            all-struct))
         (no-in     (filter (lambda (s) (null? (struct-index--views-into s)))
                            all-struct))
         (sym-tick  (lambda (s)
                      (display "`") (display s) (display "`"))))
    (display "## Graph topology\n\n")
    (display "Adjacency-list view of the view-as directed graph: each ")
    (display "target structure with the source structures pointing into ")
    (display "it.  Anchors link to per-structure detail sections.\n\n")
    (cond
      ((null? with-in)
       (display "*(no view-as edges declared yet)*\n\n"))
      (else
       (for-each
         (lambda (target)
           (display "- [`") (display target) (display "`](#")
           (display (struct-index--anchor target)) (display ") ← ")
           (struct-index--emit-comma
             (struct-index--unique-sources-into target)
             sym-tick)
           (newline))
         with-in)
       (newline)))
    (when (not (null? no-in))
      (display "*Structures with no incoming views (graph sources):* ")
      (struct-index--emit-comma no-in sym-tick)
      (display ".\n\n"))))

(define (struct-index--emit-axiom-line name)
  (let ((f (hash-table-ref/default *theorem-table* name #f)))
    (when f
      (display "- `") (display name) (display "` — ")
      (display (expression->string f)) (newline))))

;;; Substitute `(acc s)` with `acc` and bare `s` with `(LIST acc1 acc2 …)`
;;; throughout EXPR, where ACCESSORS is the structure's slot-name list.
;;; Used by `struct-index--emit-isx-axiom-destructured' to render the IS-X
;;; definitional predicate in destructured form (see the section comment
;;; near "Destructured pretty-print of IS-X axioms" below).
(define (destructure-isx-expr expr svar accessors)
  (cond
    ;; (acc s) where acc is one of the accessors → acc
    ((and (pair? expr)
          (= (length expr) 2)
          (memq (car expr) accessors)
          (eq? (cadr expr) svar))
     (car expr))
    ;; bare s → (LIST acc1 acc2 ...)
    ((eq? expr svar) `(LIST ,@accessors))
    ;; recurse into pairs (don't descend into the LIST tail we just made;
    ;; that's harmless because LIST's args are atoms here)
    ((pair? expr)
     (cons (destructure-isx-expr (car expr) svar accessors)
           (destructure-isx-expr (cdr expr) svar accessors)))
    (else expr)))

;;; -----------------------------------------------------------------------
;;; Destructured pretty-print of IS-X axioms
;;;
;;; The raw IS-X axiom for, say, FIELD prints as
;;;   forall([s], is-field(s) iff is-integral-domain(s) and ...)
;;; — which leaves the reader squinting at what `s` is and what `a(s)`,
;;; `add(s)`, … mean.  The destructured form makes the components explicit:
;;;   forall([a, add, mul, neg, zero, one]. is-field([a, add, mul, neg, zero, one]) iff
;;;     is-integral-domain([a, add, mul, neg, zero, one]) and ...
;;; Bound s is replaced by the n-tuple of slot accessors; every (acc s) in
;;; the body collapses to the bare accessor name.  No semantic change.
;;;
;;; Bound element variables inside the body (e.g. the `a` in
;;; `forall([a in a(s)], ...)`) keep their names and so collide visually
;;; with the carrier accessor `a` after substitution.  This is the same
;;; case-fold collision the rest of the prover handles by context; we
;;; accept it for the display.

;;; Capture-avoiding rename, applied BEFORE destructuring.  A law like
;;;   (FORALL a (IMPLIES (IN a (CARR s)) ... a ...))
;;; binds an ELEMENT variable `a` while the carrier accessor is also `a`.
;;; Destructuring (CARR s) -> a then turns the carrier into a bare `a`, so the
;;; law reads `forall a in a` -- a real variable capture, not just a clash.
;;; We rename any FORALL/FORSOME-bound var whose name is a slot accessor to a
;;; fresh name first.  Positional rule disambiguates the two roles: an
;;; accessor symbol in OPERATOR position (as in (a s)) is the free accessor
;;; and is kept; the same symbol as a bare operand/binder is the captured
;;; element var and gets renamed.
(define (rename-bound-vars-off-accessors expr accessors)
  (let ((used '()))
    (let collect ((e expr))
      (cond ((symbol? e) (unless (memq e used) (set! used (cons e used))))
            ((pair? e) (collect (car e)) (collect (cdr e)))))
    (define (fresh)
      (let loop ((cands '(x y z u v w i j k m n)))
        (cond ((null? cands)
               (let suffix ((n 1))
                 (let ((s (symbol-append 'v (string->symbol (number->string n)))))
                   (if (or (memq s used) (memq s accessors)) (suffix (+ n 1))
                       (begin (set! used (cons s used)) s)))))
              ((and (not (memq (car cands) used))
                    (not (memq (car cands) accessors)))
               (set! used (cons (car cands) used)) (car cands))
              (else (loop (cdr cands))))))
    (define (walk e env)
      (cond
        ((symbol? e) (let ((p (assq e env))) (if p (cdr p) e)))
        ((not (pair? e)) e)
        ((memq (car e) '(FORALL FORSOME))
         (let ((q (car e)) (var (cadr e)) (body (caddr e)))
           (if (and (symbol? var) (memq var accessors))
               (let ((nu (fresh)))
                 (list q nu (walk body (cons (cons var nu) env))))
               (list q var (walk body
                                  (if (symbol? var)
                                      (del-assq var env)
                                      env))))))
        (else
         ;; application: keep an accessor symbol in operator position as-is
         ;; (free accessor), otherwise walk it; always walk the operands.
         (let ((op (car e)))
           (cons (if (and (symbol? op) (memq op accessors)) op (walk op env))
                 (map (lambda (x) (walk x env)) (cdr e)))))))
    (walk expr '())))

;;; In the destructured IS-X body the tuple-length definedness conjunct
;;;   (= (LENGTH (LIST a mul e inv)) 4)
;;; is vacuously true -- destructuring already commits to an n-tuple, and the
;;; n named slots are right there -- so it only adds noise to the display.  We
;;; drop it from the destructured RENDER (the underlying axiom, where s is an
;;; opaque variable and the clause is load-bearing, is untouched).  Targeted:
;;; strips a length-equality only when its argument is the literal destructured
;;; LIST, so a genuine length constraint elsewhere would survive.
(define (struct-index--length-conjunct? c)
  (and (pair? c) (eq? (car c) '=) (= (length c) 3)
       (let ((side (lambda (x)
                     (and (pair? x) (eq? (car x) 'LENGTH)
                          (pair? (cdr x)) (pair? (cadr x))
                          (eq? (car (cadr x)) 'LIST)))))
         (or (side (cadr c)) (side (caddr c))))))

(define (struct-index--drop-length-conjuncts expr)
  (cond
    ((not (pair? expr)) expr)
    ((eq? (car expr) 'AND)
     (let ((kept (filter (lambda (c) (not (struct-index--length-conjunct? c)))
                         (map struct-index--drop-length-conjuncts (cdr expr)))))
       (cond ((null? kept)        'TRUTH)
             ((null? (cdr kept))  (car kept))
             (else (cons 'AND kept)))))
    (else (cons (struct-index--drop-length-conjuncts (car expr))
                (struct-index--drop-length-conjuncts (cdr expr))))))

;;; The destructured + bound-var-renamed IS-X law for NAME as an s-expr, or
;;; #f if NAME isn't a stored FORALL axiom.  Shared by the REPL string form
;;; (struct-index--emit-isx-axiom-destructured) and the TeX card form.
(define (isx-destructured-expr name accessors)
  (let ((f (hash-table-ref/default *theorem-table* name #f)))
    (and f (pair? f) (eq? (car f) 'FORALL)
         (struct-index--drop-length-conjuncts
           (destructure-isx-expr
             (rename-bound-vars-off-accessors f accessors)
             (cadr f) accessors)))))

(define (struct-index--emit-isx-axiom-destructured name accessors)
  (let ((destr (isx-destructured-expr name accessors)))
    (when destr
      (display "- `") (display name) (display "` — ")
      (display (expression->string destr)) (newline))))

;;; Render a source-file path as a markdown link, relative to *prover-dir*.
;;; Returns the empty string if path is #f.
;;;
;;; The path comes from `current-load-pathname' at declaration time.  When
;;; the prover is loaded from compiled .com files, that pathname has a #f
;;; type (no extension) -- so we force "scm" here: the declaration always
;;; lives in the .scm source regardless of what was loaded.  Without this,
;;; the link reads `structure-library/ring' and Emacs reports "File not
;;; found" (the .com-load file-not-found bug).
(define (struct-index--source-link path)
  (cond
    ((not path) "")
    (else
     (let* ((s   (->namestring (pathname-new-type (->pathname path) "scm")))
            (rel (if (and (>= (string-length s) (string-length *prover-dir*))
                          (string=? (substring s 0 (string-length *prover-dir*))
                                    *prover-dir*))
                     (substring s (string-length *prover-dir*) (string-length s))
                     s)))
       ;; href "../<rel>": pages live in reference/, sources one level up at the
       ;; prover root, so a browser resolves ../structure-library/X.scm correctly.
       (string-append "*Declared in* [`" rel "`](../" rel ").\n\n")))))

(define (struct-index--emit-structure name all-theorem-names)
  (let* ((sd        (lookup-structure name))
         (is-pred   (symbol-append 'IS- name))
         (accessors (structure-slot-names sd))
         (n-slots   (length accessors))
         (thms      (struct-index--theorems-for-struct name all-theorem-names))
         (vs-in     (struct-index--views-into name))
         (vs-out    (struct-index--views-from name)))
    (display "### ") (display name)
    (display "\n<a id=\"") (display (struct-index--anchor name)) (display "\"></a>\n\n")
    (display (struct-index--source-link (structure-def-source-file sd)))
    (display "*Kind.* Shape predicate (def-structure-from-clauses).\n\n")
    (display "*Slots* (") (display n-slots) (display "): ")
    (display "carriers ") (display (structure-def-carriers sd))
    (display ", ops/constants ") (display (map car (structure-def-op-specs sd)))
    (newline) (newline)
    (display "*Defining predicate* (destructured form):\n\n")
    (struct-index--emit-isx-axiom-destructured is-pred accessors)
    (newline)
    (when (not (null? thms))
      (display "*Theorems quantifying over `") (display is-pred) (display "`.*\n\n")
      (for-each struct-index--emit-axiom-line thms)
      (newline))
    (when (not (null? vs-in))
      (display "*Views into `") (display name) (display "`.*\n\n")
      (for-each
        (lambda (v)
          (let ((vd (lookup-view-as v)))
            (display "- `") (display v) (display "` — from `")
            (display (view-as-source-struct vd)) (display "`: ")
            (display (view-as-source-comps vd)) (display " ↦ ")
            (display (view-as-target-comps vd)) (newline)))
        vs-in)
      (newline))
    (when (not (null? vs-out))
      (display "*Views from `") (display name) (display "`.*\n\n")
      (for-each
        (lambda (v)
          (let ((vd (lookup-view-as v)))
            (display "- `") (display v) (display "` — into `")
            (display (view-as-target-struct vd)) (display "`: ")
            (display (view-as-source-comps vd)) (display " ↦ ")
            (display (view-as-target-comps vd)) (newline)))
        vs-out)
      (newline))))

;;; Render a definitional structure section (parallels --emit-structure).
;;; Definitional structures have no slot list; their IFF is "is-X-def" not "IS-X".
(define (struct-index--emit-definitional-structure name all-theorem-names)
  (let* ((dsd       (lookup-definitional-structure name))
         (is-pred   (symbol-append 'IS- name))
         (def-name  (string->symbol
                     (string-append "is-" (string-downcase (symbol->string name)) "-def")))
         (parent    (definitional-structure-parent dsd))
         (parent-sd (find-shape-structure parent))
         (accessors (and parent-sd (structure-slot-names parent-sd)))
         (thms      (struct-index--theorems-for-struct name all-theorem-names))
         (vs-in     (struct-index--views-into name))
         (vs-out    (struct-index--views-from name)))
    (display "### ") (display name)
    (display "\n<a id=\"") (display (struct-index--anchor name)) (display "\"></a>\n\n")
    (display (struct-index--source-link (definitional-structure-source-file dsd)))
    ;; Two kinds wear the same `register-definitional-structure!' hat: genuine
    ;; refinement PREDICATES (an `is-<name>-def' IFF axiom) and constant-tuple
    ;; INSTANCES (a `<name>-def' tuple axiom + `IS-X <name>' memberships, with
    ;; no `is-<name>-def').  The predicate path below would emit an empty
    ;; "Defining predicate" for every instance (the numeric rings/fields).
    ;; Discriminate exactly as `structure-card-md' does.
    (let ((inst-tuple (definitional-instance-tuple name)))
      (cond
        (inst-tuple
         (let ((mems (definitional-instance-memberships name)))
           (display "*Kind.* Instance — a constant tuple (an *element* of the ")
           (display "class, not a predicate).  Subtype of [`") (display parent)
           (display "`](#") (display (struct-index--anchor parent)) (display ").\n\n")
           (display "*Member of:*\n\n")
           (if (null? mems)
               (display "_(no membership witness installed)_\n")
               (for-each
                 (lambda (m)
                   (display "- `") (display (car m)) (display "` (via `")
                   (display (cdr m)) (display "`)\n"))
                 mems))
           (newline)
           (display "*Components* (mapped to inherited `") (display parent)
           (display "` slots):\n\n")
           (if (and accessors (= (length accessors) (length inst-tuple)))
               (for-each
                 (lambda (sn comp)
                   (display "- `") (display sn) (display "` = `")
                   (display (expression->string comp)) (display "`\n"))
                 accessors inst-tuple)
               (for-each
                 (lambda (comp)
                   (display "- `") (display (expression->string comp)) (display "`\n"))
                 inst-tuple))
           (newline)))
        (else
         (display "*Kind.* Definitional predicate (genuine IFF axiom).  ")
         (display "Subtype of [`") (display parent) (display "`](#")
         (display (struct-index--anchor parent)) (display ").  ")
         (display "Shape inherited from `") (display parent)
         (display "` — slots ") (display accessors) (display ".\n\n")
         (display "*Defining predicate* (destructured form):\n\n")
         (cond
           (accessors
            (struct-index--emit-isx-axiom-destructured def-name accessors))
           (else
            (struct-index--emit-axiom-line def-name)))
         (newline))))
    (when (not (null? thms))
      (display "*Theorems quantifying over `") (display is-pred) (display "`.*\n\n")
      (for-each struct-index--emit-axiom-line thms)
      (newline))
    (when (not (null? vs-in))
      (display "*Views into `") (display name) (display "`.*\n\n")
      (for-each
        (lambda (v)
          (let ((vd (lookup-view-as v)))
            (display "- `") (display v) (display "` — from `")
            (display (view-as-source-struct vd)) (display "`\n")))
        vs-in)
      (newline))
    (when (not (null? vs-out))
      (display "*Views from `") (display name) (display "`.*\n\n")
      (for-each
        (lambda (v)
          (let ((vd (lookup-view-as v)))
            (display "- `") (display v) (display "` — into `")
            (display (view-as-target-struct vd)) (display "`\n")))
        vs-out)
      (newline))))

;;; -----------------------------------------------------------------------
;;; describe-structure: a single-structure "card" for authoring recall.
;;;
;;; Prints, for one structure: its kind + inheritance chain, its operations
;;; with names and signatures (so you needn't remember whether the ring op
;;; is ADD or PLUS), the IS-X characteristic law, and the view-as relations
;;; in plain English.  Reuses the struct-index helpers.  Reads as plain text
;;; in the REPL; the elisp `describe-structure' command renders it in a card
;;; buffer and splices the user's editable notes underneath.

(define (describe-structure--slot-line slot)
  ;; slot = (name kind . extra); kind in {carrier, op, constant}
  (let ((nm (car slot)) (kind (cadr slot)) (extra (cddr slot)))
    (display "    ") (display nm)
    (case kind
      ((carrier)  (display "   carrier — the underlying set"))
      ((op)       (display " : ")
                  (display (expression->string (car extra)))
                  (display " → ")
                  (display (expression->string (cadr extra))))
      ((constant) (display " : ")
                  (display (expression->string (car extra)))
                  (display "   (distinguished element)"))
      ((substructure) (display "   ")
                  (display (string-downcase (symbol->string (car extra))))
                  (display " — a substructure of this kind"))
      (else       (display "   ?")))
    (newline)))

(define (describe-structure--join lst sep)
  (cond ((null? lst) "")
        ((null? (cdr lst)) (symbol->string (car lst)))
        (else (string-append (symbol->string (car lst)) sep
                             (describe-structure--join (cdr lst) sep)))))

(define (describe-structure--chain name)
  ;; Names from the shape root down to `name', following definitional parents.
  (let loop ((cur name) (acc '()))
    (let ((dsd (lookup-definitional-structure cur)))
      (if dsd
          (loop (definitional-structure-parent dsd) (cons cur acc))
          (cons cur acc)))))

(define (describe-structure--comp-map src tgt)
  (let loop ((s src) (t tgt) (first #t))
    (cond
      ((or (null? s) (null? t)) #t)
      (else
       (unless first (display ", "))
       (display (car s)) (display "↦") (display (car t))
       (loop (cdr s) (cdr t) #f)))))

(define (describe-structure--views name)
  (let ((vs-out (struct-index--views-from name))
        (vs-in  (struct-index--views-into name)))
    (when (not (null? vs-out))
      (newline)
      (display "Can be viewed as:") (newline)
      (for-each
        (lambda (v)
          (let ((vd (lookup-view-as v)))
            (display "    ") (display (view-as-target-struct vd)) (display "  (")
            (describe-structure--comp-map (view-as-source-comps vd)
                                          (view-as-target-comps vd))
            (display ")") (newline)))
        vs-out))
    (when (not (null? vs-in))
      (newline)
      (display "Viewable as ") (display name) (display " from:") (newline)
      (for-each
        (lambda (v)
          (let ((vd (lookup-view-as v)))
            (display "    ") (display (view-as-source-struct vd)) (newline)))
        vs-in))))

(define (describe-structure name)
  (let ((sd  (lookup-structure name))
        (dsd (lookup-definitional-structure name)))
    (cond
      (sd
       (display "═══ ") (display name) (display " ═══") (newline)
       (display "Kind: shape predicate (primitive structure).") (newline) (newline)
       (display "Operations (write  (OP s)  for component OP of structure s):") (newline)
       (for-each describe-structure--slot-line (structure-def-slots sd))
       (newline)
       (display "Characteristic law  ") (display (symbol-append 'IS- name)) (display "(s):") (newline)
       (struct-index--emit-isx-axiom-destructured (symbol-append 'IS- name)
                                                  (structure-slot-names sd))
       (describe-structure--views name))
      (dsd
       (let* ((chain  (describe-structure--chain name))
              (parent (definitional-structure-parent dsd))
              (shape  (find-shape-structure parent))
              (def-name (string->symbol
                         (string-append "is-" (string-downcase (symbol->string name)) "-def"))))
         (display "═══ ") (display name) (display " ═══") (newline)
         (display "Kind: definitional predicate (a refinement).") (newline)
         (display "Refines:  ") (display (describe-structure--join chain " ⊃ ")) (newline) (newline)
         (when shape
           (display "Operations (inherited shape; write  (OP s) ):") (newline)
           (for-each describe-structure--slot-line (structure-def-slots shape))
           (newline))
         (display "Characteristic law  ") (display (symbol-append 'IS- name)) (display "(s):") (newline)
         (if shape
             (struct-index--emit-isx-axiom-destructured def-name (structure-slot-names shape))
             (struct-index--emit-axiom-line def-name))
         (describe-structure--views name)))
      (else
       (display "describe-structure: unknown structure '") (display name) (display "'.") (newline)
       (display "Try (catalog) or Browse Library for the list.") (newline)))))

;;; Sorted list of every known structure name (shape + definitional).  Used
;;; by the elisp describe-structure command for name completion.
(define (known-structures)
  (sort (append (hash-table-keys *structure-table*)
                (hash-table-keys *definitional-structure-table*))
        (lambda (a b) (string<? (symbol->string a) (symbol->string b)))))

;;; All installed theorem/support/axiom names, alphabetical -- the completion
;;; pool for interactive lemma entry (the Focus Cite-Lemma `B' prompt).
(define (theorem-names)
  (sort (hash-table-keys *theorem-table*)
        (lambda (a b) (string<? (symbol->string a) (symbol->string b)))))

;;; Write the describe-structure card for NAME to PATH (consumed by the
;;; elisp card buffer, which then splices the editable notes underneath).
(define (write-structure-card name path)
  (with-output-to-file path
    (lambda () (describe-structure name)))
  path)

;;; -----------------------------------------------------------------------
;;; what-is: a "what is this thing?" copilot.  You type a token; it figures
;;; out what KIND of thing you meant and answers in kind.  A dispatcher runs
;;; ordered resolvers, first one that fires wins:
;;;
;;;   numeral   "7"        -> 7 in nn subseteq zz subseteq ... cc (the tower)
;;;   constant  "pi"/"%i"  -> symbol + TeX + type (pi in rr, i in cc)
;;;   alias     "complex"  -> the structure(s)/set(s) that word means
;;;   concept   "number"   -> the family (nn, zz-ring, qq-ring, ... ord)
;;;   substring "metric"   -> matching structure names + their shape/parts
;;;   fuzzy     "ordnial"  -> nearest name(s) by edit distance ("did you mean")
;;;
;;; The three tables below (*what-is-constants*, *what-is-aliases*,
;;; *what-is-sets*) are the data; extend them as the copilot grows.  Backs the
;;; elisp `M-x what-is' -- the front door for building a formula, since for a
;;; structure it tells you what `(OP s)' accessors you actually have.

(define (what-is--summary-line name)
  ;; one compact line: NAME — kind; parts: a b c
  (let ((sd  (lookup-structure name))
        (dsd (lookup-definitional-structure name)))
    (display "  ") (display name)
    (cond
      (sd
       (display "  — shape;  parts: ")
       (display (describe-structure--join (structure-slot-names sd) " ")))
      (dsd
       (let ((shape (find-shape-structure (definitional-structure-parent dsd))))
         (display "  — refines ")
         (display (definitional-structure-parent dsd))
         (when shape
           (display ";  parts: ")
           (display (describe-structure--join (structure-slot-names shape) " "))))))
    (newline)))

;;; --- data (case-folded lowercase, as the reader stores everything) -------

;;; The numeric tower, smallest first.  Inclusions: nn-subset-zz ... rr-subset-cc.
(define *what-is-tower* '(nn zz qq rr cc))

;;; Set name -> one-line gloss (the carriers a numeral/number-word lands in).
(define *what-is-sets*
  '((nn  . "natural numbers (0, 1, 2, ...)")
    (zz  . "integers")
    (qq  . "rationals")
    (rr  . "reals")
    (cc  . "complex numbers")
    (ord . "ordinals (a proper class)")))

;;; Named constant -> (TeX  surface-input  type  gloss).  %pi/%e parse as formal
;;; symbols (no value yet); %i evaluates to the exact Gaussian unit +i.
(define *what-is-constants*
  '((pi "\\pi"        "%pi" rr "ratio of a circle's circumference to its diameter; parsed as %pi, a formal symbol (no value/axiom yet)")
    (e  "\\mathrm{e}" "%e"  rr "base of the natural logarithm; parsed as %e, a formal symbol (no value/axiom yet)")
    (i  "i"           "%i"  cc "the imaginary unit, i^2 = -1; %i evaluates to the exact Gaussian unit +i")))

;;; Common word -> the structure(s)/set(s) it means.  Targets are resolved by
;;; `what-is--describe-target' (structure -> shape line; set -> gloss line).
(define *what-is-aliases*
  '(("complex"   cc-ring)
    ("real"      rr-ring)     ("reals"     rr-ring)
    ("rational"  qq-ring)     ("rationals" qq-ring)
    ("integer"   zz-ring)     ("integers"  zz-ring)
    ("natural"   nn)          ("naturals"  nn)
    ("ordinal"   ord)         ("ordinals"  ord)
    ("number"    nn zz-ring qq-ring rr-ring cc-ring ord)
    ("numbers"   nn zz-ring qq-ring rr-ring cc-ring ord)))

;;; --- resolvers (each prints + returns #t when it handles S, else #f) ------

(define (what-is--describe-target name)
  ;; A target is a structure (-> shape summary) or a tower set (-> gloss).
  (let ((setrow (assq name *what-is-sets*)))
    (cond
      ((or (lookup-structure name) (lookup-definitional-structure name))
       (what-is--summary-line name))
      (setrow
       (display "  ") (display name) (display "  -- set: ")
       (display (cdr setrow)) (newline))
      (else (display "  ") (display name) (newline)))))

(define (what-is--tower-tail set)
  ;; Suffix of the tower from SET up to cc.
  (let loop ((t *what-is-tower*))
    (cond ((null? t) '())
          ((eq? (car t) set) t)
          (else (loop (cdr t))))))

(define (what-is--number-set v)
  ;; Smallest tower set containing the real number V.
  (cond ((and (exact? v) (integer? v) (>= v 0)) 'nn)
        ((and (exact? v) (integer? v))          'zz)
        ((and (exact? v) (rational? v))         'qq)
        ((real? v)                              'rr)
        (else                                   'cc)))

(define (what-is--try-numeral s)
  (let ((v (string->number s)))
    (and v (real? v)
         (let* ((set (what-is--number-set v)) (tail (what-is--tower-tail set)))
           (display s) (display "  -- a number.") (newline)
           (display "  ") (display s) (display " in ")
           (display (describe-structure--join tail " subseteq ")) (newline)
           (display "  (smallest tower set: ") (display set)
           (display ";  inclusions nn-subset-zz ... rr-subset-cc)") (newline)
           #t))))

(define (what-is--try-constant s)
  (let* ((bare (if (and (> (string-length s) 0) (char=? (string-ref s 0) #\%))
                   (string-tail s 1) s))
         (row  (assq (string->symbol (string-downcase bare)) *what-is-constants*)))
    (and row
         (let ((tex (cadr row)) (mx (caddr row))
               (ty (cadddr row)) (gl (car (cddddr row))))
           (display (car row)) (display "  -- a named constant.") (newline)
           (display "  input as  ") (display mx)
           (display "      TeX  ") (display tex) (newline)
           (display "  ") (display mx) (display " in ") (display ty) (newline)
           (display "  (") (display gl) (display ")") (newline)
           #t))))

(define (what-is--try-alias s)
  (let ((row (assoc (string-downcase s) *what-is-aliases*)))
    (and row
         (let ((targets (cdr row)))
           (display s) (display "  -- ")
           (display (if (null? (cdr targets)) "means:" "could mean:")) (newline)
           (for-each what-is--describe-target targets)
           #t))))

(define (what-is--try-structures s)
  (let* ((low  (string-downcase s))
         (hits (filter (lambda (n)
                         (string-search-forward low (string-downcase (symbol->string n)) 0))
                       (known-structures))))
    (cond
      ((null? hits) #f)
      ((null? (cdr hits)) (describe-structure (car hits)) #t)
      (else
       (display (length hits)) (display " structures match \"")
       (display s) (display "\":") (newline) (newline)
       (for-each what-is--summary-line hits)
       (newline)
       (display "(describe-structure 'NAME) -- or M-x what-is on the full name -- for the full card.")
       (newline)
       #t))))

;;; Levenshtein edit distance (two-row DP) for typo-tolerant fallback.
(define (what-is--levenshtein a b)
  (let* ((la (string-length a)) (lb (string-length b))
         (prev (make-vector (+ lb 1) 0))
         (cur  (make-vector (+ lb 1) 0)))
    (do ((j 0 (+ j 1))) ((> j lb)) (vector-set! prev j j))
    (do ((i 1 (+ i 1))) ((> i la))
      (vector-set! cur 0 i)
      (do ((j 1 (+ j 1))) ((> j lb))
        (let ((cost (if (char=? (string-ref a (- i 1)) (string-ref b (- j 1))) 0 1)))
          (vector-set! cur j
            (min (+ (vector-ref cur (- j 1)) 1)
                 (+ (vector-ref prev j) 1)
                 (+ (vector-ref prev (- j 1)) cost)))))
      (do ((j 0 (+ j 1))) ((> j lb)) (vector-set! prev j (vector-ref cur j))))
    (vector-ref prev lb)))

(define (what-is--split-dash s)
  (let ((n (string-length s)))
    (let loop ((i 0) (start 0) (acc '()))
      (cond
        ((= i n) (reverse (cons (substring s start n) acc)))
        ((char=? (string-ref s i) #\-)
         (loop (+ i 1) (+ i 1) (cons (substring s start i) acc)))
        (else (loop (+ i 1) start acc))))))

;;; Distinct hyphen-components of structure names (>= 3 chars), each routed
;;; back through the substring resolver -- so a typo of a component ("mtric"
;;; for the "metric" in metric-space) still finds it.
(define (what-is--name-components)
  (let loop ((names (known-structures)) (seen '()) (acc '()))
    (if (null? names)
        (reverse acc)
        (let inner ((parts (what-is--split-dash (symbol->string (car names))))
                    (seen seen) (acc acc))
          (cond
            ((null? parts) (loop (cdr names) seen acc))
            ((or (< (string-length (car parts)) 3) (member (car parts) seen))
             (inner (cdr parts) seen acc))
            (else
             (let ((c (car parts)))
               (inner (cdr parts) (cons c seen)
                      (cons (cons c (lambda () (what-is--try-structures c))) acc)))))))))

;;; Every name a typo might have meant -- structures, their components, tower
;;; sets, alias words -- each paired with a thunk that renders it the right way
;;; (so a fuzzy hit on a set or alias word answers as a set/alias, not as a
;;; missing structure).
(define (what-is--fuzzy-candidates)
  (append
    (map (lambda (n) (cons (symbol->string n) (lambda () (describe-structure n))))
         (known-structures))
    (what-is--name-components)
    (map (lambda (r) (cons (symbol->string (car r))
                           (lambda () (what-is--describe-target (car r)))))
         *what-is-sets*)
    (map (lambda (r) (cons (car r) (lambda () (what-is--try-alias (car r)))))
         *what-is-aliases*)))

;; Keep the first (lowest-distance) entry per candidate string.
(define (what-is--dedup-near pairs)
  (let loop ((ps pairs) (seen '()) (acc '()))
    (cond ((null? ps) (reverse acc))
          ((member (car (caar ps)) seen) (loop (cdr ps) seen acc))
          (else (loop (cdr ps) (cons (car (caar ps)) seen) (cons (car ps) acc))))))

(define (what-is--try-fuzzy s)
  (let* ((low    (string-downcase s))
         (scored (map (lambda (c)
                        (cons c (what-is--levenshtein low (string-downcase (car c)))))
                      (what-is--fuzzy-candidates)))
         (thresh (max 2 (quotient (string-length low) 3)))
         (near   (what-is--dedup-near
                  (sort (filter (lambda (p) (<= (cdr p) thresh)) scored)
                        (lambda (a b) (< (cdr a) (cdr b)))))))
    (and (pair? near)
         (cond
           ;; one strictly-closest hit -> render it
           ((or (null? (cdr near)) (< (cdar near) (cdr (cadr near))))
            (display "what-is: no exact match for \"") (display s)
            (display "\" -- showing nearest, ") (display (car (caar near))) (display ":")
            (newline) (newline)
            ((cdr (caar near))) #t)
           (else
            (display "what-is: no match for \"") (display s)
            (display "\".  Did you mean:") (newline)
            (for-each (lambda (p) (display "  ") (display (car (car p))) (newline))
                      (list-head near (min 5 (length near))))
            #t)))))

;;; --- the dispatcher -------------------------------------------------------

(define (what-is needle)
  (let ((s (if (symbol? needle) (symbol->string needle) needle)))
    (or (what-is--try-numeral s)
        (what-is--try-constant s)
        (what-is--try-alias s)
        (what-is--try-structures s)
        (what-is--try-fuzzy s)
        (begin
          (display "what-is: nothing matching \"") (display s) (display "\".") (newline)
          (display "Try (catalog) or Browse Library for the full list.") (newline)
          #t))
    (if #f #f)))

;;; Capture a what-is answer to PATH (consumed by the elisp `vnb-what-is',
;;; which shows it in its own single-window buffer -- no REPL/proof split).
(define (write-what-is needle path)
  (with-output-to-file path (lambda () (what-is needle)))
  path)

;;; -----------------------------------------------------------------------
;;; Markdown + TeX card (the "beautiful" Emacs / manual form)
;;;
;;; Same content as `describe-structure', but emitted as markdown with every
;;; formula wrapped in $...$ so the elisp renderer can replace it with an
;;; inline PNG (latex -> dvipng).  This is the AUTO-GENERATED half of the
;;; manual; the user's editable prose/notes are spliced in by the elisp side.

;;; Flatten a (possibly nested) top-level AND into its conjuncts.
(define (and-conjuncts e)
  (if (and (pair? e) (eq? (car e) 'and))
      (apply append (map and-conjuncts (cdr e)))
      (list e)))

;;; One markdown bullet for a slot; signatures rendered as inline math.
(define (structure-card--sig-md slot)
  (let ((nm (symbol->string (car slot))) (kind (cadr slot)) (extra (cddr slot)))
    (case kind
      ((carrier)  (string-append "- **" nm "** — carrier (the underlying set)"))
      ((op)       (string-append "- **" nm "** : $" (expr->tex (car extra))
                                 " \\to " (expr->tex (cadr extra)) "$"))
      ((constant) (string-append "- **" nm "** : $" (expr->tex (car extra))
                                 "$ — distinguished element"))
      ((substructure) (string-append "- **" nm "** — a "
                                 (string-downcase (symbol->string (car extra)))
                                 " substructure"))
      (else       (string-append "- **" nm "**")))))

;;; The IS-X law, peeled to its defining conditions and emitted as one
;;; markdown bullet per top-level conjunct (each its own inline formula, so
;;; no single ruinously-wide image).
(define (structure-card--law-md is-name accessors)
  (let ((destr (isx-destructured-expr is-name accessors)))
    (cond
      ((not destr)
       (display "_(no stored characteristic law)_") (newline))
      (else
       (let* ((body (if (and (pair? destr) (eq? (car destr) 'forall)
                             (pair? (caddr destr))
                             (eq? (car (caddr destr)) 'iff))
                        (caddr (caddr destr))
                        destr))
              (cjs  (and-conjuncts body)))
         (display "`") (display is-name)
         (display "(s)` holds exactly when **all** of the following:")
         (newline) (newline)
         (for-each
           (lambda (c) (display "- $") (display (expr->tex-display c)) (display "$") (newline))
           cjs)
         (newline))))))

(define (structure-card--comp-map-md src tgt)
  (let loop ((s src) (t tgt) (first #t))
    (cond ((or (null? s) (null? t)) #t)
          (else (if (not first) (display ", "))
                (display (car s)) (display " ↦ ") (display (car t))
                (loop (cdr s) (cdr t) #f)))))

(define (structure-card--views-md name)
  (let ((vs-out (struct-index--views-from name))
        (vs-in  (struct-index--views-into name)))
    (when (not (null? vs-out))
      (newline) (display "## Can be viewed as") (newline) (newline)
      (for-each
        (lambda (v)
          (let ((vd (lookup-view-as v)))
            (display "- **") (display (view-as-target-struct vd)) (display "** — ")
            (structure-card--comp-map-md (view-as-source-comps vd)
                                         (view-as-target-comps vd))
            (newline)))
        vs-out))
    (when (not (null? vs-in))
      (newline) (display "## Specialised by") (newline) (newline)
      (for-each
        (lambda (v)
          (let ((vd (lookup-view-as v)))
            (display "- **") (display (view-as-source-struct vd)) (display "**") (newline)))
        vs-in))))

;;; An instance constant NAME has a `<name>-def' axiom of the form
;;; (= NAME (LIST ...)) -- the tuple.  (CARR refinement-predicate class has
;;; `is-<name>-def' instead.)  Return the component list, or #f if NAME is
;;; not such an instance.  This is the instance/refinement discriminator the
;;; card generator uses.
(define (definitional-instance-tuple name)
  (let* ((def-name (string->symbol
                     (string-append (string-downcase (symbol->string name)) "-def")))
         (ax (assq def-name (theory-axioms *current-theory*))))
    (and ax
         (let ((f (cdr ax)))
           (and (pair? f) (eq? (car f) '=) (eq? (cadr f) name)
                (pair? (caddr f)) (eq? (car (caddr f)) 'list)
                (cdr (caddr f)))))))

;;; All installed membership witnesses for the instance NAME: axioms of the
;;; form (IS-X NAME).  Returns a list of (is-pred . axiom-name).
(define (definitional-instance-memberships name)
  (let loop ((axs (theory-axioms *current-theory*)) (acc '()))
    (if (null? axs)
        (reverse acc)
        (let* ((entry (car axs)) (axname (car entry)) (f (cdr entry)))
          (if (and (pair? f) (= (length f) 2) (symbol? (car f)) (eq? (cadr f) name)
                   (let ((s (symbol->string (car f))))
                     (and (>= (string-length s) 3) (string=? (substring s 0 3) "is-"))))
              (loop (cdr axs) (cons (cons (car f) axname) acc))
              (loop (cdr axs) acc))))))

(define (structure-card-md name)
  (let ((sd  (lookup-structure name))
        (dsd (lookup-definitional-structure name)))
    (cond
      (sd
       (display "# ") (display name) (newline) (newline)
       (display "**Kind.** Shape predicate (primitive structure).") (newline) (newline)
       (display "## Operations") (newline) (newline)
       (display "Write `(op s)` for component `op` of a structure `s`.") (newline) (newline)
       (for-each (lambda (slot) (display (structure-card--sig-md slot)) (newline))
                 (structure-def-slots sd))
       (newline)
       (display "## Defining conditions") (newline) (newline)
       (structure-card--law-md (symbol-append 'IS- name) (structure-slot-names sd))
       (structure-card--views-md name))
      (dsd
       (let* ((inst-tuple (definitional-instance-tuple name))
              (parent     (definitional-structure-parent dsd))
              (shape      (find-shape-structure parent)))
         (cond
           (inst-tuple
            ;; --- Instance card: a constant tuple, an *element* of a class. ---
            (let ((slots (and shape (structure-slot-names shape)))
                  (mems  (definitional-instance-memberships name)))
              (display "# ") (display name) (newline) (newline)
              (display "**Kind.** Instance — a constant tuple (an *element* of a class, ")
              (display "not a predicate).") (newline) (newline)
              (display "**Member of:**") (newline) (newline)
              (if (null? mems)
                  (begin (display "_(no membership witness installed)_") (newline))
                  (for-each
                    (lambda (m)
                      (display "- **") (display (car m)) (display "** (via `")
                      (display (cdr m)) (display "`)") (newline))
                    mems))
              (newline)
              (display "## Components") (newline) (newline)
              (if (and slots (= (length slots) (length inst-tuple)))
                  (begin
                    (display "Mapped to the inherited `") (display parent)
                    (display "` slot names:") (newline) (newline)
                    (for-each
                      (lambda (sn comp)
                        (display "- **") (display sn) (display "** $= ")
                        (display (expr->tex comp)) (display "$") (newline))
                      slots inst-tuple))
                  (for-each
                    (lambda (comp)
                      (display "- $") (display (expr->tex comp)) (display "$") (newline))
                    inst-tuple))
              (newline)
              (structure-card--views-md name)))
           (else
            ;; --- Refinement-class card: a genuine is-<name>-def predicate. ---
            (let ((chain    (describe-structure--chain name))
                  (def-name (string->symbol
                              (string-append "is-" (string-downcase (symbol->string name))
                                             "-def"))))
              (display "# ") (display name) (newline) (newline)
              (display "**Kind.** Definitional predicate (a refinement).") (newline) (newline)
              (display "**Refines:** ") (display (describe-structure--join chain " ⊃ "))
              (newline) (newline)
              (when shape
                (display "## Operations") (newline) (newline)
                (display "Inherited shape; write `(op s)` for component `op`.") (newline) (newline)
                (for-each (lambda (slot) (display (structure-card--sig-md slot)) (newline))
                          (structure-def-slots shape))
                (newline))
              (display "## Defining conditions") (newline) (newline)
              (if shape
                  (structure-card--law-md def-name (structure-slot-names shape))
                  (struct-index--emit-axiom-line def-name))
              (structure-card--views-md name))))))
      (else
       (display "# ") (display name) (newline) (newline)
       (display "Unknown structure. Try `(known-structures)`.") (newline)))))

;;; Write the markdown+TeX card for NAME to PATH (consumed by the elisp card
;;; buffer, which renders the $...$ spans and splices the editable notes).
(define (write-structure-card-md name path)
  (with-output-to-file path (lambda () (structure-card-md name)))
  path)

;;; Write EVERY structure's card into one markdown file: the render-all
;;; "manual" reference.  Cards are separated by a horizontal rule.
(define (write-structure-manual-md path)
  (with-output-to-file path
    (lambda ()
      (display "# VNB Structure Library") (newline) (newline)
      (display "Auto-generated from the live theory — do not edit by hand.")
      (newline) (newline)
      (for-each
        (lambda (nm)
          (structure-card-md nm) (newline)
          (display "---") (newline) (newline))
        (known-structures))))
  path)

;;; -----------------------------------------------------------------------
;;; Graphviz DOT of the structure library.
;;;
;;; Nodes = structures.  Two edge kinds:
;;;   solid  -- "refines" (a definitional structure -> its parent), e.g.
;;;             field -> integral-domain;
;;;   dashed -- "view-as" (source -> target component map), e.g.
;;;             ring -> abelian-group, labelled with the view (source-name
;;;             prefix stripped: "additive-ag", "multiplicative-monoid", ...).
;;;
;;; Emitted to PATH; the elisp side renders it with `dot -Tpng' and shows it
;;; inline.  A self-contained light-canvas figure (readable on any buffer
;;; background), unlike the transparent inline formula PNGs.

(define (structure-graph--id name)
  (string-downcase (symbol->string name)))

;;; View label = the view name with a leading "<source>-" stripped, so e.g.
;;; ring-additive-ag -> additive-ag, field-as-euclidean-ring -> as-euclidean-ring.
(define (structure-graph--edge-label vname source)
  (let ((vs (string-downcase (symbol->string vname)))
        (ss (string-append (structure-graph--id source) "-")))
    (if (and (>= (string-length vs) (string-length ss))
             (string=? (substring vs 0 (string-length ss)) ss))
        (substring vs (string-length ss) (string-length vs))
        vs)))

;;; "(a add zero neg)" from the symbol list (a, add, zero, neg) -- for the
;;; component-map shown in an arrow's hover tooltip.
(define (structure-graph--symlist lst)
  (let loop ((l lst) (acc "(") (first? #t))
    (if (null? l)
        (string-append acc ")")
        (loop (cdr l)
              (string-append acc (if first? "" " ")
                             (string-downcase (symbol->string (car l))))
              #f))))

;;; Edge tooltip = the UNABBREVIATED functoid name (the symbol you actually
;;; call in proofs, e.g. RING-ADDITIVE-AG) plus the component map, so the SVG
;;; recovers what the short visible label drops.
(define (structure-graph--view-tooltip v)
  (string-append
    (string-downcase (symbol->string (view-as-name v))) " :  "
    (structure-graph--id (view-as-source-struct v)) " -> "
    (structure-graph--id (view-as-target-struct v)) "    "
    (structure-graph--symlist (view-as-source-comps v)) " |-> "
    (structure-graph--symlist (view-as-target-comps v))))

;;; Node tooltip = the structure's slot list.
(define (structure-graph--node-tooltip name)
  (let ((sd (find-shape-structure name)))
    (if sd
        (string-append (structure-graph--id name) " -- slots "
                       (structure-graph--symlist (structure-slot-names sd)))
        (structure-graph--id name))))

;;; All structures that should get an explicit, tooltip/URL-carrying node:
;;; shape structures plus definitional refinements (deduped).
(define (structure-graph--all-nodes)
  (let ((seen (make-equal-hash-table)) (out '()))
    (for-each (lambda (n)
                (unless (hash-table-ref/default seen n #f)
                  (hash-table-set! seen n #t)
                  (set! out (cons n out))))
              (append (known-structures)
                      (hash-table-keys *definitional-structure-table*)))
    (reverse out)))

;;; ---- bridges: structure-valued functoids as functor object-maps ----
;;; A BRIDGE is a def-functoid that carries one structure to another by BUILDING
;;; a new slot rather than reshuffling existing ones -- e.g.
;;;   NF-METRIC-SPACE : normed-field -> metric-space,  d(x,y) = NRM(x - y).
;;; Because the target's distinguishing slot (the metric DIST) is not a slot of the
;;; source, it cannot be a def-view-as (see normed-field-metric.scm) -- it is a
;;; plain functoid, hence invisible to the refines/view-as layers.  We recover
;;; the edges from the theorem that certifies the functor lands in its target:
;;;     FORALL x. IS-SRC(x) [and ...] => IS-TGT(F(x ...))
;;; with F a STRUCTURE-VALUED functoid and SRC/TGT both graph nodes.

(define (structure-graph--pred->struct pred)
  ;; IS-METRIC-SPACE -> 'metric-space, but only when that is a graph node.
  (and (symbol? pred)
       (let ((s (string-downcase (symbol->string pred))))
         (and (> (string-length s) 3)
              (string=? (substring s 0 3) "is-")
              (let ((nm (string->symbol (substring s 3 (string-length s)))))
                (and (memq nm (structure-graph--all-nodes)) nm))))))

(define (structure-graph--guard-structs ante)
  ;; source structures named by IS-X(var) conjuncts in an antecedent (AND-tree).
  (cond ((not (pair? ante)) '())
        ((eq? (car ante) 'AND)
         (append (structure-graph--guard-structs (binary-left ante))
                 (structure-graph--guard-structs (binary-right ante))))
        ((and (= (length ante) 2) (structure-graph--pred->struct (car ante)))
         (list (structure-graph--pred->struct (car ante))))
        (else '())))

(define (structure-graph--bridge-of formula)
  ;; strip FORALLs; on (IMPLIES ante (IS-TGT (F ...))) with F a structure-valued
  ;; functoid, return a list of (src tgt F) triples (one per guarded source).
  (let loop ((f formula))
    (cond
      ((and (pair? f) (eq? (car f) 'FORALL)) (loop (quantifier-body f)))
      ((and (pair? f) (eq? (car f) 'IMPLIES) (= (length f) 3))
       (let ((concl (binary-right f)))
         (and (pair? concl) (= (length concl) 2)
              (let ((tgt (structure-graph--pred->struct (car concl)))
                    (arg (cadr concl)))
                (and tgt (pair? arg) (symbol? (car arg))
                     ;; a bridge is a functoid that is NOT a view-as: a view-as
                     ;; reshuffles existing slots (its own layer); a bridge
                     ;; BUILDS a new one.  Exclude view-as functoids so we don't
                     ;; duplicate the dashed layer.
                     (not (lookup-view-as (car arg)))
                     (let ((reg (hash-table-ref/default *functoid-registry* (car arg) #f)))
                       (and reg
                            (functoid--structure-valued? (cadr reg) '())
                            (map (lambda (s) (list s tgt (car arg)))
                                 (structure-graph--guard-structs (binary-left f))))))))))
      (else #f))))

(define (structure-graph--bridges)
  (let ((seen (make-equal-hash-table)) (out '()))
    (for-each
      (lambda (name)
        (let ((b (structure-graph--bridge-of (lookup-theorem name))))
          (when (pair? b)
            (for-each
              (lambda (triple)
                (unless (hash-table-ref/default seen triple #f)
                  (hash-table-set! seen triple #t)
                  (set! out (cons triple out))))
              b))))
      (hash-table-keys *theorem-table*))
    (reverse out)))

(define (write-structure-graph-dot path)
  (with-output-to-file path
    (lambda ()
      (display "digraph VNB {\n")
      (display "  rankdir=BT;\n")
      (display "  bgcolor=\"white\";\n")
      (display "  node [shape=box, style=\"rounded,filled\", fillcolor=\"#eaf2fb\", color=\"#2a4a6a\", fontname=\"Helvetica\", fontsize=13];\n")
      (display "  edge [fontname=\"Helvetica\", fontsize=11];\n\n")
      ;; Nodes carry a slot-list tooltip and a click-through into the index.
      (for-each
        (lambda (n)
          (display "  \"") (display (structure-graph--id n))
          (display "\" [tooltip=\"") (display (structure-graph--node-tooltip n))
          (display "\", URL=\"structure-graph.html#") (display (structure-graph--id n))
          (display "\"];\n"))
        (structure-graph--all-nodes))
      (display "\n  // refines (specialisation): child -> parent\n")
      (for-each
        (lambda (name)
          (let* ((ds (lookup-definitional-structure name))
                 (parent (and ds (definitional-structure-parent ds))))
            (when parent
              (display "  \"") (display (structure-graph--id name))
              (display "\" -> \"") (display (structure-graph--id parent))
              (display "\" [color=\"#2a4a6a\", penwidth=1.4, tooltip=\"")
              (display (structure-graph--id name)) (display " refines ")
              (display (structure-graph--id parent)) (display "\"];\n"))))
        (hash-table-keys *definitional-structure-table*))
      (display "\n  // view-as (forgetful / component maps): source -> target\n")
      (for-each
        (lambda (vname)
          (let ((v (lookup-view-as vname)))
            (when v
              (display "  \"") (display (structure-graph--id (view-as-source-struct v)))
              (display "\" -> \"") (display (structure-graph--id (view-as-target-struct v)))
              (display "\" [style=dashed, color=\"#b06a00\", fontcolor=\"#b06a00\", label=\"")
              (display (structure-graph--edge-label vname (view-as-source-struct v)))
              (display "\", tooltip=\"") (display (structure-graph--view-tooltip v))
              (display "\", URL=\"structure-graph.html#views\"];\n"))))
        (hash-table-keys *view-as-table*))
      (display "\n  // bridges (structure-valued functoids): source -> target\n")
      (for-each
        (lambda (triple)
          (let ((src (car triple)) (tgt (cadr triple))
                (fn  (string-downcase (symbol->string (caddr triple)))))
            (display "  \"") (display (structure-graph--id src))
            (display "\" -> \"") (display (structure-graph--id tgt))
            (display "\" [style=dotted, color=\"#2a8a4a\", fontcolor=\"#2a8a4a\", penwidth=1.3, label=\"")
            (display fn)
            (display "\", tooltip=\"") (display fn) (display " :  ")
            (display (structure-graph--id src)) (display " -> ")
            (display (structure-graph--id tgt))
            (display "    (constructor functoid)\", URL=\"structure-graph.html#")
            (display (structure-graph--id tgt)) (display "\"];\n")))
        (structure-graph--bridges))
      (display "}\n")))
  path)

;;; Convenience for the CLI workflow (no Emacs launcher needed): write the
;;; enriched .dot to a stable path and return it.  MIT Scheme has no
;;; subprocess here, so render externally:
;;;   dot -Tsvg prover/structure-graph.dot -o prover/structure-graph.svg
;;; then open the .svg in a browser for live tooltips + click-through.
(define (structure-graph-dot-file)
  (let ((dot (string-append *reference-dir* "structure-graph.dot")))
    (write-structure-graph-dot dot)
    dot))

(define (structure-index)
  (let* ((sym<        (lambda (a b) (string<? (symbol->string a) (symbol->string b))))
         (structures  (sort (hash-table-keys *structure-table*) sym<))
         (defstructs  (sort (hash-table-keys *definitional-structure-table*) sym<))
         (all-struct  (sort (append structures defstructs) sym<))
         (views       (sort (hash-table-keys *view-as-table*) sym<))
         (all-names   (sort (hash-table-keys *theorem-table*) sym<))
         (path        (string-append *reference-dir* "STRUCTURE-INDEX.md")))
    (with-output-to-file path
      (lambda ()
        (display "# VNB structure-grouped index\n\n")
        (display "Auto-generated by `(catalog)`.  ")
        (display (length all-struct)) (display " structures (")
        (display (length structures)) (display " shape + ")
        (display (length defstructs)) (display " definitional), ")
        (display (length views))      (display " views.\n\n")
        (display "Each section lists a structure's defining predicate, the\n")
        (display "theorems quantifying over it, and the view-as declarations\n")
        (display "into/out of it.  *Shape* structures (def-structure-from-clauses)\n")
        (display "have a slot listing; *definitional* structures (genuine IFF\n")
        (display "predicates such as `IS-FIELD`) note their parent structure\n")
        (display "instead.  Anchors are lower-case-kebab: `#monoid`,\n")
        (display "`#ring-additive-ag`, etc.  Flat theorem listing in\n")
        (display "`THEOREMS.md`.\n\n")
        (display "## Table of contents\n\n")
        (for-each
          (lambda (s)
            (display "- [`") (display s) (display "`](#")
            (display (struct-index--anchor s)) (display ")")
            (when (lookup-definitional-structure s)
              (display " *(definitional, ⊂ ")
              (display (definitional-structure-parent (lookup-definitional-structure s)))
              (display ")*"))
            (newline))
          all-struct)
        (newline)
        (struct-index--emit-topology all-struct)
        (display "## Structures\n\n")
        (for-each
          (lambda (s)
            (cond
              ((lookup-structure s)
               (struct-index--emit-structure s all-names))
              ((lookup-definitional-structure s)
               (struct-index--emit-definitional-structure s all-names))))
          all-struct)
        (display "## View-as declarations (alphabetical)\n\n")
        (display "A view-as is a *forgetful functor* between structure ")
        (display "categories, in exactly two cases: it forgets **shape** ")
        (display "(keeps a sub-list of the source's slots) and/or forgets ")
        (display "**properties** (the target's laws are fewer than the ")
        (display "source's).  The slot map below is written in the *target's* ")
        (display "coordinates: position k shows which source accessor fills the ")
        (display "target's k-th slot.  Non-forgetful functors (quotient, ")
        (display "completion) are constructions, not views.\n\n")
        (for-each
          (lambda (v)
            (let ((vd (lookup-view-as v)))
              (display "- `") (display v) (display "` — `")
              (display (view-as-source-struct vd)) (display "` → `")
              (display (view-as-target-struct vd)) (display "`: ")
              (display (view-as-source-comps vd)) (display " ↦ ")
              (display (view-as-target-comps vd)) (newline)))
          views)))
    (display ";; structure-index: ") (display (length all-struct))
    (display " structures (") (display (length structures)) (display "+")
    (display (length defstructs)) (display "), ")
    (display (length views)) (display " views -> ") (display path) (newline)))

;;; D-7 short forms (REVIEW.md D-7) — SEP / COMP / IOTA / VNB-LAMBDA
(define (sep-set)  (vnb--run! 'sep-set  '() (lambda () (cmd-sep-sethood       *ps*))))
(define (sep-mi)   (vnb--run! 'sep-mi   '() (lambda () (cmd-sep-mem-intro     *ps*))))
(define (sep-me f)
  (vnb--run! 'sep-me (list f)
             (lambda ()
               (let ((raw (->raw-formula/idx f)))
                 (if (vnb-warning? raw) raw (cmd-sep-mem-elim *ps* raw))))))
(define (comp-mi)  (vnb--run! 'comp-mi  '() (lambda () (cmd-comp-mem-intro    *ps*))))
(define (comp-me f)
  (vnb--run! 'comp-me (list f)
             (lambda ()
               (let ((raw (->raw-formula/idx f)))
                 (if (vnb-warning? raw) raw (cmd-comp-mem-elim *ps* raw))))))
(define (iota-d t)  (let ((raw (->raw-formula t)))
                      (vnb--run! 'iota-d (list raw) (lambda () (cmd-iota-def *ps* raw)))))
(define (lam-t)    (vnb--run! 'lam-t    '() (lambda () (cmd-lambda-type      *ps*))))
(define (lam-b)    (vnb--run! 'lam-b    '() (lambda () (cmd-lambda-beta      *ps*))))

;;; BIG-UNION short forms (notes-16 step 1)
(define (bu-set)   (vnb--run! 'bu-set   '() (lambda () (cmd-big-union-sethood *ps*))))
(define (bu-mi w)  (let ((raw (->raw-formula w)))
                     (vnb--run! 'bu-mi (list raw) (lambda () (cmd-big-union-mem-intro *ps* raw)))))
(define (bu-me f)
  (vnb--run! 'bu-me (list f)
             (lambda ()
               (let ((raw (->raw-formula/idx f)))
                 (if (vnb-warning? raw) raw (cmd-big-union-mem-elim *ps* raw))))))

(define (inst f t)
  (vnb--run! 'inst (list f t)
             (lambda ()
               (let ((rawf (->raw-formula/idx f))
                     (rawt (->raw-formula t)))
                 (if (vnb-warning? rawf) rawf (cmd-instantiate *ps* rawf rawt))))))

;; (apply-thm 'thm t1 t2 ...) -- apply a registered theorem to terms positionally
;; (one per leading FORALL), landing the instantiated body in context.  A direct
;; "instantiate this theorem at these terms" move: it threads the live wff
;; objects through theorem-assumption + forall-elim rather than re-finding each
;; intermediate by alpha-equivalence.  NOTE: (fact ...) already does the same
;; instantiation (including when a term is a VNB-LAMBDA whose free vars collide
;; with the theorem's bound vars -- capture-avoidance handles that), so apply-thm
;; is a convenience, not a workaround for any defect; it differs from fact only
;; in skipping fact's forward-detach pass over in-context guards.
(define (apply-thm thm-name . terms)
  (let ((parsed (map ->raw-formula terms)))
    (vnb--run! 'apply-thm (cons thm-name parsed)
               (lambda () (cmd-spec *ps* thm-name parsed)))))
;; inst+ : instantiate an in-context universal at a term, then forward-detach
;; any in-context guards (the witness-choosing move scout's inst lane emits).
(define (inst+ f t)
  (vnb--run! 'inst+ (list f t)
             (lambda ()
               (let ((rawf (->raw-formula/idx f))
                     (rawt (->raw-formula t)))
                 (if (vnb-warning? rawf) rawf (cmd-inst+ *ps* rawf rawt))))))
(define (ce f k)
  (vnb--run! 'ce (list f k)
             (lambda ()
               (let ((raw (->raw-formula/idx f)))
                 (if (vnb-warning? raw) raw (cmd-cartesian-elim *ps* raw k))))))
(define (te f k)
  (vnb--run! 'te (list f k)
             (lambda ()
               (let ((raw (->raw-formula/idx f)))
                 (if (vnb-warning? raw) raw (cmd-tuples-elim *ps* raw k))))))
(define (ie f k)
  (vnb--run! 'ie (list f k)
             (lambda ()
               (let ((raw (->raw-formula/idx f)))
                 (if (vnb-warning? raw) raw (cmd-intersection-elim *ps* raw k))))))

;;; Switch focus to the n-th open goal (1-based).  Recorded for replay.
(define (focus n)
  (vnb-guard
    (lambda ()
      (vnb--require-proof!)
      (let ((goals (proof-open-goals *ps*)))
        (if (and (integer? n) (>= n 1) (<= n (length goals)))
            (begin
              (record-cmd! 'focus (list n))
              (set! *ps* (focus-on *ps* (list-ref goals (- n 1))))
              (show))
            (begin
              (display ";VNB warning: focus: index out of range: ")
              (display n) (display " (")
              (display (length goals)) (display " open goals)")
              (newline)))))))

;;; (focus-id k) -- focus the open goal whose displayed NODE NUMBER is k (the
;;; bracketed [k] in the state display), as opposed to (focus n) which takes a
;;; 1-based position.  This is what UI surfaces that show [k] should drive, so
;;; "focus [0]" focuses node 0 regardless of its position in the open-goal list.
(define (focus-id k)
  (vnb-guard
    (lambda ()
      (vnb--require-proof!)
      (let ((g (let loop ((gs (proof-open-goals *ps*)))
                 (cond ((null? gs) #f)
                       ((eqv? (sequent-node-number (car gs)) k) (car gs))
                       (else (loop (cdr gs)))))))
        (if g
            (begin
              (record-cmd! 'focus-id (list k))
              (set! *ps* (focus-on *ps* g))
              (show))
            (begin
              (display ";VNB warning: focus-id: no open goal with node number ")
              (display k) (newline)))))))

;;; -----------------------------------------------------------------------
;;; Install the completed current proof as a named theorem AND save the
;;; proof script under the same name.

(define (qed name)
  (vnb-guard
    (lambda ()
      (vnb--require-proof!)
      (cmd-qed *ps* name)
      (save-proof name)
      (set! *session-log*
            (append *session-log*
                    (list (list name *current-goal* *proof-script*))))
      (hash-table-set! *proof-start-counter* name *sp-counter-snapshot*)
      ;; Harvest the live trace (captured as the proof actually ran) so
      ;; proof-tex can render WITHOUT replaying -- robust for forward-fact proofs.
      (hash-table-set! *proof-live-trace* name (reverse *live-trace*))
      ;; Ledger: compute and memoize this proof's bill of asserted debt from
      ;; the just-saved script, then report `proven modulo {...}'.  (Defined
      ;; in proof-debt.scm, loaded right after this file.)
      (announce-proof-debt name (record-proof-debt! name))
      name)))

;;; -----------------------------------------------------------------------
;;; Replay a saved proof script on the current proof state.
;;;
;;; (replay-proof name)             -- replay verbatim
;;; (replay-proof name '((x . term-x) (y . term-y)))
;;;     -- substitute free variables in every command argument before applying.

(define (replay-proof name . maybe-subst)
  (vnb-guard
    (lambda ()
      (vnb--require-proof!)
      (let ((script (lookup-proof name))
            (subst  (if (null? maybe-subst) '() (car maybe-subst))))
        (fluid-let ((*replaying?* #t))
          (for-each (lambda (entry)
                      (let ((cmd-name (car entry))
                            (args     (cdr entry)))
                        (apply-recorded-cmd! cmd-name
                                             (map (lambda (a) (replay--subst-args subst a))
                                                  args))))
                    script))
        (show)))))

(define (replay--subst-args subst expr)
  (let loop ((s subst) (e expr))
    (if (null? s)
        e
        (loop (cdr s)
              (subst-free (caar s) (cdar s) e)))))

;;; Dispatch a recorded command back to its underlying cmd-* function.
;;; Bypasses recording (we call cmd-* directly, not the short form), so
;;; replay does not corrupt *proof-script*.
;;; A warning during replay is a hard error: the saved proof is broken.
(define (apply-recorded-cmd! name args)
  (let ((result
    (case name
      ((di)     (cmd-direct-inference *ps*))
      ((pbc)    (cmd-proof-by-contradiction *ps*))
      ((ass)    (cmd-assumption *ps*))
      ((arith)  (cmd-arith *ps*))
      ((rfl)    (cmd-reflexivity *ps*))
      ((qrfl)   (cmd-quasi-reflexivity *ps*))
      ((subst)  (cmd-eq-subst *ps* (car args)))
      ((oi-l)   (cmd-or-intro-left *ps*))
      ((oi-r)   (cmd-or-intro-right *ps*))
      ((ci)     (cmd-cartesian-intro *ps*))
      ((ti)     (cmd-tuples-intro *ps*))
      ((nth-r)  (cmd-nth-reduce *ps*))
      ((len-r)  (cmd-length-reduce *ps*))
      ((beta)   (cmd-functoid-beta *ps*))
      ((ii)     (cmd-intersection-intro *ps*))
      ((tfi)    (cmd-tfi  *ps*))
      ((tfi3)   (cmd-tfi3 *ps*))
      ((ai)     (cmd-antecedent-inference *ps* (->raw-formula/idx (car args))))
      ((cut)    (cmd-cut *ps* (car args)))
      ((if-true)  (cmd-if-true  *ps* (car args)))
      ((if-false) (cmd-if-false *ps* (car args)))
      ((ew)     (cmd-exists-witness *ps* (car args)))
      ((bc)     (cmd-backchain *ps* (->raw-formula/idx (car args))))
      ((wk)     (cmd-weaken *ps* (->raw-formula/idx (car args))))
      ((ui)     (cmd-union-intro *ps* (car args)))
      ((ue)     (cmd-union-elim *ps* (car args)))
      ((ta)     (cmd-theorem-assumption *ps* (car args)))
      ;; fact records (thm arglist): forward application of a theorem.
      ((fact)   (cmd-fact *ps* (car args) (cadr args)))
      ((mac)    (cmd-apply-macete *ps* (car args)))
      ((mac-h)  (cmd-apply-macete-to-assumption *ps* (car args) (->raw-formula/idx (cadr args))))
      ((mac-h*) (cmd-mac-h* *ps*))
      ((grind)  (cmd-grind *ps*))
      ((inst)   (cmd-instantiate *ps* (->raw-formula/idx (car args)) (->raw-formula (cadr args))))
      ((inst+)  (cmd-inst+ *ps* (->raw-formula/idx (car args)) (->raw-formula (cadr args))))
      ((ce)     (cmd-cartesian-elim *ps* (->raw-formula/idx (car args)) (cadr args)))
      ((ie)     (cmd-intersection-elim *ps* (->raw-formula/idx (car args)) (cadr args)))
      ((te)     (cmd-tuples-elim *ps* (->raw-formula/idx (car args)) (cadr args)))
      ((ni)     (cmd-nn-induction *ps*))
      ((rs)     (cmd-ring-simplify *ps*))
      ((crs)    (cmd-comm-ring-simplify *ps*))
      ((ineq)   (cmd-ineq *ps* args))
      ((sos)    (cmd-sos *ps* args))
      ;; D-7 replay dispatch
      ((sep-set) (cmd-sep-sethood       *ps*))
      ((sep-mi)  (cmd-sep-mem-intro     *ps*))
      ((sep-me)  (cmd-sep-mem-elim      *ps* (->raw-formula/idx (car args))))
      ((comp-mi) (cmd-comp-mem-intro    *ps*))
      ((comp-me) (cmd-comp-mem-elim     *ps* (->raw-formula/idx (car args))))
      ((iota-d)  (cmd-iota-def          *ps* (car args)))
      ((lam-t)   (cmd-lambda-type       *ps*))
      ((lam-b)   (cmd-lambda-beta       *ps*))
      ((bu-set)  (cmd-big-union-sethood  *ps*))
      ((bu-mi)   (cmd-big-union-mem-intro *ps* (car args)))
      ((bu-me)   (cmd-big-union-mem-elim  *ps* (->raw-formula/idx (car args))))
      ((focus)  (focus-on *ps*
                          (list-ref (proof-open-goals *ps*)
                                    (- (car args) 1))))
      ;; bc* re-derives by re-matching the conclusion (and any recorded
      ;; bindings) against the current goal, mutating *ps* in place; return
      ;; *ps* so the uniform (set! *ps* result) below is a no-op.  The recorded
      ;; entry is (bc* name bindings . handler-forms); any handler forms are
      ;; discharged on their subgoals via apply-recorded-cmd! (so the
      ;; hyp-discharge form replays faithfully too, not just (bc* 'n)).
      ((bc*)    (let* ((nm    (car args))
                       (bd    (if (pair? (cdr args)) (cadr args) '()))
                       (forms (if (pair? (cdr args)) (cddr args) '()))
                       (gs    (bc*-run! nm bd)))
                  (cond
                    ((not (list? gs))
                     (error "replay: bc* failed to re-apply" nm))
                    ((null? forms) *ps*)
                    ((not (= (length gs) (length forms)))
                     (error "replay: bc* handler/subgoal count mismatch" nm))
                    (else
                     (for-each (lambda (g form)
                                 (set-proof-state-focus! *ps* g)
                                 ;; Handler forms are recorded as re-runnable
                                 ;; SOURCE syntax ((quote handler) in the bc*
                                 ;; macro) -- quotes, nested begin/bc* intact --
                                 ;; NOT evaluated args.  Eval them directly:
                                 ;; routing through apply-recorded-cmd! (which
                                 ;; expects evaluated args) only ever coped with
                                 ;; bare (ass) and choked on (begin ...) or any
                                 ;; handler carrying a (quoted) argument.
                                 ;; Recording is suppressed here (*replaying?*).
                                 (eval form user-initial-environment))
                               gs forms)
                     *ps*))))
      (else (error "replay: unknown recorded command" name)))))
    (if (vnb-warning? result)
        (error "replay: command failed" name (vnb-warning-message result))
        (set! *ps* result))))

;;; -----------------------------------------------------------------------
;;; Emit a recorded proof script as readable, re-runnable command forms.
;;;
;;; A tactical like (repeat di) was already flattened into its primitive steps
;;; at record time, so the emitted script is in terms of kernel-ish commands
;;; and does NOT depend on repeat/orelse existing.  bc* is one entry --
;;; (bc* name bindings . handler-forms) -- emitted as loadable macro syntax
;;; (bc* 'name (binds ...) handler ...), so the hyp-discharge form re-nests
;;; instead of flattening its handlers into trailing steps.  Remaining gap:
;;; (ass-all) is not step-recorded.  The exact, guaranteed re-execution path is
;;; (replay-proof name); the emitted text is the human-readable / editable form.

;; Quote data args (symbols, lists) so the printed form re-reads; leave
;; self-evaluating args (numbers, strings, booleans) bare.
(define (script--emit-arg a)
  (if (or (number? a) (string? a) (boolean? a) (char? a))
      a
      (list 'quote a)))

;; bc* is a MACRO, so its emitted form must be literal macro syntax, NOT data:
;;   (bc* 'name (binds ...) handler ...)
;; The recorded entry is (bc* name bindings-alist . handler-forms).  Emit name
;; quoted (evaluated to the symbol), bindings as a LITERAL ((v val) ...) clause
;; list (NOT (quote ...), which the bc*-binds pattern would reject -> the old
;; `Ill-formed special form: (bc*-binds quote ())' bug), and handler forms RAW
;; as code.  An empty bindings + no handlers emits (bc* 'name ()), which the
;; macro routes to bc*-apply exactly as before.
(define (script--emit-bc* args)
  (let* ((name     (car args))
         (bindings (if (pair? (cdr args)) (cadr args) '()))
         (forms    (if (pair? (cdr args)) (cddr args) '()))
         (clauses  (map (lambda (p) (list (car p) (script--emit-arg (cdr p))))
                        bindings)))
    (append (list 'bc* (list 'quote name) clauses) forms)))

(define (proof-script->forms script)
  (map (lambda (entry)
         (if (eq? (car entry) 'bc*)
             (script--emit-bc* (cdr entry))
             (cons (car entry) (map script--emit-arg (cdr entry)))))
       script))

(define (script--write-forms port script)
  (for-each (lambda (form) (write form port) (newline port))
            (proof-script->forms script)))

;; Emit one (sp ...) <commands> (qed 'name) block to PORT.
(define (script--write-block port name goal script)
  (when goal
    (write `(sp (make-wff (quote ,goal))) port) (newline port))
  (script--write-forms port script)
  (when name
    (write `(qed (quote ,name)) port) (newline port)))

;; Print the current proof script (commands since the last sp) to the console.
(define (dump-proof-script)
  (let ((n (length *proof-script*)))
    (display ";; --- proof script: ")
    (display n) (display (if (= n 1) " step ---" " steps ---")) (newline)
    (script--write-forms (current-output-port) *proof-script*)
    (display ";; --- end ---") (newline)))

;; Write the current proof script to FILE as a standalone, re-loadable block:
;; (sp (make-wff '<goal>)) ... [ (qed 'NAME) ].  NAME optional.
(define (write-proof-script filename #!optional name)
  (let ((nm (if (default-object? name) #f name)))
    (call-with-output-file filename
      (lambda (port)
        (display ";; VNB proof script -- auto-emitted.  Re-load to replay.\n" port)
        (script--write-block port nm *current-goal* *proof-script*))))
  filename)

;; Print every proof completed this session (since load) as a sequence of
;; (sp ...) ... (qed 'name) blocks -- the whole session as one big script.
(define (dump-session)
  (if (null? *session-log*)
      (begin (display ";; (no proofs completed this session)") (newline))
      (for-each
       (lambda (rec)
         (script--write-block (current-output-port) (car rec) (cadr rec) (caddr rec))
         (newline))
       *session-log*)))

;; Write the whole session (all completed proofs, in order) to FILE.
(define (write-session filename)
  (call-with-output-file filename
    (lambda (port)
      (display ";; VNB session script -- all proofs completed this session.\n" port)
      (for-each
       (lambda (rec)
         (script--write-block port (car rec) (cadr rec) (caddr rec))
         (newline port))
       *session-log*)))
  filename)

;;; -----------------------------------------------------------------------
;;; Multi-variable quantification expanders
;;;
;;; Each binding is either (x) for a bare variable ranging over all objects,
;;; or (in x A) for a bounded variable restricted to class A.
;;;
;;; (fa '((x) (in y NN) (z)) 'BODY)
;;;   => (FORALL x (FORALL y (IMPLIES (IN y NN) (FORALL z BODY))))
;;;
;;; (fs '((x) (in y NN)) 'BODY)
;;;   => (FORSOME x (FORSOME y (AND (IN y NN) BODY)))

(define (fa bindings body)
  (if (null? bindings)
      body
      (let* ((b    (car bindings))
             (rest (fa (cdr bindings) body)))
        (cond
          ((and (pair? b) (= (length b) 1) (symbol? (car b)))
           `(FORALL ,(car b) ,rest))
          ((and (pair? b) (= (length b) 3)
                (eq? (cadr b) 'IN) (symbol? (car b)))
           `(FORALL ,(car b) (IMPLIES (IN ,(car b) ,(caddr b)) ,rest)))
          ((and (pair? b) (= (length b) 3)
                (eq? (car b) 'IN) (symbol? (cadr b)))
           `(FORALL ,(cadr b) (IMPLIES (IN ,(cadr b) ,(caddr b)) ,rest)))
          ;; (IN (LIST x1 ... xn) A) — tuple destructuring; expansion deferred to make-wff
          ((and (pair? b) (= (length b) 3)
                (eq? (car b) 'IN)
                (pair? (cadr b)) (eq? (car (cadr b)) 'LIST)
                (all-symbols? (cdr (cadr b))))
           `(FORALL ,b ,rest))
          (else (error "fa: invalid binding" b))))))

(define (fs bindings body)
  (if (null? bindings)
      body
      (let* ((b    (car bindings))
             (rest (fs (cdr bindings) body)))
        (cond
          ((and (pair? b) (= (length b) 1) (symbol? (car b)))
           `(FORSOME ,(car b) ,rest))
          ((and (pair? b) (= (length b) 3)
                (eq? (cadr b) 'IN) (symbol? (car b)))
           `(FORSOME ,(car b) (AND (IN ,(car b) ,(caddr b)) ,rest)))
          ((and (pair? b) (= (length b) 3)
                (eq? (car b) 'IN) (symbol? (cadr b)))
           `(FORSOME ,(cadr b) (AND (IN ,(cadr b) ,(caddr b)) ,rest)))
          ;; (IN (LIST x1 ... xn) A) — tuple destructuring; expansion deferred to make-wff
          ((and (pair? b) (= (length b) 3)
                (eq? (car b) 'IN)
                (pair? (cadr b)) (eq? (car (cadr b)) 'LIST)
                (all-symbols? (cdr (cadr b))))
           `(FORSOME ,b ,rest))
          (else (error "fs: invalid binding" b))))))

;;; -----------------------------------------------------------------------
;;; vnb-unwind / vnb-wind
;;;
;;; Operate on surface S-expressions in the new binding-list syntax.
;;; They do NOT expand to primitive form; use make-wff for that.
;;;
;;; vnb-unwind: (FORALL ((b1 b2 ... bn) ...) body)
;;;             => (FORALL ((b1)) (FORALL ((b2)) ... (FORALL ((bn)) body)...))
;;;
;;; vnb-wind:   (FORALL ((b1)) (FORALL ((b2)) body))
;;;             => (FORALL ((b1) (b2)) body)   [same quantifier type only]

;;; Flatten a binding spec to a list of single-var specs.
;;; (x y z) -> ((x) (y) (z));  (x) -> ((x));  (IN x A) -> ((IN x A))
(define (flatten-binding-spec b)
  (if (and (pair? b) (not (null? b)) (all-symbols? b) (not (eq? (car b) 'in)))
      (map list b)
      (list b)))

(define (vnb-unwind expr)
  (if (not (pair? expr))
      expr
      (cond
        ((and (memq (car expr) '(FORALL FORSOME))
              (= (length expr) 3)
              (pair? (cadr expr))
              (all-binding-specs? (cadr expr)))
         (let* ((q          (car expr))
                (flat-specs (apply append (map flatten-binding-spec (cadr expr))))
                (body       (vnb-unwind (caddr expr))))
           (let loop ((ss (reverse flat-specs)) (acc body))
             (if (null? ss)
                 acc
                 (loop (cdr ss) `(,q (,(car ss)) ,acc))))))
        (else (cons (car expr) (map vnb-unwind (cdr expr)))))))

(define (vnb-wind expr)
  (if (not (pair? expr))
      expr
      (let ((expr (cons (car expr) (map vnb-wind (cdr expr)))))
        (if (and (memq (car expr) '(FORALL FORSOME))
                 (= (length expr) 3)
                 (pair? (cadr expr))
                 (all-binding-specs? (cadr expr)))
            (let loop ((q     (car expr))
                       (specs (cadr expr))
                       (body  (caddr expr)))
              (if (and (pair? body)
                       (eq? (car body) q)
                       (= (length body) 3)
                       (pair? (cadr body))
                       (all-binding-specs? (cadr body)))
                  (loop q
                        (append specs (cadr body))
                        (caddr body))
                  `(,q ,specs ,body)))
            expr))))

;;; -----------------------------------------------------------------------
;;; Structure specialization shorthand
;;;
;;; (spec 'HARP 'RING 'harp-is-ring)
;;; Installs all ring theorems specialized to HARP.
;;; Not a proof command — does not touch *ps*.

(define (spec instance struct is-thm)
  (specialize-structure instance struct is-thm))
