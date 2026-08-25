;;; preamble.scm -- a STRATEGY, executed.
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
(define (preamble . clauses)
  (cond
   ((or (not *ps*) (proof-done? *ps*))
    (display ";; preamble: no open goal.") (newline) '())
   ((null? clauses)
    (error "preamble: no clauses -- expected e.g. (preamble '(induct) '(close))"))
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
