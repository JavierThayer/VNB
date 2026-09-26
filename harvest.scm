;;; harvest.scm -- MEASURE the What Now panel against the library's own proofs.
;;;
;;; THE QUESTION NOBODY COULD ANSWER.  Every lane of the copilot ranks by some
;;; syntactic proxy for relevance -- fingerprint specificity, connective count,
;;; term size, sequent vocabulary -- and each proxy is tuned on whatever goal
;;; provoked it.  Four lanes were changed on 2026-08-18 on the strength of ONE
;;; goal each.  Whether any of that helped ON AVERAGE was unknown, and unknowable
;;; without a measurement.  This file is the measurement.
;;;
;;; THE DATA IS ALREADY THERE, and no agent is needed to make it.  Every `qed'
;;; stores its command list in `*proof-script-table*' (interactive.scm:88), so a
;;; loaded library carries 464 scripts and 22,816 recorded steps -- and they are
;;; KNOWN-GOOD proofs, which is far better supervision than exploration would
;;; give: an agent driving proofs generates mostly failed branches, and you would
;;; be learning from the noise.
;;;
;;; THE SIGNAL.  Replay a script.  Before each step, the sequent is the input,
;;; the step actually taken is the positive label, and everything the panel
;;; offered and the author did NOT take is a negative.  What comes out is the
;;; number the panel has never had: was the move you wanted offered at all, and
;;; at what rank.
;;;
;;; MATCHING IS BY (TACTIC . NAME), deliberately.  A recorded step is
;;; `(fact metric-self-zero m a)' and the offered form is
;;; `(fact (quote metric-self-zero) (quote m) (quote a))'; comparing whole forms
;;; would score the panel on whether it guessed the same INSTANTIATION TERMS,
;;; which is a different and much harder question.  The question here is whether
;;; it named the right THEOREM.
;;;
;;; WHAT IT DOES NOT MEASURE, so the gap is visible.  Only steps whose tactic
;;; the panel is supposed to NAME something for are scored (`*harvest-scored*'
;;; below); `di'/`ass'/`ai' are structural and the live-fire lane reports them
;;; separately.  And a script that fails to replay is COUNTED AND REPORTED, not
;;; skipped silently -- composites that drive focus without recording themselves
;;; defeat replay (the complement-union case), and how many do is itself worth
;;; knowing.
;;;
;;; SELECTION BIAS, stated once.  The library was written by someone who already
;;; knew which lemma to cite, so this measures "does the panel name what an
;;; expert named".  That is the right target, but the tempting-and-wrong moves
;;; appear only as un-taken offers, never as labelled mistakes.
;;;
;;; Not in load.scm: it is an instrument, not part of the library.  Load it
;;; after a normal load and call `(harvest-report! N)'.

;;; The tactics whose job is to NAME a library fact.
(define *harvest-scored* '(fact mac mac-h bc bc* inst+ ta))

;;; How deep into an offered list still counts as "found".
(define *harvest-buckets* '(1 3 5 10 25))

(define (harvest--key form)
  (if (not (pair? form))
      (cons form #f)
      (let ((arg (and (pair? (cdr form)) (cadr form))))
        (cons (car form)
              (cond ((and (pair? arg) (eq? (car arg) 'quote) (pair? (cdr arg))) (cadr arg))
                    ((symbol? arg) arg)
                    (else #f))))))

(define (harvest--rank key moves)
  (let loop ((ms moves) (i 1))
    (cond ((null? ms) #f)
          ((equal? key (harvest--key (wn--move-form (car ms)))) i)
          (else (loop (cdr ms) (+ i 1))))))

;;; ---- accumulator -----------------------------------------------------
;;; (tactic . (scored found rank-sum . rank-list))
(define *harvest-stats* #f)
(define *harvest-failures* '())
(define *harvest-scripts-ok* 0)

(define (harvest--bump! tactic rank)
  (let ((e (hash-table-ref/default *harvest-stats* tactic (list 0 0 '()))))
    (hash-table-set! *harvest-stats* tactic
      (list (+ 1 (car e))
            (+ (if rank 1 0) (cadr e))
            (if rank (cons rank (caddr e)) (caddr e))))))

(define (harvest--measure! entry)
  (let* ((key (cons (car entry)
                    (let ((a (and (pair? (cdr entry)) (cadr entry))))
                      (cond ((and (pair? a) (eq? (car a) 'quote) (pair? (cdr a))) (cadr a))
                            ((symbol? a) a)
                            (else #f)))))
         ;; NOT wrapped in `vnb-guard'.  The guard is RE-ENTRANT: an outer call
         ;; sets `*vnb-guard-active*', and every INNER guard then becomes a
         ;; pass-through so errors propagate to the outermost one.  what-now's
         ;; lanes rely on their own guards -- a probe whose `have!' fails on a
         ;; false claim is normal and is swallowed locally -- so a defensive
         ;; wrapper here disabled all of that and the first probe error killed
         ;; the whole panel.  The first two runs of this file scored 0% because
         ;; of it, which looked like a result.  Wrapping a composite in
         ;; `vnb-guard' makes it MORE fragile, not less.
         (moves (what-now-moves (what-now-data))))
    (harvest--bump! (car entry)
                    (and (list? moves) (harvest--rank key moves)))))

(define (harvest--one name)
  (let ((goal   (vnb-guard (lambda () (lookup-theorem name))))
        (script (hash-table-ref/default *proof-script-table* name '())))
    (if (not (and (pair? goal) (pair? script)))
        #f
        (call-with-current-continuation
         (lambda (bail)
           (bind-condition-handler (list condition-type:error)
             (lambda (c) (set! *harvest-failures* (cons name *harvest-failures*)) (bail #f))
             (lambda ()
               ;; LEAVE-ONE-OUT.  The citation index is built from these very
               ;; scripts, so scoring `matmul-assoc''s citations with an index
               ;; that counted them is the index reading its own notes back.
               ;; `*cite-exclude-script*' subtracts this script's contribution
               ;; from every count for the duration (cite-index.scm).  Without
               ;; it the numbers below are not a measurement.
               (fluid-let ((*cite-exclude-script* name)
                           ;; Restore the fresh-var counter to this proof's
                           ;; sp-time value, as proof-tex's replay does.
                           ;; Eigenvariables are minted from a monotonic global,
                           ;; so without this a recorded `ai'/`ew' witness names
                           ;; a variable the replay never created -- 50 of the
                           ;; 1022 scripts died on that alone, and the death
                           ;; counted here as a replay failure of the script.
                           (*fresh-counter*
                            (hash-table-ref/default *proof-start-counter*
                                                    name *fresh-counter*)))
               (quietly
                (lambda ()
                  (sp (make-wff goal))
                  ;; `*replaying?*' is bound around the STEP ONLY, never around
                  ;; the measurement.  Binding it across `what-now' makes the
                  ;; panel error out -- its probes bind the same flag themselves
                  ;; (`vnb--probing', suggest.scm) to keep from recording phantom
                  ;; steps, and an outer binding defeats that: a lane's internal
                  ;; `have!' then fails and the whole call returns a vnb-error.
                  ;; The first run of this file scored 0% for exactly that reason
                  ;; and it looked like a result rather than a bug.
                  (for-each
                   (lambda (entry)
                     (if (memq (car entry) *harvest-scored*) (harvest--measure! entry))
                     (fluid-let ((*replaying?* #t))
                       (apply-recorded-cmd! (car entry) (cdr entry))))
                   script))))
               (set! *harvest-scripts-ok* (+ 1 *harvest-scripts-ok*))
               #t)))))))

;;; ---- the report ------------------------------------------------------
(define (harvest--pct n d) (if (= d 0) 0 (round (/ (* 100 n) d))))

(define (harvest-report! #!optional limit)
  (set! *harvest-stats* (make-equal-hash-table))
  (set! *harvest-failures* '())
  (set! *harvest-scripts-ok* 0)
  (let* ((all   (sort (hash-table-keys *proof-script-table*)
                      (lambda (a b) (string<? (symbol->string a) (symbol->string b)))))
         (names (if (default-object? limit) all
                    (list-head all (min limit (length all))))))
    (for-each harvest--one names)
    (newline)
    (display ";; ==== WHAT-NOW BASELINE ====") (newline)
    (display ";; scripts attempted : ") (display (length names)) (newline)
    (display ";; scripts replayed  : ") (display *harvest-scripts-ok*) (newline)
    (display ";; replay FAILURES   : ") (display (length *harvest-failures*))
    (display "  ") (display (list-head *harvest-failures*
                                       (min 6 (length *harvest-failures*))))
    (newline)
    (let ((tot 0) (fnd 0))
      (for-each
       (lambda (t)
         (let* ((e (hash-table-ref/default *harvest-stats* t #f)))
           (when e
             (let ((n (car e)) (f (cadr e)) (rs (caddr e)))
               (set! tot (+ tot n)) (set! fnd (+ fnd f))
               (display ";;   ") (display t)
               (display "  scored ") (display n)
               (display "  offered ") (display f)
               (display " (") (display (harvest--pct f n)) (display "%)")
               (for-each (lambda (b)
                           (display "  top") (display b) (display " ")
                           (display (harvest--pct
                                     (length (filter (lambda (r) (<= r b)) rs)) n))
                           (display "%"))
                         *harvest-buckets*)
               (newline)))))
       *harvest-scored*)
      (display ";; TOTAL scored ") (display tot)
      (display ", offered ") (display fnd)
      (display " (") (display (harvest--pct fnd tot)) (display "%)") (newline))
    (list (cons 'scripts *harvest-scripts-ok*)
          (cons 'failures *harvest-failures*)
          (cons 'stats *harvest-stats*))))

;;; -----------------------------------------------------------------------
;;; WHY WAS IT MISSED?  The baseline says `fact' is offered 16% of the time and
;;; that ALL of what it offers lands in the top 5 -- so the forward lane's
;;; problem is RECALL, not ranking, and no amount of re-sorting will move it.
;;; This is the instrument that says which of the lane's seven successive
;;; narrowings threw the author's citation away.  Each stage below is a real
;;; line of `what-now--forward-citations' / `what-now--show-forward-citations',
;;; re-run in order on the same sequent, and the FIRST one that rejects is the
;;; reason reported.
;;;
;;; Reasons, in the order the lane applies them:
;;;
;;;   unknown-name        the cited name is not in *theorem-table* at all
;;;   no-antecedent       the theorem has no hypothesis, so the lane skips it
;;;                       by design ("that is `ta''s job") -- but the author
;;;                       reached for `fact' anyway, so this is a hole
;;;   head-filter         no antecedent head occurs anywhere in the context
;;;   unmatched-k         antecedent k matches no assumption
;;;   svars-open          every antecedent matched, but the instantiation left
;;;                       a schema variable undetermined -- which is exactly the
;;;                       case the author fixes by NAMING the terms
;;;   landed-already      the conclusion is already in context (a real no-op)
;;;   churn               the conclusion is an assumption turned around
;;;   rank2-suppressed    it fired, but nothing outranked 2 and the lane
;;;                       reported the count instead of the list
;;;   foreign-vocab       demoted for introducing a head the sequent lacks
;;;   below-cut           ranked, but past *what-now-limit*
;;;   offered             it was there (so the miss is elsewhere)

(define *harvest-miss-reasons* #f)
(define *harvest-miss-examples* #f)
;;; For the below-cut cases: the rank the lane DID give the author's citation.
;;; This is the number that decides between "raise the cap" and "rank better".
;;; A median of 8 says the cap is the whole story; a median of 40 says no cap a
;;; reader would tolerate will help and the ordering has to change.
(define *harvest-miss-ranks* '())

(define (harvest--miss! reason name)
  (when *harvest-miss-reasons*
    (hash-table-set! *harvest-miss-reasons* reason
                     (+ 1 (hash-table-ref/default *harvest-miss-reasons* reason 0)))
    (let ((ex (hash-table-ref/default *harvest-miss-examples* reason '())))
      (if (< (length ex) 4)
          (hash-table-set! *harvest-miss-examples* reason (cons name ex))))))

;;; Mirror of `what-now--forward-fire', reporting WHERE it stopped rather than
;;; #f.  Returns 'ok, 'svars-open, or (unmatched . k) for the DEEPEST antecedent
;;; the search ever reached -- "it matched the first two hypotheses and stalled
;;; on the third" is a different finding from "nothing matched at all", and the
;;; search backtracks, so the last failure is not the informative one.
(define (harvest--fire-diagnosis thm asms pool)
  (let-values (((svars hyps concl) (bc*--peel-full thm)))
    (let ((flat (apply append (map what-now--conjuncts hyps))))
      (call-with-current-continuation
       (lambda (win)
         (let ((deepest 0) (saw-svars-open #f) (saw-not-grounded #f))
           (let loop ((hs flat) (subst '()) (k 1))
             (if (null? hs)
                 ;; ANCHORING is part of the lane now, so the mirror has to run
                 ;; it too or every anchored citation is reported as a miss the
                 ;; lane in fact makes.
                 (let ((sub (if (every-pred (lambda (v) (assoc v subst)) svars)
                                subst
                                (and pool
                                     (what-now--anchor-svars concl svars subst pool)))))
                   (if sub
                       (if (or (pair? flat)
                               (what-now--grounded-in?
                                (bc*--apply-subst sub concl) pool))
                           (win 'ok)
                           (set! saw-not-grounded #t))
                       (set! saw-svars-open #t)))
                 (begin
                   (if (> k deepest) (set! deepest k))
                   (let* ((h   (bc*--apply-subst subst (car hs)))
                          (rem (filter (lambda (v) (not (assoc v subst))) svars)))
                     (for-each
                      (lambda (a)
                        (let ((hm (fluid-let ((*match-var-head* #t))
                                    (match-expr h a rem))))
                          (if hm
                              (let ((merged (merge-subst subst hm)))
                                (if merged (loop (cdr hs) merged (+ k 1)))))))
                      asms)))))
           (cond (saw-not-grounded 'not-grounded)
                 (saw-svars-open 'svars-open)
                 (else (cons 'unmatched deepest)))))))))

(define (harvest--fact-miss-reason name goal asms)
  (let ((thm (hash-table-ref/default *theorem-table* name #f)))
    (if (not thm)
        'unknown-name
        (let-values (((svars hyps concl) (bc*--peel-full thm)))
          (let ((ctx-heads (apply append (map what-now--all-heads asms))))
            (cond
              ((and (null? hyps) (not *what-now-anchor*)) 'no-antecedent)
              ((not (if (pair? hyps)
                        (any-pred (lambda (h)
                                    (any-pred (lambda (hd) (memq hd ctx-heads))
                                              (what-now--all-heads h)))
                                  hyps)
                        (any-pred (lambda (hd) (memq hd ctx-heads))
                                  (what-now--all-heads concl))))
               'head-filter)
              (else
               (let ((d (harvest--fire-diagnosis
                         thm asms (and *what-now-anchor*
                                       (what-now--term-pool goal asms)))))
                 (cond
                   ((pair? d) (string->symbol
                               (string-append (if (pair? hyps) "unmatched-" "no-anchor-")
                                              (number->string (cdr d)))))
                   ((eq? d 'not-grounded) 'not-grounded)
                   ((eq? d 'svars-open) 'svars-open)
                   (else
                    ;; it fires -- so the loss is downstream, in the drops,
                    ;; the rank-2 suppression, the vocabulary split or the cap
                    (let* ((all (what-now--forward-citations goal asms))
                           (hit (let lp ((h all))
                                  (cond ((null? h) #f)
                                        ((eq? (car (car h)) name) (car h))
                                        (else (lp (cdr h)))))))
                      (cond
                        ((not hit) 'dropped-noop-or-churn)
                        ((and (every-pred (lambda (h) (= (cadddr h) 2)) all)
                              (= (cadddr hit) 2))
                         'rank2-suppressed)
                        ((let ((vs (what-now--split-vocab all goal)))
                           ;; (cdr vs) holds (HIT . FOREIGN-HEADS) pairs, not
                           ;; bare hits -- so the membership test is on the name.
                           (any-pred (lambda (p) (eq? (car (car p)) name)) (cdr vs)))
                         'foreign-vocab)
                        (else
                         (let* ((vs   (what-now--split-vocab all goal))
                                (hits (car vs))
                                (pos  (let lp ((h hits) (i 1))
                                        (cond ((null? h) #f)
                                              ((eq? (car (car h)) name) i)
                                              (else (lp (cdr h) (+ i 1)))))))
                           ;; Record the rank for EVERY citation the lane keeps,
                           ;; offered or not: the A/B question is where in the
                           ;; kept list the author's choice lands, and counting
                           ;; only the ones past the cap hides every improvement
                           ;; that pulls one inside it.
                           (cond ((not pos) 'foreign-vocab)
                                 (else
                                  (set! *harvest-miss-ranks*
                                        (cons pos *harvest-miss-ranks*))
                                  (if (> pos *what-now-limit*) 'below-cut 'offered)))))))))))))))))

;;; The report.  Run AFTER `harvest-report!' has populated nothing -- this is a
;;; separate pass, because diagnosing a miss re-runs the whole lane and roughly
;;; doubles the cost of a step.
(define (harvest--diagnose! entry)
  (let ((tac  (car entry))
        (name (let ((a (and (pair? (cdr entry)) (cadr entry))))
                (cond ((and (pair? a) (eq? (car a) 'quote) (pair? (cdr a))) (cadr a))
                      ((symbol? a) a)
                      (else #f)))))
    (when (and (eq? tac 'fact) name *ps* (not (proof-done? *ps*)))
      (let* ((sqn  (proof-state-focus *ps*))
             (goal (wff-formula (sequent-node-assertion sqn)))
             (asms (map wff-formula (sequent-node-assumptions sqn))))
        (harvest--miss!
         (call-with-current-continuation
          (lambda (bail)
            (bind-condition-handler (list condition-type:error)
              (lambda (c)
                ;; NAME the error.  `lane-error' as a bare tally says the panel
                ;; broke and nothing about where, which is the failure mode the
                ;; whole harvester exists to stop hiding.
                (bail (string->symbol
                       (string-append
                        "lane-error: "
                        (call-with-output-string
                         (lambda (port) (write-condition-report c port)))))))
              (lambda () (harvest--fact-miss-reason name goal asms)))))
         name)))))

(define (harvest--diagnose-one name)
  (let ((goal   (vnb-guard (lambda () (lookup-theorem name))))
        (script (hash-table-ref/default *proof-script-table* name '())))
    (if (not (and (pair? goal) (pair? script)))
        #f
        (call-with-current-continuation
         (lambda (bail)
           (bind-condition-handler (list condition-type:error)
             (lambda (c) (bail #f))
             (lambda ()
               (fluid-let ((*cite-exclude-script* name)    ; leave-one-out
                           (*fresh-counter*                ; see harvest--one
                            (hash-table-ref/default *proof-start-counter*
                                                    name *fresh-counter*)))
                 (quietly
                  (lambda ()
                    (sp (make-wff goal))
                    (for-each
                     (lambda (entry)
                       (harvest--diagnose! entry)
                       (fluid-let ((*replaying?* #t))
                         (apply-recorded-cmd! (car entry) (cdr entry))))
                     script))))
               #t)))))))

;;; Diagnose a NAMED set of scripts rather than the first N.  What the topic
;;; hold-out needs: build the index without a family, then measure on it.
(define (harvest-diagnose-names! names)
  (set! *harvest-miss-reasons* (make-equal-hash-table))
  (set! *harvest-miss-examples* (make-equal-hash-table))
  (set! *harvest-miss-ranks* '())
  (for-each harvest--diagnose-one names)
  (harvest--diagnose-report (length names)))

(define (harvest--diagnose-report nscripts)
  (newline)
  (display ";; ==== WHY `fact' CITATIONS ARE MISSED ====") (newline)
  (display ";; scripts attempted : ") (display nscripts) (newline)
  (let* ((rs (sort (hash-table->alist *harvest-miss-reasons*)
                   (lambda (a b) (> (cdr a) (cdr b)))))
         (tot (fold-left + 0 (map cdr rs))))
    (display ";; fact steps seen   : ") (display tot) (newline)
    (for-each
     (lambda (p)
       (display ";;   ") (display (car p))
       (display "  ") (display (cdr p))
       (display " (") (display (harvest--pct (cdr p) tot)) (display "%)")
       (display "   e.g. ")
       (display (hash-table-ref/default *harvest-miss-examples* (car p) '()))
       (newline))
     rs)
    (let ((rk (sort *harvest-miss-ranks* <)))
      (when (pair? rk)
        (display ";; RANK of the author's citation among the kept hits: n=")
        (display (length rk))
        (display "  min ") (display (car rk))
        (display "  median ") (display (list-ref rk (quotient (length rk) 2)))
        (display "  p75 ") (display (list-ref rk (quotient (* 3 (length rk)) 4)))
        (display "  max ") (display (car (last-pair rk)))
        (newline)
        (display ";;   within a cap of 5: ")
        (display (harvest--pct (length (filter (lambda (r) (<= r 5)) rk)) (length rk)))
        (display "%   10: ")
        (display (harvest--pct (length (filter (lambda (r) (<= r 10)) rk)) (length rk)))
        (display "%   25: ")
        (display (harvest--pct (length (filter (lambda (r) (<= r 25)) rk)) (length rk)))
        (display "%") (newline)))
    (list (cons 'total tot) (cons 'reasons rs)
          (cons 'ranks (sort *harvest-miss-ranks* <)))))

(define (harvest-diagnose! #!optional limit)
  (set! *harvest-miss-reasons* (make-equal-hash-table))
  (set! *harvest-miss-examples* (make-equal-hash-table))
  (set! *harvest-miss-ranks* '())
  (let* ((all   (sort (hash-table-keys *proof-script-table*)
                      (lambda (a b) (string<? (symbol->string a) (symbol->string b)))))
         (names (if (default-object? limit) all
                    (list-head all (min limit (length all))))))
    (for-each harvest--diagnose-one names)
    (harvest--diagnose-report (length names))))
