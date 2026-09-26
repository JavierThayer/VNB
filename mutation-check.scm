;;; mutation-check.scm -- IS THE MUST-NOT-PROVE CORPUS ACTUALLY DETECTING ANYTHING?
;;;
;;; test-suite-negative.scm asserts that a list of false statements stays
;;; unproven.  Every way of failing to prove something looks identical from
;;; outside such a test: a sound refusal, a misspelled goal, a tactic that
;;; errored inside `quietly', an attack aimed at the wrong leaf and an attack
;;; too weak to close anything all print the same PASS.  So a green corpus is
;;; not evidence on its own, and this file is what makes it evidence.
;;;
;;; THE METHOD is mutation testing (DeMillo, Lipton and Sayward, 1978): inject
;;; into the PROVER, on purpose, exactly the fault a given entry claims to
;;; detect, and require that same entry to go red.  A mutant that no entry
;;; detects is a mutant the corpus is blind to, whatever the entry's label says.
;;; The program under test here is the CORPUS; each mutant is a known-bad
;;; prover, supplied as the positive control an instrument needs before its
;;; readings mean anything.
;;;
;;; TWO WORDS, used throughout and worth pinning down:
;;;
;;;   ENTRY -- one check in test-suite-negative.scm: a false statement, a script
;;;     that attacks it, and the assertion that the proof state stays open.  A
;;;     mutant is not an entry; it is the damage an entry is asked to notice.
;;;
;;;   GUARD -- a side condition in the CHECKER'S OWN CODE that must hold before a
;;;     step is allowed.  Three examples, which are the ones the mutants below
;;;     delete.  `pi-lambda-type!' and `pi-reflexivity!' are KERNEL RULES: two of
;;;     the 50 `pi-*' procedures in primitive-inferences.scm, which are the only
;;;     things in VNB that may post an inference (a tactic can ask a rule to
;;;     fire; it cannot conclude anything itself).  Inside `pi-lambda-type!',
;;;     (i) the `alpha-equiv?' test that the term's declared domain is the one
;;;     membership in the FUN class requires,
;;;     and (ii) the `(IN A SET)' subgoal it emits -- a guard need not be a test
;;;     that passes or fails; an obligation the rule hands back is one too.
;;;     Inside `pi-reflexivity!', (iii) the `term-self-defined?' test.
;;;
;;;     NOT VNB's other sense of the word -- the restricting hypothesis
;;;     `(IN x A)' on a binder, as in `minimize!'s GUARD argument.  Same spelling,
;;;     unrelated notion; nothing in this file means the logical one.
;;;
;;; Each mutant below is the UN-REPAIR of a specific fix, and carries the
;;; PREDICTION that came with it: this guard is what that entry watches, so
;;; deleting the guard must turn that entry, and nothing else, red.  The
;;; prediction is machine-checked, which is the whole difference between this
;;; file and the record it replaces:
;;;
;;;   * a predicted entry that stays GREEN is a FAILURE -- the corpus does not
;;;     detect the fault it is named after.  That is not hypothetical: on
;;;     2026-08-06 `no-domain-match' reddened nothing, twice over, and both
;;;     causes were defects in the corpus (it attacked only the focus leaf,
;;;     then its attacker could not prove even `(IN EMPTY-SET SET)').
;;;   * an UNPREDICTED red is reported and is not a failure.  It is information:
;;;     `credulous-arith' also reddens `pred(0) = pred(0)', because a credulous
;;;     `arith' closes a reflexivity goal about an undefined term.  That entry
;;;     is guarded twice over, which is worth knowing and not worth failing on.
;;;
;;; RUNNING IT.  `./mutation-check' runs the baseline and all five mutants and
;;; prints the table.  One configuration per process, selected by the
;;; environment variable MNP_MUT (default "baseline"), because a mutation is a
;;; global `set!' and a fresh image is the only way to be sure the previous one
;;; left nothing behind.  A run costs 0.16 s against the band, so six of them
;;; cost a second; there is no reason to be clever.
;;;
;;;     MNP_MUT=no-sethood ./prover -b mutation-check.scm
;;;
;;; It runs against the BAND, which is a snapshot: rebuild it (`./prover
;;; --build-band') after any change to the tree, or the mutants are applied to
;;; a stale library and the table is about a prover that no longer exists.
;;;
;;; NOT LOADED BY load.scm, and must not be: it rebinds `check' and friends at
;;; top level, and it is a tool, not a component.
;;;
;;; THE DECAY THIS FILE CANNOT PREVENT.  `no-sethood' and `no-domain-match' work
;;; by installing a COPY of `pi-lambda-type!' with one piece removed.  A copy
;;; rots the moment the original is edited, and a rotted mutant may still redden
;;; its entry while testing something else entirely.  So both check the real
;;; defining form against a recorded hash and say so when it moves; re-author
;;; the mutant, then re-record.  There is no way to express "delete this
;;; internal subgoal" without a copy, short of putting a hook in the kernel,
;;; which would be a soundness surface added for a test's convenience.

;;; -----------------------------------------------------------------------
;;; Recording harness.  test-suite-negative.scm calls check / check-false /
;;; check-proof, which test-suite.scm supplies and which print.  Here they
;;; RECORD, because the verdict is a set comparison over labels, not a count.
;;; -----------------------------------------------------------------------

(define *mc-results* '())               ; reversed ((label . pass?) ...)

(define (mc-record! label pass?)
  (set! *mc-results* (cons (cons label pass?) *mc-results*)))

(define (mc-results) (reverse *mc-results*))

(define (check label thunk expected)
  (mc-record! label (equal? (thunk) expected)))

(define (check-true  label thunk) (check label thunk #t))
(define (check-false label thunk) (check label thunk #f))
(define (check-error label thunk) (mc-record! label (vnb-error? (thunk))))

(define (check-proof label thunk)
  (mc-record! label
    (call-with-current-continuation
      (lambda (k)
        (with-exception-handler (lambda (e) (k #f))
          (lambda () (thunk) #t))))))

;;; -----------------------------------------------------------------------
;;; Source-drift guard for the mutants that copy a procedure.
;;;
;;; Compares the CODE of the defining form, read as data, so reformatting and
;;; comment edits do not trip it and a semantic edit does.
;;; -----------------------------------------------------------------------

(define (mc-defining-form file name)
  (call-with-input-file file
    (lambda (port)
      (let loop ()
        (let ((d (read port)))
          (cond ((eof-object? d) #f)
                ((and (pair? d) (eq? (car d) 'define)
                      (pair? (cadr d)) (eq? (car (cadr d)) name))
                 d)
                (else (loop))))))))

;;; Recorded 2026-08-06 against primitive-inferences.scm:1327.
(define *mc-pi-lambda-type-hash* 1953352202)

(define (mc-drift-warn! name file recorded)
  (let ((form (mc-defining-form file name)))
    (cond ((not form)
           (display "DRIFT  ") (display name)
           (display " -- no defining form found in ") (display file) (newline)
           #f)
          ((not (= (string-hash (write-to-string form)) recorded))
           (display "DRIFT  ") (display name) (display " has been edited since ")
           (display "this mutant was authored: recorded hash ") (display recorded)
           (display ", now ") (display (string-hash (write-to-string form)))
           (newline)
           (display "       The mutant is a COPY and may no longer differ from ")
           (display "the original in only the intended way.") (newline)
           (display "       Re-author it, then record the new hash in ")
           (display "*mc-pi-lambda-type-hash*.") (newline)
           #f)
          (else #t))))

;;; -----------------------------------------------------------------------
;;; The mutants.
;;; -----------------------------------------------------------------------

(define (make-mutant name doc install! predicted-keys drift-check)
  (list name doc install! predicted-keys drift-check))
(define (mutant-name m)      (list-ref m 0))
(define (mutant-doc m)       (list-ref m 1))
(define (mutant-install! m)  (list-ref m 2))
(define (mutant-keys m)      (list-ref m 3))
(define (mutant-drift m)     (list-ref m 4))

(define (mc-check-pi-lambda-type-drift)
  (mc-drift-warn! 'pi-lambda-type!
                  (string-append *prover-dir* "primitive-inferences.scm")
                  *mc-pi-lambda-type-hash*))

;;; M1 and M2 share everything but the two pieces they delete, so they are one
;;; copy parameterised on which piece goes.  Keep this body in step with
;;; primitive-inferences.scm:1327; the drift guard above says when it is not.
(define (mc-lambda-type-mutant keep-sethood? keep-domain-match?)
  (lambda (sqn)
    (let* ((asms (sequent-node-assumptions sqn))
           (goal (sequent-node-assertion   sqn))
           (g    (wff-formula goal))
           (dg   (sqn-dg sqn)))
      (and (pair? g) (eq? (car g) 'IN)
           (let ((subj (cadr g)) (cls (caddr g)))
             (and (pair? subj) (eq? (car subj) 'VNB-LAMBDA) (= (length subj) 4)
                  (symbol? (cadr subj))
                  (pair? cls) (eq? (car cls) 'FUN) (= (length cls) 3)
                  (or (not keep-domain-match?)
                      (alpha-equiv? (caddr subj) (cadr cls)))
                  (let* ((x    (cadr subj))
                         (A    (cadr cls))
                         (body (cadddr subj))
                         (B    (caddr cls))
                         (avoids (cons body (cons A (cons B (map wff-formula asms)))))
                         (x*   (apply fresh-var x avoids))
                         (body*(subst-free x x* body))
                         (sub-goal `(FORALL ,x* (IMPLIES (IN ,x* ,A) (IN ,body* ,B))))
                         (set-goal `(IN ,A SET)))
                    (dg-apply-rule! dg 'lambda-type
                      (if keep-sethood?
                          (list (make-sequent asms (wff-child goal sub-goal))
                                (make-sequent asms (wff-child goal set-goal)))
                          (list (make-sequent asms (wff-child goal sub-goal))))
                      sqn))))))))

(define *mc-mutants*
  (list

   (make-mutant "no-sethood"
     "pi-lambda-type! stops emitting the (IN A SET) subgoal -- one of the two it
      normally hands back -- so nothing ever demands that the domain be a set and
      a lambda over the proper class ORD types into FUN(ORD, ORD)."
     ;; install the damage: (keep-sethood? keep-domain-match?)
     (lambda () (set! pi-lambda-type! (mc-lambda-type-mutant #f #t)))
     ;; the prediction: substrings naming the entry that must go red
     '("FUN(ORD, ORD)")
     mc-check-pi-lambda-type-drift)

   (make-mutant "no-domain-match"
     "pi-lambda-type! stops checking the term's declared domain.  Membership in
      FUN(A,B) REQUIRES domain exactly A -- FUN is total functions -- and a VNB
      lambda declares its domain syntactically, so the rule can check that before
      doing anything else: (VNB-LAMBDA x X body) in FUN(A,B) needs X = A.  With
      the check gone the declared X plays NO part in the derivation: the rule
      builds its subgoal from A, so it verifies only that the BODY carries A into
      B, and never looks at the domain the term actually has.  So
      (VNB-LAMBDA x NN x) -- the identity on NN and on nothing else -- certifies
      into FUN(EMPTY-SET, EMPTY-SET), where the subgoal is vacuous."
     ;; install the damage: (keep-sethood? keep-domain-match?)
     (lambda () (set! pi-lambda-type! (mc-lambda-type-mutant #t #f)))
     ;; the prediction: substrings naming the entry that must go red
     '("FUN(EMPTY-SET, EMPTY-SET)")
     mc-check-pi-lambda-type-drift)

   (make-mutant "no-definedness"
     "pi-reflexivity! stops asking whether the term is defined, so t = t closes
      for a t that denotes nothing."
     (lambda () (set! term-self-defined? (lambda (t) #t)))
     '("pred is undefined at 0" "reciprocal is undefined at 0")
     (lambda () #t))

   (make-mutant "credulous-arith"
     "the arith oracle answers TRUE to every sentence it can decide at all."
     (lambda ()
       (let ((old arith-eval-formula))
         (set! arith-eval-formula
           (lambda (e) (let ((r (old e))) (if (eq? r 'UNDEF) 'UNDEF #t))))))
     '("must NOT prove: 0 = 1" "2 + 2 = 5" "pred is undefined at 0")
     (lambda () #t))

   (make-mutant "credulous-ineq"
     "Fourier-Motzkin reports an infeasibility for every query, so ineq closes
      any goal it is willing to linearise."
     (lambda () (set! fm-prove (lambda (hyps gcoeffs gconst grel) '(BOGUS))))
     '("b < a")
     (lambda () #t))))

(define (mc-find-mutant name)
  (let loop ((ms *mc-mutants*))
    (cond ((null? ms) #f)
          ((string=? (mutant-name (car ms)) name) (car ms))
          (else (loop (cdr ms))))))

;;; -----------------------------------------------------------------------
;;; Resolving a prediction key to an entry.
;;;
;;; The keys are substrings, so that a typo fix in a label does not silently
;;; void a row.  What WOULD silently void a row is a key that now matches no
;;; entry (the entry was renamed or removed) or two (the corpus grew a
;;; look-alike), so both are hard errors rather than warnings.
;;; -----------------------------------------------------------------------

(define (mc-labels-matching key results)
  (let loop ((rs results) (acc '()))
    (cond ((null? rs) (reverse acc))
          ((string-search-forward key (caar rs) 0) (loop (cdr rs) (cons (caar rs) acc)))
          (else (loop (cdr rs) acc)))))

(define (mc-resolve-key key results)      ; -> label | 'none | 'ambiguous
  (let ((hits (mc-labels-matching key results)))
    (cond ((null? hits) 'none)
          ((null? (cdr hits)) (car hits))
          (else 'ambiguous))))

;;; -----------------------------------------------------------------------
;;; Run.
;;; -----------------------------------------------------------------------

(define (mc-failed results)
  (let loop ((rs results) (acc '()))
    (cond ((null? rs) (reverse acc))
          ((cdr (car rs)) (loop (cdr rs) acc))
          (else (loop (cdr rs) (cons (caar rs) acc))))))

(define (mc-member? x lst)
  (cond ((null? lst) #f)
        ((equal? x (car lst)) #t)
        (else (mc-member? x (cdr lst)))))

(define (mc-say tag text)
  (display tag) (display "  ") (display text) (newline))

(define (mc-run-baseline results)
  (let ((failed (mc-failed results)))
    (display "MUTANT   baseline (no mutation)") (newline)
    (display "ENTRIES  ") (display (length results)) (newline)
    (for-each (lambda (l) (mc-say "RED     " l)) failed)
    (if (null? failed)
        (begin (mc-say "VERDICT" "ok -- every entry green, so the mutants below mean something")
               0)
        (begin (mc-say "VERDICT" "FAILED -- the corpus is not green to begin with; nothing below is interpretable")
               1))))

;;; Set by the drift guard before the mutant is installed.  A drifted copy is
;;; FATAL, not a warning: it may still redden its entry while no longer being
;;; the fault the row is named after, and a warning nobody acts on is exactly
;;; the decay this file exists to prevent.
(define *mc-drift-ok?* #t)

(define (mc-run-mutant m results)
  (let* ((failed (mc-failed results))
         (bad (if *mc-drift-ok?* 0 1))
         (predicted '()))
    (display "MUTANT   ") (display (mutant-name m)) (newline)
    (display "ENTRIES  ") (display (length results)) (newline)
    ;; resolve every key, then judge it
    (for-each
      (lambda (key)
        (let ((label (mc-resolve-key key results)))
          (cond ((eq? label 'none)
                 (set! bad (+ bad 1))
                 (mc-say "KEYERROR" (string-append
                   "no entry's label contains \"" key
                   "\" -- the corpus changed under this prediction")))
                ((eq? label 'ambiguous)
                 (set! bad (+ bad 1))
                 (mc-say "KEYERROR" (string-append
                   "\"" key "\" matches more than one entry -- the prediction is not specific")))
                (else
                 (set! predicted (cons label predicted))
                 (if (mc-member? label failed)
                     (mc-say "KILLED  " label)
                     (begin (set! bad (+ bad 1))
                            (mc-say "SURVIVED" label)))))))
      (mutant-keys m))
    ;; reds nobody predicted: information, not failure
    (for-each (lambda (l)
                (if (not (mc-member? l predicted))
                    (mc-say "EXTRA-RED" l)))
              failed)
    (if (= bad 0)
        (begin (mc-say "VERDICT" "ok -- the corpus detects this fault") 0)
        (begin (mc-say "VERDICT" "FAILED -- see DRIFT/SURVIVED/KEYERROR above") 1))))

(define (mc-main)
  (let* ((name (or (get-environment-variable "MNP_MUT") "baseline"))
         (m    (and (not (string=? name "baseline")) (mc-find-mutant name))))
    (cond
     ((and (not (string=? name "baseline")) (not m))
      (display "mutation-check: no such mutant: ") (display name) (newline)
      (display "known: ")
      (for-each (lambda (x) (display (mutant-name x)) (display " ")) *mc-mutants*)
      (newline)
      2)
     (else
      (newline)
      (if m
          (begin (set! *mc-drift-ok?* ((mutant-drift m)))
                 ((mutant-install! m))))
      (load (string-append *prover-dir* "test-suite-negative.scm"))
      (newline)
      (let ((results (mc-results)))
        (if m (mc-run-mutant m results) (mc-run-baseline results)))))))

(exit (mc-main))
