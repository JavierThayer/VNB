;;; counterexample.scm -- probes that try to REFUTE the focus goal.
;;;
;;; The user's notes-41 (2026-09-25), "Attempting to prove falsehoods": on the goal
;;;
;;;     forall([x in rr], x + x = x)
;;;
;;; he wants to choose x = 1 and watch the goal fail, so that a bad proof path is flagged
;;; before hours go into it.
;;;
;;; WHY THE CHOOSE MOVE CANNOT DO IT.  `choose' (witness-tactics.scm) cuts
;;; forsome([x in rr], x = 1) and skolemizes: the context gains a NEW eigenvariable x1 with
;;; x1 in rr and x1 = 1, and the goal's own x stays bound.  After (di) that x is an arbitrary
;;; eigenvariable which nothing equates to 1.  Instantiating a UNIVERSAL GOAL at a value is
;;; not an inference in either direction -- forall-intro needs an arbitrary x -- and a value
;;; can only REFUTE.  So this file is a PROBE: it computes, prints and returns.  It writes no
;;; inference, records no step, moves no focus and adds no trust.
;;;
;;;   (try-at t1 t2 ...)   substitute t1, t2, ... for the leading universally bound
;;;                        variables of the goal, guards included (forall x. x in RR => BODY
;;;                        becomes 1 in RR => BODY[1/x]), evaluate the instance with the
;;;                        ground evaluator `arith-eval-formula' (arith-eval.scm), and report
;;;                          REFUTED    the instance is decidably FALSE: the goal cannot be
;;;                                     proven unless the context is contradictory (an
;;;                                     inconsistent context proves anything);
;;;                          holds      decidably TRUE at these values: no evidence against;
;;;                          undecided  the evaluator cannot decide it (a free variable, a
;;;                                     predicate it does not know, ...).
;;;                        Value: the symbol refuted / holds / undecided.
;;;   (try-small)          try the values 0 1 2 -1 1/2 3 10 on the first bound variable and
;;;                        every pair of them on the first two; report the first refutation.
;;;                        Value: the binding list of the refutation, e.g. ((x 1)), or #f.
;;;
;;; The what-now lane `counterexample' (suggest.scm, right after the reader's own rules,
;;; since a dead path outranks any advice) runs `try-small' silently and, on a refutation,
;;; prints it and offers the (try-at ...) form that reproduces it.  It is silent otherwise:
;;; "holds at 0, 1, 2" is not evidence and is not said.
;;;
;;; Loaded at the root beside witness-tactics (before suggest.scm, which calls the lane).

(define *counterexample-values* '(0 1 2 -1 1/2 3 10))

;;; The leading universally bound variables of a raw formula, GUARDS INCLUDED: a goal written
;;; forall([x in rr], forall([y in rr], B)) is (FORALL x (IMPLIES (IN x RR) (FORALL y (IMPLIES (IN y
;;; RR) B)))), so the walk steps through a guard (IMPLIES (IN v C) rest) on the variable just
;;; peeled and goes on into rest.  Nothing is peeled past any other head.
(define (cx--guard-of? f v)
  (and (pair? f) (eq? (car f) 'IMPLIES) (pair? (cdr f)) (pair? (cddr f))
       (let ((g (cadr f)))
         (and (pair? g) (eq? (car g) 'IN) (pair? (cdr g)) (eq? (cadr g) v)))))

(define (cx--count-vars f)
  (if (and (pair? f) (eq? (car f) 'FORALL) (pair? (cdr f)) (pair? (cddr f)) (symbol? (cadr f)))
      (let ((v (cadr f)) (b (caddr f)))
        (+ 1 (cx--count-vars (if (cx--guard-of? b v) (caddr b) b))))
      0))

;;; The instance: the first (length terms) bound variables replaced, guards kept in place, the
;;; rest left bound.  Returns (bindings . formula).
(define (cx--instance f terms)
  (let ((nvars (cx--count-vars f)))
    (if (> (length terms) nvars)
        (error "try-at: more values than leading universal variables in the goal"
               (length terms) nvars)))
  (let strip ((f f) (ts terms) (bound '()))
    (cond
      ((null? ts) (cons (reverse bound) f))
      (else
       (let* ((v  (cadr f))
              (t  (car ts))
              (b* (subst-free v t (caddr f))))
         (if (cx--guard-of? b* t)           ; the guard now reads (IN t C): keep it, go on under it
             (let ((r (strip (caddr b*) (cdr ts) (cons (list v t) bound))))
               (cons (car r) (list 'IMPLIES (cadr b*) (cdr r))))
             (strip b* (cdr ts) (cons (list v t) bound))))))))

(define (cx--goal)
  (if (not *ps*) (error "try-at: no proof in progress"))
  (wff-formula (sequent-node-assertion (proof-state-focus *ps*))))

(define (cx--context-empty?)
  (null? (sequent-node-assumptions (proof-state-focus *ps*))))

(define (cx--bindings-string bindings)
  (let loop ((bs bindings) (acc '()))
    (if (null? bs)
        (apply string-append (reverse acc))
        (loop (cdr bs)
              (cons (string-append (if (null? acc) "" ", ")
                                   (symbol->string (caar bs)) " = "
                                   (expression->string (cadar bs)))
                    acc)))))

;;; Evaluate the goal at the given values; print and return the verdict.
(define (try-at . terms)
  (if (null? terms) (error "try-at: give at least one value"))
  (let* ((goal     (cx--goal))
         (inst     (cx--instance goal terms))
         (bindings (car inst))
         (formula  (cdr inst))
         (verdict  (arith-eval-formula formula))
         (at       (cx--bindings-string bindings)))
    (cond
      ((eq? verdict #f)
       (display ";; REFUTED at ") (display at) (display ": the goal reads") (newline)
       (display ";;   ") (display (expression->string formula)) (newline)
       (display ";; which is FALSE.  This goal cannot be proven")
       (if (cx--context-empty?)
           (display ": the context is empty.")
           (display " unless the context is contradictory."))
       (newline)
       (display ";; No inference was made; the proof is unchanged.") (newline)
       'refuted)
      ((eq? verdict #t)
       (display ";; holds at ") (display at)
       (display " (a true instance is no evidence for the goal).") (newline)
       'holds)
      (else
       (display ";; undecided at ") (display at) (display ": the ground evaluator cannot decide")
       (newline)
       (display ";;   ") (display (expression->string formula)) (newline)
       'undecided))))

;;; Silent search over the small values; the binding list of the first refutation, or #f.
(define (cx--search goal)
  (let ((nvars (cx--count-vars goal)))
    (cond
      ((= nvars 0) #f)
      (else
       (let ((singles
              (let loop ((vs *counterexample-values*))
                (cond ((null? vs) #f)
                      ((eq? (arith-eval-formula (cdr (cx--instance goal (list (car vs))))) #f)
                       (car (cx--instance goal (list (car vs)))))
                      (else (loop (cdr vs)))))))
         (or singles
             (and (>= nvars 2)
                  (let outer ((us *counterexample-values*))
                    (cond ((null? us) #f)
                          (else
                           (or (let inner ((vs *counterexample-values*))
                                 (cond ((null? vs) #f)
                                       ((eq? (arith-eval-formula
                                              (cdr (cx--instance goal (list (car us) (car vs)))))
                                             #f)
                                        (car (cx--instance goal (list (car us) (car vs)))))
                                       (else (inner (cdr vs)))))
                               (outer (cdr us)))))))))))))

(define (try-small)
  (let ((found (cx--search (cx--goal))))
    (if found
        (begin (apply try-at (map cadr found)) found)
        (begin
          (display ";; no refutation among the values ")
          (display *counterexample-values*)
          (display " (which proves nothing).") (newline)
          #f))))

;;; The what-now lane.  Returns the move forms it offers: the reproducing (try-at ...) on a
;;; refutation, nothing otherwise.  Prints only on a refutation.
(define (what-now--show-counterexample goal)
  (let ((found (and *ps* (pair? goal) (eq? (car goal) 'FORALL)
                    (cx--search goal))))
    (if (not found)
        '()
        (let ((form (cons 'try-at (map cadr found))))
          (display ";; COUNTEREXAMPLE at ") (display (cx--bindings-string found))
          (display ": the goal reads") (newline)
          (display ";;   ")
          (display (expression->string (cdr (cx--instance goal (map cadr found)))))
          (newline)
          (display ";; which is FALSE -- this path is dead")
          (if (cx--context-empty?) (display " (the context is empty)")
              (display " unless the context is contradictory"))
          (display ".  Reproduce with:") (newline)
          (display ";;   ") (vnb--write-form form) (newline)
          (list form)))))
