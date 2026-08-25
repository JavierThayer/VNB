;;; rr-max-basics.scm -- the usable facts about MAX on RR, PROVEN from its
;;; defining equation.
;;;
;;;   rr-max-closed     max(x,y) in RR
;;;   rr-max-cases      max(x,y) = x  or  max(x,y) = y
;;;   rr-le-max-left    x <= max(x,y)
;;;   rr-le-max-right   y <= max(x,y)
;;;   rr-max-le         x <= z and y <= z  =>  max(x,y) <= z
;;;
;;; WHY THESE ARE PROVEN AND NOT ASSERTED.  `MAX' is introduced in
;;; number-systems.scm by ONE equation, `rr-max-def', by cases on `y <= x'.
;;; Everything above follows, and stating any of it as an axiom instead would
;;; repeat the mistake the note beside `rr-abs-def' records: five norm-shaped
;;; facts about `abs' stood there as axioms until 2026-08-17, and because the
;;; DEFINITION was missing, `x <= |x|' was independent of the theory -- true in
;;; the intended model and underivable.  "They were not wrong; they were
;;; incomplete."  So the definition goes in the base and the properties are
;;; earned here.
;;;
;;; THE PROOF IS EXCLUDED MIDDLE ON THE GUARD.  `rr-max-def' splits on `y <= x',
;;; so `use-em' on that very proposition hands back exactly the two branches the
;;; definition has, and in each branch one `detach!' turns the matching
;;; implication into the equation.
;;;
;;; ONE STEP NEEDS MORE THAN THAT, and I first claimed it did not.  In the
;;; NOT-branch of `rr-le-max-left' the goal is `x <= y' from `not(y <= x)' --
;;; which is order TOTALITY, and `ineq' does not supply it: Fourier-Motzkin
;;; will not negate a `<=' premise, and the call fails with "goal not a
;;; linear-RR consequence".  `rr-le-total' is PROVEN in rr-order-basics.scm
;;; (from rr-lt-trichotomy); here it is one citation and a `prop', the step
;;; being disjunctive syllogism with both relations opaque.
;;;
;;; The guard is `<=' and not `<', so the two cases OVERLAP at x = y -- both
;;; give x, so the definition is still single-valued, and the first branch
;;; covers equality, which is the branch `use-em' hands you first.
;;;
;;; WHAT IT COSTS.  Nothing: `modulo 0'.
;;;
;;; Loads after number-systems (rr-max-def) and rr-order-basics; needs `prop'
;;; (prop.scm) for the disjunctive goal and `ineq' for the two order steps.

;;; ---- file-local driver helpers (the `mx-' prefix) --------------------

(define (mx-peel!)
  (let loop ((n 0))
    (let ((g (dk-goal)))
      (if (and (pair? g) (memq (car g) '(FORALL IMPLIES)) (< n 12))
          (begin (di) (loop (+ n 1))) #t))))

(define (mx-split!)
  (let loop ((l (dk-asms)) (n 0))
    (cond ((or (null? l) (> n 14)) #t)
          ((and (pair? (car l)) (eq? (caar l) 'AND)) (ai (car l)) (loop (dk-asms) (+ n 1)))
          (else (loop (cdr l) n)))))

(define (mx-idx form)
  (let loop ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "mx-idx: not in context" form))
          ((equal? (car l) form) i)
          (else (loop (cdr l) (+ i 1))))))

(define (mx-ineq . forms) (apply ineq (map mx-idx forms)))

;;; Land both branches of the definition at x, y as separate implications.
(define (mx-def! x y)
  (fact 'rr-max-def x y)
  (mx-split!))

;;; The two cases of the definition, as `use-em' on its own guard.  P-BRANCH
;;; first (y <= x, so max = x), then the NOT-P branch (max = y).
(define (mx-cases! x y p-closer notp-closer)
  (use-em (list '<= y x)
    (lambda ()
      (detach! (list 'IMPLIES (list '<= y x) (list '= (list 'max x y) x)))
      (subst (list '= (list 'max x y) x))
      (p-closer))
    (lambda ()
      (detach! (list 'IMPLIES (list 'NOT (list '<= y x)) (list '= (list 'max x y) y)))
      (subst (list '= (list 'max x y) y))
      (notp-closer))))

;;; =====================================================================
;;; (1) max is real.
;;; =====================================================================
(sp (make-wff-from-string "forall([x in rr, y in rr], max(x,y) in rr)"))
(mx-peel!)
(mx-def! 'x 'y)
(mx-cases! 'x 'y (lambda () (ass)) (lambda () (ass)))
(qed 'rr-max-closed)
(topic! 'rr-max-closed 'inequalities)

;;; =====================================================================
;;; (2) max is one of its arguments.  The disjunction is decided by `prop':
;;; the equation is in context and the goal is a disjunct of it, atoms opaque.
;;; =====================================================================
(sp (make-wff-from-string
     "forall([x in rr, y in rr], max(x,y) = x or max(x,y) = y)"))
(mx-peel!)
(mx-def! 'x 'y)
(use-em '(<= y x)
  (lambda ()
    (detach! '(IMPLIES (<= y x) (= (max x y) x)))
    (prop))
  (lambda ()
    (detach! '(IMPLIES (NOT (<= y x)) (= (max x y) y)))
    (prop)))
(qed 'rr-max-cases)
(topic! 'rr-max-cases 'inequalities)
(alias! 'rr-max-cases "the maximum is one of the two arguments")

;;; =====================================================================
;;; (3) and (4): max bounds each argument.
;;;
;;; The NOT-branch of (3) is the one place an order step is taken: from
;;; not(y <= x) the goal x <= y is linear, so `ineq' decides it off that
;;; premise and the two typings.
;;; =====================================================================
(sp (make-wff-from-string "forall([x in rr, y in rr], x <= max(x,y))"))
(mx-peel!)
(mx-def! 'x 'y)
(mx-cases! 'x 'y
  (lambda () (mx-ineq '(IN x RR)))
  ;; not(y <= x) |- x <= y is disjunctive syllogism against `rr-le-total',
  ;; and `prop' decides it with both relations opaque.  `ineq' cannot: it will
  ;; not negate a `<=' premise.
  (lambda () (fact 'rr-le-total 'x 'y) (prop)))
(qed 'rr-le-max-left)
(topic! 'rr-le-max-left 'inequalities)

(sp (make-wff-from-string "forall([x in rr, y in rr], y <= max(x,y))"))
(mx-peel!)
(mx-def! 'x 'y)
(mx-cases! 'x 'y
  (lambda () (mx-ineq '(<= y x) '(IN x RR) '(IN y RR)))
  (lambda () (mx-ineq '(IN y RR))))
(qed 'rr-le-max-right)
(topic! 'rr-le-max-right 'inequalities)

;;; =====================================================================
;;; (5) the universal property: max is the LEAST common upper bound of the two.
;;; Both branches close by `ass' -- whichever argument max turned out to be,
;;; its bound is a hypothesis.
;;; =====================================================================
(sp (make-wff-from-string
     "forall([x in rr, y in rr, z in rr], x <= z implies y <= z implies max(x,y) <= z)"))
(mx-peel!)
(mx-def! 'x 'y)
(mx-cases! 'x 'y (lambda () (ass)) (lambda () (ass)))
(qed 'rr-max-le)
(topic! 'rr-max-le 'inequalities)
(alias! 'rr-max-le "the maximum is the least common upper bound")
