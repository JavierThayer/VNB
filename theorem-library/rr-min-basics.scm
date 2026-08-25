;;; rr-min-basics.scm -- the usable facts about MIN on RR, PROVEN from its
;;; defining equation, and the NN closure of both MIN and MAX.
;;;
;;;   rr-min-closed     min(x,y) in RR
;;;   rr-min-cases      min(x,y) = x  or  min(x,y) = y
;;;   rr-min-le-left    min(x,y) <= x
;;;   rr-min-le-right   min(x,y) <= y
;;;   rr-le-min         z <= x and z <= y  =>  z <= min(x,y)
;;;   nn-max-closed     x, y in NN  =>  max(x,y) in NN
;;;   nn-min-closed     x, y in NN  =>  min(x,y) in NN
;;;   rr-min-one-subadditive   0 <= a, 0 <= b  =>
;;;                     min(1,a+b) <= min(1,a) + min(1,b)
;;;
;;; THE MIRROR OF rr-max-basics.scm, deliberately and line for line: same
;;; helpers under an `mn-' prefix, same `use-em' on the definition's own guard,
;;; same closers.  Two operators whose proofs look different would be two
;;; operators a reader has to learn twice.
;;;
;;; WHY MIN WAS MISSING.  `*ineq-supply-wanted*' (ineq-supply.scm) carried it as
;;; the one gap in the oracle-supply table: "no min bounds in the tree:
;;; rr-min-closed / rr-min-le-left / rr-min-le-right do not exist, and `min' has
;;; no registered head".  The tree's habit was to state a minimum
;;; EXISTENTIALLY -- `rr-min-pos' gives a positive lower bound of two positives
;;; rather than naming MIN(a,b) -- which is right when a proof needs only the
;;; bounding property and wrong when the minimum is a TERM the statement is
;;; about, as in every "take delta = min(delta_1, delta_2)" step in the metric
;;; work.  MAX was given a real operator on 2026-08-19 for exactly that reason;
;;; this is the other half.
;;;
;;; WHY NN GETS NO OPERATOR OF ITS OWN, and this was the decision to make.  The
;;; obvious move is a second head, NN-MAX(a,b) = IF (<= a b) b a, with its own
;;; three lemmas.  It is the wrong move: NN is a subset of RR and `<=' is the
;;; SAME relation on it (nn-in-rr, proven), so `max' and `min' restricted to NN
;;; already take the right values and all that is owed is that they stay inside
;;; NN.  That is one theorem each, below, and it is a THEOREM and not an axiom.
;;; A second head would mean two operators, two sets of laws, two entries in
;;; every table that knows about maxima, and a rewrite whenever a proof crosses
;;; between NN and RR -- the per-system proliferation the project has a standing
;;; rule against ([[no-closure-axiom-proliferation]]: closure facts belong to
;;; PRIMITIVE operations; a derived one gets a definitional reduction instead).
;;; The same argument settles ZZ and QQ if they are ever wanted: one more
;;; six-line proof each, no new vocabulary.
;;;
;;; The NN proofs need nothing about the ORDER of NN -- no induction, no
;;; least-element, no NN-specific order lemma.  `rr-max-cases' says the value IS
;;; one of the two arguments, and both arguments are in NN by hypothesis.  That
;;; is why they are here, beside the operator, rather than in nn-order-basics.
;;;
;;; WHAT IT COSTS.  Nothing: every result below is `modulo 0'.
;;;
;;; Loads after number-systems (rr-min-def), rr-order-basics (rr-le-total),
;;; nn-order-basics (nn-in-rr) and rr-max-basics (rr-max-cases); needs `prop'
;;; for the two disjunctive steps and `ineq' for the order steps.

;;; ---- file-local driver helpers (the `mn-' prefix) --------------------

(define (mn-peel!)
  (let loop ((n 0))
    (let ((g (dk-goal)))
      (if (and (pair? g) (memq (car g) '(FORALL IMPLIES)) (< n 12))
          (begin (di) (loop (+ n 1))) #t))))

(define (mn-split!)
  (let loop ((l (dk-asms)) (n 0))
    (cond ((or (null? l) (> n 14)) #t)
          ((and (pair? (car l)) (eq? (caar l) 'AND)) (ai (car l)) (loop (dk-asms) (+ n 1)))
          (else (loop (cdr l) n)))))

(define (mn-idx form)
  (let loop ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "mn-idx: not in context" form))
          ((equal? (car l) form) i)
          (else (loop (cdr l) (+ i 1))))))

(define (mn-ineq . forms) (apply ineq (map mn-idx forms)))

;;; Land both branches of the definition at x, y as separate implications.
(define (mn-def! x y)
  (fact 'rr-min-def x y)
  (mn-split!))

;;; The two cases of the definition, as `use-em' on its own guard.  P-BRANCH
;;; first (x <= y, so min = x), then the NOT-P branch (min = y).
(define (mn-cases! x y p-closer notp-closer)
  (use-em (list '<= x y)
    (lambda ()
      (detach! (list 'IMPLIES (list '<= x y) (list '= (list 'min x y) x)))
      (subst (list '= (list 'min x y) x))
      (p-closer))
    (lambda ()
      (detach! (list 'IMPLIES (list 'NOT (list '<= x y)) (list '= (list 'min x y) y)))
      (subst (list '= (list 'min x y) y))
      (notp-closer))))

;;; =====================================================================
;;; (1) min is real.
;;; =====================================================================
(sp (make-wff-from-string "forall([x in rr, y in rr], min(x,y) in rr)"))
(mn-peel!)
(mn-def! 'x 'y)
(mn-cases! 'x 'y (lambda () (ass)) (lambda () (ass)))
(qed 'rr-min-closed)
(topic! 'rr-min-closed 'inequalities)

;;; =====================================================================
;;; (2) min is one of its arguments.
;;; =====================================================================
(sp (make-wff-from-string
     "forall([x in rr, y in rr], min(x,y) = x or min(x,y) = y)"))
(mn-peel!)
(mn-def! 'x 'y)
(use-em '(<= x y)
  (lambda ()
    (detach! '(IMPLIES (<= x y) (= (min x y) x)))
    (prop))
  (lambda ()
    (detach! '(IMPLIES (NOT (<= x y)) (= (min x y) y)))
    (prop)))
(qed 'rr-min-cases)
(topic! 'rr-min-cases 'inequalities)
(alias! 'rr-min-cases "the minimum is one of the two arguments")

;;; =====================================================================
;;; (3) and (4): min is bounded by each argument.
;;;
;;; The NOT-branch of (4) is the mirror of rr-le-max-left's: from not(x <= y)
;;; the goal y <= x is order TOTALITY, which `ineq' does not supply -- it will
;;; not negate a `<=' premise -- so it is `rr-le-total' plus a `prop', the step
;;; being disjunctive syllogism with both relations opaque.
;;; =====================================================================
(sp (make-wff-from-string "forall([x in rr, y in rr], min(x,y) <= x)"))
(mn-peel!)
(mn-def! 'x 'y)
(mn-cases! 'x 'y
  (lambda () (mn-ineq '(IN x RR)))
  (lambda () (fact 'rr-le-total 'x 'y) (prop)))
(qed 'rr-min-le-left)
(topic! 'rr-min-le-left 'inequalities)

(sp (make-wff-from-string "forall([x in rr, y in rr], min(x,y) <= y)"))
(mn-peel!)
(mn-def! 'x 'y)
(mn-cases! 'x 'y
  (lambda () (mn-ineq '(<= x y) '(IN x RR) '(IN y RR)))
  (lambda () (mn-ineq '(IN y RR))))
(qed 'rr-min-le-right)
(topic! 'rr-min-le-right 'inequalities)

;;; =====================================================================
;;; (5) the universal property: min is the GREATEST common lower bound.
;;; Both branches close by `ass' -- whichever argument min turned out to be,
;;; its bound is a hypothesis.
;;; =====================================================================
(sp (make-wff-from-string
     "forall([x in rr, y in rr, z in rr], z <= x implies z <= y implies z <= min(x,y))"))
(mn-peel!)
(mn-def! 'x 'y)
(mn-cases! 'x 'y (lambda () (ass)) (lambda () (ass)))
(qed 'rr-le-min)
(topic! 'rr-le-min 'inequalities)
(alias! 'rr-le-min "the minimum is the greatest common lower bound")

;;; =====================================================================
;;; (6) and (7): MAX and MIN stay inside NN.
;;;
;;; No NN order theory is used.  `rr-max-cases' / `rr-min-cases' say the value
;;; IS one of the two arguments; both arguments are in NN by hypothesis; and
;;; `nn-in-rr' is what lets the RR-level fact be cited at NN-typed terms in the
;;; first place.  The whole content is the case split.
;;; =====================================================================
(define (mn-nn-closed! head)
  (fact 'nn-in-rr 'x)
  (fact 'nn-in-rr 'y)
  (fact (if (eq? head 'max) 'rr-max-cases 'rr-min-cases) 'x 'y)
  (use-cases (list (list '= (list head 'x 'y) 'x) (list '= (list head 'x 'y) 'y))
    (lambda () (subst (list '= (list head 'x 'y) 'x)) (ass))
    (lambda () (subst (list '= (list head 'x 'y) 'y)) (ass))))

(sp (make-wff-from-string "forall([x in nn, y in nn], max(x,y) in nn)"))
(mn-peel!)
(mn-nn-closed! 'max)
(qed 'nn-max-closed)
(topic! 'nn-max-closed 'inequalities)

(sp (make-wff-from-string "forall([x in nn, y in nn], min(x,y) in nn)"))
(mn-peel!)
(mn-nn-closed! 'min)
(qed 'nn-min-closed)
(topic! 'nn-min-closed 'inequalities)

;;; =====================================================================
;;; (8) MIN AGAINST 1 IS SUBADDITIVE ON THE NONNEGATIVES:
;;;
;;;     0 <= a, 0 <= b   =>   min(1, a+b) <= min(1,a) + min(1,b)
;;;
;;; The one min law the truncated-metric constructions want and the five above
;;; do not give.  It is what makes  d |-> min(1,d)  carry the TRIANGLE
;;; INEQUALITY: from d(x,z) <= d(x,y) + d(y,z) and monotonicity of min in its
;;; second argument, min(1,d(x,z)) <= min(1, d(x,y)+d(y,z)), and this lemma
;;; finishes.  C-METRIC's per-coordinate term min(1, d_k(u,v)) is exactly that
;;; truncation.
;;;
;;; NO NEW MECHANISM AND NO SUBST.  `rr-min-cases' says each of min(1,a) and
;;; min(1,b) IS one of its arguments, so two nested `use-cases' give four
;;; leaves, and in every one of them `ineq' closes from the SAME six premises:
;;; the two case equations, the two bounds min(1,a+b) <= 1 and
;;; min(1,a+b) <= a+b, and the two nonnegativity hypotheses.  `min(1,a)' is an
;;; opaque ATOM to the oracle and the case equation is what ties it down -- so
;;; the equations are named as PREMISES rather than substituted into the goal,
;;; which is one step shorter and leaves the goal alone.
;;;
;;; The four leaves, in the order the nesting takes them:
;;;   min(1,a)=1, min(1,b)=1   1 <= 1 + 1              (min(1,a+b) <= 1)
;;;   min(1,a)=1, min(1,b)=b   1 <= 1 + b              (b >= 0)
;;;   min(1,a)=a, min(1,b)=1   1 <= a + 1              (a >= 0)
;;;   min(1,a)=a, min(1,b)=b   a+b <= a + b            (min(1,a+b) <= a+b)
;;; =====================================================================
(sp (make-wff-from-string
     "forall([x in rr, y in rr], 0 <= x implies 0 <= y implies
      min(1, x + y) <= min(1, x) + min(1, y))"))
(mn-peel!)
(fact 'rr-one-in)
(have! '(AND (IN x RR) (IN y RR)))
(fact 'rr-add-closed 'x 'y)
(fact 'rr-min-closed 1 'x)
(fact 'rr-min-closed 1 'y)
(fact 'rr-min-closed 1 '(+ x y))
(fact 'rr-min-le-left 1 '(+ x y))
(fact 'rr-min-le-right 1 '(+ x y))
(fact 'rr-min-cases 1 'x)
(fact 'rr-min-cases 1 'y)
(define mn-cases-x (list '(= (min 1 x) 1) '(= (min 1 x) x)))
(define mn-cases-y (list '(= (min 1 y) 1) '(= (min 1 y) y)))
(define (mn-sub-close! ex ey)
  (mn-ineq ex ey '(<= (min 1 (+ x y)) 1) '(<= (min 1 (+ x y)) (+ x y))
           '(<= 0 x) '(<= 0 y)))
(use-cases mn-cases-x
  (lambda ()
    (use-cases mn-cases-y
      (lambda () (mn-sub-close! (car mn-cases-x) (car mn-cases-y)))
      (lambda () (mn-sub-close! (car mn-cases-x) (cadr mn-cases-y)))))
  (lambda ()
    (use-cases mn-cases-y
      (lambda () (mn-sub-close! (cadr mn-cases-x) (car mn-cases-y)))
      (lambda () (mn-sub-close! (cadr mn-cases-x) (cadr mn-cases-y))))))
(qed 'rr-min-one-subadditive)
(topic! 'rr-min-one-subadditive 'inequalities)
(alias! 'rr-min-one-subadditive
        "truncation at 1 is subadditive on the nonnegatives"
        "min(1, a+b) <= min(1,a) + min(1,b)")
