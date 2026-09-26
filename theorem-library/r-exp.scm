;;; theorem-library/r-exp.scm -- THE REAL EXPONENTIAL, DEFINED AS THE INVERSE
;;; OF THE LOGARITHM, and its laws.
;;;
;;;     R-EXP(y)  ==  IOTA x_.  x_ in RR  and  0 < x_  and  LOG(x_) = y
;;;
;;; The name is the user's: `R-EXP' and not `EXP', so that the complex
;;; exponential defined later can have the plain name.  Same discipline as
;;; C-INT versus the measure-theoretic INTEGRAL.
;;;
;;; WHY THE `x_ in RR' IS IN THE DESCRIPTION, when `0 < x_' looks like enough.
;;; `<' is primitive and unguarded -- the RR order axioms constrain it on reals
;;; without forbidding it to relate a real to a non-real, which is the point
;;; ivt-proof.scm's header makes about its witness and real-powers.scm's makes
;;; about SQRT.  Without the typing, `log-injective-pos' does not apply to the
;;; description's own candidates and the IOTA describes nothing.  This is the
;;; second group of the eight IOTA-defined functoids (see c-int.scm's header):
;;; the characterising predicate says nothing about membership, so the body
;;; opens with a typing conjunct.
;;;
;;; =====================================================================
;;; 1.  WHAT SURJECTIVITY COSTS, and why it is the only real work here.
;;;
;;; Nothing in the tree says LOG attains every real value, and without that the
;;; inverse is not total.  The route needs no analysis beyond the intermediate
;;; value theorem, and in particular NO POWERS:
;;;
;;;   log-two-pos          0 < log 2                    (log-pos-above-one at 2)
;;;   log-unbounded-above  for every n in NN there is a positive b with
;;;                        n.log2 <= log b.  DOUBLING INDUCTION: b := 1 at 0,
;;;                        and b |-> 2b at the step, where log(2b) = log 2 +
;;;                        log b is the functional equation.  Stating it this
;;;                        way -- an existential over b, inducted on n -- avoids
;;;                        the term 2^n entirely, and with it the whole
;;;                        `power' apparatus.
;;;   log-above-any        for every real y there is a positive b with y <= log b:
;;;                        `nn-unbounded-in-rr' at y.recip(log 2) gives the n,
;;;                        and rr-lt-scale-pos multiplies the bound back up by
;;;                        log 2.
;;;   log-below-any        the mirror, one citation of `log-recip'
;;;                        (log(1/x) = -log x): recip*(b) is positive and its
;;;                        logarithm is -log b.
;;;   log-surjective       `ivt' on x |-> log x over [a,b], where log a <= y <=
;;;                        log b.  Continuity on [a,b] is `log-deriv' followed
;;;                        by `diff-implies-continuous' -- log is DIFFERENTIABLE
;;;                        at every positive point, so no separate continuity
;;;                        argument is needed -- and a <= b is the trichotomy
;;;                        against strict monotonicity.
;;;
;;; =====================================================================
;;; 2.  `deriv-inverse' DOES NOT APPLY, and the obstruction is PROVED here.
;;;
;;; `deriv-inverse' (theorem-library/inverse-function.scm) asks for f to be a
;;; BIJECTION OF RR: BOTH `forall x in RR. g(f(x)) = x' AND `forall y in RR.
;;; f(g(y)) = y'.  With f = log and g = R-EXP the second holds globally and the
;;; first DOES NOT -- and it is not merely unproven, it is FALSE.
;;; `r-exp-log-not-global' below is the theorem
;;;
;;;     NOT (forall x in RR.  R-EXP(LOG(x)) = x)
;;;
;;; proved in four lines: R-EXP's values are POSITIVE (`r-exp-pos', which is a
;;; conjunct of the description), so R-EXP(LOG(0)) > 0 while the universal
;;; instance at 0 says it is 0.  Nothing about the value LOG takes off the
;;; positives enters the argument, so the refutation does not depend on
;;; C-INT-OR's fall-through branch at all.  R-EXP(LOG(x)) = x holds exactly on
;;; the positives (`r-exp-log'), LOG(R-EXP(y)) = y holds everywhere
;;; (`log-r-exp'): one direction is global, the other is not, and
;;; `deriv-inverse' needs both.
;;;
;;; WHAT WAS DONE INSTEAD, and it is a repair rather than a detour.  Reading
;;; inverse-function.scm's driver, the hypothesis `forall x in RR. g(f(x)) = x'
;;; is used in exactly TWO places: once as its instance at a, and once inside
;;; the proof that the Caratheodory factor phi never vanishes.  That second use
;;; only ever needs phi to be non-zero at points of the form g(y) -- because
;;; that is the only place the factorisation of g evaluates it -- and at such a
;;; point non-vanishing follows from the OTHER inverse relation alone:
;;; phi(g(y)) = 0 gives f(g(y)) = f(a), i.e. y = f(a), hence g(y) = g(f(a)) = a,
;;; hence phi(g(y)) = phi(a) = L /= 0.  So the whole universal collapses to the
;;; single equation g(f(a)) = a, and `deriv-right-inverse' below is
;;; `deriv-inverse' with that replacement:
;;;
;;;     IS-DIFF-AT(f,a,L),  L /= 0,  g in FUN(RR,RR),
;;;     forall y in RR. f(g(y)) = y,          -- g a RIGHT inverse of f
;;;     g(f(a)) = a,                          -- a is in the image of g
;;;     g continuous at f(a)
;;;       =>  IS-DIFF-AT(g, f(a), recip(L))
;;;
;;; It is a strict weakening of the hypotheses of `deriv-inverse' (a bijection
;;; satisfies both new clauses), it costs the same driver, and it is what the
;;; exponential -- a bijection RR -> (0, oo), which is not a bijection of RR --
;;; needs.  inverse-function.scm is not touched.
;;;
;;; **`diff-at-local' IS NOT USED, AND THAT IS THE FINDING.**  The brief
;;; expected the derivative to need it -- "establish the Caratheodory identity
;;; on a ball about LOG(c), then diff-at-local".  It does not: the identity is
;;; GLOBAL.  log's own Caratheodory identity holds at every real x, and the
;;; only points it is ever instantiated at here are x = R-EXP(z) for z real,
;;; every one of which is POSITIVE.  So the ball is all of RR and there is
;;; nothing local to patch.  `diff-at-local' earns its keep where the DATA is
;;; local (the FTC in log.scm, where log agrees with an antiderivative only on
;;; an interval); here the data is global and the restriction is on the RANGE,
;;; which IS-DIFF-AT does not quantify over.  Its second use is still ahead of
;;; it.
;;;
;;; =====================================================================
;;; 3.  TOTALITY IS HONEST -- the IFT's packaged-existence obstacle does not
;;;     arise.
;;;
;;; theorem-library/monotone-inverse.scm cannot package its inverse as a
;;; FUNCTION because IS-CONTINUOUS-AT and IS-STRICTLY-INCREASING-ON are about
;;; maps TOTAL on RR, and any total extension of an inverse past an image
;;; INTERVAL is discontinuous at that interval's endpoints -- so the statement
;;; one can write down is false.  That does not happen here.  LOG is onto RR
;;; (section 1), so R-EXP's DOMAIN is genuinely all of RR: `r-exp-lam-in-fun'
;;; is unconditional and no totalisation is performed anywhere in this file.
;;; The positivity of the values is a statement about the RANGE, and a range
;;; restriction costs nothing -- FUN(RR,RR) does not ask a map to be onto.
;;;
;;; CONTINUITY (r-exp-continuous-at) is pure monotonicity and contains no
;;; analysis: given eps, halve a positive lower bound of eps and c = R-EXP(t) to
;;; get d, so that c-d and c+d are POSITIVE reals straddling c; LOG names their
;;; preimages exactly, and delta is a positive lower bound of the two gaps
;;; t - log(c-d) and log(c+d) - t.  Monotonicity of R-EXP carries the ball in
;;; the domain to [c-d, c+d] and d <= eps finishes.  It is the general fact
;;; "a strictly increasing map whose image has no gap at f(t) is continuous at
;;; t", specialised; the general statement is not stated because the tree has no
;;; vocabulary for "the image has no gap" that is shorter than this proof.
;;;
;;; =====================================================================
;;; WHAT IS PROVED
;;;
;;;   log-two-pos, log-unbounded-above, log-above-any, log-below-any,
;;;   log-surjective, log-injective-pos          -- section 1
;;;   r-exp-prop, r-exp-char                     -- the description
;;;   r-exp-in-rr, r-exp-pos, log-r-exp,
;;;   r-exp-lam-in-fun, r-exp-zero, r-exp-log    -- the projections
;;;   r-exp-add, r-exp-strictly-increasing,
;;;   r-exp-mono, r-exp-neg                      -- the algebra
;;;   r-exp-log-not-global                       -- section 2's obstruction
;;;   r-exp-continuous-at                        -- section 3
;;;   rr-recip-recip-pos, deriv-right-inverse,
;;;   r-exp-diff-at-log, r-exp-deriv             -- R-EXP' = R-EXP
;;;
;;; THE BILL.  Nothing here is asserted: there is no `support' and no
;;; `add-axiom!' in this file.  Everything that touches LOG inherits,
;;; unchanged, the thirty-six-leaf `well-known' residue that every log-* theorem
;;; bills (Cor 4.11's MVT/EVT debt, through equation (64)); `rr-recip-recip-pos'
;;; and `deriv-right-inverse' mention no logarithm and are `modulo 0'.
;;;
;;; ONE MECHANICAL POINT worth keeping.  `subst' rewrites the whole goal, and in
;;; `IS-DIFF-AT(R-EXP-lam, y, R-EXP(y))' the point and the derivative value are
;;; the SAME variable, so neither can be rewritten without damaging the other.
;;; `r-exp-diff-at-log' therefore carries the point as a SEPARATE variable w
;;; pinned by `w = log c'; with two variables the two substitutions are
;;; independent, and `r-exp-deriv' is one citation of it at c := R-EXP(y),
;;; w := y.
;;;
;;; Loads after log (log-mul, log-recip, log-deriv, log-strictly-increasing,
;;; log-pos-above-one, log-lam-in-fun, log-in-rr, log-one), ivt-proof (ivt),
;;; inverse-function (rr-recip-solve), continuity-compose
;;; (compose-continuous-at), continuity-recip (recip-continuous-at,
;;; recip-lam-in-fun), differentiation (IS-DIFF-AT, diff-implies-continuous),
;;; recip-star, compose (compose-type, compose-apply), rr-metric-space-proof
;;; (rr-is-metric-space), rr-ms-dist, rr-abs-basics (rr-abs-bound),
;;; rr-order-basics (rr-min-pos, rr-lt-trichotomy), rr-halving
;;; (rr-pos-halvable), ccint-basics (ccint-membership), fun-apply-type-proof
;;; and driver-kit.
;;; =====================================================================

;;; ---- file-local driver helpers (the `rx-' prefix) --------------------

(define (rx-check name)
  (if (not (proof-done? *ps*))
      (error "r-exp: proof did not close" name (expression->string (dk-goal)))))

(define (rx-peel!)
  (let loop ((n 0))
    (let ((g (dk-goal)))
      (if (and (pair? g) (memq (car g) '(FORALL IMPLIES)) (< n 16))
          (begin (di) (loop (+ n 1))) #t))))

(define (rx-split!)
  (let loop ((b 40))
    (when (> b 0)
      (let ((t (let scan ((as (dk-asms)))
                 (cond ((null? as) #f)
                       ((and (pair? (car as)) (memq (caar as) '(AND FORSOME))) (car as))
                       (else (scan (cdr as)))))))
        (when t (ai t) (loop (- b 1)))))))

;;; `ineq' demands an (IN t RR) certificate for every atom of every NAMED
;;; premise, so a blanket sweep of the context's order facts fails as soon as
;;; one of them mentions a term nothing has typed.  Name the premises.
(define (rx-idx f)
  (let lp ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "rx-idx: not in context" (expression->string f)))
          ((equal? (car l) f) i) (else (lp (cdr l) (+ i 1))))))
(define (rx-ineq . fs) (apply ineq (map rx-idx fs)))

;;; a `have!' of a formula already in context is an ALPHA SELF-LOOP, not a no-op
(define (rx-need! f) (if (not (member f (dk-asms))) (have! f)))

(define (rx-fvs forms) (apply append (map free-vars forms)))

;;; `ai' the existential, split what lands, and read the eigenvariable off by
;;; free-variable difference.  `obtain' will not do: it diffs its own lane and
;;; is blind to an existential ALREADY in the context, which is where `fact'
;;; puts one.
(define (rx-skolem! ex)
  (let ((fv0 (rx-fvs (dk-asms))))
    (dk-landed (lambda () (ai ex)))
    (rx-split!)
    (let ((fresh (filter (lambda (v) (not (memq v fv0))) (rx-fvs (dk-asms)))))
      (if (null? fresh) (error "rx-skolem!: no eigenvariable appeared for" ex)
          (car fresh)))))

(define (rx-and! closer)
  (let ((g (dk-goal)))
    (if (and (pair? g) (eq? (car g) 'AND))
        (for-each (lambda (k) (dk-focus! k) (rx-and! closer)) (dk-opened (lambda () (di))))
        (closer))))

(define (rx-goal-ands!)
  (let loop ((fuel 12))
    (let ((ands (filter (lambda (nd) (eq? (car (dk-goal-of nd)) 'AND)) (proof-leaves))))
      (if (and (pair? ands) (> fuel 0))
          (begin (for-each (lambda (nd) (dk-focus! nd) (di)) ands) (loop (- fuel 1)))
          #t))))

;;; `di' until an assumption lands: a GUARDED universal goes whole, an unguarded
;;; one peels the quantifier first and lands nothing.
(define (rx-di-landed!)
  (let loop ((n 0))
    (let ((new (dk-landed* (lambda () (di)))))
      (cond ((pair? new) new)
            ((> n 4) (error "rx-di-landed!: di landed no assumption"))
            (else (loop (+ n 1)))))))

(define (rx-pos-rr! t)
  (have! (list 'POS-RR t)
    (lambda ()
      (fact 'rr-lt-implies-le 0 t)
      (fact 'rr-pos-ne-zero t)
      (fact 'neq-sym t 0)
      (for-each (lambda (nd) (dk-focus! nd) (ass))
                (dk-opened (lambda () (mac 'pos-rr) (rx-goal-ands!)))))))

(define (rx-from-pos-rr! t)
  (mac-h 'pos-rr (list 'POS-RR t))
  (dk-split! (list 'AND (list 'IN t 'RR)
                   (list 'AND (list '<= 0 t) (list 'NOT (list '= 0 t)))))
  (fact 'neq-sym 0 t)
  (rx-need! (list 'AND (list '<= 0 t) (list 'NOT (list '= 0 t))))
  (fact 'rr-le-ne-lt 0 t))

(define (rx-beta!)
  (define (has? g)
    (cond ((and (pair? g) (pair? (car g)) (eq? (caar g) 'VNB-LAMBDA)) #t)
          ((pair? g) (or (has? (car g)) (has? (cdr g))))
          (else #f)))
  (let loop ((fuel 12))
    (if (and (> fuel 0) (has? (dk-goal)))
        (let ((b (dk-goal))) (lam-b) (if (equal? (dk-goal) b) #t (loop (- fuel 1))))
        #t)))

(define (rx-find what p)
  (let lp ((l (dk-asms)))
    (cond ((null? l) (error "rx-find" what)) ((p (car l)) (car l)) (else (lp (cdr l))))))

;;; ---- the two maps ----------------------------------------------------

(define RX-LOGLAM '(VNB-LAMBDA x_ RR (LOG x_)))
(define RX-EXPLAM '(VNB-LAMBDA y_ RR (R-EXP y_)))

;;; =====================================================================
;;; 1.  0 < log 2.
;;; =====================================================================

(sp (make-wff '(< 0 (LOG 2))))
(quietly (lambda ()
  (fact 'rr-zero-in) (fact 'rr-one-in)
  (have! '(IN 2 RR) (lambda () (arith)))
  (have! '(< 1 2) (lambda () (arith)))
  (fact 'log-pos-above-one 2) (ass)))
(rx-check 'log-two-pos)
(qed 'log-two-pos)
(topic! 'log-two-pos 'analysis)
(alias! 'log-two-pos "log 2 is positive")

;;; =====================================================================
;;; 2.  LOG IS UNBOUNDED ABOVE -- the DOUBLING INDUCTION.
;;;
;;; Stated as an existential over b inducted on n, so that the term 2^n never
;;; appears and `power' is not needed at all: the base takes b = 1 and the step
;;; takes b |-> 2b, where log(2b) = log 2 + log b is `log-mul'.
;;; =====================================================================

(sp (make-wff '(FORALL n_ (IMPLIES (IN n_ NN)
   (FORSOME b_ (AND (IN b_ RR) (AND (< 0 b_) (<= (* n_ (LOG 2)) (LOG b_)))))))))
(quietly (lambda ()
  (fact 'rr-zero-in) (fact 'rr-one-in)
  (have! '(IN 2 RR) (lambda () (arith)))
  (have! '(< 0 2) (lambda () (arith)))
  (fact 'rr-zero-lt-one) (fact 'log-two-pos)
  (fact 'log-in-rr 2) (fact 'log-one)
  (ni)
  (for-each
   (lambda (nd)
     (dk-focus! nd)
     (if (eq? (car (dk-goal)) 'FORSOME)
         ;; BASE:  b = 1,  0.log2 = 0 = log 1.
         (begin
           (ew 1)
           (have! '(= (* 0 (LOG 2)) 0) (lambda () (crs)))
           (rx-and! (lambda ()
             (let ((g (dk-goal)))
               (if (memq (car g) '(IN <)) (ass)
                   (begin (subst '(= (LOG 1) 0))
                          (subst '(= (* 0 (LOG 2)) 0))
                          (fact 'rr-leq-reflexive 0) (ass)))))))
         ;; STEP:  b |-> 2b.
         (begin
           (di)
           (let* ((ihl (dk-landed-1 (lambda () (di))))
                  (b   (rx-skolem! ihl)))
             (fact 'nn-in-rr 'n_)
             (fact 'nn-succ-plus-one 'n_)
             (rx-need! (list 'AND '(IN 2 RR) (list 'IN b 'RR)))
             (fact 'rr-mul-closed 2 b)
             (fact 'rr-mul-pos 2 b)
             (fact 'log-mul 2 b)
             (fact 'log-in-rr b) (fact 'log-in-rr (list '* 2 b))
             (rx-need! '(AND (IN n_ RR) (IN (LOG 2) RR)))
             (fact 'rr-mul-closed 'n_ '(LOG 2))
             (have! '(= (* (+ n_ 1) (LOG 2)) (+ (* n_ (LOG 2)) (LOG 2))) (lambda () (crs)))
             (ew (list '* 2 b))
             (rx-and! (lambda ()
               (let ((g (dk-goal)))
                 (if (memq (car g) '(IN <)) (ass)
                     (begin
                       (subst '(= (succ n_) (+ n_ 1)))
                       (subst '(= (* (+ n_ 1) (LOG 2)) (+ (* n_ (LOG 2)) (LOG 2))))
                       (subst (list '= (list 'LOG (list '* 2 b))
                                       (list '+ '(LOG 2) (list 'LOG b))))
                       (rx-ineq (list '<= (list '* 'n_ '(LOG 2)) (list 'LOG b))))))))))))
   (proof-leaves))))
(rx-check 'log-unbounded-above)
(qed 'log-unbounded-above)
(topic! 'log-unbounded-above 'analysis)
(alias! 'log-unbounded-above
        "the logarithm is unbounded above"
        "n.log2 is attained by log at some positive point, for every n")

;;; =====================================================================
;;; 3.  ... hence log exceeds ANY real.
;;; =====================================================================

(sp (make-wff (forall-guarded 'y_ '(IN y_ RR)
   '(FORSOME b_ (AND (IN b_ RR) (AND (< 0 b_) (<= y_ (LOG b_))))))))
(quietly (lambda ()
  (rx-peel!)
  (fact 'rr-zero-in)
  (fact 'log-two-pos) (fact 'log-in-rr 2)
  (fact 'rr-pos-ne-zero '(LOG 2))
  (rx-need! '(AND (IN (LOG 2) RR) (NOT (= (LOG 2) 0))))
  (fact 'rr-recip-closed '(LOG 2))
  (fact 'rr-recip-inverse '(LOG 2))
  (rx-need! '(AND (IN y_ RR) (IN (recip (LOG 2)) RR)))
  (fact 'rr-mul-closed 'y_ '(recip (LOG 2)))
  (let* ((ex (dk-fact! 'nn-unbounded-in-rr '(* y_ (recip (LOG 2)))))
         (n  (rx-skolem! ex)))
    (fact 'nn-in-rr n)
    (rx-need! (list 'AND '(IN (LOG 2) RR) (list 'IN n 'RR)))
    (fact 'rr-mul-closed '(LOG 2) n)
    (rx-need! (list 'AND (list 'IN n 'RR) '(IN (LOG 2) RR)))
    (fact 'rr-mul-closed n '(LOG 2))
    (rx-need! '(AND (IN (LOG 2) RR) (IN (* y_ (recip (LOG 2))) RR)))
    (fact 'rr-mul-closed '(LOG 2) '(* y_ (recip (LOG 2))))
    (rx-need! (list 'AND '(< 0 (LOG 2)) (list '< '(* y_ (recip (LOG 2))) n)))
    (fact 'rr-lt-scale-pos '(LOG 2) '(* y_ (recip (LOG 2))) n)
    ;; log2 . (y . recip(log2)) = y -- `crs' decides ring identities, so the
    ;; inverse law has to be handed to it: commute, substitute, then crs.
    (have! '(= (* (LOG 2) (* y_ (recip (LOG 2)))) y_)
      (lambda ()
        (have! '(= (* (LOG 2) (* y_ (recip (LOG 2)))) (* y_ (* (LOG 2) (recip (LOG 2)))))
               (lambda () (crs)))
        (subst '(= (* (LOG 2) (* y_ (recip (LOG 2)))) (* y_ (* (LOG 2) (recip (LOG 2))))))
        (subst '(= (* (LOG 2) (recip (LOG 2))) 1))
        (crs)))
    (have! (list '= (list '* '(LOG 2) n) (list '* n '(LOG 2))) (lambda () (crs)))
    (let* ((ex2 (dk-fact! 'log-unbounded-above n))
           (b   (rx-skolem! ex2)))
      (fact 'log-in-rr b)
      (ew b)
      (rx-and! (lambda ()
        (let ((g (dk-goal)))
          (if (memq (car g) '(IN <)) (ass)
              (rx-ineq (list '< (list '* '(LOG 2) '(* y_ (recip (LOG 2)))) (list '* '(LOG 2) n))
                       '(= (* (LOG 2) (* y_ (recip (LOG 2)))) y_)
                       (list '= (list '* '(LOG 2) n) (list '* n '(LOG 2)))
                       (list '<= (list '* n '(LOG 2)) (list 'LOG b)))))))))))
(rx-check 'log-above-any)
(qed 'log-above-any)
(topic! 'log-above-any 'analysis)
(alias! 'log-above-any "the logarithm exceeds any prescribed real somewhere")

;;; =====================================================================
;;; 4.  ... and falls below any real:  log(1/b) = -log b.
;;; =====================================================================

(sp (make-wff (forall-guarded 'y_ '(IN y_ RR)
   '(FORSOME a_ (AND (IN a_ RR) (AND (< 0 a_) (<= (LOG a_) y_)))))))
(quietly (lambda ()
  (rx-peel!)
  (fact 'rr-zero-in)
  (fact 'rr-neg-closed 'y_)
  (let* ((ex (dk-fact! 'log-above-any '(- y_)))
         (b  (rx-skolem! ex)))
    (fact 'log-in-rr b)
    (fact 'rr-pos-ne-zero b)
    (fact 'recip-star-in-rr b)
    (fact 'recip-star-value b)
    (fact 'rr-recip-pos b)
    (have! (list '< 0 (list 'RECIP-STAR b))
      (lambda () (subst (list '= (list 'RECIP-STAR b) (list 'recip b))) (ass)))
    (fact 'log-recip b)
    (ew (list 'RECIP-STAR b))
    (rx-and! (lambda ()
      (let ((g (dk-goal)))
        (if (memq (car g) '(IN <)) (ass)
            (begin
              (subst (list '= (list 'LOG (list 'RECIP-STAR b)) (list '- (list 'LOG b))))
              (rx-ineq (list '<= '(- y_) (list 'LOG b)))))))))))
(rx-check 'log-below-any)
(qed 'log-below-any)
(topic! 'log-below-any 'analysis)
(alias! 'log-below-any "the logarithm falls below any prescribed real somewhere")

;;; =====================================================================
;;; 5.  SURJECTIVITY.  `ivt' between the two.
;;; =====================================================================

(sp (make-wff (forall-guarded 'y_ '(IN y_ RR)
   '(FORSOME x_ (AND (IN x_ RR) (AND (< 0 x_) (= (LOG x_) y_)))))))
(quietly (lambda ()
  (rx-peel!)
  (fact 'rr-zero-in)
  (fact 'log-lam-in-fun)
  (let* ((exa (dk-fact! 'log-below-any 'y_))
         (a   (rx-skolem! exa))
         (exb (dk-fact! 'log-above-any 'y_))
         (b   (rx-skolem! exb)))
    (fact 'log-in-rr a) (fact 'log-in-rr b)
    ;; a <= b, from log a <= y <= log b and strict monotonicity
    (have! (list '<= a b)
      (lambda ()
        (fact 'rr-lt-trichotomy a b)
        (use-cases (list (list '< a b) (list '= a b) (list '< b a))
          (lambda () (fact 'rr-lt-implies-le a b) (ass))
          (lambda () (subst (list '= a b)) (fact 'rr-leq-reflexive b) (ass))
          (lambda () (fact 'log-strictly-increasing b a)
                     (rx-ineq (list '< (list 'LOG b) (list 'LOG a))
                              (list '<= (list 'LOG a) 'y_)
                              (list '<= 'y_ (list 'LOG b)))))))
    ;; log is continuous on [a,b] because it is DIFFERENTIABLE there
    (have! (list 'FORALL 'x_ (list 'IMPLIES (list 'IN 'x_ (list 'CCINT a b))
                              (list 'IS-CONTINUOUS-AT 'RR-MS 'RR-MS RX-LOGLAM 'x_)))
      (lambda ()
        (di)
        (mac-h 'ccint-membership (list 'IN 'x_ (list 'CCINT a b)))
        (rx-split!)
        (have! '(< 0 x_) (lambda () (rx-ineq (list '< 0 a) (list '<= a 'x_))))
        (fact 'log-deriv 'x_)
        ;; LUTINS instantiation (2026-09-18): diff-implies-continuous is
        ;; instantiated at the DERIVATIVE VALUE recip-star(x_), an IF-bodied
        ;; functoid the certificate does not reach; recip-star-in-rr types it.
        (fact 'recip-star-in-rr 'x_)
        (fact 'diff-implies-continuous RX-LOGLAM 'x_ '(RECIP-STAR x_))
        (ass)))
    (have! (list '= (list RX-LOGLAM a) (list 'LOG a)) (lambda () (lam-b) (rfl)))
    (have! (list '= (list RX-LOGLAM b) (list 'LOG b)) (lambda () (lam-b) (rfl)))
    ;; `ivt' asks for its two endpoint bounds as ONE conjunction
    (have! (list 'AND (list '<= (list RX-LOGLAM a) 'y_) (list '<= 'y_ (list RX-LOGLAM b)))
      (lambda ()
        (rx-and! (lambda ()
          (let ((g (dk-goal)))
            (if (equal? (cadr g) (list RX-LOGLAM a))
                (begin (subst (list '= (list RX-LOGLAM a) (list 'LOG a))) (ass))
                (begin (subst (list '= (list RX-LOGLAM b) (list 'LOG b))) (ass))))))))
    (let* ((exr (dk-fact! 'ivt RX-LOGLAM a b 'y_))
           (p   (rx-skolem! exr)))
      (mac-h 'ccint-membership (list 'IN p (list 'CCINT a b)))
      (rx-split!)
      (have! (list '< 0 p) (lambda () (rx-ineq (list '< 0 a) (list '<= a p))))
      ;; `rfl' wants a DEFINEDNESS certificate, not just syntactic equality
      (fact 'log-in-rr p)
      (have! (list '= (list RX-LOGLAM p) (list 'LOG p)) (lambda () (lam-b) (rfl)))
      (have! (list '= (list 'LOG p) 'y_)
        (lambda () (subst (list '= (list 'LOG p) (list RX-LOGLAM p))) (ass)))
      (ew p)
      (rx-and! (lambda () (ass)))))))
(rx-check 'log-surjective)
(qed 'log-surjective)
(topic! 'log-surjective 'analysis)
(alias! 'log-surjective
        "the logarithm attains every real value"
        "log is onto the reals")

;;; =====================================================================
;;; 6.  INJECTIVITY on the positives -- the other half of the description.
;;; =====================================================================

(sp (make-wff (forall-guarded '(u_ v_) (list '(IN u_ RR) '(IN v_ RR))
      '(IMPLIES (< 0 u_) (IMPLIES (< 0 v_) (IMPLIES (= (LOG u_) (LOG v_)) (= u_ v_)))))))
(quietly (lambda ()
  (rx-peel!)
  (fact 'log-in-rr 'u_) (fact 'log-in-rr 'v_)
  (fact 'rr-lt-trichotomy 'u_ 'v_)
  (use-cases '((< u_ v_) (= u_ v_) (< v_ u_))
    (lambda () (fact 'log-strictly-increasing 'u_ 'v_)
               (rx-ineq '(< (LOG u_) (LOG v_)) '(= (LOG u_) (LOG v_))))
    (lambda () (ass))
    (lambda () (fact 'log-strictly-increasing 'v_ 'u_)
               (rx-ineq '(< (LOG v_) (LOG u_)) '(= (LOG u_) (LOG v_)))))))
(rx-check 'log-injective-pos)
(qed 'log-injective-pos)
(topic! 'log-injective-pos 'analysis)
(alias! 'log-injective-pos "the logarithm is injective on the positives")

;;; =====================================================================
;;; 7.  THE DEFINITION.
;;; =====================================================================

(def-functoid 'R-EXP '(y_)
  '(IOTA x_ (AND (IN x_ RR) (AND (< 0 x_) (= (LOG x_) y_)))))
(notation! 'R-EXP 'kind 'functoid 'arity 1
           'english "the exponential of $1"
           'noun "exponential of $1"
           'tex "\\exp\\left($1\\right)")

;;; THE DEFINING PROPERTY -- the `iota-d' step, and the only one.
(sp (make-wff (forall-guarded 'y_ '(IN y_ RR)
      '(AND (IN (R-EXP y_) RR) (AND (< 0 (R-EXP y_)) (= (LOG (R-EXP y_)) y_))))))
(rx-peel!)
(fact 'rr-zero-in)
(mac 'R-EXP)
(define rx-io (cadr (cadr (dk-goal))))       ; the IOTA term, as the engine built it
(quietly (lambda ()
(for-each
 (lambda (l)
   (dk-focus! l)
   (if (eq? (car (dk-goal)) 'FORSOME)
       ;; existence-and-uniqueness: surjectivity, then injectivity
       (let* ((ex (dk-fact! 'log-surjective 'y_))
              (w  (rx-skolem! ex)))
         (ew w)
         (for-each
          (lambda (k)
            (dk-focus! k)
            (if (eq? (car (dk-goal)) 'FORALL)
                (begin
                  (rx-peel!) (rx-split!)
                  (let ((z (caddr (dk-goal))))            ; goal (= w z)
                    (fact 'log-in-rr w) (fact 'log-in-rr z)
                    (have! (list '= (list 'LOG w) (list 'LOG z))
                      (lambda () (subst (list '= (list 'LOG w) 'y_))
                                 (subst (list '= (list 'LOG z) 'y_))
                                 (rfl)))
                    (fact 'log-injective-pos w z)
                    (ass)))
                (from-context!)))
          (dk-opened (lambda () (di)))))
       (ass)))                                            ; the defining property IS the goal
 (dk-opened (lambda () (iota-d rx-io))))))
(rx-check 'r-exp-prop)
(qed 'r-exp-prop)
(topic! 'r-exp-prop 'analysis)
(alias! 'r-exp-prop "the defining property of the real exponential")

;;; =====================================================================
;;; 8.  THE PROJECTIONS, and the characterisation.
;;; =====================================================================

(sp (make-wff (forall-guarded 'y_ '(IN y_ RR) '(IN (R-EXP y_) RR))))
(quietly (lambda () (rx-peel!) (fact 'r-exp-prop 'y_) (rx-split!) (ass)))
(rx-check 'r-exp-in-rr)
(qed 'r-exp-in-rr)
(topic! 'r-exp-in-rr 'plumbing)
(alias! 'r-exp-in-rr "the exponential of a real is a real")

(sp (make-wff (forall-guarded 'y_ '(IN y_ RR) '(< 0 (R-EXP y_)))))
(quietly (lambda () (rx-peel!) (fact 'r-exp-prop 'y_) (rx-split!) (ass)))
(rx-check 'r-exp-pos)
(qed 'r-exp-pos)
(topic! 'r-exp-pos 'analysis)
(alias! 'r-exp-pos "the exponential is positive")

(sp (make-wff (forall-guarded 'y_ '(IN y_ RR) '(= (LOG (R-EXP y_)) y_))))
(quietly (lambda () (rx-peel!) (fact 'r-exp-prop 'y_) (rx-split!) (ass)))
(rx-check 'log-r-exp)
(qed 'log-r-exp)
(topic! 'log-r-exp 'analysis)
(alias! 'log-r-exp "log(exp y) = y, at EVERY real y")

(sp (make-wff (forall-guarded '(y_ x_) (list '(IN y_ RR) '(IN x_ RR))
      '(IMPLIES (< 0 x_) (IMPLIES (= (LOG x_) y_) (= (R-EXP y_) x_))))))
(quietly (lambda ()
  (rx-peel!)
  (fact 'r-exp-prop 'y_)
  (rx-split!)
  (fact 'log-in-rr 'x_) (fact 'log-in-rr '(R-EXP y_))
  (have! '(= (LOG (R-EXP y_)) (LOG x_))
    (lambda () (subst '(= (LOG (R-EXP y_)) y_)) (subst '(= (LOG x_) y_)) (rfl)))
  (fact 'log-injective-pos '(R-EXP y_) 'x_)
  (ass)))
(rx-check 'r-exp-char)
(qed 'r-exp-char)
(topic! 'r-exp-char 'analysis)
(alias! 'r-exp-char "characterisation of the real exponential"
        "a positive real whose logarithm is y IS exp(y)")

;;; R-EXP IS A MAP RR -> RR, unconditionally -- see section 3 of the header.
(sp (make-wff (list 'IN RX-EXPLAM '(FUN RR RR))))
(quietly (lambda ()
  (for-each (lambda (leaf)
              (dk-focus! leaf)
              (if (eq? (car (dk-goal)) 'FORALL)
                  (let* ((lnd (dk-landed-1 (lambda () (di))))
                         (v   (cadr lnd)))
                    (fact 'r-exp-in-rr v) (ass))
                  (begin (fact 'rr-is-set) (ass))))
            (dk-opened (lambda () (lam-t))))))
(rx-check 'r-exp-lam-in-fun)
(qed 'r-exp-lam-in-fun)
(topic! 'r-exp-lam-in-fun 'analysis)
(alias! 'r-exp-lam-in-fun "the exponential is a function from the reals to the reals")

;;; =====================================================================
;;; 9.  exp 0 = 1,  and exp(log x) = x on the POSITIVES.
;;; =====================================================================

(sp (make-wff '(= (R-EXP 0) 1)))
(quietly (lambda ()
  (fact 'rr-zero-in) (fact 'rr-one-in) (fact 'rr-zero-lt-one) (fact 'log-one)
  (fact 'r-exp-char 0 1) (ass)))
(rx-check 'r-exp-zero)
(qed 'r-exp-zero)
(topic! 'r-exp-zero 'analysis)
(alias! 'r-exp-zero "exp 0 = 1")

(sp (make-wff (forall-guarded 'x_ '(IN x_ RR) '(IMPLIES (< 0 x_) (= (R-EXP (LOG x_)) x_)))))
(quietly (lambda ()
  (rx-peel!)
  (fact 'log-in-rr 'x_)
  (fact 'rr-zero-in)
  (have! '(= (LOG x_) (LOG x_)) (lambda () (rfl)))
  (fact 'r-exp-char '(LOG x_) 'x_)
  (ass)))
(rx-check 'r-exp-log)
(qed 'r-exp-log)
(topic! 'r-exp-log 'analysis)
(alias! 'r-exp-log "exp(log x) = x, for POSITIVE x")

;;; =====================================================================
;;; 10.  THE FUNCTIONAL EQUATION,  exp(u+v) = exp u . exp v.
;;; =====================================================================

(sp (make-wff (forall-guarded '(u_ v_) (list '(IN u_ RR) '(IN v_ RR))
      '(= (R-EXP (+ u_ v_)) (* (R-EXP u_) (R-EXP v_))))))
(quietly (lambda ()
  (rx-peel!)
  (fact 'rr-zero-in)
  (rx-need! '(AND (IN u_ RR) (IN v_ RR)))
  (fact 'rr-add-closed 'u_ 'v_)
  (fact 'r-exp-in-rr 'u_) (fact 'r-exp-in-rr 'v_)
  (fact 'r-exp-pos 'u_) (fact 'r-exp-pos 'v_)
  (rx-need! '(AND (IN (R-EXP u_) RR) (IN (R-EXP v_) RR)))
  (fact 'rr-mul-closed '(R-EXP u_) '(R-EXP v_))
  (fact 'rr-mul-pos '(R-EXP u_) '(R-EXP v_))
  (fact 'log-mul '(R-EXP u_) '(R-EXP v_))
  (fact 'log-r-exp 'u_) (fact 'log-r-exp 'v_)
  (have! '(= (LOG (* (R-EXP u_) (R-EXP v_))) (+ u_ v_))
    (lambda ()
      (subst '(= (LOG (* (R-EXP u_) (R-EXP v_)))
                 (+ (LOG (R-EXP u_)) (LOG (R-EXP v_)))))
      (subst '(= (LOG (R-EXP u_)) u_))
      (subst '(= (LOG (R-EXP v_)) v_))
      (rfl)))
  (fact 'r-exp-char '(+ u_ v_) '(* (R-EXP u_) (R-EXP v_)))
  (ass)))
(rx-check 'r-exp-add)
(qed 'r-exp-add)
(topic! 'r-exp-add 'analysis)
(alias! 'r-exp-add "the exponential turns sums into products"
        "exp(u+v) = exp u . exp v")

;;; =====================================================================
;;; 11.  MONOTONICITY, strict and not.
;;; =====================================================================

(sp (make-wff (forall-guarded '(u_ v_) (list '(IN u_ RR) '(IN v_ RR))
      '(IMPLIES (< u_ v_) (< (R-EXP u_) (R-EXP v_))))))
(quietly (lambda ()
  (rx-peel!)
  (fact 'rr-zero-in)
  (fact 'r-exp-in-rr 'u_) (fact 'r-exp-in-rr 'v_)
  (fact 'r-exp-pos 'u_) (fact 'r-exp-pos 'v_)
  (fact 'log-r-exp 'u_) (fact 'log-r-exp 'v_)
  (fact 'log-in-rr '(R-EXP u_)) (fact 'log-in-rr '(R-EXP v_))
  (fact 'rr-lt-trichotomy '(R-EXP u_) '(R-EXP v_))
  (use-cases '((< (R-EXP u_) (R-EXP v_)) (= (R-EXP u_) (R-EXP v_)) (< (R-EXP v_) (R-EXP u_)))
    (lambda () (ass))
    (lambda ()
      (have! '(= (LOG (R-EXP u_)) (LOG (R-EXP v_)))
             (lambda () (subst '(= (R-EXP u_) (R-EXP v_))) (rfl)))
      (rx-ineq '(= (LOG (R-EXP u_)) (LOG (R-EXP v_)))
               '(= (LOG (R-EXP u_)) u_) '(= (LOG (R-EXP v_)) v_) '(< u_ v_)))
    (lambda ()
      (fact 'log-strictly-increasing '(R-EXP v_) '(R-EXP u_))
      (rx-ineq '(< (LOG (R-EXP v_)) (LOG (R-EXP u_)))
               '(= (LOG (R-EXP u_)) u_) '(= (LOG (R-EXP v_)) v_) '(< u_ v_))))))
(rx-check 'r-exp-strictly-increasing)
(qed 'r-exp-strictly-increasing)
(topic! 'r-exp-strictly-increasing 'analysis)
(alias! 'r-exp-strictly-increasing "the exponential is strictly increasing")

(sp (make-wff (forall-guarded '(u_ v_) (list '(IN u_ RR) '(IN v_ RR))
      '(IMPLIES (<= u_ v_) (<= (R-EXP u_) (R-EXP v_))))))
(quietly (lambda ()
  (rx-peel!)
  (fact 'r-exp-in-rr 'u_) (fact 'r-exp-in-rr 'v_)
  (fact 'rr-lt-trichotomy 'u_ 'v_)
  (use-cases '((< u_ v_) (= u_ v_) (< v_ u_))
    (lambda () (fact 'r-exp-strictly-increasing 'u_ 'v_)
               (rx-ineq '(< (R-EXP u_) (R-EXP v_))))
    (lambda () (subst '(= u_ v_)) (fact 'rr-leq-reflexive '(R-EXP v_)) (ass))
    (lambda () (rx-ineq '(< v_ u_) '(<= u_ v_))))))
(rx-check 'r-exp-mono)
(qed 'r-exp-mono)
(topic! 'r-exp-mono 'analysis)
(alias! 'r-exp-mono "the exponential is nondecreasing")

;;; =====================================================================
;;; 12.  exp(-y) = 1/exp(y).
;;; =====================================================================

(sp (make-wff (forall-guarded 'y_ '(IN y_ RR)
      '(= (R-EXP (- y_)) (RECIP-STAR (R-EXP y_))))))
(quietly (lambda ()
  (rx-peel!)
  (fact 'rr-zero-in)
  (fact 'rr-neg-closed 'y_)
  (fact 'r-exp-in-rr 'y_) (fact 'r-exp-pos 'y_) (fact 'log-r-exp 'y_)
  (fact 'rr-pos-ne-zero '(R-EXP y_))
  (fact 'recip-star-in-rr '(R-EXP y_))
  (fact 'recip-star-value '(R-EXP y_))
  (fact 'rr-recip-pos '(R-EXP y_))
  (have! '(< 0 (RECIP-STAR (R-EXP y_)))
    (lambda () (subst '(= (RECIP-STAR (R-EXP y_)) (recip (R-EXP y_)))) (ass)))
  (fact 'log-recip '(R-EXP y_))
  (have! '(= (LOG (RECIP-STAR (R-EXP y_))) (- y_))
    (lambda ()
      (subst '(= (LOG (RECIP-STAR (R-EXP y_))) (- (LOG (R-EXP y_)))))
      (subst '(= (LOG (R-EXP y_)) y_))
      (rfl)))
  (fact 'r-exp-char '(- y_) '(RECIP-STAR (R-EXP y_)))
  (ass)))
(rx-check 'r-exp-neg)
(qed 'r-exp-neg)
(topic! 'r-exp-neg 'analysis)
(alias! 'r-exp-neg "exp(-y) = 1/exp(y)")

;;; =====================================================================
;;; 13.  THE OBSTRUCTION.  The global inverse relation `deriv-inverse' asks
;;;      for is FALSE -- see section 2 of the header.
;;; =====================================================================

(sp (make-wff '(NOT (FORALL x_ (IMPLIES (IN x_ RR) (= (R-EXP (LOG x_)) x_))))))
(quietly (lambda ()
  (di)
  (fact 'rr-zero-in)
  (fact 'log-in-rr 0)
  (fact 'r-exp-pos '(LOG 0))
  (fact 'r-exp-in-rr '(LOG 0))
  (fact 'rr-pos-ne-zero '(R-EXP (LOG 0)))
  (inst+ '(FORALL x_ (IMPLIES (IN x_ RR) (= (R-EXP (LOG x_)) x_))) 0)
  ;; NOT-elim, not `contra': this file loads long before contra.scm, and the
  ;; positive is already in context, which is what `ai' on a NOT requires.
  (ai '(NOT (= (R-EXP (LOG 0)) 0)))))
(rx-check 'r-exp-log-not-global)
(qed 'r-exp-log-not-global)
(topic! 'r-exp-log-not-global 'analysis)
(alias! 'r-exp-log-not-global
        "exp(log x) = x is NOT a global identity"
        "why deriv-inverse cannot be cited for the exponential")

;;; =====================================================================
;;; 14.  CONTINUITY.  Pure monotonicity: the image of R-EXP has no gap at
;;;      R-EXP(t), because LOG names the preimages of c-d and c+d exactly.
;;; =====================================================================

(define rx-t #f) (define rx-c #f) (define rx-e #f)
(define rx-m #f) (define rx-d #f) (define rx-delta #f)
(define (rx-lo) (list '- rx-c rx-d))
(define (rx-hi) (list '+ rx-c rx-d))
(define (rx-p)  (list 'LOG (rx-lo)))
(define (rx-q)  (list 'LOG (rx-hi)))

;;; the innermost goal:  |exp t - exp b| <= eps  for b within delta of t.
(define (rx-inner!)
  (let* ((landed (rx-di-landed!))
         (mem (or (find-first (lambda (a) (and (pair? a) (eq? (car a) 'IN))) landed)
                  (error "rx-inner!: no membership landed")))
         (b (cadr mem)))
    (if (not (find-first (lambda (a) (and (pair? a) (eq? (car a) '<=))) landed))
        (rx-di-landed!))
    ;; ONLY NOW may the two applications be beta-reduced: the enclosing binder
    ;; guards b in PTS(RR-MS), not in RR, and `lam-b' on an untyped argument
    ;; still fires and then owes (IN b RR) at a node whose context predates b.
    (slot-h 'PTS mem)
    (fact 'r-exp-in-rr b)
    (fact 'rr-sub-in-rr rx-t b)
    (fact 'rr-sub-in-rr rx-c (list 'R-EXP b))
    (rx-beta!)
    (mac-h 'rr-ms-dist (list '<= (list '(DIST RR-MS) rx-t b) rx-delta))
    (mac-h 'rr-abs-bound (list '<= (list 'abs (list '- rx-t b)) rx-delta))
    (rx-split!)
    ;; the ball in the DOMAIN, read through log's two named preimages
    (have! (list '<= (rx-p) b)
      (lambda () (rx-ineq (list '<= (list '- rx-t b) rx-delta)
                          (list '<= rx-delta (list '- rx-t (rx-p))))))
    (have! (list '<= b (rx-q))
      (lambda () (rx-ineq (list '<= (list '- rx-delta) (list '- rx-t b))
                          (list '<= rx-delta (list '- (rx-q) rx-t)))))
    (fact 'log-in-rr (rx-lo)) (fact 'log-in-rr (rx-hi))
    (fact 'r-exp-in-rr (rx-p)) (fact 'r-exp-in-rr (rx-q))
    (fact 'r-exp-mono (rx-p) b)
    (fact 'r-exp-mono b (rx-q))
    (fact 'r-exp-log (rx-lo))
    (fact 'r-exp-log (rx-hi))
    (have! (list '<= (rx-lo) (list 'R-EXP b))
      (lambda () (rx-ineq (list '<= (list 'R-EXP (rx-p)) (list 'R-EXP b))
                          (list '= (list 'R-EXP (rx-p)) (rx-lo)))))
    (have! (list '<= (list 'R-EXP b) (rx-hi))
      (lambda () (rx-ineq (list '<= (list 'R-EXP b) (list 'R-EXP (rx-q)))
                          (list '= (list 'R-EXP (rx-q)) (rx-hi)))))
    ;; ... and back to a distance in the CODOMAIN.  d + d = m <= eps.
    (mac 'rr-ms-dist)
    (mac 'rr-abs-bound)
    (rx-and! (lambda ()
      (rx-ineq (list '<= (rx-lo) (list 'R-EXP b))
               (list '<= (list 'R-EXP b) (rx-hi))
               (list '= (list '+ rx-d rx-d) rx-m)
               (list '<= rx-m rx-e)
               (list '< 0 rx-d))))))

;;; the eps branch: halve a positive lower bound of eps and c, then choose delta.
(define (rx-eps!)
  (let* ((pos (car (rx-di-landed!)))
         (eps (cadr pos)))
    (set! rx-e eps)
    (mac-h 'pos-rr pos)
    (rx-split!)
    (rx-need! (list 'AND (list '<= 0 eps) (list 'NOT (list '= 0 eps))))
    (fact 'rr-le-ne-lt 0 eps)
    (rx-need! (list 'AND (list 'IN eps 'RR) (list 'IN rx-c 'RR)))
    (set! rx-m (rx-skolem! (dk-deepest (lambda () (fact 'rr-min-pos eps rx-c)))))
    (rx-pos-rr! rx-m)
    (set! rx-d (rx-skolem! (dk-deepest (lambda () (fact 'rr-pos-halvable rx-m)))))
    (rx-from-pos-rr! rx-d)
    ;; c-d and c+d are POSITIVE reals straddling c -- positivity of c-d is what
    ;; the halving is for, and it is linear:  d + d = m <= c  and  0 < d.
    (rx-need! (list 'AND (list 'IN rx-c 'RR) (list 'IN rx-d 'RR)))
    (fact 'rr-sub-in-rr rx-c rx-d)
    (fact 'rr-add-closed rx-c rx-d)
    (have! (list '< 0 (rx-lo))
      (lambda () (rx-ineq (list '= (list '+ rx-d rx-d) rx-m)
                          (list '<= rx-m rx-c) (list '< 0 rx-d))))
    (have! (list '< (rx-lo) rx-c) (lambda () (rx-ineq (list '< 0 rx-d))))
    (have! (list '< rx-c (rx-hi)) (lambda () (rx-ineq (list '< 0 rx-d))))
    (have! (list '< 0 (rx-hi))
      (lambda () (rx-ineq (list '< 0 (rx-lo)) (list '< (rx-lo) rx-c)
                          (list '< rx-c (rx-hi)))))
    (fact 'log-in-rr (rx-lo)) (fact 'log-in-rr (rx-hi)) (fact 'log-in-rr rx-c)
    (fact 'log-strictly-increasing (rx-lo) rx-c)
    (fact 'log-strictly-increasing rx-c (rx-hi))
    (fact 'log-r-exp rx-t)
    (have! (list '< (rx-p) rx-t)
      (lambda () (rx-ineq (list '< (rx-p) (list 'LOG rx-c))
                          (list '= (list 'LOG rx-c) rx-t))))
    (have! (list '< rx-t (rx-q))
      (lambda () (rx-ineq (list '< (list 'LOG rx-c) (rx-q))
                          (list '= (list 'LOG rx-c) rx-t))))
    (fact 'rr-sub-in-rr rx-t (rx-p))
    (fact 'rr-sub-in-rr (rx-q) rx-t)
    (have! (list '< 0 (list '- rx-t (rx-p)))
           (lambda () (rx-ineq (list '< (rx-p) rx-t))))
    (have! (list '< 0 (list '- (rx-q) rx-t))
           (lambda () (rx-ineq (list '< rx-t (rx-q)))))
    (rx-need! (list 'AND (list 'IN (list '- rx-t (rx-p)) 'RR)
                         (list 'IN (list '- (rx-q) rx-t) 'RR)))
    (set! rx-delta (rx-skolem! (dk-deepest
      (lambda () (fact 'rr-min-pos (list '- rx-t (rx-p)) (list '- (rx-q) rx-t))))))
    (rx-pos-rr! rx-delta)
    (ew rx-delta)
    (rx-and! (lambda ()
      (let ((g (dk-goal)))
        (cond ((eq? (car g) 'POS-RR) (ass))
              ((eq? (car g) 'FORALL) (rx-inner!))
              (else (ass))))))))

(sp (make-wff (forall-guarded 't_ '(IN t_ RR)
      (list 'IS-CONTINUOUS-AT 'RR-MS 'RR-MS RX-EXPLAM 't_))))
(rx-peel!)
(set! rx-t 't_)
(set! rx-c '(R-EXP t_))
(quietly (lambda ()
  (fact 'rr-zero-in)
  (fact 'rr-is-metric-space)
  (fact 'r-exp-lam-in-fun)
  (fact 'r-exp-in-rr 't_)
  (fact 'r-exp-pos 't_)
  (mac 'is-continuous-at)
  (rx-and!
   (lambda ()
     (let ((g (dk-goal)))
       (cond ((eq? (car g) 'FORALL) (rx-eps!))
             ((and (eq? (car g) 'IN) (dk-contains? g 'PTS)) (slot 'PTS) (ass))
             (else (ass))))))
  ;; A GUARDED macete applied to a HYPOTHESIS does not decline -- it applies and
  ;; posts its guard as a side-condition subgoal.  `rr-abs-bound' is guarded on
  ;; its arguments being real, so rx-inner! leaves a typing leaf behind that the
  ;; linear script walks straight past; it surfaces only at `qed'.
  (let close ((fuel 40) (prev #f))
    (let ((s (find-first (lambda (s) (null? (sequent-node-in-arrows s))) (proof-leaves))))
      (if (and s (> fuel 0))
          (begin
            (if (eq? s prev) (error "r-exp: leftover leaf did not close" (dk-goal)))
            (dk-focus! s)
            (let ((g (dk-goal)))
              (if (and (pair? g) (eq? (car g) 'IN) (equal? (caddr g) 'RR))
                  (ass)
                  (error "r-exp: unexpected leftover leaf" (expression->string g))))
            (close (- fuel 1) s)))))))
(rx-check 'r-exp-continuous-at)
(qed 'r-exp-continuous-at)
(topic! 'r-exp-continuous-at 'analysis)
(alias! 'r-exp-continuous-at "the exponential is continuous")

;;; =====================================================================
;;; 15.  recip(recip c) = c for c > 0 -- there was no involution law.
;;; =====================================================================

(sp (make-wff (forall-guarded 'c_ '(IN c_ RR) '(IMPLIES (< 0 c_) (= (recip (recip c_)) c_)))))
(quietly (lambda ()
  (rx-peel!)
  (fact 'rr-zero-in) (fact 'rr-one-in)
  (fact 'rr-pos-ne-zero 'c_)
  (rx-need! '(AND (IN c_ RR) (NOT (= c_ 0))))
  (fact 'rr-recip-closed 'c_)
  (fact 'rr-recip-inverse 'c_)
  (fact 'rr-recip-pos 'c_)
  (fact 'rr-pos-ne-zero '(recip c_))
  (rx-need! '(AND (IN (recip c_) RR) (NOT (= (recip c_) 0))))
  (fact 'rr-recip-closed '(recip c_))
  (fact 'rr-recip-inverse '(recip c_))
  (have! '(= (* (* c_ (recip c_)) (recip (recip c_)))
             (* c_ (* (recip c_) (recip (recip c_))))) (lambda () (crs)))
  (have! '(= (recip (recip c_)) (* (* c_ (recip c_)) (recip (recip c_))))
    (lambda () (subst '(= (* c_ (recip c_)) 1)) (crs)))
  (subst '(= (recip (recip c_)) (* (* c_ (recip c_)) (recip (recip c_)))))
  (subst '(= (* (* c_ (recip c_)) (recip (recip c_)))
             (* c_ (* (recip c_) (recip (recip c_))))))
  (subst '(= (* (recip c_) (recip (recip c_))) 1))
  (crs)))
(rx-check 'rr-recip-recip-pos)
(qed 'rr-recip-recip-pos)
(topic! 'rr-recip-recip-pos 'algebra)
(alias! 'rr-recip-recip-pos "the reciprocal is an involution on the positives")

;;; =====================================================================
;;; 16.  deriv-right-inverse -- `deriv-inverse' with the global left-inverse
;;;      hypothesis weakened to ONE equation.  See section 2 of the header.
;;; =====================================================================

(define RX-FA '(fm_ am_))
(define RX-FG '(FORALL z_ (IMPLIES (IN z_ RR) (= (fm_ (gm_ z_)) z_))))

(sp (make-wff (forall-guarded '(fm_ gm_ am_ lv_)
  (list '(IS-DIFF-AT fm_ am_ lv_)
        '(NOT (= lv_ 0))
        '(IN gm_ (FUN RR RR))
        RX-FG
        '(= (gm_ (fm_ am_)) am_)
        '(IS-CONTINUOUS-AT RR-MS RR-MS gm_ (fm_ am_)))
  '(IS-DIFF-AT gm_ (fm_ am_) (recip lv_)))))
(dk-peel-to! 'IS-DIFF-AT)
;; `mac-h' is destructive, so the two inverse facts and g's continuity are read
;; off the context BEFORE IS-DIFF-AT(f,a,L) is unfolded -- here they are literal
;; formulas, so nothing has to be searched for but phi itself.
(mac-h 'IS-DIFF-AT '(IS-DIFF-AT fm_ am_ lv_))
(rx-split!)
(define rx-phi
  (list-ref (rx-find 'phi-cont
    (lambda (u) (and (pair? u) (eq? (car u) 'IS-CONTINUOUS-AT) (equal? (list-ref u 4) 'am_))))
            3))
(define rx-idphi
  (rx-find 'phi-id
    (lambda (u) (and (pair? u) (eq? (car u) 'FORALL) (dk-contains? u rx-phi)
                     (pair? (caddr u)) (eq? (car (caddr u)) 'IMPLIES)
                     (let ((c (caddr (caddr u))))
                       (and (pair? c) (eq? (car c) '=) (pair? (caddr c))
                            (eq? (car (caddr c)) '*)))))))
(define rx-nz
  (list 'FORALL 'z_ (list 'IMPLIES '(IN z_ RR)
        (list 'NOT (list '= (list rx-phi '(gm_ z_)) 0)))))
(define rx-h (list 'COMPOSE rx-phi 'gm_))
(define rx-aph #f)
(define rx-psi #f)

(quietly (lambda ()
(fact 'rr-zero-in)
(fact 'fun-apply-type-c 'fm_ 'RR 'RR 'am_)

;;; phi does not vanish at any point of g's IMAGE -- which is the only place the
;;; Caratheodory factorisation of g ever evaluates it.  This is where
;;; `deriv-inverse' used its global left inverse; the RIGHT inverse plus the one
;;; equation g(f(a)) = a does the same job.
(have! rx-nz
  (lambda ()
    (di) (di)
    (fact 'fun-apply-type-c 'gm_ 'RR 'RR 'z_)
    (dk-deepest (lambda () (inst+ rx-idphi '(gm_ z_))))
    (fact 'fun-apply-type-c 'fm_ 'RR 'RR '(gm_ z_))
    (fact 'fun-apply-type-c rx-phi 'RR 'RR '(gm_ z_))
    (fact 'rr-sub-in-rr '(gm_ z_) 'am_)
    (fact 'rr-sub-in-rr '(fm_ (gm_ z_)) RX-FA)
    (have! (list '= (list '- '(fm_ (gm_ z_)) RX-FA) 0)
      (lambda ()
        (subst (list '= (list '- '(fm_ (gm_ z_)) RX-FA)
                        (list '* (list rx-phi '(gm_ z_)) '(- (gm_ z_) am_))))
        (subst (list '= (list rx-phi '(gm_ z_)) 0))
        (crs)))
    (dk-deepest (lambda () (inst+ RX-FG 'z_)))
    (have! (list '= 'z_ RX-FA)
      (lambda () (rx-ineq (list '= (list '- '(fm_ (gm_ z_)) RX-FA) 0)
                          '(= (fm_ (gm_ z_)) z_))))
    (have! '(= (gm_ z_) am_)
      (lambda () (subst (list '= 'z_ RX-FA)) (ass)))
    (have! '(= lv_ 0)
      (lambda ()
        (fact 'eq-sym (list rx-phi 'am_) 'lv_)
        (subst (list '= 'lv_ (list rx-phi 'am_)))
        (fact 'eq-sym '(gm_ z_) 'am_)
        (subst '(= am_ (gm_ z_)))
        (ass)))
    (ai '(NOT (= lv_ 0)))))

;;; H = phi o g,  and psi = recip o H is the Caratheodory factor of g.
(fact 'rr-is-set)
(rx-need! (list 'AND '(IN gm_ (FUN RR RR)) (list 'IN rx-phi '(FUN RR RR))))
(fact 'compose-type 'RR 'RR 'RR rx-phi 'gm_)
(set! rx-aph (dk-fact! 'compose-apply 'RR 'RR 'RR rx-phi 'gm_))
(have! (list 'FORALL 'z_ (list 'IMPLIES '(IN z_ RR)
              (list 'NOT (list '= (list rx-h 'z_) 0))))
  (lambda ()
    (di)
    (dk-deepest (lambda () (inst+ rx-aph 'z_)))
    (subst (list '= (list rx-h 'z_) (list rx-phi '(gm_ z_))))
    (dk-deepest (lambda () (inst+ rx-nz 'z_)))
    (ass)))
(have! (list 'IS-CONTINUOUS-AT 'RR-MS 'RR-MS rx-phi (list 'gm_ RX-FA))
  (lambda () (subst (list '= (list 'gm_ RX-FA) 'am_)) (ass)))
(fact 'compose-continuous-at rx-phi 'gm_ RX-FA)
(fact 'recip-lam-in-fun rx-h)
;; the witness is not rebuilt by hand: `recip-continuous-at' concludes about the
;; literal term (VNB-LAMBDA x RR (recip (H x))), and that term IS the witness.
(set! rx-psi (list-ref (dk-fact! 'recip-continuous-at rx-h RX-FA) 3))
(rx-need! '(AND (IN lv_ RR) (NOT (= lv_ 0))))
(fact 'rr-recip-closed 'lv_)

(mac 'IS-DIFF-AT)
(rx-and!
 (lambda ()
   (if (eq? (car (dk-goal)) 'FORSOME)
       (begin
         (ew rx-psi)
         (rx-and!
          (lambda ()
            (let ((h (dk-goal)))
              (cond
               ((eq? (car h) '=)
                (rx-beta!)
                (dk-deepest (lambda () (inst+ rx-aph RX-FA)))
                (subst (list '= (list rx-h RX-FA) (list rx-phi (list 'gm_ RX-FA))))
                (subst (list '= (list 'gm_ RX-FA) 'am_))
                (subst (list '= (list rx-phi 'am_) 'lv_))
                (rfl))
               ((eq? (car h) 'FORALL)
                (let* ((landed (dk-landed (lambda () (di))))
                       (y (cadr (car landed)))
                       (gy (list 'gm_ y))
                       (cf (list rx-phi gy))
                       (u (list '- y RX-FA))
                       (v (list '- gy 'am_)))
                  (rx-beta!)
                  (dk-deepest (lambda () (inst+ rx-aph y)))
                  (subst (list '= (list rx-h y) cf))
                  (subst (list '= (list 'gm_ RX-FA) 'am_))
                  (fact 'fun-apply-type-c 'gm_ 'RR 'RR y)
                  (fact 'fun-apply-type-c rx-phi 'RR 'RR gy)
                  (fact 'rr-sub-in-rr y RX-FA)
                  (fact 'rr-sub-in-rr gy 'am_)
                  (dk-deepest (lambda () (inst+ rx-nz y)))
                  (have! (list '= u (list '* cf v))
                    (lambda ()
                      (dk-deepest (lambda () (inst+ rx-idphi gy)))
                      (dk-deepest (lambda () (inst+ RX-FG y)))
                      (have! (list '= u (list '- (list 'fm_ gy) RX-FA))
                        (lambda () (subst (list '= (list 'fm_ gy) y)) (rfl)))
                      (subst (list '= u (list '- (list 'fm_ gy) RX-FA)))
                      (ass)))
                  (fact 'rr-recip-solve cf u v)
                  (ass)))
               (else (ass)))))))
       (ass))))))
(rx-check 'deriv-right-inverse)
(qed 'deriv-right-inverse)
(topic! 'deriv-right-inverse 'analysis)
(alias! 'deriv-right-inverse
        "the derivative of a right inverse"
        "inverse function theorem, derivative form, without the global left inverse")

;;; =====================================================================
;;; 17.  R-EXP' = R-EXP.
;;;
;;; Two variables: in IS-DIFF-AT(exp, y, exp(y)) the point and the derivative
;;; VALUE are built from the same variable, and `subst' rewrites the whole goal,
;;; so neither can be rewritten without damaging the other.  Carrying the point
;;; as a separate w pinned by w = log c makes the two substitutions independent.
;;; =====================================================================

(sp (make-wff (forall-guarded '(c_ w_) (list '(IN c_ RR) '(IN w_ RR))
  (list 'IMPLIES '(< 0 c_)
    (list 'IMPLIES '(= w_ (LOG c_))
      (list 'IS-DIFF-AT RX-EXPLAM 'w_ 'c_))))))
(quietly (lambda ()
  (rx-peel!)
  (fact 'rr-zero-in)
  (fact 'log-in-rr 'c_)
  (fact 'rr-pos-ne-zero 'c_)
  (fact 'recip-star-in-rr 'c_)
  (fact 'recip-star-value 'c_)
  (fact 'rr-recip-pos 'c_)
  (have! '(< 0 (RECIP-STAR c_))
    (lambda () (subst '(= (RECIP-STAR c_) (recip c_))) (ass)))
  (fact 'rr-pos-ne-zero '(RECIP-STAR c_))
  (fact 'log-deriv 'c_)
  (fact 'r-exp-lam-in-fun)
  ;; the RIGHT inverse relation, GLOBAL: log(exp z) = z at every real z
  (have! (list 'FORALL 'z_ (list 'IMPLIES '(IN z_ RR)
                (list '= (list RX-LOGLAM (list RX-EXPLAM 'z_)) 'z_)))
    (lambda () (di) (fact 'r-exp-in-rr 'z_) (rx-beta!) (fact 'log-r-exp 'z_) (ass)))
  ;; ... and the ONE instance of the left one the argument needs
  (have! (list '= (list RX-EXPLAM (list RX-LOGLAM 'c_)) 'c_)
    (lambda () (rx-beta!) (fact 'r-exp-log 'c_) (ass)))
  (have! (list '= (list RX-LOGLAM 'c_) '(LOG c_)) (lambda () (rx-beta!) (rfl)))
  (have! (list 'IS-CONTINUOUS-AT 'RR-MS 'RR-MS RX-EXPLAM (list RX-LOGLAM 'c_))
    (lambda () (subst (list '= (list RX-LOGLAM 'c_) '(LOG c_)))
               (fact 'r-exp-continuous-at '(LOG c_)) (ass)))
  (fact 'deriv-right-inverse RX-LOGLAM RX-EXPLAM 'c_ '(RECIP-STAR c_))
  (fact 'rr-recip-recip-pos 'c_)
  (have! '(= (recip (RECIP-STAR c_)) c_)
    (lambda () (subst '(= (RECIP-STAR c_) (recip c_))) (ass)))
  (fact 'eq-sym '(recip (RECIP-STAR c_)) 'c_)
  (have! (list '= 'w_ (list RX-LOGLAM 'c_))
    (lambda () (subst (list '= (list RX-LOGLAM 'c_) '(LOG c_))) (ass)))
  ;; the VALUE first, while the point is still the bare w
  (subst '(= c_ (recip (RECIP-STAR c_))))
  (subst (list '= 'w_ (list RX-LOGLAM 'c_)))
  (ass)))
(rx-check 'r-exp-diff-at-log)
(qed 'r-exp-diff-at-log)
(topic! 'r-exp-diff-at-log 'analysis)
(alias! 'r-exp-diff-at-log "the exponential is differentiable at log c with derivative c")

;; the bound variable is t_, NOT y_: RX-EXPLAM's own binder is y_, and a
;; universal spelled the same way SHADOWS it inside the lambda -- invisible on
;; screen, and exactly what `case-fold-audit' is for.
(sp (make-wff (forall-guarded 't_ '(IN t_ RR)
      (list 'IS-DIFF-AT RX-EXPLAM 't_ '(R-EXP t_)))))
(quietly (lambda ()
  (rx-peel!)
  (fact 'rr-zero-in)
  (fact 'r-exp-in-rr 't_) (fact 'r-exp-pos 't_) (fact 'log-r-exp 't_)
  (fact 'eq-sym '(LOG (R-EXP t_)) 't_)
  (fact 'r-exp-diff-at-log '(R-EXP t_) 't_)
  (ass)))
(rx-check 'r-exp-deriv)
(qed 'r-exp-deriv)
(topic! 'r-exp-deriv 'analysis)
(alias! 'r-exp-deriv "the exponential is its own derivative" "exp' = exp")
