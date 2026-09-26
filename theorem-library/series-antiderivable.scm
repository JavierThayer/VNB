;;; series-antiderivable.scm -- A FINITE SUM OF ANTIDERIVABLE TERMS IS
;;; ANTIDERIVABLE, and the vocabulary that makes such a statement usable.
;;;
;;; Proposition 4.8 (antiderivative.scm) says the antiderivable functions on
;;; [a,b] form a VECTOR SPACE: `antiderivable-add' and `antiderivable-scale',
;;; both `modulo 0'.  A vector space is closed under FINITE sums, and a
;;; SERIES-PARTIAL-SUM is a finite sum.  That is all this file is: the induction
;;; that turns the two-term closure into an n-term closure, plus the four small
;;; pieces the induction needs to be writable.
;;;
;;; WHY THIS IS NOT A THEOREM ABOUT POLYNOMIALS.  `poly-is-antiderivable'
;;; (antiderivative.scm, Example 4.7) concludes about
;;;
;;;     x |-> SERIES-PARTIAL-SUM( k |-> cf(k) x^k, m )
;;;
;;; and its proof exhibits the antiderivative in closed form, term by term.  The
;;; SUM STRUCTURE, not the monomial, is what makes it work: nothing in the
;;; argument needs the summand to be a monomial, only that each summand is
;;; antiderivable.  `series-partial-sum-antiderivable' below is that statement,
;;; and `poly-is-antiderivable' is one instance of it.  Two agents reported the
;;; Bernstein polynomials "blocked on converting BERNSTEIN-POLY into the
;;; coefficient-lambda shape" -- a binomial expansion of (1-x)^(n-l) plus a
;;; re-index of a double sum, neither of which exists in this tree.  There is
;;; nothing to convert: BERNSTEIN-POLY is already a SERIES-PARTIAL-SUM, and the
;;; only question is whether its summand is antiderivable.
;;;
;;; THE FIVE PIECES, in dependency order.
;;;
;;;  1. `antiderivable-fn-in-fun' -- the projection.  IS-ANTIDERIVABLE is an
;;;     existential over IS-ANTIDERIVATIVE, whose first conjunct types the
;;;     integrand; `antiderivative-fn-in-fun' is the same projection one level
;;;     down.  Needed because every transfer below asks for FUN(RR,RR)
;;;     membership of a map only known to be antiderivable.
;;;
;;;  2. `antiderivative-integrand-transfer' / `antiderivable-integrand-transfer'
;;;     -- a map agreeing POINTWISE with an antiderivable map is antiderivable.
;;;     This is the piece the vector-space route cannot do without, and it is
;;;     the CHEAP transfer: the ANTIDERIVATIVE f is untouched, only the value
;;;     phi(th) inside IS-DIFF-AT(f, th, phi(th)) moves, and equal values
;;;     substitute.  (Contrast `diff-transfer-ptwise-eq', which moves the
;;;     differentiated map and has to rebuild the Caratheodory factorization.)
;;;     Every conclusion of Prop 4.8 is about a LITERAL lambda -- `x |-> phi(x)
;;;     + psi(x)' -- so without a transfer the algebra can only ever conclude
;;;     about lambdas it built itself, and an induction cannot be written at
;;;     all.  Same mechanism, same reason, as `cont-transfer-ptwise-eq'.
;;;
;;;     RELATION TO `antiderivative-transfer-ptwise-eq' (antiderivative-transfer.scm,
;;;     which loads immediately above).  That theorem moves BOTH slots of Def 4.6 --
;;;     the antiderivative AND the integrand -- and asks for STRICT `=' in each.
;;;     `antiderivative-integrand-transfer' is its f = g case with the hypothesis
;;;     weakened to `=='.  The weakening is not cosmetic: every pointwise equation
;;;     this induction produces comes out of `lam-b' and `qrfl', which hand you `=='
;;;     and not `=', and upgrading would cost a definedness argument in each of the
;;;     four lanes.  The IS-ANTIDERIVABLE-level statement is not in that file at
;;;     all, and it is the one the induction actually cites.
;;;
;;;  3. `antiderivable-from-deriv' -- the packaging.  A map differentiable at
;;;     every real, with derivative phi(x) there, makes phi antiderivable on
;;;     every [a,b].  Def 4.6's continuity clause is FREE
;;;     (`diff-implies-continuous'), and its derivative clause is the hypothesis
;;;     restricted to (a,b).  This is `poly-is-antiderivable''s driver with the
;;;     polynomial taken out of it; it is what makes a base case one line.
;;;
;;;  4. `zero-is-antiderivable' -- the base case.  SERIES-PARTIAL-SUM(f,0) is 0
;;;     (`series-partial-sum-zero'), and the zero map is its own antiderivative
;;;     (`deriv-const' at c = 0).
;;;
;;;  5. `series-partial-sum-antiderivable' -- the induction.  Peel with
;;;     `series-partial-sum-succ', add with `antiderivable-add', transfer.
;;;
;;; and then `power-antiderivable' -- x |-> x^l is antiderivable -- which is the
;;; m = 0 base of the Bernstein term induction and, on its own, the honest
;;; one-line statement of Example 4.7's content.
;;;
;;; STATED IN TRANSFER FORM.  The conclusion is about a map `ph_' constrained
;;; only by a pointwise `==' to the partial sum, not about the literal partial-sum
;;; lambda.  A caller whose object is a def-functoid -- BERNSTEIN-POLY is -- gets
;;; the equation from the functoid's own unfold macete and never has to make its
;;; term literally equal to anything.  Same design, and the same reason, as
;;; series-linearity.scm's four pointwise laws.
;;;
;;; Needs: antiderivative (Def 4.6, Prop 4.8, the projections),
;;; comparison-test-proof (series-partial-sum-zero/-succ), series-linearity
;;; (series-partial-sum-in-rr-ptwise), differentiation (deriv-const,
;;; diff-implies-continuous), poly-antiderivative (deriv-anti-monomial),
;;; continuity-basics (const-lam-in-fun), ccint-basics (ccint-membership),
;;; fun-apply-type-proof (fun-apply-type-c), dyadic-weights (power-closed-at),
;;; driver-kit.
;;; =====================================================================

;;; ---- file-local driver helpers (the `sa-' prefix) --------------------

;; split every AND leaf to exhaustion: `di' takes one level per call and Def 4.6
;; is a seven-conjunct definition.
(define (sa-split-goal!)
  (let loop ((fuel 12))
    (let ((ands (filter (lambda (nd) (eq? (car (dk-goal-of nd)) 'AND)) (proof-leaves))))
      (if (and (pair? ands) (> fuel 0))
          (begin (for-each (lambda (nd) (dk-focus! nd) (di)) ands) (loop (- fuel 1)))
          #t))))

;; peel a guarded universal, returning the eigenvariable of the guard it landed
(define (sa-di-var!) (cadr (car (dk-landed (lambda () (di))))))

;; (IN t RR) off a CCINT membership WITHOUT destroying the membership: `mac-h'
;; replaces the hypothesis it unfolds, so the unfold happens in a `have!' lane.
(define (sa-rr-of! v lo hi)
  (have! (list 'IN v 'RR)
    (lambda () (mac-h 'ccint-membership (list 'IN v (list 'CCINT lo hi))) (prop))))

;; the two universals of Def 4.6 have the same FORALL/IMPLIES head and are told
;; apart on the head of the CONSEQUENT, never by position in the context.
(define (sa-univ head)
  (or (any-pred (lambda (z) (and (pair? z) (eq? (car z) 'FORALL) (dk-contains? z head)))
                (dk-asms))
      (error "series-antiderivable: no universal mentioning" head)))

;; ... and the two universal GOALS the same way: a CCINT membership guards the
;; continuity clause, a three-way AND the derivative clause.
(define (sa-continuity-clause? gl)
  (eq? (car (cadr (caddr gl))) 'IN))

;; a silent no-op leaves every later command in the wrong branch, so each proof
;; is checked before its `qed' -- which would report it anyway, but not by name.
(define (sa-check name)
  (if (not (proof-done? *ps*))
      (error "series-antiderivable: proof did not close" name
             (expression->string (dk-goal)))))

;; the summand family of the partial sum: k_ |-> (s k_)(x)
(define (sa-term-lam s x) (list 'VNB-LAMBDA 'j_ 'NN (list (list s 'j_) x)))
;; ... and the partial sum itself at n
(define (sa-sps s x n) (list 'SERIES-PARTIAL-SUM (sa-term-lam s x) n))

(define sa-zero-lam '(VNB-LAMBDA x RR 0))

;; (IN (* u v) RR) -- rr-mul-closed's antecedent is an AND, which `fact' will
;; not split, so the conjunction is landed immediately before the citation.
(define (sa-mul! u v)
  (have! (list 'AND (list 'IN u 'RR) (list 'IN v 'RR)))
  (fact 'rr-mul-closed u v))

;; everything recip(succ k) needs: succ k is a natural, hence a real, and it is
;; nonzero.  (poly-antiderivative.scm's `pa-recip-succ!', which is file-local
;; there; only the typing half is wanted here.)
(define (sa-recip-succ! k)
  (fact 'nn-succ-closed k)
  (fact 'nn-in-rr (list 'succ k))
  (fact 'nn-succ-nonzero k)
  (have! (list 'AND (list 'IN (list 'succ k) 'RR)
                    (list 'NOT (list '= (list 'succ k) 0))))
  (fact 'rr-recip-closed (list 'succ k)))

;; LUTINS instantiation (2026-09-18).  `antiderivable-fn-in-fun' is the theorem
;; that types an antiderivable map -- but CITING it at a compound term t (here
;; `(s_ k)', an application of the family variable) instantiates a universal AT
;; t, which now owes the side sequent `t = t'.  Nothing in the context certifies
;; an application of an untyped function, and the typing we are after is the one
;; that would certify it: citing the theorem cannot be the way in.
;;
;; The UNFOLD is.  `mac-h' rewrites a hypothesis by the defining IFF and `ai'
;; splits what it lands -- neither is a forall-elim, so neither owes anything --
;; and `(IN t (FUN RR RR))' is the second conjunct of Def 4.6 under the
;; existential.  This is `antiderivable-fn-in-fun's own proof (section 1),
;; inlined at a term the citation cannot reach.
(define (sa-ad-in-fun! t a b)
  (let ((claim (list 'IN t '(FUN RR RR))))
    (if (not (member claim (dk-asms)))
        (have! claim
          (lambda ()
            (mac-h 'IS-ANTIDERIVABLE (list 'IS-ANTIDERIVABLE t a b))
            (dk-ai-head! 'FORSOME)
            (dk-split-all!
             (dk-landed* (lambda ()
               (mac-h 'IS-ANTIDERIVATIVE
                      (car (filter (dk-head? 'IS-ANTIDERIVATIVE) (dk-asms)))))))
            (ass))))
    claim))

;;; =====================================================================
;;; 1.  THE PROJECTION.  IS-ANTIDERIVABLE(phi,a,b) types phi.
;;; =====================================================================

(quietly (lambda ()
  (sp (make-wff (forall-guarded '(phi a b) (list '(IS-ANTIDERIVABLE phi a b))
                  '(IN phi (FUN RR RR)))))
  (dk-peel-to! 'IN)
  (mac-h 'IS-ANTIDERIVABLE '(IS-ANTIDERIVABLE phi a b))
  (dk-ai-head! 'FORSOME)
  (let ((w (cadr (car (filter (dk-head? 'IS-ANTIDERIVATIVE) (dk-asms))))))
    (fact 'antiderivative-fn-in-fun w 'phi 'a 'b)
    (ass))))
(sa-check 'antiderivable-fn-in-fun)
(qed 'antiderivable-fn-in-fun)
(topic! 'antiderivable-fn-in-fun 'analysis)
(alias! 'antiderivable-fn-in-fun "an antiderivable map is a map RR -> RR")

;;; =====================================================================
;;; 2.  THE INTEGRAND TRANSFER.
;;;
;;; Def 4.6 mentions the integrand phi in exactly one place -- the VALUE slot of
;;; IS-DIFF-AT(f, th, phi(th)) -- and `subst' at th is the whole proof.  The
;;; continuity clause is about f and is copied across untouched.
;;;
;;; The hypothesis is `==' (quasi-equality), not `=': that is the WEAKER
;;; hypothesis, hence the stronger theorem, and it is what a beta law hands you.
;;; The conclusion's own (IN psi (FUN RR RR)) makes psi total on RR, so on RR the
;;; two readings coincide.  (Same choice, for the same reason, as
;;; `diff-transfer-ptwise-eq'.)
;;; =====================================================================

(define sa-pw-eq '(FORALL x_ (IMPLIES (IN x_ RR) (== (psi x_) (phi x_)))))

(quietly (lambda ()
  (sp (make-wff
        (forall-guarded '(f phi psi a b)
          (list '(IN psi (FUN RR RR)) '(IS-ANTIDERIVATIVE f phi a b) sa-pw-eq)
          '(IS-ANTIDERIVATIVE f psi a b))))
  (dk-peel-to! 'IS-ANTIDERIVATIVE)
  (dk-split! (dk-landed-1
               (lambda () (mac-h 'IS-ANTIDERIVATIVE '(IS-ANTIDERIVATIVE f phi a b)))))
  (let ((cf (sa-univ 'IS-CONTINUOUS-AT))
        (df (sa-univ 'IS-DIFF-AT)))
    (mac 'IS-ANTIDERIVATIVE)
    (sa-split-goal!)
    (for-each
     (lambda (nd)
       (dk-focus! nd)
       (let ((gl (dk-goal)))
         (cond
           ((memq (car gl) '(IN <)) (ass))
           ((sa-continuity-clause? gl)
            (let ((v (sa-di-var!))) (inst+ cf v) (ass)))
           (else
            (di)
            (dk-split! (dk-landed-1 (lambda () (di))))
            (let ((v (caddr (dk-goal))))
              ;; `inst+' will not split a CONJUNCTIVE antecedent, and `dk-split!'
              ;; has just taken the guard apart, so the AND is put back before
              ;; the derivative universal is instantiated -- otherwise the
              ;; citation lands the IMPLICATION, silently.
              (have! (list 'AND (list 'IN v 'RR)
                                (list 'AND (list '< 'a v) (list '< v 'b))))
              (inst+ df v)
              (inst+ sa-pw-eq v)
              (subst (list '== (list 'psi v) (list 'phi v)))
              (ass))))))
     (proof-leaves)))))
(sa-check 'antiderivative-integrand-transfer)
(qed 'antiderivative-integrand-transfer)
(topic! 'antiderivative-integrand-transfer 'analysis)
(alias! 'antiderivative-integrand-transfer
        "an antiderivative of phi is an antiderivative of any map agreeing with phi pointwise")

;;; ... and the same statement one level up, in IS-ANTIDERIVABLE.
(quietly (lambda ()
  (sp (make-wff
        (forall-guarded '(phi psi a b)
          (list '(IN psi (FUN RR RR)) '(IS-ANTIDERIVABLE phi a b) sa-pw-eq)
          '(IS-ANTIDERIVABLE psi a b))))
  (dk-peel-to! 'IS-ANTIDERIVABLE)
  (mac-h 'IS-ANTIDERIVABLE '(IS-ANTIDERIVABLE phi a b))
  (let ((fv (cadr (car (dk-landed* (lambda () (dk-ai-head! 'FORSOME)))))))
    (mac 'IS-ANTIDERIVABLE)
    (ew fv)
    (fact 'antiderivative-integrand-transfer fv 'phi 'psi 'a 'b)
    (ass))))
(sa-check 'antiderivable-integrand-transfer)
(qed 'antiderivable-integrand-transfer)
(topic! 'antiderivable-integrand-transfer 'analysis)
(alias! 'antiderivable-integrand-transfer
        "a map agreeing pointwise with an antiderivable map is antiderivable")

;;; =====================================================================
;;; 3.  ANTIDERIVABLE FROM A GLOBAL DERIVATIVE.
;;;
;;; This is `poly-is-antiderivable''s driver with the polynomial removed.  Def
;;; 4.6's clause (1) is free: a map differentiable at a point is continuous
;;; there, so `diff-implies-continuous' discharges it from the SAME citation
;;; that discharges clause (3).  The one mechanical point is that clause (1) is
;;; tested at points of CCINT(a,b) while the hypothesis is stated at points of
;;; RR, so a CCINT membership has to be read down to an RR membership -- inside
;;; a `have!' lane, because `mac-h' would consume the membership itself.
;;; =====================================================================

(define sa-global-deriv '(FORALL x_ (IMPLIES (IN x_ RR) (IS-DIFF-AT f x_ (phi x_)))))

(quietly (lambda ()
  (sp (make-wff
        (forall-guarded '(f phi a b)
          (list '(IN f (FUN RR RR)) '(IN phi (FUN RR RR))
                '(AND (IN a RR) (AND (IN b RR) (< a b)))
                sa-global-deriv)
          '(IS-ANTIDERIVABLE phi a b))))
  (dk-peel-to! 'IS-ANTIDERIVABLE)
  (dk-split! '(AND (IN a RR) (AND (IN b RR) (< a b))))
  (mac 'IS-ANTIDERIVABLE)
  (ew 'f)
  (mac 'IS-ANTIDERIVATIVE)
  (sa-split-goal!)
  (for-each
   (lambda (nd)
     (dk-focus! nd)
     (let ((gl (dk-goal)))
       (cond
         ((memq (car gl) '(IN <)) (ass))
         ((sa-continuity-clause? gl)
          (let ((v (sa-di-var!)))
            (sa-rr-of! v 'a 'b)
            (inst+ sa-global-deriv v)
            (fact 'diff-implies-continuous 'f v (list 'phi v))
            (ass)))
         (else
          (di)
          (dk-split! (dk-landed-1 (lambda () (di))))
          (let ((v (caddr (dk-goal))))
            (inst+ sa-global-deriv v)
            (ass))))))
   (proof-leaves))))
(sa-check 'antiderivable-from-deriv)
(qed 'antiderivable-from-deriv)
(topic! 'antiderivable-from-deriv 'analysis)
(alias! 'antiderivable-from-deriv
        "a map with a global derivative phi makes phi antiderivable on every [a,b]")

;;; =====================================================================
;;; 4.  THE ZERO MAP IS ANTIDERIVABLE.  Its own antiderivative: deriv-const at
;;; c = 0 says d/dx 0 = 0.
;;; =====================================================================

(quietly (lambda ()
  (sp (make-wff
        (forall-guarded '(a b) (list '(AND (IN a RR) (AND (IN b RR) (< a b))))
          (list 'IS-ANTIDERIVABLE sa-zero-lam 'a 'b))))
  (dk-peel-to! 'IS-ANTIDERIVABLE)
  (fact 'rr-zero-in)
  (fact 'const-lam-in-fun 0)
  (have! (list 'FORALL 'x_ (list 'IMPLIES '(IN x_ RR)
               (list 'IS-DIFF-AT sa-zero-lam 'x_ (list sa-zero-lam 'x_))))
    (lambda ()
      (let ((v (sa-di-var!)))
        (have! (list 'AND '(IN 0 RR) (list 'IN v 'RR)))
        (fact 'deriv-const 0 v)
        (lam-b)
        (ass))))
  (fact 'antiderivable-from-deriv sa-zero-lam sa-zero-lam 'a 'b)
  (ass)))
(sa-check 'zero-is-antiderivable)
(qed 'zero-is-antiderivable)
(topic! 'zero-is-antiderivable 'analysis)
(alias! 'zero-is-antiderivable "the zero map is antiderivable on every [a,b]")

;;; =====================================================================
;;; 5.  THE THEOREM.  A SERIES-PARTIAL-SUM whose every summand is antiderivable
;;; is antiderivable.
;;;
;;;   ph_(x) == sum_{j<n} (s_ j)(x)  for every real x,  each (s_ j) antiderivable
;;;   ==>  ph_ antiderivable on [a,b]
;;;
;;; Induction on n.  Base: the empty sum is 0 (`series-partial-sum-zero') and
;;; the zero map is antiderivable.  Step: `series-partial-sum-succ' peels the
;;; last term, `antiderivable-add' (Prop 4.8) adds it, and the integrand
;;; transfer carries the conclusion off the literal lambda that Prop 4.8 builds
;;; and onto ph_.
;;;
;;; THE INDUCTION VARIABLE IS OUTERMOST: `ni' tests the goal's SHAPE literally,
;;; and one greedy `di' would take s_, ph_, a and b with it, after which the
;;; induction is gone.
;;;
;;; The summand family is POINTWISE-typed -- `forall j in NN. (s_ j) is
;;; antiderivable' -- rather than `s_ in FUN(NN, FUN(RR,RR))'.  That is what an
;;; induction over an initial NN segment ever uses, it is what a caller whose
;;; family is a lambda can discharge by `lam-b' alone, and FUN membership would
;;; additionally cost a `lam-t' (two leaves, one of them a sethood).  Same
;;; choice, and the same reason, as series-linearity.scm's four laws.
;;; =====================================================================

(define sa-guard '(AND (IN a RR) (AND (IN b RR) (< a b))))

;;; THE GUARD IS NEVER SPLIT IN THIS PROOF, and that is deliberate.  Every
;;; citation the induction makes -- `zero-is-antiderivable', the IH itself --
;;; carries the nondegeneracy of [a,b] as ONE conjunctive antecedent, and `fact'
;;; / `inst+' will not split a conjunctive antecedent: fed the three conjuncts
;;; they land the IMPLICATION, silently, and the proof fails several steps
;;; later at an `ass' that reads like a different bug.  `dk-split!' is
;;; destructive (`ai' REPLACES the conjunction by its conjuncts), so splitting
;;; the guard once, early, breaks every later citation.  Nothing here wants the
;;; conjuncts separately, so it is simply not split.
(define sa-terms-ad
  '(FORALL j_ (IMPLIES (IN j_ NN) (IS-ANTIDERIVABLE (s_ j_) a b))))
(define (sa-transfer-hyp n)
  (list 'FORALL 'x_ (list 'IMPLIES '(IN x_ RR)
        (list '== '(ph_ x_) (sa-sps 's_ 'x_ n)))))
(define (sa-inner n)
  (forall-guarded '(s_ ph_ a b)
    (list sa-guard '(IN ph_ (FUN RR RR)) sa-terms-ad (sa-transfer-hyp n))
    '(IS-ANTIDERIVABLE ph_ a b)))

;; `inst+' takes ONE term, and a four-binder universal wants four calls with the
;; intermediate formula captured each time: `dk-deepest' takes the landing no
;; other landing contains, which is the one the next call must instantiate.
(define (sa-inst-chain! f terms)
  (let loop ((cur f) (ts terms))
    (if (null? ts) cur
        (loop (dk-deepest (lambda () (inst+ cur (car ts)))) (cdr ts)))))

;; the pointwise-real typing `series-partial-sum-in-rr-ptwise' asks of the
;; summand family, discharged from the antiderivability of each term
(define (sa-summand-real! s v)
  (have! (list 'FORALL 'k_ (list 'IMPLIES '(IN k_ NN)
               (list 'IN (list (sa-term-lam s v) 'k_) 'RR)))
    (lambda ()
      (let ((kk (sa-di-var!)))
        (lam-b)
        (inst+ sa-terms-ad kk)
        (sa-ad-in-fun! (list s kk) 'a 'b)
        (fact 'fun-apply-type-c (list s kk) 'RR 'RR v)
        (ass)))))

(quietly (lambda ()
  (sp (make-wff (list 'FORALL 'n_ (list 'IMPLIES '(IN n_ NN) (sa-inner 'n_)))))
  (let* ((br (use-induction))
         (n  (cdr (assq 'var br)))
         (ih (cdr (assq 'ih  br))))

    ;; ---- BASE: the empty sum is the zero map --------------------------
    (dk-focus! (cdr (assq 'base br)))
    (dk-peel-to! 'IS-ANTIDERIVABLE)
    (fact 'zero-is-antiderivable 'a 'b)
    (have! (list 'FORALL 'x_ (list 'IMPLIES '(IN x_ RR)
                 (list '== '(ph_ x_) (list sa-zero-lam 'x_))))
      (lambda ()
        (let ((v (sa-di-var!)))
          (lam-b)                                   ; (lam x. 0)(v) -> 0
          (inst+ (sa-transfer-hyp 0) v)             ; ph_(v) == SPS(term, 0)
          (fact 'series-partial-sum-zero (sa-term-lam 's_ v))
          (subst (list '== (list 'ph_ v) (sa-sps 's_ v 0)))
          (ass))))
    (fact 'antiderivable-integrand-transfer sa-zero-lam 'ph_ 'a 'b)
    (ass)

    ;; ---- STEP ---------------------------------------------------------
    (dk-focus! (cdr (assq 'step br)))
    (dk-peel-to! 'IS-ANTIDERIVABLE)
    (let* ((phi0 (list 'VNB-LAMBDA 'w_ 'RR (sa-sps 's_ 'w_ n)))
           (big  (list 'VNB-LAMBDA 'x 'RR
                       (list '+ (list phi0 'x) (list (list 's_ n) 'x)))))
      ;; (1) the partial sum at n IS a map RR -> RR.  `lam-t' opens TWO leaves:
      ;; the pointwise typing and the SETHOOD of the domain.
      (have! (list 'IN phi0 '(FUN RR RR))
        (lambda ()
          (for-each
           (lambda (leaf)
             (dk-focus! leaf)
             (if (eq? (car (dk-goal)) 'FORALL)
                 (let ((v (sa-di-var!)))
                   (sa-summand-real! 's_ v)
                   (fact 'series-partial-sum-in-rr-ptwise n (sa-term-lam 's_ v))
                   (ass))
                 (begin (fact 'rr-is-set) (ass))))
           (dk-opened (lambda () (lam-t))))))
      ;; (2) ... and it satisfies the IH's transfer hypothesis, by beta alone.
      (have! (list 'FORALL 'x_ (list 'IMPLIES '(IN x_ RR)
                   (list '== (list phi0 'x_) (sa-sps 's_ 'x_ n))))
        (lambda () (sa-di-var!) (lam-b) (qrfl)))
      ;; (3) the IH at (s_, phi0, a, b)
      (sa-inst-chain! ih (list 's_ phi0 'a 'b))
      ;; (4) the last term is antiderivable, and Prop 4.8 adds it
      (inst+ sa-terms-ad n)
      ;; LUTINS: antiderivable-add is instantiated AT (s_ n), so type it first.
      (sa-ad-in-fun! (list 's_ n) 'a 'b)
      (fact 'antiderivable-add phi0 (list 's_ n) 'a 'b)
      ;; (5) ... and the transfer moves that conclusion onto ph_.
      (have! (list 'FORALL 'x_ (list 'IMPLIES '(IN x_ RR)
                   (list '== '(ph_ x_) (list big 'x_))))
        (lambda ()
          (let ((v (sa-di-var!)))
            (lam-b)                                  ; big(v) -> phi0(v) + (s_ n)(v)
            (lam-b)                                  ; phi0(v) -> SPS(term, n)
            (inst+ (sa-transfer-hyp (list 'succ n)) v)
            (subst (list '== (list 'ph_ v) (sa-sps 's_ v (list 'succ n))))
            ;; series-partial-sum-succ is guarded on its two arguments being
            ;; real since 2026-08-29.  `sa-summand-real!' establishes the
            ;; POINTWISE realness of the summand family -- which is the form this
            ;; file works in throughout -- and the two instances follow from it.
            (sa-summand-real! 's_ v)
            (fact 'series-partial-sum-in-rr-ptwise n (sa-term-lam 's_ v))
            (dk-have! (list 'IN (list (sa-term-lam 's_ v) n) 'RR)
              (lambda () (lam-b) (inst+ sa-terms-ad n)
                         (fact 'antiderivable-fn-in-fun (list 's_ n) 'a 'b)
                         (fact 'fun-apply-type-c (list 's_ n) 'RR 'RR v)
                         (ass)))
            (fact 'series-partial-sum-succ (sa-term-lam 's_ v) n)
            (subst (list '== (sa-sps 's_ v (list 'succ n))
                             (list '+ (sa-sps 's_ v n)
                                      (list (sa-term-lam 's_ v) n))))
            (lam-b)                                  ; term(n) -> (s_ n)(v)
            (qrfl))))
      (fact 'antiderivable-integrand-transfer big 'ph_ 'a 'b)
      (ass)))))
(sa-check 'series-partial-sum-antiderivable)
(qed 'series-partial-sum-antiderivable)
(topic! 'series-partial-sum-antiderivable 'analysis)
(alias! 'series-partial-sum-antiderivable
        "a finite sum of antiderivable terms is antiderivable")

;;; =====================================================================
;;; 6.  THE MONOMIAL.  x |-> x^m is antiderivable on every [a,b] --
;;; `deriv-anti-monomial' at coefficient 1, packaged by
;;; `antiderivable-from-deriv'.
;;;
;;; This is Example 4.7's content in one statement, and it is the m = 0 base of
;;; the Bernstein term induction  x^l (1-x)^m.
;;; =====================================================================

(define sa-pow-lam '(VNB-LAMBDA x RR (power x m_)))
(define sa-pow-anti
  '(VNB-LAMBDA x RR (* (* (recip (succ m_)) 1) (power x (succ m_)))))

(quietly (lambda ()
  (sp (make-wff (forall-guarded '(m_ a b) (list '(IN m_ NN) sa-guard)
                  (list 'IS-ANTIDERIVABLE sa-pow-lam 'a 'b))))
  (dk-peel-to! 'IS-ANTIDERIVABLE)
  (fact 'rr-one-in)
  (sa-recip-succ! 'm_)
  ;; the two maps are maps RR -> RR: pointwise typing plus the sethood of RR.
  (for-each
   (lambda (lam pt)
     (have! (list 'IN lam '(FUN RR RR))
       (lambda ()
         (for-each
          (lambda (leaf)
            (dk-focus! leaf)
            (if (eq? (car (dk-goal)) 'FORALL)
                (let ((v (sa-di-var!))) (pt v) (ass))
                (begin (fact 'rr-is-set) (ass))))
          (dk-opened (lambda () (lam-t)))))))
   (list sa-pow-lam sa-pow-anti)
   (list (lambda (v) (fact 'power-closed-at 'm_ v))
         (lambda (v)
           (sa-mul! '(recip (succ m_)) 1)
           (fact 'power-closed-at '(succ m_) v)
           (sa-mul! '(* (recip (succ m_)) 1) (list 'power v '(succ m_))))))
  (have! (list 'FORALL 'x_ (list 'IMPLIES '(IN x_ RR)
               (list 'IS-DIFF-AT sa-pow-anti 'x_ (list sa-pow-lam 'x_))))
    (lambda ()
      (let ((v (sa-di-var!)))
        (lam-b)                                     ; goal value -> power(v, m_)
        (fact 'power-closed-at 'm_ v)
        (fact 'deriv-anti-monomial 1 'm_ v)         ; value (* 1 power(v,m_))
        (have! (list '= (list 'power v 'm_) (list '* 1 (list 'power v 'm_)))
               (lambda () (crs)))
        (subst (list '= (list 'power v 'm_) (list '* 1 (list 'power v 'm_))))
        (ass))))
  (fact 'antiderivable-from-deriv sa-pow-anti sa-pow-lam 'a 'b)
  (ass)))
(sa-check 'power-antiderivable)
(qed 'power-antiderivable)
(topic! 'power-antiderivable 'analysis)
(alias! 'power-antiderivable "x |-> x^m is antiderivable on every [a,b]")

;;; =====================================================================
;;; 7.  EXAMPLE 4.7, DERIVED.
;;;
;;; `poly-is-antiderivable' (antiderivative.scm) is `series-partial-sum-
;;; antiderivable' at the family  j |-> (x |-> cf(j) x^j),  and this section is
;;; the derivation, written out.  It is here as EVIDENCE rather than as
;;; vocabulary: it says that section 5 really is the general theorem and that
;;; Example 4.7 carries no polynomial-specific content -- the closed-form
;;; antiderivative poly-antiderivative.scm builds, term by term, is not needed.
;;;
;;; Three steps, and they are the three ANY caller of section 5 takes:
;;;   (1) exhibit the family as a lambda and prove each of its values
;;;       antiderivable -- here `power-antiderivable' scaled by cf(j), with the
;;;       integrand transfer to cross from the literal term `antiderivable-scale'
;;;       builds to the reduced one;
;;;   (2) match the sum: `lam-b' reduces the family application UNDER the
;;;       partial sum's own binder (the beta walker threads the enclosing
;;;       VNB-LAMBDA, so j_ is typed there), leaving two alpha-variant lambdas
;;;       that `qrfl' closes;
;;;   (3) cite section 5.
;;; No reindexing, no coefficient shift, no expansion of any kind.
;;;
;;; Stated in the same transfer form as section 5, so it is STRONGER than
;;; `poly-is-antiderivable', which is its instance at ph_ = the literal
;;; polynomial lambda (the FUN(RR,RR) membership that instance needs is
;;; `poly-lam-in-fun', and the pointwise `==' is one `lam-b' and a `qrfl').
;;; =====================================================================

(define (sa-mono j)  (list 'VNB-LAMBDA 'x 'RR (list 'power 'x j)))
(define (sa-pterm j) (list 'VNB-LAMBDA 'x 'RR (list '* (list 'cf j) (list 'power 'x j))))
(define (sa-scaled j)
  (list 'VNB-LAMBDA 'x 'RR (list '* (list 'cf j) (list (sa-mono j) 'x))))
(define sa-pfam (list 'VNB-LAMBDA 'j_ 'NN (sa-pterm 'j_)))
(define (sa-polysum x n)
  (list 'SERIES-PARTIAL-SUM
        (list 'VNB-LAMBDA 'k_ 'NN (list '* (list 'cf 'k_) (list 'power x 'k_))) n))

(quietly (lambda ()
  (sp (make-wff
    (list 'FORALL 'n_ (list 'IMPLIES '(IN n_ NN)
      (forall-guarded '(cf ph_ a b)
        (list '(IN cf (FUN NN RR)) sa-guard '(IN ph_ (FUN RR RR))
              (list 'FORALL 'x_ (list 'IMPLIES '(IN x_ RR)
                    (list '== '(ph_ x_) (sa-polysum 'x_ 'n_)))))
        '(IS-ANTIDERIVABLE ph_ a b))))))
  (dk-peel-to! 'IS-ANTIDERIVABLE)
  ;; (1) every value of the family is antiderivable
  (have! (list 'FORALL 'j_ (list 'IMPLIES '(IN j_ NN)
               (list 'IS-ANTIDERIVABLE (list sa-pfam 'j_) 'a 'b)))
    (lambda ()
      (let ((jj (sa-di-var!)))
        (lam-b)                                        ; (sa-pfam jj) -> the term
        (fact 'fun-apply-type-c 'cf 'NN 'RR jj)
        (fact 'power-antiderivable jj 'a 'b)
        (fact 'antiderivable-scale (list 'cf jj) (sa-mono jj) 'a 'b)
        (have! (list 'IN (sa-pterm jj) '(FUN RR RR))
          (lambda ()
            (for-each
             (lambda (leaf)
               (dk-focus! leaf)
               (if (eq? (car (dk-goal)) 'FORALL)
                   (let ((v (sa-di-var!)))
                     (fact 'power-closed-at jj v)
                     (sa-mul! (list 'cf jj) (list 'power v jj))
                     (ass))
                   (begin (fact 'rr-is-set) (ass))))
             (dk-opened (lambda () (lam-t))))))
        (have! (list 'FORALL 'x_ (list 'IMPLIES '(IN x_ RR)
                     (list '== (list (sa-pterm jj) 'x_) (list (sa-scaled jj) 'x_))))
          (lambda () (sa-di-var!) (lam-b) (lam-b) (lam-b) (qrfl)))
        (fact 'antiderivable-integrand-transfer (sa-scaled jj) (sa-pterm jj) 'a 'b)
        (ass))))
  ;; (2) the polynomial sum IS the family's partial sum -- beta under the binder
  (have! (list 'FORALL 'x_ (list 'IMPLIES '(IN x_ RR)
               (list '== '(ph_ x_) (sa-sps sa-pfam 'x_ 'n_))))
    (lambda ()
      (let ((v (sa-di-var!)))
        (inst+ (list 'FORALL 'x_ (list 'IMPLIES '(IN x_ RR)
                     (list '== '(ph_ x_) (sa-polysum 'x_ 'n_)))) v)
        (subst (list '== (list 'ph_ v) (sa-polysum v 'n_)))
        (lam-b) (lam-b)
        (qrfl))))
  ;; (3) ... and section 5 concludes.
  (fact 'series-partial-sum-antiderivable 'n_ sa-pfam 'ph_ 'a 'b)
  (ass)))
(sa-check 'poly-fn-antiderivable)
(qed 'poly-fn-antiderivable)
(topic! 'poly-fn-antiderivable 'analysis)
(alias! 'poly-fn-antiderivable
        "Example 4.7, as an instance of the finite-sum theorem"
        "a map agreeing pointwise with a polynomial partial sum is antiderivable")
