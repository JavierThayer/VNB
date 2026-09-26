;;; dominated-convergence.scm -- DOMINATED CONVERGENCE, PROVEN, in two forms:
;;; for real series (the content) and in ELL-ONE (the statement the user asked
;;; for), together with the twenty limit / partial-sum / complex-magnitude
;;; lemmas the two are assembled from.
;;;
;;;   REAL FORM (`dominated-null-series'):
;;;     0 <= u_j(n) <= g(n) for all j,n,   Sum g converges,
;;;     u_j(n) -> 0 as j -> oo for each fixed n
;;;       =>   Sum_n u_j(n) -> 0 as j -> oo.
;;;
;;;   ELL-ONE FORM (`ell-one-dominated-convergence'):
;;;     x_j in SQN(CC),  |x_j(k)| <= a(k) with Sum a convergent,
;;;     x_j(k) -> x(k) in CC for each k
;;;       =>  x in ELL-ONE  and  ||x_j - x||_1 -> 0.
;;;
;;; The real form is the whole argument: split the sum at an index N chosen so
;;; that the TAIL of the dominating series is small (that is where summability
;;; of the dominator is spent), and kill the finite HEAD by pointwise
;;; convergence.  The ell^1 form is that theorem plus the complex packaging.
;;;
;;; ------------------------------------------------------------------
;;; WHAT WAS MISSING, AND HAD TO BE BUILT.  Four things, and each is a gap in
;;; the library rather than bookkeeping for this proof:
;;;
;;; 1. A FINITE MAX OVER A FAMILY -- the step the argument is supposed to need
;;;    for the head, and which the tree does not have.  IT IS NOT NEEDED.
;;;    `series-head-null' inducts on the head LENGTH, and each step is one
;;;    application of `rr-null-sum', whose own max is the binary MAX the tree
;;;    already has.  The mechanism dissolves the obligation; no family
;;;    operator was invented.
;;;
;;; 2. LIMIT UNIQUENESS.  The tree had none, for RR-MS or for a general metric
;;;    space -- so the sum of a series could not be NAMED: `iota-d'
;;;    (pi-iota-def!) posts existence AND uniqueness and only existence was
;;;    available.  `rr-limit-unique' supplies it, and with it SERIES-LIMIT(f) =
;;;    IOTA L. SERIES-CONVERGES-TO(f,L) is a defined term (`series-limit-in-rr').
;;;    That is the ell^1 norm; it is also the shape of the product metric's
;;;    D_w (structure-library/product-metric.scm), whose IOTA has the same
;;;    obligation and now has half of it discharged.
;;;
;;; 3. LINEARITY OF SERIES CONVERGENCE.  There was none -- no sum, no scalar
;;;    multiple.  It is unavoidable here: |x_j(k) - x(k)| is dominated by
;;;    a(k) + a(k) and by nothing smaller.  `series-converges-sum' proves the
;;;    NONNEGATIVE case, which needs no limit arithmetic: the partial sums add
;;;    (`series-partial-sum-add'), each summand's are bounded
;;;    (`series-partial-sum-bounded'), so the sum's are nondecreasing and
;;;    bounded and `monotone-convergence-rr' finishes.  The signed case wants
;;;    lim(f+g) = lim f + lim g and is NOT here.
;;;
;;; 4. THE CC-MS DISTANCE ON THE SURFACE.  `rr-ms-dist' exists precisely
;;;    because unfolding a metric predicate at RR-MS leaves ((DIST RR-MS) u v);
;;;    the same was true at CC-MS and nothing said so.  `cc-ms-dist' is the
;;;    five-line clone, and the three magnitude estimates beside it are the
;;;    complex counterparts of the `abs' lemmas rr-abs-basics already had.
;;;
;;; ------------------------------------------------------------------
;;; THREE DESIGN DECISIONS, and what each one buys.
;;;
;;; 1. THE SUMS ARE NAMED BY A SEQUENCE, NOT BY A DESCRIPTION.  The conclusion
;;;    of `dominated-null-series' is about a sequence `e' carrying the
;;;    hypothesis SERIES-CONVERGES-TO(u(j), e(j)) rather than about
;;;    SERIES-LIMIT(u(j)).  Both are available (L9 defines SERIES-LIMIT and
;;;    proves it is the limit), and the ell^1 statement does use SERIES-LIMIT
;;;    -- but the core theorem should not depend on a description operator
;;;    when the same content is available without one.
;;;
;;; 2. THE FAMILY IS UNGUARDED, WITH A POINTWISE TYPING HYPOTHESIS.  `u' ranges
;;;    over sequences of sequences; writing (IN u (FUN NN (FUN NN RR))) would
;;;    make every application site owe FUN-sethood and a lam-t over a function
;;;    space.  (FORALL j (IMPLIES (IN j NN) (IN (u j) (FUN NN RR)))) is the same
;;;    hypothesis with none of that.
;;;
;;; 3. EVERY SEQUENCE-VALUED CONCLUSION IS STATED IN TRANSFER FORM.
;;;    `rr-null-sum' does NOT conclude about (VNB-LAMBDA j NN (+ (f j) (g j)));
;;;    it concludes about any `h' with h(j) = f(j) + g(j) pointwise.  This is
;;;    the lesson of continuity-transfer.scm one lane over: a theorem that
;;;    concludes about the LITERAL term it builds can only ever be applied to
;;;    lambdas the prover built itself, and the induction in `series-head-null'
;;;    would then need a beta-reduction under a binder at every step.  In
;;;    transfer form the step is one `fact'.  `series-converges-sum' and
;;;    `cc-converges-magnitude-null' are stated the same way for the same
;;;    reason.
;;;
;;; ------------------------------------------------------------------
;;; WHAT IT COSTS.  Read the bills the qed lines print.  Fourteen of the
;;; twenty-two theorems are `modulo 0'; the residual debt of the two headline
;;; theorems is FOUR asserted facts and no more:
;;;
;;;   series-cauchy-criterion   (theorem-library/series-order-lemmas.scm) --
;;;     convergent implies Cauchy in RR-MS, the vanishing tail.  The one
;;;     genuinely un-discharged ANALYTIC fact here, and the obvious next
;;;     target: everything else it would need is now in this file.
;;;   nn-zero-le, nn-le-succ-cases  (structure-library/order-lemmas.scm) --
;;;     the NN order backlog, inherited by every induction in the series lane.
;;;   rr-le-all-pos-nonpos      (structure-library/order-predicates.scm) --
;;;     "x <= eps for every eps > 0 implies x <= 0", derivable from the
;;;     archimedean property since the arithmetic-base cleanup and left alone
;;;     on the ground that re-tiering moves every citing bill.
;;;
;;; Loads after theorem-library/comparison-test-proof (series-partial-sum-succ /
;;; -zero / -in-rr / -seq-in-fun, the partial-sum recurrence in the surface
;;; language and the comparison test), theorem-library/rr-max-basics +
;;; rr-min-basics (MAX and its order laws), theorem-library/rr-abs-basics,
;;; binary-minus-laws, nn-order-basics, order-lemmas, fun-apply-type-proof,
;;; rr-ms-dist, cc-magnitude, sqn and driver-kit.

;;; ---- file-local driver helpers (the `dn-' prefix) --------------------

(define (dn-and! closer)
  (let ((g (dk-goal)))
    (if (and (pair? g) (eq? (car g) 'AND))
        (for-each (lambda (k) (dk-focus! k) (dn-and! closer))
                  (dk-opened (lambda () (di))))
        (closer))))

;;; Select a hypothesis by CONTENT and ERROR on a miss.
(define (dn-find what pred)
  (let loop ((l (dk-asms)))
    (cond ((null? l) (error "dn-find: no context formula" what))
          ((pred (car l)) (car l))
          (else (loop (cdr l))))))

(define (dn-fvs forms) (apply append (map free-vars forms)))

;;; Skolemize a FORSOME already in the CONTEXT (`obtain' sees only what its own
;;; lane landed); the eigenvariable is read off by free-variable set difference.
(define (dn-skolem! ex)
  (let* ((fv0 (dn-fvs (dk-asms)))
         (landed (dk-landed (lambda () (ai ex)))))
    (for-each (lambda (f) (if (and (pair? f) (eq? (car f) 'AND)) (dk-split! f))) landed)
    (let ((fresh (filter (lambda (v) (not (memq v fv0))) (dn-fvs (dk-asms)))))
      (if (null? fresh) (error "dn-skolem!: nothing appeared" ex) (car fresh)))))

;;; `ineq' wants 1-based assumption indices, and premises are named ONE BY ONE.
(define (dn-idx form)
  (let loop ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "dn-idx: not in context" form))
          ((equal? (car l) form) i) (else (loop (cdr l) (+ i 1))))))
(define (dn-ineq . forms) (apply ineq (map dn-idx forms)))

;;; `di' until an ASSUMPTION lands: an UNGUARDED universal peels the quantifier
;;; and lands nothing, so loop on the LANDING, never on a `di' count.
(define (dn-di-landed!)
  (let loop ((n 0))
    (let ((new (dk-landed* (lambda () (di)))))
      (cond ((pair? new) new)
            ((> n 5) (error "dn-di-landed!: di landed no assumption"))
            (else (loop (+ n 1)))))))
(define (dn-di-landed-1!)
  (let ((new (dn-di-landed!)))
    (if (null? (cdr new)) (car new)
        (error "dn-di-landed-1!: expected 1" (map expression->string new)))))

;;; (IN x RR) from (POS-RR x), on a SIDE branch: `mac-h' is destructive and the
;;; main branch still wants POS-RR for later detachments.
(define (dn-pos-in-rr! x)
  (have! (list 'IN x 'RR)
    (lambda ()
      (mac-h 'pos-rr (list 'POS-RR x))
      (dk-split! (list 'AND (list 'IN x 'RR)
                       (list 'AND (list '<= 0 x) (list 'NOT (list '= 0 x)))))
      (ass))))

;;; ... and the (0 <= x) conjunct, the same way.
(define (dn-pos-nonneg! x)
  (have! (list '<= 0 x)
    (lambda ()
      (mac-h 'pos-rr (list 'POS-RR x))
      (dk-split! (list 'AND (list 'IN x 'RR)
                       (list 'AND (list '<= 0 x) (list 'NOT (list '= 0 x)))))
      (ass))))

;;; Beta-reduce the GOAL to exhaustion.  One `lam-b' takes the redexes that
;;; are SIBLINGS but not the ones that are NESTED, and a family of families
;;; ((u j) i) is nested; calling `lam-b' when nothing is reducible only warns,
;;; but the warning reads like a failure, so the redex test comes first.
(define (dn-has-redex? e)
  (cond ((not (pair? e)) #f)
        ((and (pair? (car e)) (eq? (caar e) 'VNB-LAMBDA)) #t)
        (else (any-pred dn-has-redex? e))))
(define (dn-beta!)
  (let lp ((n 0))
    (if (and (< n 6) (dn-has-redex? (dk-goal)))
        (begin (lam-b) (lp (+ n 1))))))

;;; The four conjuncts of an unfolded CONVERGES-TO(RR-MS, seq, L) GOAL: the
;;; metric-space fact, the two typings (PTS(RR-MS) = RR, one `slot'), and the
;;; eps-N estimate, which is the caller's business.
(define (dn-converges-to! eps-branch)
  (mac 'converges-to)
  (dn-and!
   (lambda ()
     (let ((gl (dk-goal)))
       (cond ((eq? (car gl) 'IS-METRIC-SPACE) (fact 'rr-is-metric-space) (ass))
             ((eq? (car gl) 'IN) (slot 'PTS) (ass))
             (else (eps-branch)))))))

;;; =====================================================================
;;; L1.  rr-null-sum -- the sum of two null sequences is null, in TRANSFER
;;; form: the conclusion is about any `h' agreeing pointwise with f + g.
;;; =====================================================================

(sp (make-wff "forall([f in fun(nn,rr), g in fun(nn,rr), h in fun(nn,rr)],
     converges-to(rr-ms, f, 0) implies converges-to(rr-ms, g, 0) implies
     forall([j_ in nn], h(j_) = f(j_) + g(j_)) implies
     converges-to(rr-ms, h, 0))"))
(di)(di)(di)(di)
(define ns-pt (dn-find 'pointwise
                (lambda (a) (and (pair? a) (eq? (car a) 'FORALL) (dk-contains? a 'h)))))
(dk-split! (dk-landed-find (lambda () (mac-h 'converges-to '(CONVERGES-TO RR-MS f 0)))
                           (lambda (a) (eq? (car a) 'AND))))
(dk-split! (dk-landed-find (lambda () (mac-h 'converges-to '(CONVERGES-TO RR-MS g 0)))
                           (lambda (a) (eq? (car a) 'AND))))
(define (ns-tail-of s)
  (dn-find s (lambda (a) (and (pair? a) (eq? (car a) 'FORALL) (dk-contains? a s)
                              (dk-contains? a 'POS-RR)))))
(define ns-tf (ns-tail-of 'f))
(define ns-tg (ns-tail-of 'g))

;;; The inner (FORALL n_ ... (<= thr n_) => ...) of a skolemized eps-N clause,
;;; discriminated on its THRESHOLD and captured while the context is clean:
;;; once `rr-le-max-left' has been cited, its own partly-peeled chain is a
;;; FORALL mentioning the same threshold, and a shape test picks that instead.
(define (ns-inner thr)
  (dn-find thr (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                                (let ((b (caddr a)))
                                  (and (pair? b) (eq? (car b) 'IMPLIES)
                                       (dk-contains? (caddr b) thr)))))))

(define (ns-eps-branch!)
  (let* ((ns-eps (cadr (dn-di-landed-1!)))
         (ns-hex (dk-fact! 'rr-pos-halvable ns-eps))
         (ns-d   (dn-skolem! ns-hex))
         (exf (dk-deepest (lambda () (inst+ ns-tf ns-d))))
         (nf  (dn-skolem! exf))
         (inf (ns-inner nf))
         (exg (dk-deepest (lambda () (inst+ ns-tg ns-d))))
         (ng  (dn-skolem! exg))
         (ing (ns-inner ng))
         (ns-bnd (list 'MAX nf ng)))
    (fact 'nn-max-closed nf ng)
    (ew ns-bnd)
    (dn-and!
     (lambda ()
       (if (eq? (car (dk-goal)) 'IN) (ass)
           (let* ((memb (dn-di-landed-1!))
                  (n_   (cadr memb)))
             (dn-di-landed!)                       ; the (<= max n_) hypothesis
             (fact 'nn-in-rr nf) (fact 'nn-in-rr ng)
             (fact 'nn-in-rr ns-bnd) (fact 'nn-in-rr n_)
             (fact 'rr-le-max-left nf ng)
             (fact 'rr-le-max-right nf ng)
             (have! (list '<= nf n_)
               (lambda () (dn-ineq (list '<= nf ns-bnd) (list '<= ns-bnd n_))))
             (have! (list '<= ng n_)
               (lambda () (dn-ineq (list '<= ng ns-bnd) (list '<= ns-bnd n_))))
             (inst+ inf n_)
             (inst+ ing n_)
             (inst+ ns-pt n_)
             (fact 'fun-apply-type-c 'f 'NN 'RR n_)
             (fact 'fun-apply-type-c 'g 'NN 'RR n_)
             (fact 'fun-apply-type-c 'h 'NN 'RR n_)
             (fact 'rr-zero-in)
             (subst (list '= (list 'h n_) (list '+ (list 'f n_) (list 'g n_))))
             (have! (list 'AND (list 'IN (list 'f n_) 'RR) (list 'IN (list 'g n_) 'RR))
               (lambda () (dn-and! (lambda () (ass)))))
             (fact 'rr-add-closed (list 'f n_) (list 'g n_))
             ;; rr-ms-dist is GUARDED: every argument typed BEFORE the rewrite.
             (mac 'rr-ms-dist)
             (mac-h 'rr-ms-dist (list '<= (list (list 'DIST 'RR-MS) (list 'f n_) 0) ns-d))
             (mac-h 'rr-ms-dist (list '<= (list (list 'DIST 'RR-MS) (list 'g n_) 0) ns-d))
             ;; `ineq' reads abs(x) as an ATOM, so abs(f+g-0) and abs(f-0)+abs(g-0)
             ;; are unrelated until the ARGUMENTS are brought to a common shape.
             (let ((uf (list '- (list 'f n_) 0)) (ug (list '- (list 'g n_) 0)))
               (have! (list '= (list '- (list '+ (list 'f n_) (list 'g n_)) 0)
                               (list '+ uf ug))
                 (lambda () (crs)))
               (subst (list '= (list '- (list '+ (list 'f n_) (list 'g n_)) 0)
                               (list '+ uf ug)))
               (fact 'rr-sub-in-rr (list 'f n_) 0)
               (fact 'rr-sub-in-rr (list 'g n_) 0)
               (fact 'rr-abs-closed uf) (fact 'rr-abs-closed ug)
               (fact 'rr-abs-closed (list '+ uf ug))
               (fact 'rr-abs-triangle-c uf ug)
               (dn-pos-in-rr! ns-eps)
               (dn-pos-in-rr! ns-d)
               (dn-ineq (list '<= (list 'abs (list '+ uf ug))
                                  (list '+ (list 'abs uf) (list 'abs ug)))
                        (list '<= (list 'abs uf) ns-d)
                        (list '<= (list 'abs ug) ns-d)
                        (list '= (list '+ ns-d ns-d) ns-eps)))))))))

(mac 'converges-to)
(dn-and!
 (lambda ()
   (let ((gl (dk-goal)))
     (cond ((eq? (car gl) 'IS-METRIC-SPACE) (ass))
           ((and (eq? (car gl) 'IN) (equal? (cadr gl) 0)) (ass))
           ((eq? (car gl) 'IN) (slot 'PTS) (ass))
           (else (ns-eps-branch!))))))
(qed 'rr-null-sum)
(topic! 'rr-null-sum 'analysis)
(alias! 'rr-null-sum "the sum of two null sequences is null")

;;; =====================================================================
;;; L2.  rr-limit-abs-le -- a limit inherits a uniform bound on |f|.
;;;
;;; The route is `rr-le-all-pos-nonpos' (|L| - c <= eps for every eps > 0 gives
;;; |L| - c <= 0), with the reverse triangle inequality supplying the estimate
;;; at ONE index -- no case split and no epsilon bookkeeping beyond that.
;;; =====================================================================

(sp (make-wff "forall([f in fun(nn,rr), lv in rr, bd in rr],
     converges-to(rr-ms, f, lv) implies
     forall([n_ in nn], abs(f(n_)) <= bd) implies
     abs(lv) <= bd)"))
(di)(di)(di)
(define la-pt (dn-find 'bound
                (lambda (a) (and (pair? a) (eq? (car a) 'FORALL) (dk-contains? a 'abs)))))
(dk-split! (dk-landed-find (lambda () (mac-h 'converges-to '(CONVERGES-TO RR-MS f lv)))
                           (lambda (a) (eq? (car a) 'AND))))
(define la-tail (dn-find 'tail (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                                                (dk-contains? a 'POS-RR)))))
(fact 'rr-abs-closed 'lv)
(have! '(IN (- (abs lv) bd) RR) (lambda () (fact 'rr-sub-in-rr '(abs lv) 'bd) (ass)))
(have! '(FORALL eps (IMPLIES (POS-RR eps) (<= (- (abs lv) bd) eps)))
  (lambda ()
    (let* ((eps (cadr (dn-di-landed-1!)))
           (ex  (dk-deepest (lambda () (inst+ la-tail eps))))
           (bigN (dn-skolem! ex))
           (inner (dn-find 'inner
                    (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                                     (let ((b (caddr a)))
                                       (and (pair? b) (eq? (car b) 'IMPLIES)
                                            (dk-contains? (caddr b) bigN))))))))
      (fact 'nn-in-rr bigN)
      (fact 'rr-leq-reflexive bigN)
      (inst+ inner bigN)
      (inst+ la-pt bigN)
      (fact 'fun-apply-type-c 'f 'NN 'RR bigN)
      (mac-h 'rr-ms-dist (list '<= (list (list 'DIST 'RR-MS) (list 'f bigN) 'lv) eps))
      (dn-pos-in-rr! eps)
      (fact 'rr-abs-reverse-triangle 'lv (list 'f bigN))
      (fact 'rr-abs-sub-sym 'lv (list 'f bigN))
      (fact 'rr-abs-closed (list 'f bigN))
      (fact 'rr-sub-in-rr '(abs lv) (list 'abs (list 'f bigN)))
      (fact 'rr-sub-in-rr 'lv (list 'f bigN))
      (fact 'rr-sub-in-rr (list 'f bigN) 'lv)
      (fact 'rr-le-abs (list '- '(abs lv) (list 'abs (list 'f bigN))))
      (fact 'rr-abs-closed (list '- '(abs lv) (list 'abs (list 'f bigN))))
      (fact 'rr-abs-closed (list '- 'lv (list 'f bigN)))
      (fact 'rr-abs-closed (list '- (list 'f bigN) 'lv))
      (dn-ineq (list '<= (list '- '(abs lv) (list 'abs (list 'f bigN)))
                          (list 'abs (list '- '(abs lv) (list 'abs (list 'f bigN)))))
               (list '<= (list 'abs (list '- '(abs lv) (list 'abs (list 'f bigN))))
                          (list 'abs (list '- 'lv (list 'f bigN))))
               (list '= (list 'abs (list '- 'lv (list 'f bigN)))
                        (list 'abs (list '- (list 'f bigN) 'lv)))
               (list '<= (list 'abs (list '- (list 'f bigN) 'lv)) eps)
               (list '<= (list 'abs (list 'f bigN)) 'bd)))))
(fact 'rr-le-all-pos-nonpos '(- (abs lv) bd))
(dn-ineq '(<= (- (abs lv) bd) 0))
(qed 'rr-limit-abs-le)
(topic! 'rr-limit-abs-le 'analysis)
(alias! 'rr-limit-abs-le "a limit inherits a uniform bound on the absolute value")

;;; =====================================================================
;;; L3.  series-block-le -- a BLOCK of a dominated series is dominated.
;;;
;;;   0 <= f <= g termwise,  n_ <= k   =>   S(f,k) - S(f,n_) <= S(g,k) - S(g,n_)
;;;
;;; `k' is quantified FIRST: `ni' tests the goal SHAPE, so the induction
;;; variable has to be outermost or there is no induction to start.
;;; =====================================================================

(sp (make-wff "forall([k in nn, n_ in nn, f in fun(nn,rr), g in fun(nn,rr)],
     forall([i_ in nn], 0 <= f(i_) and f(i_) <= g(i_)) implies
     n_ <= k implies
     series-partial-sum(f,k) - series-partial-sum(f,n_)
       <= series-partial-sum(g,k) - series-partial-sum(g,n_))"))
(define bl-br (use-induction))

;;; BASE.  n_ <= 0 forces n_ = 0 and both sides collapse to 0 - 0.
;;; `nn-zero-le' + antisymmetry rather than the proven `nn-le-zero-is-zero',
;;; whose own bill carries two further NN supports (monotone-convergence-proof
;;; declines the same citation for the same reason).
(dk-focus! (cdr (assq 'base bl-br)))
(dn-di-landed!) (dn-di-landed!) (dn-di-landed!)
(let ((n_ (cadr (dn-find 'le0 (lambda (a) (and (pair? a) (eq? (car a) '<=)
                                               (equal? (caddr a) 0)))))))
  (fact 'nn-zero-le n_)
  (fact 'nn-in-rr n_)
  (fact 'nn-in-rr 0)
  (have! (list 'AND (list 'IN n_ 'RR) '(IN 0 RR)))
  (have! (list 'AND (list '<= n_ 0) (list '<= 0 n_)))
  (fact 'rr-leq-antisymmetric n_ 0)
  (subst (list '= n_ 0))
  (mac 'series-partial-sum-zero)
  (arith))

;;; STEP.  n_ <= succ k splits: n_ <= k (the IH, plus f(k) <= g(k)) or
;;; n_ = succ k (both sides are X - X).
(dk-focus! (cdr (assq 'step bl-br)))
(define bl-k (cadr (dn-find 'k (dk-head? 'IN))))
(define bl-ih (dn-find 'ih (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)))))
(dn-di-landed!) (dn-di-landed!) (dn-di-landed!)
(define bl-tw (dn-find 'termwise
                (lambda (x) (and (pair? x) (eq? (car x) 'FORALL) (dk-contains? x 'i_)))))
(define bl-n (cadr (dn-find 'nle (lambda (a) (and (pair? a) (eq? (car a) '<=)
                                     (equal? (caddr a) (list 'succ bl-k)))))))
;; series-partial-sum-succ is guarded on its two arguments being real since
;; 2026-08-29, and it rewrites BOTH sides here -- so all four typings precede it.
(fact 'series-partial-sum-in-rr bl-k 'f)
(fact 'series-partial-sum-in-rr bl-k 'g)
(fact 'fun-apply-type-c 'f 'NN 'RR bl-k)
(fact 'fun-apply-type-c 'g 'NN 'RR bl-k)
(mac 'series-partial-sum-succ)
(fact 'nn-le-succ-cases bl-k bl-n)
(use-cases (list (list '<= bl-n bl-k) (list '= bl-n (list 'succ bl-k)))
  (lambda ()
    (let* ((a1 (dk-deepest (lambda () (inst+ bl-ih bl-n))))
           (a2 (dk-deepest (lambda () (inst+ a1 'f))))
           (a3 (dk-deepest (lambda () (inst+ a2 'g)))))
      (for-each (lambda (x) (if (and (pair? x) (eq? (car x) 'AND)) (dk-split! x)))
                (dk-landed* (lambda () (inst+ bl-tw bl-k))))
      (fact 'fun-apply-type-c 'f 'NN 'RR bl-k)
      (fact 'fun-apply-type-c 'g 'NN 'RR bl-k)
      (fact 'series-partial-sum-in-rr bl-k 'f)
      (fact 'series-partial-sum-in-rr bl-k 'g)
      (fact 'series-partial-sum-in-rr bl-n 'f)
      (fact 'series-partial-sum-in-rr bl-n 'g)
      (dn-ineq a3 (list '<= (list 'f bl-k) (list 'g bl-k)))))
  (lambda ()
    (subst (list '= bl-n (list 'succ bl-k)))
    (mac 'series-partial-sum-succ)
    (fact 'fun-apply-type-c 'f 'NN 'RR bl-k)
    (fact 'fun-apply-type-c 'g 'NN 'RR bl-k)
    (fact 'series-partial-sum-in-rr bl-k 'f)
    (fact 'series-partial-sum-in-rr bl-k 'g)
    (let* ((gl (dk-goal)) (lhs (cadr gl)) (rhs (caddr gl)))
      (have! (list '= lhs 0) (lambda () (crs)))
      (subst (list '= lhs 0))
      (have! (list '= rhs 0) (lambda () (crs)))
      (subst (list '= rhs 0))
      (arith))))
(qed 'series-block-le)
(topic! 'series-block-le 'analysis)
(alias! 'series-block-le "a block of a dominated series is dominated")

;;; =====================================================================
;;; L4.  series-head-null -- the FINITE HEAD of a pointwise-null family is
;;; null, uniformly in nothing at all: for a FIXED length n_,
;;;      j |-> S(u(j), n_)  ->  0.
;;;
;;; This is the step the user flagged as the expected blocker -- "a finite max
;;; over coordinates, for which a MAX OVER A FINITE FAMILY does not exist".  It
;;; is not needed.  Induction on the head length turns the family max into
;;; ONE application of `rr-null-sum' per step, and rr-null-sum's own max is the
;;; binary `MAX' the tree already has.  The mechanism dissolves the obligation.
;;; =====================================================================

(sp (make-wff "forall([n_ in nn], forall([u],
  forall([j_ in nn], u(j_) in fun(nn,rr)) implies
  forall([i_ in nn], converges-to(rr-ms, vnb-lambda(j_, nn, u(j_)(i_)), 0)) implies
  forall([hd in fun(nn,rr)],
    forall([j_ in nn], hd(j_) = series-partial-sum(u(j_), n_)) implies
    converges-to(rr-ms, hd, 0))))"))
(define hn-br (use-induction))

;;; BASE.  hd(j) = S(u(j),0) = 0: the constant zero sequence, threshold 0.
(dk-focus! (cdr (assq 'base hn-br)))
(dn-di-landed!) (dn-di-landed!) (dn-di-landed!)
(define hn0-pw (dn-di-landed-1!))
(fact 'rr-zero-in)
(dn-converges-to!
 (lambda ()
   (let ((eps (cadr (dn-di-landed-1!))))
     (fact 'nn-zero-in)
     (ew 0)
     (dn-and!
      (lambda ()
        (if (eq? (car (dk-goal)) 'IN) (ass)
            (let ((j (cadr (dn-di-landed-1!))))
              (dn-di-landed!)                      ; 0 <= j
              (inst+ hn0-pw j)
              (subst (list '= (list 'hd j) (list 'SERIES-PARTIAL-SUM (list 'u j) 0)))
              (mac 'series-partial-sum-zero)
              (mac 'rr-ms-dist)
              (have! '(= (abs (- 0 0)) 0) (lambda () (arith)))
              (subst '(= (abs (- 0 0)) 0))
              (mac-h 'pos-rr (list 'POS-RR eps))
              (dk-split! (list 'AND (list 'IN eps 'RR)
                               (list 'AND (list '<= 0 eps) (list 'NOT (list '= 0 eps)))))
              (ass))))))))

;;; STEP.  S(u(j), succ n_) = S(u(j), n_) + u(j)(n_): the head of length
;;; succ n_ is the head of length n_ plus the n_-th coordinate, so it is the
;;; sum of a sequence the IH kills and one the hypothesis kills.
(dk-focus! (cdr (assq 'step hn-br)))
(define hn-ih (dn-find 'ih (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)))))
(define hn-n  (cadr (dn-find 'n (dk-head? 'IN))))
(dn-di-landed!)
(define hn-ut (dn-find 'utyping (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                                                 (dk-contains? a 'FUN)))))
(define hn-co (dk-landed-1 (lambda () (di))))     ; the coordinate hypothesis
(dn-di-landed!)                                   ; hd typing
(define hn-pw (dn-di-landed-1!))                  ; pointwise, at succ n_

(define hn-f (list 'VNB-LAMBDA 'j_ 'NN (list 'SERIES-PARTIAL-SUM '(u j_) hn-n)))
(define hn-g (list 'VNB-LAMBDA 'j_ 'NN (list '(u j_) hn-n)))

(have! (list 'IN hn-f '(FUN NN RR))
  (lambda ()
    (dk-lam-t!)
    (let ((j (cadr (dn-di-landed-1!))))
      (inst+ hn-ut j)
      (fact 'series-partial-sum-in-rr hn-n (list 'u j))
      (ass))))
(have! (list 'IN hn-g '(FUN NN RR))
  (lambda ()
    (dk-lam-t!)
    (let ((j (cadr (dn-di-landed-1!))))
      (inst+ hn-ut j)
      (fact 'fun-apply-type-c (list 'u j) 'NN 'RR hn-n)
      (ass))))
(inst+ hn-co hn-n)                                ; the n_-th coordinate is null
(define hn-ih1 (dk-deepest (lambda () (inst+ hn-ih 'u))))
(define hn-ih2 (dk-deepest (lambda () (inst+ hn-ih1 hn-f))))
(have! (list 'FORALL 'j_ (list 'IMPLIES '(IN j_ NN)
         (list '= (list hn-f 'j_) (list 'SERIES-PARTIAL-SUM '(u j_) hn-n))))
  (lambda ()
    (let ((j (cadr (dn-di-landed-1!))))
      (inst+ hn-ut j)
      (fact 'series-partial-sum-in-rr hn-n (list 'u j))
      (lam-b)
      (rfl))))
(detach! hn-ih2)
(have! (list 'FORALL 'j_ (list 'IMPLIES '(IN j_ NN)
         (list '= '(hd j_) (list '+ (list hn-f 'j_) (list hn-g 'j_)))))
  (lambda ()
    (let ((j (cadr (dn-di-landed-1!))))
      (inst+ hn-ut j)
      (fact 'series-partial-sum-in-rr hn-n (list 'u j))
      (fact 'fun-apply-type-c (list 'u j) 'NN 'RR hn-n)
      (fact 'nn-succ-closed hn-n)
      (lam-b)                       ; one call takes BOTH redexes
      (inst+ hn-pw j)
      (subst (list '= (list 'hd j) (list 'SERIES-PARTIAL-SUM (list 'u j) (list 'succ hn-n))))
      (mac 'series-partial-sum-succ)
      (have! (list 'AND (list 'IN (list 'SERIES-PARTIAL-SUM (list 'u j) hn-n) 'RR)
                        (list 'IN (list (list 'u j) hn-n) 'RR))
        (lambda () (dn-and! (lambda () (ass)))))
      (fact 'rr-add-closed (list 'SERIES-PARTIAL-SUM (list 'u j) hn-n)
                           (list (list 'u j) hn-n))
      (rfl))))
(fact 'rr-null-sum hn-f hn-g 'hd)
(ass)
(qed 'series-head-null)
(topic! 'series-head-null 'analysis)
(alias! 'series-head-null "a finite head of a pointwise-null family is null")

;;; =====================================================================
;;; L5.  series-partial-sum-nonneg / -mono -- partial sums of a NONNEGATIVE
;;; series are nonnegative and nondecreasing in the index.
;;;
;;; Both are proved by NN-induction from the recurrence rather than from
;;; `series-partial-sum-monotone-nonneg' + `nn-monotone-step-implies-le'.  That
;;; route exists and is one line shorter to state, but it goes through the
;;; partial-sum SEQUENCE (VNB-LAMBDA k NN (SERIES-PARTIAL-SUM f k)), and
;;; `mac-h series-partial-sum-seq-apply' will not rewrite an assumption whose
;;; lambda has been alpha-renamed by the kernel: it reports
;;; "does not occur in the cited assumption" and no-ops.  Induction on the index
;;; never builds the lambda at all.
;;; =====================================================================

(sp (make-wff "forall([k in nn, f in fun(nn,rr)],
     forall([i_ in nn], 0 <= f(i_)) implies 0 <= series-partial-sum(f,k))"))
(define sn-br (use-induction))
(dk-focus! (cdr (assq 'base sn-br)))
(dn-di-landed!) (dn-di-landed!)
(mac 'series-partial-sum-zero)
(arith)
(dk-focus! (cdr (assq 'step sn-br)))
(define sn-k  (cadr (dn-find 'k (dk-head? 'IN))))
(define sn-ih (dn-find 'ih (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                                            (dk-contains? a 'FUN)))))
(dn-di-landed!)
(define sn-tw (dn-di-landed-1!))
;; guarded on its two arguments being real since 2026-08-29: land both first.
(fact 'fun-apply-type-c 'f 'NN 'RR sn-k)
(fact 'series-partial-sum-in-rr sn-k 'f)
(mac 'series-partial-sum-succ)
(dk-deepest (lambda () (inst+ sn-ih 'f)))
(inst+ sn-tw sn-k)
(dn-ineq (list '<= 0 (list 'SERIES-PARTIAL-SUM 'f sn-k))
         (list '<= 0 (list 'f sn-k)))
(qed 'series-partial-sum-nonneg)
(topic! 'series-partial-sum-nonneg 'analysis)
(alias! 'series-partial-sum-nonneg "a partial sum of a nonnegative series is nonnegative")

(sp (make-wff "forall([k in nn, m in nn, f in fun(nn,rr)],
     forall([i_ in nn], 0 <= f(i_)) implies m <= k implies
     series-partial-sum(f,m) <= series-partial-sum(f,k))"))
(define sm-br (use-induction))

(dk-focus! (cdr (assq 'base sm-br)))
(dn-di-landed!) (dn-di-landed!) (dn-di-landed!)
(let ((m (cadr (dn-find 'le0 (lambda (a) (and (pair? a) (eq? (car a) '<=)
                                              (equal? (caddr a) 0)))))))
  (fact 'nn-zero-le m)
  (fact 'nn-in-rr m)
  (fact 'nn-in-rr 0)
  (have! (list 'AND (list 'IN m 'RR) '(IN 0 RR)))
  (have! (list 'AND (list '<= m 0) (list '<= 0 m)))
  (fact 'rr-leq-antisymmetric m 0)
  (subst (list '= m 0))
  (fact 'series-partial-sum-in-rr 0 'f)
  (fact 'rr-leq-reflexive '(SERIES-PARTIAL-SUM f 0))
  (ass))

(dk-focus! (cdr (assq 'step sm-br)))
(define sm-k  (cadr (dn-find 'k (dk-head? 'IN))))
(define sm-ih (dn-find 'ih (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                                            (dk-contains? a 'FUN)))))
(dn-di-landed!) (dn-di-landed!) (dn-di-landed!)
(define sm-tw (dn-find 'termwise
                (lambda (x) (and (pair? x) (eq? (car x) 'FORALL) (dk-contains? x 'i_)))))
(define sm-m (cadr (dn-find 'mle (lambda (a) (and (pair? a) (eq? (car a) '<=)
                                     (equal? (caddr a) (list 'succ sm-k)))))))
;; guarded on its two arguments being real since 2026-08-29: land both first.
(fact 'fun-apply-type-c 'f 'NN 'RR sm-k)
(fact 'series-partial-sum-in-rr sm-k 'f)
(fact 'series-partial-sum-in-rr sm-m 'f)
(mac 'series-partial-sum-succ)
(fact 'nn-le-succ-cases sm-k sm-m)
(inst+ sm-tw sm-k)
(use-cases (list (list '<= sm-m sm-k) (list '= sm-m (list 'succ sm-k)))
  (lambda ()
    (let* ((a1 (dk-deepest (lambda () (inst+ sm-ih sm-m))))
           (a2 (dk-deepest (lambda () (inst+ a1 'f)))))
      (dn-ineq a2 (list '<= 0 (list 'f sm-k)))))
  (lambda ()
    (subst (list '= sm-m (list 'succ sm-k)))
    (mac 'series-partial-sum-succ)
    (have! (list 'AND (list 'IN (list 'SERIES-PARTIAL-SUM 'f sm-k) 'RR)
                      (list 'IN (list 'f sm-k) 'RR))
      (lambda () (dn-and! (lambda () (ass)))))
    (fact 'rr-add-closed (list 'SERIES-PARTIAL-SUM 'f sm-k) (list 'f sm-k))
    (fact 'rr-leq-reflexive (list '+ (list 'SERIES-PARTIAL-SUM 'f sm-k) (list 'f sm-k)))
    (ass)))
(qed 'series-partial-sum-mono)
(topic! 'series-partial-sum-mono 'analysis)
(alias! 'series-partial-sum-mono
        "partial sums of a nonnegative series are nondecreasing")

;;; =====================================================================
;;; L6.  series-tail-small -- a convergent series has arbitrarily small TAILS,
;;; in the block form the dominated-convergence argument needs.
;;;
;;;   Sum g converges  =>  for every eps > 0 there is N with
;;;                        S(g,k) - S(g,N) <= eps  for every k >= N.
;;;
;;; This is the ONE analytic fact the file does not discharge: it is
;;; `series-cauchy-criterion' (theorem-library/series-order-lemmas.scm, an
;;; asserted `well-known' support) at m = N, n_ = k, plus x <= |x|.  Proving
;;; the Cauchy criterion itself -- convergent implies Cauchy in RR-MS -- is a
;;; separate piece of work and is recorded as such.
;;; =====================================================================

(sp (make-wff "forall([g in fun(nn,rr)], series-converges(g) implies
     forall([eps], pos-rr(eps) implies
       forsome([bnd in nn], forall([k in nn], bnd <= k implies
          series-partial-sum(g,k) - series-partial-sum(g,bnd) <= eps))))"))
(dn-di-landed!) (dn-di-landed!)
(let* ((eps (cadr (dn-di-landed-1!)))
       (cc  (dk-fact! 'series-cauchy-criterion 'g))
       (ex  (dk-deepest (lambda () (inst+ cc eps))))
       (bnd (dn-skolem! ex))
       (inner (dn-find 'inner
                (lambda (a) (and (pair? a) (eq? (car a) 'FORALL) (dk-contains? a bnd)
                                 (dk-contains? a 'abs))))))
  (ew bnd)
  (dn-and!
   (lambda ()
     (if (eq? (car (dk-goal)) 'IN) (ass)
         (let ((k (cadr (dn-di-landed-1!))))
           (dn-di-landed!)                           ; bnd <= k
           (fact 'nn-in-rr bnd)
           (fact 'rr-leq-reflexive bnd)
           (have! (list 'AND (list '<= bnd bnd) (list '<= bnd k)))
           (let* ((b1 (dk-deepest (lambda () (inst+ inner bnd))))
                  (b2 (dk-deepest (lambda () (inst+ b1 k)))))
             (fact 'series-partial-sum-in-rr k 'g)
             (fact 'series-partial-sum-in-rr bnd 'g)
             (fact 'rr-sub-in-rr (list 'SERIES-PARTIAL-SUM 'g k)
                                 (list 'SERIES-PARTIAL-SUM 'g bnd))
             (fact 'rr-le-abs (list '- (list 'SERIES-PARTIAL-SUM 'g k)
                                       (list 'SERIES-PARTIAL-SUM 'g bnd)))
             (fact 'rr-abs-closed (list '- (list 'SERIES-PARTIAL-SUM 'g k)
                                           (list 'SERIES-PARTIAL-SUM 'g bnd)))
             (dn-pos-in-rr! eps)
             (dn-ineq b2 (list '<= (list '- (list 'SERIES-PARTIAL-SUM 'g k)
                                            (list 'SERIES-PARTIAL-SUM 'g bnd))
                                   (list 'abs (list '- (list 'SERIES-PARTIAL-SUM 'g k)
                                                       (list 'SERIES-PARTIAL-SUM 'g bnd))))))))))) 
(qed 'series-tail-small)
(topic! 'series-tail-small 'analysis)
(alias! 'series-tail-small "a convergent series has arbitrarily small tails")

;;; =====================================================================
;;; L7.  dominated-null-series -- THE THEOREM.
;;;
;;;   0 <= u_j(n) <= g(n),  Sum g converges,  u_j(n) -> 0 for each n
;;;     =>  the sums e(j) = Sum_n u_j(n) tend to 0.
;;;
;;; Given eps, halve it to d.  `series-tail-small' picks N with the g-tail
;;; below d; `series-head-null' picks J beyond which the FIXED head
;;; S(u_j, N) is below d.  For j >= J and ANY k the partial sum splits at N:
;;; below N it is at most S(u_j,N) <= d (`series-partial-sum-mono'), above N it
;;; is S(u_j,N) plus a block that `series-block-le' compares with the g-block,
;;; hence at most d + d = eps.  Every partial sum of u_j is then in [0, eps],
;;; and `rr-limit-abs-le' hands that bound to the limit e(j).
;;; =====================================================================

(sp (make-wff "forall([g in fun(nn,rr), e in fun(nn,rr)], forall([u],
  forall([j_ in nn], u(j_) in fun(nn,rr)) implies
  forall([j_ in nn], forall([i_ in nn], 0 <= u(j_)(i_) and u(j_)(i_) <= g(i_))) implies
  series-converges(g) implies
  forall([i_ in nn], converges-to(rr-ms, vnb-lambda(j_, nn, u(j_)(i_)), 0)) implies
  forall([j_ in nn], series-converges-to(u(j_), e(j_))) implies
  converges-to(rr-ms, e, 0)))"))
(dn-di-landed!)                                     ; g, e typings
(dn-di-landed!)                                     ; u typing hypothesis
(define dc-ut (dn-find 'utyping
                (lambda (a) (and (pair? a) (eq? (car a) 'FORALL) (dk-contains? a 'FUN)))))
(define dc-dom (dn-di-landed-1!))                   ; the domination hypothesis
(dn-di-landed!)                                     ; series-converges(g)
(define dc-co (dn-di-landed-1!))                    ; the coordinate hypothesis
(define dc-sum (dn-di-landed-1!))                   ; series-converges-to(u(j), e(j))
(fact 'rr-zero-in)

;;; the termwise hypothesis for ONE j, in the two shapes the lemmas want
(define (dc-termwise! j)
  (let ((both (dk-deepest (lambda () (inst+ dc-dom j)))))
    (have! (list 'FORALL 'i_ (list 'IMPLIES '(IN i_ NN)
                                   (list '<= 0 (list (list 'u j) 'i_))))
      (lambda ()
        (let ((i (cadr (dn-di-landed-1!))))
          (for-each (lambda (x) (if (and (pair? x) (eq? (car x) 'AND)) (dk-split! x)))
                    (dk-landed* (lambda () (inst+ both i))))
          (ass))))
    both))

(dn-converges-to!
 (lambda ()
   (let* ((eps  (cadr (dn-di-landed-1!)))
          (hex  (dk-fact! 'rr-pos-halvable eps))
          (d    (dn-skolem! hex))
          ;; ---- the TAIL of g, below d beyond bigN
          (tex  (dk-deepest (lambda () (fact 'series-tail-small 'g d))))
          (bigN (dn-skolem! tex))
          (tail (dn-find 'tail
                  (lambda (a) (and (pair? a) (eq? (car a) 'FORALL) (dk-contains? a bigN)
                                   (dk-contains? a 'SERIES-PARTIAL-SUM)))))
          (hd   (list 'VNB-LAMBDA 'j_ 'NN (list 'SERIES-PARTIAL-SUM '(u j_) bigN))))
     ;; ---- the fixed HEAD of length bigN is a null sequence
     (have! (list 'IN hd '(FUN NN RR))
       (lambda ()
         (dk-lam-t!)
         (let ((j (cadr (dn-di-landed-1!))))
           (inst+ dc-ut j)
           (fact 'series-partial-sum-in-rr bigN (list 'u j))
           (ass))))
     (have! (list 'FORALL 'j_ (list 'IMPLIES '(IN j_ NN)
              (list '= (list hd 'j_) (list 'SERIES-PARTIAL-SUM '(u j_) bigN))))
       (lambda ()
         (let ((j (cadr (dn-di-landed-1!))))
           (inst+ dc-ut j)
           (fact 'series-partial-sum-in-rr bigN (list 'u j))
           (lam-b)
           (rfl))))
     (fact 'series-head-null bigN 'u hd)
     (let* ((hcv (dn-find 'headconv
                   (lambda (a) (and (pair? a) (eq? (car a) 'CONVERGES-TO)
                                    (equal? (caddr a) hd))))))
       (dk-split! (dk-landed-find (lambda () (mac-h 'converges-to hcv))
                                  (lambda (a) (eq? (car a) 'AND))))
       (let* ((hep (dn-find 'headeps
                     (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                                      (dk-contains? a 'POS-RR) (dk-contains? a hd)))))
              (jex (dk-deepest (lambda () (inst+ hep d))))
              (bigJ (dn-skolem! jex))
              (jin (dn-find 'headinner
                     (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                                      (let ((b (caddr a)))
                                        (and (pair? b) (eq? (car b) 'IMPLIES)
                                             (dk-contains? (caddr b) bigJ))))))))
         (ew bigJ)
         (dn-and!
          (lambda ()
            (if (eq? (car (dk-goal)) 'IN) (ass)
                (let ((j (cadr (dn-di-landed-1!))))
                  (dn-di-landed!)                       ; bigJ <= j
                  (inst+ dc-ut j)
                  (inst+ jin j)
                  (fact 'fun-apply-type-c hd 'NN 'RR j)
                  (fact 'fun-apply-type-c 'e 'NN 'RR j)
                  (fact 'series-partial-sum-in-rr bigN (list 'u j))
                  (dn-pos-in-rr! eps)
                  (dn-pos-in-rr! d)
                  (dn-pos-nonneg! d)
                  (mac-h 'rr-ms-dist (list '<= (list (list 'DIST 'RR-MS) (list hd j) 0) d))
                  (fact 'rr-sub-in-rr (list hd j) 0)
                  (fact 'rr-abs-closed (list '- (list hd j) 0))
                  (fact 'rr-le-abs (list '- (list hd j) 0))
                  ;; the head bound, read off the lambda
                  (have! (list '<= (list 'SERIES-PARTIAL-SUM (list 'u j) bigN) d)
                    (lambda ()
                      (have! (list '= (list 'SERIES-PARTIAL-SUM (list 'u j) bigN)
                                      (list hd j))
                        (lambda () (lam-b) (rfl)))
                      (subst (list '= (list 'SERIES-PARTIAL-SUM (list 'u j) bigN)
                                      (list hd j)))
                      (dn-ineq (list '<= (list '- (list hd j) 0)
                                         (list 'abs (list '- (list hd j) 0)))
                               (list '<= (list 'abs (list '- (list hd j) 0)) d))))
                  ;; every partial sum of u(j) is in [0, eps]
                  (let ((both (dc-termwise! j))
                        (psq  (list 'VNB-LAMBDA 'k_ 'NN
                                    (list 'SERIES-PARTIAL-SUM (list 'u j) 'k_))))
                    (fact 'series-partial-sum-seq-in-fun (list 'u j))
                    (have! (list 'FORALL 'k_ (list 'IMPLIES '(IN k_ NN)
                             (list '<= (list 'abs (list psq 'k_)) eps)))
                      (lambda ()
                        (let ((k (cadr (dn-di-landed-1!))))
                          (lam-b)
                          (fact 'series-partial-sum-in-rr k (list 'u j))
                          (fact 'series-partial-sum-nonneg k (list 'u j))
                          (fact 'rr-abs-of-nonneg (list 'SERIES-PARTIAL-SUM (list 'u j) k))
                          (subst (list '= (list 'abs (list 'SERIES-PARTIAL-SUM (list 'u j) k))
                                          (list 'SERIES-PARTIAL-SUM (list 'u j) k)))
                          (fact 'nn-in-rr k) (fact 'nn-in-rr bigN)
                          (fact 'rr-le-total k bigN)
                          (use-cases (list (list '<= k bigN) (list '<= bigN k))
                            (lambda ()
                              (fact 'series-partial-sum-mono bigN k (list 'u j))
                              (dn-ineq (list '<= (list 'SERIES-PARTIAL-SUM (list 'u j) k)
                                                 (list 'SERIES-PARTIAL-SUM (list 'u j) bigN))
                                       (list '<= (list 'SERIES-PARTIAL-SUM (list 'u j) bigN) d)
                                       (list '= (list '+ d d) eps)
                                       (list '<= 0 d)))
                            (lambda ()
                              (fact 'series-block-le k bigN (list 'u j) 'g)
                              (inst+ tail k)
                              (fact 'series-partial-sum-in-rr k 'g)
                              (fact 'series-partial-sum-in-rr bigN 'g)
                              (dn-ineq (list '<= (list '- (list 'SERIES-PARTIAL-SUM (list 'u j) k)
                                                          (list 'SERIES-PARTIAL-SUM (list 'u j) bigN))
                                                 (list '- (list 'SERIES-PARTIAL-SUM 'g k)
                                                          (list 'SERIES-PARTIAL-SUM 'g bigN)))
                                       (list '<= (list '- (list 'SERIES-PARTIAL-SUM 'g k)
                                                          (list 'SERIES-PARTIAL-SUM 'g bigN)) d)
                                       (list '<= (list 'SERIES-PARTIAL-SUM (list 'u j) bigN) d)
                                       (list '= (list '+ d d) eps)))))))
                    ;; ... and so is the limit
                    (inst+ dc-sum j)
                    (mac-h 'series-converges-to
                           (list 'SERIES-CONVERGES-TO (list 'u j) (list 'e j)))
                    (fact 'rr-limit-abs-le psq (list 'e j) eps)
                    (mac 'rr-ms-dist)
                    (have! (list '= (list '- (list 'e j) 0) (list 'e j))
                      (lambda () (crs)))
                    (subst (list '= (list '- (list 'e j) 0) (list 'e j)))
                    (ass))))))))))) 
(qed 'dominated-null-series)
(topic! 'dominated-null-series 'analysis)
(alias! 'dominated-null-series "dominated convergence for real series"
        "a dominated, pointwise-null family of nonnegative series has vanishing sums")

;;; =====================================================================
;;; L8.  rr-limit-unique -- MOVED 2026-09-01 to
;;; theorem-library/metric-limit-unique.scm, where it is one of two three-line
;;; instances of `metric-limit-unique': a sequence in ANY metric space has at
;;; most one limit.
;;;
;;; The proof that stood here was sixty lines and none of them was about limits.
;;; It unfolded (DIST RR-MS) to `abs' by `rr-ms-dist' and then spent its length
;;; on rr-abs-* bookkeeping -- rr-le-abs, rr-neg-abs-le, rr-abs-sub-sym,
;;; rr-abs-closed -- putting the two eps/2 estimates in front of the oracle,
;;; twice, once per direction.  In the abstract metric there is no absolute
;;; value to open: metric-triangle and metric-sym give
;;; d(lm1,lm2) <= d(f(n),lm1) + d(f(n),lm2) directly, one lane instead of two,
;;; and metric-zero-eq finishes.  Both proofs are `modulo 0'; the general one is
;;; shorter, and it also yields `cc-limit-unique', which is what makes a complex
;;; series limit describable by IOTA.
;;;
;;; The statement is unchanged, so every citation below (L9's `fact
;;; rr-limit-unique' at the SERIES-LIMIT description, and the citers in
;;; limit-arithmetic and antiderivable-uniform-limit) sees the formula it always
;;; saw.  The instance carries no extra hypothesis: CONVERGES-TO's own first
;;; three conjuncts are IS-METRIC-SPACE(s), the FUN typing and the PTS typing,
;;; so `rr-is-metric-space' is NOT cited and no bill moved.
;;; =====================================================================

;;; =====================================================================
;;; L9.  SERIES-LIMIT, and the theorem that makes it usable.
;;;
;;; With uniqueness in hand the sum of a convergent real series can be NAMED:
;;;    SERIES-LIMIT(f)  =  IOTA lm_. SERIES-CONVERGES-TO(f, lm_).
;;; `iota-d' posts existence-and-uniqueness; existence is SERIES-CONVERGES
;;; unfolded and uniqueness is L8.  This is the ell^1 norm of a nonnegative
;;; sequence, and the shape the product metric's D_w wants.
;;; =====================================================================

(def-functoid 'SERIES-LIMIT '(f)
  '(IOTA lm_ (SERIES-CONVERGES-TO f lm_)))
(notation! 'SERIES-LIMIT 'kind 'functoid 'arity 1
           'english "the sum of the series $1"
           'noun "sum of the series $1")

(sp (make-wff "forall([f in fun(nn,rr)], series-converges(f) implies
     series-converges-to(f, series-limit(f)))"))
(dn-di-landed!) (dn-di-landed!)
(mac 'series-limit)
(define sl-iota '(IOTA lm_ (SERIES-CONVERGES-TO f lm_)))
(define sl-psq '(VNB-LAMBDA k NN (SERIES-PARTIAL-SUM f k)))
(for-each
 (lambda (l)
   (dk-focus! l)
   (if (eq? (car (dk-goal)) 'SERIES-CONVERGES-TO)
       (ass)                                      ; the defining property, assumed
       ;; the existence-and-uniqueness obligation
       (begin
         (mac-h 'series-converges '(SERIES-CONVERGES f))
         (let* ((cex (dk-landed-1 (lambda () (mac-h 'converges (list 'CONVERGES 'RR-MS sl-psq)))))
                (lm  (dn-skolem! cex))
                (cvt (dn-find 'conv (dk-head? 'CONVERGES-TO))))
           (fact 'series-partial-sum-seq-in-fun 'f)
           (have! (list 'IN lm 'RR)
             (lambda ()
               (dk-split! (dk-landed-find (lambda () (mac-h 'converges-to cvt))
                                          (lambda (a) (eq? (car a) 'AND))))
               (slot-h 'PTS (list 'IN lm '(PTS RR-MS)))
               (ass)))
           (ew lm)
           (dn-and!
            (lambda ()
              (let ((gl (dk-goal)))
                (cond ((eq? (car gl) 'IN) (ass))
                      ((eq? (car gl) 'SERIES-CONVERGES-TO) (mac 'series-converges-to) (ass))
                      (else
                       (let* ((yt (dn-di-landed-1!))
                              (y  (caddr yt)))
                         (let ((ycv (dk-landed-1
                                     (lambda () (mac-h 'series-converges-to yt)))))
                           (have! (list 'IN y 'RR)
                             (lambda ()
                               (dk-split! (dk-landed-find
                                           (lambda () (mac-h 'converges-to ycv))
                                           (lambda (a) (eq? (car a) 'AND))))
                               (slot-h 'PTS (list 'IN y '(PTS RR-MS)))
                               (ass))))
                         (fact 'rr-limit-unique sl-psq lm y)
                         (ass)))))))))))
 (dk-opened (lambda () (iota-d sl-iota))))
(qed 'series-limit-converges-to)
(topic! 'series-limit-converges-to 'analysis)
(alias! 'series-limit-converges-to
        "a convergent series converges to its sum")

;;; The sum of a convergent real series is a REAL -- i.e. the description is
;;; DEFINED.  Without it SERIES-LIMIT cannot be used inside a VNB-LAMBDA (the
;;; lam-t body obligation is exactly this), so it is what makes
;;;    (VNB-LAMBDA j_ NN (SERIES-LIMIT (u j_)))  in  FUN(NN,RR)
;;; available as the `e' of dominated-null-series.
(sp (make-wff "forall([f in fun(nn,rr)], series-converges(f) implies
     series-limit(f) in rr)"))
(dn-di-landed!) (dn-di-landed!)
(fact 'series-limit-converges-to 'f)
(mac-h 'series-converges-to
       '(SERIES-CONVERGES-TO f (SERIES-LIMIT f)))
(dk-split! (dk-landed-find
            (lambda () (mac-h 'converges-to (dn-find 'conv (dk-head? 'CONVERGES-TO))))
            (lambda (a) (eq? (car a) 'AND))))
(slot-h 'PTS '(IN (SERIES-LIMIT f) (PTS RR-MS)))
(ass)
(qed 'series-limit-in-rr)
(topic! 'series-limit-in-rr 'analysis)
(alias! 'series-limit-in-rr "the sum of a convergent real series is real")

;;; =====================================================================
;;; L10.  SERIES CONVERGENCE IS CLOSED UNDER ADDITION (nonnegative terms).
;;;
;;; The tree had NO linearity for SERIES-CONVERGES -- neither a sum nor a
;;; scalar multiple -- which is what stops the ell^1 statement of dominated
;;; convergence: the difference |x_j(k) - x(k)| is dominated by a(k) + a(k)
;;; and by nothing smaller, so the dominator of the ell^1 argument is a SUM of
;;; two convergent series and the theory could not say it converges.
;;;
;;; For NONNEGATIVE terms it needs no limit arithmetic: the partial sums add
;;; (L10a, one induction), each summand's partial sums are bounded
;;; (`monotone-convergent-bounded-above'), so the sum's partial sums are
;;; nondecreasing and bounded, and `monotone-convergence-rr' finishes.  The
;;; general (signed) case does want lim(f+g) = lim f + lim g and is not here.
;;; =====================================================================

(sp (make-wff "forall([k in nn, f in fun(nn,rr), g in fun(nn,rr), h in fun(nn,rr)],
     forall([i_ in nn], h(i_) = f(i_) + g(i_)) implies
     series-partial-sum(h,k) = series-partial-sum(f,k) + series-partial-sum(g,k))"))
(define pa-br (use-induction))
(dk-focus! (cdr (assq 'base pa-br)))
(dn-di-landed!) (dn-di-landed!)
(mac 'series-partial-sum-zero)
(arith)
(dk-focus! (cdr (assq 'step pa-br)))
(define pa-k  (cadr (dn-find 'k (dk-head? 'IN))))
(define pa-ih (dn-find 'ih (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                                            (dk-contains? a 'FUN)))))
(dn-di-landed!)
(define pa-pw (dn-di-landed-1!))
;; guarded on its two arguments being real since 2026-08-29, and it rewrites all
;; THREE partial sums here, so h needs its typings too -- it did not before.
(fact 'fun-apply-type-c 'f 'NN 'RR pa-k)
(fact 'fun-apply-type-c 'g 'NN 'RR pa-k)
(fact 'fun-apply-type-c 'h 'NN 'RR pa-k)
(fact 'series-partial-sum-in-rr pa-k 'f)
(fact 'series-partial-sum-in-rr pa-k 'g)
(fact 'series-partial-sum-in-rr pa-k 'h)
(mac 'series-partial-sum-succ)
(let* ((a1 (dk-deepest (lambda () (inst+ pa-ih 'f))))
       (a2 (dk-deepest (lambda () (inst+ a1 'g))))
       (a3 (dk-deepest (lambda () (inst+ a2 'h)))))
  (inst+ pa-pw pa-k)
  (subst a3)
  (subst (list '= (list 'h pa-k) (list '+ (list 'f pa-k) (list 'g pa-k))))
  (crs))
(qed 'series-partial-sum-add)
(topic! 'series-partial-sum-add 'analysis)
(alias! 'series-partial-sum-add "partial sums add")

;;; The partial sums of a convergent NONNEGATIVE series are bounded above, in
;;; the SURFACE form (about SERIES-PARTIAL-SUM, not about the lambda).  The
;;; lambda-to-surface step is done on the GOAL with the `-rev' macete rather
;;; than on the assumption with `mac-h': the bound universal comes back from
;;; the skolemizer with its lambda binder RENAMED, and `mac-h' will not match
;;; an alpha-variant (it reports "does not occur in the cited assumption").
(sp (make-wff "forall([f in fun(nn,rr)], forall([i_ in nn], 0 <= f(i_)) implies
     series-converges(f) implies
     forsome([bnd in rr], forall([kx in nn], series-partial-sum(f,kx) <= bnd)))"))
(dn-di-landed!) (dn-di-landed!) (dn-di-landed!)
(define sb-seq '(VNB-LAMBDA k NN (SERIES-PARTIAL-SUM f k)))
(fact 'series-partial-sum-seq-in-fun 'f)
(mac-h 'series-converges '(SERIES-CONVERGES f))
(define sb-step (dk-fact! 'series-partial-sum-monotone-nonneg 'f))
(have! (list 'FORALL 'k (list 'IMPLIES '(IN k NN)
         (list '<= (list sb-seq 'k) (list sb-seq '(succ k)))))
  (lambda ()
    (let ((k (cadr (dn-di-landed-1!))))
      (fact 'nn-succ-closed k)
      (mac 'series-partial-sum-seq-apply)
      (inst+ sb-step k)
      (ass))))
(let* ((bex (dk-fact! 'monotone-convergent-bounded-above sb-seq))
       (bnd (dn-skolem! bex))
       (bfa (dn-find 'bound
              (lambda (a) (and (pair? a) (eq? (car a) 'FORALL) (dk-contains? a bnd))))))
  (ew bnd)
  (dn-and!
   (lambda ()
     (if (eq? (car (dk-goal)) 'IN) (ass)
         (let ((k (cadr (dn-di-landed-1!))))
           ;; the skolemized bound universal carries an ALPHA-RENAMED copy of
           ;; the partial-sum lambda, so the redex is read off the landed
           ;; instance and beta-reduced inside a `have!' -- neither `mac-h' nor
           ;; `ass' matches an alpha-variant here.
           (let* ((inst (dk-deepest (lambda () (inst+ bfa k))))
                  (app  (cadr inst)))
             (have! (list '= (list 'SERIES-PARTIAL-SUM 'f k) app)
               (lambda ()
                 (fact 'series-partial-sum-in-rr k 'f)
                 (lam-b)
                 (rfl)))
             (subst (list '= (list 'SERIES-PARTIAL-SUM 'f k) app))
             (ass)))))))
(qed 'series-partial-sum-bounded)
(topic! 'series-partial-sum-bounded 'analysis)
(alias! 'series-partial-sum-bounded
        "the partial sums of a convergent nonnegative series are bounded")

;;; ... and so the sum of two convergent nonnegative series converges.  Stated
;;; in TRANSFER form (`h' agrees pointwise with f + g) for the same reason as
;;; rr-null-sum: a conclusion about the literal lambda would need a beta under
;;; a binder at every application site.
(sp (make-wff "forall([f in fun(nn,rr), g in fun(nn,rr), h in fun(nn,rr)],
     forall([i_ in nn], 0 <= f(i_)) implies
     forall([i_ in nn], 0 <= g(i_)) implies
     forall([i_ in nn], h(i_) = f(i_) + g(i_)) implies
     series-converges(f) implies series-converges(g) implies
     series-converges(h))"))
(dn-di-landed!)
(define cs-nf (dn-di-landed-1!))
(define cs-ng (dn-di-landed-1!))
(define cs-pw (dn-di-landed-1!))
(dn-di-landed!) (dn-di-landed!)
(define cs-psh '(VNB-LAMBDA k NN (SERIES-PARTIAL-SUM h k)))
(have! '(FORALL i_ (IMPLIES (IN i_ NN) (<= 0 (h i_))))
  (lambda ()
    (let ((i (cadr (dn-di-landed-1!))))
      (inst+ cs-nf i) (inst+ cs-ng i) (inst+ cs-pw i)
      (fact 'fun-apply-type-c 'f 'NN 'RR i)
      (fact 'fun-apply-type-c 'g 'NN 'RR i)
      (fact 'fun-apply-type-c 'h 'NN 'RR i)
      (dn-ineq (list '<= 0 (list 'f i)) (list '<= 0 (list 'g i))
               (list '= (list 'h i) (list '+ (list 'f i) (list 'g i)))))))
(define cs-nh (dn-find 'hnonneg
                (lambda (a) (and (pair? a) (eq? (car a) 'FORALL) (dk-contains? a 'h)
                                 (dk-contains? a '<=)))))
(fact 'series-partial-sum-seq-in-fun 'h)
(define cs-sth (dk-fact! 'series-partial-sum-monotone-nonneg 'h))
(have! (list 'FORALL 'k (list 'IMPLIES '(IN k NN)
         (list '<= (list cs-psh 'k) (list cs-psh '(succ k)))))
  (lambda ()
    (let ((k (cadr (dn-di-landed-1!))))
      (fact 'nn-succ-closed k)
      (mac 'series-partial-sum-seq-apply)
      (inst+ cs-sth k)
      (ass))))
(let* ((fex (dk-fact! 'series-partial-sum-bounded 'f))
       (bf  (dn-skolem! fex))
       (bfa (dn-find 'fbound
              (lambda (a) (and (pair? a) (eq? (car a) 'FORALL) (dk-contains? a bf)))))
       (gex (dk-fact! 'series-partial-sum-bounded 'g))
       (bg  (dn-skolem! gex))
       (bga (dn-find 'gbound
              (lambda (a) (and (pair? a) (eq? (car a) 'FORALL) (dk-contains? a bg))))))
  (have! (list 'AND (list 'IN bf 'RR) (list 'IN bg 'RR)))
  (fact 'rr-add-closed bf bg)
  (have! (list 'FORSOME 'bnd (list 'AND '(IN bnd RR)
           (list 'FORALL 'k (list 'IMPLIES '(IN k NN)
                                  (list '<= (list cs-psh 'k) 'bnd)))))
    (lambda ()
      (ew (list '+ bf bg))
      (dn-and!
       (lambda ()
         (if (eq? (car (dk-goal)) 'IN) (ass)
             (let ((k (cadr (dn-di-landed-1!))))
               (mac 'series-partial-sum-seq-apply)
               (fact 'series-partial-sum-add k 'f 'g 'h)
               (inst+ bfa k) (inst+ bga k)
               (fact 'series-partial-sum-in-rr k 'f)
               (fact 'series-partial-sum-in-rr k 'g)
               (fact 'series-partial-sum-in-rr k 'h)
               (dn-ineq (list '= (list 'SERIES-PARTIAL-SUM 'h k)
                                 (list '+ (list 'SERIES-PARTIAL-SUM 'f k)
                                          (list 'SERIES-PARTIAL-SUM 'g k)))
                        (list '<= (list 'SERIES-PARTIAL-SUM 'f k) bf)
                        (list '<= (list 'SERIES-PARTIAL-SUM 'g k) bg)))))))))
(have! (list 'AND
        (list 'FORALL 'k (list 'IMPLIES '(IN k NN)
                               (list '<= (list cs-psh 'k) (list cs-psh '(succ k)))))
        (list 'FORSOME 'bnd (list 'AND '(IN bnd RR)
           (list 'FORALL 'k (list 'IMPLIES '(IN k NN)
                                  (list '<= (list cs-psh 'k) 'bnd)))))))
(fact 'monotone-convergence-rr cs-psh)
(mac 'series-converges)
(ass)
(qed 'series-converges-sum)
(topic! 'series-converges-sum 'analysis)
(alias! 'series-converges-sum
        "the sum of two convergent nonnegative series converges")

;;; =====================================================================
;;; L11.  THE COMPLEX LAYER.  Two facts about CC-MS that the tree did not
;;; have and that any ell^1 argument lands on immediately.
;;;
;;; `cc-ms-dist' is the exact analogue of `rr-ms-dist'
;;; (theorem-library/rr-ms-dist.scm) and exists for the same reason: unfolding
;;; a metric predicate at CC-MS leaves ((DIST CC-MS) u v), and every complex
;;; estimate has to walk that accessor down to `magnitude' first.  Three steps:
;;; the slot equation (a macete -- the accessor is in OPERATOR position, where
;;; `subst' cannot reach), the tupled beta, and qrfl.
;;; =====================================================================

(sp (make-wff (forall-guarded '(u_ v_) '((IN u_ CC) (IN v_ CC))
      '(== ((DIST CC-MS) u_ v_) (magnitude (- u_ v_))))))
(di) (di) (di)
(slot 'DIST)
(lam-b)
(qrfl)
(qed 'cc-ms-dist)
(topic! 'cc-ms-dist 'analysis)
(alias! 'cc-ms-dist "the distance of CC-MS is the magnitude of the difference")

;;; |p - q| <= |p| + |q|:  the triangle inequality at (p, -q), with
;;; p + (-q) = p - q by `crs' and |-q| = |q| by cc-magnitude-neg.
(sp (make-wff "forall([p_ in cc, q_ in cc],
     magnitude(p_ - q_) <= magnitude(p_) + magnitude(q_))"))
(dn-di-landed!)
(fact 'cc-neg-closed 'q_)
(have! '(AND (IN p_ CC) (IN (- q_) CC)))
(fact 'cc-magnitude-triangle 'p_ '(- q_))
(fact 'cc-add-closed 'p_ '(- q_))
(fact 'cc-magnitude-neg 'q_)
(fact 'cc-magnitude-closed 'p_)
(fact 'cc-magnitude-closed 'q_)
(fact 'cc-magnitude-closed '(- q_))
(fact 'cc-sub-in-cc 'p_ 'q_)
(fact 'cc-magnitude-closed '(- p_ q_))
(fact 'cc-magnitude-closed '(+ p_ (- q_)))
(have! '(= (- p_ q_) (+ p_ (- q_))) (lambda () (crs)))
(subst '(= (- p_ q_) (+ p_ (- q_))))
(dn-ineq '(<= (magnitude (+ p_ (- q_))) (+ (magnitude p_) (magnitude (- q_))))
         '(= (magnitude (- q_)) (magnitude q_)))
(qed 'cc-magnitude-sub-triangle)
(topic! 'cc-magnitude-sub-triangle 'analysis)
(alias! 'cc-magnitude-sub-triangle "the magnitude of a difference is at most the sum")

;;; |p - q| = |q - p|, and |p| <= |p - q| + |q|.  Both are the complex
;;; counterparts of `rr-abs-sub-sym' / the abs estimate the RR limit lemmas
;;; use.  The pattern in each is the same and is worth stating once: `ineq'
;;; reads magnitude(t) as an OPAQUE ATOM, so an identity between the ARGUMENTS
;;; (crs) is of no use to it -- the rewriting has to happen inside a `have!'
;;; that produces an equation between the MAGNITUDES.
(sp (make-wff "forall([p_ in cc, q_ in cc],
     magnitude(p_ - q_) = magnitude(q_ - p_))"))
(dn-di-landed!)
(fact 'cc-sub-in-cc 'p_ 'q_)
(fact 'cc-sub-in-cc 'q_ 'p_)
(have! '(= (- q_ p_) (- (- p_ q_))) (lambda () (crs)))
(subst '(= (- q_ p_) (- (- p_ q_))))
(fact 'cc-magnitude-neg-rev '(- p_ q_))
(ass)
(qed 'cc-magnitude-sub-sym)
(topic! 'cc-magnitude-sub-sym 'analysis)
(alias! 'cc-magnitude-sub-sym "the magnitude of a difference is symmetric")

(sp (make-wff "forall([p_ in cc, q_ in cc],
     magnitude(p_) <= magnitude(p_ - q_) + magnitude(q_))"))
(dn-di-landed!)
(fact 'cc-sub-in-cc 'p_ 'q_)
(have! '(AND (IN (- p_ q_) CC) (IN q_ CC)))
(fact 'cc-magnitude-triangle '(- p_ q_) 'q_)
(fact 'cc-add-closed '(- p_ q_) 'q_)
(fact 'cc-magnitude-closed 'p_)
(fact 'cc-magnitude-closed 'q_)
(fact 'cc-magnitude-closed '(- p_ q_))
(fact 'cc-magnitude-closed '(+ (- p_ q_) q_))
(have! '(= (magnitude (+ (- p_ q_) q_)) (magnitude p_))
  (lambda ()
    (have! '(= (+ (- p_ q_) q_) p_) (lambda () (crs)))
    (subst '(= (+ (- p_ q_) q_) p_))
    (rfl)))
(dn-ineq '(<= (magnitude (+ (- p_ q_) q_)) (+ (magnitude (- p_ q_)) (magnitude q_)))
         '(= (magnitude (+ (- p_ q_) q_)) (magnitude p_)))
(qed 'cc-magnitude-le-add)
(topic! 'cc-magnitude-le-add 'analysis)
(alias! 'cc-magnitude-le-add "the magnitude is at most the difference plus the subtrahend")

;;; A complex limit inherits a uniform bound on the magnitude -- the CC-MS
;;; counterpart of L2, and what says that the pointwise limit of a family
;;; dominated by `a' is itself dominated by `a'.
(sp (make-wff "forall([s_ in fun(nn,cc), lv in cc, bd in rr],
     converges-to(cc-ms, s_, lv) implies
     forall([n_ in nn], magnitude(s_(n_)) <= bd) implies
     magnitude(lv) <= bd)"))
(di)(di)(di)
(define cl-pt (dn-find 'bound
                (lambda (a) (and (pair? a) (eq? (car a) 'FORALL) (dk-contains? a 'magnitude)))))
(dk-split! (dk-landed-find (lambda () (mac-h 'converges-to '(CONVERGES-TO CC-MS s_ lv)))
                           (lambda (a) (eq? (car a) 'AND))))
(define cl-tail (dn-find 'tail (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                                                (dk-contains? a 'POS-RR)))))
(fact 'cc-magnitude-closed 'lv)
(have! '(IN (- (magnitude lv) bd) RR)
  (lambda () (fact 'rr-sub-in-rr '(magnitude lv) 'bd) (ass)))
(have! '(FORALL eps (IMPLIES (POS-RR eps) (<= (- (magnitude lv) bd) eps)))
  (lambda ()
    (let* ((eps (cadr (dn-di-landed-1!)))
           (ex  (dk-deepest (lambda () (inst+ cl-tail eps))))
           (bigN (dn-skolem! ex))
           (inner (dn-find 'inner
                    (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                                     (let ((b (caddr a)))
                                       (and (pair? b) (eq? (car b) 'IMPLIES)
                                            (dk-contains? (caddr b) bigN)))))))
           (sN (list 's_ bigN)))
      (fact 'nn-in-rr bigN)
      (fact 'rr-leq-reflexive bigN)
      (inst+ inner bigN)
      (inst+ cl-pt bigN)
      (fact 'fun-apply-type-c 's_ 'NN 'CC bigN)
      (mac-h 'cc-ms-dist (list '<= (list (list 'DIST 'CC-MS) sN 'lv) eps))
      (dn-pos-in-rr! eps)
      (fact 'cc-magnitude-le-add 'lv sN)
      (fact 'cc-magnitude-sub-sym 'lv sN)
      (fact 'cc-sub-in-cc 'lv sN)
      (fact 'cc-sub-in-cc sN 'lv)
      (fact 'cc-magnitude-closed sN)
      (fact 'cc-magnitude-closed (list '- 'lv sN))
      (fact 'cc-magnitude-closed (list '- sN 'lv))
      (dn-ineq (list '<= '(magnitude lv)
                         (list '+ (list 'magnitude (list '- 'lv sN))
                                  (list 'magnitude sN)))
               (list '= (list 'magnitude (list '- 'lv sN))
                        (list 'magnitude (list '- sN 'lv)))
               (list '<= (list 'magnitude (list '- sN 'lv)) eps)
               (list '<= (list 'magnitude sN) 'bd)))))
(fact 'rr-le-all-pos-nonpos '(- (magnitude lv) bd))
(dn-ineq '(<= (- (magnitude lv) bd) 0))
(qed 'cc-limit-magnitude-le)
(topic! 'cc-limit-magnitude-le 'analysis)
(alias! 'cc-limit-magnitude-le "a complex limit inherits a uniform magnitude bound")

;;; Convergence in CC-MS IS the vanishing of the magnitude of the difference,
;;; as a REAL null sequence -- the bridge that turns the ell^1 hypothesis
;;; "x_j(k) -> x(k) for each k" into the coordinatewise hypothesis of
;;; dominated-null-series.  Transfer form again (`m' agrees pointwise).
(sp (make-wff "forall([s_ in fun(nn,cc), lv in cc, m in fun(nn,rr)],
     converges-to(cc-ms, s_, lv) implies
     forall([j_ in nn], m(j_) = magnitude(s_(j_) - lv)) implies
     converges-to(rr-ms, m, 0))"))
(di)(di)(di)
(define cn-pt (dn-find 'pointwise
                (lambda (a) (and (pair? a) (eq? (car a) 'FORALL) (dk-contains? a 'm)))))
(dk-split! (dk-landed-find (lambda () (mac-h 'converges-to '(CONVERGES-TO CC-MS s_ lv)))
                           (lambda (a) (eq? (car a) 'AND))))
(define cn-tail (dn-find 'tail (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                                                (dk-contains? a 'POS-RR)))))
(fact 'rr-zero-in)
(dn-converges-to!
 (lambda ()
   (let* ((eps (cadr (dn-di-landed-1!)))
          (ex  (dk-deepest (lambda () (inst+ cn-tail eps))))
          (bigN (dn-skolem! ex))
          (inner (dn-find 'inner
                   (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                                    (let ((b (caddr a)))
                                      (and (pair? b) (eq? (car b) 'IMPLIES)
                                           (dk-contains? (caddr b) bigN))))))))
     (ew bigN)
     (dn-and!
      (lambda ()
        (if (eq? (car (dk-goal)) 'IN) (ass)
            (let* ((j (cadr (dn-di-landed-1!)))
                   (sj (list 's_ j))
                   (dj (list '- sj 'lv))
                   (mj (list 'm j)))
              (dn-di-landed!)                        ; bigN <= j
              (inst+ inner j)
              (inst+ cn-pt j)
              (fact 'fun-apply-type-c 's_ 'NN 'CC j)
              (fact 'fun-apply-type-c 'm 'NN 'RR j)
              (mac-h 'cc-ms-dist (list '<= (list (list 'DIST 'CC-MS) sj 'lv) eps))
              (fact 'cc-sub-in-cc sj 'lv)
              (fact 'cc-magnitude-nonneg dj)
              (fact 'cc-magnitude-closed dj)
              (dn-pos-in-rr! eps)
              (have! (list '<= 0 mj)
                (lambda () (dn-ineq (list '= mj (list 'magnitude dj))
                                    (list '<= 0 (list 'magnitude dj)))))
              (mac 'rr-ms-dist)
              (have! (list '= (list '- mj 0) mj) (lambda () (crs)))
              (subst (list '= (list '- mj 0) mj))
              (fact 'rr-abs-of-nonneg mj)
              (subst (list '= (list 'abs mj) mj))
              (dn-ineq (list '= mj (list 'magnitude dj))
                       (list '<= (list 'magnitude dj) eps)))))))))
(qed 'cc-converges-magnitude-null)
(topic! 'cc-converges-magnitude-null 'analysis)
(alias! 'cc-converges-magnitude-null
        "complex convergence is the vanishing of the magnitude of the difference")

;;; =====================================================================
;;; L12.  ELL-ONE, and DOMINATED CONVERGENCE IN ELL-ONE.
;;; =====================================================================

(def-constant 'ELL-ONE
  '(ell-one-def
    (= ELL-ONE
       (SEP x_ (SQN CC)
            (SERIES-CONVERGES (VNB-LAMBDA k_ NN (magnitude (x_ k_))))))))
(notation! 'ELL-ONE 'kind 'constant 'arity 0
           'english "the absolutely summable complex sequences"
           'tex "\\ell^1")

(sp (make-wff "forall([y_], y_ in ell-one iff
     (y_ in sqn(cc) and series-converges(vnb-lambda(k_, nn, magnitude(y_(k_))))))"))
(mac 'ell-one-def)
(define e1-sep '(SEP x_ (SQN CC)
                  (SERIES-CONVERGES (VNB-LAMBDA k_ NN (magnitude (x_ k_))))))
(fact 'cc-is-set)
(fact 'sqn-sethood 'CC)
(for-each
 (lambda (l)
   (dk-focus! l)
   (if (eq? (car (dk-goal)) 'AND)
       ;; forward: separation ELIMINATION splits the membership
       (begin (sep-me (list 'IN 'y_ e1-sep))
              (dn-and! (lambda () (ass))))
       ;; backward: separation INTRODUCTION, from the two conjuncts
       (begin (dk-split! (dn-find 'conj (dk-head? 'AND)))
              (for-each (lambda (k) (dk-focus! k) (ass))
                        (dk-opened (lambda () (sep-mi)))))))
 (dk-opened (lambda () (di) (di))))
(qed 'ell-one-membership)
(topic! 'ell-one-membership 'analysis)
(alias! 'ell-one-membership "membership in ell^1")

;;; DOMINATED CONVERGENCE IN ELL-ONE.
;;;
;;;   x_j in SQN(CC),  |x_j(k)| <= a(k) with Sum a convergent,
;;;   x_j(k) -> x(k) in CC for each k
;;;     =>  x in ELL-ONE  and  ||x_j - x||_1 -> 0.
;;;
;;; The dominator is stated as a real sequence `a' with a convergent series
;;; rather than as an element of ELL-ONE: for a NONNEGATIVE real sequence the
;;; two say the same thing (|a(k)| = a(k)), and nonnegativity here is free --
;;; a(k) >= |x_0(k)| >= 0.
;;;
;;; The ell^1 norms are carried by a sequence `e' with e(j) = SERIES-LIMIT of
;;; the magnitude sequence of x_j - x, which is exactly ||x_j - x||_1 now that
;;; SERIES-LIMIT is a defined term (L9).
(sp (make-wff "forall([a_ in fun(nn,rr), x in sqn(cc), e in fun(nn,rr)], forall([xs],
  forall([j_ in nn], xs(j_) in sqn(cc)) implies
  series-converges(a_) implies
  forall([j_ in nn], forall([k_ in nn], magnitude(xs(j_)(k_)) <= a_(k_))) implies
  forall([k_ in nn], converges-to(cc-ms, vnb-lambda(j_, nn, xs(j_)(k_)), x(k_))) implies
  forall([j_ in nn], e(j_) = series-limit(vnb-lambda(k_, nn, magnitude(xs(j_)(k_) - x(k_)))))
    implies
  (x in ell-one and converges-to(rr-ms, e, 0))))"))
(dn-di-landed!)                                   ; a_, x, e typings
(mac-h 'sqn-membership '(IN x (SQN CC)))          ; x in FUN(NN,CC)
(define ec-xt (dn-di-landed-1!))                  ; forall j. xs(j) in SQN(CC)
(define ec-sc (dn-di-landed-1!))                  ; series-converges(a_)
(define ec-dom (dn-di-landed-1!))                 ; the domination hypothesis
(define ec-cv  (dn-di-landed-1!))                 ; coordinatewise CC convergence
(define ec-ne  (dn-di-landed-1!))                 ; e(j) is the ell^1 norm

;;; the typing hypothesis, with SQN unfolded
(have! '(FORALL j_ (IMPLIES (IN j_ NN) (IN (xs j_) (FUN NN CC))))
  (lambda ()
    (let ((j (cadr (dn-di-landed-1!))))
      (inst+ ec-xt j)
      (mac-h 'sqn-membership (list 'IN (list 'xs j) '(SQN CC)))
      (ass))))
(define ec-xf (dn-find 'xsfun
                (lambda (a) (and (pair? a) (eq? (car a) 'FORALL) (dk-contains? a 'FUN)
                                 (dk-contains? a 'xs)))))

;;; a is NONNEGATIVE -- free, since a(k) >= |x_0(k)| >= 0.
(fact 'nn-zero-in)
(have! '(FORALL k_ (IMPLIES (IN k_ NN) (<= 0 (a_ k_))))
  (lambda ()
    (let ((k (cadr (dn-di-landed-1!))))
      (inst+ ec-xf 0)
      (let ((d0 (dk-deepest (lambda () (inst+ ec-dom 0)))))
        (inst+ d0 k))
      (fact 'fun-apply-type-c '(xs 0) 'NN 'CC k)
      (fact 'cc-magnitude-nonneg (list '(xs 0) k))
      (fact 'cc-magnitude-closed (list '(xs 0) k))
      (fact 'fun-apply-type-c 'a_ 'NN 'RR k)
      (dn-ineq (list '<= 0 (list 'magnitude (list '(xs 0) k)))
               (list '<= (list 'magnitude (list '(xs 0) k)) (list 'a_ k))))))
(define ec-anon (dn-find 'anonneg
                  (lambda (a) (and (pair? a) (eq? (car a) 'FORALL) (dk-contains? a 'a_)
                                   (dk-contains? a '<=) (not (dk-contains? a 'magnitude))))))

;;; the LIMIT is dominated by a too -- cc-limit-magnitude-le at each coordinate.
(have! '(FORALL k_ (IMPLIES (IN k_ NN) (<= (magnitude (x k_)) (a_ k_))))
  (lambda ()
    (let* ((k   (cadr (dn-di-landed-1!)))
           (cvk (dk-deepest (lambda () (inst+ ec-cv k))))
           (seq (caddr cvk)))
      (fact 'fun-apply-type-c 'x 'NN 'CC k)
      (fact 'fun-apply-type-c 'a_ 'NN 'RR k)
      (have! (list 'IN seq '(FUN NN CC))
        (lambda ()
          (dk-lam-t!)
          (let ((j (cadr (dn-di-landed-1!))))
            (inst+ ec-xf j)
            (fact 'fun-apply-type-c (list 'xs j) 'NN 'CC k)
            (ass))))
      (have! (list 'FORALL 'n_ (list 'IMPLIES '(IN n_ NN)
                (list '<= (list 'magnitude (list seq 'n_)) (list 'a_ k))))
        (lambda ()
          (let ((n (cadr (dn-di-landed-1!))))
            (lam-b)
            (let ((dn (dk-deepest (lambda () (inst+ ec-dom n)))))
              (inst+ dn k))
            (ass))))
      (fact 'cc-limit-magnitude-le seq (list 'x k) (list 'a_ k))
      (ass))))
(define ec-xbd (dn-find 'xbound
                 (lambda (a) (and (pair? a) (eq? (car a) 'FORALL) (dk-contains? a 'magnitude)
                                  (dk-contains? a 'x) (not (dk-contains? a 'xs))))))
;;; the magnitude sequence of the limit, and the doubled dominator
(define ec-mx '(VNB-LAMBDA k_ NN (magnitude (x k_))))
(have! (list 'IN ec-mx '(FUN NN RR))
  (lambda ()
    (dk-lam-t!)
    (let ((k (cadr (dn-di-landed-1!))))
      (fact 'fun-apply-type-c 'x 'NN 'CC k)
      (fact 'cc-magnitude-closed (list 'x k))
      (ass))))
(have! (list 'AND
         (list 'FORALL 'n (list 'IMPLIES '(IN n NN)
                 (list 'AND (list '<= 0 (list ec-mx 'n))
                            (list '<= (list ec-mx 'n) (list 'a_ 'n)))))
         '(SERIES-CONVERGES a_))
  (lambda ()
    (dn-and!
     (lambda ()
       (if (eq? (car (dk-goal)) 'SERIES-CONVERGES) (ass)
           (let ((n (cadr (dn-di-landed-1!))))
             (lam-b)
             (fact 'fun-apply-type-c 'x 'NN 'CC n)
             (fact 'cc-magnitude-nonneg (list 'x n))
             (inst+ ec-xbd n)
             (dn-and! (lambda () (ass)))))))))
(fact 'comparison-test ec-mx 'a_)

;;; THE DOMINATOR of the differences is a + a, and THAT is why the file needs
;;; series-converges-sum: |x_j(k) - x(k)| <= |x_j(k)| + |x(k)| <= a(k) + a(k),
;;; and nothing smaller works.
(define ec-g2 '(VNB-LAMBDA k_ NN (+ (a_ k_) (a_ k_))))
(have! (list 'IN ec-g2 '(FUN NN RR))
  (lambda ()
    (dk-lam-t!)
    (let ((k (cadr (dn-di-landed-1!))))
      (fact 'fun-apply-type-c 'a_ 'NN 'RR k)
      (have! (list 'AND (list 'IN (list 'a_ k) 'RR) (list 'IN (list 'a_ k) 'RR)))
      (fact 'rr-add-closed (list 'a_ k) (list 'a_ k))
      (ass))))
(have! (list 'FORALL 'k_ (list 'IMPLIES '(IN k_ NN)
         (list '= (list ec-g2 'k_) (list '+ '(a_ k_) '(a_ k_)))))
  (lambda ()
    (let ((k (cadr (dn-di-landed-1!))))
      (fact 'fun-apply-type-c 'a_ 'NN 'RR k)
      (have! (list 'AND (list 'IN (list 'a_ k) 'RR) (list 'IN (list 'a_ k) 'RR)))
      (fact 'rr-add-closed (list 'a_ k) (list 'a_ k))
      (lam-b)
      (rfl))))
(fact 'series-converges-sum 'a_ 'a_ ec-g2)

;;; the family u, and the two universals every antecedent of
;;; dominated-null-series is read off (proved ONCE here rather than at each
;;; antecedent, which would repeat the same triangle estimate three times).
(define ec-u '(VNB-LAMBDA j_ NN (VNB-LAMBDA k_ NN (magnitude (- ((xs j_) k_) (x k_))))))
(define (ec-inner j) (list 'VNB-LAMBDA 'k_ 'NN
                       (list 'magnitude (list '- (list (list 'xs j) 'k_) '(x k_)))))
(have! (list 'FORALL 'j_ (list 'IMPLIES '(IN j_ NN)
         (list 'FORALL 'k_ (list 'IMPLIES '(IN k_ NN)
           (list 'AND (list '<= 0 '(magnitude (- ((xs j_) k_) (x k_))))
                      (list '<= '(magnitude (- ((xs j_) k_) (x k_)))
                                '(+ (a_ k_) (a_ k_))))))))
  (lambda ()
    (let* ((typs (dn-di-landed!))
           (j (cadr (car typs)))
           (k (cadr (if (pair? (cdr typs)) (cadr typs) (car (dn-di-landed!))))))
      (inst+ ec-xf j)
      (fact 'fun-apply-type-c (list 'xs j) 'NN 'CC k)
      (fact 'fun-apply-type-c 'x 'NN 'CC k)
      (fact 'fun-apply-type-c 'a_ 'NN 'RR k)
      (let ((xj (list (list 'xs j) k)) (xk (list 'x k)))
        (fact 'cc-sub-in-cc xj xk)
        (fact 'cc-magnitude-nonneg (list '- xj xk))
        (fact 'cc-magnitude-closed (list '- xj xk))
        (fact 'cc-magnitude-closed xj)
        (fact 'cc-magnitude-closed xk)
        (fact 'cc-magnitude-sub-triangle xj xk)
        (let ((dj (dk-deepest (lambda () (inst+ ec-dom j)))))
          (inst+ dj k))
        (inst+ ec-xbd k)
        (dn-and!
         (lambda ()
           (if (equal? (cadr (dk-goal)) 0) (ass)
               (dn-ineq (list '<= (list 'magnitude (list '- xj xk))
                                  (list '+ (list 'magnitude xj) (list 'magnitude xk)))
                        (list '<= (list 'magnitude xj) (list 'a_ k))
                        (list '<= (list 'magnitude xk) (list 'a_ k))))))))))
(define ec-est (dn-find 'estimate
                 (lambda (a) (and (pair? a) (eq? (car a) 'FORALL) (dk-contains? a 'AND)
                                  (dk-contains? a 'magnitude)))))
(have! (list 'FORALL 'j_ (list 'IMPLIES '(IN j_ NN)
         (list 'IN '(VNB-LAMBDA k_ NN (magnitude (- ((xs j_) k_) (x k_)))) '(FUN NN RR))))
  (lambda ()
    (let ((j (cadr (dn-di-landed-1!))))
      (inst+ ec-xf j)
      (dk-lam-t!)
      (let ((k (cadr (dn-di-landed-1!))))
        (fact 'fun-apply-type-c (list 'xs j) 'NN 'CC k)
        (fact 'fun-apply-type-c 'x 'NN 'CC k)
        (fact 'cc-sub-in-cc (list (list 'xs j) k) (list 'x k))
        (fact 'cc-magnitude-closed (list '- (list (list 'xs j) k) (list 'x k)))
        (ass)))))
(define ec-inty (dn-find 'innertyping
                  (lambda (a) (and (pair? a) (eq? (car a) 'FORALL) (dk-contains? a 'FUN)
                                   (dk-contains? a 'magnitude)))))

;;; ---- the five antecedents of dominated-null-series at (g2, e, u) --------
(have! (list 'FORALL 'j_ (list 'IMPLIES '(IN j_ NN)
         (list 'IN (list ec-u 'j_) '(FUN NN RR))))
  (lambda ()
    (let ((j (cadr (dn-di-landed-1!))))
      (dn-beta!)
      (inst+ ec-inty j)
      (ass))))
(have! (list 'FORALL 'j_ (list 'IMPLIES '(IN j_ NN)
         (list 'FORALL 'i_ (list 'IMPLIES '(IN i_ NN)
           (list 'AND (list '<= 0 (list (list ec-u 'j_) 'i_))
                      (list '<= (list (list ec-u 'j_) 'i_) (list ec-g2 'i_)))))))
  (lambda ()
    (let* ((typs (dn-di-landed!))
           (j (cadr (car typs)))
           (k (cadr (if (pair? (cdr typs)) (cadr typs) (car (dn-di-landed!))))))
      (dn-beta!)
      (let* ((ej (dk-deepest (lambda () (inst+ ec-est j))))
             (ek (dk-deepest (lambda () (inst+ ej k)))))
        (dk-split! ek))
      (dn-and! (lambda () (ass))))))
(have! (list 'FORALL 'i_ (list 'IMPLIES '(IN i_ NN)
         (list 'CONVERGES-TO 'RR-MS
               (list 'VNB-LAMBDA 'j_ 'NN (list (list ec-u 'j_) 'i_)) 0)))
  (lambda ()
    (let* ((i   (cadr (dn-di-landed-1!)))
           (cvi (dk-deepest (lambda () (inst+ ec-cv i))))
           (seq (caddr cvi))
           (m   (list 'VNB-LAMBDA 'j_ 'NN (list (list ec-u 'j_) i))))
      (fact 'fun-apply-type-c 'x 'NN 'CC i)
      (have! (list 'IN seq '(FUN NN CC))
        (lambda ()
          (dk-lam-t!)
          (let ((j (cadr (dn-di-landed-1!))))
            (inst+ ec-xf j)
            (fact 'fun-apply-type-c (list 'xs j) 'NN 'CC i)
            (ass))))
      (have! (list 'IN m '(FUN NN RR))
        (lambda ()
          (dk-lam-t!)
          (let ((j (cadr (dn-di-landed-1!))))
            (dn-beta!)
            (inst+ ec-xf j)
            (fact 'fun-apply-type-c (list 'xs j) 'NN 'CC i)
            (fact 'cc-sub-in-cc (list (list 'xs j) i) (list 'x i))
            (fact 'cc-magnitude-closed (list '- (list (list 'xs j) i) (list 'x i)))
            (ass))))
      (have! (list 'FORALL 'j_ (list 'IMPLIES '(IN j_ NN)
               (list '= (list m 'j_)
                        (list 'magnitude (list '- (list seq 'j_) (list 'x i))))))
        (lambda ()
          (let ((j (cadr (dn-di-landed-1!))))
            (inst+ ec-xf j)
            (fact 'fun-apply-type-c (list 'xs j) 'NN 'CC i)
            (fact 'cc-sub-in-cc (list (list 'xs j) i) (list 'x i))
            (fact 'cc-magnitude-closed (list '- (list (list 'xs j) i) (list 'x i)))
            (dn-beta!)
            (rfl))))
      (fact 'cc-converges-magnitude-null seq (list 'x i) m)
      (ass))))
(have! (list 'FORALL 'j_ (list 'IMPLIES '(IN j_ NN)
         (list 'SERIES-CONVERGES-TO (list ec-u 'j_) '(e j_))))
  (lambda ()
    (let* ((j (cadr (dn-di-landed-1!)))
           (inner (ec-inner j)))
      (dn-beta!)
      (inst+ ec-inty j)
      (have! (list 'AND
               (list 'FORALL 'n (list 'IMPLIES '(IN n NN)
                       (list 'AND (list '<= 0 (list inner 'n))
                                  (list '<= (list inner 'n) (list ec-g2 'n)))))
               (list 'SERIES-CONVERGES ec-g2))
        (lambda ()
          (dn-and!
           (lambda ()
             (if (eq? (car (dk-goal)) 'SERIES-CONVERGES) (ass)
                 (let ((n (cadr (dn-di-landed-1!))))
                   (dn-beta!)
                   (let* ((ej (dk-deepest (lambda () (inst+ ec-est j))))
                          (en (dk-deepest (lambda () (inst+ ej n)))))
                     (dk-split! en))
                   (dn-and! (lambda () (ass)))))))))
      (fact 'comparison-test inner ec-g2)
      (fact 'series-limit-converges-to inner)
      (inst+ ec-ne j)
      (subst (list '= (list 'e j) (list 'SERIES-LIMIT inner)))
      (ass))))
(fact 'dominated-null-series ec-g2 'e ec-u)

;;; ---- the two conjuncts of the conclusion --------------------------------
(dn-and!
 (lambda ()
   (if (eq? (car (dk-goal)) 'CONVERGES-TO)
       (ass)
       (begin (mac 'ell-one-membership)
              (dn-and!
               (lambda ()
                 (if (eq? (car (dk-goal)) 'SERIES-CONVERGES)
                     (ass)
                     (begin (mac 'sqn-membership) (ass)))))))))
(qed 'ell-one-dominated-convergence)
(topic! 'ell-one-dominated-convergence 'analysis)
(alias! 'ell-one-dominated-convergence
        "dominated convergence in ell^1"
        "a dominated, pointwise convergent family in ell^1 converges in ell^1")

