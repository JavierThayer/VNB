;;; product-summable.scm -- THE DEFINING SERIES OF THE PRODUCT METRIC
;;; CONVERGES, proven -- retiring the asserted `product-weighted-summable'
;;; (structure-library/product-metric.scm), which is what makes the IOTA in
;;; PRODUCT-METRIC-W a well-defined distance, and with it the second asserted
;;; support of that file, `product-metric-carrier'.
;;;
;;;   D_w(x,y) = SUM_n w(n) * rho_n(x(n), y(n)),   rho_n = d_n/(1+d_n).
;;;
;;; The analysis is one citation: rho_n < 1 (bdd-metric-bounded), so the term
;;; sequence is dominated by the summable weights and `comparison-test'
;;; finishes.  What had never been exercised is the PLUMBING between the two,
;;; and the lemmas below are exactly that plumbing.  Two of them go further
;;; than the retired support needed and are here because they are the entry
;;; point of every later convergence argument in the product: L6
;;; (`product-metric-distance') is the distance FORMULA -- D_w(x,y) is the sum
;;; of the coordinate series -- and L7 (`product-metric-dist-converges') says
;;; the series converges to it.  The tree had a distance formula for BDD-METRIC
;;; (asserted) and none for the product.
;;;
;;; 1.  READING A COORDINATE OUT OF PRODUCT-CARRIER.  PRODUCT-CARRIER is a
;;;     `def-functoid', so it installs a rewrite macete and no theorem, and
;;;     `mac-h' cannot unfold it in an ASSUMPTION by its own name -- it warns
;;;     `unknown theorem/macete' and the driver sails on with the hypothesis
;;;     untouched.  The standing answer used to be a membership axiom beside
;;;     the constructor.  It is not needed: the unfold EQUATION is provable,
;;;     `modulo 0', in one line --
;;;
;;;         (di) (mac 'PRODUCT-CARRIER) (qrfl)
;;;
;;;     -- because `mac' unfolds a functoid in the GOAL, which is the half that
;;;     works, and `qrfl' closes the resulting X == X.  The result is a
;;;     THEOREM, so `mac-h' rebuilds its rule from the theorem table and
;;;     rewrites the hypothesis into a literal SEP membership that `sep-me'
;;;     reads apart.  `product-carrier-coord' is that readout: x in
;;;     PRODUCT-CARRIER(ms) and n in NN give x(n) in PTS(ms n).
;;;
;;; 2.  TYPING A BOUNDED DISTANCE.  `bdd-metric-weight-bound' packages the three
;;;     facts every term of the series needs -- w(n)*rho_n is real, is
;;;     nonnegative, and is at most w(n) -- so the main driver never opens
;;;     IS-METRIC-SPACE and never touches PTS(BDD-METRIC s).  The carrier
;;;     transfer PTS(BDD-METRIC s) == PTS(s) is done with `mac', not `subst':
;;;     the term to be replaced is in OPERATOR position inside (DIST ...), where
;;;     a Leibniz walk does not reach.  The same operator-position problem
;;;     recurs one level up in L6, where the DIST SLOT of a functoid-built
;;;     structure has to be projected: `slot' rewrites DIST at every
;;;     occurrence, so it is applied twice, with `nth-r' and a TUPLED `lam-b'
;;;     between.
;;;
;;; 3.  NO MULTIPLICATIVE ORDER LEMMA.  w*rho <= w is derived from
;;;     `rr-leq-mul-nonneg' (PRIMITIVE): 0 <= (1-rho)*w, which `crs' rewrites
;;;     to 0 <= w - w*rho.
;;;
;;; WHAT IT COSTS.  `product-weighted-summable' bills six asserted leaves and
;;; not one of them is about the product: four are the bounded-metric supports
;;; of structure-library/bounded-metric.scm (bdd-metric-is-metric-space,
;;; bdd-metric-carrier, bdd-metric-bounded) plus `metric-dist-real', and two are
;;; the NN order backlog (nn-zero-le, nn-le-succ-cases) inherited through
;;; `comparison-test'.  The construction itself is discharged.
;;;
;;; Loads after theorem-library/comparison-test-proof (comparison-test) and
;;; structure-library/product-metric (PRODUCT-CARRIER, IS-MS-SEQUENCE,
;;; SUMMABLE-WEIGHT) and bounded-metric (BDD-METRIC).

;;; ---- file-local driver helpers (the `pm-' prefix) --------------------

(define (pm-and! closer)
  (let ((g (dk-goal)))
    (if (and (pair? g) (eq? (car g) 'AND))
        (for-each (lambda (k) (dk-focus! k) (pm-and! closer))
                  (dk-opened (lambda () (di))))
        (closer))))
(define (pm-and2! a b) (have! (list 'AND a b) (lambda () (pm-and! (lambda () (ass))))))
(define (pm-idx form)
  (let loop ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "pm-idx: not in context" form))
          ((equal? (car l) form) i) (else (loop (cdr l) (+ i 1))))))
(define (pm-ineq . forms) (apply ineq (map pm-idx forms)))
(define (pm-eq! e) (have! e (lambda () (crs))) (subst e))
(define (pm-find what pred)
  (let loop ((l (dk-asms)))
    (cond ((null? l) (error "pm-find: no context formula" what))
          ((pred (car l)) (car l))
          (else (loop (cdr l))))))
(define (pm-di-landed!)
  (let loop ((n 0))
    (let ((new (dk-landed* (lambda () (di)))))
      (cond ((pair? new) new)
            ((> n 5) (error "pm-di-landed!: di landed no assumption"))
            (else (loop (+ n 1)))))))
(define (pm-di-landed-1!)
  (let ((new (pm-di-landed!)))
    (if (null? (cdr new)) (car new)
        (error "pm-di-landed-1!: expected 1" (map expression->string new)))))
(define (pm-split-h! name form)
  (dk-split! (dk-landed-find (lambda () (mac-h name form))
                             (lambda (f) (eq? (car f) 'AND)))))
;; the conjuncts of a context (< a b), landed without destroying it
(define (pm-from-lt! a b)
  (let ((lt (list '< a b)))
    (for-each
     (lambda (part)
       (have! part (lambda ()
                     (dk-split! (dk-landed-find (lambda () (mac-h '< lt))
                                                (lambda (f) (eq? (car f) 'AND))))
                     (ass))))
     (list (list '<= a b) (list 'NOT (list '= a b))))))
(define (pm-peel-to! head)
  (let lp ((k 0))
    (if (and (< k 14) (not (eq? (car (dk-goal)) head)))
        (begin (di) (lp (+ k 1))))))

;;; =====================================================================
;;; L1.  product-carrier-unfold -- the functoid's defining equation, as a
;;; THEOREM.  `mac' unfolds the functoid in the goal; `qrfl' closes X == X.
;;; =====================================================================

(sp (make-wff '(FORALL ms (== (PRODUCT-CARRIER ms)
   (SEP x (FUN NN (BIG-UNION n NN (PTS (ms n))))
        (FORALL n (IMPLIES (IN n NN) (IN (x n) (PTS (ms n))))))))))
(di)
(mac 'PRODUCT-CARRIER)
(qrfl)
(qed 'product-carrier-unfold)
(topic! 'product-carrier-unfold 'constructions)
(alias! 'product-carrier-unfold "the product carrier, unfolded")

;;; =====================================================================
;;; L2.  product-carrier-coord -- a point of the product has its n-th
;;; coordinate in the n-th factor.  L1 through `mac-h', then `sep-me'.
;;; =====================================================================

(sp (make-wff '(FORALL ms (FORALL x_ (IMPLIES (IN x_ (PRODUCT-CARRIER ms))
   (FORALL n_ (IMPLIES (IN n_ NN) (IN (x_ n_) (PTS (ms n_))))))))))
(di)
(mac-h 'product-carrier-unfold '(IN x_ (PRODUCT-CARRIER ms)))
(sep-me (pm-find 'sepmem
          (lambda (a) (and (pair? a) (eq? (car a) 'IN)
                           (pair? (caddr a)) (eq? (car (caddr a)) 'SEP)))))
(inst+ '(FORALL n (IMPLIES (IN n NN) (IN (x_ n) (PTS (ms n))))) 'n_)
(ass)
(qed 'product-carrier-coord)
(topic! 'product-carrier-coord 'constructions)
(alias! 'product-carrier-coord
        "a point of a countable product has its coordinates in the factors")

;;; =====================================================================
;;; L3.  bdd-metric-weight-bound -- everything one weighted bounded distance
;;; owes:  w*rho is real, 0 <= w*rho, and w*rho <= w.
;;; =====================================================================

(define pm-rho '((DIST (BDD-METRIC s)) u_ v_))
(define pm-wt (list '* 'wn pm-rho))

(sp (make-wff "forall([s], is-metric-space(s) implies
  forall([u_ in pts(s), v_ in pts(s), wn in rr], 0 <= wn implies
    (wn * (dist(bdd-metric(s)))(u_, v_) in rr and
     (0 <= wn * (dist(bdd-metric(s)))(u_, v_) and
      wn * (dist(bdd-metric(s)))(u_, v_) <= wn))))"))
(pm-peel-to! 'AND)
(fact 'bdd-metric-is-metric-space 's)
(fact 'bdd-metric-carrier 's)
;; PTS(BDD-METRIC s) is in OPERATOR position under DIST, so the carrier
;; equation is used as a MACETE on the goal, never as a `subst'.
(have! '(IN u_ (PTS (BDD-METRIC s))) (lambda () (mac 'bdd-metric-carrier) (ass)))
(have! '(IN v_ (PTS (BDD-METRIC s))) (lambda () (mac 'bdd-metric-carrier) (ass)))
(fact 'metric-dist-real '(BDD-METRIC s) 'u_ 'v_)
(fact 'metric-pos '(BDD-METRIC s) 'u_ 'v_)
(fact 'bdd-metric-bounded 's 'u_ 'v_)
(pm-from-lt! pm-rho 1)
(fact 'rr-one-in)
(pm-and2! '(IN wn RR) (list 'IN pm-rho 'RR))
(fact 'rr-mul-closed 'wn pm-rho)
(fact 'rr-sub-in-rr 1 pm-rho)
(have! (list '<= 0 (list '- 1 pm-rho)) (lambda () (pm-ineq (list '<= pm-rho 1))))
(pm-and2! (list 'IN (list '- 1 pm-rho) 'RR) '(IN wn RR))
(pm-and2! (list '<= 0 (list '- 1 pm-rho)) '(<= 0 wn))
(fact 'rr-leq-mul-nonneg (list '- 1 pm-rho) 'wn)
(have! (list '<= 0 (list '- 'wn pm-wt))
  (lambda ()
    (pm-eq! (list '= (list '- 'wn pm-wt) (list '* (list '- 1 pm-rho) 'wn)))
    (ass)))
(pm-and2! '(<= 0 wn) (list '<= 0 pm-rho))
(fact 'rr-leq-mul-nonneg 'wn pm-rho)
(pm-and!
 (lambda ()
   (let ((g (dk-goal)))
     (cond ((eq? (car g) 'IN) (ass))
           ((equal? (cadr g) 0) (ass))
           (else (pm-ineq (list '<= 0 (list '- 'wn pm-wt))))))))
(qed 'bdd-metric-weight-bound)
(topic! 'bdd-metric-weight-bound 'analysis)
(alias! 'bdd-metric-weight-bound "a weighted bounded distance is between 0 and the weight")

;;; =====================================================================
;;; L3a.  product-metric-carrier -- the CARRIER slot, the same five-step move
;;; as L6 one slot over and two steps shorter (no lambda to beta-reduce).  It
;;; retires the second asserted support of structure-library/product-metric.scm,
;;; whose warrant read "read off the functoid carrier slot" -- the proof,
;;; written in prose and then not run.
;;; =====================================================================

(sp (make-wff '(FORALL ms (FORALL w (== (PTS (PRODUCT-METRIC-W ms w))
                                        (PRODUCT-CARRIER ms))))))
(di)
(mac 'PRODUCT-METRIC-W)
(slot 'PTS)
(nth-r)
(qrfl)
(qed 'product-metric-carrier)
(alias! 'product-metric-carrier "the carrier of the product metric")

;;; =====================================================================
;;; L4.  product-term-seq-in-fun -- the term sequence of D_w is a real
;;; sequence.  Cited by L5 (the comparison test wants it) and by L7 (so does
;;; series-limit-converges-to), so it is a theorem rather than a `have!'.
;;; =====================================================================

(define pm-lam '(VNB-LAMBDA n NN (* (w n) ((DIST (BDD-METRIC (ms n))) (x n) (y n)))))

;;; the hypotheses of every theorem below, peeled, with the two universals the
;;; per-index helper instantiates read off the context
(define pm-msu #f)
(define pm-wpos #f)
(define (pm-setup!)
  (pm-split-h! 'summable-weight '(SUMMABLE-WEIGHT w))
  (mac-h 'is-ms-sequence '(IS-MS-SEQUENCE ms))
  (set! pm-msu (pm-find 'msuniv
                 (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                                  (dk-contains? a 'IS-METRIC-SPACE)))))
  (set! pm-wpos (pm-find 'wpos
                  (lambda (a) (and (pair? a) (eq? (car a) 'FORALL) (dk-contains? a '<))))))

;;; everything the n-th term of the series needs, landed at the index n_
(define (pm-coord! n_)
  (inst+ pm-msu n_)
  (fact 'product-carrier-coord 'ms 'x n_)
  (fact 'product-carrier-coord 'ms 'y n_)
  (fact 'fun-apply-type-c 'w 'NN 'RR n_)
  (inst+ pm-wpos n_)
  (pm-from-lt! 0 (list 'w n_))
  (fact 'bdd-metric-weight-bound (list 'ms n_) (list 'x n_) (list 'y n_) (list 'w n_))
  (let* ((rho (list (list 'DIST (list 'BDD-METRIC (list 'ms n_))) (list 'x n_) (list 'y n_)))
         (t   (list '* (list 'w n_) rho)))
    (dk-split! (list 'AND (list 'IN t 'RR)
                     (list 'AND (list '<= 0 t) (list '<= t (list 'w n_)))))
    t))

(sp (make-wff '(FORALL ms (IMPLIES (IS-MS-SEQUENCE ms)
     (FORALL w (IMPLIES (SUMMABLE-WEIGHT w)
       (FORALL x (IMPLIES (IN x (PRODUCT-CARRIER ms))
         (FORALL y (IMPLIES (IN y (PRODUCT-CARRIER ms))
           (IN (VNB-LAMBDA n NN (* (w n) ((DIST (BDD-METRIC (ms n))) (x n) (y n))))
               (FUN NN RR))))))))))))
(pm-peel-to! 'IN)
(pm-setup!)
(dk-lam-t!)
(let ((n_ (cadr (pm-di-landed-1!))))
  (pm-coord! n_)
  (ass))
(qed 'product-term-seq-in-fun)
(topic! 'product-term-seq-in-fun 'constructions)
(alias! 'product-term-seq-in-fun
        "the term sequence of the product metric is a real sequence")

;;; =====================================================================
;;; L5.  product-weighted-summable -- THE THEOREM.  Statement VERBATIM from
;;; the support this file retires (structure-library/product-metric.scm).
;;; =====================================================================

(sp (make-wff '(FORALL ms (IMPLIES (IS-MS-SEQUENCE ms)
     (FORALL w (IMPLIES (SUMMABLE-WEIGHT w)
       (FORALL x (IMPLIES (IN x (PRODUCT-CARRIER ms))
         (FORALL y (IMPLIES (IN y (PRODUCT-CARRIER ms))
           (SERIES-CONVERGES
             (VNB-LAMBDA n NN (* (w n) ((DIST (BDD-METRIC (ms n))) (x n) (y n)))))))))))))))
(pm-peel-to! 'SERIES-CONVERGES)
;;; (a) the term sequence is a real sequence.  CITED BEFORE `pm-setup!': that
;;; helper unfolds IS-MS-SEQUENCE and SUMMABLE-WEIGHT with `mac-h', which
;;; REPLACES them, and they are this theorem's own antecedents.
(fact 'product-term-seq-in-fun 'ms 'w 'x 'y)
(pm-setup!)

;;; (b) termwise:  0 <= term(k) <= w(k)
(define pm-termwise
  (list 'FORALL 'k_ (list 'IMPLIES '(IN k_ NN)
    (list 'AND (list '<= 0 (list pm-lam 'k_))
               (list '<= (list pm-lam 'k_) (list 'w 'k_))))))
(have! pm-termwise
  (lambda ()
    (let ((n_ (cadr (pm-di-landed-1!))))
      (lam-b)
      (pm-coord! n_)
      (pm-and! (lambda () (ass))))))

;;; (c) the comparison test
(pm-and2! pm-termwise '(SERIES-CONVERGES w))
(fact 'comparison-test pm-lam 'w)
(ass)
(qed 'product-weighted-summable)
(topic! 'product-weighted-summable 'constructions)
(alias! 'product-weighted-summable
        "the series defining the weighted product metric converges")

;;; =====================================================================
;;; L6.  product-metric-distance -- the DISTANCE FORMULA of the product
;;; metric, which the tree had for BDD-METRIC (bdd-metric-distance, asserted)
;;; and for nothing else:
;;;
;;;   D_w(x,y)  ==  SERIES-LIMIT( n |-> w(n) * rho_n(x(n), y(n)) ).
;;;
;;; It is PROVEN, `modulo 0', in five steps, and the steps are the answer to
;;; "how does one read a slot of a functoid-built structure whose slot is a
;;; TUPLED lambda":
;;;
;;;   (mac 'SERIES-LIMIT)     turn the right-hand side back into its IOTA
;;;   (mac 'PRODUCT-METRIC-W) unfold the functoid to the literal [carrier, dist]
;;;   (slot 'DIST)            project -- this rewrites DIST to nth(2,.) at EVERY
;;;                           occurrence, the per-factor (DIST (BDD-METRIC ...))
;;;                           included, which is why the SECOND (slot 'DIST)
;;;                           below is needed rather than a mistake
;;;   (nth-r)                 reduce nth(2, [a,b]) to b
;;;   (lam-b)                 beta-reduce the TUPLED lambda at (x,y) -- it fires
;;;                           and owes NOTHING extra, because x and y are typed
;;;                           in PRODUCT-CARRIER(ms) above it
;;;   (slot 'DIST) (qrfl)     bring the two sides to the same normal form
;;;
;;; No hypothesis about ms or w is needed: this is the functoid's own equation.
;;; The two carrier hypotheses are what `lam-b' spends.
;;; =====================================================================

(sp (make-wff '(FORALL ms (FORALL w (FORALL x (IMPLIES (IN x (PRODUCT-CARRIER ms))
   (FORALL y (IMPLIES (IN y (PRODUCT-CARRIER ms))
     (== ((DIST (PRODUCT-METRIC-W ms w)) x y)
         (SERIES-LIMIT
           (VNB-LAMBDA n NN (* (w n) ((DIST (BDD-METRIC (ms n))) (x n) (y n))))))))))))))
(pm-peel-to! '==)
(mac 'SERIES-LIMIT)
(mac 'PRODUCT-METRIC-W)
(slot 'DIST)
(nth-r)
(lam-b)
(slot 'DIST)
(qrfl)
(qed 'product-metric-distance)
(topic! 'product-metric-distance 'constructions)
(alias! 'product-metric-distance
        "the product metric is the sum of the weighted coordinate distances")

;;; =====================================================================
;;; L7.  product-metric-dist-converges -- and the series actually converges TO
;;; that distance.  L5 (the series converges) plus `series-limit-converges-to'
;;; (dominated-convergence.scm, which is where the IOTA's uniqueness half was
;;; discharged) plus L6.  This is the form a convergence argument in the
;;; product metric consumes: it turns D_w(x,y) from a description into the
;;; limit of a named sequence of partial sums.
;;; =====================================================================

(sp (make-wff '(FORALL ms (IMPLIES (IS-MS-SEQUENCE ms)
     (FORALL w (IMPLIES (SUMMABLE-WEIGHT w)
       (FORALL x (IMPLIES (IN x (PRODUCT-CARRIER ms))
         (FORALL y (IMPLIES (IN y (PRODUCT-CARRIER ms))
           (SERIES-CONVERGES-TO
             (VNB-LAMBDA n NN (* (w n) ((DIST (BDD-METRIC (ms n))) (x n) (y n))))
             ((DIST (PRODUCT-METRIC-W ms w)) x y))))))))))))
(pm-peel-to! 'SERIES-CONVERGES-TO)
(fact 'product-term-seq-in-fun 'ms 'w 'x 'y)
(fact 'product-weighted-summable 'ms 'w 'x 'y)
(fact 'series-limit-converges-to pm-lam)
(fact 'product-metric-distance 'ms 'w 'x 'y)
(mac 'product-metric-distance)
(ass)
(qed 'product-metric-dist-converges)
(topic! 'product-metric-dist-converges 'constructions)
(alias! 'product-metric-dist-converges
        "the coordinate series converges to the product distance")
