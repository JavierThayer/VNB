;;; rake-metric-constructions.scm -- BATCH S of the 2026-09-18 rake: the metric
;;; CONSTRUCTIONS (bounded metric, ball cover, countable product).  Every
;;; statement below is its support's statement UNCHANGED, copied from the
;;; support site, except where the header says otherwise.
;;;
;;; PROVEN here, all `modulo 0':
;;;   bdd-metric-id-bicontinuous   structure-library/bounded-metric.scm:52
;;;   ball-cover-is-open-cover     structure-library/compactness.scm:120
;;;   product-projection-continuous structure-library/product-metric.scm:83
;;;
;;; AND THREE STATEMENTS THAT CANNOT BE PROVEN AS WRITTEN, for a mechanical
;;; reason that is a DEFECT IN `def-functoid', not in the mathematics:
;;;   rr-bounded-ms-is-metric-space  bounded-metric.scm:96
;;;   rr-bounded-ms-bounded          bounded-metric.scm:103
;;;   rr-bounded-equivalent          bounded-metric.scm:113
;;;
;;; `RR-BOUNDED-MS' is declared (bounded-metric.scm:94)
;;;
;;;     (def-functoid 'RR-BOUNDED-MS '() '(BDD-METRIC RR-MS))
;;;
;;; -- the ONLY nullary def-functoid in the tree.  `def-functoid'
;;; (structures.scm:942) computes its pattern variables as
;;;
;;;     (if (pair? params) params (list params))
;;;
;;; which is there to accept a BARE SYMBOL parameter; `'()' is not a pair, so
;;; the nullary case is wrapped and the pattern variable list becomes `(())'.
;;; The installed macete therefore has left-hand side `(RR-BOUNDED-MS ())' --
;;; a UNARY application to the empty list -- while the three supports above
;;; write the bare constant `RR-BOUNDED-MS'.  The two never match:
;;; `(mac 'RR-BOUNDED-MS)' answers `macete not applicable', and a sweep of
;;; *theorem-table* finds exactly three formulas mentioning `rr-bounded-ms' --
;;; the three supports themselves.  So RR-BOUNDED-MS is an UNINTERPRETED
;;; CONSTANT: nothing in the theory relates it to BDD-METRIC(RR-MS).
;;;
;;; The three statements are then UNDERDETERMINED, not false-by-content:
;;; interpret the constant as EMPTY-SET (nothing constrains it) and
;;; `IS-METRIC-SPACE(RR-BOUNDED-MS)' fails, because a metric space is a
;;; 2-tuple.  What the supports MEAN is proven below at the term they meant:
;;;
;;;   bdd-rr-ms-is-metric-space   IS-METRIC-SPACE(BDD-METRIC(RR-MS))
;;;   bdd-rr-ms-bounded           every BDD-METRIC(RR-MS) distance is < 1
;;;   bdd-rr-equivalent           the identity RR-MS <-> BDD-METRIC(RR-MS)
;;;                               is bicontinuous
;;;
;;; Each is one citation from the original once `def-functoid' is repaired
;;; (one line: treat `'()' as a parameter list, and emit the BARE SYMBOL, not
;;; a nullary application, as the macete's left-hand side -- a nullary
;;; application is itself rejected by `validate-wff!' since 2026-08-15).
;;;
;;; NOT ATTEMPTED, with the route written down:
;;;   cauchy-rapid-subsequence   structure-library/metric-completeness.scm:123
;;;     CHAINS TO the asserted `dc-on-nn-pred' (theorem-library/dc-on-nn.scm:83,
;;;     `reference').  Route: X := NN; P(k,m) := "forall p,q in NN with m <= p
;;;     and m <= q, d(f p, f q) <= rad k" (IS-CAUCHY-SEQ at eps := rad k gives
;;;     an m with P(k,m), and P is upward closed in m); a := any m with P(0,m);
;;;     nxt(k,u) := SEP m NN (AND (< u m) P(succ k, m)) -- inhabited because
;;;     the threshold for rad(succ k) may be raised past succ u.  dc-on-nn-pred
;;;     returns phi in FUN(NN,NN) with phi 0 = a and phi(succ k) in nxt(k, phi k),
;;;     i.e. phi k < phi(succ k) and P(succ k, phi(succ k)); an NN induction on
;;;     the invariant gives P(k, phi k) for every k, and P(k, phi k) read at
;;;     (phi k, phi (succ k)) -- both at least phi k -- is the conclusion.
;;;     Strict monotonicity from phi k < phi (succ k) is the usual
;;;     consecutive-step induction; the ready-made form
;;;     `nn-step-strictly-mono' (theorem-library/diagonalization-lemmas.scm:28)
;;;     is ITSELF asserted `well-known' AND concludes STRICTLY-MONO-NN rather
;;;     than the support's spelled-out universal, so a hand induction is the
;;;     honest route there.  Not chained here: the brief forbids chaining to
;;;     another asserted leaf, and `dc-on-nn-pred' is one.
;;;   completion-is-metric-space  structure-library/metric-completion.scm:107
;;;   completion-is-complete      structure-library/metric-completion.scm:120
;;;     Batch O's report (theorem-library/rake-setoid2.scm, "THE TWO LEFT")
;;;     names the one missing brick for the first: DIST-SEQ(M,f,g) is a CAUCHY
;;;     real sequence for any two Cauchy f, g -- `rko2-quad' plus the two
;;;     Cauchy thresholds -- followed by `rr-cauchy-converges'.  That brick
;;;     plus the four limit laws is a 400+ line file of its own and is past
;;;     this batch's "do not slog" line; the second waits on the first.
;;;
;;; ---------------------------------------------------------------------
;;; MECHANICS WORTH KEEPING.
;;;
;;; * THE TWO DELTAS.  Forward (d -> rho) delta := eps, because rho <= d
;;;   (`bdd-metric-dist-le'); backward (rho -> d) delta := eps/(1+eps), because
;;;   rho <= f(eps) forces d <= eps (`bdd-metric-dist-reflect').  Both bricks
;;;   are PROVEN in theorem-library/bdd-metric-convergence.scm, which is why
;;;   this file needs no eps/delta analysis of its own.  POS-RR(eps/(1+eps))
;;;   is NOT read off `bdd-fn-nonneg' -- that gives `0 <=' only.  It is
;;;   `rr-mul-pos' on eps and recip(1+eps), transported across
;;;   `binary-divide-def' (named-only, so cited by name) and finished by
;;;   `rr-pos-rr-of-lt'.
;;;
;;; * PTS(BDD-METRIC s) IS REWRITTEN AWAY WITH `mac bdd-metric-carrier' AFTER
;;;   EVERY PREDICATE UNFOLD, not once at the top: `mac is-continuous' and
;;;   `mac is-continuous-at' each MINT fresh occurrences of it.
;;;
;;; * INSTANTIATING AT THE FREE VARIABLE `n' RENAMES A BOUND `n', AND THE
;;;   ALPHA-VARIANT IS A DIFFERENT ATOM TO `ineq'.  The product family is
;;;   `(VNB-LAMBDA n NN (* (w n) ((DIST (BDD-METRIC (ms n))) (x n) (y n))))'
;;;   -- binder `n' -- and `product-projection-continuous' quantifies a FREE
;;;   `n'.  `(fact 'series-term-le-sum fam L n)' substitutes n for the
;;;   theorem's index, capture-avoidance renames the family's own `n' to
;;;   `n_8013', and the SERIES-LIMIT term it lands is alpha-equivalent to --
;;;   but not `equal?' to -- the one `product-metric-distance' put in the
;;;   context.  `ineq' then has two unrelated atoms and cannot chain.  The cure
;;;   is NOT to cut the wanted spelling afterwards: `context-add-assumption' is
;;;   alpha-idempotent, so that cut is a self-loop with no main branch
;;;   (CLAUDE.md).  Run the CITATION INSIDE the `have!' lane instead -- cut the
;;;   claim in the spelling the context already uses and let `ass', which is
;;;   alpha-aware, absorb the difference on the side branch.  The alpha-variant
;;;   never reaches the main context.
;;;
;;; * A `have!' CALLED ONCE PER LEAF RE-CLAIMS WHAT IS ALREADY THERE.
;;;   `r5s-have!' declines when the claim is in context, for the same
;;;   self-loop reason (bdd-metric-basics.scm's `bmb-have!' is the precedent).
;;;
;;; * `class-extensionality' (unconditional, no sethood premise) is how the
;;;   BIG-UNION of the ball cover is shown equal to PTS(s); the goal is an
;;;   `==', so the `=' it delivers is `subst'-ed in and closed by `qrfl'.
;;;
;;; WINDOW.  [417, end).  lo is forced by theorem-library/bdd-metric-convergence
;;; (position 416: bdd-metric-dist-le, bdd-metric-dist-reflect).  The next
;;; latest citations are theorem-library/product-is-metric-space (413:
;;; product-is-metric-space), theorem-library/product-summable (412:
;;; product-metric-distance, product-metric-carrier, product-carrier-coord,
;;; product-term-seq-in-fun, product-weighted-summable, bdd-metric-weight-bound),
;;; theorem-library/mono-le-limit (405: series-term-le-sum),
;;; theorem-library/dominated-convergence (401: series-limit-converges-to,
;;; series-limit-in-rr), theorem-library/ball-is-open (288: ball-is-open),
;;; theorem-library/rr-metric-space-proof (281: rr-is-metric-space),
;;; theorem-library/bdd-metric-basics (275: bdd-metric-is-metric-space,
;;; bdd-metric-bounded), theorem-library/rake-balls (270: ball-center-in,
;;; ball-membership), theorem-library/ball-cover-lemmas (260:
;;; ball-cover-unfold, ball-cover-mem-fwd), theorem-library/rr-recip-order
;;; (182: rr-mul-pos, rr-recip-pos), theorem-library/pos-rr-of-lt (183:
;;; rr-pos-rr-of-lt) and theorem-library/op-typing (200: metric-dist-real).
;;; No proven theorem cites any of these six leaves, so nothing forces hi.
;;;
;;; Helper prefix: r5s-.

(define (r5s-idx form)
  (let loop ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "r5s-idx: not in context" form))
          ((equal? (car l) form) i)
          (#t (loop (cdr l) (+ i 1))))))
(define (r5s-ineq . forms) (apply ineq (map r5s-idx forms)))
(define (r5s-di-landed!)
  (let loop ((n 0))
    (let ((new (dk-landed* (lambda () (di)))))
      (cond ((pair? new) new)
            ((> n 5) (error "r5s-di-landed!: nothing landed"))
            (#t (loop (+ n 1)))))))
(define (r5s-has-lambda-app? g)
  (cond ((and (pair? g) (pair? (car g)) (eq? (caar g) 'VNB-LAMBDA)) #t)
        ((pair? g) (or (r5s-has-lambda-app? (car g)) (r5s-has-lambda-app? (cdr g))))
        (#t #f)))
(define (r5s-beta!)
  (let loop ((fuel 20))
    (if (and (> fuel 0) (r5s-has-lambda-app? (dk-goal)))
        (let ((before (dk-goal)))
          (lam-b)
          (if (equal? (dk-goal) before) #t (loop (- fuel 1))))
        #t)))
(define (r5s-and! closer)
  (let ((g (dk-goal)))
    (if (and (pair? g) (eq? (car g) 'AND))
        (for-each (lambda (k) (dk-focus! k) (r5s-and! closer))
                  (dk-opened (lambda () (di))))
        (closer))))
(define r5s-id '(VNB-LAMBDA x (PTS s) x))
(define r5s-bd '(BDD-METRIC s))
(define (r5s-pts-set!)
  (mac-h 'IS-METRIC-SPACE '(IS-METRIC-SPACE s))
  (dk-split-all!)
  (ass))

;; `have!' that declines when the claim is ALREADY in context (the cut would be
;; an alpha self-loop with no main branch).
(define (r5s-have! f . opt)
  (if (find-first (lambda (g) (equal? g f)) (dk-asms))
      f
      (if (pair? opt) (have! f (car opt)) (have! f))))

;;; ---------------- kit (file-local) ----------------
(define (r5s-inner-point!)
  (let* ((landed (r5s-di-landed!))
         (mem (find-first (lambda (f) (and (pair? f) (eq? (car f) 'IN))) landed)))
    (if (not (find-first (lambda (f) (and (pair? f) (eq? (car f) '<=))) landed))
        (r5s-di-landed!))
    (if (not mem) (error "r5s-inner-point!: no membership landed") (cadr mem))))

(define (r5s-recip-of e) (list 'recip (list '+ 1 e)))
(define (r5s-div-of e)   (list '/ e (list '+ 1 e)))

(define (r5s-delta! eps)
  (let* ((den (list '+ 1 eps)) (rp (r5s-recip-of eps)) (dl (r5s-div-of eps)))
    (fact 'rr-pos-rr-in-rr eps)
    (fact 'rr-lt-of-pos-rr eps)
    (fact 'rr-zero-in) (fact 'rr-one-in)
    (r5s-have! (list '<= 0 eps) (lambda () (r5s-ineq (list '< 0 eps))))
    (r5s-have! (list 'AND '(IN 1 RR) (list 'IN eps 'RR)))
    (fact 'rr-add-closed 1 eps)
    (r5s-have! (list '< 0 den) (lambda () (r5s-ineq (list '< 0 eps))))
    (fact 'rr-pos-ne-zero den)
    (r5s-have! (list 'AND (list 'IN den 'RR) (list 'NOT (list '= den 0))))
    (fact 'rr-recip-closed den)
    (fact 'rr-recip-pos den)
    (r5s-have! (list 'AND (list 'IN eps 'RR) (list 'IN rp 'RR)))
    (fact 'rr-mul-closed eps rp)
    (r5s-have! (list 'AND (list '< 0 eps) (list '< 0 rp)))
    (fact 'rr-mul-pos eps rp)
    (r5s-have! (list 'IN dl 'RR) (lambda () (mac 'binary-divide-def) (ass)))
    (r5s-have! (list '< 0 dl) (lambda () (mac 'binary-divide-def) (ass)))
    (r5s-have! (list 'POS-RR dl) (lambda () (fact 'rr-pos-rr-of-lt dl) (ass)))
    dl))

;; rho(a,b) <= d(a,b) <= eps
(define (r5s-fwd-close! a b eps)
  (let ((d  (list (list 'DIST 's) a b))
        (rh (list (list 'DIST r5s-bd) a b)))
    (fact 'rr-pos-rr-in-rr eps)
    (fact 'metric-dist-real 's a b)
    (r5s-have! (list 'IN a (list 'PTS r5s-bd)) (lambda () (mac 'bdd-metric-carrier) (ass)))
    (r5s-have! (list 'IN b (list 'PTS r5s-bd)) (lambda () (mac 'bdd-metric-carrier) (ass)))
    (fact 'metric-dist-real r5s-bd a b)
    (fact 'bdd-metric-dist-le 's a b)
    (r5s-ineq (list '<= rh d) (list '<= d eps))))

;; one IS-CONTINUOUS leaf; FWD? says which way the identity runs.
(define (r5s-cont-leaf! fwd?)
  (mac 'is-continuous)
  (mac 'bdd-metric-carrier)
  (r5s-and!
   (lambda ()
     (let ((g (dk-goal)))
       (if (eq? (car g) 'FORALL)
           (let ((a (cadr (car (r5s-di-landed!)))))
             (mac 'is-continuous-at)
             (mac 'bdd-metric-carrier)
             (r5s-and!
              (lambda ()
                (let ((h (dk-goal)))
                  (if (eq? (car h) 'FORALL)
                      (let* ((eps (cadr (car (r5s-di-landed!))))
                             (dl  (if fwd? eps (r5s-delta! eps))))
                        (ew dl)
                        (r5s-and!
                         (lambda ()
                           (let ((k (dk-goal)))
                             (if (eq? (car k) 'FORALL)
                                 (let ((b (r5s-inner-point!)))
                                   (r5s-beta!)
                                   (if fwd?
                                       (r5s-fwd-close! a b eps)
                                       (begin (fact 'bdd-metric-dist-reflect 's a b eps)
                                              (ass))))
                                 (ass))))))
                      (ass))))))
           (ass))))))

;;; ---------------- L1.  bdd-metric-id-bicontinuous ----------------
(sp (make-wff
  '(FORALL s (IMPLIES (IS-METRIC-SPACE s)
     (AND (IS-CONTINUOUS s (BDD-METRIC s) (VNB-LAMBDA x (PTS s) x))
          (IS-CONTINUOUS (BDD-METRIC s) s (VNB-LAMBDA x (PTS (BDD-METRIC s)) x)))))))
(dk-peel!)
(fact 'bdd-metric-is-metric-space 's)
(r5s-have! '(IN (PTS s) SET) (lambda () (r5s-pts-set!)))
(r5s-have! (list 'IN r5s-id '(FUN (PTS s) (PTS s)))
  (lambda ()
    (for-each (lambda (leaf)
                (dk-focus! leaf)
                (if (eq? (car (dk-goal)) 'FORALL)
                    (begin (r5s-di-landed!) (ass))
                    (ass)))
              (dk-opened (lambda () (lam-t))))))
(mac 'bdd-metric-carrier)
(for-each (lambda (n)
            (dk-focus! n)
            (r5s-cont-leaf! (eq? (cadr (dk-goal)) 's)))
          (dk-opened (lambda () (di))))
(qed 'bdd-metric-id-bicontinuous)
(gloss! 'bdd-metric-id-bicontinuous
  "The identity map between (X,d) and (X, d/(1+d)) is continuous in both
   directions, so the two metrics give the same topology.")
(topic! 'bdd-metric-id-bicontinuous 'topology)

;;; L2 -- IS-METRIC-SPACE(BDD-METRIC(RR-MS))
(sp (make-wff '(IS-METRIC-SPACE (BDD-METRIC RR-MS))))
(fact 'rr-is-metric-space)
(fact 'bdd-metric-is-metric-space 'RR-MS)
(ass)
(qed 'bdd-rr-ms-is-metric-space)
(topic! 'bdd-rr-ms-is-metric-space 'constructions)

;;; L3 -- every BDD-METRIC(RR-MS) distance is < 1
(sp (make-wff '(FORALL x (IMPLIES (IN x RR)
     (FORALL y (IMPLIES (IN y RR)
       (< ((DIST (BDD-METRIC RR-MS)) x y) 1)))))))
(dk-peel!)
(fact 'rr-is-metric-space)
(have! '(IN x (PTS RR-MS)) (lambda () (slot 'PTS) (ass)))
(have! '(IN y (PTS RR-MS)) (lambda () (slot 'PTS) (ass)))
(fact 'bdd-metric-bounded 'RR-MS 'x 'y)
(ass)
(qed 'bdd-rr-ms-bounded)
(topic! 'bdd-rr-ms-bounded 'constructions)

;;; L4 -- the identity RR-MS <-> BDD-METRIC(RR-MS) is bicontinuous
(sp (make-wff '(AND (IS-CONTINUOUS RR-MS (BDD-METRIC RR-MS) (VNB-LAMBDA x RR x))
                    (IS-CONTINUOUS (BDD-METRIC RR-MS) RR-MS
                                   (VNB-LAMBDA x RR x)))))
(fact 'rr-is-metric-space)
(have! '(== RR (PTS RR-MS)) (lambda () (slot 'PTS) (qrfl)))
(subst '(== RR (PTS RR-MS)))
(let ((inst (dk-fact! 'bdd-metric-id-bicontinuous 'RR-MS)))
  (mac-h 'bdd-metric-carrier inst))
(ass)
(qed 'bdd-rr-equivalent)
(gloss! 'bdd-rr-equivalent
  "RR carries a BOUNDED metric topologically equivalent to the usual one: the
   identity RR-MS <-> BDD-METRIC(RR-MS) is bicontinuous.")
(topic! 'bdd-rr-equivalent 'constructions)

(define r5s-bcov '(BALL-COVER s r))
(define r5s-bu (list 'BIG-UNION 'U r5s-bcov 'U))
;; a member of the r-ball cover is open
(define (r5s-cover-open!)
  (let* ((uu (cadr (car (r5s-di-landed!))))            ; (IN U (BALL-COVER s r))
         (ex (dk-fact! 'ball-cover-mem-fwd 's 'r uu))
         (c  (dk-skolem! ex))
         (eq (list '= (list 'BALL 's c 'r) uu)))
    (fact 'ball-is-open 's c 'r)
    (r5s-have! (list '= uu (list 'BALL 's c 'r))
           (lambda () (subst eq) (rfl)))
    (subst (list '= uu (list 'BALL 's c 'r)))
    (ass)))

(define (r5s-cover-fwd! xv)
  (let* ((landed (dk-landed (lambda () (bu-me (list 'IN xv r5s-bu)))))
         (idx (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                        (equal? (caddr f) r5s-bcov)
                                        (member f landed)))
                       "the landed cover membership"))
         (w   (cadr idx))
         (ex  (dk-fact! 'ball-cover-mem-fwd 's 'r w))
         (c   (dk-skolem! ex))
         (bl  (list 'BALL 's c 'r)))
    (r5s-have! (list 'IN xv bl) (lambda () (subst (list '= bl w)) (ass)))
    (fact 'ball-membership 's c 'r xv)
    (dk-only! (list 'IFF (list 'IN xv bl)
                    (list 'AND (list 'IN xv '(PTS s))
                          (list 'AND (list '<= (list (list 'DIST 's) c xv) 'r)
                                (list 'NOT (list '= (list (list 'DIST 's) c xv) 'r)))))
              (list 'IN xv bl))
    (prop)))

(define (r5s-cover-bwd! xv)
  (let ((bl (list 'BALL 's xv 'r)))
    (for-each
     (lambda (n)
       (dk-focus! n)
       (let ((g (dk-goal)))
         (if (equal? (caddr g) r5s-bcov)
             (begin
               (mac 'ball-cover-unfold)
               (dk-image-goal!)
               (ew xv)
               (r5s-and!
                (lambda ()
                  (let ((h (dk-goal)))
                    (if (eq? (car h) '=) (begin (lam-b) (rfl)) (ass))))))
             (begin (fact 'ball-center-in 's xv 'r) (ass)))))
     (dk-opened (lambda () (bu-mi bl))))))

(define (r5s-cover-eq!)
  (r5s-have! (list 'FORALL 'x_ (list 'IFF (list 'IN 'x_ r5s-bu) (list 'IN 'x_ '(PTS s))))
    (lambda ()
      (di)
      (let ((ls (dk-opened (lambda () (di)))))
        (dk-focus! (any-pred (lambda (n) (equal? (caddr (dk-goal-of n)) '(pts s))) ls))
        (r5s-cover-fwd! 'x_)
        (dk-focus! (any-pred (lambda (n) (not (equal? (caddr (dk-goal-of n)) '(pts s)))) ls))
        (r5s-cover-bwd! 'x_))))
  (fact 'class-extensionality r5s-bu '(PTS s))
  (subst (list '= r5s-bu '(PTS s)))
  (qrfl))

(sp (make-wff '(FORALL s (IMPLIES (IS-METRIC-SPACE s)
     (FORALL r (IMPLIES (AND (IN r RR) (AND (<= 0 r) (NOT (= 0 r))))
       (IS-OPEN-COVER s (BALL-COVER s r))))))))
(dk-peel!)
(mac 'is-open-cover)
(r5s-and!
 (lambda ()
   (let ((g (dk-goal)))
     (cond ((eq? (car g) 'IS-METRIC-SPACE) (ass))
           ((eq? (car g) 'FORALL) (r5s-cover-open!))
           (#t (r5s-cover-eq!))))))

(qed 'ball-cover-is-open-cover)
(gloss! 'ball-cover-is-open-cover
  "For r > 0 the family of all r-balls of a metric space is an open cover: each
   ball is open, and every point lies in its own ball.")
(topic! 'ball-cover-is-open-cover 'topology)

;;; ---------------- kit (file-local) ----------------
(define (r5s-pp-and! closer)
  (let ((g (dk-goal)))
    (if (and (pair? g) (eq? (car g) 'AND))
        (for-each (lambda (k) (dk-focus! k) (r5s-pp-and! closer))
                  (dk-opened (lambda () (di))))
        (closer))))

(define (r5s-nn-set-goal?) (equal? (dk-goal) '(IN NN SET)))

;; (IN (PTS (ms k)) SET) off the folded IS-MS-SEQUENCE(ms)
(define (r5s-pts-set-ms! k)
  (mac-h 'is-ms-sequence '(IS-MS-SEQUENCE ms))
  (let ((u (dk-pick (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                                     (dk-contains? a 'IS-METRIC-SPACE)))
                    "the ms universal")))
    (inst+ u k))
  (mac-h 'IS-METRIC-SPACE (list 'IS-METRIC-SPACE (list 'ms k)))
  (dk-split-all!)
  (ass))

;; focus goal is (IN (PRODUCT-CARRIER ms) SET)
(define (r5s-carrier-set!)
  (mac 'PRODUCT-CARRIER)
  (sep-set)
  (mac 'fun-set-iff)
  (r5s-pp-and!
   (lambda ()
     (if (r5s-nn-set-goal?)
         (begin (fact 'nn-is-set) (ass))
         (begin
           (bu-set)
           (r5s-pp-and!
            (lambda ()
              (if (r5s-nn-set-goal?)
                  (begin (fact 'nn-is-set) (ass))
                  (r5s-pts-set-ms! (cadr (dk-landed-1 (lambda () (di)))))))))))))

(define (r5s-ms-n! k)
  (r5s-have! (list 'IS-METRIC-SPACE (list 'ms k))
    (lambda ()
      (mac-h 'is-ms-sequence '(IS-MS-SEQUENCE ms))
      (let ((u (dk-pick (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                                         (dk-contains? a 'IS-METRIC-SPACE)))
                        "the ms universal")))
        (inst+ u k))
      (ass))))


;; (IN (w k) RR) and (< 0 (w k))
(define (r5s-wpos! k)
  (fact 'fun-apply-type-c 'w 'NN 'RR k)
  (r5s-have! (list '< 0 (list 'w k))
    (lambda ()
      (mac-h 'summable-weight '(SUMMABLE-WEIGHT w))
      (dk-split-all!)
      (let ((u (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                         (dk-contains? f 'w)))
                        "the weight positivity universal")))
        (inst+ u k))
      (ass)))
  (r5s-have! (list '<= 0 (list 'w k)) (lambda () (r5s-ineq (list '< 0 (list 'w k))))))

;; rho_k(a,b) in RR, at the BOUNDED metric of the k-th factor
(define (r5s-rho-real! ab bb k)
  (let ((mk (list 'ms k)))
    (fact 'bdd-metric-is-metric-space mk)
    (r5s-have! (list 'IN (list ab k) (list 'PTS (list 'BDD-METRIC mk)))
           (lambda () (mac 'bdd-metric-carrier) (ass)))
    (r5s-have! (list 'IN (list bb k) (list 'PTS (list 'BDD-METRIC mk)))
           (lambda () (mac 'bdd-metric-carrier) (ass)))
    (fact 'metric-dist-real (list 'BDD-METRIC mk) (list ab k) (list bb k))))

;; goal  X <= Y  with (IN X RR) (IN Y RR) (IN C RR) (< 0 C) (<= (* C X) (* C Y))
(define (r5s-cancel! x y c)
  (let ((d (list '- y x)))
    (r5s-have! (list 'AND (list 'IN y 'RR) (list 'IN x 'RR)))
    (fact 'rr-sub-in-rr y x)
    (r5s-have! (list 'AND (list 'IN c 'RR) (list 'IN d 'RR)))
    (fact 'rr-mul-closed c d)
    (r5s-have! (list '= (list '* c d) (list '- (list '* c y) (list '* c x)))
           (lambda () (crs)))
    (r5s-have! (list '<= 0 (list '* c d))
      (lambda () (r5s-ineq (list '<= (list '* c x) (list '* c y))
                           (list '= (list '* c d)
                                 (list '- (list '* c y) (list '* c x))))))
    (fact 'rr-nonneg-cancel-pos c d)
    (r5s-ineq (list '<= 0 d))))

(define (r5s-pp-close! a b eps)
  (let* ((fe  (r5s-div-of eps))
         (wn  '(w n))
         (dl  (list '* wn fe))
         (dd  (list (list 'DIST '(PRODUCT-METRIC-W ms w)) a b))
         (rho (list (list 'DIST '(BDD-METRIC (ms n))) (list a 'n) (list b 'n)))
         (deq (dk-fact! 'product-metric-distance 'ms 'w a b))
         (sl  (caddr deq))
         (lam (cadr sl))
         (wrho (list '* wn rho)))
    ;; the term family is a real sequence and its series converges
    (fact 'product-term-seq-in-fun 'ms 'w a b)
    (fact 'product-weighted-summable 'ms 'w a b)
    (fact 'series-limit-converges-to lam)
    (fact 'series-limit-in-rr lam)
    ;; termwise nonnegativity
    (r5s-have! (list 'FORALL 'k_ (list 'IMPLIES '(IN k_ NN) (list '<= 0 (list lam 'k_))))
      (lambda ()
        (let ((kk (cadr (car (r5s-di-landed!)))))
          (lam-b)
          (r5s-ms-n! kk)
          (fact 'product-carrier-coord 'ms a kk)
          (fact 'product-carrier-coord 'ms b kk)
          (r5s-wpos! kk)
          (dk-split! (dk-deepest
            (lambda () (fact 'bdd-metric-weight-bound (list 'ms kk)
                             (list a kk) (list b kk) (list 'w kk)))))
          (ass))))
    ;; ONE TERM IS AT MOST THE SUM.  The citation runs INSIDE the `have!' lane:
    ;; instantiating the index at the free variable `n' forces capture-avoidance
    ;; to rename the family's own bound `n', and the alpha-variant of
    ;; SERIES-LIMIT(fam) it lands is a different ATOM to `ineq'.  Cut the claim
    ;; in the spelling the rest of the context uses and let `ass' -- which IS
    ;; alpha-aware -- absorb the difference on the side branch.
    (r5s-have! (list '<= wrho sl)
      (lambda ()
        (let ((le (dk-fact! 'series-term-le-sum lam sl 'n)))
          (lam-b-h le))
        (ass)))
    ;; and the sum is the product distance, which is at most delta
    (mac-h 'product-metric-distance (list '<= dd dl))
    ;; typings for the oracle
    (r5s-wpos! 'n)
    (fact 'product-carrier-coord 'ms a 'n)
    (fact 'product-carrier-coord 'ms b 'n)
    (r5s-rho-real! a b 'n)
    (r5s-have! (list 'AND (list 'IN wn 'RR) (list 'IN rho 'RR)))
    (fact 'rr-mul-closed wn rho)
    ;; w(n)*rho <= w(n)*fe
    (r5s-have! (list '<= wrho dl)
      (lambda () (r5s-ineq (list '<= wrho sl) (list '<= sl dl))))
    (r5s-have! (list '<= rho fe) (lambda () (r5s-cancel! rho fe wn)))
    (fact 'bdd-metric-dist-reflect (list 'ms 'n) (list a 'n) (list b 'n) eps)
    (ass)))

(sp (make-wff '(FORALL ms (IMPLIES (IS-MS-SEQUENCE ms)
     (FORALL w (IMPLIES (SUMMABLE-WEIGHT w)
       (FORALL n (IMPLIES (IN n NN)
         (IS-CONTINUOUS (PRODUCT-METRIC-W ms w) (ms n) (PRODUCT-PROJ ms n))))))))))
(dk-peel!)
(fact 'product-is-metric-space 'ms 'w)
(r5s-have! '(IN w (FUN NN RR))
  (lambda () (mac-h 'summable-weight '(SUMMABLE-WEIGHT w)) (dk-split-all!) (ass)))
(r5s-have! '(< 0 (w n))
  (lambda ()
    (mac-h 'summable-weight '(SUMMABLE-WEIGHT w))
    (dk-split-all!)
    (let ((u (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                       (dk-contains? f 'w)))
                      "the weight positivity universal")))
      (inst+ u 'n))
    (ass)))
(fact 'fun-apply-type-c 'w 'NN 'RR 'n)
(r5s-ms-n! 'n)
(r5s-have! '(IN (PRODUCT-CARRIER ms) SET) (lambda () (r5s-carrier-set!)))
(r5s-have! (list 'IN '(PRODUCT-PROJ ms n) (list 'FUN '(PRODUCT-CARRIER ms) '(PTS (ms n))))
  (lambda ()
    (mac 'PRODUCT-PROJ)
    (for-each
     (lambda (k)
       (dk-focus! k)
       (let ((g (dk-goal)))
         (if (and (eq? (car g) 'IN) (eq? (caddr g) 'SET))
             (ass)
             (let ((xv (cadr (car (r5s-di-landed!)))))
               (fact 'product-carrier-coord 'ms xv 'n)
               (ass)))))
     (dk-opened (lambda () (lam-t))))))
(mac 'is-continuous)
(mac 'product-metric-carrier)
(r5s-and!
 (lambda ()
   (let ((g (dk-goal)))
     (if (eq? (car g) 'FORALL)
         (let ((a (cadr (car (r5s-di-landed!)))))
           (mac 'is-continuous-at)
           (mac 'product-metric-carrier)
           (r5s-and!
            (lambda ()
              (let ((h (dk-goal)))
                (if (eq? (car h) 'FORALL)
                    (let* ((eps (cadr (car (r5s-di-landed!))))
                           (fe  (r5s-div-of eps))
                           (wn  '(w n))
                           (dl  (list '* wn fe)))
                      (r5s-delta! eps)
                      (r5s-have! (list 'AND (list '< 0 wn) (list '< 0 fe)))
                      (fact 'rr-mul-pos wn fe)
                      (r5s-have! (list 'AND (list 'IN wn 'RR) (list 'IN fe 'RR)))
                      (fact 'rr-mul-closed wn fe)
                      (r5s-have! (list 'POS-RR dl)
                             (lambda () (fact 'rr-pos-rr-of-lt dl) (ass)))
                      (ew dl)
                      (r5s-and!
                       (lambda ()
                         (let ((k (dk-goal)))
                           (if (eq? (car k) 'FORALL)
                               (let ((b (r5s-inner-point!)))
                                 (mac 'PRODUCT-PROJ)
                                 (r5s-beta!)
                                 (r5s-pp-close! a b eps))
                               (ass))))))
                    (ass))))))
         (ass)))))
(qed 'product-projection-continuous)
(gloss! 'product-projection-continuous
  "Each coordinate projection of the countable product metric is continuous:
   w(n)*rho_n(x(n),y(n)) is one term of the series that defines D_w, hence at
   most D_w(x,y), and rho_n small forces d_n small.")
(topic! 'product-projection-continuous 'topology)
