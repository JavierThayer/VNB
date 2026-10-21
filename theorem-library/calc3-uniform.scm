;;; calc3-uniform.scm -- calculus.pdf Prop 3.22 and Cor 3.23: UNIFORM CONTINUITY
;;; OFF A COMPACT SET.  Agent CALC-3, 2026-10-19.
;;;
;;;   continuous-uniform-near-compact            (the step inside the notes' proof)
;;;     f continuous from s to t, K subset pts(s) compact, eps > 0  ==>
;;;       some delta > 0 with d_t(f(x), f(y)) <= eps whenever x in K, y in pts(s),
;;;       d_s(x, y) <= delta
;;;
;;;   uniformly-continuous-off-compact                                  (Prop 3.22)
;;;     f continuous from s to t, K subset pts(s) compact, and f uniformly continuous
;;;     on X \ K, i.e. RESTRICT(f, X \ K) uniformly continuous from the SUBSPACE
;;;     X \ K to t  ==>  f uniformly continuous from s to t
;;;
;;;   constant-off-compact-uniformly-continuous                         (Cor 3.23)
;;;     f continuous, constant (= some c) at every point of pts(s) outside the
;;;     compact K  ==>  f uniformly continuous
;;;
;;; X \ K is COMPLEMENT-IN(PTS s, K); "f uniformly continuous on X \ K" is stated on
;;; the subspace with f restricted to it, as the notes state functions ON their sets.
;;; The library's uniform continuity is the closed form (d <= delta => d <= eps); the
;;; notes' (49) uses strict inequalities.  The two definitions are equivalent.
;;;
;;; THE STEP NEAR K.  The notes cover K by finitely many balls B(a, delta_a / 2) and
;;; take the least radius.  A finite subfamily of a family of balls with CHOSEN radii
;;; wants a choice function a |-> delta_a and a minimum over a finite set; here the
;;; cover is COUNTABLE and indexed by the radius, so neither is needed:
;;;
;;;   W_n = { x in K : some a in pts(s) has d(a, x) < r_n and
;;;                    d(a, z) < 2 r_n  =>  d(f(a), f(z)) <= eps/2  for every z },
;;;   r_n = 1/(n+1).
;;;
;;; Each W_n is open in the subspace K (a ball of radius r_n - d(a, x) around x stays
;;; in it, with the same a), and the W_n cover K (continuity at x with eps/2 gives a
;;; delta; take r_n < delta/2 and a = x).  `compact-closed-countable-subcover' (compact m, closed a,
;;; a cover by open csq(n)) returns N with every point of K in some W_n, n < N.  Then
;;; delta = r_N works: for x in K, y with d(x, y) <= r_N <= r_n, x in W_n with centre
;;; a, d(a, y) < r_n + r_n, and d(f x, f y) <= d(f x, f a) + d(f a, f y) <= eps.
;;;
;;; PROP 3.22 is then the notes' three cases on the pair (x, y): x in K, y in K
;;; (symmetry), both off K (the hypothesis, read through the subspace distance and
;;; RESTRICT); delta the smaller of the two deltas (rr-min-pos).  Cor 3.23: a function
;;; constant off K is trivially uniformly continuous on X \ K (delta = eps).
;;;
;;; WINDOW.  Latest citations: compact-closed-countable-subcover (theorem-library/
;;; metric-finite-subcover, moved there from riesz-markov-cantor at the wiring of
;;; 2026-10-20 for the library gate), subspace-ball-membership / subspace-dist /
;;; subspace-pts / restrict-apply / restrict-in-fun (theorem-library/metric-subspace-laws),
;;; rr-min-pos, rr-le-ne-lt, nn-recip-succ-*, metric-*, closure-in-carrier and
;;; closure-subset-closed (metric-closure-laws).
;;; hi = none.  Library: analysis.
;;;
;;; Helper prefix: c3u-.

(define (c3u-head g) (and (pair? g) (car g)))

(define (c3u-iff-rhs! iff)
  (let ((rhs (caddr iff)))
    (dk-have! rhs (lambda () (prop)))
    (if (eq? (c3u-head rhs) 'AND) (dk-split-all! (list rhs)))
    rhs))

(define (c3u-ds a b) (list '(DIST s) a b))
(define (c3u-dt a b) (list '(DIST t) a b))
(define (c3u-r n) (list 'RECIP (list '+ n 1)))

;;; W_n, with eps/2 = H.
(define (c3u-w n H)
  (let ((r (c3u-r n)))
    (list 'SEP 'c3ux_ 'K
      (list 'FORSOME 'c3ua_
        (list 'AND (list 'IN 'c3ua_ '(PTS s))
         (list 'AND (list '< (c3u-ds 'c3ua_ 'c3ux_) r)
           (list 'FORALL 'c3uz_
             (list 'IMPLIES (list 'IN 'c3uz_ '(PTS s))
               (list 'IMPLIES (list '< (c3u-ds 'c3ua_ 'c3uz_) (list '+ r r))
                 (list '<= (c3u-dt '(f c3ua_) '(f c3uz_)) H))))))))))

;;; Membership in W_n of a point P with centre A, from the context: run sep-mi and
;;; close the condition's conjuncts: LT-PROOF for the strict inequality, ALL-PROOF
;;; (or `ass' when #f) for the universal clause.
(define (c3u-into-w! P A lt-proof all-proof)
  (for-each
   (lambda (leaf)
     (if (not (sequent-node-grounded? leaf))
         (begin
           (dk-focus! leaf)
           (if (eq? (c3u-head (dk-goal)) 'FORSOME)
               (begin
                 (ew A)
                 (dk-conj-close!
                  (lambda ()
                    (cond ((eq? (c3u-head (dk-goal)) '<) (lt-proof))
                          ((and all-proof (eq? (c3u-head (dk-goal)) 'FORALL)) (all-proof))
                          (#t (ass))))))
               (ass)))))
   (dk-opened (lambda () (sep-mi)))))

;;; Open the membership (IN P (SEP ...)) the context holds (picked, never rebuilt).
(define (c3u-sep-open! P)
  (let ((m (dk-pick (lambda (h) (and (eq? (c3u-head h) 'IN) (equal? (cadr h) P)
                                     (dk-head-is? (caddr h) 'SEP)))
                    "the SEP membership")))
    (dk-split-all! (dk-landed (lambda () (sep-me m))))))

;;; =====================================================================
;;; (1) THE STEP NEAR K.
;;; =====================================================================
(sp (make-wff '(FORALL s (FORALL t (FORALL f (IMPLIES (IS-CONTINUOUS s t f)
     (FORALL K (IMPLIES (SUBSET K (PTS s))
       (IMPLIES (IS-COMPACT (SUBSPACE-MS s K))
         (FORALL eps (IMPLIES (POS-RR eps)
           (FORSOME delta (AND (POS-RR delta)
             (FORALL x (IMPLIES (IN x K)
               (FORALL y (IMPLIES (IN y (PTS s))
                 (IMPLIES (<= ((DIST s) x y) delta)
                   (<= ((DIST t) (f x) (f y)) eps)))))))))))))))))))
(define c3u-landed (dk-peel!))
(define c3u-eps (cadr (car (filter (lambda (f) (eq? (c3u-head f) 'POS-RR)) c3u-landed))))
(define c3u-sub '(SUBSPACE-MS s K))
(c3u-iff-rhs! (dk-cite! 'is-continuous 's 't 'f))
(dk-have! '(IN K SET) (lambda () (dk-sethood! 'K)))
(fact 'subspace-is-metric-space 's 'K)
(fact 'subspace-pts 's 'K)
(define c3u-h (dk-halve! c3u-eps))
(define c3u-L (list 'VNB-LAMBDA 'c3un_ 'NN (c3u-w 'c3un_ c3u-h)))
(define c3u-inst (dk-cite! 'compact-closed-countable-subcover c3u-sub 'K c3u-L))
;;; (b) K is closed in its own subspace: its closure there lies in the subspace's
;;; points, which are K (closure-in-carrier, closure-subset-closed)
(dk-have! (list 'SUBSET (list 'CLOSURE c3u-sub 'K) 'K)
  (lambda ()
    (fact 'closure-in-carrier c3u-sub)
    (let ((cc (dk-apply! (dk-pick (lambda (h) (and (eq? (c3u-head h) 'FORALL) (dk-contains? h 'CLOSURE)
                                                    (dk-contains? h c3u-sub)))
                                  "closure-in-carrier at the subspace")
                         'K)))
      (dk-rewrite-h! cc (list 'PTS c3u-sub) 'K)
      (ass))))
(dk-have! (list 'SUBSET 'K (list 'PTS c3u-sub))
  (lambda () (subst (list '== (list 'PTS c3u-sub) 'K)) (fact 'subset-refl 'K) (ass)))
(dk-have! (cadr c3u-inst)
  (lambda () (fact 'closure-subset-closed c3u-sub 'K) (ass)))
;;; (c) every W_n is open in the subspace
(dk-have! (cadr (caddr c3u-inst))
  (lambda ()
    (let* ((n (dk-di-var!))
           (rn (c3u-r n))
           (wn (c3u-w n c3u-h)))
      (dk-lam-b!)
      (fact 'nn-recip-succ-pos n)
      (fact 'rr-pos-rr-in-rr rn)
      (mac 'IS-OPEN)
      (dk-conj-close!
       (lambda ()
         (let ((g (dk-goal)))
           (cond
            ((eq? (c3u-head g) 'SUBSET)
             (subst (list '== (list 'PTS c3u-sub) 'K))
             (mac 'subset-def)
             (let ((x (dk-di-var!)))
               (c3u-sep-open! x)
               (ass)))
            ((eq? (c3u-head g) 'FORALL)
             (let* ((y (dk-di-var!))
                    (yin (c3u-sep-open! y))
                    (a (dk-skolem! (dk-pick (lambda (h) (and (eq? (c3u-head h) 'FORSOME)
                                                             (dk-contains? h '(DIST t))))
                                            "the centre existential")))
                    (day (c3u-ds a y))
                    (r (list '- rn day)))
               (fact 'subset-mem-fwd 'K '(PTS s) y)
               (fact 'metric-dist-real 's a y)
               (fact 'rr-sub-in-rr rn day)
               (dk-have! (list '< 0 r)
                 (lambda () (dk-ineq! (list '< day rn) (list 'IN day 'RR) (list 'IN rn 'RR)
                                      (list 'IN r 'RR))))
               (fact 'rr-pos-rr-of-lt r)
               (ew r)
               (dk-conj-close!
                (lambda ()
                  (if (eq? (c3u-head (dk-goal)) 'SUBSET)
                      (begin
                        (mac 'subset-def)
                        (let* ((z (dk-di-var!))
                               (dyz (c3u-ds y z))
                               (daz (c3u-ds a z)))
                          (c3u-iff-rhs! (dk-cite! 'subspace-ball-membership 's 'K y r z))
                          (mac-h 'ball-membership (list 'IN z (list 'BALL 's y r)))
                          (dk-split-all!)
                          (fact 'metric-dist-real 's y z)
                          (fact 'metric-dist-real 's a z)
                          (dk-have! (list 'AND (list '<= dyz r) (list 'NOT (list '= dyz r)))
                            (lambda () (dk-conj-close! (lambda () (ass)))))
                          (fact 'rr-le-ne-lt dyz r)
                          (fact 'metric-triangle 's a y z)
                          (c3u-into-w! z a
                            (lambda ()
                              (dk-ineq! (list '<= daz (list '+ day dyz))
                                        (list '< dyz r)
                                        (list 'IN day 'RR) (list 'IN dyz 'RR) (list 'IN daz 'RR)
                                        (list 'IN rn 'RR) (list 'IN r 'RR)))
                            #f)))
                      (ass))))))
            (#t (ass)))))))))
;;; (d) the W_n cover K
(dk-have! (cadr (caddr (caddr c3u-inst)))
  (lambda ()
    (let* ((x (dk-di-var!))
           (ucont (dk-pick (lambda (h) (and (eq? (c3u-head h) 'FORALL)
                                            (dk-contains? h 'IS-CONTINUOUS-AT)))
                           "the pointwise continuity universal")))
      (fact 'subset-mem-fwd 'K '(PTS s) x)
      (dk-apply! ucont x)
      (c3u-iff-rhs! (dk-cite! 'is-continuous-at 's 't 'f x))
      (let* ((ue (dk-pick (lambda (h) (and (eq? (c3u-head h) 'FORALL) (dk-contains? h 'POS-RR)
                                           (dk-contains? h '(DIST t))))
                          "the continuity eps universal"))
             (dl (dk-skolem! (dk-apply! ue c3u-h)))
             (dclause (dk-pick (lambda (h) (and (eq? (c3u-head h) 'FORALL) (dk-contains? h dl)))
                               "the delta clause"))
             (hd (dk-halve! dl))
             (n (dk-skolem! (dk-cite! 'nn-recip-succ-small hd)))
             (rn (c3u-r n)))
        (fact 'nn-recip-succ-pos n)
        (fact 'rr-pos-rr-in-rr rn)
        (fact 'rr-lt-of-pos-rr rn)
        (fact 'metric-self-zero 's x)
        (fact 'metric-dist-real 's x x)
        (ew n)
        (dk-conj-close!
         (lambda ()
           (if (eq? (c3u-head (dk-goal)) 'IN)
               (if (dk-contains? (dk-goal) 'VNB-LAMBDA)
                   (begin
                     (dk-lam-b!)
                     (c3u-into-w! x x
                       (lambda ()
                         (dk-ineq! (list '= (c3u-ds x x) 0) (list '< 0 rn)
                                   (list 'IN (c3u-ds x x) 'RR) (list 'IN rn 'RR)))
                       (lambda ()
                         (let* ((pz (dk-peel!))
                                (z (cadr (car (filter (lambda (f) (eq? (c3u-head f) 'IN)) pz))))
                                (dxz (c3u-ds x z)))
                           (fact 'metric-dist-real 's x z)
                           (fact 'rr-pos-rr-in-rr hd)
                           (fact 'rr-pos-rr-in-rr dl)
                           (dk-have! (list '<= dxz dl)
                             (lambda ()
                               (dk-ineq! (list '< dxz (list '+ rn rn)) (list '< rn hd)
                                         (list '= (list '+ hd hd) dl)
                                         (list 'IN dxz 'RR) (list 'IN rn 'RR)
                                         (list 'IN hd 'RR) (list 'IN dl 'RR))))
                           (dk-apply! dclause z)
                           (ass)))))
                   (ass))
               (ass))))))))
(define c3u-nf (dk-skolem! (dk-apply! c3u-inst)))
;;; the finite subcover: every point of K is in some W_n with n < N
(define c3u-cover (dk-pick (lambda (h) (and (eq? (c3u-head h) 'FORALL) (dk-contains? h c3u-nf)))
                           "the finite subcover clause"))
(define c3u-delta (c3u-r c3u-nf))
(fact 'nn-recip-succ-pos c3u-nf)
(fact 'rr-pos-rr-in-rr c3u-delta)
(fact 'nn-in-rr c3u-nf)
(fact 'rr-pos-rr-in-rr c3u-h)
(fact 'rr-pos-rr-in-rr c3u-eps)
(ew c3u-delta)
(dk-conj-close!
 (lambda ()
   (if (eq? (c3u-head (dk-goal)) 'FORALL)
       (let* ((pl (dk-peel!))
              (x (cadr (car (filter (lambda (f) (and (eq? (c3u-head f) 'IN) (eq? (caddr f) 'K))) pl))))
              (y (cadr (car (filter (lambda (f) (and (eq? (c3u-head f) 'IN) (equal? (caddr f) '(PTS s)))) pl))))
              (n (dk-skolem! (dk-apply! c3u-cover x)))
              (rn (c3u-r n))
              (mem (dk-pick (lambda (h) (and (eq? (c3u-head h) 'IN) (eq? (cadr h) x)
                                             (dk-contains? h 'VNB-LAMBDA)))
                            "x in L(n)")))
         (dk-lam-b-h! mem)
         (c3u-sep-open! x)
         (let* ((a (dk-skolem! (dk-pick (lambda (h) (and (eq? (c3u-head h) 'FORSOME)
                                                         (dk-contains? h '(DIST t))))
                                        "the centre existential")))
                (zc (dk-pick (lambda (h) (and (eq? (c3u-head h) 'FORALL) (dk-contains? h a)))
                             "the centre clause"))
                (dax (c3u-ds a x)) (dxy (c3u-ds x y)) (day (c3u-ds a y))
                (fx (list 'f x)) (fa (list 'f a)) (fy (list 'f y)))
           (fact 'subset-mem-fwd 'K '(PTS s) x)
           (fact 'metric-dist-real 's a x)
           (fact 'metric-dist-real 's x y)
           (fact 'metric-dist-real 's a y)
           (fact 'nn-recip-succ-pos n)
           (fact 'rr-pos-rr-in-rr rn)
           (fact 'nn-in-rr n)
           (fact 'rr-lt-of-pos-rr rn)
           (dk-have! (list '<= n c3u-nf)
             (lambda () (dk-ineq! (list '< n c3u-nf) (list 'IN n 'RR) (list 'IN c3u-nf 'RR))))
           (fact 'nn-recip-succ-antitone n c3u-nf)
           (fact 'metric-triangle 's a x y)
           (dk-have! (list '< dax (list '+ rn rn))
             (lambda () (dk-ineq! (list '< dax rn) (list 'IN dax 'RR) (list 'IN rn 'RR)
                                  (list '< 0 rn))))
           (dk-apply! zc x)
           (dk-have! (list '< day (list '+ rn rn))
             (lambda () (dk-ineq! (list '<= day (list '+ dax dxy)) (list '< dax rn)
                                  (list '<= dxy c3u-delta) (list '<= c3u-delta rn)
                                  (list 'IN dax 'RR) (list 'IN dxy 'RR) (list 'IN day 'RR)
                                  (list 'IN rn 'RR) (list 'IN c3u-delta 'RR))))
           (dk-apply! zc y)
           (fact 'fun-apply-type-c 'f '(PTS s) '(PTS t) x)
           (fact 'fun-apply-type-c 'f '(PTS s) '(PTS t) y)
           (fact 'fun-apply-type-c 'f '(PTS s) '(PTS t) a)
           (fact 'metric-triangle 't fx fa fy)
           (fact 'metric-sym 't fx fa)
           (fact 'metric-dist-real 't fx fa)
           (fact 'metric-dist-real 't fa fx)
           (fact 'metric-dist-real 't fa fy)
           (fact 'metric-dist-real 't fx fy)
           (dk-ineq! (list '<= (c3u-dt fx fy) (list '+ (c3u-dt fx fa) (c3u-dt fa fy)))
                     (list '= (c3u-dt fx fa) (c3u-dt fa fx))
                     (list '<= (c3u-dt fa fx) c3u-h)
                     (list '<= (c3u-dt fa fy) c3u-h)
                     (list '= (list '+ c3u-h c3u-h) c3u-eps)
                     (list 'IN (c3u-dt fx fy) 'RR) (list 'IN (c3u-dt fx fa) 'RR)
                     (list 'IN (c3u-dt fa fx) 'RR) (list 'IN (c3u-dt fa fy) 'RR)
                     (list 'IN c3u-h 'RR) (list 'IN c3u-eps 'RR))))
       (ass))))
(qed 'continuous-uniform-near-compact)
(topic! 'continuous-uniform-near-compact 'analysis)
(alias! 'continuous-uniform-near-compact
        "a continuous function is uniformly continuous near a compact set")
;;; =====================================================================
;;; (2) PROP 3.22.
;;; =====================================================================
(define c3u-C '(COMPLEMENT-IN (PTS s) K))
(define c3u-sc (list 'SUBSPACE-MS 's c3u-C))
(define c3u-fr (list 'RESTRICT 'f c3u-C))

;;; x in C from x in PTS(s) and NOT(x in K), both in context.
(define (c3u-in-c! x)
  (dk-have! (list 'IN x c3u-C)
    (lambda () (mac 'complement-in-membership) (dk-conj-close! (lambda () (ass))))))

(sp (make-wff (list 'FORALL 's (list 'FORALL 't (list 'FORALL 'f (list 'IMPLIES '(IS-CONTINUOUS s t f)
     (list 'FORALL 'K (list 'IMPLIES '(SUBSET K (PTS s))
       (list 'IMPLIES '(IS-COMPACT (SUBSPACE-MS s K))
         (list 'IMPLIES (list 'IS-UNIFORMLY-CONTINUOUS c3u-sc 't c3u-fr)
           '(IS-UNIFORMLY-CONTINUOUS s t f)))))))))))
(dk-peel!)
(c3u-iff-rhs! (dk-cite! 'is-continuous 's 't 'f))
(c3u-iff-rhs! (dk-cite! 'is-uniformly-continuous c3u-sc 't c3u-fr))
(dk-have! (list 'IN c3u-C 'SET) (lambda () (dk-sethood! c3u-C)))
(fact 'subspace-pts 's c3u-C)
(define c3u-uoff (dk-pick (lambda (h) (and (eq? (c3u-head h) 'FORALL) (dk-contains? h 'POS-RR)
                                           (dk-contains? h 'RESTRICT)))
                          "uniform continuity off K"))
(mac 'IS-UNIFORMLY-CONTINUOUS)
(dk-conj-close!
 (lambda ()
   (if (eq? (c3u-head (dk-goal)) 'FORALL)
       (let* ((pe (dk-peel!))
              (eps (cadr (car (filter (lambda (f) (eq? (c3u-head f) 'POS-RR)) pe))))
              (d1 (dk-skolem! (dk-apply! c3u-uoff eps)))
              (c1 (dk-pick (lambda (h) (and (eq? (c3u-head h) 'FORALL) (dk-contains? h d1)))
                           "the clause off K"))
              (d2 (dk-skolem! (dk-cite! 'continuous-uniform-near-compact 's 't 'f 'K eps)))
              (c2 (dk-pick (lambda (h) (and (eq? (c3u-head h) 'FORALL) (dk-contains? h d2)))
                           "the clause near K")))
         (dk-pos-parts! d1)
         (dk-pos-parts! d2)
         (let ((w (dk-skolem! (dk-cite! 'rr-min-pos d1 d2))))
           (fact 'rr-pos-rr-of-lt w)
           (ew w)
           (dk-conj-close!
            (lambda ()
              (if (eq? (c3u-head (dk-goal)) 'FORALL)
                  (let* ((pl (dk-peel!))
                         (ins (filter (lambda (f) (and (eq? (c3u-head f) 'IN)
                                                       (equal? (caddr f) '(PTS s))))
                                      pl))
                         (le (car (filter (lambda (f) (eq? (c3u-head f) '<=)) pl)))
                         (x (cadr (cadr le)))
                         (y (caddr (cadr le)))
                         (dxy (c3u-ds x y)) (dyx (c3u-ds y x))
                         (fx (list 'f x)) (fy (list 'f y)))
                    (fact 'metric-dist-real 's x y)
                    (fact 'metric-dist-real 's y x)
                    (fact 'metric-sym 's x y)
                    (fact 'fun-apply-type-c 'f '(PTS s) '(PTS t) x)
                    (fact 'fun-apply-type-c 'f '(PTS s) '(PTS t) y)
                    (use-em (list 'IN x 'K)
                      (lambda ()
                        (dk-have! (list '<= dxy d2)
                          (lambda () (dk-ineq! (list '<= dxy w) (list '<= w d2)
                                               (list 'IN dxy 'RR) (list 'IN w 'RR) (list 'IN d2 'RR))))
                        (dk-apply! c2 x y)
                        (ass))
                      (lambda ()
                        (use-em (list 'IN y 'K)
                          (lambda ()
                            (dk-have! (list '<= dyx d2)
                              (lambda () (dk-ineq! (list '= dxy dyx) (list '<= dxy w) (list '<= w d2)
                                                   (list 'IN dxy 'RR) (list 'IN dyx 'RR)
                                                   (list 'IN w 'RR) (list 'IN d2 'RR))))
                            (dk-apply! c2 y x)
                            (fact 'metric-sym 't fx fy)
                            (subst (list '= (c3u-dt fx fy) (c3u-dt fy fx)))
                            (ass))
                          (lambda ()
                            (c3u-in-c! x)
                            (c3u-in-c! y)
                            (let ((dsc (list (list 'DIST c3u-sc) x y)))
                              (dk-have! (list 'IN x (list 'PTS c3u-sc))
                                (lambda () (subst (list '== (list 'PTS c3u-sc) c3u-C)) (ass)))
                              (dk-have! (list 'IN y (list 'PTS c3u-sc))
                                (lambda () (subst (list '== (list 'PTS c3u-sc) c3u-C)) (ass)))
                              (fact 'subspace-dist 's c3u-C x y)
                              (dk-have! (list '<= dsc d1)
                                (lambda ()
                                  (subst (list '== dsc dxy))
                                  (dk-ineq! (list '<= dxy w) (list '<= w d1)
                                            (list 'IN dxy 'RR) (list 'IN w 'RR) (list 'IN d1 'RR))))
                              (dk-apply! c1 x y)
                              (fact 'restrict-apply 'f c3u-C x)
                              (fact 'restrict-apply 'f c3u-C y)
                              (subst (list '== fx (list c3u-fr x)))
                              (subst (list '== fy (list c3u-fr y)))
                              (ass)))))))
                  (ass))))))
       (ass))))
(qed 'uniformly-continuous-off-compact)
(topic! 'uniformly-continuous-off-compact 'analysis)
(alias! 'uniformly-continuous-off-compact
        "continuous, and uniformly continuous off a compact set, is uniformly continuous")

;;; =====================================================================
;;; (3) COR 3.23.
;;; =====================================================================
(sp (make-wff '(FORALL s (FORALL t (FORALL f (IMPLIES (IS-CONTINUOUS s t f)
     (FORALL K (IMPLIES (SUBSET K (PTS s))
       (IMPLIES (IS-COMPACT (SUBSPACE-MS s K))
         (IMPLIES (FORSOME cv (FORALL x (IMPLIES (IN x (PTS s))
                                (IMPLIES (NOT (IN x K)) (= (f x) cv)))))
           (IS-UNIFORMLY-CONTINUOUS s t f)))))))))))
(dk-peel!)
(define c3u-cv (dk-skolem! (dk-pick (lambda (h) (and (eq? (c3u-head h) 'FORSOME) (dk-contains? h 'K)))
                                    "the constant")))
(define c3u-const (dk-pick (lambda (h) (and (eq? (c3u-head h) 'FORALL) (dk-contains? h c3u-cv)))
                           "the constancy clause"))
(c3u-iff-rhs! (dk-cite! 'is-continuous 's 't 'f))
(dk-have! (list 'IN c3u-C 'SET) (lambda () (dk-sethood! c3u-C)))
(fact 'complement-in-subset 'K '(PTS s))
(fact 'subspace-is-metric-space 's c3u-C)
(fact 'subspace-pts 's c3u-C)
(fact 'restrict-in-fun 'f '(PTS s) '(PTS t) c3u-C)
;;; constant off K at a point of C, read off the constancy clause
(define (c3u-const-at! a)
  (fact 'complement-in-membership a '(PTS s) 'K)
  (mac-h 'complement-in-membership (list 'IN a c3u-C))
  (dk-split-all!)
  (dk-apply! c3u-const a))
(dk-have! (list 'IS-UNIFORMLY-CONTINUOUS c3u-sc 't c3u-fr)
  (lambda ()
    (mac 'IS-UNIFORMLY-CONTINUOUS)
    (dk-conj-close!
     (lambda ()
       (let ((g (dk-goal)))
         (cond
          ((eq? (c3u-head g) 'FORALL)
           (let* ((pe (dk-peel!))
                  (eps (cadr (car (filter (lambda (f) (eq? (c3u-head f) 'POS-RR)) pe)))))
             (dk-pos-parts! eps)
             (ew eps)
             (dk-conj-close!
              (lambda ()
                (if (eq? (c3u-head (dk-goal)) 'FORALL)
                    (let* ((pl (dk-peel!))
                           (le (car (filter (lambda (f) (eq? (c3u-head f) '<=)) pl)))
                           (a (cadr (cadr le)))
                           (b (caddr (cadr le))))
                      (dk-have! (list 'IN a c3u-C)
                        (lambda () (subst (list '== c3u-C (list 'PTS c3u-sc))) (ass)))
                      (dk-have! (list 'IN b c3u-C)
                        (lambda () (subst (list '== c3u-C (list 'PTS c3u-sc))) (ass)))
                      (fact 'restrict-apply 'f c3u-C a)
                      (fact 'restrict-apply 'f c3u-C b)
                      (c3u-const-at! a)
                      (c3u-const-at! b)
                      (fact 'fun-apply-type-c 'f '(PTS s) '(PTS t) a)
                      (dk-have! (list 'IN c3u-cv '(PTS t))
                        (lambda () (subst (list '= c3u-cv (list 'f a))) (ass)))
                      (fact 'metric-self-zero 't c3u-cv)
                      (subst (list '== (list c3u-fr a) (list 'f a)))
                      (subst (list '== (list c3u-fr b) (list 'f b)))
                      (subst (list '= (list 'f a) c3u-cv))
                      (subst (list '= (list 'f b) c3u-cv))
                      (subst (list '= (c3u-dt c3u-cv c3u-cv) 0))
                      (dk-ineq! (list '< 0 eps) (list 'IN eps 'RR)))
                    (ass))))))
          ((eq? (c3u-head g) 'IN)
           (subst (list '== (list 'PTS c3u-sc) c3u-C))
           (ass))
          (#t (ass))))))))
(fact 'uniformly-continuous-off-compact 's 't 'f 'K)
(ass)
(qed 'constant-off-compact-uniformly-continuous)
(topic! 'constant-off-compact-uniformly-continuous 'analysis)
(alias! 'constant-off-compact-uniformly-continuous
        "a continuous function constant off a compact set is uniformly continuous")
