;;; series-linearity.scm -- LINEARITY OF THE REAL PARTIAL SUM, in POINTWISE form.
;;;
;;;   series-partial-sum-in-rr-ptwise    SPS(f,n) in RR
;;;   series-partial-sum-add-ptwise      SPS(h,n) = SPS(f,n) + SPS(g,n)
;;;   series-partial-sum-scale-ptwise    SPS(h,n) = c * SPS(f,n)
;;;   series-partial-sum-le-termwise-ptwise   f(k) <= g(k) ==> SPS(f,n) <= SPS(g,n)
;;;
;;; all four `modulo 0', each a three-line NN induction whose step is
;;; `series-partial-sum-succ' (comparison-test-proof.scm) followed by `crs'
;;; (by `rr-le-add' for the monotonicity, which is an order fact rather than a
;;; ring identity).
;;;
;;; WHY THESE EXIST BESIDE `series-partial-sum-add' (dominated-convergence.scm),
;;; which says the same thing.  Two differences, and both are needed by the
;;; Bernstein moments (bernstein-moments.scm), which is the first caller:
;;;
;;;  (1) POINTWISE typing, not FUN(NN,RR) membership.  The Bernstein basis
;;;      family is indexed by ZZ -- COMB-KK(R,x,y,m) is in FUN(ZZ, CARR R), so
;;;      that k-1 is total at k = 0 -- and is therefore not an element of
;;;      FUN(NN,RR) at all.  What it does satisfy is `forall k in NN. f(k) in
;;;      RR', which is all an induction over an initial NN segment ever uses.
;;;      The hypothesis is also what a VNB-LAMBDA summand can discharge by
;;;      `lam-b' alone, where FUN membership would cost a `lam-t' (two leaves,
;;;      one of them the sethood of the domain).
;;;
;;;  (2) TRANSFER form.  The sum family `h' is a free variable constrained by a
;;;      pointwise equation, not the literal lambda `k |-> f(k) + g(k)'.  A
;;;      conclusion about the literal term is a conclusion about that term only;
;;;      the transfer form applies to any family that happens to agree with it,
;;;      which is what lets the three moment identities be chained.  (Same
;;;      mechanism, and the same reason, as `cont-transfer-ptwise-eq' in
;;;      continuity-transfer.scm.)
;;;
;;; This is the infrastructure the Bernstein rung was missing.  It replaces NO
;;; axiom, but it is what makes `sum-left-scalar' (sequences.scm:192 -- a bare
;;; `theory-add-axiom!' with no `warrant!', i.e. `trust: none' for every citer)
;;; unnecessary on the RR surface: cite these instead.
;;;
;;; Loads after comparison-test-proof (series-partial-sum-zero/-succ).

;;; ---- file-local builders and driver (the `sl-' prefix) ---------------

;;; forall k in NN. f(k) in RR   -- the pointwise typing hypothesis
(define (sl-ptwise-real f)
  (list 'FORALL 'k_ (list 'IMPLIES '(IN k_ NN) (list 'IN (list f 'k_) 'RR))))

;;; forall k in NN. h(k) = RHS(k)   -- the transfer hypothesis
(define (sl-ptwise-eq h rhs)
  (list 'FORALL 'k_ (list 'IMPLIES '(IN k_ NN) (list '= (list h 'k_) (rhs 'k_)))))

;;; the shape `ni' (and hence `use-induction') tests for: the NN variable FIRST.
(define (sl-nn-induction inner)
  (list 'FORALL 'n_ (list 'IMPLIES '(IN n_ NN) inner)))

;;; `di' is greedy and a guarded universal goes whole under one call while an
;;; unguarded one does not, so a COUNT of di's is not a way to land on a chosen
;;; goal.  Loop until the goal's head stops being FORALL/IMPLIES.
(define (sl-peel!)
  (let loop ((n 0))
    (let ((g (dk-goal)))
      (if (and (pair? g) (memq (car g) '(FORALL IMPLIES)) (< n 14))
          (begin (di) (loop (+ n 1))) #t))))

;;; Instantiate every UNIVERSAL among the landed hypotheses at the index `n'.
;;; Done by shape rather than by position in the landing list: `dk-landed*'
;;; returns newest-first, and a driver that reads the third landing as "the
;;; transfer equation" gets the typing hypothesis when the binder count changes.
(define (sl-inst-all! hyps n)
  (for-each (lambda (a)
              (if (and (pair? a) (eq? (car a) 'FORALL))
                  (dk-deepest (lambda () (inst+ a n)))))
            hyps))

(define (sl-check name)
  (if (not (proof-done? *ps*))
      (error "series-linearity: proof did not close" name
             (expression->string (dk-goal)))))

;;; =====================================================================
;;; 1.  A POINTWISE-REAL FAMILY HAS REAL PARTIAL SUMS.
;;;
;;; `series-partial-sum-in-rr' says this for f in FUN(NN,RR); this is the same
;;; induction under the weaker hypothesis.  Base is series-partial-sum-zero,
;;; step is the recurrence plus rr-add-closed (whose antecedent is an AND, so
;;; it wants a `have!' immediately before the `fact').
;;; =====================================================================

(quietly (lambda ()
  (sp (make-wff (sl-nn-induction
        (list 'FORALL 'f_ (list 'IMPLIES (sl-ptwise-real 'f_)
              '(IN (SERIES-PARTIAL-SUM f_ n_) RR))))))
  (let* ((br (use-induction)) (n (cdr (assq 'var br))) (ih (cdr (assq 'ih br))))
    (dk-focus! (cdr (assq 'base br)))
    (sl-peel!) (mac 'series-partial-sum-zero) (fact 'rr-zero-in) (ass)
    (dk-focus! (cdr (assq 'step br)))
    (let ((pw (dk-landed-1 (lambda () (sl-peel!)))))
      (mac 'series-partial-sum-succ)
      (dk-deepest (lambda () (inst+ ih 'f_)))
      (dk-deepest (lambda () (inst+ pw n)))
      (have! (list 'AND (list 'IN (list 'SERIES-PARTIAL-SUM 'f_ n) 'RR)
                        (list 'IN (list 'f_ n) 'RR)))
      (fact 'rr-add-closed (list 'SERIES-PARTIAL-SUM 'f_ n) (list 'f_ n))
      (ass)))))
(sl-check 'series-partial-sum-in-rr-ptwise)
(qed 'series-partial-sum-in-rr-ptwise)
(topic! 'series-partial-sum-in-rr-ptwise 'analysis)
(alias! 'series-partial-sum-in-rr-ptwise
        "a pointwise-real family has real partial sums")

;;; =====================================================================
;;; 2.  PARTIAL SUMS ADD (transfer form).
;;; =====================================================================

(quietly (lambda ()
  (sp (make-wff (sl-nn-induction
    (forall-guarded '(f_ g_ h_)
      (list (sl-ptwise-real 'f_) (sl-ptwise-real 'g_)
            (sl-ptwise-eq 'h_ (lambda (k) (list '+ (list 'f_ k) (list 'g_ k)))))
      '(= (SERIES-PARTIAL-SUM h_ n_)
          (+ (SERIES-PARTIAL-SUM f_ n_) (SERIES-PARTIAL-SUM g_ n_)))))))
  (let* ((br (use-induction)) (n (cdr (assq 'var br))) (ih (cdr (assq 'ih br))))
    (dk-focus! (cdr (assq 'base br)))
    (sl-peel!) (mac 'series-partial-sum-zero) (arith)
    (dk-focus! (cdr (assq 'step br)))
    (let ((hyps (dk-landed* (lambda () (sl-peel!)))))
      (mac 'series-partial-sum-succ)
      (let* ((i1  (dk-deepest (lambda () (inst+ ih 'f_))))
             (i2  (dk-deepest (lambda () (inst+ i1 'g_))))
             (ihc (dk-deepest (lambda () (inst+ i2 'h_)))))
        (sl-inst-all! hyps n)
        (fact 'series-partial-sum-in-rr-ptwise n 'f_)
        (fact 'series-partial-sum-in-rr-ptwise n 'g_)
        (subst ihc)
        (subst (list '= (list 'h_ n) (list '+ (list 'f_ n) (list 'g_ n))))
        (crs))))))
(sl-check 'series-partial-sum-add-ptwise)
(qed 'series-partial-sum-add-ptwise)
(topic! 'series-partial-sum-add-ptwise 'analysis)
(alias! 'series-partial-sum-add-ptwise "partial sums add (pointwise form)")

;;; =====================================================================
;;; 3.  A SCALAR COMES OUT OF A PARTIAL SUM (transfer form).
;;;
;;; This is what `sum-left-scalar' (sequences.scm) asserts for the ring SUM,
;;; here PROVEN for the real partial sum.
;;; =====================================================================

(quietly (lambda ()
  (sp (make-wff (sl-nn-induction
    (forall-guarded '(c_ f_ h_)
      (list '(IN c_ RR) (sl-ptwise-real 'f_)
            (sl-ptwise-eq 'h_ (lambda (k) (list '* 'c_ (list 'f_ k)))))
      '(= (SERIES-PARTIAL-SUM h_ n_) (* c_ (SERIES-PARTIAL-SUM f_ n_)))))))
  (let* ((br (use-induction)) (n (cdr (assq 'var br))) (ih (cdr (assq 'ih br))))
    (dk-focus! (cdr (assq 'base br)))
    (sl-peel!) (mac 'series-partial-sum-zero) (crs)
    (dk-focus! (cdr (assq 'step br)))
    (let ((hyps (dk-landed* (lambda () (sl-peel!)))))
      (mac 'series-partial-sum-succ)
      (let* ((j1  (dk-deepest (lambda () (inst+ ih 'c_))))
             (j2  (dk-deepest (lambda () (inst+ j1 'f_))))
             (ihc (dk-deepest (lambda () (inst+ j2 'h_)))))
        (sl-inst-all! hyps n)
        (fact 'series-partial-sum-in-rr-ptwise n 'f_)
        (subst ihc)
        (subst (list '= (list 'h_ n) (list '* 'c_ (list 'f_ n))))
        (crs))))))
(sl-check 'series-partial-sum-scale-ptwise)
(qed 'series-partial-sum-scale-ptwise)
(topic! 'series-partial-sum-scale-ptwise 'analysis)
(alias! 'series-partial-sum-scale-ptwise
        "a scalar comes out of a partial sum (pointwise form)")

;;; =====================================================================
;;; 4.  THE WEIGHTED EXPANSION -- multiply-and-shift, on the RR surface.
;;;
;;;   SPS(k |-> w(k)(x g(k-1) + y g(k)), succ N)
;;;      =  x ( w(0) g(-1) + SPS(j |-> w(succ j) g(j), N) )
;;;      +  y ( SPS(k |-> w(k) g(k), N)   +  w(N) g(N) )
;;;
;;; `sum-expansion' (binomial-proof.scm) is the WEIGHT-1 case of this, stated
;;; over an arbitrary commutative ring; this is the same induction with a
;;; weight `w' threaded through and the ring replaced by RR's surface
;;; arithmetic, which is where `crs' can see it.
;;;
;;; WHY THIS, AND NOT THE TEXTBOOK ABSORPTION IDENTITY.  The classical route to
;;; the Bernstein moments is  k C(n,k) = n C(n-1,k-1)  by induction on n.  That
;;; is true, and it is out of reach here: `comb-kk-zero' is
;;;   COMB-KK(R,x,y,0) = VNB-LAMBDA k NN. IF k = 0 THEN ONE(R) ELSE ZERO(R),
;;; so its base case is a four-way case split on a ZZ index -- k<0, k=0, k=1,
;;; k>1 -- whose middle two cases are separated from the outer two only by the
;;; DISCRETENESS of ZZ.  The tree has no ZZ order theory at all (there are no
;;; zz-lt / zz-le facts anywhere), and the ordinal route that unblocked the NN
;;; order ladder is unavailable because ZZ does not embed in ORD.  `ineq' is a
;;; REAL oracle and cannot supply discreteness either.
;;;
;;; This expansion never splits on k.  It only ever peels the TOP index with
;;; the partial-sum recurrence, so the shift is carried by the recursion rather
;;; than by a reindex bijection -- exactly as IMPS's expansion lemma, and
;;; exactly as `sum-expansion' does one storey down.  That is why it is the
;;; right mechanism and not merely a tidier one.
;;;
;;; The pointwise-realness of q and s is HYPOTHESISED rather than derived from
;;; w and g: every caller has to establish it for its own weight anyway (the
;;; moment inductions need SPS(q,N) and SPS(s,N) to be real to run at all), and
;;; deriving it here would duplicate that work inside both branches.
;;;
;;; Bills the four ZZ/NN index shims of binomial.scm (bt-nn-in-zz,
;;; bt-succ-in-nn, bt-neg1-in-zz, bt-succ-minus-1), all `well-known'.
;;; =====================================================================

;;; forall k in ZZ. f(k) in RR -- the ZZ-indexed pointwise typing.  A family
;;; used at k-1 must be typed at -1, which no NN-indexed hypothesis reaches.
(define (sl-ptwise-real-zz f)
  (list 'FORALL 'k_ (list 'IMPLIES '(IN k_ ZZ) (list 'IN (list f 'k_) 'RR))))

(define sl-p-eq
  (sl-ptwise-eq 'p_ (lambda (k) (list '* (list 'w_ k)
                     (list '+ (list '* 'x_ (list 'g_ (list '- k 1)))
                              (list '* 'y_ (list 'g_ k)))))))
(define sl-q-eq
  (sl-ptwise-eq 'q_ (lambda (k) (list '* (list 'w_ (list 'succ k)) (list 'g_ k)))))
(define sl-s-eq
  (sl-ptwise-eq 's_ (lambda (k) (list '* (list 'w_ k) (list 'g_ k)))))

(define sl-weighted-stmt
  (sl-nn-induction
    (forall-guarded '(x_ y_ g_ w_ p_ q_ s_)
      (list '(IN x_ RR) '(IN y_ RR)
            (sl-ptwise-real-zz 'g_) (sl-ptwise-real-zz 'w_)
            (sl-ptwise-real 'q_) (sl-ptwise-real 's_)
            sl-p-eq sl-q-eq sl-s-eq)
      '(= (SERIES-PARTIAL-SUM p_ (succ n_))
          (+ (* x_ (+ (* (w_ 0) (g_ (- 0 1))) (SERIES-PARTIAL-SUM q_ n_)))
             (* y_ (+ (SERIES-PARTIAL-SUM s_ n_) (* (w_ n_) (g_ n_)))))))))

;;; A hypothesis this driver rebuilds by hand rather than reading off the
;;; landing list -- and CHECKS, because a reconstructed formula that matches
;;; nothing makes `inst+' a silent no-op and every later step run in the wrong
;;; branch.
(define (sl-hyp form)
  (if (any-pred (lambda (a) (alpha-equiv? a form)) (dk-asms))
      form
      (error "series-linearity: hypothesis not in context"
             (expression->string form))))

(quietly (lambda ()
  (sp (make-wff sl-weighted-stmt))
  (let* ((br (use-induction)) (n (cdr (assq 'var br))) (ih (cdr (assq 'ih br))))

    ;; ---- BASE.  Both partial sums on the right are empty; the left has the
    ;; single term p(0), which the transfer equation opens.
    (dk-focus! (cdr (assq 'base br)))
    (sl-peel!)
    (fact 'nn-zero-in) (fact 'zz-zero-in) (fact 'bt-neg1-in-zz)
    (fact 'series-partial-sum-succ 'p_ 0)
    (subst '(== (SERIES-PARTIAL-SUM p_ (succ 0))
                (+ (SERIES-PARTIAL-SUM p_ 0) (p_ 0))))
    (mac 'series-partial-sum-zero)
    (dk-deepest (lambda () (inst+ (sl-hyp sl-p-eq) 0)))
    (subst '(= (p_ 0) (* (w_ 0) (+ (* x_ (g_ (- 0 1))) (* y_ (g_ 0))))))
    (dk-deepest (lambda () (inst+ (sl-hyp (sl-ptwise-real-zz 'w_)) 0)))
    (dk-deepest (lambda () (inst+ (sl-hyp (sl-ptwise-real-zz 'g_)) '(- 0 1))))
    (dk-deepest (lambda () (inst+ (sl-hyp (sl-ptwise-real-zz 'g_)) 0)))
    (crs)

    ;; ---- STEP.  Peel the top term off each of the three partial sums with
    ;; `series-partial-sum-succ' cited AT THE INSTANCE rather than applied as a
    ;; goal rewrite: SPS(p, succ(succ N)) unfolds to SPS(p, succ N) + p(succ N),
    ;; and SPS(p, succ N) is exactly what the induction hypothesis is about, so
    ;; a rewrite that fired everywhere would consume it.
    (dk-focus! (cdr (assq 'step br)))
    (sl-peel!)
    (fact 'bt-succ-in-nn n) (fact 'nn-zero-in) (fact 'zz-zero-in)
    (fact 'bt-neg1-in-zz) (fact 'bt-nn-in-zz n)
    (fact 'bt-nn-in-zz (list 'succ n))
    (fact 'series-partial-sum-succ 'p_ (list 'succ n))
    (subst (list '== (list 'SERIES-PARTIAL-SUM 'p_ (list 'succ (list 'succ n)))
                     (list '+ (list 'SERIES-PARTIAL-SUM 'p_ (list 'succ n))
                              (list 'p_ (list 'succ n)))))
    (fact 'series-partial-sum-succ 'q_ n)
    (subst (list '== (list 'SERIES-PARTIAL-SUM 'q_ (list 'succ n))
                     (list '+ (list 'SERIES-PARTIAL-SUM 'q_ n) (list 'q_ n))))
    (fact 'series-partial-sum-succ 's_ n)
    (subst (list '== (list 'SERIES-PARTIAL-SUM 's_ (list 'succ n))
                     (list '+ (list 'SERIES-PARTIAL-SUM 's_ n) (list 's_ n))))
    (let ((ihc (let loop ((f ih) (vs '(x_ y_ g_ w_ p_ q_ s_)))
                 (if (null? vs) f
                     (loop (dk-deepest (lambda () (inst+ f (car vs))))
                           (cdr vs))))))
      (subst ihc))
    (dk-deepest (lambda () (inst+ (sl-hyp sl-p-eq) (list 'succ n))))
    (subst (list '= (list 'p_ (list 'succ n))
                 (list '* (list 'w_ (list 'succ n))
                       (list '+ (list '* 'x_ (list 'g_ (list '- (list 'succ n) 1)))
                                (list '* 'y_ (list 'g_ (list 'succ n)))))))
    (fact 'bt-succ-minus-1 n)
    (subst (list '= (list '- (list 'succ n) 1) n))
    (dk-deepest (lambda () (inst+ (sl-hyp sl-q-eq) n)))
    (subst (list '= (list 'q_ n) (list '* (list 'w_ (list 'succ n)) (list 'g_ n))))
    (dk-deepest (lambda () (inst+ (sl-hyp sl-s-eq) n)))
    (subst (list '= (list 's_ n) (list '* (list 'w_ n) (list 'g_ n))))
    (for-each (lambda (t) (dk-deepest
                            (lambda () (inst+ (sl-ptwise-real-zz 'w_) t))))
              (list 0 n (list 'succ n)))
    (for-each (lambda (t) (dk-deepest
                            (lambda () (inst+ (sl-ptwise-real-zz 'g_) t))))
              (list '(- 0 1) n (list 'succ n)))
    (fact 'series-partial-sum-in-rr-ptwise n 'q_)
    (fact 'series-partial-sum-in-rr-ptwise n 's_)
    (crs))))
(sl-check 'series-partial-sum-weighted-expansion)
(qed 'series-partial-sum-weighted-expansion)
(topic! 'series-partial-sum-weighted-expansion 'analysis)
(alias! 'series-partial-sum-weighted-expansion
        "the weighted multiply-and-shift expansion of a partial sum")

;;; =====================================================================
;;; 5.  PARTIAL SUMS ARE MONOTONE, TERMWISE (pointwise form).
;;;
;;;   forall k in NN. f(k) <= g(k)   ==>   SPS(f,n) <= SPS(g,n)
;;;
;;; `series-partial-sum-le-termwise' (comparison-test-proof.scm) says this for
;;; f, g in FUN(NN,RR); this is the same three-line induction under the weaker
;;; POINTWISE typing, which is what a ZZ-indexed family such as the Bernstein
;;; basis satisfies and FUN(NN,RR) membership does not -- the same reason the
;;; three laws above exist beside their FUN-typed twins.
;;;
;;; It is what carries the Bernstein term estimate (bernstein-density.scm) from
;;; each summand to the sum, in both directions: monotonicity is one-sided, so
;;; the lower bound crosses the sum as the upper bound of the negated family.
;;; =====================================================================

(quietly (lambda ()
  (sp (make-wff (sl-nn-induction
      (forall-guarded '(f_ g_)
        (list (sl-ptwise-real 'f_) (sl-ptwise-real 'g_)
              (list 'FORALL 'k_ (list 'IMPLIES '(IN k_ NN)
                                      (list '<= (list 'f_ 'k_) (list 'g_ 'k_)))))
        '(<= (SERIES-PARTIAL-SUM f_ n_) (SERIES-PARTIAL-SUM g_ n_))))))
  (let* ((br (use-induction)) (n (cdr (assq 'var br))) (ih (cdr (assq 'ih br))))
    (dk-focus! (cdr (assq 'base br)))
    (sl-peel!) (mac 'series-partial-sum-zero) (arith)
    (dk-focus! (cdr (assq 'step br)))
    (let ((hyps (dk-landed* (lambda () (sl-peel!)))))
      (mac 'series-partial-sum-succ)
      (let ((j1 (dk-deepest (lambda () (inst+ ih 'f_)))))
        (dk-deepest (lambda () (inst+ j1 'g_))))
      (sl-inst-all! hyps n)
      (fact 'series-partial-sum-in-rr-ptwise n 'f_)
      (fact 'series-partial-sum-in-rr-ptwise n 'g_)
      (have! (list 'AND (list '<= (list 'SERIES-PARTIAL-SUM 'f_ n)
                                   (list 'SERIES-PARTIAL-SUM 'g_ n))
                        (list '<= (list 'f_ n) (list 'g_ n))))
      (fact 'rr-le-add (list 'SERIES-PARTIAL-SUM 'f_ n) (list 'SERIES-PARTIAL-SUM 'g_ n)
                       (list 'f_ n) (list 'g_ n))
      (ass)))))
(sl-check 'series-partial-sum-le-termwise-ptwise)
(qed 'series-partial-sum-le-termwise-ptwise)
(topic! 'series-partial-sum-le-termwise-ptwise 'analysis)
(alias! 'series-partial-sum-le-termwise-ptwise
        "partial sums are termwise monotone (pointwise form)")
