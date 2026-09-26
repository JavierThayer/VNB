;;; rake-series2.scm -- rake batch 5c (2026-09-18), assignment 5c-R: the two
;;; series leaves batch T left BLOCKED, and the four bricks they were missing.
;;;
;;;   metric-chain-bound         d(f m, f n) <= P(n) - P(m) for a dominating
;;;                              real sequence rad and m <= n           (NEW)
;;;   metric-chain-triangle      the same with rad := the consecutive-distance
;;;                              sequence itself                        (NEW)
;;;   summable-bound-implies-cauchy   theorem-library/summable-cauchy.scm:23
;;;   rr-power-le-one            0 <= r <= 1  =>  r^k <= 1              (NEW)
;;;   rr-power-shrink-bound      0 <= r <= 1  =>  k(1-r) r^k <= 1       (NEW)
;;;   power-small-threshold      0 <= r < 1, eps > 0 => some N with
;;;                              r^k <= eps for all k >= N              (NEW)
;;;   power-tends-to-zero        |r| < 1  =>  r^k -> 0                  (NEW)
;;;   rr-const-converges-to      the constant sequence                  (NEW)
;;;   geometric-series-converges-to   theorem-library/power-series.scm:214
;;;
;;; Helper prefix: r7r-.
;;;
;;; ---------------------------------------------------------------------------
;;; THE RANGE OF r IN geometric-series-converges-to, asked for by the brief.
;;; The support quantifies `r in RR' with the single guard `|r| < 1' -- so the
;;; statement covers the WHOLE open interval (-1, 1), negative r included, and
;;; the value is recip(1 - r) throughout.  The negative half is not a special
;;; case here and needs nothing extra: the only place the sign could matter is
;;; the null sequence r^k, and `rr-abs-power' (|r^k| = |r|^k, geometric-series.scm)
;;; reduces that to the nonnegative case verbatim -- which is why
;;; `power-tends-to-zero' below is stated at |r| < 1 and proved by one citation of
;;; `power-small-threshold' at |r|.  1 - r is positive for every r < 1, so
;;; recip(1 - r) denotes on the whole range and `geometric-partial-sum' (which
;;; asks only r /= 1) applies unchanged.
;;;
;;; ---------------------------------------------------------------------------
;;; BERNOULLI IS NOT THE CHEAPEST ROUTE to r^k -> 0, and the brief's plan (and
;;; geometric-series.scm's header, "Bernoulli, the Archimedean property, a
;;; squeeze, and a case split at r = 0") is worth amending on that point.
;;; `rr-bernoulli' bounds (1+x)^n BELOW; to get an upper bound on r^n out of it
;;; one must pass to 1/r, which costs a power-of-a-reciprocal lemma the tree does
;;; not have ((recip a)^n = recip(a^n)) and a case split at r = 0 to make 1/r
;;; denote.  The division-free inequality
;;;
;;;     k (1 - r) r^k  <=  1          (0 <= r <= 1, k in NN)
;;;
;;; is Bernoulli in disguise, is a direct induction on k, needs no reciprocal and
;;; no case split, and hands the Archimedean step its bound in one line.  Its
;;; step is
;;;
;;;     (k+1)(1-r) r^(k+1) = r . [k (1-r) r^k] + (1-r) . r^(k+1)
;;;                       <= r . 1             + (1-r) . 1        = 1,
;;;
;;; the two scalings being `rr-le-scale-nonneg' at r and at 1-r; the second wants
;;; r^(k+1) <= 1, which is `rr-power-le-one'.  No case split at r = 0 appears
;;; anywhere: the argument only ever uses 0 <= r and 0 <= 1-r.
;;;
;;; ---------------------------------------------------------------------------
;;; THE TELESCOPING HALF.  `summable-bound-implies-cauchy' needed one lemma and
;;; one citation.  The lemma is the CHAIN bound -- the triangle inequality run
;;; along f(m), f(m+1), ..., f(n) -- which the tree did not have in any form; it
;;; is an induction on the UPPER index n with everything else universally
;;; quantified inside, so `ni' fires on it directly.  Stating it against an
;;; arbitrary dominating sequence `rad' rather than against the
;;; consecutive-distance sequence is what makes it usable: the version with the
;;; distances themselves (`metric-chain-triangle') is then one instance, at
;;; rad := the lambda, closed by reflexivity of <=, and no termwise comparison of
;;; partial sums is needed anywhere.
;;;
;;; The citation is `series-cauchy-criterion' (theorem-library/series-cauchy-proof.scm,
;;; proven modulo 0), which turns SERIES-CONVERGES(rad) into exactly the
;;; |P(n) - P(m)| <= eps estimate for bnd <= m <= n_ that the chain bound wants.
;;; The warrant's route ("SERIES-CONVERGES says P converges in RR, hence P is
;;; Cauchy") names a convergent-implies-Cauchy step that does NOT exist for a
;;; general metric space in this tree; for the real line it is that criterion.
;;; The criterion is stated only for m <= n_, so the Cauchy goal's unordered pair
;;; is split by `rr-leq-total' and the second case goes through `metric-sym'.
;;;
;;; ---------------------------------------------------------------------------
;;; CITATIONS, with the 0-based load position of the installing file:
;;;   primitive / base theory: rr-leq-reflexive, rr-leq-total, rr-leq-mul-nonneg,
;;;     rr-mul-closed, rr-one-in, rr-zero-in, rr-subset-cc, rr-recip-inverse,
;;;     rr-recip-closed, nn-zero-in, nn-is-set, nn-succ-closed, power-zero,
;;;     power-succ.
;;;   definitional unfolds: is-cauchy-seq (44), series-converges-to (125),
;;;     pos-rr, `<'.
;;;   proven: eq-sym / neq-sym (equality-basics 148); fun-apply-type-c 162;
;;;     nn-le-succ-cases / nn-zero-le (nn-order-ord 164); nn-in-rr
;;;     (nn-order-basics 166); rr-order-basics 173 (rr-le-scale-nonneg,
;;;     rr-lt-scale-pos, rr-lt-implies-le); pos-rr-bridges 175
;;;     (rr-pos-rr-in-rr, rr-lt-of-pos-rr); rr-abs-basics 176 (rr-abs-closed,
;;;     rr-abs-nonneg, rr-abs-zero-value, rr-le-abs); rr-recip-order 180
;;;     (rr-mul-pos, rr-recip-pos); nn-unbounded-in-rr 194; metric-dist-real /
;;;     metric-triangle / metric-sym / metric-self-zero (op-typing 200 and
;;;     subtype-laws); nn-le-zero-is-zero (nn-order-proof 227);
;;;     comparison-test-proof 402 (series-partial-sum-in-rr,
;;;     series-partial-sum-succ); series-cauchy-proof 409
;;;     (series-cauchy-criterion); limit-arithmetic 415 (rr-limit-sub,
;;;     rr-null-scale); antiderivable-uniform-limit 488 (rr-converges-to-abs);
;;;     geometric-series 514 (rr-abs-power, geometric-partial-sum);
;;;     nn-succ-plus-one (nn-parity-proof).
;;;   oracles: ineq, crs, arith.  Every one of the nine results is `modulo 0'.
;;;
;;; LOAD WINDOW [515, end).
;;;   lo = 515: theorem-library/geometric-series (514) is the latest citation.
;;;   hi = end: neither retired support is cited by anything proven, so no citer
;;;     forces a ceiling.  The natural slot is immediately after
;;;     "theorem-library/rake-series" (516), before "preamble".
;;;
;;; `topic!' NOTE for the integrator: theorem-library/pss-topics.scm:221 and :225
;;; tag these two names as PSS entries and load AFTER this file; the tag is the
;;; same topic ('analysis) this file assigns, so nothing drifts, but the two
;;; lines belong with the retired supports.
;;;
;;; SUPPORTS TO RETIRE (the integrator's job, not this file's):
;;;   theorem-library/summable-cauchy.scm:23-37   summable-bound-implies-cauchy
;;;       (support :23-31, warrant! :32-37)
;;;   theorem-library/power-series.scm:214-222    geometric-series-converges-to
;;;       (support :214-217, warrant! :219-222; the one-line comment at :213 goes
;;;        with them)
;;; Both probe with `install-theorem!: ... already installed; re-installing the
;;; SAME statement', so neither statement moved.

;;; --- file-local helpers (r7r-) --------------------------------------------

;; right-nested AND tower from a list
(define (r7r-and lst)
  (if (null? (cdr lst)) (car lst) (list 'AND (car lst) (r7r-and (cdr lst)))))

;; 1-based context index of FORM, for `ineq'.  Named by FORMULA, never by shape.
(define (r7r-idx form)
  (let loop ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "r7r-idx: not in context" (expression->string form)))
          ((equal? (car l) form) i)
          (#t (loop (cdr l) (+ i 1))))))
(define (r7r-ineq . fs) (apply ineq (map r7r-idx fs)))

;; (IN (* a b) RR) by rr-mul-closed, whose antecedent is a CONJUNCTION and so is
;; not split by `fact'.  Idempotent: a repeat lands nothing (and `have!' errors
;; on a claim already in context).
(define (r7r-mul! a b)
  (let ((g (list 'AND (list 'IN a 'RR) (list 'IN b 'RR))))
    (if (not (dk-asm? g)) (have! g))
    (if (not (dk-asm? (list 'IN (list '* a b) 'RR))) (fact 'rr-mul-closed a b))))

;; c*x <= c*y from 0 <= c and x <= y (rr-le-scale-nonneg; the ORDER pair is one
;; conjunction, the three typings are separate antecedents)
(define (r7r-scale! c x y)
  (let ((g (list 'AND (list '<= 0 c) (list '<= x y))))
    (if (not (dk-asm? g)) (have! g))
    (fact 'rr-le-scale-nonneg c x y)))

;; the one leaf of LEAVES whose goal is a FORALL; ERRORS on a miss
(define (r7r-leaf-forall leaves)
  (or (find-first (lambda (l) (eq? (car (dk-goal-of l)) 'FORALL)) leaves)
      (error "r7r-leaf-forall: no FORALL-headed leaf")))

;; close every leaf of LEAVES that is not FORALL-headed by `ass', and focus the
;; FORALL one
(define (r7r-keep-forall! leaves)
  (for-each (lambda (l)
              (dk-focus! l)
              (if (not (eq? (car (dk-goal)) 'FORALL)) (ass)))
            leaves)
  (dk-focus! (r7r-leaf-forall leaves)))

;; (NOT (= t 0)) from (< 0 t) in context, on a SIDE branch: `mac-h' is
;; destructive and the main branch still wants the strict inequality.
(define (r7r-nonzero! t)
  (have! (list 'NOT (list '= t 0))
    (lambda ()
      (mac-h '< (list '< 0 t))
      (dk-split! (list 'AND (list '<= 0 t) (list 'NOT (list '= 0 t))))
      (fact 'neq-sym 0 t)
      (ass))))

;;; =====================================================================
;;; metric-chain-bound -- the triangle inequality along a finite chain.
;;;
;;;   m <= n,  d(f k, f (succ k)) <= rad(k) for every k
;;;     =>  d(f m, f n) <= P(n) - P(m),   P = SERIES-PARTIAL-SUM(rad, -)
;;;
;;; Induction on the UPPER index, which is therefore outermost.
;;; =====================================================================

(define r7r-cb-hyps
  '((IS-METRIC-SPACE s)
    (IN f (FUN NN (PTS s)))
    (IN rad (FUN NN RR))
    (FORALL k (IMPLIES (IN k NN) (<= ((DIST s) (f k) (f (succ k))) (rad k))))
    (IN m NN)))

(define (r7r-cb-stmt up)
  (list 'FORALL 's (list 'FORALL 'f (list 'FORALL 'rad (list 'FORALL 'm
    (list 'IMPLIES (r7r-and (append r7r-cb-hyps (list (list '<= 'm up))))
      (list '<= (list (list 'DIST 's) '(f m) (list 'f up))
            (list '- (list 'SERIES-PARTIAL-SUM 'rad up)
                  '(SERIES-PARTIAL-SUM rad m)))))))))

(sp (make-wff (list 'FORALL 'n_ (list 'IMPLIES '(IN n_ NN) (r7r-cb-stmt 'n_)))))
(define r7r-cb-br (use-induction))

;;; ---- BASE: n_ = 0, so m = 0 and both sides are 0. --------------------
(dk-focus! (cdr (assq 'base r7r-cb-br)))
(dk-split-all! (dk-peel!))
(fact 'nn-le-zero-is-zero 'm)
(subst '(= m 0))
(fact 'nn-zero-in)
(fact 'fun-apply-type-c 'f 'NN '(PTS s) 0)
(fact 'metric-self-zero 's '(f 0))
(subst '(= ((DIST s) (f 0) (f 0)) 0))
(fact 'series-partial-sum-in-rr 0 'rad)
(ineq)

;;; ---- STEP ------------------------------------------------------------
(dk-focus! (cdr (assq 'step r7r-cb-br)))
(define r7r-cb-n  (cdr (assq 'var r7r-cb-br)))
(define r7r-cb-ih (cdr (assq 'ih  r7r-cb-br)))
(dk-split-all! (dk-peel!))

;; the two points of the chain that are always in play
(fact 'nn-succ-closed r7r-cb-n)
(fact 'fun-apply-type-c 'f 'NN '(PTS s) 'm)
(fact 'fun-apply-type-c 'f 'NN '(PTS s) r7r-cb-n)
(fact 'fun-apply-type-c 'f 'NN '(PTS s) (list 'succ r7r-cb-n))

(fact 'nn-le-succ-cases r7r-cb-n 'm)
(use-cases (list (list '<= 'm r7r-cb-n) (list '= 'm (list 'succ r7r-cb-n)))

  ;; CASE m <= n: triangle through f(n), then the induction hypothesis.
  ;;
  ;; The consecutive-distance bound is instantiated FIRST, and is named by the
  ;; literal formula rather than found by shape.  Once the IH has been applied
  ;; the context holds its whole instantiation chain, and every partly-peeled
  ;; link of that chain is a FORALL mentioning both DIST and rad -- so a
  ;; shape-based finder picks `forall([m], ...)' off the chain, instantiates it
  ;; at n_, and `detach!' then reports an antecedent that is not in context.
  (lambda ()
    (dk-apply! (list-ref r7r-cb-hyps 3) r7r-cb-n)
    (have! (r7r-and (append r7r-cb-hyps (list (list '<= 'm r7r-cb-n)))))
    (dk-apply! r7r-cb-ih 's 'f 'rad 'm)
    (fact 'metric-triangle 's '(f m) (list 'f r7r-cb-n) (list 'f (list 'succ r7r-cb-n)))
    ;; the recurrence, written out: `dk-sps-succ!' lands its two typing
    ;; prerequisites under `quietly', so a miss there is silent and the `subst'
    ;; that follows reports only "equality not in context".
    (fact 'series-partial-sum-in-rr r7r-cb-n 'rad)
    (fact 'fun-apply-type-c 'rad 'NN 'RR r7r-cb-n)
    (fact 'series-partial-sum-succ 'rad r7r-cb-n)
    (subst (list '== (list 'SERIES-PARTIAL-SUM 'rad (list 'succ r7r-cb-n))
                 (list '+ (list 'SERIES-PARTIAL-SUM 'rad r7r-cb-n)
                       (list 'rad r7r-cb-n))))
    (fact 'metric-dist-real 's '(f m) (list 'f (list 'succ r7r-cb-n)))
    (fact 'metric-dist-real 's '(f m) (list 'f r7r-cb-n))
    (fact 'metric-dist-real 's (list 'f r7r-cb-n) (list 'f (list 'succ r7r-cb-n)))
    (fact 'series-partial-sum-in-rr 'm 'rad)
    (r7r-ineq
     (list '<= (list (list 'DIST 's) '(f m) (list 'f (list 'succ r7r-cb-n)))
           (list '+ (list (list 'DIST 's) '(f m) (list 'f r7r-cb-n))
                 (list (list 'DIST 's) (list 'f r7r-cb-n) (list 'f (list 'succ r7r-cb-n)))))
     (list '<= (list (list 'DIST 's) (list 'f r7r-cb-n) (list 'f (list 'succ r7r-cb-n)))
           (list 'rad r7r-cb-n))
     (list '<= (list (list 'DIST 's) '(f m) (list 'f r7r-cb-n))
           (list '- (list 'SERIES-PARTIAL-SUM 'rad r7r-cb-n)
                 '(SERIES-PARTIAL-SUM rad m)))))

  ;; CASE m = succ n: the two points coincide and both sides are 0.
  (lambda ()
    (subst (list '= 'm (list 'succ r7r-cb-n)))
    (fact 'metric-self-zero 's (list 'f (list 'succ r7r-cb-n)))
    (subst (list '= (list (list 'DIST 's) (list 'f (list 'succ r7r-cb-n))
                          (list 'f (list 'succ r7r-cb-n))) 0))
    (fact 'series-partial-sum-in-rr (list 'succ r7r-cb-n) 'rad)
    (ineq)))

(qed 'metric-chain-bound)
(topic! 'metric-chain-bound 'analysis)
(alias! 'metric-chain-bound
        "the triangle inequality along a chain, against a dominating series")

;;; =====================================================================
;;; metric-chain-triangle -- the same bound against the consecutive-distance
;;; sequence itself, i.e. literally
;;;
;;;   d(f m, f n) <= sum_{k=m}^{n-1} d(f k, f (succ k)).
;;;
;;; One instance of metric-chain-bound, at rad := the lambda; the termwise
;;; hypothesis is then reflexivity of <=.
;;; =====================================================================

(define r7r-dlam '(VNB-LAMBDA k NN ((DIST s) (f k) (f (succ k)))))

(sp (make-wff
     (list 'FORALL 's (list 'FORALL 'f
       (list 'IMPLIES '(AND (IS-METRIC-SPACE s) (IN f (FUN NN (PTS s))))
         (list 'FORALL 'm (list 'IMPLIES '(IN m NN)
           (list 'FORALL 'n_ (list 'IMPLIES '(IN n_ NN)
             (list 'IMPLIES '(<= m n_)
               (list '<= '((DIST s) (f m) (f n_))
                     (list '- (list 'SERIES-PARTIAL-SUM r7r-dlam 'n_)
                           (list 'SERIES-PARTIAL-SUM r7r-dlam 'm)))))))))))))
(dk-split-all! (dk-peel!))

;; the consecutive-distance sequence is a real sequence
(have! (list 'IN r7r-dlam '(FUN NN RR))
  (lambda ()
    (dk-lam-t!)
    (let ((v (dk-di-var!)))
      (fact 'nn-succ-closed v)
      (fact 'fun-apply-type-c 'f 'NN '(PTS s) v)
      (fact 'fun-apply-type-c 'f 'NN '(PTS s) (list 'succ v))
      (fact 'metric-dist-real 's (list 'f v) (list 'f (list 'succ v)))
      (ass))))

;; ... and it dominates itself
(define r7r-ct-bound
  (list 'FORALL 'k (list 'IMPLIES '(IN k NN)
    (list '<= '((DIST s) (f k) (f (succ k))) (list r7r-dlam 'k)))))
(have! r7r-ct-bound
  (lambda ()
    (di)
    (fact 'nn-succ-closed 'k)
    (fact 'fun-apply-type-c 'f 'NN '(PTS s) 'k)
    (fact 'fun-apply-type-c 'f 'NN '(PTS s) '(succ k))
    (fact 'metric-dist-real 's '(f k) '(f (succ k)))
    (lam-b)
    (fact 'rr-leq-reflexive '((DIST s) (f k) (f (succ k))))
    (ass)))

(have! (r7r-and (list '(IS-METRIC-SPACE s)
                      '(IN f (FUN NN (PTS s)))
                      (list 'IN r7r-dlam '(FUN NN RR))
                      r7r-ct-bound
                      '(IN m NN)
                      '(<= m n_))))
(fact 'metric-chain-bound 'n_ 's 'f r7r-dlam 'm)
(ass)
(qed 'metric-chain-triangle)
(topic! 'metric-chain-triangle 'analysis)
(alias! 'metric-chain-triangle
        "the triangle inequality along a chain of consecutive points")

;;; =====================================================================
;;; summable-bound-implies-cauchy -- the statement VERBATIM from the support
;;; at theorem-library/summable-cauchy.scm:23.
;;; =====================================================================

(define r7r-sc-kbound
  '(FORALL k (IMPLIES (IN k NN) (<= ((DIST s) (f k) (f (succ k))) (rad k)))))

(sp (make-wff
     '(FORALL s (FORALL f (FORALL rad
        (IMPLIES (AND (IS-METRIC-SPACE s)
                 (AND (IN f (FUN NN (PTS s)))
                 (AND (IN rad (FUN NN RR))
                 (AND (SERIES-CONVERGES rad)
                      (FORALL k (IMPLIES (IN k NN)
                        (<= ((DIST s) (f k) (f (succ k))) (rad k))))))))
          (IS-CAUCHY-SEQ s f)))))))
(dk-split-all! (dk-peel!))
(mac 'is-cauchy-seq)

;;; three obligations; the first two are in the context already.
(define r7r-sc-leaves '())
(let r7r-sc-walk ()
  (let ((g (dk-goal)))
    (if (and (pair? g) (eq? (car g) 'AND))
        (for-each (lambda (l) (dk-focus! l) (r7r-sc-walk))
                  (dk-opened (lambda () (di))))
        (set! r7r-sc-leaves (cons (proof-state-focus *ps*) r7r-sc-leaves)))))
(r7r-keep-forall! r7r-sc-leaves)

;;; the estimate.
(dk-split-all! (dk-peel!))
(fact 'rr-pos-rr-in-rr 'eps)
(define r7r-sc-crit (dk-fact! 'series-cauchy-criterion 'rad 'eps))
(define r7r-sc-bnd (dk-skolem! r7r-sc-crit))
;; Name the estimate by CONTENT, and exclude the partly-peeled links of the
;; citation chain, every one of which is also a FORALL mentioning `abs'.
(define r7r-sc-est
  (dk-pick (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                            (dk-contains? a 'abs)
                            (not (dk-contains? a 'POS-RR))
                            (not (dk-contains? a 'SERIES-CONVERGES))))
           "the Cauchy estimate for rad at eps"))
(ew r7r-sc-bnd)
(r7r-keep-forall! (dk-opened (lambda () (di))))

(dk-split-all! (dk-peel!))
(define r7r-sc-dist (cadr (dk-goal)))                  ; ((DIST s) (f m) (f n_))
(define r7r-sc-m (cadr (cadr r7r-sc-dist)))
(define r7r-sc-n (cadr (caddr r7r-sc-dist)))

;;; ONE ordered case: goal (<= ((DIST s) (f LO) (f HI)) eps) with LO <= HI and
;;; bnd <= LO in context.  The chain bound gives d <= P(HI) - P(LO); the Cauchy
;;; estimate bounds |P(HI) - P(LO)| by eps; `rr-le-abs' joins them.
(define (r7r-sc-case! lo hi)
  (let ((phi (list 'SERIES-PARTIAL-SUM 'rad hi))
        (plo (list 'SERIES-PARTIAL-SUM 'rad lo)))
    (have! (r7r-and (list '(IS-METRIC-SPACE s)
                          '(IN f (FUN NN (PTS s)))
                          '(IN rad (FUN NN RR))
                          r7r-sc-kbound
                          (list 'IN lo 'NN)
                          (list '<= lo hi))))
    (fact 'metric-chain-bound hi 's 'f 'rad lo)
    (have! (list 'AND (list '<= r7r-sc-bnd lo) (list '<= lo hi)))
    (dk-apply! r7r-sc-est lo hi)
    (fact 'series-partial-sum-in-rr hi 'rad)
    (fact 'series-partial-sum-in-rr lo 'rad)
    (fact 'rr-sub-in-rr phi plo)
    (fact 'rr-le-abs (list '- phi plo))
    (fact 'rr-abs-closed (list '- phi plo))
    (fact 'fun-apply-type-c 'f 'NN '(PTS s) lo)
    (fact 'fun-apply-type-c 'f 'NN '(PTS s) hi)
    (fact 'metric-dist-real 's (list 'f lo) (list 'f hi))
    (r7r-ineq (list '<= (list (list 'DIST 's) (list 'f lo) (list 'f hi))
                    (list '- phi plo))
              (list '<= (list '- phi plo) (list 'abs (list '- phi plo)))
              (list '<= (list 'abs (list '- phi plo)) 'eps))))

(fact 'nn-in-rr r7r-sc-m)
(fact 'nn-in-rr r7r-sc-n)
;; rr-leq-total's antecedent is a CONJUNCTION, which `fact' will not split: the
;; citation without this `have!' lands the implication and the `use-cases' below
;; then has no disjunction to establish.
(have! (list 'AND (list 'IN r7r-sc-m 'RR) (list 'IN r7r-sc-n 'RR)))
(fact 'rr-leq-total r7r-sc-m r7r-sc-n)
(use-cases (list (list '<= r7r-sc-m r7r-sc-n) (list '<= r7r-sc-n r7r-sc-m))
  (lambda () (r7r-sc-case! r7r-sc-m r7r-sc-n))
  (lambda ()
    (fact 'fun-apply-type-c 'f 'NN '(PTS s) r7r-sc-m)
    (fact 'fun-apply-type-c 'f 'NN '(PTS s) r7r-sc-n)
    (fact 'metric-sym 's (list 'f r7r-sc-m) (list 'f r7r-sc-n))
    (subst (list '= (list (list 'DIST 's) (list 'f r7r-sc-m) (list 'f r7r-sc-n))
                 (list (list 'DIST 's) (list 'f r7r-sc-n) (list 'f r7r-sc-m))))
    (r7r-sc-case! r7r-sc-n r7r-sc-m)))

(qed 'summable-bound-implies-cauchy)
(topic! 'summable-bound-implies-cauchy 'analysis)

;;; =====================================================================
;;; rr-power-le-one -- 0 <= r <= 1  =>  r^k <= 1.  Induction on k.
;;; =====================================================================

(sp (make-wff '(FORALL k (IMPLIES (IN k NN)
   (FORALL r (IMPLIES (IN r RR)
     (IMPLIES (AND (<= 0 r) (<= r 1)) (<= (power r k) 1))))))))
(define r7r-plo-br (use-induction))

(dk-focus! (cdr (assq 'base r7r-plo-br)))
(dk-peel!)
(fact 'rr-subset-cc 'r)
(mac 'power-zero)
(arith)

(dk-focus! (cdr (assq 'step r7r-plo-br)))
(define r7r-plo-n  (cdr (assq 'var r7r-plo-br)))
(define r7r-plo-ih (cdr (assq 'ih  r7r-plo-br)))
(dk-peel!)
;; the IH is detached against the CONJUNCTION, so it goes before the split
(dk-apply! r7r-plo-ih 'r)
(dk-split! '(AND (<= 0 r) (<= r 1)))
(fact 'rr-one-in)
(fact 'rr-subset-cc 'r)
(fact 'power-real-closed 'r r7r-plo-n)
(mac 'power-succ)
(r7r-scale! 'r (list 'power 'r r7r-plo-n) 1)
(r7r-mul! 'r (list 'power 'r r7r-plo-n))
(r7r-mul! 'r 1)
(r7r-ineq (list '<= (list '* 'r (list 'power 'r r7r-plo-n)) '(* r 1))
          '(<= r 1))
(qed 'rr-power-le-one)
(topic! 'rr-power-le-one 'inequalities)
(alias! 'rr-power-le-one "a power of a real in [0,1] is at most 1")

;;; =====================================================================
;;; rr-power-shrink-bound -- k (1 - r) r^k <= 1 for 0 <= r <= 1.
;;;
;;; Bernoulli in division-free form; see the header.  Induction on k, the step
;;; being the identity
;;;   (k+1)(1-r) . (r . r^k) = r . [k (1-r) r^k]  +  (1-r) . (r . r^k)
;;; and two scalings.
;;; =====================================================================

(sp (make-wff '(FORALL k (IMPLIES (IN k NN)
   (FORALL r (IMPLIES (IN r RR)
     (IMPLIES (AND (<= 0 r) (<= r 1))
       (<= (* (* k (- 1 r)) (power r k)) 1))))))))
(define r7r-psb-br (use-induction))

(dk-focus! (cdr (assq 'base r7r-psb-br)))
(dk-peel!)
(fact 'rr-subset-cc 'r)
(mac 'power-zero)
(have! '(= (* (* 0 (- 1 r)) 1) 0) (lambda () (crs)))
(subst '(= (* (* 0 (- 1 r)) 1) 0))
(arith)

(dk-focus! (cdr (assq 'step r7r-psb-br)))
(define r7r-psb-n  (cdr (assq 'var r7r-psb-br)))
(define r7r-psb-ih (cdr (assq 'ih  r7r-psb-br)))
(define r7r-psb-p  (list 'power 'r r7r-psb-n))
(define r7r-psb-b  (list '* (list '* r7r-psb-n '(- 1 r)) r7r-psb-p))
(define r7r-psb-c  (list '* 'r r7r-psb-p))
(dk-peel!)
(dk-apply! r7r-psb-ih 'r)
(dk-split! '(AND (<= 0 r) (<= r 1)))
(fact 'rr-one-in)
(fact 'rr-subset-cc 'r)
(fact 'nn-in-rr r7r-psb-n)
(fact 'power-real-closed 'r r7r-psb-n)
(fact 'rr-sub-in-rr 1 'r)
(mac 'power-succ)
(fact 'nn-succ-plus-one r7r-psb-n)
(subst (list '= (list 'succ r7r-psb-n) (list '+ r7r-psb-n 1)))

;; C = r . r^k is itself at most 1.  (The AND was consumed by the split above,
;; and rr-power-le-one's antecedent is that conjunction.)
(have! '(AND (<= 0 r) (<= r 1)))
(fact 'rr-power-le-one r7r-psb-n 'r)
(r7r-scale! 'r r7r-psb-p 1)
(r7r-mul! 'r r7r-psb-p)
(r7r-mul! 'r 1)
(have! (list '<= r7r-psb-c 1)
  (lambda () (r7r-ineq (list '<= r7r-psb-c '(* r 1)) '(<= r 1))))

;; the two scalings
(r7r-mul! r7r-psb-n '(- 1 r))
(r7r-mul! (list '* r7r-psb-n '(- 1 r)) r7r-psb-p)
(r7r-scale! 'r r7r-psb-b 1)
(r7r-mul! 'r r7r-psb-b)
(have! '(<= 0 (- 1 r)) (lambda () (r7r-ineq '(<= r 1))))
(r7r-scale! '(- 1 r) r7r-psb-c 1)
(r7r-mul! '(- 1 r) r7r-psb-c)
(r7r-mul! '(- 1 r) 1)

;; ... and the identity that puts the goal in their shape
(have! (list '= (list '* (list '* (list '+ r7r-psb-n 1) '(- 1 r)) r7r-psb-c)
             (list '+ (list '* 'r r7r-psb-b) (list '* '(- 1 r) r7r-psb-c)))
  (lambda () (crs)))
(subst (list '= (list '* (list '* (list '+ r7r-psb-n 1) '(- 1 r)) r7r-psb-c)
             (list '+ (list '* 'r r7r-psb-b) (list '* '(- 1 r) r7r-psb-c))))
(r7r-ineq (list '<= (list '* 'r r7r-psb-b) '(* r 1))
          (list '<= (list '* '(- 1 r) r7r-psb-c) '(* (- 1 r) 1)))
(qed 'rr-power-shrink-bound)
(topic! 'rr-power-shrink-bound 'inequalities)
(alias! 'rr-power-shrink-bound "Bernoulli's inequality, division-free")

;;; =====================================================================
;;; power-small-threshold -- the Archimedean step.  For 0 <= r < 1 and eps > 0
;;; there is a natural cap with r^k <= eps for every k >= cap.
;;;
;;; From k(1-r) r^k <= 1 and a cap with 1 < (1-r).eps.cap: for k >= cap,
;;; (k(1-r)).eps <= (k(1-r)).r^k would force (1-r).eps.k <= 1 < (1-r).eps.cap
;;; <= (1-r).eps.k.  So the alternative r^k <= eps is the only one left, and the
;;; cancellation is done by Farkas on an infeasible system rather than by a
;;; cancellation lemma the tree does not have.
;;; =====================================================================

(define r7r-pst-u '(* (- 1 r) eps))

(sp (make-wff
     '(FORALL r (IMPLIES (IN r RR)
        (IMPLIES (AND (<= 0 r) (< r 1))
          (FORALL eps (IMPLIES (POS-RR eps)
            (FORSOME cap (AND (IN cap NN)
              (FORALL k (IMPLIES (IN k NN)
                (IMPLIES (<= cap k) (<= (power r k) eps)))))))))))))
(dk-split-all! (dk-peel!))
(fact 'rr-pos-rr-in-rr 'eps)
(fact 'rr-lt-of-pos-rr 'eps)
(fact 'rr-one-in)
(fact 'rr-sub-in-rr 1 'r)
(have! '(< 0 (- 1 r)) (lambda () (r7r-ineq '(< r 1))))
(fact 'rr-mul-pos '(- 1 r) 'eps)
(r7r-mul! '(- 1 r) 'eps)
(r7r-nonzero! r7r-pst-u)
(have! (list 'AND (list 'IN r7r-pst-u 'RR) (list 'NOT (list '= r7r-pst-u 0))))
(fact 'rr-recip-closed r7r-pst-u)
(fact 'rr-recip-pos r7r-pst-u)
(fact 'rr-recip-inverse r7r-pst-u)
(r7r-mul! r7r-pst-u (list 'recip r7r-pst-u))

(define r7r-pst-cap
  (dk-skolem! (dk-fact! 'nn-unbounded-in-rr (list 'recip r7r-pst-u))))
(fact 'nn-in-rr r7r-pst-cap)
(have! (list 'AND (list '< 0 r7r-pst-u)
             (list '< (list 'recip r7r-pst-u) r7r-pst-cap)))
(fact 'rr-lt-scale-pos r7r-pst-u (list 'recip r7r-pst-u) r7r-pst-cap)
(r7r-mul! r7r-pst-u r7r-pst-cap)
(have! (list '< 1 (list '* r7r-pst-u r7r-pst-cap))
  (lambda () (r7r-ineq (list '< (list '* r7r-pst-u (list 'recip r7r-pst-u))
                             (list '* r7r-pst-u r7r-pst-cap))
                       (list '= (list '* r7r-pst-u (list 'recip r7r-pst-u)) 1))))

(ew r7r-pst-cap)
(r7r-keep-forall! (dk-opened (lambda () (di))))
(dk-split-all! (dk-peel!))

(define r7r-pst-w '(* k (- 1 r)))
(define r7r-pst-p '(power r k))
(fact 'nn-in-rr 'k)
(fact 'nn-zero-le 'k)
(fact 'power-real-closed 'r 'k)
(fact 'rr-lt-implies-le 'r 1)
(fact 'rr-lt-implies-le 0 '(- 1 r))
(fact 'rr-lt-implies-le 0 r7r-pst-u)
(have! '(AND (<= 0 r) (<= r 1)))
(fact 'rr-power-shrink-bound 'k 'r)

;; cap <= k scales the threshold up
(r7r-scale! r7r-pst-u r7r-pst-cap 'k)
(r7r-mul! r7r-pst-u 'k)

;; w = k(1-r) is nonnegative
(have! (list 'AND (list 'IN 'k 'RR) '(IN (- 1 r) RR)))
(have! '(AND (<= 0 k) (<= 0 (- 1 r))))
(fact 'rr-leq-mul-nonneg 'k '(- 1 r))
(r7r-mul! 'k '(- 1 r))
(r7r-mul! r7r-pst-w r7r-pst-p)
(r7r-mul! r7r-pst-w 'eps)
(have! (list '= (list '* r7r-pst-w 'eps) (list '* r7r-pst-u 'k))
  (lambda () (crs)))

(have! (list 'AND (list 'IN r7r-pst-p 'RR) '(IN eps RR)))
(fact 'rr-leq-total r7r-pst-p 'eps)
(use-cases (list (list '<= r7r-pst-p 'eps) (list '<= 'eps r7r-pst-p))
  (lambda () (ass))
  (lambda ()
    (r7r-scale! r7r-pst-w 'eps r7r-pst-p)
    (r7r-ineq (list '<= (list '* r7r-pst-w 'eps) (list '* r7r-pst-w r7r-pst-p))
              (list '<= (list '* r7r-pst-w r7r-pst-p) 1)
              (list '= (list '* r7r-pst-w 'eps) (list '* r7r-pst-u 'k))
              (list '<= (list '* r7r-pst-u r7r-pst-cap) (list '* r7r-pst-u 'k))
              (list '< 1 (list '* r7r-pst-u r7r-pst-cap)))))

(qed 'power-small-threshold)
(topic! 'power-small-threshold 'analysis)
(alias! 'power-small-threshold "the powers of a real in [0,1) fall below any positive bound")

;;; =====================================================================
;;; power-tends-to-zero -- |r| < 1  =>  r^k -> 0 in RR-MS.
;;;
;;; `rr-converges-to-abs' (antiderivable-uniform-limit.scm) is the eps/N
;;; criterion with the CONVERGES-TO boilerplate already discharged, so the whole
;;; proof is: type the lambda, and produce the threshold -- which is
;;; power-small-threshold at |r|, transported by rr-abs-power.
;;; =====================================================================

(define r7r-ptz-lam '(VNB-LAMBDA n NN (power r n)))

(sp (make-wff
     (list 'FORALL 'r (list 'IMPLIES '(AND (IN r RR) (< (abs r) 1))
       (list 'CONVERGES-TO 'RR-MS r7r-ptz-lam 0)))))
(dk-split-all! (dk-peel!))
(fact 'rr-abs-closed 'r)
(fact 'rr-abs-nonneg 'r)
(fact 'rr-zero-in)
(have! (list 'IN r7r-ptz-lam '(FUN NN RR))
  (lambda ()
    (dk-lam-t!)
    (let ((v (dk-di-var!)))
      (fact 'power-real-closed 'r v)
      (ass))))
(define r7r-ptz-imp (dk-fact! 'rr-converges-to-abs r7r-ptz-lam 0))
(have! (cadr r7r-ptz-imp)
  (lambda ()
    (dk-peel!)
    (fact 'rr-pos-rr-in-rr 'eps)
    (have! '(AND (<= 0 (abs r)) (< (abs r) 1)))
    (define r7r-ptz-cap
      (dk-skolem! (dk-fact! 'power-small-threshold '(abs r) 'eps)))
    (define r7r-ptz-thr
      (dk-pick (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                                (dk-contains? a 'power)
                                (not (dk-contains? a 'POS-RR))))
               "the threshold estimate at |r|"))
    (ew r7r-ptz-cap)
    (r7r-keep-forall! (dk-opened (lambda () (di))))
    (dk-split-all! (dk-peel!))
    (let ((kk (cadr (dk-pick (lambda (a) (and (pair? a) (eq? (car a) 'IN)
                                              (eq? (caddr a) 'NN)
                                              (not (eq? (cadr a) r7r-ptz-cap))))
                             "the running index"))))
      (lam-b)
      (fact 'power-real-closed 'r kk)
      (have! (list '= (list '- (list 'power 'r kk) 0) (list 'power 'r kk))
        (lambda () (crs)))
      (subst (list '= (list '- (list 'power 'r kk) 0) (list 'power 'r kk)))
      (fact 'rr-abs-power kk 'r)
      (subst (list '= (list 'abs (list 'power 'r kk))
                   (list 'power '(abs r) kk)))
      (dk-apply! r7r-ptz-thr kk)
      (ass))))
(dk-apply! r7r-ptz-imp)
(ass)
(qed 'power-tends-to-zero)
(topic! 'power-tends-to-zero 'analysis)
(alias! 'power-tends-to-zero "the powers of a real of modulus below 1 converge to 0")

;;; =====================================================================
;;; rr-const-converges-to -- the constant sequence converges to its value.
;;; =====================================================================

(define r7r-cc-lam '(VNB-LAMBDA n NN c))

(sp (make-wff
     (list 'FORALL 'c (list 'IMPLIES '(IN c RR)
       (list 'CONVERGES-TO 'RR-MS r7r-cc-lam 'c)))))
(dk-peel!)
(have! (list 'IN r7r-cc-lam '(FUN NN RR))
  (lambda () (dk-lam-t!) (dk-di-var!) (ass)))
(define r7r-cc-imp (dk-fact! 'rr-converges-to-abs r7r-cc-lam 'c))
(have! (cadr r7r-cc-imp)
  (lambda ()
    (dk-peel!)
    (fact 'rr-lt-of-pos-rr 'eps)
    (fact 'rr-pos-rr-in-rr 'eps)
    (fact 'nn-zero-in)
    (ew 0)
    (r7r-keep-forall! (dk-opened (lambda () (di))))
    (dk-split-all! (dk-peel!))
    (lam-b)
    (have! '(= (- c c) 0) (lambda () (crs)))
    (subst '(= (- c c) 0))
    (fact 'rr-abs-zero-value)
    (subst '(= (abs 0) 0))
    (r7r-ineq '(< 0 eps))))
(dk-apply! r7r-cc-imp)
(ass)
(qed 'rr-const-converges-to)
(topic! 'rr-const-converges-to 'analysis)
(alias! 'rr-const-converges-to "a constant real sequence converges to its value")

;;; =====================================================================
;;; geometric-series-converges-to -- the statement VERBATIM from the support at
;;; theorem-library/power-series.scm:214.
;;;
;;;   S_k = (1 - r^k)/(1-r) = c - c.r^k  with c = 1/(1-r),
;;; so the partial-sum sequence is the constant c minus the null sequence c.r^k;
;;; rr-limit-sub does the rest.  The two ring identities below are stated with
;;; the coefficient QUANTIFIED and instantiated at c afterwards: `crs' declines
;;; any identity containing a `recip', and c is one.
;;; =====================================================================

;; beta-reduce every redex the goal still carries (arguments typed above)
(define (r7r-beta!)
  (let loop ((fuel 6))
    (let ((before (dk-goal)))
      (quietly (lambda () (lam-b)))
      (if (or (= fuel 0) (equal? (dk-goal) before)) #t (loop (- fuel 1))))))

(define r7r-gs-lam '(VNB-LAMBDA n NN (power r n)))
(define r7r-gs-c   '(recip (- 1 r)))
(define r7r-gs-clam (list 'VNB-LAMBDA 'n 'NN r7r-gs-c))
(define r7r-gs-glam (list 'VNB-LAMBDA 'n 'NN (list '* r7r-gs-c '(power r n))))
(define r7r-gs-slam (list 'VNB-LAMBDA 'k 'NN (list 'SERIES-PARTIAL-SUM r7r-gs-lam 'k)))

(sp (make-wff
     '(FORALL r
        (IMPLIES (AND (IN r RR) (< (abs r) 1))
          (SERIES-CONVERGES-TO (VNB-LAMBDA n NN (power r n)) (recip (- 1 r)))))))
(dk-split-all! (dk-peel!))

;; r < 1, and 1 - r is a positive real with a positive reciprocal
(fact 'rr-abs-closed 'r)
(fact 'rr-le-abs 'r)
(fact 'rr-one-in)
(have! '(< r 1) (lambda () (r7r-ineq '(< (abs r) 1) '(<= r (abs r)))))
(fact 'rr-sub-in-rr 1 'r)
(have! '(< 0 (- 1 r)) (lambda () (r7r-ineq '(< r 1))))
(r7r-nonzero! '(- 1 r))
(have! '(AND (IN (- 1 r) RR) (NOT (= (- 1 r) 0))))
(fact 'rr-recip-closed '(- 1 r))
(fact 'rr-recip-pos '(- 1 r))
(fact 'rr-lt-implies-le 0 r7r-gs-c)
(have! '(NOT (= r 1))
  (lambda ()
    (mac-h '< '(< r 1))
    (dk-split! '(AND (<= r 1) (NOT (= r 1))))
    (ass)))
(have! '(AND (IN r RR) (NOT (= r 1))))

;; the two ring identities, with the coefficient quantified
(define r7r-gs-distrib
  '(FORALL cv (IMPLIES (IN cv RR)
     (FORALL xv (IMPLIES (IN xv RR)
       (= (* (- 1 xv) cv) (- cv (* cv xv))))))))
(have! r7r-gs-distrib (lambda () (dk-peel!) (crs)))
(define r7r-gs-subzero
  '(FORALL av (IMPLIES (IN av RR) (= (- av 0) av))))
(have! r7r-gs-subzero (lambda () (dk-peel!) (crs)))

;; the four sequences, typed
(have! (list 'IN r7r-gs-lam '(FUN NN RR))
  (lambda () (dk-lam-t!)
             (let ((v (dk-di-var!))) (fact 'power-real-closed 'r v) (ass))))
(have! (list 'IN r7r-gs-clam '(FUN NN RR))
  (lambda () (dk-lam-t!) (dk-di-var!) (ass)))
(have! (list 'IN r7r-gs-glam '(FUN NN RR))
  (lambda () (dk-lam-t!)
             (let ((v (dk-di-var!)))
               (fact 'power-real-closed 'r v)
               (r7r-mul! r7r-gs-c (list 'power 'r v))
               (ass))))
(have! (list 'IN r7r-gs-slam '(FUN NN RR))
  (lambda () (dk-lam-t!)
             (let ((v (dk-di-var!)))
               (fact 'series-partial-sum-in-rr v r7r-gs-lam)
               (ass))))

;; r^k -> 0, hence c.r^k -> 0
(have! '(AND (IN r RR) (< (abs r) 1)))
(fact 'power-tends-to-zero 'r)
(define r7r-gs-pw1
  (list 'FORALL 'j_ (list 'IMPLIES '(IN j_ NN)
    (list '= (list r7r-gs-glam 'j_) (list '* r7r-gs-c (list r7r-gs-lam 'j_))))))
(have! r7r-gs-pw1
  (lambda ()
    (di)
    (fact 'power-real-closed 'r 'j_)
    (r7r-mul! r7r-gs-c '(power r j_))
    (r7r-beta!)
    (rfl)))
(fact 'rr-null-scale r7r-gs-c r7r-gs-lam r7r-gs-glam)

;; the constant sequence converges to c
(fact 'rr-const-converges-to r7r-gs-c)

;; the partial sums are the difference of the two
(define r7r-gs-pw2
  (list 'FORALL 'j_ (list 'IMPLIES '(IN j_ NN)
    (list '= (list r7r-gs-slam 'j_)
          (list '- (list r7r-gs-clam 'j_) (list r7r-gs-glam 'j_))))))
(have! r7r-gs-pw2
  (lambda ()
    (di)
    (fact 'power-real-closed 'r 'j_)
    (fact 'series-partial-sum-in-rr 'j_ r7r-gs-lam)
    (r7r-beta!)
    (fact 'geometric-partial-sum 'r 'j_)
    (subst (list '= (list 'SERIES-PARTIAL-SUM r7r-gs-lam 'j_)
                 (list '* '(- 1 (power r j_)) r7r-gs-c)))
    (dk-apply! r7r-gs-distrib r7r-gs-c '(power r j_))
    (ass)))
(fact 'rr-limit-sub r7r-gs-clam r7r-gs-glam r7r-gs-slam r7r-gs-c 0)

;; ... and the limit c - 0 is c
(mac 'series-converges-to)
(dk-apply! r7r-gs-subzero r7r-gs-c)
(fact 'eq-sym (list '- r7r-gs-c 0) r7r-gs-c)
(subst (list '= r7r-gs-c (list '- r7r-gs-c 0)))
(ass)
(qed 'geometric-series-converges-to)
(topic! 'geometric-series-converges-to 'analysis)
