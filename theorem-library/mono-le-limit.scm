;;; mono-le-limit.scm -- A TERM OF A NONDECREASING CONVERGENT SEQUENCE IS AT
;;; MOST ITS LIMIT, and the corollary the product metric's zero law needs.
;;;
;;;   rr-mono-le-limit       f in FUN(NN,RR), f(k) <= f(succ k) for every k,
;;;                          CONVERGES-TO(RR-MS, f, L)   =>   f(m) <= L
;;;   series-nonneg-zero-sum a nonnegative series whose sum is 0 has every
;;;                          term 0
;;;
;;; WHY THE TREE DID NOT HAVE IT, AND WHY IT MATTERS.  This is the rung the
;;; retired warrant of `comparison-test' named and then did not use -- the
;;; comment above `comparison-test' in power-series.scm says so in as many
;;; words: "the chain was one rung SHORT: `G_k <= lim G' is the lemma `a
;;; nondecreasing sequence converging to L satisfies x_k <= L for every k',
;;; which the tree did not have.  It is also not needed" -- for the comparison
;;; test, which wants SOME bound and takes eps = 1
;;; (`monotone-convergent-bounded-above', its sibling one file up).  It IS
;;; needed as soon as one wants the SHARP bound: a partial sum is at most the
;;; sum.  Everything the countable product of metric spaces asks of its
;;; defining series -- that a single term is at most D_w(x,y), that D_w >= 0,
;;; that D_w(x,y) = 0 forces every coordinate distance to 0 -- is this lemma.
;;;
;;; Nothing else in the tree runs this way round.  `rr-limit-abs-le' bounds the
;;; LIMIT from a uniform bound on the terms; `monotone-convergent-bounded-above'
;;; produces SOME bound (L + 1), not the limit.
;;;
;;; THE PROOF IS NOT BY CONTRADICTION.  The obvious argument -- suppose
;;; L < f(m), take eps = f(m) - L -- has to halve eps to reach a strict clash
;;; (CONVERGES-TO is stated with a NON-strict `dist <= eps'), and it has to
;;; manufacture `L < f(m)' from `not (f(m) <= L)', which is order totality plus
;;; an antisymmetry step.  `contra' would do the arithmetic half, and is not
;;; reachable: contra.scm loads BELOW the whole theorem library.  The direct
;;; route is shorter and needs neither:
;;;
;;;     for every eps > 0,   f(m) - L <= eps,
;;;
;;; and `rr-le-all-pos-nonpos' collapses that to f(m) - L <= 0.  Given eps, the
;;; threshold N of convergence and the index m are combined by the BINARY MAX
;;; (`nn-max-closed', `rr-le-max-left/-right'): at n = max(m,N) the monotone
;;; lift gives f(m) <= f(n) and the tail estimate gives f(n) - L <= eps, and
;;; `ineq' chains the two.  No case split, no negation, one `ineq' call.
;;;
;;; TWO MECHANICS.  `rr-abs-bound' is GUARDED on the bound being real, so
;;; `(IN eps RR)' has to be landed BEFORE the `mac-h' fires -- otherwise the
;;; rewrite still happens and posts `eps in rr' as a spawned side-condition
;;; leaf, which the `have!' lane then reports as "THUNK left the side goal
;;; open" several steps later.  And the inner tail universal is captured
;;; BEFORE `rr-le-max-left' is cited: that citation's own partly-peeled chain
;;; is a FORALL mentioning the same threshold, and a shape test picks it
;;; instead.
;;;
;;; WHAT IT COSTS.  `modulo {nn-zero-le, nn-le-succ-cases, rr-le-all-pos-nonpos}'
;;; [trust: well-known].  The first two are inherited through the monotone lift
;;; `nn-monotone-step-implies-le' and are the NN-order backlog of
;;; structure-library/order-lemmas.scm; the third is the archimedean-flavoured
;;; support of order-predicates.scm.  Nothing here is about the reals beyond
;;; those.
;;;
;;; Loads after theorem-library/comparison-test-proof (series-partial-sum-*),
;;; monotone-convergence-proof (nn-monotone-step-implies-le) and
;;; dominated-convergence (series-partial-sum-nonneg -- L2 below needs the
;;; partial sums bounded from BELOW, and that lemma is already there, proved by
;;; induction on the index rather than through the partial-sum SEQUENCE); its other
;;; needs are rr-max-basics (rr-le-max-left/-right), rr-min-basics
;;; (nn-max-closed), nn-order-basics (nn-in-rr, nn-zero-le is in order-lemmas),
;;; rr-abs-basics (rr-abs-bound, rr-abs-closed), binary-minus-laws
;;; (rr-sub-in-rr), order-predicates (rr-le-all-pos-nonpos), rr-ms-dist,
;;; fun-apply-type-proof (fun-apply-type-c), metric-completeness (CONVERGES-TO)
;;; and driver-kit.

;;; ---- file-local driver helpers (the `ml-' prefix) --------------------

;;; Select a hypothesis by CONTENT and ERROR on a miss.
(define (ml-find what pred)
  (let loop ((l (dk-asms)))
    (cond ((null? l) (error "ml-find: no context formula" what))
          ((pred (car l)) (car l))
          (else (loop (cdr l))))))

;;; `ineq' wants 1-based assumption indices, named ONE BY ONE: a premise whose
;;; atoms cannot be certified in RR poisons the whole call.
(define (ml-idx form)
  (let loop ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "ml-idx: not in context" form))
          ((equal? (car l) form) i)
          (else (loop (cdr l) (+ i 1))))))

(define (ml-ineq . forms) (apply ineq (map ml-idx forms)))

(define (ml-fvs forms) (apply append (map free-vars forms)))

;;; Skolemize a FORSOME already in the CONTEXT -- `obtain' recognises only an
;;; existential its own lane landed.  A miss ERRORS.
(define (ml-skolem! ex)
  (let* ((fv0 (ml-fvs (dk-asms)))
         (landed (dk-landed (lambda () (ai ex)))))
    (for-each (lambda (f) (if (and (pair? f) (eq? (car f) 'AND)) (dk-split! f))) landed)
    (let ((fresh (filter (lambda (v) (not (memq v fv0))) (ml-fvs (dk-asms)))))
      (if (null? fresh)
          (error "ml-skolem!: no eigenvariable appeared for" ex)
          (car fresh)))))

;;; `di' until an ASSUMPTION lands -- never a `di' count.
(define (ml-di-landed!)
  (let loop ((n 0))
    (let ((new (dk-landed* (lambda () (di)))))
      (cond ((pair? new) new)
            ((> n 4) (error "ml-di-landed!: di landed no assumption"))
            (else (loop (+ n 1)))))))

(define (ml-di-landed-1!)
  (let ((new (ml-di-landed!)))
    (if (null? (cdr new)) (car new)
        (error "ml-di-landed-1!: expected 1 landing"
               (map expression->string new)))))

;;; (IN x RR) off a POS-RR, on a SIDE branch: `mac-h' REPLACES the hypothesis
;;; and the eps universal above still wants it.
(define (ml-pos-in-rr! x)
  (have! (list 'IN x 'RR)
    (lambda ()
      (mac-h 'pos-rr (list 'POS-RR x))
      (dk-split! (list 'AND (list 'IN x 'RR)
                       (list 'AND (list '<= 0 x) (list 'NOT (list '= 0 x)))))
      (ass))))

;;; The inner (FORALL n_ ... (<= thr n_) => ...) of a skolemized eps-N clause,
;;; discriminated on its THRESHOLD and captured while the context is clean.
(define (ml-inner thr)
  (ml-find thr (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                                (let ((b (caddr a)))
                                  (and (pair? b) (eq? (car b) 'IMPLIES)
                                       (dk-contains? (caddr b) thr)))))))

;;; di-split an AND goal to its leaves and run CLOSER on each.
(define (ml-goal-and! closer)
  (let ((g (dk-goal)))
    (if (and (pair? g) (eq? (car g) 'AND))
        (for-each (lambda (k) (dk-focus! k) (ml-goal-and! closer))
                  (dk-opened (lambda () (di))))
        (closer))))

;;; =====================================================================
;;; L1.  rr-mono-le-limit -- a term of a nondecreasing convergent sequence is
;;; at most its limit.  The typing of L is NOT a hypothesis: CONVERGES-TO
;;; carries (IN L (PTS RR-MS)) and `slot-h' brings it to RR.
;;; =====================================================================

(define ml-stmt
  '(FORALL f (IMPLIES (IN f (FUN NN RR))
     (IMPLIES (FORALL k (IMPLIES (IN k NN) (<= (f k) (f (succ k)))))
       (FORALL lm_ (IMPLIES (CONVERGES-TO RR-MS f lm_)
         (FORALL m (IMPLIES (IN m NN) (<= (f m) lm_)))))))))

(sp (make-wff ml-stmt))
(define ml-typ  (ml-di-landed-1!))                 ; (IN f (FUN NN RR))
(define ml-f    (cadr ml-typ))
(define ml-step (ml-di-landed-1!))                 ; the successor hypothesis
(define ml-conv (ml-di-landed-1!))                 ; (CONVERGES-TO RR-MS f L)
(define ml-L    (cadddr ml-conv))
(define ml-m    (cadr (ml-di-landed-1!)))          ; (IN m NN)

(dk-split! (dk-landed-find (lambda () (mac-h 'converges-to ml-conv))
                           (lambda (a) (eq? (car a) 'AND))))
(slot-h 'PTS (list 'IN ml-L '(PTS RR-MS)))         ; PTS(RR-MS) = RR

(define ml-epsu
  (ml-find 'eps-universal
    (lambda (a) (and (pair? a) (eq? (car a) 'FORALL) (dk-contains? a 'POS-RR)))))

(fact 'fun-apply-type-c ml-f 'NN 'RR ml-m)
(fact 'rr-sub-in-rr (list ml-f ml-m) ml-L)

(define ml-diff (list '- (list ml-f ml-m) ml-L))

;;; for every eps > 0:  f(m) - L <= eps,  witnessed at n = max(m, N).
(have! (list 'FORALL 'eps (list 'IMPLIES '(POS-RR eps) (list '<= ml-diff 'eps)))
  (lambda ()
    (let* ((eps (cadr (ml-di-landed-1!)))
           (ex  (dk-deepest (lambda () (inst+ ml-epsu eps))))
           (n0  (ml-skolem! ex))
           (inner (ml-inner n0))                   ; captured BEFORE the max facts
           (bnd (list 'MAX ml-m n0)))
      (fact 'nn-max-closed ml-m n0)
      (fact 'nn-in-rr ml-m) (fact 'nn-in-rr n0) (fact 'nn-in-rr bnd)
      (fact 'rr-le-max-left ml-m n0)
      (fact 'rr-le-max-right ml-m n0)
      (inst+ inner bnd)
      (fact 'fun-apply-type-c ml-f 'NN 'RR bnd)
      (fact 'nn-monotone-step-implies-le ml-f bnd ml-m)   ; f(m) <= f(max(m,N))
      (fact 'rr-sub-in-rr (list ml-f bnd) ml-L)
      (fact 'rr-abs-closed (list '- (list ml-f bnd) ml-L))
      ;; rr-abs-bound is GUARDED on the bound being real: type eps FIRST, or the
      ;; rewrite posts `eps in rr' as a spawned leaf nobody closes.
      (ml-pos-in-rr! eps)
      (mac-h 'rr-ms-dist (list '<= (list '(DIST RR-MS) (list ml-f bnd) ml-L) eps))
      (dk-split! (dk-landed-1
        (lambda () (mac-h 'rr-abs-bound
          (list '<= (list 'abs (list '- (list ml-f bnd) ml-L)) eps)))))
      (ml-ineq (list '<= (list ml-f ml-m) (list ml-f bnd))
               (list '<= (list '- (list ml-f bnd) ml-L) eps)))))

(fact 'rr-le-all-pos-nonpos ml-diff)
(ml-ineq (list '<= ml-diff 0))
(qed 'rr-mono-le-limit)
(topic! 'rr-mono-le-limit 'analysis)
(alias! 'rr-mono-le-limit
        "a term of a nondecreasing convergent sequence is at most its limit"
        "a partial sum is at most the sum")

;;; =====================================================================
;;; L2.  series-term-le-sum -- A SINGLE TERM OF A NONNEGATIVE CONVERGENT
;;; SERIES IS AT MOST ITS SUM.
;;;
;;;   f in FUN(NN,RR),  0 <= f(n) for every n,  SERIES-CONVERGES-TO(f, L)
;;;     =>   f(n) <= L   for every n in NN.
;;;
;;; This is L1 read at the PARTIAL-SUM sequence, which is nondecreasing because
;;; the terms are nonnegative, plus the two facts that squeeze one term out of
;;; two consecutive partial sums:
;;;
;;;   S_{n+1} <= L                (L1)
;;;   S_{n+1} = S_n + f(n)        (the recurrence)
;;;   0 <= S_n                    (series-partial-sum-nonneg)
;;;
;;; so f(n) = S_{n+1} - S_n <= L, and `ineq' does the whole step once `mac-h'
;;; has put the recurrence into the hypothesis.  It is what the countable
;;; product metric needs of its defining series in two separate places: that
;;; the sum dominates each weighted coordinate distance (so the projections are
;;; continuous), and, at n = 0, that the sum is nonnegative.
;;; =====================================================================

(define ml3-stmt
  '(FORALL f (IMPLIES (IN f (FUN NN RR))
     (IMPLIES (FORALL n_ (IMPLIES (IN n_ NN) (<= 0 (f n_))))
       (FORALL lm_ (IMPLIES (SERIES-CONVERGES-TO f lm_)
         (FORALL n_ (IMPLIES (IN n_ NN) (<= (f n_) lm_)))))))))

(sp (make-wff ml3-stmt))
(define ml3-f      (cadr (ml-di-landed-1!)))
(define ml3-nonneg (ml-di-landed-1!))
(define ml3-conv   (ml-di-landed-1!))              ; (SERIES-CONVERGES-TO f L)
(define ml3-L      (caddr ml3-conv))
(define ml3-n      (cadr (ml-di-landed-1!)))
(define ml3-seq (list 'VNB-LAMBDA 'k 'NN (list 'SERIES-PARTIAL-SUM ml3-f 'k)))

(fact 'nn-succ-closed ml3-n)

(have! (list 'IN ml3-seq '(FUN NN RR))
  (lambda () (fact 'series-partial-sum-seq-in-fun ml3-f) (ass)))

;;; the successor step, in the LAMBDA language rr-mono-le-limit speaks
(have! (list 'FORALL 'k (list 'IMPLIES '(IN k NN)
                              (list '<= (list ml3-seq 'k) (list ml3-seq '(succ k)))))
  (lambda ()
    (let ((k (cadr (ml-di-landed-1!))))
      (fact 'nn-succ-closed k)
      (mac 'series-partial-sum-seq-apply)
      (fact 'series-partial-sum-monotone-nonneg ml3-f k)
      (ass))))

;;; SERIES-CONVERGES-TO(f,L) IS CONVERGES-TO(RR-MS, partial sums, L), unfolded
;;; on a SIDE branch (`mac-h' would replace the hypothesis).
(have! (list 'CONVERGES-TO 'RR-MS ml3-seq ml3-L)
  (lambda () (mac-h 'series-converges-to ml3-conv) (ass)))

;;; L in RR -- for the oracle, which certifies no atom it cannot type.  Again
;;; on a side branch: `mac-h' on the CONVERGES-TO would delete the hypothesis
;;; `rr-mono-le-limit' is about to be cited on.
(have! (list 'IN ml3-L 'RR)
  (lambda ()
    (dk-split! (dk-landed-find
                (lambda () (mac-h 'converges-to
                                  (list 'CONVERGES-TO 'RR-MS ml3-seq ml3-L)))
                (lambda (a) (eq? (car a) 'AND))))
    (slot-h 'PTS (list 'IN ml3-L '(PTS RR-MS)))
    (ass)))

;;; L1 at the partial-sum sequence: every partial sum is at most the sum.
(fact 'rr-mono-le-limit ml3-seq ml3-L)
(define ml3-above
  (ml-find 'sums-le-limit
    (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                     (let ((b (caddr a)))
                       (and (pair? b) (eq? (car b) 'IMPLIES)
                            (pair? (caddr b)) (eq? (car (caddr b)) '<=)
                            (equal? (caddr (caddr b)) ml3-L)
                            (dk-contains? b 'VNB-LAMBDA)))))))
(inst+ ml3-above (list 'succ ml3-n))
(mac-h 'series-partial-sum-seq-apply
       (list '<= (list ml3-seq (list 'succ ml3-n)) ml3-L))
;; series-partial-sum-succ is guarded on its two arguments being real since
;; 2026-08-29, so the typings have to precede the rewrite rather than follow it.
(fact 'series-partial-sum-nonneg ml3-n ml3-f)
(fact 'series-partial-sum-in-rr ml3-n ml3-f)
(fact 'fun-apply-type-c ml3-f 'NN 'RR ml3-n)

(mac-h 'series-partial-sum-succ
       (list '<= (list 'SERIES-PARTIAL-SUM ml3-f (list 'succ ml3-n)) ml3-L))

(ml-ineq (list '<= (list '+ (list 'SERIES-PARTIAL-SUM ml3-f ml3-n)
                            (list ml3-f ml3-n)) ml3-L)
         (list '<= 0 (list 'SERIES-PARTIAL-SUM ml3-f ml3-n)))
(qed 'series-term-le-sum)
(topic! 'series-term-le-sum 'analysis)
(alias! 'series-term-le-sum
        "a term of a nonnegative convergent series is at most its sum")

;;; =====================================================================
;;; L3.  series-nonneg-zero-sum -- a nonnegative series with sum 0 is the zero
;;; sequence.  L2 at L = 0 gives f(n) <= 0; the hypothesis gives 0 <= f(n);
;;; antisymmetry finishes.  This is the ZERO LAW of the countable product
;;; metric, one instantiation away from being about D_w.
;;; =====================================================================

(sp (make-wff
  '(FORALL f (IMPLIES (IN f (FUN NN RR))
     (IMPLIES (FORALL n_ (IMPLIES (IN n_ NN) (<= 0 (f n_))))
       (IMPLIES (SERIES-CONVERGES-TO f 0)
         (FORALL n_ (IMPLIES (IN n_ NN) (= (f n_) 0)))))))))
(define ml4-f      (cadr (ml-di-landed-1!)))
(define ml4-nonneg (ml-di-landed-1!))
(define ml4-conv   (ml-di-landed-1!))
(define ml4-n      (cadr (ml-di-landed-1!)))
(fact 'series-term-le-sum ml4-f 0 ml4-n)
(inst+ ml4-nonneg ml4-n)
(fact 'fun-apply-type-c ml4-f 'NN 'RR ml4-n)
(fact 'rr-zero-in)
(have! (list 'AND (list 'IN (list ml4-f ml4-n) 'RR) '(IN 0 RR)))
(have! (list 'AND (list '<= (list ml4-f ml4-n) 0) (list '<= 0 (list ml4-f ml4-n))))
(fact 'rr-leq-antisymmetric (list ml4-f ml4-n) 0)
(ass)
(qed 'series-nonneg-zero-sum)
(topic! 'series-nonneg-zero-sum 'analysis)
(alias! 'series-nonneg-zero-sum
        "a nonnegative series with sum zero has every term zero")
