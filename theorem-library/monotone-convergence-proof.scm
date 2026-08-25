;;; monotone-convergence-proof.scm -- MONOTONE CONVERGENCE on RR, PROVEN.
;;;
;;;   f in FUN(NN,RR),  f(k) <= f(succ k) for every k,  f bounded above
;;;     =>  CONVERGES(RR-MS, f)
;;;
;;; `monotone-convergence-rr' was an ASSERTED support carrying a `well-known'
;;; warrant (theorem-library/series-order-lemmas.scm), and it is the keystone of
;;; the series lane: `comparison-test' (power-series.scm) names it in its own
;;; warrant as "the named lemma comparison-test was waiting on", and through
;;; comparison-test it is the bottom rung of the countable-product-of-metric-
;;; spaces lane (structure-library/product-metric.scm), where nothing is proven.
;;;
;;; THE ROUTE.  The textbook one, and it is cheap here because rr-sup-approx
;;; already exists:
;;;
;;;   RANGE = { y in RR : forsome k in NN.  y = f(k) },  L = SUP(RANGE).
;;;
;;;   1. RANGE is a SEP over RR, so (SUBSET RANGE RR) is one `sep-me' and no
;;;      image/replacement axiom is needed.  It is inhabited by f(0) and
;;;      bounded above by the hypothesis `bnd'.
;;;   2. rr-sup-in / rr-sup-upper give L in RR and f(n) <= L for every n.
;;;   3. Given eps > 0, rr-sup-approx hands back w in RANGE with L - eps < w,
;;;      and w = f(N) for some N in NN -- that N is the threshold.
;;;   4. For n >= N the MONOTONE LIFT (L1 below) gives f(N) <= f(n), so
;;;          L - eps < f(N) <= f(n) <= L,
;;;      and `ineq' closes both halves of the abs bound in one call each.
;;;
;;; L1, THE LIFT, IS THE ONLY REAL WORK.  The hypothesis gives the SUCCESSOR
;;; step alone; step 4 needs m <= n => f(m) <= f(n).  That is an NN-induction on
;;; n with m fixed, so n is stated OUTERMOST -- `ni' tests the goal SHAPE, and
;;; with the binders the other way round the induction is simply not available.
;;; The step splits m <= succ n by `nn-le-succ-cases'; the base needs m <= 0 to
;;; force m = 0, done by `nn-zero-le' plus antisymmetry rather than by the
;;; proven `nn-le-zero-is-zero', because that theorem's own bill carries two
;;; further NN supports and this way the whole file rests on exactly two.
;;;
;;; WHAT IT COSTS.  `modulo {nn-zero-le, nn-le-succ-cases}', trust `well-known'.
;;; Both leaves are the NN-order/discreteness supports of
;;; structure-library/order-lemmas.scm (:373 and :241) and neither is about the
;;; reals: order completeness (rr-sup-in/-upper, primitive), rr-sup-approx,
;;; rr-abs-bound, rr-ms-dist, fun-apply-type-c, nn-in-rr and rr-sub-in-rr are
;;; all theorems or primitive, and `ineq'/`arith' add no debt.  So the residual
;;; debt of monotone convergence on RR is now the NN order backlog, nothing
;;; else.
;;;
;;; The distance is brought to the surface by `rr-ms-dist' as a MACETE and never
;;; by `subst' (the accessor sits in OPERATOR position), and `rr-abs-bound'
;;; turns the one abs goal into the two linear ones -- the rr-complete-proof
;;; pattern, of which this file is the easier sibling one storey down.
;;;
;;; Loads after theorem-library/rr-sup-approx (rr-sup-approx) and before
;;; ccint-creep; its other needs are order-lemmas (nn-zero-le, nn-le-succ-cases),
;;; nn-order-basics (nn-in-rr), fun-apply-type-proof (fun-apply-type-c),
;;; rr-abs-basics (rr-abs-bound), binary-minus-laws (rr-sub-in-rr), rr-ms-dist,
;;; rr-metric-space-proof (rr-is-metric-space), metric-completeness (CONVERGES,
;;; CONVERGES-TO) and driver-kit.

;;; ---- file-local driver helpers (the `mc-' prefix) --------------------

;;; Select a hypothesis by CONTENT and ERROR on a miss -- a driver that
;;; reconstructs a formula to cite it addresses the wrong assumption silently.
(define (mc-find what pred)
  (let loop ((l (dk-asms)))
    (cond ((null? l) (error "mc-find: no context formula" what))
          ((pred (car l)) (car l))
          (else (loop (cdr l))))))

;;; `ineq' wants 1-based assumption indices, and the premises are named ONE BY
;;; ONE: the context carries memberships and equations whose atoms can never be
;;; certified in RR, and a single such premise poisons the whole call.
(define (mc-idx form)
  (let loop ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "mc-idx: not in context" form))
          ((equal? (car l) form) i)
          (else (loop (cdr l) (+ i 1))))))

(define (mc-ineq . forms) (apply ineq (map mc-idx forms)))

;;; di-split an AND goal to its leaves and run CLOSER on each.
(define (mc-goal-and! closer)
  (let ((g (dk-goal)))
    (if (and (pair? g) (eq? (car g) 'AND))
        (for-each (lambda (k) (dk-focus! k) (mc-goal-and! closer))
                  (dk-opened (lambda () (di))))
        (closer))))

(define (mc-fvs forms) (apply append (map free-vars forms)))

;;; Skolemize a FORSOME already in the CONTEXT.  `obtain' recognises only an
;;; existential its own lane landed, so it cannot do this one; the eigenvariable
;;; is read off by free-variable set difference and a miss ERRORS.
(define (mc-skolem! ex)
  (let* ((fv0 (mc-fvs (dk-asms)))
         (landed (dk-landed (lambda () (ai ex)))))
    (for-each (lambda (f) (if (and (pair? f) (eq? (car f) 'AND)) (dk-split! f))) landed)
    (let ((fresh (filter (lambda (v) (not (memq v fv0))) (mc-fvs (dk-asms)))))
      (if (null? fresh)
          (error "mc-skolem!: no eigenvariable appeared for" ex)
          (car fresh)))))

;;; `di' until an ASSUMPTION lands.  One `di' takes a GUARDED universal whole,
;;; but on an unguarded (FORALL y (IMPLIES ...)) it peels the quantifier and
;;; lands nothing -- so loop on the LANDING, not on a `di' count.
(define (mc-di-landed!)
  (let loop ((n 0))
    (let ((new (dk-landed* (lambda () (di)))))
      (cond ((pair? new) new)
            ((> n 4) (error "mc-di-landed!: di landed no assumption"))
            (else (loop (+ n 1)))))))

(define (mc-di-landed-1!)
  (let ((new (mc-di-landed!)))
    (if (null? (cdr new)) (car new)
        (error "mc-di-landed-1!: expected 1 landing"
               (map expression->string new)))))

;;; =====================================================================
;;; L1.  nn-monotone-step-implies-le -- consecutive-nondecreasing => monotone.
;;;
;;;   f(k) <= f(succ k) for every k in NN   =>   m <= n  =>  f(m) <= f(n)
;;;
;;; The induction variable n is stated OUTERMOST: `ni' tests the goal's shape
;;; literally, and a greedy `di' that ate it first cannot be undone.
;;; =====================================================================

(sp (make-wff
  '(FORALL f (IMPLIES (IN f (FUN NN RR))
     (IMPLIES (FORALL k (IMPLIES (IN k NN) (<= (f k) (f (succ k)))))
       (FORALL n (IMPLIES (IN n NN)
         (FORALL m (IMPLIES (IN m NN)
           (IMPLIES (<= m n) (<= (f m) (f n))))))))))))

(define mc1-typ  (dk-landed-1 (lambda () (di))))    ; (IN f (FUN NN RR))
(define mc1-f    (cadr mc1-typ))
(define mc1-step (dk-landed-1 (lambda () (di))))    ; the successor hypothesis

(fact 'nn-zero-in)
(fact 'fun-apply-type-c mc1-f 'NN 'RR 0)

(define mc1-br (use-induction))

;;; base:  forall m in NN.  m <= 0  =>  f(m) <= f(0).
;;; m <= 0 and 0 <= m force m = 0, and then the goal is reflexivity.
(dk-focus! (cdr (assq 'base mc1-br)))
(dk-peel-to! '<=)                      ; m, (IN m NN), (<= m 0) -- never count di's
(let ((m (cadr (cadr (dk-goal)))))
  (fact 'nn-zero-le m)
  (fact 'nn-in-rr m)
  (fact 'nn-in-rr 0)
  ;; rr-leq-antisymmetric has AND antecedents, which `fact' will not split.
  (have! (list 'AND (list 'IN m 'RR) '(IN 0 RR)))
  (have! (list 'AND (list '<= m 0) (list '<= 0 m)))
  (fact 'rr-leq-antisymmetric m 0)
  (subst (list '= m 0)))
(fact 'rr-leq-reflexive (list mc1-f 0))
(ass)

;;; step:  forall m in NN.  m <= succ n  =>  f(m) <= f(succ n).
;;; m <= succ n splits: either m <= n, where the IH gives f(m) <= f(n) and one
;;; more step of the hypothesis chains f(n) <= f(succ n), or m = succ n, where
;;; the two sides coincide.  All three typings are landed BEFORE the split, so
;;; both branches inherit them.
(dk-focus! (cdr (assq 'step mc1-br)))
(define mc1-n  (cdr (assq 'var mc1-br)))
(define mc1-ih (cdr (assq 'ih  mc1-br)))
(dk-peel-to! '<=)
(define mc1-m (cadr (cadr (dk-goal))))
(fact 'nn-succ-closed mc1-n)
(fact 'fun-apply-type-c mc1-f 'NN 'RR mc1-m)
(fact 'fun-apply-type-c mc1-f 'NN 'RR mc1-n)
(fact 'fun-apply-type-c mc1-f 'NN 'RR (list 'succ mc1-n))
(fact 'nn-le-succ-cases mc1-n mc1-m)
(use-cases (list (list '<= mc1-m mc1-n) (list '= mc1-m (list 'succ mc1-n)))
  (lambda ()
    (inst+ mc1-ih mc1-m)
    (inst+ mc1-step mc1-n)
    (mc-ineq (list '<= (list mc1-f mc1-m) (list mc1-f mc1-n))
             (list '<= (list mc1-f mc1-n) (list mc1-f (list 'succ mc1-n)))))
  (lambda ()
    (subst (list '= mc1-m (list 'succ mc1-n)))
    (fact 'rr-leq-reflexive (list mc1-f (list 'succ mc1-n)))
    (ass)))

(qed 'nn-monotone-step-implies-le)
(topic! 'nn-monotone-step-implies-le 'analysis)
(alias! 'nn-monotone-step-implies-le
        "the monotone lift" "consecutive-nondecreasing implies monotone")

;;; =====================================================================
;;; L2.  monotone-convergence-rr.  Statement reproduced VERBATIM from the
;;; support this file retires (series-order-lemmas.scm), so that any citer
;;; sees the formula it always saw.
;;; =====================================================================

(define mc-stmt
  '(FORALL f (IMPLIES (IN f (FUN NN RR))
     (IMPLIES (AND (FORALL k (IMPLIES (IN k NN) (<= (f k) (f (succ k)))))
                   (FORSOME bnd (AND (IN bnd RR)
                     (FORALL k (IMPLIES (IN k NN) (<= (f k) bnd))))))
       (CONVERGES RR-MS f)))))

(sp (make-wff mc-stmt))

(define mc-typ   (dk-landed-1 (lambda () (di))))    ; (IN f (FUN NN RR))
(define mc-f     (cadr mc-typ))
(define mc-hyp   (dk-landed-1 (lambda () (di))))    ; the conjunction
(define mc-parts (dk-split! mc-hyp))
(define mc-step (or (find-first (lambda (a) (eq? (car a) 'FORALL)) mc-parts)
                    (error "monotone-convergence: no step hypothesis")))
(define mc-ex   (or (find-first (lambda (a) (eq? (car a) 'FORSOME)) mc-parts)
                    (error "monotone-convergence: no bound existential")))
(define mc-bnd  (mc-skolem! mc-ex))

;;; Discriminate the bounding universal on its CONSEQUENT, not on a symbol it
;;; contains: the step hypothesis has the same head and the same binder.
(define mc-bound
  (mc-find 'bounding
    (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                     (let ((b (caddr a)))
                       (and (pair? b) (eq? (car b) 'IMPLIES)
                            (pair? (caddr b)) (eq? (car (caddr b)) '<=)
                            (equal? (caddr (caddr b)) mc-bnd)))))))

;;; RANGE = { y in RR : forsome k in NN.  y = f(k) }, and its supremum.
;;; The equation is written y = f(k) and not f(k) = y so that the member's own
;;; equation rewrites the GOAL (subst walks the goal, never a hypothesis).
(define mc-S (list 'SEP 'y_ 'RR
                (list 'FORSOME 'k_ (list 'AND '(IN k_ NN)
                                         (list '= 'y_ (list mc-f 'k_))))))
(define mc-L (list 'SUP mc-S))

;;; (IN (f u) RANGE), for u already typed in NN with f(u) in RR.  The equation
;;; conjunct is f(u) = f(u), i.e. DEFINEDNESS, which `rfl' discharges from the
;;; (IN (f u) RR) already in context.
(define (mc-member! u)
  (have! (list 'IN (list mc-f u) mc-S)
    (lambda ()
      (for-each (lambda (leaf)
                  (dk-focus! leaf)
                  (if (eq? (car (dk-goal)) 'IN)
                      (ass)
                      (begin (ew u)
                             (mc-goal-and!
                              (lambda () (if (eq? (car (dk-goal)) '=) (rfl) (ass)))))))
                (dk-opened (lambda () (sep-mi)))))))

(fact 'nn-zero-in)
(fact 'fun-apply-type-c mc-f 'NN 'RR 0)
(mc-member! 0)
(have! (list 'FORSOME 'x_ (list 'IN 'x_ mc-S))
  (lambda () (ew (list mc-f 0)) (ass)))
(have! (list 'SUBSET mc-S 'RR)
  (lambda () (mac 'subset-def) (di)
             (sep-me (mc-find 'member (lambda (a) (and (pair? a) (eq? (car a) 'IN)
                                                       (equal? (caddr a) mc-S)))))
             (ass)))

;;; goal (<= x BOUND) for the eigenvariable x of RANGE, with FA bounding f.
(define (mc-range-le! fa)
  (let ((x (cadr (dk-goal))))
    (sep-me (mc-find 'member (lambda (a) (equal? a (list 'IN x mc-S)))))
    (let ((k (mc-skolem!
              (mc-find 'range-witness
                (lambda (a) (and (pair? a) (eq? (car a) 'FORSOME)
                                 (dk-contains? a x)))))))
      (inst+ fa k)
      (subst (list '= x (list mc-f k)))
      (ass))))

(have! (list 'RR-BOUNDED-ABOVE mc-S)
  (lambda ()
    (mac 'rr-bounded-above)
    (ew mc-bnd)
    (mac 'rr-upper-bound)
    (for-each (lambda (leaf)
                (dk-focus! leaf)
                (if (eq? (car (dk-goal)) 'IN)
                    (ass)
                    (begin (di) (mc-range-le! mc-bound))))
              (dk-opened (lambda () (di))))))

(fact 'rr-sup-in mc-S)                              ; L in RR
(fact 'rr-sup-upper mc-S)                           ; RR-UPPER-BOUND(RANGE, L)
(mac-h 'rr-upper-bound (list 'RR-UPPER-BOUND mc-S mc-L))
(dk-split! (list 'AND (list 'IN mc-L 'RR)
                 (list 'FORALL 'x (list 'IMPLIES (list 'IN 'x mc-S)
                                        (list '<= 'x mc-L)))))
(define mc-ub
  (mc-find 'sup-upper
    (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                     (let ((b (caddr a)))
                       (and (pair? b) (eq? (car b) 'IMPLIES)
                            (pair? (caddr b)) (eq? (car (caddr b)) '<=)
                            (equal? (caddr (caddr b)) mc-L)))))))

;;; ---- the limit is SUP(RANGE) ----------------------------------------

(mac 'converges)
(ew mc-L)
(mac 'converges-to)

;;; The eps-N estimate, with n introduced and N <= n landed.  Every argument of
;;; every atom is typed in RR BEFORE the two macetes fire: `rr-ms-dist' is
;;; GUARDED, so on a goal whose arguments are untyped `mac' silently refuses.
(define (mc-tail! mc-bigN mc-w mc-eps)
  (let* ((mem (mc-di-landed-1!))
         (n_  (cadr mem)))
    (di)                                                  ; land (<= N n)
    (fact 'fun-apply-type-c mc-f 'NN 'RR n_)
    (fact 'fun-apply-type-c mc-f 'NN 'RR mc-bigN)
    (mc-member! n_)
    (inst+ mc-ub (list mc-f n_))                          ; f(n) <= L
    (fact 'nn-monotone-step-implies-le mc-f n_ mc-bigN)   ; f(N) <= f(n)
    (fact 'rr-sub-in-rr (list mc-f n_) mc-L)
    (mac 'rr-ms-dist)
    (mac 'rr-abs-bound)
    (mc-goal-and!
     (lambda ()
       (if (equal? (cadr (dk-goal)) (list '- mc-eps))
           ;; L - eps < w = f(N) <= f(n)
           (mc-ineq (list '< (list '- mc-L mc-eps) mc-w)
                    (list '= mc-w (list mc-f mc-bigN))
                    (list '<= (list mc-f mc-bigN) (list mc-f n_)))
           ;; f(n) <= L and 0 <= eps
           (mc-ineq (list '<= (list mc-f n_) mc-L)
                    (list '<= 0 mc-eps)))))))

(define (mc-eps!)
  (let* ((posr (mc-di-landed-1!))
         (mc-eps (cadr posr)))
    (mac-h 'pos-rr posr)
    (dk-split! (list 'AND (list 'IN mc-eps 'RR)
                     (list 'AND (list '<= 0 mc-eps)
                                (list 'NOT (list '= 0 mc-eps)))))
    (have! (list '< 0 mc-eps) (lambda () (mac '<) (from-context!)))
    (let* ((approx (dk-fact! 'rr-sup-approx mc-S mc-eps))
           (mc-w   (mc-skolem! approx)))
      (sep-me (mc-find 'w-in-range (lambda (a) (equal? a (list 'IN mc-w mc-S)))))
      (let ((mc-bigN (mc-skolem!
                      (mc-find 'w-witness
                        (lambda (a) (and (pair? a) (eq? (car a) 'FORSOME)
                                         (dk-contains? a mc-w)))))))
        (ew mc-bigN)
        (mc-goal-and!
         (lambda ()
           (if (eq? (car (dk-goal)) 'FORALL)
               (mc-tail! mc-bigN mc-w mc-eps)
               (ass))))))))

(mc-goal-and!
 (lambda ()
   (let ((g (dk-goal)))
     (cond ((eq? (car g) 'IS-METRIC-SPACE) (fact 'rr-is-metric-space) (ass))
           ((eq? (car g) 'IN) (slot 'PTS) (ass))     ; PTS(RR-MS) = RR
           (else (mc-eps!))))))

(qed 'monotone-convergence-rr)
(topic! 'monotone-convergence-rr 'analysis)
(alias! 'monotone-convergence-rr
        "the monotone convergence theorem"
        "a nondecreasing bounded real sequence converges")
