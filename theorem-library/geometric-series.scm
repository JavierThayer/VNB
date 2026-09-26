;;; geometric-series.scm -- THE GEOMETRIC MAJORANT, PROVEN, and the four small
;;; facts about powers it rests on.
;;;
;;;   rr-abs-power                |r^k| = |r|^k
;;;   rr-power-nonneg             0 <= r  =>  0 <= r^k
;;;   geometric-partial-sum-mul   (1 - r) . S_k  =  1 - r^k          DIVISION-FREE
;;;   geometric-partial-sum       S_k = (1 - r^k) . 1/(1-r)          (r /= 1)
;;;   geometric-series-converges  0 <= r < 1  =>  SERIES-CONVERGES(n |-> r^n)
;;;
;;; WHY THIS FILE EXISTS.  `ratio-test-converges' (theorem-library/power-series.scm)
;;; is asserted, and its warrant says the proof "factors through the geometric
;;; majorant (geometric-series-converges-to) and the comparison test, both now in
;;; the library -- the proof chain is assembled, not missing."  Half of that was
;;; true: `comparison-test' is proven.  The majorant was NOT -- both
;;; `geometric-partial-sum' and `geometric-series-converges-to' were themselves
;;; asserted, and the second one's own warrant names the reason: it needs
;;; `r^k -> 0', "not yet in the library".  So the chain rested on two assertions,
;;; one of which was waiting on a fact nobody had proved.
;;;
;;; THE OBSERVATION THAT MAKES THIS CHEAP, and it is the whole design of the
;;; file: **the ratio test does not need the geometric series' VALUE.**
;;; `comparison-test' asks only for SERIES-CONVERGES of the dominating series.
;;; Convergence follows from monotone convergence -- the partial sums increase
;;; (terms are nonnegative) and are bounded above by 1/(1-r) -- and THAT needs no
;;; limit of r^k at all, only the closed form and 0 <= r^k.  `r^k -> 0' is a
;;; genuinely harder fact (Bernoulli, the Archimedean property, a squeeze, and a
;;; case split at r = 0); it is still open, and so is
;;; `geometric-series-converges-to', which is the statement that actually needs
;;; it.  What is proven here is the half the ratio test consumes.
;;;
;;; WHY THE DIVISION-FREE FORM COMES FIRST.  The telescoping identity is
;;; (1-r).S_k = 1 - r^k, and in that shape the induction step is a pure ring
;;; identity that `crs' closes.  Introducing 1/(1-r) first would put a `recip'
;;; inside the induction, and `crs' declines any identity containing one --
;;; `recip' is not a ring operation, so the simplifier refuses the whole goal
;;; rather than treating the reciprocal as an atom.  (That is also why the last
;;; commutation below is `rr-mul-comm' and not `crs'.)  The recip form is then
;;; one citation of `rr-recip-solve', which exists for exactly this.
;;;
;;; The `-mul' form additionally carries NO `r /= 1' hypothesis, and that is not
;;; an accident of the proof: multiplying through by (1-r) is what removes the
;;; only place the guard was needed.
;;;
;;; TWO MECHANICS worth carrying away.  A conjunctive antecedent is not split by
;;; `fact' -- and rr-mul-comm, rr-mul-closed, rr-recip-closed, rr-le-scale-nonneg
;;; and rr-abs-mult ALL have one, so nearly every citation here is preceded by a
;;; `have!' of the AND.  And `prop' hits its 2^n cap on a context of this size,
;;; so the two small contradictions (1 - r /= 0 from r /= 1) are written out by
;;; hand rather than dispatched.
;;;
;;; Loads after monotone-convergence-proof (monotone-convergence-rr),
;;; comparison-test-proof (series-partial-sum-mono/-nonneg/-in-rr/-zero/-succ),
;;; dyadic-weights (power-real-closed), rr-order-basics (rr-le-scale-nonneg),
;;; rr-recip-order (rr-recip-pos) and `contra'; must PRECEDE pss-topics, which
;;; tags geometric-partial-sum.

;;; |r^k| = |r|^k  -- induction on k.
(define (ap-idx form)
  (let loop ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "ap-idx: not in context" form))
          ((equal? (car l) form) i)
          (else (loop (cdr l) (+ i 1))))))
(define (ap-ineq . fs) (apply ineq (map ap-idx fs)))
(define (ap-di-landed!)
  (let loop ((n 0))
    (let ((new (dk-landed* (lambda () (di)))))
      (cond ((pair? new) new)
            ((> n 4) (error "ap-di-landed!: nothing landed"))
            (else (loop (+ n 1)))))))

(sp (make-wff '(FORALL k (IMPLIES (IN k NN)
   (FORALL r (IMPLIES (IN r RR)
     (= (abs (power r k)) (power (abs r) k))))))))
(define ap-br (use-induction))

;;; BASE
(dk-focus! (cdr (assq 'base ap-br)))
(di)
(fact 'rr-subset-cc 'r)
(fact 'rr-abs-closed 'r)
(fact 'rr-subset-cc '(abs r))
(mac 'power-zero)
(fact 'rr-one-in)
(have! '(<= 0 1) (lambda () (arith)))
(fact 'rr-abs-of-nonneg 1)
(ass)

;;; STEP
(dk-focus! (cdr (assq 'step ap-br)))
(define ap-n  (cdr (assq 'var ap-br)))
(define ap-ih (cdr (assq 'ih  ap-br)))
(di)
(fact 'rr-subset-cc 'r)
(fact 'rr-abs-closed 'r)
(fact 'rr-subset-cc '(abs r))
(fact 'power-real-closed 'r ap-n)
(mac 'power-succ)
(have! (list 'AND '(IN r RR) (list 'IN (list 'power 'r ap-n) 'RR)))
(fact 'rr-abs-mult 'r (list 'power 'r ap-n))
(inst+ ap-ih 'r)
;; flip the IH so `subst' can walk the goal's `abs(r)^k' back to `abs(r^k)',
;; after which the goal IS the rr-abs-mult instance already in context.
(fact 'eq-sym (list 'abs (list 'power 'r ap-n)) (list 'power '(abs r) ap-n))
(subst (list '= (list 'power '(abs r) ap-n) (list 'abs (list 'power 'r ap-n))))
(ass)
(qed 'rr-abs-power)


;;; (1 - r) * S_k = 1 - r^k   -- division-free telescoping, induction on k.
(define (gp-idx form)
  (let loop ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "gp-idx: not in context" form))
          ((equal? (car l) form) i)
          (else (loop (cdr l) (+ i 1))))))
(define (gp-ineq . fs) (apply ineq (map gp-idx fs)))
(define gp-lam '(VNB-LAMBDA n NN (power r n)))

(sp (make-wff (list 'FORALL 'k (list 'IMPLIES '(IN k NN)
   (list 'FORALL 'r (list 'IMPLIES '(IN r RR)
     (list '= (list '* (list '- 1 'r) (list 'SERIES-PARTIAL-SUM gp-lam 'k))
           (list '- 1 (list 'power 'r 'k)))))))))
(define gp-br (use-induction))

(dk-focus! (cdr (assq 'base gp-br)))
(di)
(fact 'rr-subset-cc 'r)
(mac 'series-partial-sum-zero)
(mac 'power-zero)
(crs)

(dk-focus! (cdr (assq 'step gp-br)))
(define gp-n  (cdr (assq 'var gp-br)))
(define gp-ih (cdr (assq 'ih  gp-br)))
(di)
;; the lambda has to be a member of FUN(NN,RR) before any partial sum is typed
(define (gp-type-lam!)
  (have! (list 'IN gp-lam '(FUN NN RR))
    (lambda ()
      (dk-lam-t!)
      (di)
      (let ((v (caddr (cadr (dk-goal)))))      ; goal (IN (power r v) RR) -> v
        (fact 'power-real-closed 'r v))
      (ass))))
(gp-type-lam!)
(fact 'series-partial-sum-in-rr gp-n gp-lam)
(fact 'rr-subset-cc 'r)
(fact 'power-real-closed 'r gp-n)
;; the recurrence is guarded on BOTH arguments; the applied term is the lambda
;; at k, so type it by beta first.
(have! (list 'IN (list gp-lam gp-n) 'RR)
  (lambda () (lam-b) (fact 'power-real-closed 'r gp-n) (ass)))
(mac 'series-partial-sum-succ)
(lam-b)
(mac 'power-succ)
(inst+ gp-ih 'r)
;; DISTRIBUTE FIRST.  The IH is an equation in (1-r)*S, and the goal holds
;; (1-r)*(S + r^k); `subst' rewrites a literal occurrence, so the product has
;; to be opened before the IH can be used.  The distribution itself is a pure
;; ring identity, so `crs' proves it and `subst' applies it.
(define gp-S (list 'SERIES-PARTIAL-SUM gp-lam gp-n))
(define gp-rk (list 'power 'r gp-n))
(define gp-one-r '(- 1 r))
(have! (list '= (list '* gp-one-r (list '+ gp-S gp-rk))
             (list '+ (list '* gp-one-r gp-S) (list '* gp-one-r gp-rk)))
  (lambda () (crs)))
(subst (list '= (list '* gp-one-r (list '+ gp-S gp-rk))
             (list '+ (list '* gp-one-r gp-S) (list '* gp-one-r gp-rk))))
(subst (list '= (list '* gp-one-r gp-S) (list '- 1 gp-rk)))
(crs)
(qed 'geometric-partial-sum-mul)


;;; 0 <= r  =>  0 <= r^k   -- induction on k.
(define (pn-peel-to! head)
  (let loop ((n 0))
    (let ((g (dk-goal)))
      (cond ((and (pair? g) (eq? (car g) head)) g)
            ((> n 8) (error "pn-peel-to!: never reached" head))
            (else (di) (loop (+ n 1)))))))
(sp (make-wff '(FORALL k (IMPLIES (IN k NN)
   (FORALL r (IMPLIES (IN r RR) (IMPLIES (<= 0 r) (<= 0 (power r k)))))))))
(define pn-br (use-induction))

(dk-focus! (cdr (assq 'base pn-br)))
(pn-peel-to! '<=)
(fact 'rr-subset-cc 'r)
(mac 'power-zero)
(arith)

(dk-focus! (cdr (assq 'step pn-br)))
(define pn-n  (cdr (assq 'var pn-br)))
(define pn-ih (cdr (assq 'ih  pn-br)))
(pn-peel-to! '<=)
(fact 'rr-subset-cc 'r)
(fact 'power-real-closed 'r pn-n)
(mac 'power-succ)
(dk-deepest (lambda () (inst+ pn-ih 'r)))
(have! (list 'AND '(IN r RR) (list 'IN (list 'power 'r pn-n) 'RR)))
(have! (list 'AND '(<= 0 r) (list '<= 0 (list 'power 'r pn-n))))
(fact 'rr-leq-mul-nonneg 'r (list 'power 'r pn-n))
(ass)
(qed 'rr-power-nonneg)


;;; geometric-partial-sum, the recip form -- from the division-free one.
(define gp-lam '(VNB-LAMBDA n NN (power r n)))
(define (gp-peel-to! head)
  (let loop ((n 0))
    (let ((g (dk-goal)))
      (cond ((and (pair? g) (eq? (car g) head)) g)
            ((> n 8) (error "gp-peel-to!: never reached" head))
            (else (di) (loop (+ n 1)))))))

(sp (make-wff (list 'FORALL 'r (list 'IMPLIES '(AND (IN r RR) (NOT (= r 1)))
   (list 'FORALL 'k (list 'IMPLIES '(IN k NN)
     (list '= (list 'SERIES-PARTIAL-SUM gp-lam 'k)
           (list '* (list '- 1 (list 'power 'r 'k)) '(recip (- 1 r))))))))))
(gp-peel-to! '=)
(dk-split! '(AND (IN r RR) (NOT (= r 1))))
(fact 'rr-one-in)
(fact 'rr-sub-in-rr 1 'r)
(fact 'rr-subset-cc 'r)
(fact 'power-real-closed 'r 'k)
(fact 'rr-sub-in-rr 1 '(power r k))
;; the lambda, and the partial sum, as reals
(have! (list 'IN gp-lam '(FUN NN RR))
  (lambda () (dk-lam-t!) (di)
             (fact 'power-real-closed 'r (caddr (cadr (dk-goal)))) (ass)))
(fact 'series-partial-sum-in-rr 'k gp-lam)
;; 1 - r is nonzero, from r /= 1
;; `prop' hits its 2^n cap on a context this size, so the contradiction is
;; written out: assume 1 - r = 0, flip it, rr-diff-zero-eq gives 1 = r, and
;; the hypothesis r /= 1 flipped is the contradiction.
(have! '(NOT (= (- 1 r) 0))
  (lambda ()
    (di)
    (fact 'eq-sym '(- 1 r) 0)
    (fact 'rr-diff-zero-eq 1 'r)
    (fact 'neq-sym 'r 1)
    (ai '(NOT (= 1 r)))))
;; the division-free form, flipped into the shape rr-recip-solve wants
(fact 'geometric-partial-sum-mul 'k 'r)
(fact 'eq-sym (list '* '(- 1 r) (list 'SERIES-PARTIAL-SUM gp-lam 'k))
              '(- 1 (power r k)))
(fact 'rr-recip-solve '(- 1 r) '(- 1 (power r k)) (list 'SERIES-PARTIAL-SUM gp-lam 'k))
(display (expression->string (car (dk-asms)))) (newline)

;; finish the recip form
;; `crs' will not commute a product with a `recip' in it -- recip is not a ring
;; operation, so the simplifier declines the whole identity rather than treating
;; the reciprocal as an atom.  The commutation is one citation.
(subst (list '= (list 'SERIES-PARTIAL-SUM gp-lam 'k)
             (list '* '(recip (- 1 r)) '(- 1 (power r k)))))
(have! '(AND (IN (- 1 r) RR) (NOT (= (- 1 r) 0))))
(fact 'rr-recip-closed '(- 1 r))
;; rr-mul-comm has a conjunctive antecedent, like every other closure law here
(have! '(AND (IN (recip (- 1 r)) RR) (IN (- 1 (power r k)) RR)))
(fact 'rr-mul-comm '(recip (- 1 r)) '(- 1 (power r k)))
(ass)
(qed 'geometric-partial-sum)


;;; =====================================================================
;;; The geometric series CONVERGES for 0 <= r < 1.
;;; =====================================================================
(define gs-lam '(VNB-LAMBDA n NN (power r n)))
(define gs-g   (list 'VNB-LAMBDA 'k 'NN (list 'SERIES-PARTIAL-SUM gs-lam 'k)))
(define (gs-idx form)
  (let loop ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "gs-idx: not in context" form))
          ((equal? (car l) form) i)
          (else (loop (cdr l) (+ i 1))))))
(define (gs-ineq . fs) (apply ineq (map gs-idx fs)))
(define (gs-peel-to! head)
  (let loop ((n 0))
    (let ((g (dk-goal)))
      (cond ((and (pair? g) (eq? (car g) head)) g)
            ((> n 8) (error "gs-peel-to!: never reached" head))
            (else (di) (loop (+ n 1)))))))

(sp (make-wff (list 'FORALL 'r (list 'IMPLIES '(IN r RR)
   (list 'IMPLIES '(<= 0 r) (list 'IMPLIES '(< r 1)
     (list 'SERIES-CONVERGES gs-lam)))))))
(gs-peel-to! 'SERIES-CONVERGES)
(mac 'series-converges)
(have! '(NOT (= r 1)) (lambda () (di) (contra)))
;; groundwork: the term lambda is real-valued, its terms are nonnegative, and
;; 1 - r is a nonzero real with a nonnegative reciprocal.
(fact 'rr-one-in)
(fact 'rr-sub-in-rr 1 'r)
(fact 'rr-subset-cc 'r)
(have! (list 'IN gs-lam '(FUN NN RR))
  (lambda () (dk-lam-t!) (di)
             (fact 'power-real-closed 'r (caddr (cadr (dk-goal)))) (ass)))
(define gs-nonneg
  (list 'FORALL 'i_ (list 'IMPLIES '(IN i_ NN) (list '<= 0 (list gs-lam 'i_)))))
(have! gs-nonneg
  (lambda () (di) (lam-b)
             (fact 'power-real-closed 'r 'i_)
             (fact 'rr-power-nonneg 'i_ 'r) (ass)))
(have! '(NOT (= (- 1 r) 0))
  (lambda () (di)
             (fact 'eq-sym '(- 1 r) 0)
             (fact 'rr-diff-zero-eq 1 'r)
             (fact 'neq-sym 'r 1)
             (ai '(NOT (= 1 r)))))
(have! '(AND (IN (- 1 r) RR) (NOT (= (- 1 r) 0))))
(fact 'rr-recip-closed '(- 1 r))
(have! '(< 0 (- 1 r)) (lambda () (gs-ineq '(< r 1))))
(fact 'rr-recip-pos '(- 1 r))
;; the partial-sum sequence is real-valued
(have! (list 'IN gs-g '(FUN NN RR))
  (lambda () (dk-lam-t!) (di)
             (fact 'series-partial-sum-in-rr (caddr (cadr (dk-goal))) gs-lam)
             (ass)))

;; NONDECREASING
(define gs-mono
  (list 'FORALL 'k (list 'IMPLIES '(IN k NN)
     (list '<= (list gs-g 'k) (list gs-g '(succ k))))))
(have! gs-mono
  (lambda ()
    (di)
    (fact 'nn-succ-closed 'k)
    (lam-b)                     ; one call rewrites BOTH applications
    (fact 'nn-le-succ 'k)
    (fact 'series-partial-sum-mono '(succ k) 'k gs-lam)
    (ass)))
;; BOUNDED ABOVE by 1/(1-r)
(define gs-bdd
  (list 'FORSOME 'bnd (list 'AND '(IN bnd RR)
     (list 'FORALL 'k (list 'IMPLIES '(IN k NN) (list '<= (list gs-g 'k) 'bnd))))))
(have! gs-bdd
  (lambda ()
    (ew '(recip (- 1 r)))
    (for-each
     (lambda (l)
       (dk-focus! l)
       (if (eq? (car (dk-goal)) 'IN)
           (ass)
           (begin
             (di)
             (lam-b)
             (fact 'power-real-closed 'r 'k)
             (fact 'rr-sub-in-rr 1 '(power r k))
             (fact 'rr-power-nonneg 'k 'r)
             ;; rr-le-scale-nonneg-right wants BOTH the ordering and 0 <= c
             (have! '(<= (- 1 (power r k)) 1)
               (lambda () (gs-ineq '(<= 0 (power r k)))))
             (fact 'rr-lt-implies-le 0 '(recip (- 1 r)))
             ;; every atom `ineq' will see needs an IN _ RR certificate
             (fact 'series-partial-sum-in-rr 'k gs-lam)
             (have! '(AND (IN (- 1 (power r k)) RR) (IN (recip (- 1 r)) RR)))
             (fact 'rr-mul-closed '(- 1 (power r k)) '(recip (- 1 r)))
             (have! '(AND (IN 1 RR) (IN (recip (- 1 r)) RR)))
             (fact 'rr-mul-closed 1 '(recip (- 1 r)))
             (have! '(AND (IN r RR) (NOT (= r 1))))
             (fact 'geometric-partial-sum 'r 'k)
             ;; rr-le-scale-nonneg (LEFT form) is PROVEN; its `-right' sibling is
             ;; an asserted support, so the commutations are cheaper than the bill.
             ;; ... and its antecedent is a conjunction, like everything else here
             (have! '(AND (<= 0 (recip (- 1 r))) (<= (- 1 (power r k)) 1)))
             (fact 'rr-le-scale-nonneg '(recip (- 1 r)) '(- 1 (power r k)) 1)
             (have! '(AND (IN (recip (- 1 r)) RR) (IN (- 1 (power r k)) RR)))
             (fact 'rr-mul-closed '(recip (- 1 r)) '(- 1 (power r k)))
             (fact 'rr-mul-comm '(- 1 (power r k)) '(recip (- 1 r)))
             (have! '(AND (IN (recip (- 1 r)) RR) (IN 1 RR)))
             (fact 'rr-mul-closed '(recip (- 1 r)) 1)
             (fact 'rr-mul-comm '(recip (- 1 r)) 1)
             (fact 'rr-one-mul '(recip (- 1 r)))
             (gs-ineq (list '= (list 'SERIES-PARTIAL-SUM gs-lam 'k)
                            '(* (- 1 (power r k)) (recip (- 1 r))))
                      '(= (* (- 1 (power r k)) (recip (- 1 r)))
                          (* (recip (- 1 r)) (- 1 (power r k))))
                      '(<= (* (recip (- 1 r)) (- 1 (power r k))) (* (recip (- 1 r)) 1))
                      '(= (* (recip (- 1 r)) 1) (* 1 (recip (- 1 r))))
                      '(= (* 1 (recip (- 1 r))) (recip (- 1 r)))))))
     (dk-opened (lambda () (di))))))
;; monotone-convergence-rr takes its two clauses as ONE conjunction
(have! (list 'AND gs-mono gs-bdd))
(fact 'monotone-convergence-rr gs-g)
(ass)
(qed 'geometric-series-converges)

(topic! 'rr-abs-power 'analysis)
(alias! 'rr-abs-power "the modulus of a power is the power of the modulus")
(topic! 'rr-power-nonneg 'inequalities)
(alias! 'rr-power-nonneg "a power of a nonnegative real is nonnegative")
(topic! 'geometric-partial-sum-mul 'analysis)
(alias! 'geometric-partial-sum-mul "the geometric partial sum, cleared of its denominator")
(topic! 'geometric-partial-sum 'analysis)
(topic! 'geometric-series-converges 'analysis)
(alias! 'geometric-series-converges "the geometric series converges for 0 <= r < 1")
