;;; dyadic-weights.scm -- THE CANONICAL PRODUCT-METRIC WEIGHTS ARE SUMMABLE,
;;; proven -- retiring `product-metric-default-summable'
;;; (structure-library/product-metric.scm), the last asserted support of that
;;; file that is not blocked on a bridge somebody else is proving:
;;;
;;;     SUMMABLE-WEIGHT( n |-> 1 / 2^(n+1) ).
;;;
;;; SUMMABLE-WEIGHT asks three things: the sequence is in FUN(NN,RR), every
;;; term is strictly positive, and the series converges.  The first two are
;;; plumbing.  The third is the closed form
;;;
;;;     SERIES-PARTIAL-SUM(w, k)  =  1 - 2^-k                (dyadic-partial-sum)
;;;
;;; by induction on k, which delivers BOTH hypotheses of `monotone-convergence-rr'
;;; at once -- nondecreasing (the terms are positive) and bounded above by 1
;;; (2^-k > 0) -- so the convergence is one citation and no eps/N argument.
;;;
;;; NOT VIA THE GEOMETRIC SERIES.  `geometric-series-converges-to' is itself
;;; ASSERTED, it gives SUM r^n = 1/(1-r) where this wants SUM 2^-(n+1), and
;;; bridging the two needs a scalar multiple of a convergent series, which the
;;; tree does not have.  The direct route needs none of that.
;;;
;;; THE OBSTACLE, AND THE MECHANISM THAT DISSOLVES IT.  `crs' -- the commutative
;;; ring simplifier, which every other arithmetic identity in the tree is closed
;;; by -- CANNOT SEE EITHER OF THE TWO HEADS THIS FILE IS MADE OF:
;;;
;;;   * on a goal containing `recip' it declines, reporting "goal is not a
;;;     provable commutative-ring identity" -- even for  recip(a) = recip(a) * 1;
;;;   * on a goal containing a SYMBOLIC power  2^k  it CRASHES, with
;;;     ";; VNB error: The object #f, passed as an argument to exact?, is not
;;;     the correct type" (so does `rfl' on such a term).
;;;
;;; The dissolution is one move, and it is why this file has three lemmas that
;;; look like nothing: STATE THE IDENTITY OVER RR VARIABLES, WHERE `crs' WORKS,
;;; AND INSTANTIATE IT AT THE recip/power TERM.  `rr-scaled-inverse-unique'
;;; (a*u = 1 and (2a)*v = 1 give u = 2v) and `rr-halving-identity'
;;; ((1 - 2b) + b = 1 - b) are exactly that: their proofs are pure `crs', and
;;; every recip step of this file is one `fact' of one of them.  No cancellation
;;; lemma and no uniqueness-of-inverses axiom is needed -- the chain
;;;
;;;     u = u*((2a)v) = (au)(2v) = 2v
;;;
;;; multiplies by 1 twice and is closed by `calc' in three links, each a `crs'
;;; identity after one `subst'.
;;;
;;; `calc' (calc.scm) is the tool for that chain and it is worth naming: it cuts
;;; each link, dispatches a lane, and folds the links with `eq-trans'.  Its
;;; justifications are EVAL'd in `user-initial-environment', so a file-local
;;; helper is NOT visible inside one -- the two justifications here are
;;; `(begin (subst (quote ...)) (crs))', built from globals only.
;;;
;;; TWO SMALLER TRAPS, both of which cost a run:
;;;
;;;   * `subst' rewrites LEFT to RIGHT only.  A landed  succ(k) = k + 1  will
;;;     NOT turn a goal's  k + 1  back into  succ(k); it warns "equality not in
;;;     context, or nothing to rewrite" and no-ops.  `eq-sym' first, then subst.
;;;     The weights are written with  n + 1  and `power-succ' is stated at
;;;     `succ n', so this conversion happens in every lemma below.
;;;   * the surface `(2 * a) * v' PARSES FLAT, to (* 2 a v).  A `subst' or an
;;;     `ass' built from the nested (* (* 2 a) v) then matches nothing.  The
;;;     statement of `rr-scaled-inverse-unique' is therefore a raw
;;;     S-expression, not a `make-wff' of a surface string.
;;;
;;; ALSO RETIRED HERE: `power-real-closed' (power-series.scm), asserted
;;; `well-known' since that file was written, with the warrant "Induction on n:
;;; x^0 = 1 in RR; x^{n+1} = x * x^n ... a candidate to discharge into a formal
;;; `proof' later".  It had NO citer in the tree.  It is that induction, twelve
;;; lines, and it is proved here because `power-two-pos' immediately below it is
;;; the same induction one storey up and would otherwise have billed it.
;;;
;;; WHAT IT COSTS.  `product-metric-default-summable' bills
;;; `modulo {nn-add-succ, nn-zero-le, nn-le-succ-cases}' [trust: well-known] --
;;; the NN-order/arithmetic backlog of structure-library/{nn-arith,order-lemmas}
;;; and nothing else.  Two of the three are inherited through
;;; `monotone-convergence-rr'; `nn-add-succ' comes in through
;;; `nn-succ-plus-one', i.e. through the fact that the weights are written
;;; 2^-(n+1) and the recursion is stated at `succ'.
;;;
;;; Loads after theorem-library/comparison-test-proof (series-partial-sum-*),
;;; monotone-convergence-proof (monotone-convergence-rr), rr-recip-order
;;; (rr-mul-pos, rr-recip-pos), nn-parity-proof (nn-succ-plus-one),
;;; equality-basics (eq-sym, eq-trans), calc, and structure-library/product-metric
;;; (SUMMABLE-WEIGHT).

;;; ---- file-local driver helpers (the `dw-' prefix) --------------------

(define (dw-find what pred)
  (let loop ((l (dk-asms)))
    (cond ((null? l) (error "dw-find: no context formula" what))
          ((pred (car l)) (car l)) (else (loop (cdr l))))))
(define (dw-idx form)
  (let loop ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "dw-idx: not in context" form))
          ((equal? (car l) form) i) (else (loop (cdr l) (+ i 1))))))
(define (dw-ineq . fs) (apply ineq (map dw-idx fs)))
(define (dw-and! closer)
  (let ((g (dk-goal)))
    (if (and (pair? g) (eq? (car g) 'AND))
        (for-each (lambda (k) (dk-focus! k) (dw-and! closer))
                  (dk-opened (lambda () (di))))
        (closer))))
(define (dw-di-landed!)
  (let loop ((n 0))
    (let ((new (dk-landed* (lambda () (di)))))
      (cond ((pair? new) new)
            ((> n 4) (error "dw-di-landed!: nothing landed"))
            (else (loop (+ n 1)))))))
(define (dw-di-landed-1!)
  (let ((new (dw-di-landed!)))
    (if (null? (cdr new)) (car new) (error "dw-di-landed-1!" new))))
;; (NOT (= t 0)) from a context (< 0 t), on a side branch
(define (dw-nonzero! t)
  (have! (list 'NOT (list '= t 0))
    (lambda ()
      (mac-h '< (list '< 0 t))
      (dk-split! (list 'AND (list '<= 0 t) (list 'NOT (list '= 0 t))))
      (fact 'neq-sym 0 t)
      (ass))))
;; everything about recip(t) for a t already known positive and real
(define (dw-recip! t)
  (dw-nonzero! t)
  (have! (list 'AND (list 'IN t 'RR) (list 'NOT (list '= t 0))))
  (fact 'rr-recip-inverse t)
  (fact 'rr-recip-closed t)
  (fact 'rr-recip-pos t))

;;; ---- x^n is real -------------------------------------------------
;;; Retires the asserted `power-real-closed' of power-series.scm.  The
;;; induction variable is OUTERMOST (`ni' tests the goal's shape literally), so
;;; the statement the support carried is recovered from it in three lines.
(sp (make-wff '(FORALL n (IMPLIES (IN n NN)
   (FORALL x (IMPLIES (IN x RR) (IN (power x n) RR)))))))
(define dw0-br (use-induction))

(dk-focus! (cdr (assq 'base dw0-br)))
(dk-peel-to! 'IN)
(fact 'rr-subset-cc 'x)
(mac 'power-zero)
(fact 'rr-one-in)
(ass)

(dk-focus! (cdr (assq 'step dw0-br)))
(define dw0-n  (cdr (assq 'var dw0-br)))
(define dw0-ih (cdr (assq 'ih  dw0-br)))
(dk-peel-to! 'IN)
(define dw0-x (cadr (cadr (dk-goal))))
(fact 'rr-subset-cc dw0-x)
(have! (list 'AND (list 'IN dw0-x 'CC) (list 'IN dw0-n 'NN)))
(fact 'power-succ dw0-x dw0-n)
(subst (list '= (list 'power dw0-x (list 'succ dw0-n))
                (list '* dw0-x (list 'power dw0-x dw0-n))))
(inst+ dw0-ih dw0-x)
(have! (list 'AND (list 'IN dw0-x 'RR) (list 'IN (list 'power dw0-x dw0-n) 'RR)))
(fact 'rr-mul-closed dw0-x (list 'power dw0-x dw0-n))
(ass)
(qed 'power-closed-at)
(topic! 'power-closed-at 'analysis)
(alias! 'power-closed-at "a real power is real, by induction on the exponent")

;;; the statement `power-real-closed' carried in power-series.scm, verbatim
(sp (make-wff '(FORALL x (IMPLIES (IN x RR)
   (FORALL n (IMPLIES (IN n NN) (IN (power x n) RR)))))))
(di)                                    ; a GUARDED universal goes whole under one `di'
(fact 'power-closed-at 'n 'x)
(ass)
(qed 'power-real-closed)
(topic! 'power-real-closed 'plumbing)
(alias! 'power-real-closed "a real power is real")

;;; ---- 0 < 2 -------------------------------------------------------
(sp (make-wff '(< 0 2)))
(arith)
(qed 'rr-zero-lt-two)
(topic! 'rr-zero-lt-two 'inequalities)
(alias! 'rr-zero-lt-two "zero is less than two")

;;; ---- 0 < 2^k -----------------------------------------------------
(sp (make-wff '(FORALL k (IMPLIES (IN k NN) (< 0 (power 2 k))))))
(define dw-br (use-induction))
(dk-focus! (cdr (assq 'base dw-br)))
(have! '(IN 2 CC) (lambda () (arith)))
(mac 'power-zero)
(arith)
(dk-focus! (cdr (assq 'step dw-br)))
(define dw-k (cdr (assq 'var dw-br)))
(have! '(IN 2 CC) (lambda () (arith)))
(have! '(IN 2 RR) (lambda () (arith)))
(have! (list 'AND '(IN 2 CC) (list 'IN dw-k 'NN)))
(fact 'power-succ 2 dw-k)
(subst (list '= (list 'power 2 (list 'succ dw-k)) (list '* 2 (list 'power 2 dw-k))))
(fact 'power-real-closed 2 dw-k)
(fact 'rr-zero-lt-two)
(fact 'rr-mul-pos 2 (list 'power 2 dw-k))
(ass)
(qed 'power-two-pos)
(topic! 'power-two-pos 'inequalities)
(alias! 'power-two-pos "every power of two is positive")

;;; ---- u = 2v from a*u = 1 and (2a)*v = 1 --------------------------
(sp (make-wff '(FORALL a (IMPLIES (IN a RR)
   (FORALL u (IMPLIES (IN u RR)
     (FORALL v (IMPLIES (IN v RR)
       (IMPLIES (= (* a u) 1)
         (IMPLIES (= (* (* 2 a) v) 1)
           (= u (* 2 v))))))))))))
(di)(di)(di)
(calc 'u
  '(= (* u (* (* 2 a) v)) (begin (subst '(= (* (* 2 a) v) 1)) (crs)))
  '(= (* (* a u) (* 2 v)) (crs))
  '(= (* 2 v) (begin (subst '(= (* a u) 1)) (crs))))
(qed 'rr-scaled-inverse-unique)
(topic! 'rr-scaled-inverse-unique 'inequalities)
(alias! 'rr-scaled-inverse-unique
        "the inverse of twice a number is half its inverse")

;;; ---- recip(2^k) = 2 recip(2 * 2^k) -------------------------------
(define dw-P '(power 2 k))
(define dw-Q (list '* 2 dw-P))
(sp (make-wff (list 'FORALL 'k (list 'IMPLIES '(IN k NN)
    (list '= (list 'recip dw-P) (list '* 2 (list 'recip dw-Q)))))))
(di)                                    ; a GUARDED universal goes whole under one `di'
(have! '(IN 2 RR) (lambda () (arith)))
(fact 'rr-zero-lt-two)
(fact 'power-real-closed 2 'k)
(fact 'power-two-pos 'k)
(dw-recip! dw-P)
(have! (list 'AND '(IN 2 RR) (list 'IN dw-P 'RR)))
(fact 'rr-mul-closed 2 dw-P)
(fact 'rr-mul-pos 2 dw-P)
(dw-recip! dw-Q)
(fact 'rr-scaled-inverse-unique dw-P (list 'recip dw-P) (list 'recip dw-Q))
(ass)
(qed 'recip-power-two-halves)
(topic! 'recip-power-two-halves 'analysis)
(alias! 'recip-power-two-halves "2^-k is twice 2^-(k+1)")

;;; ---- the dyadic weight sequence ----------------------------------
(define DW '(VNB-LAMBDA n NN (/ 1 (power 2 (+ n 1)))))

(sp (make-wff (list 'FORALL 'k (list 'IMPLIES '(IN k NN)
    (list '= (list DW 'k) '(recip (power 2 (succ k))))))))
(di)                                    ; a GUARDED universal goes whole under one `di'
(lam-b)
(fact 'nn-succ-plus-one 'k)
(subst '(= (succ k) (+ k 1)))
(mac 'binary-divide-def)
(fact 'nn-succ-closed 'k)
(fact 'eq-sym '(succ k) '(+ k 1))
(have! '(IN (+ k 1) NN) (lambda () (subst '(= (+ k 1) (succ k))) (ass)))
(have! '(IN 2 RR) (lambda () (arith)))
(fact 'power-real-closed 2 '(+ k 1))
(fact 'power-two-pos '(+ k 1))
(dw-recip! '(power 2 (+ k 1)))
(fact 'rr-one-mul '(recip (power 2 (+ k 1))))
(ass)
(qed 'dyadic-weight-apply)
(topic! 'dyadic-weight-apply 'analysis)
(alias! 'dyadic-weight-apply "the n-th canonical product weight is 2^-(n+1)")

;;; ---- (1 - 2b) + b = 1 - b, over a VARIABLE (crs cannot see recip) ----
(sp (make-wff '(FORALL b (IMPLIES (IN b RR) (= (+ (- 1 (* 2 b)) b) (- 1 b))))))
(di)                                    ; a GUARDED universal goes whole under one `di'
(crs)
(qed 'rr-halving-identity)
(topic! 'rr-halving-identity 'inequalities)
(alias! 'rr-halving-identity "(1 - 2b) + b = 1 - b")

;;; ---- the weight sequence is a real sequence ----------------------
(sp (make-wff (list 'IN DW '(FUN NN RR))))
(dk-lam-t!)
(define dw-n (cadr (dw-di-landed-1!)))
(fact 'nn-succ-plus-one dw-n)
(fact 'eq-sym (list 'succ dw-n) (list '+ dw-n 1))
(have! (list 'IN (list '+ dw-n 1) 'NN)
  (lambda () (subst (list '= (list '+ dw-n 1) (list 'succ dw-n)))
             (fact 'nn-succ-closed dw-n) (ass)))
(have! '(IN 2 RR) (lambda () (arith)))
(fact 'rr-zero-lt-two)
(fact 'power-real-closed 2 (list '+ dw-n 1))
(fact 'power-two-pos (list '+ dw-n 1))
(dw-recip! (list 'power 2 (list '+ dw-n 1)))
(mac 'binary-divide-def)
(fact 'rr-one-mul (list 'recip (list 'power 2 (list '+ dw-n 1))))
(subst (list '= (list '* 1 (list 'recip (list 'power 2 (list '+ dw-n 1))))
                (list 'recip (list 'power 2 (list '+ dw-n 1)))))
(ass)
(qed 'dyadic-weight-in-fun)
(topic! 'dyadic-weight-in-fun 'analysis)
(alias! 'dyadic-weight-in-fun "the canonical product weights are a real sequence")

;;; ---- every weight is positive ------------------------------------
(sp (make-wff (list 'FORALL 'n_ (list 'IMPLIES '(IN n_ NN) (list '< 0 (list DW 'n_))))))
(di)                                    ; a GUARDED universal goes whole under one `di'
(fact 'dyadic-weight-apply 'n_)
(subst (list '= (list DW 'n_) '(recip (power 2 (succ n_)))))
(fact 'nn-succ-closed 'n_)
(have! '(IN 2 RR) (lambda () (arith)))
(fact 'power-real-closed 2 '(succ n_))
(fact 'power-two-pos '(succ n_))
(dw-recip! '(power 2 (succ n_)))
(ass)
(qed 'dyadic-weight-pos)
(topic! 'dyadic-weight-pos 'analysis)
(alias! 'dyadic-weight-pos "the canonical product weights are positive")

;;; ---- the closed-form partial sum:  Sum_{n<k} 2^-(n+1) = 1 - 2^-k ----
(sp (make-wff (list 'FORALL 'k (list 'IMPLIES '(IN k NN)
    (list '= (list 'SERIES-PARTIAL-SUM DW 'k) '(- 1 (recip (power 2 k))))))))
(define dw2-br (use-induction))

(dk-focus! (cdr (assq 'base dw2-br)))
(mac 'series-partial-sum-zero)
(have! '(IN 2 CC) (lambda () (arith)))
(mac 'power-zero)
(fact 'rr-one-in)
(have! '(NOT (= 1 0)) (lambda () (arith)))
(have! '(AND (IN 1 RR) (NOT (= 1 0))))
(fact 'rr-recip-inverse 1)                    ; 1 * recip 1 = 1
(fact 'rr-recip-closed 1)
(fact 'rr-one-mul '(recip 1))                 ; 1 * recip 1 = recip 1
(fact 'eq-sym '(* 1 (recip 1)) '(recip 1))    ; recip 1 = 1 * recip 1
(fact 'eq-trans '(recip 1) '(* 1 (recip 1)) 1)
(subst '(= (recip 1) 1))
(arith)

(dk-focus! (cdr (assq 'step dw2-br)))
(define dw2-k (cdr (assq 'var dw2-br)))
(define dw2-ih (cdr (assq 'ih dw2-br)))
(have! '(IN 2 CC) (lambda () (arith)))
(have! '(IN 2 RR) (lambda () (arith)))
(mac 'series-partial-sum-succ)
(subst dw2-ih)
(fact 'dyadic-weight-apply dw2-k)
(subst (list '= (list DW dw2-k) (list 'recip (list 'power 2 (list 'succ dw2-k)))))
(have! (list 'AND '(IN 2 CC) (list 'IN dw2-k 'NN)))
(fact 'power-succ 2 dw2-k)
(subst (list '= (list 'power 2 (list 'succ dw2-k)) (list '* 2 (list 'power 2 dw2-k))))
(fact 'recip-power-two-halves dw2-k)
(subst (list '= (list 'recip (list 'power 2 dw2-k))
                (list '* 2 (list 'recip (list '* 2 (list 'power 2 dw2-k))))))
(fact 'rr-zero-lt-two)
(fact 'power-real-closed 2 dw2-k)
(fact 'power-two-pos dw2-k)
(have! (list 'AND '(IN 2 RR) (list 'IN (list 'power 2 dw2-k) 'RR)))
(fact 'rr-mul-closed 2 (list 'power 2 dw2-k))
(fact 'rr-mul-pos 2 (list 'power 2 dw2-k))
(dw-recip! (list '* 2 (list 'power 2 dw2-k)))
(fact 'rr-halving-identity (list 'recip (list '* 2 (list 'power 2 dw2-k))))
(ass)
(qed 'dyadic-partial-sum)
(topic! 'dyadic-partial-sum 'analysis)
(alias! 'dyadic-partial-sum
        "the partial sums of the dyadic series are 1 - 2^-k")

;;; ---- SUMMABLE-WEIGHT(2^-(n+1)) ------------------------------------
(define DWSEQ (list 'VNB-LAMBDA 'k 'NN (list 'SERIES-PARTIAL-SUM DW 'k)))

(sp (make-wff (list 'SUMMABLE-WEIGHT DW)))
(mac 'summable-weight)
(fact 'dyadic-weight-in-fun)
(fact 'dyadic-weight-pos)
(fact 'rr-one-in)
;; the nonnegative form of positivity, which the partial-sum lemmas want
(have! (list 'FORALL 'n_ (list 'IMPLIES '(IN n_ NN) (list '<= 0 (list DW 'n_))))
  (lambda ()
    (let ((n (cadr (dw-di-landed-1!))))
      (inst+ (dw-find 'pos (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                                            (dk-contains? a '<)))) n)
      (mac-h '< (list '< 0 (list DW n)))
      (dk-split! (list 'AND (list '<= 0 (list DW n))
                       (list 'NOT (list '= 0 (list DW n)))))
      (ass))))
(define dw-nonneg
  (dw-find 'nonneg (lambda (a) (and (pair? a) (eq? (car a) 'FORALL) (dk-contains? a '<=)))))

(have! (list 'IN DWSEQ '(FUN NN RR))
  (lambda () (fact 'series-partial-sum-seq-in-fun DW) (ass)))

(have! (list 'FORALL 'k (list 'IMPLIES '(IN k NN)
                              (list '<= (list DWSEQ 'k) (list DWSEQ '(succ k)))))
  (lambda ()
    (let ((k (cadr (dw-di-landed-1!))))
      (fact 'nn-succ-closed k)
      (mac 'series-partial-sum-seq-apply)
      (fact 'series-partial-sum-monotone-nonneg DW k)
      (ass))))

(define dw-mcrr (let ((t (lookup-theorem 'monotone-convergence-rr)))
                  (if (wff? t) (wff-formula t) t)))
(define dw-mc-ante (subst-free 'f DWSEQ (cadr (caddr (caddr dw-mcrr)))))

(dw-and!
 (lambda ()
   (let ((g (dk-goal)))
     (cond
       ((eq? (car g) 'IN) (ass))
       ((eq? (car g) 'FORALL) (ass))
       (else
        (mac 'series-converges)
        (have! dw-mc-ante
          (lambda ()
            (dw-and!
             (lambda ()
               (let ((g2 (dk-goal)))
                 (cond
                   ((eq? (car g2) 'FORALL) (ass))
                   (else
                    (ew 1)
                    (dw-and!
                     (lambda ()
                       (if (eq? (car (dk-goal)) 'IN)
                           (ass)
                           (let ((k (cadr (dw-di-landed-1!))))
                             (mac 'series-partial-sum-seq-apply)
                             (fact 'dyadic-partial-sum k)
                             (subst (list '= (list 'SERIES-PARTIAL-SUM DW k)
                                             (list '- 1 (list 'recip (list 'power 2 k)))))
                             (have! '(IN 2 RR) (lambda () (arith)))
                             (fact 'power-real-closed 2 k)
                             (fact 'power-two-pos k)
                             (dw-recip! (list 'power 2 k))
                             (dw-ineq (list '< 0 (list 'recip (list 'power 2 k)))))))))))))))
        (fact 'monotone-convergence-rr DWSEQ)
        (ass))))))
(qed 'product-metric-default-summable)
(topic! 'product-metric-default-summable 'analysis)
(alias! 'product-metric-default-summable
        "the canonical product-metric weights are summable")
