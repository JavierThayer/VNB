;;; theorem-library/taylor-g-diff.scm -- the derivative of the Taylor remainder
;;; in the CENTRE:  G(z) = f(x) - TAYLOR-POLY(f, z, n, x)  has, at any t with
;;; a < t < x,
;;;
;;;     G'(t) = 0 - (recip(n!) * f^(n+1)(t)) * (x - t)^n .
;;;
;;; This is `taylor-G-diff' of taylor-proof.scm, which was an `add-to-pss' +
;;; `warrant! 'reference' whose text WAS the telescoping argument, written out
;;; and never run.  It is proven here, `modulo 0', with ONE deliberate change of
;;; statement (the user's decision, 2026-09-14): the triage found the support
;;; FALSE AS WRITTEN because `n' was unguarded (off NN the sum, the power and
;;; the factorial mean nothing).  The statement below is the support's with two
;;; leading antecedents added and nothing else touched:
;;;
;;;     (IN n NN)   -- the guard the triage asked for;
;;;     (IN x RR)   -- the Taylor point is real.  Nothing in
;;;                    TAYLOR-DIFFERENTIABLE types x (it mentions x only inside
;;;                    CCINT and `<'), and (x - z)^k is real only for real x.
;;;
;;; Nothing else had to be added, and two things one might expect to need are
;;; DERIVED from TAYLOR-DIFFERENTIABLE rather than assumed:  (IN t RR), and the
;;; typing  (NTH-DERIV f k) in FUN(RR,RR)  for every k <= n.  Both sit inside
;;; IS-DIFF-AT (its first two conjuncts), and TD's second conjunct at k and t
;;; is exactly such an IS-DIFF-AT.  So the citing proof (taylor-lagrange, which
;;; has f, a, x in RR, n in NN and t = theta in context) detaches the new
;;; antecedents automatically.
;;;
;;; PLAN.  Unfold TAYLOR-POLY:  G(z) = f(x) - SPS(term_z, succ n)  where
;;;   term_z = k |-> f^(k)(z) (x-z)^k recip(k!)      (z FREE in the summand).
;;; The content is the derivative of  z |-> SPS(term_z, succ m),  by INDUCTION
;;; ON m (degree OUTERMOST so `ni' fires; CLAUDE.md on greedy `di'):
;;;
;;;   S_m'(t) = V_m := recip(m!) f^(m+1)(t) (x-t)^m
;;;
;;;   base  SPS(term_z, succ 0) == f(z) pointwise, so S_0' = f' by transfer
;;;         (diff-transfer-ptwise-eq), and V_0 = f^(1)(t) after 0! = 1,
;;;         (x-t)^0 = 1.
;;;   step  SPS(term_z, succ succ m) == S_m(z) + T_{m+1}(z) pointwise
;;;         (series-partial-sum-succ), where T_{m+1} is the summand at succ m
;;;         as a function of z.  deriv-sum, then transfer.  The TELESCOPING is
;;;         entirely in the value of T_{m+1}':  it is  V_{m+1} - V_m  (lemma
;;;         tgd-term-diff below), so  S_{m+1}' = V_m + (V_{m+1} - V_m) = V_{m+1}
;;;         and the induction step owes NO arithmetic beyond that one identity.
;;;
;;; tgd-term-diff is the product rule twice (f^(m+1) . (x-z)^(succ m), then
;;; . recip((succ m)!) as a constant), with d/dz (x-z)^(succ m) by the chain
;;; rule (deriv-chain on deriv-power and d/dz (x-z) = -1, transferred through
;;; compose-apply), and its value collapses to V_{m+1} - V_m by ONE ring
;;; identity over six variables (tgd-step-identity, `crs') once
;;;   recip(m!) = (succ m) recip((succ m)!)          (tgd-recip-factorial-succ)
;;; has been substituted -- that equation is the whole of the telescoping.
;;;
;;; The pointwise hypotheses the induction carries are
;;;   DH(f,t,m) = forall k <= m. IS-DIFF-AT (NTH-DERIV f k) t ((NTH-DERIV f (succ k)) t)
;;; which TD supplies at any t in (a,x); the step weakens DH(succ m) to DH(m)
;;; exactly as taylor-center-partial-sum weakens its guard (nn-le-trans-guarded).
;;;
;;; DUPLICATES, deliberate.  `rr-recip-one', `factorial-real-pos' and
;;; `recip-factorial-in-rr' are proven in taylor-proof.scm -- ABOVE this file's
;;; window, since taylor-proof is the citer.  They are re-proven here under the
;;; tgd- prefix (three short proofs); the integrator may instead hoist those
;;; three out of taylor-proof.scm into a file below this one and drop the copies.
;;;
;;; LOAD WINDOW [lo, hi):  hi = taylor-proof (the citer).  lo = the latest of:
;;; deriv-power (the power rule), comparison-test-proof (series-partial-sum-
;;; zero/-succ), chain-rule (deriv-chain), compose-apply-proof, deriv-sum-
;;; product, diff-transfer, mvt-cluster-readoffs (deriv-neg, diff-value-real),
;;; higher-derivatives (nth-deriv-zero), inverse-function (rr-recip-solve),
;;; nn-parity-proof (nn-succ-nonzero), dyadic-weights (power-closed-at), power-
;;; series (SERIES-PARTIAL-SUM).  All precede deriv-power in load.scm, so the
;;; file goes anywhere after deriv-power and before taylor-proof.
;;;
;;; Helper prefix: tgd-.  Every top-level define is prefixed (case folding:
;;; `tgd-PW' and `tgd-pw' are ONE name, which cost this file a probe).
;;; ====================================================================

;;; ---- file-local helpers ----
(define (tgd-di-var!) (cadr (car (dk-landed (lambda () (di))))))
(define (tgd-split-ands!)
  (let loop ((n 0))
    (let ((tgt (any-pred (lambda (a) (and (pair? a) (memq (car a) '(AND FORSOME)))) (dk-asms))))
      (if (and tgt (< n 20)) (begin (ai tgt) (loop (+ n 1)))))))
;; read a conjunct of an IS-DIFF-AT hypothesis WITHOUT destroying it (mac-h
;; replaces the assumption; the unfold happens on the have! side branch)
(define (tgd-proj! hyp claim)
  (have! claim (lambda () (mac-h 'IS-DIFF-AT hyp) (tgd-split-ands!) (ass))))
(define (tgd-mentions? sym f)
  (cond ((eq? f sym) #t)
        ((pair? f) (or (tgd-mentions? sym (car f)) (tgd-mentions? sym (cdr f))))
        (#t #f)))
(define (tgd-find pred what)
  (or (any-pred pred (dk-asms)) (error "taylor-g-diff: no assumption" what)))

;;; the shapes
(define (tgd-term f x)          ; the Taylor summand  k |-> f^(k)(z) (x-z)^k recip(k!),  z FREE
  (list 'VNB-LAMBDA 'k 'NN
        (list '* (list '* (list (list 'NTH-DERIV f 'k) 'z) (list 'power (list '- x 'z) 'k))
                 (list 'recip (list 'FACTORIAL 'k)))))
(define (tgd-term-lam f x k)    ; z |-> f^(k)(z) (x-z)^k recip(k!)
  (list 'VNB-LAMBDA 'z 'RR
        (list '* (list '* (list (list 'NTH-DERIV f k) 'z) (list 'power (list '- x 'z) k))
                 (list 'recip (list 'FACTORIAL k)))))
(define (tgd-sum-lam f x m)     ; z |-> SPS(term_z, succ m)
  (list 'VNB-LAMBDA 'z 'RR (list 'SERIES-PARTIAL-SUM (tgd-term f x) (list 'succ m))))
(define (tgd-val f x t m)       ; V_m = (recip(m!) f^(m+1)(t)) (x-t)^m
  (list '* (list '* (list 'recip (list 'FACTORIAL m)) (list (list 'NTH-DERIV f (list 'succ m)) t))
           (list 'power (list '- x t) m)))
(define (tgd-dh f t m)          ; DH(f,t,m): f^(k) differentiable at t with value f^(k+1)(t), k <= m
  (list 'FORALL 'k (list 'IMPLIES (list 'AND '(IN k NN) (list '<= 'k m))
    (list 'IS-DIFF-AT (list 'NTH-DERIV f 'k) t (list (list 'NTH-DERIV f '(succ k)) t)))))

;;; ====================================================================
;;; (1) recip 1 = 1   (rr-recip-one, taylor-proof.scm, above the window)
;;; ====================================================================
(sp (make-wff '(= (recip 1) 1)))
(fact 'rr-one-in)
(have! '(NOT (= 1 0)) (lambda () (arith)))
(have! '(AND (IN 1 RR) (NOT (= 1 0))))
(fact 'rr-recip-inverse 1)
(fact 'rr-recip-closed 1)
(fact 'rr-one-mul '(recip 1))
(fact 'eq-sym '(* 1 (recip 1)) '(recip 1))
(fact 'eq-trans '(recip 1) '(* 1 (recip 1)) 1)
(ass)
(qed 'tgd-recip-one)
(topic! 'tgd-recip-one 'analysis)

;;; ====================================================================
;;; (2) n! is a POSITIVE REAL, and recip(n!) is real
;;;     (factorial-real-pos / recip-factorial-in-rr, taylor-proof.scm)
;;; ====================================================================
(sp (make-wff '(FORALL n (IMPLIES (IN n NN)
   (AND (IN (FACTORIAL n) RR) (< 0 (FACTORIAL n)))))))
(define tgd-fbr (use-induction))
(dk-focus! (cdr (assq 'base tgd-fbr)))
(mac 'factorial-zero)
(have! '(= (succ 0) 1) (lambda () (arith)))
(subst '(= (succ 0) 1))
(fact 'rr-one-in)
(fact 'rr-zero-lt-one)
(prop)
(dk-focus! (cdr (assq 'step tgd-fbr)))
(define tgd-fn (cdr (assq 'var tgd-fbr)))
(dk-split! (cdr (assq 'ih tgd-fbr)))
(mac 'factorial-succ)
(fact 'nn-succ-closed tgd-fn)
(fact 'nn-in-rr (list 'succ tgd-fn))
(fact 'nn-zero-le (list 'succ tgd-fn))
(fact 'nn-succ-nonzero tgd-fn)
(fact 'neq-sym (list 'succ tgd-fn) 0)
(have! (list 'AND (list '<= 0 (list 'succ tgd-fn)) (list 'NOT (list '= 0 (list 'succ tgd-fn)))))
(fact 'rr-le-ne-lt 0 (list 'succ tgd-fn))
(have! (list 'AND (list 'IN (list 'succ tgd-fn) 'RR) (list 'IN (list 'FACTORIAL tgd-fn) 'RR)))
(fact 'rr-mul-closed (list 'succ tgd-fn) (list 'FACTORIAL tgd-fn))
(fact 'rr-mul-pos    (list 'succ tgd-fn) (list 'FACTORIAL tgd-fn))
(prop)
(qed 'tgd-factorial-real-pos)
(topic! 'tgd-factorial-real-pos 'analysis)

(sp (make-wff '(FORALL n (IMPLIES (IN n NN) (IN (recip (FACTORIAL n)) RR)))))
(di)
(fact 'tgd-factorial-real-pos 'n)
(dk-split! '(AND (IN (FACTORIAL n) RR) (< 0 (FACTORIAL n))))
(fact 'rr-pos-ne-zero '(factorial n))
(have! '(AND (IN (FACTORIAL n) RR) (NOT (= (FACTORIAL n) 0))))
(fact 'rr-recip-closed '(factorial n))
(ass)
(qed 'tgd-recip-factorial-in-rr)
(topic! 'tgd-recip-factorial-in-rr 'analysis)

;;; ====================================================================
;;; (3) THE TELESCOPING EQUATION:  recip(m!) = (succ m) * recip((succ m)!).
;;; (succ m)! = (succ m) m!;  (succ m)m! . R = 1 (rr-recip-inverse) is
;;; rearranged to  1 = m! . ((succ m) R)  (crs over the typed generators) and
;;; rr-recip-solve reads  (succ m) R = recip(m!) . 1  off it.
;;; ====================================================================
(sp (make-wff '(FORALL m (IMPLIES (IN m NN)
   (= (recip (FACTORIAL m)) (* (succ m) (recip (FACTORIAL (succ m)))))))))
(di)
(mac 'factorial-succ)
(fact 'tgd-factorial-real-pos 'm)
(dk-split! '(AND (IN (FACTORIAL m) RR) (< 0 (FACTORIAL m))))
(fact 'rr-pos-ne-zero '(factorial m))
(fact 'nn-succ-closed 'm)
(fact 'tgd-factorial-real-pos '(succ m))
(dk-split! '(AND (IN (FACTORIAL (succ m)) RR) (< 0 (FACTORIAL (succ m)))))
(mac-h 'factorial-succ '(IN (FACTORIAL (succ m)) RR))
(mac-h 'factorial-succ '(< 0 (FACTORIAL (succ m))))
(fact 'rr-pos-ne-zero '(* (succ m) (factorial m)))
(have! '(AND (IN (* (succ m) (FACTORIAL m)) RR) (NOT (= (* (succ m) (FACTORIAL m)) 0))))
(fact 'rr-recip-inverse '(* (succ m) (factorial m)))
(fact 'rr-recip-closed '(* (succ m) (factorial m)))
(fact 'nn-in-rr '(succ m))
(have! '(= (* (* (succ m) (FACTORIAL m)) (recip (* (succ m) (FACTORIAL m))))
           (* (FACTORIAL m) (* (succ m) (recip (* (succ m) (FACTORIAL m))))))
       (lambda () (crs)))
(fact 'eq-sym '(* (* (succ m) (FACTORIAL m)) (recip (* (succ m) (FACTORIAL m)))) 1)
(fact 'eq-trans 1 '(* (* (succ m) (FACTORIAL m)) (recip (* (succ m) (FACTORIAL m))))
                 '(* (FACTORIAL m) (* (succ m) (recip (* (succ m) (FACTORIAL m))))))
(have! '(AND (IN (FACTORIAL m) RR) (NOT (= (FACTORIAL m) 0))))
(have! '(AND (IN (succ m) RR) (IN (recip (* (succ m) (FACTORIAL m))) RR)))
(fact 'rr-mul-closed '(succ m) '(recip (* (succ m) (factorial m))))
(fact 'rr-one-in)
(fact 'rr-recip-solve '(factorial m) 1 '(* (succ m) (recip (* (succ m) (factorial m)))))
(subst '(= (* (succ m) (recip (* (succ m) (FACTORIAL m)))) (* (recip (FACTORIAL m)) 1)))
(fact 'rr-recip-closed '(factorial m))
(crs)
(qed 'tgd-recip-factorial-succ)
(topic! 'tgd-recip-factorial-succ 'analysis)
(alias! 'tgd-recip-factorial-succ "recip(m!) = (m+1) recip((m+1)!)")

;;; ====================================================================
;;; (4) d/dz (x - z) = -1.   deriv-const + deriv-identity + deriv-neg + deriv-sum
;;; build  z |-> x + (-z);  binary-minus-def carries it to the literal difference.
;;; ====================================================================
(sp (make-wff '(FORALL x (IMPLIES (IN x RR) (FORALL t (IMPLIES (IN t RR)
   (IS-DIFF-AT (VNB-LAMBDA z RR (- x z)) t (- 1))))))))
(dk-peel-to! 'IS-DIFF-AT)
(define tgd-sub-lam '(VNB-LAMBDA z RR (- x z)))
(have! '(AND (IN x RR) (IN t RR)))
(define tgd-kx (dk-fact! 'deriv-const 'x 't))
(define tgd-klam (cadr tgd-kx))
(define tgd-idn (dk-fact! 'deriv-identity 't))
(define tgd-negi (dk-fact! 'deriv-neg (cadr tgd-idn) 't 1))
(define tgd-negi2 (dk-landed-1 (lambda () (lam-b-h tgd-negi))))      ; z |-> -z
(have! (list 'AND tgd-kx tgd-negi2))
(define tgd-sum (dk-fact! 'deriv-sum tgd-klam (cadr tgd-negi2) 't 0 '(- 1)))
(define tgd-sum2 (dk-landed-1 (lambda () (lam-b-h tgd-sum))))        ; z |-> x + (-z)
(define tgd-sumlam (cadr tgd-sum2))
(have! (list 'IN tgd-sub-lam '(FUN RR RR))
  (lambda ()
    (dk-lam-t!)
    (let ((v (tgd-di-var!)))
      (fact 'rr-sub-in-rr 'x v)
      (ass))))
(have! (list 'FORALL 'x_ (list 'IMPLIES '(IN x_ RR)
              (list '== (list tgd-sub-lam 'x_) (list tgd-sumlam 'x_))))
  (lambda ()
    (let ((v (tgd-di-var!)))
      (lam-b)
      (fact 'binary-minus-def 'x v)
      (ass))))
(fact 'diff-transfer-ptwise-eq tgd-sub-lam tgd-sumlam 't '(+ 0 (- 1)))
(have! '(= (- 1) (+ 0 (- 1))) (lambda () (crs)))
(subst '(= (- 1) (+ 0 (- 1))))
(ass)
(qed 'tgd-sub-diff)
(topic! 'tgd-sub-diff 'analysis)

;;; ====================================================================
;;; (5) d/dz (x - z)^(succ m) = ((succ m) (x-t)^m) . (-1).   The chain rule on
;;; deriv-power at the point x - t and (4); the COMPOSE is carried to the
;;; literal lambda by compose-apply + beta (diff-transfer-ptwise-eq).
;;; ====================================================================
(sp (make-wff '(FORALL m (IMPLIES (IN m NN) (FORALL x (IMPLIES (IN x RR) (FORALL t (IMPLIES (IN t RR)
   (IS-DIFF-AT (VNB-LAMBDA z RR (power (- x z) (succ m))) t
               (* (* (succ m) (power (- x t) m)) (- 1)))))))))))
(dk-peel-to! 'IS-DIFF-AT)
(define tgd-pw-lam '(VNB-LAMBDA z RR (power (- x z) (succ m))))
(define tgd-subd (dk-fact! 'tgd-sub-diff 'x 't))
(fact 'rr-sub-in-rr 'x 't)
(define tgd-pwr (dk-fact! 'deriv-power 'm '(- x t)))                ; u |-> u^(succ m) at x-t
(define tgd-glam (cadr tgd-pwr))
(define tgd-mv (cadddr tgd-pwr))
(have! (list 'IS-DIFF-AT tgd-glam (list tgd-sub-lam 't) tgd-mv)      ; ... at (SUB t), for the chain rule
  (lambda () (lam-b) (ass)))
(define tgd-ch (dk-fact! 'deriv-chain tgd-sub-lam tgd-glam 't '(- 1) tgd-mv))
(define tgd-comp (cadr tgd-ch))                                      ; (COMPOSE G SUB)
(tgd-proj! tgd-subd (list 'IN tgd-sub-lam '(FUN RR RR)))
(tgd-proj! tgd-pwr (list 'IN tgd-glam '(FUN RR RR)))
(have! (list 'AND (list 'IN tgd-sub-lam '(FUN RR RR)) (list 'IN tgd-glam '(FUN RR RR))))
(define tgd-capp (dk-fact! 'compose-apply 'RR 'RR 'RR tgd-glam tgd-sub-lam))
(fact 'nn-succ-closed 'm)
(have! (list 'IN tgd-pw-lam '(FUN RR RR))
  (lambda ()
    (dk-lam-t!)
    (let ((v (tgd-di-var!)))
      (fact 'rr-sub-in-rr 'x v)
      (fact 'power-closed-at '(succ m) (list '- 'x v))
      (ass))))
(have! (list 'FORALL 'x_ (list 'IMPLIES '(IN x_ RR)
              (list '== (list tgd-pw-lam 'x_) (list tgd-comp 'x_))))
  (lambda ()
    (let ((v (tgd-di-var!)))
      (fact 'rr-sub-in-rr 'x v)
      (subst (dk-deepest (lambda () (inst+ tgd-capp v))))
      (lam-b)
      (qrfl))))
(fact 'diff-transfer-ptwise-eq tgd-pw-lam tgd-comp 't (list '* tgd-mv '(- 1)))
(ass)
(qed 'tgd-power-sub-diff)
(topic! 'tgd-power-sub-diff 'analysis)

;;; ====================================================================
;;; (6) the value identity of the telescoping step, over variables.
;;; `crs' decides it; it is applied to the terms by citation (crs sees no
;;; symbolic power), exactly as taylor-proof.scm applies its micro-identities.
;;;   s = succ m, r = recip((succ m)!), d1 = f^(m+1)(t), d2 = f^(m+2)(t),
;;;   p = (x-t)^m, q = (x-t)^(succ m).
;;; ====================================================================
(sp (make-wff '(FORALL s (IMPLIES (IN s RR) (FORALL r (IMPLIES (IN r RR)
   (FORALL d1 (IMPLIES (IN d1 RR) (FORALL d2 (IMPLIES (IN d2 RR)
   (FORALL p (IMPLIES (IN p RR) (FORALL q (IMPLIES (IN q RR)
     (= (+ (* (+ (* d2 q) (* d1 (* (* s p) (- 1)))) r) (* (* d1 q) 0))
        (- (* (* r d2) q) (* (* (* s r) d1) p)))))))))))))))))
(dk-peel-to! '=)
(crs)
(qed 'tgd-step-identity)
(topic! 'tgd-step-identity 'analysis)

(sp (make-wff '(FORALL u (IMPLIES (IN u RR) (FORALL v (IMPLIES (IN v RR)
   (= v (+ u (- v u)))))))))
(dk-peel-to! '=)
(crs)
(qed 'tgd-telescope-identity)
(topic! 'tgd-telescope-identity 'analysis)

;;; ====================================================================
;;; (7) THE SUMMAND'S DERIVATIVE.  T_{m+1}(z) = f^(m+1)(z) (x-z)^(succ m) recip((succ m)!)
;;; has derivative  V_{m+1} - V_m  at t, given f^(m+1) differentiable at t with
;;; value f^(m+2)(t).  Product rule twice, `lam-b-h' reducing each landed
;;; lambda in place (deriv-polynomial.scm's move), then (3) + (6) on the value.
;;; ====================================================================
(sp (make-wff
  (list 'FORALL 'm (list 'IMPLIES '(IN m NN) (list 'FORALL 'f (list 'FORALL 'x (list 'IMPLIES '(IN x RR)
    (list 'FORALL 't (list 'IMPLIES '(IN t RR)
      (list 'IMPLIES '(IS-DIFF-AT (NTH-DERIV f (succ m)) t ((NTH-DERIV f (succ (succ m))) t))
        (list 'IS-DIFF-AT (tgd-term-lam 'f 'x '(succ m)) 't
              (list '- (tgd-val 'f 'x 't '(succ m)) (tgd-val 'f 'x 't 'm)))))))))))))
(dk-peel-to! 'IS-DIFF-AT)
(define tgd-hyp '(IS-DIFF-AT (NTH-DERIV f (succ m)) t ((NTH-DERIV f (succ (succ m))) t)))
(define tgd-f1 '(NTH-DERIV f (succ m)))
(define tgd-d2 '((NTH-DERIV f (succ (succ m))) t))
(define tgd-d1 '((NTH-DERIV f (succ m)) t))
(tgd-proj! tgd-hyp (list 'IN tgd-f1 '(FUN RR RR)))
(tgd-proj! tgd-hyp (list 'IN tgd-d2 'RR))
(fact 'fun-apply-type-c tgd-f1 'RR 'RR 't)                            ; d1 in RR
(define tgd-pwd (dk-fact! 'tgd-power-sub-diff 'm 'x 't))
(define tgd-pwlam (cadr tgd-pwd))
(define tgd-mp (cadddr tgd-pwd))
(have! (list 'AND tgd-hyp tgd-pwd))
(define tgd-p1 (dk-fact! 'deriv-product tgd-f1 tgd-pwlam 't tgd-d2 tgd-mp))
(define tgd-p1b (dk-landed-1 (lambda () (lam-b-h tgd-p1))))          ; z |-> f^(m+1)(z) (x-z)^(succ m)
(define tgd-alam (cadr tgd-p1b))
(define tgd-va (cadddr tgd-p1b))
(fact 'nn-succ-closed 'm)
(fact 'tgd-recip-factorial-in-rr '(succ m))
(have! '(AND (IN (recip (FACTORIAL (succ m))) RR) (IN t RR)))
(define tgd-kc (dk-fact! 'deriv-const '(recip (FACTORIAL (succ m))) 't))
(have! (list 'AND tgd-p1b tgd-kc))
(define tgd-p2 (dk-fact! 'deriv-product tgd-alam (cadr tgd-kc) 't tgd-va 0))
(lam-b-h tgd-p2)                                                     ; now literally T_{m+1}
;; the value: recip(m!) -> (succ m) recip((succ m)!), then the identity
(fact 'tgd-recip-factorial-succ 'm)
(subst '(= (recip (FACTORIAL m)) (* (succ m) (recip (FACTORIAL (succ m))))))
(fact 'nn-in-rr '(succ m))
(fact 'rr-sub-in-rr 'x 't)
(fact 'power-closed-at 'm '(- x t))
(fact 'power-closed-at '(succ m) '(- x t))
(define tgd-id (dk-fact! 'tgd-step-identity '(succ m) '(recip (FACTORIAL (succ m))) tgd-d1 tgd-d2
                         '(power (- x t) m) '(power (- x t) (succ m))))
(fact 'eq-sym (cadr tgd-id) (caddr tgd-id))
(subst (list '= (caddr tgd-id) (cadr tgd-id)))
(ass)
(qed 'tgd-term-diff)
(topic! 'tgd-term-diff 'analysis)
(alias! 'tgd-term-diff "the Taylor summand's derivative in the centre telescopes")

;;; ====================================================================
;;; (8) the base sum:  SPS(term_z, succ 0) == f(z).
;;; term_z(0) = f^(0)(z) (x-z)^0 recip(0!) = f(z) . 1 . 1, and the recurrence.
;;; ====================================================================
(sp (make-wff '(FORALL f (IMPLIES (IN f (FUN RR RR)) (FORALL x (IMPLIES (IN x RR) (FORALL z (IMPLIES (IN z RR)
   (== (SERIES-PARTIAL-SUM (VNB-LAMBDA k NN (* (* ((NTH-DERIV f k) z) (power (- x z) k)) (recip (FACTORIAL k)))) (succ 0))
       (f z))))))))))
(dk-peel-to! '==)
(define tgd-tm0 (tgd-term 'f 'x))
(fact 'nn-zero-in)
(fact 'fun-apply-type-c 'f 'RR 'RR 'z)
(fact 'rr-sub-in-rr 'x 'z)
(fact 'rr-subset-cc '(- x z))
(have! '(= (recip (succ 0)) 1)
  (lambda () (have! '(= (succ 0) 1) (lambda () (arith))) (subst '(= (succ 0) 1)) (fact 'tgd-recip-one) (ass)))
(have! (list '= (list tgd-tm0 0) '(f z))
  (lambda ()
    (lam-b)
    (mac 'nth-deriv-zero)
    (mac 'power-zero)
    (mac 'factorial-zero)
    (subst '(= (recip (succ 0)) 1))
    (crs)))
(have! (list 'IN (list tgd-tm0 0) 'RR) (lambda () (subst (list '= (list tgd-tm0 0) '(f z))) (ass)))
(have! (list 'IN (list 'SERIES-PARTIAL-SUM tgd-tm0 0) 'RR)
       (lambda () (mac 'series-partial-sum-zero) (fact 'rr-zero-in) (ass)))
(fact 'series-partial-sum-succ tgd-tm0 0)
(subst (list '== (list 'SERIES-PARTIAL-SUM tgd-tm0 '(succ 0))
                 (list '+ (list 'SERIES-PARTIAL-SUM tgd-tm0 0) (list tgd-tm0 0))))
(mac 'series-partial-sum-zero)
(subst (list '= (list tgd-tm0 0) '(f z)))
(have! '(= (+ 0 (f z)) (f z)) (lambda () (crs)))
(subst '(= (+ 0 (f z)) (f z)))
(qrfl)
(qed 'tgd-base-sum-value)
(topic! 'tgd-base-sum-value 'analysis)

;;; ====================================================================
;;; (9) THE INDUCTION:  S_m'(t) = V_m,  degree OUTERMOST.
;;; ====================================================================
(sp (make-wff
  (list 'FORALL 'm (list 'IMPLIES '(IN m NN)
    (list 'FORALL 'f (list 'FORALL 'x (list 'IMPLIES '(IN x RR)
      (list 'FORALL 't (list 'IMPLIES '(IN t RR)
        (list 'IMPLIES (tgd-dh 'f 't 'm)
          (list 'IS-DIFF-AT (tgd-sum-lam 'f 'x 'm) 't (tgd-val 'f 'x 't 'm))))))))))))
(define tgd-br (use-induction))
(define tgd-m  (cdr (assq 'var tgd-br)))
(define tgd-ih (cdr (assq 'ih  tgd-br)))

;; read f, x, t off the GOAL  (IS-DIFF-AT (VNB-LAMBDA z RR (SPS TERM (succ m))) t V)
(define (tgd-goal-f) (cadr (car (cadr (cadr (cadddr (cadr (cadddr (cadr (dk-goal))))))))))
(define (tgd-goal-x) (cadr (cadr (caddr (cadr (cadddr (cadr (cadddr (cadr (dk-goal))))))))))
(define (tgd-goal-t) (caddr (dk-goal)))

;;; --- base:  S_0 == f pointwise, so S_0' = f'(t);  V_0 = f^(1)(t). ---
(dk-focus! (cdr (assq 'base tgd-br)))
(dk-peel-to! 'IS-DIFF-AT)
(define tgd-bf (tgd-goal-f))
(define tgd-bx (tgd-goal-x))
(define tgd-bt (tgd-goal-t))
(define tgd-bs (tgd-sum-lam tgd-bf tgd-bx 0))
(define tgd-bd0 (list (list 'NTH-DERIV tgd-bf '(succ 0)) tgd-bt))
(fact 'nn-zero-in)
(fact 'nn-le-refl 0)
(have! '(AND (IN 0 NN) (<= 0 0)))
(define tgd-bh0 (dk-deepest (lambda () (inst+ (tgd-dh tgd-bf tgd-bt 0) 0))))   ; IS-DIFF-AT f^(0) t f^(1)(t)
(tgd-proj! tgd-bh0 (list 'IN (list 'NTH-DERIV tgd-bf 0) '(FUN RR RR)))
(mac-h 'nth-deriv-zero (list 'IN (list 'NTH-DERIV tgd-bf 0) '(FUN RR RR)))    ; f in FUN RR RR
(define tgd-bh0f (dk-landed-1 (lambda () (mac-h 'nth-deriv-zero tgd-bh0))))  ; IS-DIFF-AT f t f^(1)(t)
(tgd-proj! tgd-bh0f (list 'IN tgd-bd0 'RR))
(have! (list 'IN tgd-bs '(FUN RR RR))
  (lambda ()
    (dk-lam-t!)
    (let ((v (tgd-di-var!)))
      (fact 'tgd-base-sum-value tgd-bf tgd-bx v)
      (subst (list '== (list 'SERIES-PARTIAL-SUM (subst-free 'z v (tgd-term tgd-bf tgd-bx)) '(succ 0)) (list tgd-bf v)))
      (fact 'fun-apply-type-c tgd-bf 'RR 'RR v)
      (ass))))
(have! (list 'FORALL 'x_ (list 'IMPLIES '(IN x_ RR)
              (list '== (list tgd-bs 'x_) (list tgd-bf 'x_))))
  (lambda ()
    (let ((v (tgd-di-var!)))
      (lam-b)
      (fact 'tgd-base-sum-value tgd-bf tgd-bx v)
      (ass))))
(fact 'diff-transfer-ptwise-eq tgd-bs tgd-bf tgd-bt tgd-bd0)
;; the value:  (recip(0!) . f^(1)(t)) . (x-t)^0  =  f^(1)(t)
(mac 'factorial-zero)
(have! '(= (recip (succ 0)) 1)
  (lambda () (have! '(= (succ 0) 1) (lambda () (arith))) (subst '(= (succ 0) 1)) (fact 'tgd-recip-one) (ass)))
(subst '(= (recip (succ 0)) 1))
(fact 'rr-sub-in-rr tgd-bx tgd-bt)
(fact 'rr-subset-cc (list '- tgd-bx tgd-bt))
(mac 'power-zero)
(have! (list '= (list '* (list '* 1 tgd-bd0) 1) tgd-bd0) (lambda () (crs)))
(subst (list '= (list '* (list '* 1 tgd-bd0) 1) tgd-bd0))
(ass)

;;; --- step:  S_{m+1} == S_m + T_{m+1} pointwise;  V_m + (V_{m+1} - V_m) = V_{m+1}. ---
(dk-focus! (cdr (assq 'step tgd-br)))
(dk-peel-to! 'IS-DIFF-AT)
(define tgd-sf (tgd-goal-f))
(define tgd-sx (tgd-goal-x))
(define tgd-st (tgd-goal-t))
(define tgd-sm (list 'succ tgd-m))
(define tgd-ssm (list 'succ tgd-sm))
(define tgd-s-lo (tgd-sum-lam tgd-sf tgd-sx tgd-m))                   ; S_m
(define tgd-s-hi (tgd-sum-lam tgd-sf tgd-sx tgd-sm))                  ; S_{m+1}
(define tgd-s-tm (tgd-term tgd-sf tgd-sx))                            ; term_z
(define tgd-s-f1 (list 'NTH-DERIV tgd-sf tgd-sm))                     ; f^(m+1)
(define tgd-v-lo (tgd-val tgd-sf tgd-sx tgd-st tgd-m))                ; V_m
(define tgd-v-hi (tgd-val tgd-sf tgd-sx tgd-st tgd-sm))               ; V_{m+1}
(fact 'nn-succ-closed tgd-m)
(fact 'nn-le-succ tgd-m)                                              ; m <= succ m
;; the goal's DH is at succ m; the induction hypothesis wants it at m
(have! (tgd-dh tgd-sf tgd-st tgd-m)
  (lambda ()
    (di)
    (let* ((landed (dk-landed-1 (lambda () (di))))                    ; (AND (IN k NN) (<= k m))
           (kv     (cadr (cadr landed))))
      (dk-split! landed)
      (fact 'nn-le-trans-guarded kv tgd-m tgd-sm)
      (have! (list 'AND (list 'IN kv 'NN) (list '<= kv tgd-sm)))
      (inst+ (tgd-dh tgd-sf tgd-st tgd-sm) kv)
      (ass))))
;; ... and the hypothesis applies:  IS-DIFF-AT S_m t V_m
(define tgd-ih1 (dk-landed-1 (lambda () (inst+ tgd-ih tgd-sf))))
(define tgd-ih2 (dk-deepest  (lambda () (inst+ tgd-ih1 tgd-sx))))
(define tgd-hs  (dk-deepest  (lambda () (inst+ tgd-ih2 tgd-st))))
(if (not (and (pair? tgd-hs) (eq? (car tgd-hs) 'IS-DIFF-AT)))
    (error "taylor-g-diff: the induction hypothesis did not detach" tgd-hs))
(tgd-proj! tgd-hs (list 'IN tgd-s-lo '(FUN RR RR)))
(fact 'diff-value-real tgd-s-lo tgd-st tgd-v-lo)                       ; V_m in RR
;; f^(m+1) is differentiable at t (DH at k = succ m), so the summand is (7)
(fact 'nn-le-refl tgd-sm)
(have! (list 'AND (list 'IN tgd-sm 'NN) (list '<= tgd-sm tgd-sm)))
(define tgd-h1 (dk-deepest (lambda () (inst+ (tgd-dh tgd-sf tgd-st tgd-sm) tgd-sm))))
(tgd-proj! tgd-h1 (list 'IN tgd-s-f1 '(FUN RR RR)))
(tgd-proj! tgd-h1 (list 'IN (cadddr tgd-h1) 'RR))                     ; f^(m+2)(t) in RR
(define tgd-ht (dk-fact! 'tgd-term-diff tgd-m tgd-sf tgd-sx tgd-st))   ; IS-DIFF-AT T_{m+1} t (V_{m+1} - V_m)
(define tgd-t-lam (cadr tgd-ht))
;; V_{m+1} in RR, from its three factors
(fact 'tgd-recip-factorial-in-rr tgd-sm)
(fact 'rr-sub-in-rr tgd-sx tgd-st)
(fact 'power-closed-at tgd-sm (list '- tgd-sx tgd-st))
(have! (list 'AND (list 'IN (list 'recip (list 'FACTORIAL tgd-sm)) 'RR) (list 'IN (cadddr tgd-h1) 'RR)))
(fact 'rr-mul-closed (list 'recip (list 'FACTORIAL tgd-sm)) (cadddr tgd-h1))
(have! (list 'AND (list 'IN (cadr tgd-v-hi) 'RR) (list 'IN (caddr tgd-v-hi) 'RR)))
(fact 'rr-mul-closed (cadr tgd-v-hi) (caddr tgd-v-hi))                ; V_{m+1} in RR
;; the sum rule on S_m and T_{m+1}
(have! (list 'AND tgd-hs tgd-ht))
(define tgd-ssum (dk-fact! 'deriv-sum tgd-s-lo tgd-t-lam tgd-st tgd-v-lo (cadddr tgd-ht)))
(define tgd-ssum2 (dk-landed-1 (lambda () (lam-b-h tgd-ssum))))       ; z |-> SPS(term_z, succ m) + T_{m+1}(z)
(define tgd-ssum-lam (cadr tgd-ssum2))
;; the recurrence at a real point v:  SPS(term_v, succ succ m) == SPS(term_v, succ m) + term_v(succ m),
;; with its two typings landed first (series-partial-sum-succ is guarded on both)
(define (tgd-sps-step! v)
  (let ((tm (tgd-term tgd-sf tgd-sx)))
    (let ((tmv (subst-free 'z v tm)))
      ;; the lower sum is real BECAUSE S_m is a function (the IH's own typing)
      (fact 'fun-apply-type-c tgd-s-lo 'RR 'RR v)
      (lam-b-h (list 'IN (list tgd-s-lo v) 'RR))
      ;; the summand is real: its three factors are
      (have! (list 'IN (list tmv tgd-sm) 'RR)
        (lambda ()
          (lam-b)
          (fact 'fun-apply-type-c tgd-s-f1 'RR 'RR v)
          (fact 'rr-sub-in-rr tgd-sx v)
          (fact 'power-closed-at tgd-sm (list '- tgd-sx v))
          (have! (list 'AND (list 'IN (list tgd-s-f1 v) 'RR)
                            (list 'IN (list 'power (list '- tgd-sx v) tgd-sm) 'RR)))
          (fact 'rr-mul-closed (list tgd-s-f1 v) (list 'power (list '- tgd-sx v) tgd-sm))
          (have! (list 'AND (list 'IN (list '* (list tgd-s-f1 v) (list 'power (list '- tgd-sx v) tgd-sm)) 'RR)
                            (list 'IN (list 'recip (list 'FACTORIAL tgd-sm)) 'RR)))
          (fact 'rr-mul-closed (list '* (list tgd-s-f1 v) (list 'power (list '- tgd-sx v) tgd-sm))
                               (list 'recip (list 'FACTORIAL tgd-sm)))
          (ass)))
      (fact 'series-partial-sum-succ tmv tgd-sm)
      (list '== (list 'SERIES-PARTIAL-SUM tmv tgd-ssm)
                (list '+ (list 'SERIES-PARTIAL-SUM tmv tgd-sm) (list tmv tgd-sm))))))
;; S_{m+1} is a function RR -> RR
(have! (list 'IN tgd-s-hi '(FUN RR RR))
  (lambda ()
    (dk-lam-t!)
    (let* ((v (tgd-di-var!))
           (rec (tgd-sps-step! v)))
      (subst rec)
      (have! (list 'AND (list 'IN (cadr (caddr rec)) 'RR) (list 'IN (caddr (caddr rec)) 'RR)))
      (fact 'rr-add-closed (cadr (caddr rec)) (caddr (caddr rec)))
      (ass))))
;; ... and agrees pointwise with the sum-rule lambda
(have! (list 'FORALL 'x_ (list 'IMPLIES '(IN x_ RR)
              (list '== (list tgd-s-hi 'x_) (list tgd-ssum-lam 'x_))))
  (lambda ()
    (let* ((v (tgd-di-var!))
           (rec (tgd-sps-step! v)))
      (lam-b)
      (subst rec)
      (lam-b)
      (qrfl))))
(fact 'diff-transfer-ptwise-eq tgd-s-hi tgd-ssum-lam tgd-st (cadddr tgd-ssum2))
;; the value:  V_{m+1} = V_m + (V_{m+1} - V_m)
(fact 'tgd-telescope-identity tgd-v-lo tgd-v-hi)
(subst (list '= tgd-v-hi (list '+ tgd-v-lo (list '- tgd-v-hi tgd-v-lo))))
(ass)
(qed 'tgd-sum-diff)
(topic! 'tgd-sum-diff 'analysis)
(alias! 'tgd-sum-diff "the derivative of the Taylor partial sum in its centre")

;;; ====================================================================
;;; (10) THE HEADLINE -- taylor-G-diff, guarded (see the header).
;;; G = f(x) - S_n:  deriv-const, deriv-neg, deriv-sum, then the transfer to
;;; the literal G through TAYLOR-POLY's unfold and binary-minus-def.
;;; ====================================================================
(sp (make-wff
  '(FORALL f (FORALL a (FORALL x (FORALL n (FORALL t
     (IMPLIES (IN n NN)
     (IMPLIES (IN x RR)
     (IMPLIES (TAYLOR-DIFFERENTIABLE f a x n)
     (IMPLIES (AND (< a t) (< t x))
       (IS-DIFF-AT (VNB-LAMBDA z RR (- (f x) (TAYLOR-POLY f z n x))) t
                   (- 0 (* (* (recip (FACTORIAL n)) ((NTH-DERIV f (succ n)) t)) (power (- x t) n)))))))))))))))
(dk-peel-to! 'IS-DIFF-AT)
(define tgd-g-lam '(VNB-LAMBDA z RR (- (f x) (TAYLOR-POLY f z n x))))
(define tgd-g-s (tgd-sum-lam 'f 'x 'n))
(define tgd-g-v (tgd-val 'f 'x 't 'n))
;; DH(f,t,n) out of TAYLOR-DIFFERENTIABLE's second conjunct, on a side branch.
;; (AND (< a t) (< t x)) stays WHOLE in context: `inst+' detaches it as one
;; antecedent, and `dk-split!' would have consumed it.)
(have! (tgd-dh 'f 't 'n)
  (lambda ()
    ;; split ONLY the unfolded TD (a blanket AND-split would also consume the
    ;; (AND (< a t) (< t x)) that the inst+ below detaches)
    (dk-split! (dk-landed-1 (lambda () (mac-h 'TAYLOR-DIFFERENTIABLE '(TAYLOR-DIFFERENTIABLE f a x n)))))
    (di)
    (let* ((landed (dk-landed-1 (lambda () (di))))                    ; (AND (IN k NN) (<= k n)), kept whole
           (kv     (cadr (cadr landed)))
           (c2     (tgd-find (lambda (u) (and (pair? u) (eq? (car u) 'FORALL)
                                              (tgd-mentions? 'IS-DIFF-AT u)))
                             'the-differentiability-conjunct)))
      (let ((at-k (dk-deepest (lambda () (inst+ c2 kv)))))
        (inst+ at-k 't)                                               ; (AND (< a t) (< t x)) is in context
        (ass)))))
;; t in RR and f in FUN RR RR, both off DH at k = 0
(fact 'nn-zero-in)
(fact 'nn-zero-le 'n)
(have! '(AND (IN 0 NN) (<= 0 n)))
(define tgd-g-h0 (dk-deepest (lambda () (inst+ (tgd-dh 'f 't 'n) 0))))
(tgd-proj! tgd-g-h0 '(IN t RR))
(tgd-proj! tgd-g-h0 '(IN (NTH-DERIV f 0) (FUN RR RR)))
(mac-h 'nth-deriv-zero '(IN (NTH-DERIV f 0) (FUN RR RR)))
(fact 'fun-apply-type-c 'f 'RR 'RR 'x)                                ; f(x) in RR
;; S_n' = V_n
(define tgd-g-hs (dk-fact! 'tgd-sum-diff 'n 'f 'x 't))
(if (not (and (pair? tgd-g-hs) (eq? (car tgd-g-hs) 'IS-DIFF-AT)))
    (error "taylor-g-diff: tgd-sum-diff did not detach" tgd-g-hs))
(tgd-proj! tgd-g-hs (list 'IN tgd-g-s '(FUN RR RR)))
;; -S_n, the constant f(x), their sum
(define tgd-g-neg (dk-fact! 'deriv-neg tgd-g-s 't tgd-g-v))
(define tgd-g-neg2 (dk-landed-1 (lambda () (lam-b-h tgd-g-neg))))     ; z |-> -SPS(term_z, succ n)
(have! '(AND (IN (f x) RR) (IN t RR)))
(define tgd-g-kc (dk-fact! 'deriv-const '(f x) 't))
(have! (list 'AND tgd-g-kc tgd-g-neg2))
(define tgd-g-sum (dk-fact! 'deriv-sum (cadr tgd-g-kc) (cadr tgd-g-neg2) 't 0 (list '- tgd-g-v)))
(define tgd-g-sum2 (dk-landed-1 (lambda () (lam-b-h tgd-g-sum))))     ; z |-> f(x) + (-SPS(...))
(define tgd-g-sum-lam (cadr tgd-g-sum2))
;; G is a function RR -> RR ...
(have! (list 'IN tgd-g-lam '(FUN RR RR))
  (lambda ()
    (dk-lam-t!)
    (let ((v (tgd-di-var!)))
      (mac 'TAYLOR-POLY)
      (fact 'fun-apply-type-c tgd-g-s 'RR 'RR v)
      (lam-b-h (list 'IN (list tgd-g-s v) 'RR))
      (fact 'rr-sub-in-rr '(f x) (list 'SERIES-PARTIAL-SUM (subst-free 'z v (tgd-term 'f 'x)) '(succ n)))
      (ass))))
;; ... and agrees pointwise with the sum-rule lambda
(have! (list 'FORALL 'x_ (list 'IMPLIES '(IN x_ RR)
              (list '== (list tgd-g-lam 'x_) (list tgd-g-sum-lam 'x_))))
  (lambda ()
    (let ((v (tgd-di-var!)))
      (lam-b)
      (mac 'TAYLOR-POLY)
      (fact 'binary-minus-def '(f x) (list 'SERIES-PARTIAL-SUM (subst-free 'z v (tgd-term 'f 'x)) '(succ n)))
      (ass))))
(fact 'diff-transfer-ptwise-eq tgd-g-lam tgd-g-sum-lam 't (list '+ 0 (list '- tgd-g-v)))
;; the value:  0 - V_n == 0 + (-V_n)
(fact 'binary-minus-def 0 tgd-g-v)
(subst (list '== (list '- 0 tgd-g-v) (list '+ 0 (list '- tgd-g-v))))
(ass)
(qed 'taylor-G-diff)
(topic! 'taylor-G-diff 'analysis)
(alias! 'taylor-G-diff "the derivative of the Taylor remainder in its centre")
