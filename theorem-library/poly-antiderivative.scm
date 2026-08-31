;;; poly-antiderivative.scm -- calculus.pdf EXAMPLE 4.7, "every polynomial
;;; function is antiderivable", with the antiderivative written out:
;;;
;;;   cf in FUN(NN,RR), n in NN, pt in RR  =>
;;;     IS-DIFF-AT( lambda x in RR. SUM_{k<succ n} (recip(succ k) a_k) x^(succ k),
;;;                 pt,
;;;                 SUM_{k<succ n} a_k pt^k )
;;;
;;; i.e. d/dx sum_{k=0}^{n} a_k x^(k+1)/(k+1) = sum_{k=0}^{n} a_k x^k.
;;;
;;; It is the rung the integration arc consumes: Cor 4.17 plus Theorem 5.2 turn
;;; it into "every continuous function has an antiderivative", which is what
;;; DEFINES the integral.
;;;
;;; THE SHAPE IS deriv-polynomial's, one storey up, and SHORTER than it.  There
;;; the polynomial splits at succ(succ n) while its derivative sum splits at
;;; succ n; here BOTH sums split at succ n, because the antiderivative and the
;;; derivative are indexed by the same k.  So there is one `series-partial-sum-
;;; succ' index in play throughout, not two.
;;;
;;; THE ONE STEP WITH CONTENT is the coefficient cancellation
;;;
;;;     (succ k) . ( recip(succ k) . a_k )  =  a_k
;;;
;;; and `crs' will not do it: `crs' decides commutative-RING identities and
;;; `recip' is not a ring operation.  What it IS is `rr-recip-inverse'
;;; (number-systems.scm:395), whose antecedent is
;;;
;;;     NOT (= (succ k) 0)
;;;
;;; -- and that formula, exactly as written, is `nn-succ-nonzero'
;;; (theorem-library/nn-parity-proof.scm:152), which bills `modulo 0'.  There is
;;; NO separate "as a real" form to reach for and none should be invented:
;;; NN <= ZZ <= QQ <= RR are genuine inclusions of SETS, not coercions, so a
;;; disequality proved of a natural number is the disequality the field axiom
;;; asks for.  `nn-in-rr' carries the other conjunct, (IN (succ k) RR).
;;;
;;; The cancellation is proved ONCE, over VARIABLES, as `recip-succ-cancel' --
;;; the same device as deriv-polynomial's poly-step-identity and deriv-power's
;;; pw-step-identity, and for the same reason: `crs' sees neither `succ' nor
;;; `power', so the rearrangement must not be attempted at the succ/power terms
;;; themselves.  Its statement is ORIENTED (c v = ((succ k)(recip(succ k) c)) v,
;;; not the other way round) so that its left-hand side is the GOAL's value and
;;; a single `subst' turns the goal into what `deriv-coef-monomial' concluded;
;;; stated the readable way round, `subst' would have to rewrite the assumption,
;;; which is not what `subst' does.
;;;
;;; WHAT THIS FILE ADDS BESIDE THE HEADLINE:
;;;   anti-term-in-rr        (recip(succ k) a_k) x^(succ k) is real -- the one
;;;                          place the recip's two side conditions are paid
;;;   anti-term-lam-in-fun   k |-> that term is in FUN(NN,RR)
;;;   anti-lam-in-fun        x |-> SUM_{k<m} that term is in FUN(RR,RR), which
;;;                          is what `diff-transfer-ptwise-eq' asks for.  Note
;;;                          poly-lam-in-fun does NOT cover this: it is stated
;;;                          for the shape SUM_k b_k x^k and the antiderivative's
;;;                          summand is b_k x^(succ k).
;;;   rr-zero-plus           0 + t = t on RR, over a VARIABLE.  `crs' proves it
;;;                          in one move, but only where it can certify its
;;;                          generators from CONTEXT typings -- and the place it
;;;                          is wanted is the empty-sum end of a partial sum,
;;;                          where the term is a triple product whose factors are
;;;                          typed nowhere.
;;;   recip-succ-cancel      the coefficient cancellation, over variables
;;;   deriv-anti-monomial    d/dx ((recip(succ m) c) x^(succ m)) = c x^m -- the
;;;                          antiderivative rule for a single monomial, and the
;;;                          only place recip-succ-cancel is used
;;;
;;; Needs deriv-polynomial (deriv-coef-monomial, and the driver this copies),
;;; diff-transfer (diff-transfer-ptwise-eq), deriv-sum-product (deriv-sum),
;;; dyadic-weights (power-closed-at), comparison-test-proof
;;; (series-partial-sum-zero/-succ/-in-rr), fun-apply-type-proof
;;; (fun-apply-type-c), nn-parity-proof (nn-succ-nonzero), nn-order-basics
;;; (nn-in-rr) and driver-kit (use-induction, have!, dk-*).

;;; ---- file-local driver helpers (the `pa-' prefix) ----------------------

;; di, returning the eigenvariable of the guard it landed
(define (pa-di-var!) (cadr (car (dk-landed* (lambda () (di))))))

;; lam-b the goal to a fixpoint; every argument reduced here is typed first.
(define (pa-beta!)
  (let loop ((k 0) (prev #f))
    (let ((g (dk-goal)))
      (if (and (< k 10) (not (equal? g prev)))
          (begin (quietly (lambda () (vnb-guard (lambda () (lam-b))))) (loop (+ k 1) g))))))

;; the three shapes this file builds over and over
(define (pa-anti-term cf x)                ; k |-> (recip(succ k) a_k) x^(succ k)
  (list 'VNB-LAMBDA 'k 'NN
        (list '* (list '* (list 'recip '(succ k)) (list cf 'k))
                 (list 'power x '(succ k)))))
(define (pa-poly-term cf x)                ; k |-> a_k x^k
  (list 'VNB-LAMBDA 'k 'NN (list '* (list cf 'k) (list 'power x 'k))))
(define (pa-anti cf m)                     ; x |-> SUM_{k<m} (recip(succ k) a_k) x^(succ k)
  (list 'VNB-LAMBDA 'x 'RR (list 'SERIES-PARTIAL-SUM (pa-anti-term cf 'x) m)))

;; (IN (* u v) RR) -- rr-mul-closed has an AND antecedent, which `fact' will
;; not split, so the conjunction goes in first.
(define (pa-mul! u v)
  (have! (list 'AND (list 'IN u 'RR) (list 'IN v 'RR)))
  (fact 'rr-mul-closed u v))

;; everything recip(succ k) needs, in the order the axioms want it: succ k is a
;; natural, hence a real, and it is nonzero -- the file's whole arithmetic
;; content, and each of the three facts bills modulo 0.
(define (pa-recip-succ! k)
  (fact 'nn-succ-closed k)                          ; (IN (succ k) NN)
  (fact 'nn-in-rr (list 'succ k))                   ; (IN (succ k) RR)
  (fact 'nn-succ-nonzero k)                         ; (NOT (= (succ k) 0))
  (have! (list 'AND (list 'IN (list 'succ k) 'RR)
                    (list 'NOT (list '= (list 'succ k) 0))))
  (fact 'rr-recip-closed (list 'succ k))            ; (IN (recip (succ k)) RR)
  (fact 'rr-recip-inverse (list 'succ k)))          ; (succ k) recip(succ k) = 1

;;; =====================================================================
;;; (1) the antiderivative's summand is real.  This is where the reciprocal's
;;; two side conditions are discharged, and the only place in the file where
;;; the successor's nonzero-ness is needed for TYPING rather than for the
;;; cancellation.
;;; =====================================================================

(sp (make-wff '(FORALL cf (IMPLIES (IN cf (FUN NN RR))
   (FORALL k (IMPLIES (IN k NN)
     (FORALL x (IMPLIES (IN x RR)
       (IN (* (* (recip (succ k)) (cf k)) (power x (succ k))) RR)))))))))
(dk-peel-to! 'IN)
(define atr-t  (cadr (dk-goal)))                    ; the summand
(define atr-cf (car (caddr (cadr atr-t))))          ; cf, out of (cf k)
(define atr-k  (cadr (caddr (cadr atr-t))))         ; k
(define atr-x  (cadr (caddr atr-t)))                ; x
(pa-recip-succ! atr-k)
(fact 'fun-apply-type-c atr-cf 'NN 'RR atr-k)       ; (IN (cf k) RR)
(pa-mul! (list 'recip (list 'succ atr-k)) (list atr-cf atr-k))
(fact 'power-closed-at (list 'succ atr-k) atr-x)    ; (IN x^(succ k) RR)
(pa-mul! (list '* (list 'recip (list 'succ atr-k)) (list atr-cf atr-k))
         (list 'power atr-x (list 'succ atr-k)))
(ass)
(qed 'anti-term-in-rr)
(topic! 'anti-term-in-rr 'analysis)
(alias! 'anti-term-in-rr
        "the antiderivative's summand (a_k/(k+1)) x^(k+1) is a real number")

;;; =====================================================================
;;; (2) the summand sequence is a function NN -> RR.  `lam-t' opens TWO leaves
;;; -- the pointwise typing and the SETHOOD of the domain -- and a driver
;;; expecting one leaves the other open until `qed'.
;;; =====================================================================

(sp (make-wff '(FORALL cf (IMPLIES (IN cf (FUN NN RR))
   (FORALL x (IMPLIES (IN x RR)
     (IN (VNB-LAMBDA k NN (* (* (recip (succ k)) (cf k)) (power x (succ k))))
         (FUN NN RR))))))))
(dk-peel-to! 'IN)
(define atl-bod (cadddr (cadr (dk-goal))))
(define atl-cf  (car (caddr (cadr atl-bod))))
(define atl-x   (cadr (caddr atl-bod)))
(dk-lam-t!)
(let ((z (pa-di-var!)))
  (fact 'anti-term-in-rr atl-cf z atl-x)
  (ass))
(qed 'anti-term-lam-in-fun)
(topic! 'anti-term-lam-in-fun 'analysis)
(alias! 'anti-term-lam-in-fun
        "the antiderivative's term sequence k |-> (a_k/(k+1)) x^(k+1) is a function NN -> RR")

;;; =====================================================================
;;; (3) the antiderivative is a function RR -> RR.  This is what the transfer
;;; asks for: pointwise agreement with a function does NOT establish it.
;;; =====================================================================

(sp (make-wff '(FORALL cf (IMPLIES (IN cf (FUN NN RR))
   (FORALL m (IMPLIES (IN m NN)
     (IN (VNB-LAMBDA x RR
           (SERIES-PARTIAL-SUM
             (VNB-LAMBDA k NN (* (* (recip (succ k)) (cf k)) (power x (succ k)))) m))
         (FUN RR RR))))))))
(dk-peel-to! 'IN)
(define alf-bod (cadddr (cadr (dk-goal))))          ; (SERIES-PARTIAL-SUM T m)
(define alf-m   (caddr alf-bod))
(define alf-cf  (car (caddr (cadr (cadddr (cadr alf-bod))))))
(dk-lam-t!)
(let ((z (pa-di-var!)))
  (fact 'anti-term-lam-in-fun alf-cf z)
  (fact 'series-partial-sum-in-rr alf-m (pa-anti-term alf-cf z))
  (ass))
(qed 'anti-lam-in-fun)
(topic! 'anti-lam-in-fun 'analysis)
(alias! 'anti-lam-in-fun
        "the antiderivative x |-> sum_{k<m} (a_k/(k+1)) x^(k+1) is a function RR -> RR")

;;; =====================================================================
;;; (3a) 0 + t = t on RR, over a VARIABLE.  `crs' proves it in one move, but
;;; only where it can certify its generators from CONTEXT typings -- and the
;;; place this identity is wanted is the empty-sum end of a partial sum, where
;;; the term is a triple product whose factors are typed nowhere.  Instantiating
;;; a one-generator theorem needs only (IN t RR), which `anti-term-in-rr'
;;; already delivers.
;;; =====================================================================

(sp (make-wff '(FORALL t_ (IMPLIES (IN t_ RR) (= (+ 0 t_) t_)))))
(dk-peel-to! '=)
(crs)
(qed 'rr-zero-plus)
(topic! 'rr-zero-plus 'inequalities)
(alias! 'rr-zero-plus "0 + t = t on RR")

;;; =====================================================================
;;; (4) THE COEFFICIENT CANCELLATION, over variables.
;;;
;;;     c v  =  ( (succ m) . ( recip(succ m) . c ) ) . v
;;;
;;; Stated in THIS orientation on purpose: `subst' rewrites the GOAL, so the
;;; left-hand side has to be the shape the goal carries and the right-hand side
;;; the shape the citation concluded.  The proof is three moves -- reassociate
;;; (a ring identity in the two opaque generators succ m and recip(succ m), both
;;; certified real above), collapse (succ m) recip(succ m) to 1 by
;;; rr-recip-inverse, and finish with `crs' on a goal that no longer mentions
;;; `recip' at all.
;;; =====================================================================

(sp (make-wff '(FORALL m (IMPLIES (IN m NN)
   (FORALL c (IMPLIES (IN c RR)
     (FORALL v (IMPLIES (IN v RR)
       (= (* c v) (* (* (succ m) (* (recip (succ m)) c)) v))))))))))
(dk-peel-to! '=)
(define rsc-goal (dk-goal))
(define rsc-c (cadr (cadr rsc-goal)))
(define rsc-v (caddr (cadr rsc-goal)))
(define rsc-m (cadr (cadr (cadr (caddr rsc-goal)))))     ; m, out of (succ m)
(define rsc-s (list 'succ rsc-m))
(define rsc-r (list 'recip rsc-s))
(pa-recip-succ! rsc-m)
(define rsc-assoc
  (list '= (list '* (list '* rsc-s (list '* rsc-r rsc-c)) rsc-v)
           (list '* (list '* (list '* rsc-s rsc-r) rsc-c) rsc-v)))
(have! rsc-assoc (lambda () (crs)))
(subst rsc-assoc)
(subst (list '= (list '* rsc-s rsc-r) 1))
(crs)
(qed 'recip-succ-cancel)
(topic! 'recip-succ-cancel 'inequalities)
(alias! 'recip-succ-cancel "(m+1)(c/(m+1)) v = c v, the antiderivative's coefficient cancellation")

;;; =====================================================================
;;; (5) THE ANTIDERIVATIVE OF A MONOMIAL:
;;;
;;;     d/dx ( (recip(succ m) . c) x^(succ m) )  =  c x^m .
;;;
;;; `deriv-coef-monomial' at coefficient recip(succ m) . c gives the same
;;; lambda and the value ((succ m)(recip(succ m) c)) x^m; recip-succ-cancel is
;;; the one `subst' between the two.
;;; =====================================================================

(sp (make-wff '(FORALL c (IMPLIES (IN c RR)
   (FORALL m (IMPLIES (IN m NN)
     (FORALL pt (IMPLIES (IN pt RR)
       (IS-DIFF-AT (VNB-LAMBDA x RR (* (* (recip (succ m)) c) (power x (succ m))))
                   pt
                   (* c (power pt m)))))))))))
(dk-peel-to! 'IS-DIFF-AT)
(define dam-goal (dk-goal))
(define dam-pt   (caddr dam-goal))
(define dam-c    (cadr (cadddr dam-goal)))               ; c, out of (* c pt^m)
(define dam-m    (caddr (caddr (cadddr dam-goal))))      ; m, out of (power pt m)
(define dam-coef (list '* (list 'recip (list 'succ dam-m)) dam-c))

(fact 'nn-succ-closed dam-m)                             ; (IN (succ m) NN)
(fact 'nn-in-rr (list 'succ dam-m))
(fact 'nn-succ-nonzero dam-m)
(have! (list 'AND (list 'IN (list 'succ dam-m) 'RR)
                  (list 'NOT (list '= (list 'succ dam-m) 0))))
(fact 'rr-recip-closed (list 'succ dam-m))
(pa-mul! (list 'recip (list 'succ dam-m)) dam-c)         ; (IN (recip(succ m) c) RR)
(fact 'power-closed-at dam-m dam-pt)                     ; (IN pt^m RR)
(fact 'deriv-coef-monomial dam-coef dam-m dam-pt)
(fact 'recip-succ-cancel dam-m dam-c (list 'power dam-pt dam-m))
(subst (list '= (list '* dam-c (list 'power dam-pt dam-m))
                (list '* (list '* (list 'succ dam-m) dam-coef)
                         (list 'power dam-pt dam-m))))
(ass)
(qed 'deriv-anti-monomial)
(topic! 'deriv-anti-monomial 'analysis)
(alias! 'deriv-anti-monomial "the derivative of (c/(m+1)) x^(m+1) is c x^m")

;;; =====================================================================
;;; (6) EXAMPLE 4.7 ITSELF.
;;;
;;; THE INDUCTION VARIABLE IS OUTERMOST: `ni' tests the goal's SHAPE literally,
;;; and one greedy `di' would take cf and pt with it, after which the induction
;;; is gone.
;;; =====================================================================

(sp (make-wff
 '(FORALL n (IMPLIES (IN n NN)
    (FORALL cf (IMPLIES (IN cf (FUN NN RR))
      (FORALL pt (IMPLIES (IN pt RR)
        (IS-DIFF-AT
          (VNB-LAMBDA x RR
            (SERIES-PARTIAL-SUM
              (VNB-LAMBDA k NN (* (* (recip (succ k)) (cf k)) (power x (succ k))))
              (succ n)))
          pt
          (SERIES-PARTIAL-SUM
            (VNB-LAMBDA k NN (* (cf k) (power pt k))) (succ n)))))))))))
(define pa-br (use-induction))

;;; ---- base: n = 0.  Both sums are the one-term sum at k = 0, so the whole
;;; base case IS deriv-anti-monomial at m = 0, carried across the empty-sum
;;; identity 0 + t = t on each side.
(dk-focus! (cdr (assq 'base pa-br)))
(dk-peel-to! 'IS-DIFF-AT)
(define bs-goal (dk-goal))
(define bs-cf   (car (cadr (cadddr (cadr (cadddr bs-goal))))))
(define bs-pt   (caddr bs-goal))
(define bs-pt-seq (pa-poly-term bs-cf bs-pt))            ; k |-> a_k pt^k
(define bs-mval (list '* (list bs-cf 0) (list 'power bs-pt 0)))
(define bs-anti (pa-anti bs-cf '(succ 0)))
(define bs-mono (list 'VNB-LAMBDA 'x 'RR
                      (list '* (list '* '(recip (succ 0)) (list bs-cf 0))
                               (list 'power 'x '(succ 0)))))

(fact 'nn-zero-in)                                       ; (IN 0 NN)
(fact 'nn-succ-closed 0)                                 ; (IN (succ 0) NN)
(fact 'fun-apply-type-c bs-cf 'NN 'RR 0)                 ; (IN (cf 0) RR)
(fact 'power-closed-at 0 bs-pt)                          ; (IN pt^0 RR)
(pa-mul! (list bs-cf 0) (list 'power bs-pt 0))           ; (IN a_0 pt^0 RR)

;;; the goal's derivative value: split the one-term sum, drop the empty sum.
;; series-partial-sum-succ is guarded on its two arguments being real (2026-08-29)
(fact 'poly-term-lam-in-fun bs-cf bs-pt)
(fact 'series-partial-sum-in-rr 0 bs-pt-seq)
(fact 'fun-apply-type-c bs-pt-seq 'NN 'RR 0)
(fact 'series-partial-sum-succ bs-pt-seq 0)
(subst (list '== (list 'SERIES-PARTIAL-SUM bs-pt-seq '(succ 0))
                 (list '+ (list 'SERIES-PARTIAL-SUM bs-pt-seq 0) (list bs-pt-seq 0))))
(fact 'series-partial-sum-zero bs-pt-seq)
(subst (list '== (list 'SERIES-PARTIAL-SUM bs-pt-seq 0) 0))
(pa-beta!)                                               ; 0 + a_0 pt^0
(fact 'rr-zero-plus bs-mval)
(subst (list '= (list '+ 0 bs-mval) bs-mval))

(fact 'deriv-anti-monomial (list bs-cf 0) 0 bs-pt)       ; IS-DIFF-AT(mono, pt, a_0 pt^0)
(fact 'anti-lam-in-fun bs-cf '(succ 0))
(have! (list 'FORALL 'x_ (list 'IMPLIES '(IN x_ RR)
          (list '== (list bs-anti 'x_) (list bs-mono 'x_))))
  (lambda ()
    (let ((z (pa-di-var!)))
      (pa-beta!)
      ;; series-partial-sum-succ is guarded on its two arguments being real (2026-08-29)
      (fact 'anti-term-lam-in-fun bs-cf z)
      (fact 'series-partial-sum-in-rr 0 (pa-anti-term bs-cf z))
      (fact 'fun-apply-type-c (pa-anti-term bs-cf z) 'NN 'RR 0)
      (fact 'series-partial-sum-succ (pa-anti-term bs-cf z) 0)
      (subst (list '== (list 'SERIES-PARTIAL-SUM (pa-anti-term bs-cf z) '(succ 0))
                       (list '+ (list 'SERIES-PARTIAL-SUM (pa-anti-term bs-cf z) 0)
                                (list (pa-anti-term bs-cf z) 0))))
      (fact 'series-partial-sum-zero (pa-anti-term bs-cf z))
      (subst (list '== (list 'SERIES-PARTIAL-SUM (pa-anti-term bs-cf z) 0) 0))
      (pa-beta!)
      (let ((tm (list '* (list '* '(recip (succ 0)) (list bs-cf 0))
                      (list 'power z '(succ 0)))))
        (fact 'anti-term-in-rr bs-cf 0 z)
        (fact 'rr-zero-plus tm)
        (subst (list '= (list '+ 0 tm) tm))
        (qrfl)))))
(fact 'diff-transfer-ptwise-eq bs-anti bs-mono bs-pt bs-mval)
(ass)

;;; ---- step.  series-partial-sum-succ at the SAME index succ n on both sums:
;;;   SUM_{k<succ(succ n)} (recip(succ k) a_k) x^(succ k)
;;;      = SUM_{k<succ n} ... + (recip(succ(succ n)) a_{n+1}) x^(succ(succ n))
;;;   SUM_{k<succ(succ n)} a_k pt^k = SUM_{k<succ n} a_k pt^k + a_{n+1} pt^(succ n)
;;; and the two right-hand summands are exactly the induction hypothesis and
;;; deriv-anti-monomial, joined by `deriv-sum'.
(dk-focus! (cdr (assq 'step pa-br)))
(define st-n  (cdr (assq 'var pa-br)))
(define st-ih (cdr (assq 'ih  pa-br)))
(dk-peel-to! 'IS-DIFF-AT)
(define st-goal (dk-goal))
(define st-cf   (car (cadr (cadddr (cadr (cadddr st-goal))))))
(define st-pt   (caddr st-goal))
(define st-sn   (list 'succ st-n))
(define st-ssn  (list 'succ st-sn))

(define st-ih2 (dk-deepest (lambda () (inst+ st-ih st-cf))))
(define st-ihd (dk-deepest (lambda () (inst+ st-ih2 st-pt))))

(define st-pt-seq (pa-poly-term st-cf st-pt))            ; k |-> a_k pt^k
(define st-an   (pa-anti st-cf st-sn))                   ; the n-th antiderivative
(define st-next (pa-anti st-cf st-ssn))                  ; the goal's antiderivative
(define st-dvn  (list 'SERIES-PARTIAL-SUM st-pt-seq st-sn))
(define st-coef (list st-cf st-sn))                      ; a_{n+1}
(define st-mono (list 'VNB-LAMBDA 'x 'RR
                      (list '* (list '* (list 'recip st-ssn) st-coef)
                               (list 'power 'x st-ssn))))
(define st-mval (list '* st-coef (list 'power st-pt st-sn)))
(define st-sum  (list 'VNB-LAMBDA 'x 'RR
                      (list '+ (list st-an 'x) (list st-mono 'x))))
(define st-val  (list '+ st-dvn st-mval))

(fact 'nn-succ-closed st-n)                              ; (IN (succ n) NN)
(fact 'nn-succ-closed st-sn)                             ; (IN (succ (succ n)) NN)
(fact 'fun-apply-type-c st-cf 'NN 'RR st-sn)             ; (IN a_{n+1} RR)
(fact 'deriv-anti-monomial st-coef st-sn st-pt)          ; the new top term
(have! (list 'AND (list 'IS-DIFF-AT st-an st-pt st-dvn)
                  (list 'IS-DIFF-AT st-mono st-pt st-mval)))
(fact 'deriv-sum st-an st-mono st-pt st-dvn st-mval)

;;; the goal's derivative sum, split at its top term and beta-reduced, IS the
;;; value `deriv-sum' just concluded.
;; series-partial-sum-succ is guarded on its two arguments being real (2026-08-29)
(fact 'poly-term-lam-in-fun st-cf st-pt)
(fact 'series-partial-sum-in-rr st-sn st-pt-seq)
(fact 'fun-apply-type-c st-pt-seq 'NN 'RR st-sn)
(fact 'series-partial-sum-succ st-pt-seq st-sn)
(subst (list '== (list 'SERIES-PARTIAL-SUM st-pt-seq st-ssn)
                 (list '+ st-dvn (list st-pt-seq st-sn))))
(pa-beta!)

;;; ... and the goal's antiderivative agrees pointwise with the literal sum.
(fact 'anti-lam-in-fun st-cf st-ssn)
(have! (list 'FORALL 'x_ (list 'IMPLIES '(IN x_ RR)
          (list '== (list st-next 'x_) (list st-sum 'x_))))
  (lambda ()
    (let ((z (pa-di-var!)))
      (pa-beta!)
      ;; series-partial-sum-succ is guarded on its two arguments being real (2026-08-29)
      (fact 'anti-term-lam-in-fun st-cf z)
      (fact 'series-partial-sum-in-rr st-sn (pa-anti-term st-cf z))
      (fact 'fun-apply-type-c (pa-anti-term st-cf z) 'NN 'RR st-sn)
      (fact 'series-partial-sum-succ (pa-anti-term st-cf z) st-sn)
      (subst (list '== (list 'SERIES-PARTIAL-SUM (pa-anti-term st-cf z) st-ssn)
                       (list '+ (list 'SERIES-PARTIAL-SUM (pa-anti-term st-cf z) st-sn)
                                (list (pa-anti-term st-cf z) st-sn))))
      (pa-beta!)
      (qrfl))))
(fact 'diff-transfer-ptwise-eq st-next st-sum st-pt st-val)
(ass)
(qed 'poly-antiderivative)
(topic! 'poly-antiderivative 'analysis)
(alias! 'poly-antiderivative
        "Example 4.7: every polynomial function is antiderivable -- d/dx sum_{k<=n} a_k x^(k+1)/(k+1) = sum_{k<=n} a_k x^k")
