;;; theorem-library/taylor-gmvt-guarded.scm -- the four gMVT hypotheses of
;;; Taylor's theorem, GUARDED and PROVEN:
;;;
;;;   taylor-H-cont     H(t) = (x-t)^(n+1) is continuous at every real t
;;;   taylor-G-cont     G(t) = f(x) - TAYLOR-POLY(f,t,n,x) is continuous at
;;;                     every t in [a,x], given TAYLOR-DIFFERENTIABLE(f,a,x,n)
;;;   taylor-gmvt-cont  both, at every t in [a,x]  (the shape generalized-mvt reads)
;;;   taylor-gmvt-diff  both have SOME derivative at every real t in (a,x)
;;;
;;; All four stood in taylor-proof.scm as `add-to-pss' + `warrant! 'reference'
;;; (lines 61-96).  The triage of 2026-09-14 found them FALSE AS WRITTEN: `n'
;;; was unguarded, and off NN the power (x-z)^(succ n), the factorial and the
;;; partial sum mean nothing.  The user's decision (2026-09-14): add the guards,
;;; prove the guarded statements.  The statements below are the supports' with
;;; antecedents ADDED and nothing else touched -- binders and bodies are
;;; byte-identical to taylor-proof.scm's (GT, HT, GHCONT, GHDIFF are copied
;;; verbatim as tgc-gt / tgc-ht / tgc-ghcont / tgc-ghdiff):
;;;
;;;   taylor-H-cont     + (IN n NN)
;;;   taylor-G-cont     + (IN n NN), (IN x RR)     -- the same two taylor-G-diff took
;;;   taylor-gmvt-cont  + (IN n NN)                -- (IN x RR) was already there
;;;   taylor-gmvt-diff  + (IN n NN), (IN x RR)
;;;
;;; No guard on `a': G-cont reads (IN t RR) off TAYLOR-DIFFERENTIABLE's own
;;; continuity conjunct (the point conjunct of IS-CONTINUOUS-AT), and gmvt-cont
;;; reads it off `ccint-membership', which is unguarded.
;;;
;;; PLAN.
;;;   H-cont:  taylor-h-diff (the spliced block of taylor-proof.scm) gives
;;;            IS-DIFF-AT HT t (HVAL t) at EVERY real t, and
;;;            diff-implies-continuous does the rest.  No endpoint case: H is
;;;            differentiable everywhere, endpoints included.
;;;   G-cont:  NOT through differentiability -- TD gives G a derivative only
;;;            on the OPEN interval, and continuity at the endpoints a, x is
;;;            exactly what that route cannot reach.  Instead the continuity
;;;            of z |-> TAYLOR-POLY(f,z,n,x) at t is proved by INDUCTION ON
;;;            THE DEGREE (taylor-g-diff.scm's `tgd-sum-diff', with
;;;            continuity in place of differentiability), from the hypothesis
;;;              CH(f,t,m) = forall k <= m. f^(k) continuous at t,
;;;            which TD's FIRST conjunct supplies at every t in [a,x],
;;;            endpoints included.  So one argument covers the whole closed
;;;            interval and no endpoint lemma is needed.
;;;              base  S_0 == f pointwise (tgd-base-sum-value), transfer.
;;;              step  S_{m+1} == S_m + T_{m+1} pointwise
;;;                    (series-partial-sum-succ), sum-continuous-at, transfer;
;;;                    T_{m+1} = f^(m+1) . (x-z)^(m+1) . recip((m+1)!) is
;;;                    continuous by product-continuous-at twice, on
;;;                    f^(m+1) (CH), taylor-H-cont at degree m, and the
;;;                    constant (const-continuous-at)  -- `tgc-term-cont'.
;;;            Then G = const(f(x)) - S_n by sub-continuous-at and one more
;;;            transfer through TAYLOR-POLY's unfold.
;;;   gmvt-cont:  the two above at t in [a,x]; `ccint-membership' for t in RR.
;;;   gmvt-diff:  taylor-g-diff / taylor-h-diff give the explicit derivatives;
;;;            `ew' each and close.
;;;
;;; LOAD WINDOW.  This file cites `taylor-h-diff' (the spliced block of
;;; taylor-proof.scm), `recip-factorial-in-rr' (taylor-proof.scm's lemma
;;; block), `tgd-base-sum-value' (theorem-library/taylor-g-diff.scm, which
;;; loads before taylor-proof), `taylor-G-diff' (same), and is cited by
;;; `taylor-lagrange' at the END of taylor-proof.scm.  So it must sit INSIDE
;;; taylor-proof.scm, after the existing spliced block (`END spliced block')
;;; and before the taylor-lagrange section: THE INTEGRATOR SPLICES THIS FILE'S
;;; BODY IN THERE and retires the four supports at taylor-proof.scm:61-96
;;; (with their warrant! / topic! lines).  Everything else cited loads well
;;; before taylor-proof: diff-implies-continuous (differentiation),
;;; sum-continuous-at / product-continuous-at / const-continuous-at /
;;; sub-continuous-at / cont-transfer-ptwise-eq (the continuity-* files),
;;; ccint-membership (ccint-basics), series-partial-sum-succ
;;; (comparison-test-proof), fun-apply-type-c, power-closed-at (dyadic-weights),
;;; rr-sub-in-rr, nn-le-refl / nn-le-succ / nn-le-trans-guarded / nn-zero-le,
;;; nth-deriv-zero (higher-derivatives).
;;;
;;; Helper prefix: tgc-.  Every top-level define is prefixed.
;;; ====================================================================

;;; ---- file-local shapes (VERBATIM copies of taylor-proof.scm's GT/HT/GHCONT/GHDIFF) ----
(define tgc-gt '(VNB-LAMBDA z RR (- (f x) (TAYLOR-POLY f z n x))))
(define tgc-ht '(VNB-LAMBDA z RR (power (- x z) (succ n))))
(define (tgc-gval t) (list '- 0 (list '* (list '* '(recip (FACTORIAL n)) (list (list 'NTH-DERIV 'f '(succ n)) t)) (list 'power (list '- 'x t) 'n))))
(define (tgc-hval t) (list '- 0 (list '* '(succ n) (list 'power (list '- 'x t) 'n))))
(define tgc-ghcont (list 'FORALL 't (list 'IMPLIES '(IN t (CCINT a x))
                 (list 'AND (list 'IS-CONTINUOUS-AT 'RR-MS 'RR-MS tgc-gt 't)
                            (list 'IS-CONTINUOUS-AT 'RR-MS 'RR-MS tgc-ht 't)))))
(define tgc-ghdiff (list 'FORALL 't (list 'IMPLIES '(AND (IN t RR) (AND (< a t) (< t x)))
                 (list 'AND (list 'FORSOME 'L (list 'IS-DIFF-AT tgc-gt 't 'L))
                            (list 'FORSOME 'M (list 'IS-DIFF-AT tgc-ht 't 'M))))))

(define (tgc-cont fn t) (list 'IS-CONTINUOUS-AT 'RR-MS 'RR-MS fn t))
(define (tgc-term f x)          ; the Taylor summand  k |-> f^(k)(z) (x-z)^k recip(k!),  z FREE
  (list 'VNB-LAMBDA 'k 'NN
        (list '* (list '* (list (list 'NTH-DERIV f 'k) 'z) (list 'power (list '- x 'z) 'k))
                 (list 'recip (list 'FACTORIAL 'k)))))
(define (tgc-term-lam f x k)    ; z |-> f^(k)(z) (x-z)^k recip(k!)
  (list 'VNB-LAMBDA 'z 'RR
        (list '* (list '* (list (list 'NTH-DERIV f k) 'z) (list 'power (list '- x 'z) k))
                 (list 'recip (list 'FACTORIAL k)))))
(define (tgc-sum-lam f x m)     ; z |-> SPS(term_z, succ m)
  (list 'VNB-LAMBDA 'z 'RR (list 'SERIES-PARTIAL-SUM (tgc-term f x) (list 'succ m))))
(define (tgc-pow-lam x m)       ; z |-> (x-z)^(succ m)   (HT with n := m)
  (list 'VNB-LAMBDA 'z 'RR (list 'power (list '- x 'z) (list 'succ m))))
(define (tgc-ch f t m)          ; CH(f,t,m): f^(k) continuous at t for k <= m
  (list 'FORALL 'k (list 'IMPLIES (list 'AND '(IN k NN) (list '<= 'k m))
    (tgc-cont (list 'NTH-DERIV f 'k) t))))

;;; ---- file-local helpers ----
(define (tgc-mentions? sym f)
  (cond ((eq? f sym) #t)
        ((pair? f) (or (tgc-mentions? sym (car f)) (tgc-mentions? sym (cdr f))))
        (#t #f)))
(define (tgc-find pred what)
  (or (find-first pred (dk-asms)) (error "taylor-gmvt-guarded: no assumption" what)))
(define (tgc-split-ands!)
  (let loop ((n 0))
    (let ((tgt (find-first (lambda (a) (and (pair? a) (memq (car a) '(AND FORSOME)))) (dk-asms))))
      (if (and tgt (< n 20)) (begin (ai tgt) (loop (+ n 1)))))))
;; read the FUN typing / the point off an IS-CONTINUOUS-AT hypothesis WITHOUT
;; destroying it: mac-h replaces the assumption, so the unfold runs on the
;; have! side branch only (continuity-sub.scm's cu-typing! / cu-point!).
(define (tgc-fun! hyp)
  (let ((fn (cadddr hyp)))
    (have! (list 'IN fn '(FUN RR RR))
      (lambda ()
        (mac-h 'IS-CONTINUOUS-AT hyp)
        (tgc-split-ands!)
        (slot-h 'PTS (list 'IN fn '(FUN (PTS RR-MS) (PTS RR-MS))))
        (ass)))))
(define (tgc-point! hyp)
  (let ((pt (car (cddddr hyp))))
    (have! (list 'IN pt 'RR)
      (lambda ()
        (mac-h 'IS-CONTINUOUS-AT hyp)
        (tgc-split-ands!)
        (slot-h 'PTS (list 'IN pt '(PTS RR-MS)))
        (ass)))))
;; (IN (* a b) RR) from the two factor typings already in context
(define (tgc-mul-real! a b)
  (have! (list 'AND (list 'IN a 'RR) (list 'IN b 'RR)))
  (fact 'rr-mul-closed a b))
;; lam-b the goal to a fixpoint (nested redexes appear one reduction at a time)
(define (tgc-beta!)
  (let loop ((k 0) (prev #f))
    (let ((g (dk-goal)))
      (if (and (< k 8) (not (equal? g prev)))
          (begin (quietly (lambda () (vnb-guard (lambda () (lam-b))))) (loop (+ k 1) g))))))
(define (tgc-check-head! f head what)
  (if (not (and (pair? f) (eq? (car f) head)))
      (error "taylor-gmvt-guarded: expected" head what f)))

;;; =====================================================================
;;; (1) taylor-H-cont, guarded by n in NN.  H is differentiable at every
;;; real t (taylor-h-diff), hence continuous there.
;;; =====================================================================
(sp (make-wff
  (list 'FORALL 'x (list 'FORALL 'n (list 'FORALL 't (list 'IMPLIES '(IN x RR) (list 'IMPLIES '(IN t RR)
    (list 'IMPLIES '(IN n NN)
      (list 'IS-CONTINUOUS-AT 'RR-MS 'RR-MS tgc-ht 't)))))))))
(dk-peel-to! 'IS-CONTINUOUS-AT)
(fact 'taylor-h-diff 'x 'n 't)
(fact 'diff-implies-continuous tgc-ht 't (tgc-hval 't))
(ass)
(qed 'taylor-H-cont)
(topic! 'taylor-H-cont 'analysis)

;;; =====================================================================
;;; (2) THE SUMMAND IS CONTINUOUS.  T_{m+1}(z) = f^(m+1)(z) (x-z)^(succ m) recip((succ m)!)
;;; at t, given f^(m+1) continuous at t: product-continuous-at on f^(m+1) and
;;; z |-> (x-z)^(succ m) (taylor-H-cont at degree m), then on that and the
;;; constant recip((succ m)!); `lam-b-h' reduces each landed lambda in place.
;;; =====================================================================
(sp (make-wff
  (list 'FORALL 'm (list 'IMPLIES '(IN m NN) (list 'FORALL 'f (list 'FORALL 'x (list 'IMPLIES '(IN x RR)
    (list 'FORALL 't (list 'IMPLIES '(IN t RR)
      (list 'IMPLIES (tgc-cont '(NTH-DERIV f (succ m)) 't)
        (tgc-cont (tgc-term-lam 'f 'x '(succ m)) 't)))))))))))
(dk-peel-to! 'IS-CONTINUOUS-AT)
(define tgc-tc-f1 '(NTH-DERIV f (succ m)))
(define tgc-tc-pw (tgc-pow-lam 'x 'm))
(fact 'taylor-H-cont 'x 'm 't)                                        ; z |-> (x-z)^(succ m) continuous at t
(define tgc-tc-p1 (dk-fact! 'product-continuous-at tgc-tc-f1 tgc-tc-pw 't))
(tgc-check-head! tgc-tc-p1 'IS-CONTINUOUS-AT "product-continuous-at (1)")
(define tgc-tc-p1b (dk-landed-1 (lambda () (lam-b-h tgc-tc-p1))))    ; z |-> f^(m+1)(z) (x-z)^(succ m)
(fact 'nn-succ-closed 'm)
(fact 'recip-factorial-in-rr '(succ m))
(define tgc-tc-kc (dk-fact! 'const-continuous-at '(recip (FACTORIAL (succ m))) 't))
(tgc-check-head! tgc-tc-kc 'IS-CONTINUOUS-AT "const-continuous-at")
(define tgc-tc-p2 (dk-fact! 'product-continuous-at (cadddr tgc-tc-p1b) (cadddr tgc-tc-kc) 't))
(tgc-check-head! tgc-tc-p2 'IS-CONTINUOUS-AT "product-continuous-at (2)")
(lam-b-h tgc-tc-p2)                                                   ; now literally T_{m+1}
(ass)
(qed 'tgc-term-cont)
(topic! 'tgc-term-cont 'analysis)
(alias! 'tgc-term-cont "the Taylor summand is continuous in the centre")

;;; =====================================================================
;;; (3) THE INDUCTION:  S_m = z |-> SPS(term_z, succ m) is continuous at t
;;; given CH(f,t,m).  Degree OUTERMOST so `ni' fires.
;;; =====================================================================
(sp (make-wff
  (list 'FORALL 'm (list 'IMPLIES '(IN m NN)
    (list 'FORALL 'f (list 'FORALL 'x (list 'IMPLIES '(IN x RR)
      (list 'FORALL 't (list 'IMPLIES '(IN t RR)
        (list 'IMPLIES (tgc-ch 'f 't 'm)
          (tgc-cont (tgc-sum-lam 'f 'x 'm) 't)))))))))))
(define tgc-br (use-induction))
(define tgc-m  (cdr (assq 'var tgc-br)))
(define tgc-ih (cdr (assq 'ih  tgc-br)))

;; read f, x, t off the GOAL  (IS-CONTINUOUS-AT RR-MS RR-MS (VNB-LAMBDA z RR (SPS TERM (succ m))) t)
(define (tgc-goal-lam) (cadddr (dk-goal)))
(define (tgc-goal-t)   (car (cddddr (dk-goal))))
(define (tgc-goal-f)   (cadr (car (cadr (cadr (cadddr (cadr (cadddr (tgc-goal-lam)))))))))
(define (tgc-goal-x)   (cadr (cadr (caddr (cadr (cadddr (cadr (cadddr (tgc-goal-lam)))))))))

;;; --- base:  S_0 == f pointwise (tgd-base-sum-value), and f is continuous (CH at 0). ---
(dk-focus! (cdr (assq 'base tgc-br)))
(dk-peel-to! 'IS-CONTINUOUS-AT)
(define tgc-bf (tgc-goal-f))
(define tgc-bx (tgc-goal-x))
(define tgc-bt (tgc-goal-t))
(define tgc-bs (tgc-sum-lam tgc-bf tgc-bx 0))
(define (tgc-b-eq v)          ; SPS(term_v, succ 0) == f(v)
  (list '== (list 'SERIES-PARTIAL-SUM (subst-free 'z v (tgc-term tgc-bf tgc-bx)) '(succ 0))
            (list tgc-bf v)))
(fact 'nn-zero-in)
(fact 'nn-le-refl 0)
(have! '(AND (IN 0 NN) (<= 0 0)))
(define tgc-bh0 (dk-deepest (lambda () (inst+ (tgc-ch tgc-bf tgc-bt 0) 0))))     ; f^(0) continuous at t
(tgc-check-head! tgc-bh0 'IS-CONTINUOUS-AT "CH at 0")
(define tgc-bh0f (dk-landed-1 (lambda () (mac-h 'nth-deriv-zero tgc-bh0))))       ; f continuous at t
(tgc-fun! tgc-bh0f)                                                                ; f in FUN RR RR
(have! (list 'IN tgc-bs '(FUN RR RR))
  (lambda ()
    (dk-lam-t!)
    (let ((v (dk-di-var!)))
      (fact 'tgd-base-sum-value tgc-bf tgc-bx v)
      (subst (tgc-b-eq v))
      (fact 'fun-apply-type-c tgc-bf 'RR 'RR v)
      (ass))))
(have! (list 'FORALL 'x_ (list 'IMPLIES '(IN x_ RR)
              (list '= (list tgc-bs 'x_) (list tgc-bf 'x_))))
  (lambda ()
    (let ((v (dk-di-var!)))
      (lam-b)
      (fact 'tgd-base-sum-value tgc-bf tgc-bx v)
      (subst (tgc-b-eq v))
      (fact 'fun-apply-type-c tgc-bf 'RR 'RR v)
      (rfl))))
(fact 'cont-transfer-ptwise-eq tgc-bs tgc-bf tgc-bt)
(ass)

;;; --- step:  S_{m+1} == S_m + T_{m+1} pointwise;  sum-continuous-at. ---
(dk-focus! (cdr (assq 'step tgc-br)))
(dk-peel-to! 'IS-CONTINUOUS-AT)
(define tgc-sf (tgc-goal-f))
(define tgc-sx (tgc-goal-x))
(define tgc-st (tgc-goal-t))
(define tgc-sm (list 'succ tgc-m))
(define tgc-ssm (list 'succ tgc-sm))
(define tgc-s-lo (tgc-sum-lam tgc-sf tgc-sx tgc-m))                   ; S_m
(define tgc-s-hi (tgc-sum-lam tgc-sf tgc-sx tgc-sm))                  ; S_{m+1}
(define tgc-s-f1 (list 'NTH-DERIV tgc-sf tgc-sm))                     ; f^(m+1)
(fact 'nn-succ-closed tgc-m)
(fact 'nn-le-succ tgc-m)                                              ; m <= succ m
;; the goal's CH is at succ m; the induction hypothesis wants it at m
(have! (tgc-ch tgc-sf tgc-st tgc-m)
  (lambda ()
    (di)
    (let* ((landed (dk-landed-1 (lambda () (di))))                    ; (AND (IN k NN) (<= k m))
           (kv     (cadr (cadr landed))))
      (dk-split! landed)
      (fact 'nn-le-trans-guarded kv tgc-m tgc-sm)
      (have! (list 'AND (list 'IN kv 'NN) (list '<= kv tgc-sm)))
      (inst+ (tgc-ch tgc-sf tgc-st tgc-sm) kv)
      (ass))))
;; ... and the hypothesis applies:  S_m continuous at t
(define tgc-ih1 (dk-landed-1 (lambda () (inst+ tgc-ih tgc-sf))))
(define tgc-ih2 (dk-deepest  (lambda () (inst+ tgc-ih1 tgc-sx))))
(define tgc-hs  (dk-deepest  (lambda () (inst+ tgc-ih2 tgc-st))))
(tgc-check-head! tgc-hs 'IS-CONTINUOUS-AT "the induction hypothesis did not detach")
(tgc-fun! tgc-hs)                                                     ; S_m in FUN RR RR
;; f^(m+1) is continuous at t (CH at k = succ m), so the summand is (2)
(fact 'nn-le-refl tgc-sm)
(have! (list 'AND (list 'IN tgc-sm 'NN) (list '<= tgc-sm tgc-sm)))
(define tgc-h1 (dk-deepest (lambda () (inst+ (tgc-ch tgc-sf tgc-st tgc-sm) tgc-sm))))
(tgc-check-head! tgc-h1 'IS-CONTINUOUS-AT "CH at succ m")
(tgc-fun! tgc-h1)                                                     ; f^(m+1) in FUN RR RR
(define tgc-ht-c (dk-fact! 'tgc-term-cont tgc-m tgc-sf tgc-sx tgc-st))   ; T_{m+1} continuous at t
(tgc-check-head! tgc-ht-c 'IS-CONTINUOUS-AT "tgc-term-cont did not detach")
(define tgc-t-lam (cadddr tgc-ht-c))
;; the sum rule on S_m and T_{m+1}
(define tgc-ssum (dk-fact! 'sum-continuous-at tgc-s-lo tgc-t-lam tgc-st))
(tgc-check-head! tgc-ssum 'IS-CONTINUOUS-AT "sum-continuous-at did not detach")
(define tgc-ssum2 (dk-landed-1 (lambda () (lam-b-h tgc-ssum))))       ; z |-> SPS(term_z, succ m) + T_{m+1}(z)
(define tgc-ssum-lam (cadddr tgc-ssum2))
(fact 'recip-factorial-in-rr tgc-sm)
;; at a real point v: the reduced summand B_v is real, and the recurrence
;;   SPS(term_v, succ succ m) == SPS(term_v, succ m) + term_v(succ m),
;; with its two typings landed first (series-partial-sum-succ is guarded on both).
;; Returns (rec . B_v).
(define (tgc-sps-step! v)
  (let* ((tmv (subst-free 'z v (tgc-term tgc-sf tgc-sx)))
         (dv  (list tgc-s-f1 v))
         (pw  (list 'power (list '- tgc-sx v) tgc-sm))
         (rc  (list 'recip (list 'FACTORIAL tgc-sm)))
         (bv  (list '* (list '* dv pw) rc)))
    ;; the lower sum is real BECAUSE S_m is a function (the IH's own typing)
    (fact 'fun-apply-type-c tgc-s-lo 'RR 'RR v)
    (lam-b-h (list 'IN (list tgc-s-lo v) 'RR))
    ;; the summand is real: its three factors are
    (fact 'fun-apply-type-c tgc-s-f1 'RR 'RR v)
    (fact 'rr-sub-in-rr tgc-sx v)
    (fact 'power-closed-at tgc-sm (list '- tgc-sx v))
    (tgc-mul-real! dv pw)
    (tgc-mul-real! (list '* dv pw) rc)                                ; (IN B_v RR)
    (have! (list 'IN (list tmv tgc-sm) 'RR) (lambda () (lam-b) (ass)))
    (fact 'series-partial-sum-succ tmv tgc-sm)
    (cons (list '== (list 'SERIES-PARTIAL-SUM tmv tgc-ssm)
                    (list '+ (list 'SERIES-PARTIAL-SUM tmv tgc-sm) (list tmv tgc-sm)))
          bv)))
;; S_{m+1} is a function RR -> RR
(have! (list 'IN tgc-s-hi '(FUN RR RR))
  (lambda ()
    (dk-lam-t!)
    (let* ((v (dk-di-var!))
           (rec (car (tgc-sps-step! v))))
      (subst rec)
      (have! (list 'AND (list 'IN (cadr (caddr rec)) 'RR) (list 'IN (caddr (caddr rec)) 'RR)))
      (fact 'rr-add-closed (cadr (caddr rec)) (caddr (caddr rec)))
      (ass))))
;; ... and agrees pointwise with the sum-rule lambda
(have! (list 'FORALL 'x_ (list 'IMPLIES '(IN x_ RR)
              (list '= (list tgc-s-hi 'x_) (list tgc-ssum-lam 'x_))))
  (lambda ()
    (let* ((v   (dk-di-var!))
           (rb  (tgc-sps-step! v))
           (rec (car rb))
           (bv  (cdr rb))
           (tmv-app (caddr (caddr rec)))                              ; term_v(succ m)
           (lo      (cadr  (caddr rec))))                             ; SPS(term_v, succ m)
      (tgc-beta!)
      (subst rec)
      (tgc-beta!)
      ;; both sides should now read  SPS(term_v, succ m) + B_v;  if the
      ;; summand redex survived on the left, reduce it by citation
      (if (not (alpha-equiv? (cadr (dk-goal)) (caddr (dk-goal))))
          (begin
            (have! (list '= tmv-app bv) (lambda () (lam-b) (rfl)))
            (subst (list '= tmv-app bv))))
      (if (not (alpha-equiv? (cadr (dk-goal)) (caddr (dk-goal))))
          (error "taylor-gmvt-guarded: the two sides did not meet" (dk-goal)))
      (have! (list 'AND (list 'IN lo 'RR) (list 'IN bv 'RR)))
      (fact 'rr-add-closed lo bv)
      (rfl))))
(fact 'cont-transfer-ptwise-eq tgc-s-hi tgc-ssum-lam tgc-st)
(ass)
(qed 'tgc-sum-cont)
(topic! 'tgc-sum-cont 'analysis)
(alias! 'tgc-sum-cont "the Taylor partial sum is continuous in its centre")

;;; =====================================================================
;;; (4) taylor-G-cont, guarded by n in NN, x in RR.  G = f(x) - S_n:
;;; const-continuous-at, sub-continuous-at, then the transfer to the literal
;;; G through TAYLOR-POLY's unfold.  CH(f,t,n) is TD's FIRST conjunct at the
;;; point t of [a,x] -- endpoints included, which is why no case split.
;;; =====================================================================
(sp (make-wff
  '(FORALL f (FORALL a (FORALL x (FORALL n (FORALL t
     (IMPLIES (IN n NN)
     (IMPLIES (IN x RR)
     (IMPLIES (TAYLOR-DIFFERENTIABLE f a x n)
     (IMPLIES (IN t (CCINT a x))
       (IS-CONTINUOUS-AT RR-MS RR-MS (VNB-LAMBDA z RR (- (f x) (TAYLOR-POLY f z n x))) t))))))))))))
(dk-peel-to! 'IS-CONTINUOUS-AT)
(define tgc-g-s (tgc-sum-lam 'f 'x 'n))
(define (tgc-g-sps v) (list 'SERIES-PARTIAL-SUM (subst-free 'z v (tgc-term 'f 'x)) '(succ n)))
;; CH(f,t,n) out of TAYLOR-DIFFERENTIABLE's first conjunct, on a side branch.
(have! (tgc-ch 'f 't 'n)
  (lambda ()
    (dk-split! (dk-landed-1 (lambda () (mac-h 'TAYLOR-DIFFERENTIABLE '(TAYLOR-DIFFERENTIABLE f a x n)))))
    (di)
    (let* ((landed (dk-landed-1 (lambda () (di))))                    ; (AND (IN k NN) (<= k n)), kept whole
           (kv     (cadr (cadr landed)))
           (c1     (tgc-find (lambda (u) (and (pair? u) (eq? (car u) 'FORALL)
                                              (tgc-mentions? 'IS-CONTINUOUS-AT u)))
                             'the-continuity-conjunct)))
      (let ((at-k (dk-deepest (lambda () (inst+ c1 kv)))))
        (inst+ at-k 't)                                               ; (IN t (CCINT a x)) is in context
        (ass)))))
;; t in RR and f in FUN RR RR, both off CH at k = 0
(fact 'nn-zero-in)
(fact 'nn-zero-le 'n)
(have! '(AND (IN 0 NN) (<= 0 n)))
(define tgc-g-h0 (dk-deepest (lambda () (inst+ (tgc-ch 'f 't 'n) 0))))
(tgc-check-head! tgc-g-h0 'IS-CONTINUOUS-AT "CH at 0")
(tgc-point! tgc-g-h0)                                                 ; (IN t RR)
(define tgc-g-h0f (dk-landed-1 (lambda () (mac-h 'nth-deriv-zero tgc-g-h0))))
(tgc-fun! tgc-g-h0f)                                                  ; f in FUN RR RR
(fact 'fun-apply-type-c 'f 'RR 'RR 'x)                                ; f(x) in RR
;; S_n continuous at t
(define tgc-g-hs (dk-fact! 'tgc-sum-cont 'n 'f 'x 't))
(tgc-check-head! tgc-g-hs 'IS-CONTINUOUS-AT "tgc-sum-cont did not detach")
(tgc-fun! tgc-g-hs)                                                   ; S_n in FUN RR RR
;; the constant f(x), and the difference
(define tgc-g-kc (dk-fact! 'const-continuous-at '(f x) 't))
(tgc-check-head! tgc-g-kc 'IS-CONTINUOUS-AT "const-continuous-at")
(define tgc-g-sub (dk-fact! 'sub-continuous-at (cadddr tgc-g-kc) tgc-g-s 't))
(tgc-check-head! tgc-g-sub 'IS-CONTINUOUS-AT "sub-continuous-at did not detach")
(define tgc-g-sub2 (dk-landed-1 (lambda () (lam-b-h tgc-g-sub))))     ; z |-> f(x) - SPS(term_z, succ n)
(define tgc-g-sub-lam (cadddr tgc-g-sub2))
;; G is a function RR -> RR ...
(have! (list 'IN tgc-gt '(FUN RR RR))
  (lambda ()
    (dk-lam-t!)
    (let ((v (dk-di-var!)))
      (mac 'TAYLOR-POLY)
      (fact 'fun-apply-type-c tgc-g-s 'RR 'RR v)
      (lam-b-h (list 'IN (list tgc-g-s v) 'RR))
      (fact 'rr-sub-in-rr '(f x) (tgc-g-sps v))
      (ass))))
;; ... and agrees pointwise with the difference lambda
(have! (list 'FORALL 'x_ (list 'IMPLIES '(IN x_ RR)
              (list '= (list tgc-gt 'x_) (list tgc-g-sub-lam 'x_))))
  (lambda ()
    (let ((v (dk-di-var!)))
      (tgc-beta!)
      (mac 'TAYLOR-POLY)
      (fact 'fun-apply-type-c tgc-g-s 'RR 'RR v)
      (lam-b-h (list 'IN (list tgc-g-s v) 'RR))
      (fact 'rr-sub-in-rr '(f x) (tgc-g-sps v))
      (if (not (alpha-equiv? (cadr (dk-goal)) (caddr (dk-goal))))
          (error "taylor-gmvt-guarded: G and the difference lambda did not meet" (dk-goal)))
      (rfl))))
(fact 'cont-transfer-ptwise-eq tgc-gt tgc-g-sub-lam 't)
(ass)
(qed 'taylor-G-cont)
(topic! 'taylor-G-cont 'analysis)

;;; =====================================================================
;;; (5) taylor-gmvt-cont, guarded by n in NN: (1) and (4) at t in [a,x].
;;; =====================================================================
(sp (make-wff
  (list 'FORALL 'f (list 'FORALL 'a (list 'FORALL 'x (list 'FORALL 'n
     (list 'IMPLIES '(TAYLOR-DIFFERENTIABLE f a x n)
     (list 'IMPLIES '(IN x RR) (list 'IMPLIES '(IN n NN) tgc-ghcont)))))))))
(dk-peel-to! 'AND)
(define tgc-c-mem '(AND (IN t RR) (AND (<= a t) (<= t x))))
(fact 'ccint-membership 'a 'x 't)
(ai (list 'IFF '(IN t (CCINT a x)) tgc-c-mem))
(detach! (list 'IMPLIES '(IN t (CCINT a x)) tgc-c-mem))
(dk-split! tgc-c-mem)                                                 ; (IN t RR) ...
(fact 'taylor-G-cont 'f 'a 'x 'n 't)
(fact 'taylor-H-cont 'x 'n 't)
(dk-conj-close!)
(qed 'taylor-gmvt-cont)
(topic! 'taylor-gmvt-cont 'analysis)

;;; =====================================================================
;;; (6) taylor-gmvt-diff, guarded by n in NN, x in RR: the explicit
;;; derivatives taylor-G-diff / taylor-h-diff give, existentially closed.
;;; =====================================================================
(sp (make-wff
  (list 'FORALL 'f (list 'FORALL 'a (list 'FORALL 'x (list 'FORALL 'n
     (list 'IMPLIES '(TAYLOR-DIFFERENTIABLE f a x n)
     (list 'IMPLIES '(IN n NN) (list 'IMPLIES '(IN x RR) tgc-ghdiff)))))))))
(dk-peel-to! 'AND)
(define tgc-d-t (caddr (caddr (cadr (dk-goal)))))                     ; the point, off the goal
(if (not (eq? tgc-d-t 't)) (error "taylor-gmvt-guarded: the point is not t" tgc-d-t))
(dk-split! '(AND (IN t RR) (AND (< a t) (< t x))))
(have! '(AND (< a t) (< t x)))                                        ; taylor-G-diff's antecedent, whole
(fact 'taylor-G-diff 'f 'a 'x 'n 't)                                  ; IS-DIFF-AT GT t (GVAL t)
(fact 'taylor-h-diff 'x 'n 't)                                        ; IS-DIFF-AT HT t (HVAL t)
(have! (list 'FORSOME 'L (list 'IS-DIFF-AT tgc-gt 't 'L))
       (lambda () (ew (tgc-gval 't)) (ass)))
(have! (list 'FORSOME 'M (list 'IS-DIFF-AT tgc-ht 't 'M))
       (lambda () (ew (tgc-hval 't)) (ass)))
(dk-conj-close!)
(qed 'taylor-gmvt-diff)
(topic! 'taylor-gmvt-diff 'analysis)
