;;; theorem-library/taylor-guarded.scm -- the endpoint / typing / derivative
;;; facts of Taylor's theorem, GUARDED and PROVEN.
;;;
;;; Eight supports of taylor-proof.scm were found FALSE AS WRITTEN (triage
;;; 2026-09-14): a binder was unguarded, so a beta redex at a non-real point,
;;; a power with a non-natural exponent, or a derivative of a function nobody
;;; said was differentiable, was undefined -- and `=' is partial.  The user's
;;; decision (2026-09-14): add the guards, prove the guarded statements.
;;;
;;; The ONE guard the G-side facts need is that the derivatives up to order n
;;; are total real functions:
;;;
;;;     DFUN(f,n)  :=  forall k. k in NN and k <= n  =>  NTH-DERIV(f,k) in FUN(RR,RR)
;;;
;;; That is what makes TAYLOR-POLY(f,z,n,x) a real number at EVERY real z, hence
;;; G a function RR -> RR, hence G(a) and G(x) defined.  TAYLOR-DIFFERENTIABLE
;;; (the citer's hypothesis) implies it -- `taylor-derivs-in-fun' below, through
;;; the FUN(PTS,PTS) conjunct of IS-CONTINUOUS-AT at the point a of [a,x] -- so
;;; the citer lands DFUN in ONE `fact' and every guarded G-fact then
;;; auto-detaches.  DFUN rather than TAYLOR-DIFFERENTIABLE itself as the guard
;;; because (i) the binder lists stay byte-identical (TD would add `a' to
;;; taylor-G-at-x and taylor-G-in-fun, whose statements never mention the
;;; interval), (ii) G(x) = 0 and G in FUN(RR,RR) have nothing to do with [a,x],
;;; and (iii) one hypothesis serves all four.
;;;
;;; Statements (the guard additions are the only change; binders and bodies
;;; are byte-identical to the support sites in taylor-proof.scm):
;;;   taylor-poly-in-rr   + DFUN
;;;   taylor-G-in-fun     + DFUN
;;;   taylor-G-at-a       + f in FUN(RR,RR), a in RR, x in RR, n in NN, DFUN
;;;   taylor-G-at-x       + f in FUN(RR,RR), x in RR, DFUN
;;;   taylor-H-at-a       + a in RR, x in RR, n in NN
;;;   taylor-H-at-x       + x in RR
;;;   taylor-H-diff       + n in NN
;;;   taylor-deriv-real   + n in NN
;;;   taylor-H-in-fun     unchanged (it was the one properly guarded)
;;;
;;; LOAD WINDOW.  This file cites `taylor-poly-at-center', `power-zero-succ',
;;; `recip-factorial-in-rr', `rr-zero-mul' -- all PROVEN in taylor-proof.scm
;;; ABOVE its support block (lines 138-431) -- and is cited by `taylor-lagrange'
;;; at the END of the same file (line 541).  So it must load between
;;; taylor-proof.scm:431 and taylor-proof.scm:541: the integrator either splices
;;; this file's body in at the support block, or splits taylor-proof.scm into
;;; its lemma half and its headline half and wires this file between them.
;;; Everything else cited loads well before taylor-proof: deriv-power /
;;; pow-lam-in-fun (deriv-power.scm), deriv-chain (chain-rule.scm),
;;; diff-transfer-ptwise-eq (diff-transfer.scm), deriv-sum (deriv-sum-product),
;;; deriv-const / deriv-identity (differentiation.scm), deriv-neg /
;;; diff-value-real (mvt-cluster-readoffs.scm), compose-apply, fun-apply-type-c,
;;; ccint-membership, power-closed-at (dyadic-weights), rr-sub-in-rr,
;;; rr-lt-implies-le, nn-le-refl / nn-le-trans-guarded, nn-le-succ,
;;; series-partial-sum-zero / -succ.
;;;
;;; Helper prefix: tg-.

;;; ---- file-local shapes ----
(define tg-gt '(VNB-LAMBDA z RR (- (f x) (TAYLOR-POLY f z n x))))
(define tg-ht '(VNB-LAMBDA z RR (power (- x z) (succ n))))
(define (tg-hval t) (list '- 0 (list '* '(succ n) (list 'power (list '- 'x t) 'n))))
;;; DFUN(f,n)
(define (tg-dfun f n)
  (list 'FORALL 'k (list 'IMPLIES (list 'AND '(IN k NN) (list '<= 'k n))
                         (list 'IN (list 'NTH-DERIV f 'k) '(FUN RR RR)))))
;;; the pointwise guard at the point a (taylor-poly-at-center's shape)
(define (tg-guard f a n)
  (list 'FORALL 'k (list 'IMPLIES (list 'AND '(IN k NN) (list '<= 'k n))
                         (list 'IN (list (list 'NTH-DERIV f 'k) a) 'RR))))
;;; the Taylor summand k |-> f^(k)(a) (x-a)^k recip(k!)  (TAYLOR-POLY's body)
(define (tg-term f a x)
  (list 'VNB-LAMBDA 'k 'NN
        (list '* (list '* (list (list 'NTH-DERIV f 'k) a) (list 'power (list '- x a) 'k))
                 (list 'recip (list 'FACTORIAL 'k)))))

(define (tg-mentions? sym form)
  (cond ((eq? form sym) #t)
        ((pair? form) (or (tg-mentions? sym (car form)) (tg-mentions? sym (cdr form))))
        (#t #f)))
(define (tg-pick pred what)
  (or (find-first pred (dk-asms)) (error "taylor-guarded: no assumption" what)))

;;; (IN (* a b) RR) from the two factor typings already in context
(define (tg-mul-real! a b)
  (have! (list 'AND (list 'IN a 'RR) (list 'IN b 'RR)))
  (fact 'rr-mul-closed a b))
(define (tg-add-real! a b)
  (have! (list 'AND (list 'IN a 'RR) (list 'IN b 'RR)))
  (fact 'rr-add-closed a b))

;;; lam-b the goal to a fixpoint (nested redexes appear one reduction at a time)
(define (tg-beta!)
  (let loop ((k 0) (prev #f))
    (let ((g (dk-goal)))
      (if (and (< k 8) (not (equal? g prev)))
          (begin (quietly (lambda () (vnb-guard (lambda () (lam-b))))) (loop (+ k 1) g))))))

;;; =====================================================================
;;; (1) TAYLOR-DIFFERENTIABLE(f,a,x,n), a < x  =>  DFUN(f,n).
;;; The continuity conjunct at the point a of [a,x] carries the typing
;;; NTH-DERIV(f,k) in FUN(PTS RR-MS, PTS RR-MS).
;;; =====================================================================
(sp (make-wff
  (list 'FORALL 'f (list 'FORALL 'a (list 'FORALL 'x (list 'FORALL 'n
    (list 'IMPLIES '(TAYLOR-DIFFERENTIABLE f a x n)
    (list 'IMPLIES '(IN a RR) (list 'IMPLIES '(IN x RR) (list 'IMPLIES '(< a x)
      (tg-dfun 'f 'n)))))))))))
(dk-peel-to! 'IN)
(let* ((g   (dk-goal))                                  ; (IN (NTH-DERIV f k) (FUN RR RR))
       (nd  (cadr g))
       (f   (cadr nd))
       (k   (caddr nd))
       (td  (tg-pick (dk-head? 'TAYLOR-DIFFERENTIABLE) "TAYLOR-DIFFERENTIABLE"))
       (a   (caddr td))
       (x   (cadddr td))
       (mem (list 'AND (list 'IN a 'RR) (list 'AND (list '<= a a) (list '<= a x)))))
  ;; a in CCINT(a,x)
  (fact 'rr-leq-reflexive a)
  (fact 'rr-lt-implies-le a x)
  (have! mem)
  (fact 'ccint-membership a x a)
  (ai (list 'IFF (list 'IN a (list 'CCINT a x)) mem))
  (detach! (list 'IMPLIES mem (list 'IN a (list 'CCINT a x))))
  ;; unfold the hypothesis; the continuity conjunct at k, at the point a
  (let* ((parts (dk-split! (dk-landed-1 (lambda () (mac-h 'taylor-differentiable td)))))
         (cont  (or (find-first (lambda (p) (tg-mentions? 'IS-CONTINUOUS-AT p)) parts)
                    (error "taylor-guarded: no continuity conjunct")))
         (u1    (dk-deepest (lambda () (inst+ cont k))))
         (u2    (dk-deepest (lambda () (inst+ u1 a)))))
    (dk-split! (dk-landed-1 (lambda () (mac-h 'is-continuous-at u2))))
    (slot-h 'PTS (list 'IN nd '(FUN (PTS RR-MS) (PTS RR-MS))))
    (ass)))
(qed 'taylor-derivs-in-fun)
(topic! 'taylor-derivs-in-fun 'analysis)
(alias! 'taylor-derivs-in-fun
        "a Taylor-differentiable f has total real derivatives up to order n")

;;; =====================================================================
;;; (2) DFUN(f,n), t in RR  =>  f^(k)(t) in RR for k <= n.
;;; =====================================================================
(sp (make-wff
  (list 'FORALL 'f (list 'FORALL 'n
    (list 'IMPLIES (tg-dfun 'f 'n)
      (list 'FORALL 't (list 'IMPLIES '(IN t RR) (tg-guard 'f 't 'n))))))))
(dk-peel-to! 'IN)
(let* ((g   (dk-goal))                                  ; (IN ((NTH-DERIV f k) t) RR)
       (app (cadr g))
       (nd  (car app))
       (t   (cadr app))
       (k   (caddr nd))
       (dfun (tg-pick (lambda (u) (and (pair? u) (eq? (car u) 'FORALL) (tg-mentions? 'FUN u)))
                      "DFUN")))
  (dk-deepest (lambda () (inst+ dfun k)))
  (fact 'fun-apply-type-c nd 'RR 'RR t)
  (ass))
(qed 'taylor-derivs-values-real)
(topic! 'taylor-derivs-values-real 'analysis)

;;; =====================================================================
;;; (3) The partial sum is real when the derivatives at the centre are:
;;; induction on the degree, taylor-center-partial-sum's shape.
;;; =====================================================================
(sp (make-wff
  (list 'FORALL 'n (list 'IMPLIES '(IN n NN)
    (list 'FORALL 'f (list 'FORALL 'a (list 'IMPLIES '(IN a RR)
      (list 'FORALL 'x (list 'IMPLIES '(IN x RR)
        (list 'IMPLIES (tg-guard 'f 'a 'n)
          (list 'IN (list 'SERIES-PARTIAL-SUM (tg-term 'f 'a 'x) '(succ n)) 'RR)))))))))))
(define tg-br (use-induction))
(define tg-n  (cdr (assq 'var tg-br)))
(define tg-ih (cdr (assq 'ih  tg-br)))

;; read f, a, x off the summand in the GOAL
(define (tg-goal-term) (cadr (cadr (dk-goal))))
(define (tg-term-f tm) (cadr (car (cadr (cadr (cadddr tm))))))
(define (tg-term-a tm) (cadr (cadr (cadr (cadddr tm)))))
(define (tg-term-x tm) (cadr (cadr (caddr (cadr (cadddr tm))))))

;; the summand at index idx is real: beta, then the three factor typings
(define (tg-term-real! tm idx)
  (let* ((f (tg-term-f tm)) (a (tg-term-a tm)) (x (tg-term-x tm))
         (dv (list (list 'NTH-DERIV f idx) a))
         (pw (list 'power (list '- x a) idx))
         (rc (list 'recip (list 'FACTORIAL idx))))
    (have! (list 'IN (list tm idx) 'RR)
      (lambda ()
        (lam-b)
        (fact 'rr-sub-in-rr x a)
        (fact 'power-closed-at idx (list '- x a))
        (fact 'recip-factorial-in-rr idx)
        (tg-mul-real! dv pw)
        (tg-mul-real! (list '* dv pw) rc)
        (ass)))))

;;; --- base: SPS(term, succ 0) = SPS(term, 0) + term(0) ---
(dk-focus! (cdr (assq 'base tg-br)))
(dk-peel-to! 'IN)
(let* ((tm (tg-goal-term)) (f (tg-term-f tm)) (a (tg-term-a tm)) (x (tg-term-x tm)))
  (fact 'nn-zero-in)
  (fact 'nn-le-refl 0)
  (have! '(AND (IN 0 NN) (<= 0 0)))
  (inst+ (tg-guard f a 0) 0)                             ; f^(0)(a) in RR
  (tg-term-real! tm 0)
  (have! (list 'IN (list 'SERIES-PARTIAL-SUM tm 0) 'RR)
         (lambda () (mac 'series-partial-sum-zero) (fact 'rr-zero-in) (ass)))
  (dk-sps-succ! tm 0)
  (tg-add-real! (list 'SERIES-PARTIAL-SUM tm 0) (list tm 0))
  (ass))

;;; --- step: SPS(term, succ(succ n)) = SPS(term, succ n) + term(succ n) ---
(dk-focus! (cdr (assq 'step tg-br)))
(dk-peel-to! 'IN)
(let* ((tm (tg-goal-term)) (f (tg-term-f tm)) (a (tg-term-a tm)) (x (tg-term-x tm))
       (sn (list 'succ tg-n)))
  (fact 'nn-succ-closed tg-n)
  (fact 'nn-le-succ tg-n)                                ; n <= succ n
  ;; the goal's guard is at succ n; the hypothesis wants it at n
  (have! (tg-guard f a tg-n)
    (lambda ()
      (di)
      (let* ((landed (dk-landed-1 (lambda () (di))))    ; (AND (IN k NN) (<= k n))
             (kv     (cadr (cadr landed))))
        (dk-split! landed)
        (fact 'nn-le-trans-guarded kv tg-n sn)
        (have! (list 'AND (list 'IN kv 'NN) (list '<= kv sn)))
        (inst+ (tg-guard f a sn) kv)
        (ass))))
  (let* ((ih1 (dk-deepest (lambda () (inst+ tg-ih f))))
         (ih2 (dk-deepest (lambda () (inst+ ih1 a)))))
    (dk-deepest (lambda () (inst+ ih2 x))))             ; SPS(term, succ n) in RR
  ;; the term at succ n
  (fact 'nn-le-refl sn)
  (have! (list 'AND (list 'IN sn 'NN) (list '<= sn sn)))
  (inst+ (tg-guard f a sn) sn)                           ; f^(succ n)(a) in RR
  (tg-term-real! tm sn)
  (dk-sps-succ! tm sn)
  (tg-add-real! (list 'SERIES-PARTIAL-SUM tm sn) (list tm sn))
  (ass))
(qed 'taylor-poly-in-rr-at)
(topic! 'taylor-poly-in-rr-at 'analysis)
(alias! 'taylor-poly-in-rr-at
        "the Taylor partial sum is real when the derivatives at the centre are")

;;; =====================================================================
;;; (4) taylor-poly-in-rr, guarded by DFUN.
;;; =====================================================================
(sp (make-wff
  (list 'FORALL 'f (list 'IMPLIES '(IN f (FUN RR RR)) (list 'FORALL 'a (list 'IMPLIES '(IN a RR)
    (list 'FORALL 'n (list 'IMPLIES '(IN n NN)
      (list 'FORALL 'x (list 'IMPLIES '(IN x RR)
        (list 'IMPLIES (tg-dfun 'f 'n)
          '(IN (TAYLOR-POLY f a n x) RR))))))))))))
(dk-peel-to! 'IN)
(mac 'TAYLOR-POLY)
(fact 'taylor-derivs-values-real 'f 'n 'a)
(fact 'taylor-poly-in-rr-at 'n 'f 'a 'x)
(ass)
(qed 'taylor-poly-in-rr)
(topic! 'taylor-poly-in-rr 'analysis)

;;; =====================================================================
;;; (5) taylor-G-in-fun, guarded by DFUN.
;;; =====================================================================
(sp (make-wff
  (list 'FORALL 'n (list 'IMPLIES '(IN n NN)
    (list 'FORALL 'f (list 'IMPLIES '(IN f (FUN RR RR)) (list 'FORALL 'x (list 'IMPLIES '(IN x RR)
      (list 'IMPLIES (tg-dfun 'f 'n)
        (list 'IN tg-gt '(FUN RR RR)))))))))))
(dk-peel-to! 'IN)
(dk-lam-t!)
(let ((z (dk-di-var!)))
  (fact 'fun-apply-type-c 'f 'RR 'RR 'x)
  (fact 'taylor-poly-in-rr 'f z 'n 'x)
  (fact 'rr-sub-in-rr '(f x) (list 'TAYLOR-POLY 'f z 'n 'x))
  (ass))
(qed 'taylor-g-in-fun)
(topic! 'taylor-g-in-fun 'analysis)

;;; =====================================================================
;;; (6) taylor-H-in-fun -- statement unchanged.
;;; =====================================================================
(sp (make-wff
  (list 'FORALL 'n (list 'IMPLIES '(IN n NN)
    (list 'FORALL 'x (list 'IMPLIES '(IN x RR) (list 'IN tg-ht '(FUN RR RR))))))))
(dk-peel-to! 'IN)
(dk-lam-t!)
(let ((z (dk-di-var!)))
  (fact 'nn-succ-closed 'n)
  (fact 'rr-sub-in-rr 'x z)
  (fact 'power-closed-at '(succ n) (list '- 'x z))
  (ass))
(qed 'taylor-h-in-fun)
(topic! 'taylor-h-in-fun 'analysis)

;;; =====================================================================
;;; (7) taylor-H-at-a: beta, then reflexivity against the power's typing.
;;; =====================================================================
(sp (make-wff
  (list 'FORALL 'a (list 'FORALL 'x (list 'FORALL 'n
    (list 'IMPLIES '(IN a RR) (list 'IMPLIES '(IN x RR) (list 'IMPLIES '(IN n NN)
      (list '= (list tg-ht 'a) '(power (- x a) (succ n)))))))))))
(dk-peel-to! '=)
(lam-b)
(fact 'nn-succ-closed 'n)
(fact 'rr-sub-in-rr 'x 'a)
(fact 'power-closed-at '(succ n) '(- x a))
(rfl)
(qed 'taylor-h-at-a)
(topic! 'taylor-h-at-a 'analysis)

;;; =====================================================================
;;; (8) taylor-H-at-x: beta, x - x = 0, 0^(succ n) = 0.
;;; =====================================================================
(sp (make-wff
  (list 'FORALL 'x (list 'FORALL 'n (list 'IMPLIES '(IN n NN) (list 'IMPLIES '(IN x RR)
    (list '= (list tg-ht 'x) 0)))))))
(dk-peel-to! '=)
(lam-b)
(have! '(= (- x x) 0) (lambda () (crs)))
(subst '(= (- x x) 0))
(fact 'power-zero-succ 'n)
(ass)
(qed 'taylor-h-at-x)
(topic! 'taylor-h-at-x 'analysis)

;;; =====================================================================
;;; (9) taylor-G-at-a: beta, then reflexivity against the remainder's typing.
;;; =====================================================================
(sp (make-wff
  (list 'FORALL 'f (list 'FORALL 'a (list 'FORALL 'x (list 'FORALL 'n
    (list 'IMPLIES '(IN f (FUN RR RR)) (list 'IMPLIES '(IN a RR) (list 'IMPLIES '(IN x RR)
    (list 'IMPLIES '(IN n NN) (list 'IMPLIES (tg-dfun 'f 'n)
      (list '= (list tg-gt 'a) '(- (f x) (TAYLOR-POLY f a n x))))))))))))))
(dk-peel-to! '=)
(lam-b)
(fact 'fun-apply-type-c 'f 'RR 'RR 'x)
(fact 'taylor-poly-in-rr 'f 'a 'n 'x)
(fact 'rr-sub-in-rr '(f x) '(TAYLOR-POLY f a n x))
(rfl)
(qed 'taylor-g-at-a)
(topic! 'taylor-g-at-a 'analysis)

;;; =====================================================================
;;; (10) taylor-G-at-x: beta, taylor-poly-at-center, f(x) - f(x) = 0.
;;; =====================================================================
(sp (make-wff
  (list 'FORALL 'f (list 'FORALL 'x (list 'FORALL 'n (list 'IMPLIES '(IN n NN)
    (list 'IMPLIES '(IN f (FUN RR RR)) (list 'IMPLIES '(IN x RR)
    (list 'IMPLIES (tg-dfun 'f 'n)
      (list '= (list tg-gt 'x) 0))))))))))
(dk-peel-to! '=)
(lam-b)
(fact 'taylor-derivs-values-real 'f 'n 'x)
(fact 'taylor-poly-at-center 'f 'x 'n)
(subst '(= (TAYLOR-POLY f x n x) (f x)))
(fact 'fun-apply-type-c 'f 'RR 'RR 'x)
(crs)
(qed 'taylor-g-at-x)
(topic! 'taylor-g-at-x 'analysis)

;;; =====================================================================
;;; (11) taylor-deriv-real: f^(n+1)(t) is the derivative value IS-DIFF-AT
;;; carries for f^(n) at t, hence real (diff-value-real).
;;; =====================================================================
(sp (make-wff
  '(FORALL f (FORALL a (FORALL x (FORALL n (FORALL t
     (IMPLIES (TAYLOR-DIFFERENTIABLE f a x n)
     (IMPLIES (< a t) (IMPLIES (< t x) (IMPLIES (IN n NN)
       (IN ((NTH-DERIV f (succ n)) t) RR))))))))))))
(dk-peel-to! 'IN)
(let* ((g   (dk-goal))                                  ; (IN ((NTH-DERIV f (succ n)) t) RR)
       (app (cadr g))
       (t   (cadr app))
       (f   (cadr (car app)))
       (n   (cadr (caddr (car app))))
       (td  (tg-pick (dk-head? 'TAYLOR-DIFFERENTIABLE) "TAYLOR-DIFFERENTIABLE"))
       (a   (caddr td))
       (x   (cadddr td)))
  (fact 'nn-le-refl n)
  (have! (list 'AND (list 'IN n 'NN) (list '<= n n)))
  (have! (list 'AND (list '< a t) (list '< t x)))
  (let* ((parts (dk-split! (dk-landed-1 (lambda () (mac-h 'taylor-differentiable td)))))
         (dcon  (or (find-first (lambda (p) (tg-mentions? 'IS-DIFF-AT p)) parts)
                    (error "taylor-guarded: no differentiability conjunct")))
         (u1    (dk-deepest (lambda () (inst+ dcon n))))
         (u2    (dk-deepest (lambda () (inst+ u1 t)))))  ; IS-DIFF-AT f^(n) t f^(n+1)(t)
    (fact 'diff-value-real (cadr u2) (caddr u2) (cadddr u2))
    (ass)))
(qed 'taylor-deriv-real)
(topic! 'taylor-deriv-real 'analysis)

;;; =====================================================================
;;; (12) taylor-H-diff:  d/dt (x-t)^(n+1) = -(n+1)(x-t)^n.
;;; Chain rule: outer u |-> u^(succ n) (deriv-power), inner z |-> x - z, itself
;;; assembled from deriv-const + deriv-neg(deriv-identity) by deriv-sum and
;;; carried to the literal lambda by diff-transfer-ptwise-eq; the composite is
;;; carried to HT the same way, through compose-apply.
;;; =====================================================================
;; the value identity, over VARIABLES (crs sees no symbolic power)
(sp (make-wff '(FORALL s (IMPLIES (IN s RR) (FORALL p (IMPLIES (IN p RR)
   (= (- 0 (* s p)) (* (* s p) (+ 0 (- 1))))))))))
(dk-peel-to! '=)
(crs)
(qed 'tg-neg-scale)
(topic! 'tg-neg-scale 'plumbing)

(sp (make-wff
  (list 'FORALL 'x (list 'FORALL 'n (list 'FORALL 't
    (list 'IMPLIES '(IN x RR) (list 'IMPLIES '(IN t RR) (list 'IMPLIES '(IN n NN)
      (list 'IS-DIFF-AT tg-ht 't (tg-hval 't))))))))))
(dk-peel-to! 'IS-DIFF-AT)
(define tg-fin '(VNB-LAMBDA z RR (- x z)))              ; the inner map
(define tg-lin '(+ 0 (- 1)))                            ; its derivative value
;; --- inner map: differentiable at t with value 0 + (-1) ---
(have! '(AND (IN x RR) (IN t RR)))
(define tg-fc (cadr (dk-fact! 'deriv-const 'x 't)))    ; lambda _. x   (bound var renamed)
(fact 'deriv-identity 't)
(define tg-fn (cadr (dk-fact! 'deriv-neg '(VNB-LAMBDA x RR x) 't 1)))   ; lambda z. -(id z)
(have! (list 'AND (list 'IS-DIFF-AT tg-fc 't 0) (list 'IS-DIFF-AT tg-fn 't '(- 1))))
(define tg-fsum (cadr (dk-fact! 'deriv-sum tg-fc tg-fn 't 0 '(- 1))))
(have! (list 'IN tg-fin '(FUN RR RR))
  (lambda () (dk-lam-t!) (let ((z (dk-di-var!))) (fact 'rr-sub-in-rr 'x z) (ass))))
(have! (list 'FORALL 'x_ (list 'IMPLIES '(IN x_ RR) (list '== (list tg-fin 'x_) (list tg-fsum 'x_))))
  (lambda ()
    (let ((v (dk-di-var!)))
      (tg-beta!)                                        ; (- x v) == (+ x (- v))
      (have! (list '= (list '- 'x v) (list '+ 'x (list '- v))) (lambda () (crs)))
      (subst (list '= (list '- 'x v) (list '+ 'x (list '- v))))
      (qrfl))))
(fact 'diff-transfer-ptwise-eq tg-fin tg-fsum 't tg-lin)   ; IS-DIFF-AT fin t (0 + -1)
;; --- outer map at the inner value ---
(fact 'fun-apply-type-c tg-fin 'RR 'RR 't)              ; (fin t) in RR
(define tg-gout (cadr (dk-fact! 'deriv-power 'n (list tg-fin 't))))
(define tg-mv  (list '* '(succ n) (list 'power (list tg-fin 't) 'n)))
;; --- chain ---
(define tg-comp (cadr (dk-fact! 'deriv-chain tg-fin tg-gout 't tg-lin tg-mv)))
(lam-b-h (list 'IS-DIFF-AT tg-comp 't (list '* tg-mv tg-lin)))   ; (fin t) -> (- x t)
(define tg-pw (list 'power '(- x t) 'n))
(define tg-val (list '* (list '* '(succ n) tg-pw) tg-lin))
;; --- the value, and the transfer to HT ---
(fact 'nn-succ-closed 'n)
(fact 'nn-in-rr '(succ n))
(fact 'rr-sub-in-rr 'x 't)
(fact 'power-closed-at 'n '(- x t))
(fact 'tg-neg-scale '(succ n) tg-pw)
(subst (list '= (tg-hval 't) tg-val))                   ; goal: IS-DIFF-AT HT t VAL
(fact 'taylor-h-in-fun 'n 'x)
(fact 'pow-lam-in-fun '(succ n))
(have! (list 'AND (list 'IN tg-fin '(FUN RR RR)) (list 'IN tg-gout '(FUN RR RR))))
(have! (list 'FORALL 'x_ (list 'IMPLIES '(IN x_ RR) (list '== (list tg-ht 'x_) (list tg-comp 'x_))))
  (lambda ()
    (let ((v (dk-di-var!)))
      (fact 'compose-apply 'RR 'RR 'RR tg-gout tg-fin v)
      (subst (list '= (list tg-comp v) (list tg-gout (list tg-fin v))))
      (fact 'fun-apply-type-c tg-fin 'RR 'RR v)         ; licence for the outer redex
      (fact 'rr-sub-in-rr 'x v)
      (tg-beta!)
      (qrfl))))
(fact 'diff-transfer-ptwise-eq tg-ht tg-comp 't tg-val)
(ass)
(qed 'taylor-h-diff)
(topic! 'taylor-h-diff 'analysis)
