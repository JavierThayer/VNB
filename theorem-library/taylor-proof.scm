;;; theorem-library/taylor-proof.scm -- Taylor's theorem, Lagrange remainder.
;;;   f^(n) C^0 on [a,x], f^(n+1) exists on (a,x), a<x  =>  there is theta in
;;;   (a,x) with  (n+1)! * R_n(x) = f^(n+1)(theta) * (x-a)^(n+1),
;;;   where R_n(x) = f(x) - TAYLOR-POLY(f,a,n,x).
;;; Strategy (Cauchy-MVT route): apply generalized-mvt to
;;;     G(t) = f(x) - TAYLOR-POLY(f,t,n,x)        (remainder as a fn of the base)
;;;     H(t) = (x-t)^(n+1)
;;; on [a,x].  G(x)=0, G(a)=R_n; H(x)=0, H(a)=(x-a)^(n+1); the telescoping
;;;     G'(t) = -(f^(n+1)(t)/n!)(x-t)^n,   H'(t) = -(n+1)(x-t)^n
;;; are warranted calc-101 supports (the f^(n+1)/n! (x-t)^n collapse of the
;;; differentiated Taylor sum; same warrant style as mvt-aux-diff/gmvt-aux-diff).
;;; gMVT gives G'(theta)(H(x)-H(a)) = H'(theta)(G(x)-G(a)); substituting and
;;; cancelling (x-theta)^n (>0) clears to the stated identity.
;;; Reuses deriv-constant-proof's global dc-* helpers; loads after
;;; generalized-mvt-proof.  Uses `fact', no bc*.
;;; ====================================================================

;;; TAYLOR-POLY(f,a,n,x) = Sum_{k=0}^{n} f^(k)(a) (x-a)^k / k!
(def-functoid 'TAYLOR-POLY '(f a n x)
  '(SERIES-PARTIAL-SUM
     (VNB-LAMBDA k (* (* ((NTH-DERIV f k) a) (power (- x a) k)) (recip (FACTORIAL k))))
     (succ n)))

;;; TAYLOR-DIFFERENTIABLE(f,a,x,n): f^(k) (k<=n) continuous on [a,x] and
;;; differentiable on (a,x) with derivative f^(k+1).  The clean hypothesis.
(def-predicate 'TAYLOR-DIFFERENTIABLE '(f a x n)
  '(AND
     (FORALL k (IMPLIES (AND (IN k NN) (<= k n))
        (FORALL t (IMPLIES (IN t (CCINT a x))
           (IS-CONTINUOUS-AT RR-MS RR-MS (NTH-DERIV f k) t)))))
     (FORALL k (IMPLIES (AND (IN k NN) (<= k n))
        (FORALL t (IMPLIES (AND (< a t) (< t x))
           (IS-DIFF-AT (NTH-DERIV f k) t ((NTH-DERIV f (succ k)) t))))))))

;;; file-local auxiliary functions (free f,x,n; bind z -- NOT the point var, to
;;; avoid capture-rename when instantiating a support at point t)
(define GT '(VNB-LAMBDA z (- (f x) (TAYLOR-POLY f z n x))))
(define HT '(VNB-LAMBDA z (power (- x z) (succ n))))
;;; their warranted derivative values at t
(define (GVAL t) (list '- 0 (list '* (list '* '(recip (FACTORIAL n)) (list (list 'NTH-DERIV 'f '(succ n)) t)) (list 'power (list '- 'x t) 'n))))
(define (HVAL t) (list '- 0 (list '* '(succ n) (list 'power (list '- 'x t) 'n))))
;;; the gMVT-shaped continuity / differentiability hypotheses for (GT, HT)
(define GHCONT (list 'FORALL 't (list 'IMPLIES '(IN t (CCINT a x))
                 (list 'AND (list 'IS-CONTINUOUS-AT 'RR-MS 'RR-MS GT 't)
                            (list 'IS-CONTINUOUS-AT 'RR-MS 'RR-MS HT 't)))))
(define GHDIFF (list 'FORALL 't (list 'IMPLIES '(AND (< a t) (< t x))
                 (list 'AND (list 'FORSOME 'L (list 'IS-DIFF-AT GT 't 'L))
                            (list 'FORSOME 'M (list 'IS-DIFF-AT HT 't 'M))))))

;;; --- warranted calc-101 supports for G, H ---
(add-to-pss 'taylor-G-cont
  `(FORALL f (FORALL a (FORALL x (FORALL n (FORALL t
     (IMPLIES (TAYLOR-DIFFERENTIABLE f a x n)
     (IMPLIES (IN t (CCINT a x))
       (IS-CONTINUOUS-AT RR-MS RR-MS ,GT t)))))))))
(warrant! 'taylor-G-cont 'reference
  "G(t)=f(x)-TAYLOR-POLY(f,t,n,x) is a sum of products of the continuous
   derivatives f^(k) and polynomials in t, hence continuous on [a,x].")
(category! 'taylor-G-cont 'analysis)

(add-to-pss 'taylor-G-diff
  `(FORALL f (FORALL a (FORALL x (FORALL n (FORALL t
     (IMPLIES (TAYLOR-DIFFERENTIABLE f a x n)
     (IMPLIES (AND (< a t) (< t x))
       (IS-DIFF-AT ,GT t ,(GVAL 't))))))))))
(warrant! 'taylor-G-diff 'reference
  "Telescoping: d/dt[f(x)-Sum_{k<=n} f^(k)(t)(x-t)^k/k!] = -(f^(n+1)(t)/n!)(x-t)^n.
   Differentiate term k by the product rule: the f^(k+1)(t)(x-t)^k/k! piece of
   term k cancels the -f^(k+1)(t)(x-t)^k/k! piece of term k+1, leaving only the
   last -(f^(n+1)(t)/n!)(x-t)^n.  Standard (calculus.pdf Taylor section).")
(category! 'taylor-G-diff 'analysis)

(add-to-pss 'taylor-H-cont
  `(FORALL x (FORALL n (FORALL t (IMPLIES (IN x RR) (IMPLIES (IN t RR)
       (IS-CONTINUOUS-AT RR-MS RR-MS ,HT t)))))))
(warrant! 'taylor-H-cont 'reference
  "H(t)=(x-t)^(n+1) is a polynomial in t, continuous everywhere.")
(category! 'taylor-H-cont 'analysis)

(add-to-pss 'taylor-H-diff
  `(FORALL x (FORALL n (FORALL t (IMPLIES (IN x RR) (IMPLIES (IN t RR)
       (IS-DIFF-AT ,HT t ,(HVAL 't))))))))
(warrant! 'taylor-H-diff 'reference
  "d/dt[(x-t)^(n+1)] = -(n+1)(x-t)^n (chain rule on the polynomial).")
(category! 'taylor-H-diff 'analysis)

;;; gMVT-shaped hypotheses, warranted directly (G,H continuous on [a,x] and
;;; differentiable on (a,x)) -- assembled from the per-function facts above.
(add-to-pss 'taylor-gmvt-cont
  `(FORALL f (FORALL a (FORALL x (FORALL n
     (IMPLIES (TAYLOR-DIFFERENTIABLE f a x n) (IMPLIES (IN x RR) ,GHCONT)))))))
(warrant! 'taylor-gmvt-cont 'reference
  "G and H are continuous on [a,x]: H is a polynomial, G a finite sum of products
   of the continuous derivatives f^(k) with polynomials (taylor-G-cont/H-cont).")
(category! 'taylor-gmvt-cont 'analysis)

(add-to-pss 'taylor-gmvt-diff
  `(FORALL f (FORALL a (FORALL x (FORALL n
     (IMPLIES (TAYLOR-DIFFERENTIABLE f a x n) ,GHDIFF))))))
(warrant! 'taylor-gmvt-diff 'reference
  "G and H are differentiable on (a,x) (taylor-G-diff/H-diff give the explicit
   derivatives), so each has SOME derivative there.")
(category! 'taylor-gmvt-diff 'analysis)

;;; function-typing of the auxiliaries
(add-to-pss 'taylor-G-in-fun
  `(FORALL f (IMPLIES (IN f (FUN RR RR)) (FORALL x (IMPLIES (IN x RR)
       (IN ,GT (FUN RR RR)))))))
(warrant! 'taylor-G-in-fun 'reference
  "G(t)=f(x)-TAYLOR-POLY(f,t,n,x) maps RR to RR (finite sum of products of
   reals).")
(category! 'taylor-G-in-fun 'analysis)

(add-to-pss 'taylor-H-in-fun
  `(FORALL x (IMPLIES (IN x RR) (IN ,HT (FUN RR RR)))))
(warrant! 'taylor-H-in-fun 'reference
  "H(t)=(x-t)^(n+1) maps RR to RR.")
(category! 'taylor-H-in-fun 'analysis)

;;; endpoint computations
(add-to-pss 'taylor-poly-at-center
  '(FORALL f (FORALL x (FORALL n (IMPLIES (IN n NN) (= (TAYLOR-POLY f x n x) (f x)))))))
(warrant! 'taylor-poly-at-center 'reference
  "TAYLOR-POLY(f,x,n,x): every term k>=1 carries (x-x)^k = 0, and term 0 is
   f^(0)(x)(x-x)^0/0! = f(x).  So the Taylor polynomial at its own centre is f(x).")
(category! 'taylor-poly-at-center 'analysis)

(add-to-pss 'power-zero-base
  '(FORALL n (IMPLIES (IN n NN) (= (power 0 (succ n)) 0))))
(warrant! 'power-zero-base 'well-known
  "0^(n+1) = 0 (power-succ: 0^(n+1) = 0 * 0^n = 0).")
(category! 'power-zero-base 'analysis)

;;; endpoint VALUES of the auxiliaries (beta + the two facts above)
(add-to-pss 'taylor-G-at-x
  `(FORALL f (FORALL x (FORALL n (IMPLIES (IN n NN) (= (,GT x) 0))))))
(warrant! 'taylor-G-at-x 'reference
  "G(x) = f(x) - TAYLOR-POLY(f,x,n,x) = f(x) - f(x) = 0 (taylor-poly-at-center).")
(category! 'taylor-G-at-x 'analysis)

(add-to-pss 'taylor-G-at-a
  `(FORALL f (FORALL a (FORALL x (FORALL n
     (= (,GT a) (- (f x) (TAYLOR-POLY f a n x))))))))
(warrant! 'taylor-G-at-a 'reference "G(a) = f(x) - TAYLOR-POLY(f,a,n,x) (beta).")
(category! 'taylor-G-at-a 'analysis)

(add-to-pss 'taylor-H-at-x
  `(FORALL x (FORALL n (IMPLIES (IN n NN) (= (,HT x) 0)))))
(warrant! 'taylor-H-at-x 'reference "H(x) = (x-x)^(n+1) = 0^(n+1) = 0.")
(category! 'taylor-H-at-x 'analysis)

(add-to-pss 'taylor-H-at-a
  `(FORALL a (FORALL x (FORALL n (= (,HT a) (power (- x a) (succ n)))))))
(warrant! 'taylor-H-at-a 'reference "H(a) = (x-a)^(n+1) (beta).")
(category! 'taylor-H-at-a 'analysis)

;;; --- elementary RR algebra micro-lemmas for the clearing step ---
(add-to-pss 'rr-power-pos
  '(FORALL d (IMPLIES (IN d RR) (FORALL n (IMPLIES (IN n NN)
     (IMPLIES (< 0 d) (< 0 (power d n))))))))
(warrant! 'rr-power-pos 'well-known
  "0<d gives 0<d^n for every n (induction: d^0=1>0; d^(n+1)=d*d^n, product of
   positives).")
(category! 'rr-power-pos 'analysis)

(add-to-pss 'rr-cancel-mul-left
  '(FORALL c (IMPLIES (IN c RR) (FORALL u (IMPLIES (IN u RR) (FORALL v (IMPLIES (IN v RR)
     (IMPLIES (NOT (= c 0)) (IMPLIES (= (* c u) (* c v)) (= u v))))))))))
(warrant! 'rr-cancel-mul-left 'well-known
  "c*u=c*v with c/=0 gives u=v (multiply by 1/c).")
(category! 'rr-cancel-mul-left 'analysis)

(add-to-pss 'rr-recip-factorial
  '(FORALL n (IMPLIES (IN n NN) (= (* (FACTORIAL n) (recip (FACTORIAL n))) 1))))
(warrant! 'rr-recip-factorial 'well-known
  "n! /= 0 (it is a positive integer), so n! * (1/n!) = 1.")
(category! 'rr-recip-factorial 'analysis)

(add-to-pss 'rr-pos-ne-zero
  '(FORALL c (IMPLIES (IN c RR) (IMPLIES (< 0 c) (NOT (= c 0))))))
(warrant! 'rr-pos-ne-zero 'well-known "0<c gives c/=0.")
(category! 'rr-pos-ne-zero 'analysis)

(add-to-pss 'power-in-rr
  '(FORALL b (IMPLIES (IN b RR) (FORALL n (IMPLIES (IN n NN) (IN (power b n) RR))))))
(warrant! 'power-in-rr 'well-known "b^n in RR for b real, n in NN (RR closed under *).")
(category! 'power-in-rr 'analysis)

(add-to-pss 'taylor-poly-in-rr
  '(FORALL f (IMPLIES (IN f (FUN RR RR)) (FORALL a (IMPLIES (IN a RR) (FORALL n (IMPLIES (IN n NN)
     (FORALL x (IMPLIES (IN x RR) (IN (TAYLOR-POLY f a n x) RR))))))))))
(warrant! 'taylor-poly-in-rr 'reference
  "TAYLOR-POLY is a finite sum of products of reals, hence real.")
(category! 'taylor-poly-in-rr 'analysis)

(add-to-pss 'taylor-deriv-real
  '(FORALL f (FORALL a (FORALL x (FORALL n (FORALL t
     (IMPLIES (TAYLOR-DIFFERENTIABLE f a x n)
     (IMPLIES (< a t) (IMPLIES (< t x)
       (IN ((NTH-DERIV f (succ n)) t) RR))))))))))
(warrant! 'taylor-deriv-real 'reference
  "f^(n+1)(t) is the derivative value of the differentiable f^(n) at t, hence
   real (IS-DIFF-AT carries its value in RR).")
(category! 'taylor-deriv-real 'analysis)

;;; the elementary clearing identity (pure RR algebra: cancel pw/=0, clear n!):
;;;   (-(fn1/n!)pw)(hx-ha) = (-(n+1)pw)(gx-ga),  gx=hx=0, ha=d, ga=r
;;;   =>  (n+1)! r = fn1 d.
(add-to-pss 'taylor-clear
  '(FORALL fn1 (IMPLIES (IN fn1 RR)
   (FORALL pw (IMPLIES (IN pw RR)
   (FORALL d (IMPLIES (IN d RR)
   (FORALL r (IMPLIES (IN r RR)
   (FORALL gx (FORALL ga (FORALL hx (FORALL ha
   (FORALL n (IMPLIES (IN n NN)
     (IMPLIES (< 0 pw)
     (IMPLIES (= gx 0)
     (IMPLIES (= hx 0)
     (IMPLIES (= ha d)
     (IMPLIES (= ga r)
     (IMPLIES (= (* (- 0 (* (* (recip (FACTORIAL n)) fn1) pw)) (- hx ha))
                 (* (- 0 (* (succ n) pw)) (- gx ga)))
       (= (* (FACTORIAL (succ n)) r) (* fn1 d)))))))))))))))))))))))
(warrant! 'taylor-clear 'well-known
  "Substitute gx=hx=0, ha=d, ga=r: (-(fn1/n!)pw)(-d) = (-(n+1)pw)(-r), i.e.
   (fn1/n!)pw*d = (n+1)pw*r; cancel pw/=0 and multiply by n! (using
   (n+1)*n! = (n+1)!) to get (n+1)! r = fn1 d.  Pure real arithmetic.")
(category! 'taylor-clear 'analysis)

;;; ====================================================================
;;; taylor-lagrange (cleared form)
;;; ====================================================================
(sp `(FORALL f (FORALL a (FORALL x (FORALL n
     (IMPLIES (AND (IN f (FUN RR RR)) (AND (IN a RR) (AND (IN x RR) (AND (IN n NN) (< a x)))))
     (IMPLIES (TAYLOR-DIFFERENTIABLE f a x n)
       (FORSOME theta (AND (< a theta) (AND (< theta x)
         (= (* (FACTORIAL (succ n)) (- (f x) (TAYLOR-POLY f a n x)))
            (* ((NTH-DERIV f (succ n)) theta) (power (- x a) (succ n))))))))))))))
(quietly (lambda () (di)(di)(di)(di)))     ; f,a,x,n
(dc-split)                                  ; typing AND
(quietly (lambda () (di)))                 ; TAYLOR-DIFFERENTIABLE hyp
(define GOAL (dc-gf))

;;; ---- gMVT typing: GT, HT in FUN RR RR (forward facts, land in ctx) ----
(quietly (lambda () (fact 'taylor-G-in-fun 'f 'x)))
(quietly (lambda () (fact 'taylor-H-in-fun 'x)))

;;; ---- gMVT continuity + differentiability hyps (warranted, land in ctx) ----
(quietly (lambda () (fact 'taylor-gmvt-cont 'f 'a 'x 'n)))   ; -> GHCONT
(quietly (lambda () (fact 'taylor-gmvt-diff 'f 'a 'x 'n)))   ; -> GHDIFF

;;; ---- apply generalized-mvt to (GT, HT) on [a,x] ----
(define GMTYP (list 'AND (list 'IN GT '(FUN RR RR))
                (list 'AND (list 'IN HT '(FUN RR RR)) '(AND (IN a RR) (AND (IN x RR) (< a x))))))
(cut GMTYP) (dc-grind!) (dc-focus! GOAL)
(quietly (lambda () (fact 'generalized-mvt GT HT 'a 'x)))
(let loop ((k 0))                            ; detach GMTYP, GHCONT, GHDIFF (alpha-equiv)
  (let ((ri (dc-find (lambda (z) (and ((dc-head? 'IMPLIES) z) (dc-ment? 'VNB-LAMBDA z))))))
    (when (and ri (< k 4)) (detach! ri) (loop (+ k 1)))))
;; existential elimination: theta, then L (for GT) and M (for HT)
(ai (dc-find (lambda (z) (and ((dc-head? 'FORSOME) z) (dc-ment? 'VNB-LAMBDA z) (dc-ment? 'is-diff-at z)))))
(dc-split)
(define THETA (caddr (dc-find (lambda (z) (and ((dc-head? '<) z) (eq? (cadr z) 'a) (symbol? (caddr z))
                 (dc-find (lambda (y) (and ((dc-head? '<) y) (equal? (cadr y) (caddr z)) (eq? (caddr y) 'x)))))))))
(ai (dc-find (lambda (z) (and ((dc-head? 'FORSOME) z) (dc-ment? 'taylor-poly z)))))   ; FORSOME L (for GT)
(ai (dc-find (lambda (z) (and ((dc-head? 'FORSOME) z) (dc-ment? 'is-diff-at z)))))    ; FORSOME M (for HT)
(dc-split)
(define LW (cadddr (dc-find (lambda (z) (and ((dc-head? 'IS-DIFF-AT) z) (equal? (caddr z) THETA) (dc-ment? 'taylor-poly z))))))
(define MW (cadddr (dc-find (lambda (z) (and ((dc-head? 'IS-DIFF-AT) z) (equal? (caddr z) THETA) (dc-ment? 'power z) (not (dc-ment? 'taylor-poly z)))))))

;;; ---- endgame: pin L,M; endpoint values; elementary clearing ----
(quietly (lambda () (fact 'rr-strict-between-real 'a 'x THETA)))   ; IN theta RR
(dc-have! (list 'IN (list '- 'x THETA) 'RR) GOAL)                 ; IN (x-theta) RR
(dc-have! '(IN (- x a) RR) GOAL)                                  ; IN (x-a) RR
(cut (list 'AND (list '< 'a THETA) (list '< THETA 'x))) (dc-grind!) (dc-focus! GOAL)
(quietly (lambda () (fact 'taylor-G-diff 'f 'a 'x 'n THETA)))   ; IS-DIFF-AT GT theta (GVAL theta)
(quietly (lambda () (fact 'taylor-H-diff 'x 'n THETA)))         ; IS-DIFF-AT HT theta (HVAL theta)
(let ((dd (list 'AND (list 'IS-DIFF-AT GT THETA (GVAL THETA)) (list 'IS-DIFF-AT GT THETA LW))))
  (cut dd) (di) (quietly (lambda () (ass-all))) (dc-focus! GOAL)
  (quietly (lambda () (fact 'derivative-unique GT THETA (GVAL THETA) LW))))   ; (= (GVAL theta) LW)
(let ((dd (list 'AND (list 'IS-DIFF-AT HT THETA (HVAL THETA)) (list 'IS-DIFF-AT HT THETA MW))))
  (cut dd) (di) (quietly (lambda () (ass-all))) (dc-focus! GOAL)
  (quietly (lambda () (fact 'derivative-unique HT THETA (HVAL THETA) MW))))   ; (= (HVAL theta) MW)

;;; TCIN: the gMVT equation with L,M pinned to their explicit values
(define TCIN (list '= (list '* (GVAL THETA) (list '- (list HT 'x) (list HT 'a)))
                      (list '* (HVAL THETA) (list '- (list GT 'x) (list GT 'a)))))
(cut TCIN)
(subst (list '= (GVAL THETA) LW))
(subst (list '= (HVAL THETA) MW))
(quietly (lambda () (ass-all)))            ; closes from the gMVT equation
(dc-focus! GOAL)

;;; endpoint values (warranted)
(define RREM '(- (f x) (TAYLOR-POLY f a n x)))
(define DPOW '(power (- x a) (succ n)))
(define FN1 (list (list 'NTH-DERIV 'f '(succ n)) THETA))
(define PW (list 'power (list '- 'x THETA) 'n))
(quietly (lambda () (fact 'taylor-G-at-x 'f 'x 'n)))   ; (= (GT x) 0)
(quietly (lambda () (fact 'taylor-G-at-a 'f 'a 'x 'n))) ; (= (GT a) RREM)
(quietly (lambda () (fact 'taylor-H-at-x 'x 'n)))       ; (= (HT x) 0)
(quietly (lambda () (fact 'taylor-H-at-a 'a 'x 'n)))    ; (= (HT a) DPOW)

;;; pw /= 0 and typings for taylor-clear
(quietly (lambda () (fact 'rr-lt-diff-pos THETA 'x)))           ; 0 < x-theta
(quietly (lambda () (fact 'rr-power-pos (list '- 'x THETA) 'n)))  ; 0 < (x-theta)^n
(quietly (lambda () (fact 'rr-pos-ne-zero PW)))                 ; (x-theta)^n /= 0
(quietly (lambda () (fact 'taylor-deriv-real 'f 'a 'x 'n THETA)))  ; IN fn1 RR
(quietly (lambda () (fact 'power-in-rr (list '- 'x THETA) 'n)))    ; IN pw RR
(quietly (lambda () (fact 'nn-succ-closed 'n)))                 ; (succ n) in NN
(quietly (lambda () (fact 'power-in-rr '(- x a) '(succ n))))    ; IN DPOW RR
(quietly (lambda () (fact 'taylor-poly-in-rr 'f 'a 'n 'x)))     ; IN taylor-poly RR
(dc-have! (list 'IN RREM 'RR) GOAL)                            ; IN R RR

;;; clear: taylor-clear -> (n+1)! R = fn1 D
(quietly (lambda () (fact 'taylor-clear FN1 PW DPOW RREM (list GT 'x) (list GT 'a) (list HT 'x) (list HT 'a) 'n)))

;;; finish: ew theta, close the three conjuncts
(ew THETA)
(quietly (lambda () (dc-grind!) (ass-all)))
(qed 'taylor-lagrange)

;;; Classic textbook name, for (find-theorem "...") lookup.
(alias! 'taylor-lagrange "Taylor's theorem" "Taylor's theorem with Lagrange remainder")
(category! 'taylor-lagrange 'analysis)

;;; -----------------------------------------------------------------------
;;; Notation -- the ENGLISH of these predicates, declared beside their
;;; definitions and read by wff->english / the proof reader (operators.scm).
;;; A def-predicate's reading cannot be derived the way a structure's noun can
;;; (noun vs adjective: IS-COMPLETE wants "s is complete", not "s is a complete"),
;;; so it is written here, once, next to what it means.
(notation! 'TAYLOR-DIFFERENTIABLE 'kind 'predicate 'arity 4
           'english "$1 is $4 times differentiable from $2 to $3")
