;;; norm-attained-general.scm -- the norm-attaining functional WITHOUT a finite-dimension hypothesis, and the
;;; two theorems that cited the finite-dimensional one, restated without it as NEW theorems beside the old.
;;; Agent DUAL-FIX, 2026-10-26.  DESTINATION: theorem-library/norm-attained-general.scm.  Library: analysis.
;;; Load window: after theorem-library/tvs-bidual (norming-functional-exists) and vector-taylor-proof (3037).
;;;
;;;   norm-attained-by-functional-nvs     = norm-attained-by-functional minus IS-FINITE-DIMENSIONAL
;;;   norm-as-sup-nvs                     = norm-as-sup minus IS-FINITE-DIMENSIONAL
;;;   vector-taylor-remainder-bound-nvs   = vector-taylor-remainder-bound minus IS-FINITE-DIMENSIONAL
;;; The old three stand unchanged.  The two citer proofs are the old scripts (norm-as-sup-proof.scm,
;;; vector-taylor-proof.scm), copied with the hypothesis and its antecedent conjunct removed and the
;;; citation of norm-attained-by-functional replaced; file-level names carry the prefixes NAG1- / NAG2-.

(sp (make-wff '(FORALL m (FORALL x
     (IMPLIES (AND (IS-NORMED-VECTOR-SPACE m) (IN x (VEC m)))
       (FORSOME g (AND (IS-BOUNDED-LINEAR-FUNCTIONAL m g)
                  (AND (<= (DUAL-NORM m g) 1)
                       (= (g x) ((VNRM m) x))))))))))
(dk-peel!)
(dk-split-all!)
(dk-cite! 'norming-functional-exists 'm 'x)
(ass)
(qed 'norm-attained-by-functional-nvs)
(topic! 'norm-attained-by-functional-nvs 'analysis)

(define NAG1-UB-CLAUSE
  '(FORALL f (IMPLIES (IS-BOUNDED-LINEAR-FUNCTIONAL m f) (IMPLIES (<= (DUAL-NORM m f) 1)
     (<= (abs (f x)) ((VNRM m) x))))))
(define NAG1-LEAST-CLAUSE
  '(FORALL d (IMPLIES (AND (IN d RR)
                       (FORALL f (IMPLIES (IS-BOUNDED-LINEAR-FUNCTIONAL m f) (IMPLIES (<= (DUAL-NORM m f) 1)
                                   (<= (abs (f x)) d)))))
     (<= ((VNRM m) x) d))))

(sp (list 'FORALL 'm (list 'FORALL 'x
     (list 'IMPLIES (conjuncts->and '((IS-NORMED-VECTOR-SPACE m)
                                      (IN x (VEC m))))
       (list 'AND NAG1-UB-CLAUSE NAG1-LEAST-CLAUSE)))))
(quietly (lambda () (di)(di)(di)))
(dc-split)                    ; splits antecedent (NVS,INx) AND the goal (UB | LEAST)
(define NAG1-VNRMx '((VNRM m) x))

;; ---- upper-bound clause (focused leaf: ||x|| bounds every |f(x)|) ----
(quietly (lambda () (di)(di)(di)))           ; f ; BLF ; (<= DN 1)
(define NAG1-UBf (caddr (dc-find (lambda (z) (and ((dc-head? 'IS-BOUNDED-LINEAR-FUNCTIONAL) z))))))
(define NAG1-UBBODY (dc-gf))
(define NAG1-NBANT (conjuncts->and (list '(IS-NORMED-VECTOR-SPACE m)
                                    (list 'IS-BOUNDED-LINEAR-FUNCTIONAL 'm NAG1-UBf)
                                    '(IN x (VEC m))
                                    (list '<= (list 'DUAL-NORM 'm NAG1-UBf) 1))))
(cut NAG1-NBANT) (dc-grind!) (dc-focus! NAG1-UBBODY)
(quietly (lambda () (fact 'norm-bounded-by-functionals 'm NAG1-UBf 'x)))
(quietly (lambda () (ass-all)))

;; ---- least clause (other leaf: ||x|| <= any upper bound d) ----
(hbf-focus-open! (lambda (z) (and (pair? z) (eq? (car z) 'FORALL) (dc-ment? 'rr z) (dc-ment? 'is-bounded-linear-functional z))))
(quietly (lambda () (di)(di)))                ; d ; (AND (IN d RR) NAG1-UBd)
(dc-split)
(define NAG1-LEASTBODY (dc-gf))                    ; (<= ((VNRM m) x) d)
(define NAG1-UBd (dc-find (lambda (z) (and ((dc-head? 'FORALL) z) (dc-ment? 'is-bounded-linear-functional z) (not (dc-ment? 'vnrm z))))))
;; obtain the norm-attaining functional g
(define NAG1-NAANT (conjuncts->and '((IS-NORMED-VECTOR-SPACE m)
                                (IN x (VEC m)))))
(cut NAG1-NAANT) (dc-grind!) (dc-focus! NAG1-LEASTBODY)
(quietly (lambda () (fact 'norm-attained-by-functional-nvs 'm 'x)))
(ai (dc-find (lambda (z) (and ((dc-head? 'FORSOME) z) (dc-ment? 'is-bounded-linear-functional z) (dc-ment? 'vnrm z)))))
(dc-split)                                    ; BLF-g, (<= DN 1), (= (g x) ||x||)   [quirk from here]
(define NAG1-GG (caddr (dc-find (lambda (z) (and ((dc-head? 'IS-BOUNDED-LINEAR-FUNCTIONAL) z))))))
(define NAG1-GXeq (dc-find (lambda (z) (and ((dc-head? '=) z) (dc-ment? 'vnrm z) (dc-ment? NAG1-GG z)))))  ; (= (g x) ||x||)
;; |g(x)| <= d : instantiate the (curried) upper bound at g and detach twice
(quietly (lambda () (inst+ NAG1-UBd NAG1-GG)))          ; (IMPLIES BLF-g (IMPLIES (<= DN 1) (<= (abs (g x)) d)))
(dc-detach-impl! (list 'IS-BOUNDED-LINEAR-FUNCTIONAL 'm NAG1-GG))   ; (IMPLIES (<= DN 1) (<= (abs (g x)) d))
(dc-detach-impl! (list '<= (list 'DUAL-NORM 'm NAG1-GG) 1))         ; (<= (abs (g x)) d)
;; ||x|| typing and ||x|| = g(x)
(quietly (lambda () (fact 'vnrm-real 'm 'x)))
(quietly (lambda () (fact 'vnrm-nonneg 'm 'x)))
(quietly (lambda () (fact 'eq-sym (list NAG1-GG 'x) NAG1-VNRMx)))           ; (= ||x|| (g x))  [NAG1-GXeq present]
;; (<= (abs ||x||) d) from |g(x)| <= d by rewriting ||x|| -> g(x)
(cut (list '<= (list 'abs NAG1-VNRMx) 'd))             ; goal (<= (abs ||x||) d)
(subst (list '= NAG1-VNRMx (list NAG1-GG 'x)))              ; ||x|| -> g(x): goal (<= (abs (g x)) d)
(quietly (lambda () (ass)))                        ; matches detached |g(x)| <= d
;; abs-nonneg-le on ||x|| (>= 0): ||x|| <= d
(quietly (lambda () (fact 'abs-nonneg-le NAG1-VNRMx 'd)))   ; (<= ||x|| d) = goal
(quietly (lambda () (ass)))
(qed 'norm-as-sup-nvs)
(topic! 'norm-as-sup-nvs 'analysis)

(define NAG2-REMV '((VADD m) (f x) ((VNEG m) (TAYLOR-POLY-V m f a x n))))
;;; ====================================================================
;;; THEOREM: vector-taylor-remainder-bound-nvs (the finite-dimension hypothesis dropped)
;;;   (n+1)! ||f(x) (-) TAYLOR-POLY-V(f,a,x,n)||  <=  ||f^(n+1)(theta)|| (x-a)^(n+1)
;;; for some theta in (a,x).  The reduction to scalar via a norm-attaining g.
;;; ====================================================================
(sp `(FORALL m (FORALL f (FORALL a (FORALL x (FORALL n
     (IMPLIES (AND (IS-NORMED-VECTOR-SPACE m)
               (AND (IN f (FUN RR (VEC m)))
               (AND (IN a RR) (AND (IN x RR) (AND (IN n NN) (< a x))))))
     (IMPLIES (TAYLOR-DIFFERENTIABLE-V m f a x n)
       (FORSOME theta (AND (IN theta RR) (AND (< a theta) (AND (< theta x)
         (<= (* (FACTORIAL (succ n)) ((VNRM m) ,NAG2-REMV))
             (* ((VNRM m) ((NTH-DERIV-V m f (succ n)) theta))
                (power (- x a) (succ n))))))))))))))))
(quietly (lambda () (di)(di)(di)(di)(di)(di)))   ; m,f,a,x,n ; ANT1
(dc-split)
(quietly (lambda () (di)))                        ; TAYLOR-DIFFERENTIABLE-V
(define NAG2-GOAL (dc-gf))

;; R is a vector
;; the guarded vtaylor-remainder-in-vec (2026-09-17) owes DFUN-V(m,f,n): taylor-v-derivs-in-fun supplies it
(quietly (lambda () (fact 'taylor-v-derivs-in-fun 'm 'f 'a 'x 'n)))
(quietly (lambda () (fact 'vtaylor-remainder-in-vec 'm 'f 'a 'x 'n)))

;; norm-attained: g bounded, ||g||<=1, g(R) = ||R||
(define NAG2-NAANT (conjuncts->and (list '(IS-NORMED-VECTOR-SPACE m)
                                    (list 'IN NAG2-REMV '(VEC m)))))
(cut NAG2-NAANT) (dc-grind!) (dc-focus! NAG2-GOAL)
(quietly (lambda () (fact 'norm-attained-by-functional-nvs 'm NAG2-REMV)))
(ai (dc-find (lambda (z) (and ((dc-head? 'FORSOME) z) (dc-ment? 'is-bounded-linear-functional z) (dc-ment? 'vnrm z)))))
(dc-split)
(define NAG2-G (caddr (dc-find (lambda (z) ((dc-head? 'IS-BOUNDED-LINEAR-FUNCTIONAL) z)))))
(define NAG2-GOF (list 'COMPOSE NAG2-G 'f))

;; g o f is a real function, and scalar-Taylor-differentiable
(quietly (lambda () (fact 'gof-in-fun 'm 'f NAG2-G)))
(quietly (lambda () (fact 'gof-taylor-diff-dfun 'm 'f NAG2-G 'a 'x 'n)))

;; scalar Taylor (Lagrange) on g o f : theta and the cleared equality
(define NAG2-TLANT (conjuncts->and (list (list 'IN NAG2-GOF '(FUN RR RR))
                                    '(IN a RR) '(IN x RR) '(IN n NN) '(< a x))))
(cut NAG2-TLANT) (dc-grind!) (dc-focus! NAG2-GOAL)
(quietly (lambda () (fact 'taylor-lagrange NAG2-GOF 'a 'x 'n)))
(ai (dc-find (lambda (z) (and ((dc-head? 'FORSOME) z) (dc-ment? 'taylor-poly z) (dc-ment? 'nth-deriv z)))))
(dc-split)
(define NAG2-THETA (caddr (dc-find (lambda (z) (and ((dc-head? '<) z) (eq? (cadr z) 'a) (symbol? (caddr z))
                 (dc-find (lambda (y) (and ((dc-head? '<) y) (equal? (cadr y) (caddr z)) (eq? (caddr y) 'x)))))))))
;; --- names for the endgame ---
(define NAG2-SF '(FACTORIAL (succ n)))
(define NAG2-PW '(power (- x a) (succ n)))
(define NAG2-SR (list '- (list NAG2-GOF 'x) (list 'TAYLOR-POLY NAG2-GOF 'a 'n 'x)))
(define NAG2-NTHGOF (list (list 'NTH-DERIV NAG2-GOF '(succ n)) NAG2-THETA))
(define NAG2-FN1 (list (list 'NTH-DERIV-V 'm 'f '(succ n)) NAG2-THETA))
(define NAG2-NR (list (list 'VNRM 'm) NAG2-REMV))
(define NAG2-NFN1 (list (list 'VNRM 'm) NAG2-FN1))
(define NAG2-GRr (list NAG2-G NAG2-REMV))
(define NAG2-GFN1 (list NAG2-G NAG2-FN1))

;; theta in RR ; (succ n) in NN
;; (IN theta RR) came out of the taylor-lagrange existential with the rest of its body.
(quietly (lambda () (fact 'nn-succ-closed 'n)))

;; commutation facts:  g(R) = scalar remainder ;  (g o f)^(n+1)(theta) = g(f^(n+1)(theta))
(quietly (lambda () (fact 'g-of-remainder-dfun 'm 'f NAG2-G 'a 'x 'n)))    ; (= NAG2-GRr NAG2-SR)
;; the guarded gof-nth-deriv-dfun also wants the IS-DIFF-AT-V of f^(n) at theta,
;; which is TD-V's second conjunct there (r8e-td-v-diff-at, spliced above).
(quietly (lambda () (fact 'r8e-td-v-diff-at 'm 'f 'a 'x 'n NAG2-THETA)))
(quietly (lambda () (fact 'gof-nth-deriv-dfun 'm 'f NAG2-G 'n NAG2-THETA)))     ; (= NAG2-NTHGOF NAG2-GFN1)

;; typings
(quietly (lambda () (fact 'taylor-v-deriv-in-vec 'm 'f 'a 'x 'n NAG2-THETA)))  ; IN NAG2-FN1 (VEC m) -- order n+1 at theta in (a,x), from TD-V (2026-09-14)
(quietly (lambda () (fact 'vnrm-real 'm NAG2-REMV)))                  ; IN NAG2-NR RR
(quietly (lambda () (fact 'vnrm-real 'm NAG2-FN1)))                   ; IN NAG2-NFN1 RR
(quietly (lambda () (fact 'blf-app-real 'm NAG2-G NAG2-FN1)))             ; IN NAG2-GFN1 RR

;; EQ1 :  (n+1)! ||R|| = g(fn1) * pw   -- rewrite the scalar Taylor equality
(quietly (lambda () (fact 'eq-sym NAG2-GRr NAG2-NR)))            ; (= NAG2-NR NAG2-GRr)  [from gReq (= NAG2-GRr NAG2-NR)]
(cut (list '= NAG2-NR NAG2-SR))                                  ; ||R|| = NAG2-SR
(subst (list '= NAG2-NR NAG2-GRr)) (quietly (lambda () (ass)))   ; -> (= NAG2-GRr NAG2-SR) = g-of-remainder
(dc-focus! NAG2-GOAL)
(quietly (lambda () (fact 'eq-sym NAG2-NTHGOF NAG2-GFN1)))       ; (= NAG2-GFN1 NAG2-NTHGOF)  [from gof-nth-deriv]
(cut (list '= (list '* NAG2-SF NAG2-NR) (list '* NAG2-GFN1 NAG2-PW)))      ; EQ1
(subst (list '= NAG2-NR NAG2-SR))                                ; NAG2-NR -> NAG2-SR
(subst (list '= NAG2-GFN1 NAG2-NTHGOF))                          ; g(fn1) -> (g o f)^(n+1)(theta)
(quietly (lambda () (ass)))                            ; = the taylor-lagrange equality
(dc-focus! NAG2-GOAL)

;; LE1 :  g(fn1) <= ||fn1||   (norm-bounded-by-functionals + g <= |g|)
(define NAG2-NBANT (conjuncts->and (list '(IS-NORMED-VECTOR-SPACE m)
                                    (list 'IS-BOUNDED-LINEAR-FUNCTIONAL 'm NAG2-G)
                                    (list 'IN NAG2-FN1 '(VEC m))
                                    (list '<= (list 'DUAL-NORM 'm NAG2-G) 1))))
(cut NAG2-NBANT) (dc-grind!) (dc-focus! NAG2-GOAL)
(quietly (lambda () (fact 'norm-bounded-by-functionals 'm NAG2-G NAG2-FN1)))  ; (<= (abs NAG2-GFN1) NAG2-NFN1)
(quietly (lambda () (fact 'bdd-linfun-abs-real 'm NAG2-G NAG2-FN1)))          ; IN (abs NAG2-GFN1) RR
(quietly (lambda () (fact 'rr-le-abs NAG2-GFN1)))                   ; (<= NAG2-GFN1 (abs NAG2-GFN1))
(quietly (lambda () (fact 'rr-le-trans-c NAG2-GFN1 (list 'abs NAG2-GFN1) NAG2-NFN1)))  ; (<= NAG2-GFN1 NAG2-NFN1)

;; pw in RR and 0 <= pw
(quietly (lambda () (fact 'rr-zero-in)))                           ; IN 0 RR
(dc-have! '(IN (- x a) RR) NAG2-GOAL)                                   ; IN (x-a) RR
(quietly (lambda () (fact 'power-real-closed '(- x a) '(succ n))))       ; IN pw RR
(quietly (lambda () (fact 'rr-lt-diff-pos 'a 'x)))                  ; (< 0 (- x a))
(quietly (lambda () (fact 'rr-power-pos '(- x a) '(succ n))))       ; (< 0 pw)
(quietly (lambda () (fact 'rr-lt-implies-le 0 NAG2-PW)))                 ; (<= 0 pw)

;; clear :  (n+1)! ||R|| <= ||fn1|| * pw.  Rewrite (n+1)!||R|| = g(fn1)*pw (EQ1),
;; then g(fn1)*pw <= ||fn1||*pw by right-monotonicity (LE1, 0<=pw).
(cut (list '<= (list '* NAG2-SF NAG2-NR) (list '* NAG2-NFN1 NAG2-PW)))
(subst (list '= (list '* NAG2-SF NAG2-NR) (list '* NAG2-GFN1 NAG2-PW)))     ; (n+1)!||R|| -> g(fn1)*pw
(quietly (lambda () (fact 'rr-mul-le-right NAG2-GFN1 NAG2-NFN1 NAG2-PW)))   ; g(fn1)*pw <= ||fn1||*pw
(quietly (lambda () (ass)))
(dc-focus! NAG2-GOAL)

;; witness theta, close the three conjuncts
(ew NAG2-THETA)
(quietly (lambda () (dc-grind!) (ass-all)))
(qed 'vector-taylor-remainder-bound-nvs)
(topic! 'vector-taylor-remainder-bound-nvs 'analysis)
