;;; vector-taylor-proof.scm -- vector-valued Taylor with a norm remainder bound,
;;; REDUCED TO THE SCALAR CASE via a norm-attaining functional (Hahn-Banach payoff).
;;;
;;; For a curve f : RR -> VEC(m) into a finite-dimensional real NVS m, the Taylor
;;; remainder R = f(x) (-) TAYLOR-POLY-V(f,a,x,n) is a VECTOR.  There is no single
;;; mean-value theta for a vector (the vector MVT fails), so the result is an
;;; INEQUALITY, not an equality:
;;;   there is theta in (a,x) with
;;;     (n+1)! * ||R||  <=  ||f^(n+1)(theta)|| * (x-a)^(n+1).
;;;
;;; REDUCTION: pick (norm-attained-by-functional) a bounded g, ||g||<=1, g(R)=||R||.
;;; Then g o f is a scalar curve, g commutes with the Caratheodory derivative and
;;; the Taylor sum, so g(R) is the scalar Taylor remainder of g o f; scalar
;;; taylor-lagrange supplies theta and the equality
;;;   (n+1)! g(R) = (g o f)^(n+1)(theta) (x-a)^(n+1) = g(f^(n+1)(theta)) (x-a)^(n+1),
;;; and norm-bounded-by-functionals gives g(f^(n+1)(theta)) <= ||f^(n+1)(theta)||.
;;; Multiplying by (x-a)^(n+1) >= 0 clears to the bound.  Loads after
;;; norm-as-sup-proof (norm-attained/bounded) and taylor-proof (scalar Taylor).
;;; ====================================================================

;;; ====================================================================
;;; vocabulary
;;; ====================================================================

;;; The metric induced by the norm: d(x,y) = ||x (-) y|| on VEC(m).
;;; (Mirrors NF-METRIC-SPACE for a normed field.)
(def-functoid 'NVS-METRIC-SPACE '(m)
  '(LIST (VEC m)
         (VNB-LAMBDA (LIST x y) (CARTESIAN (VEC m) (VEC m)) ((VNRM m) ((VADD m) x ((VNEG m) y))))))

;;; Vector Caratheodory derivative: f'(a) = L, witnessed by phi : RR -> VEC(m)
;;; continuous at a (in the norm metric) with phi(a)=L and
;;;    f(x) (-) f(a) = (x - a) . phi(x).
(def-predicate 'IS-DIFF-AT-V '(m f a L)
  '(AND (IS-NORMED-VECTOR-SPACE m)
   (AND (IN f (FUN RR (VEC m)))
   (AND (IN a RR)
   (AND (IN L (VEC m))
        (FORSOME phi
          (AND (IN phi (FUN RR (VEC m)))
          (AND (IS-CONTINUOUS-AT RR-MS (NVS-METRIC-SPACE m) phi a)
          (AND (= (phi a) L)
               (FORALL x_ (IMPLIES (IN x_ RR)
                 (= ((VADD m) (f x_) ((VNEG m) (f a)))
                    ((ACT m) (- x_ a) (phi x_))))))))))))))

;;; DERIV-V(m,f,a) = the unique vector derivative value.
(def-functoid 'DERIV-V '(m f a)
  '(IOTA L (IS-DIFF-AT-V m f a L)))

;;; f^(n) as a function RR -> VEC(m):  f^(0)=f, f^(succ n)= x |-> DERIV-V(m,f^(n),x).
(def-by-nn-recursion 'NTH-DERIV-V '(m f)
  'f
  '(n val)
  '(VNB-LAMBDA x RR (DERIV-V m val x)))

;;; Vector Taylor polynomial  Sum_{k=0}^{n} ((x-a)^k / k!) . f^(k)(a), by
;;; recursion on n (vector addition VADD, scalar action ACT -- no AG-tuple needed).
(def-by-nn-recursion 'TAYLOR-POLY-V '(m f a x)
  '((ACT m) (* (power (- x a) 0) (recip (FACTORIAL 0))) ((NTH-DERIV-V m f 0) a))
  '(n val)
  '((VADD m) val
     ((ACT m) (* (power (- x a) (succ n)) (recip (FACTORIAL (succ n))))
              ((NTH-DERIV-V m f (succ n)) a))))

;;; TAYLOR-DIFFERENTIABLE-V: f^(k) (k<=n) norm-continuous on [a,x] and vector-
;;; differentiable on (a,x) with derivative f^(k+1).  (Mirrors the scalar predicate.)
(def-predicate 'TAYLOR-DIFFERENTIABLE-V '(m f a x n)
  '(AND
     (FORALL k (IMPLIES (AND (IN k NN) (<= k n))
        (FORALL t (IMPLIES (IN t (CCINT a x))
           (IS-CONTINUOUS-AT RR-MS (NVS-METRIC-SPACE m) (NTH-DERIV-V m f k) t)))))
     (FORALL k (IMPLIES (AND (IN k NN) (<= k n))
        (FORALL t (IMPLIES (AND (< a t) (< t x))
           (IS-DIFF-AT-V m (NTH-DERIV-V m f k) t ((NTH-DERIV-V m f (succ k)) t))))))))

;;; the remainder vector R = f(x) (-) TAYLOR-POLY-V(f,a,x,n)
(define REMV '((VADD m) (f x) ((VNEG m) (TAYLOR-POLY-V m f a x n))))

;;; ====================================================================
;;; warranted cores
;;; ====================================================================

;;; the norm metric is a metric space.
(add-to-pss 'nvs-metric-is-ms
  '(FORALL m (IMPLIES (IS-NORMED-VECTOR-SPACE m) (IS-METRIC-SPACE (NVS-METRIC-SPACE m)))))
(warrant! 'nvs-metric-is-ms 'reference
  "d(x,y)=||x-y|| is a metric: nonneg + definite from the norm's definiteness,
   symmetry from ||-(x-y)||=||x-y||, triangle from the norm triangle inequality.")
(category! 'nvs-metric-is-ms 'analysis)

;;; the vector Taylor polynomial is a vector.
(add-to-pss 'vtaylor-poly-in-vec
  '(FORALL m (FORALL f (FORALL a (FORALL x (FORALL n
     (IMPLIES (IS-NORMED-VECTOR-SPACE m)
     (IMPLIES (IN f (FUN RR (VEC m)))
     (IMPLIES (IN a RR) (IMPLIES (IN x RR) (IMPLIES (IN n NN)
       (IN (TAYLOR-POLY-V m f a x n) (VEC m)))))))))))))
(warrant! 'vtaylor-poly-in-vec 'reference
  "TAYLOR-POLY-V is a finite VADD-sum of scalar actions ACT(.,f^(k)(a)) of vectors,
   closed in VEC(m) (VADD, ACT land in VEC(m); f^(k)(a) in VEC(m)).")
(category! 'vtaylor-poly-in-vec 'analysis)

;;; f^(k)(t) is a vector.
(add-to-pss 'nth-deriv-v-in-vec
  '(FORALL m (FORALL f (FORALL k (FORALL t
     (IMPLIES (IS-NORMED-VECTOR-SPACE m)
     (IMPLIES (IN f (FUN RR (VEC m)))
     (IMPLIES (IN k NN) (IMPLIES (IN t RR)
       (IN ((NTH-DERIV-V m f k) t) (VEC m)))))))))))
(warrant! 'nth-deriv-v-in-vec 'reference
  "Each vector derivative f^(k) maps RR into VEC(m) (IS-DIFF-AT-V pins the value
   in VEC(m)); so f^(k)(t) is a vector.")
(category! 'nth-deriv-v-in-vec 'analysis)

;;; the remainder is a vector.
(add-to-pss 'vtaylor-remainder-in-vec
  `(FORALL m (FORALL f (FORALL a (FORALL x (FORALL n
     (IMPLIES (IS-NORMED-VECTOR-SPACE m)
     (IMPLIES (IN f (FUN RR (VEC m)))
     (IMPLIES (IN a RR) (IMPLIES (IN x RR) (IMPLIES (IN n NN)
       (IN ,REMV (VEC m)))))))))))))
(warrant! 'vtaylor-remainder-in-vec 'reference
  "R = f(x) (-) TAYLOR-POLY-V(...) is a difference of vectors (VADD of f(x) and the
   VNEG of the polynomial), hence in VEC(m).")
(category! 'vtaylor-remainder-in-vec 'analysis)

;;; g o f is a real function when g is a bounded linear functional on m.
(add-to-pss 'gof-in-fun
  '(FORALL m (FORALL f (FORALL g
     (IMPLIES (IS-BOUNDED-LINEAR-FUNCTIONAL m g)
     (IMPLIES (IN f (FUN RR (VEC m)))
       (IN (COMPOSE g f) (FUN RR RR))))))))
(warrant! 'gof-in-fun 'reference
  "g : VEC(m) -> RR (bounded linear functional) composed with f : RR -> VEC(m)
   is g o f : RR -> RR.")
(category! 'gof-in-fun 'analysis)

;;; KEY commutation 1: g o f inherits the scalar Taylor-differentiability.
(add-to-pss 'gof-taylor-diff
  '(FORALL m (FORALL f (FORALL g (FORALL a (FORALL x (FORALL n
     (IMPLIES (IS-BOUNDED-LINEAR-FUNCTIONAL m g)
     (IMPLIES (IN f (FUN RR (VEC m)))
     (IMPLIES (TAYLOR-DIFFERENTIABLE-V m f a x n)
       (TAYLOR-DIFFERENTIABLE (COMPOSE g f) a x n)))))))))))
(warrant! 'gof-taylor-diff 'reference
  "A bounded linear functional g is linear and continuous, so it commutes with the
   Caratheodory derivative: if f^(k) is norm-continuous / vector-differentiable
   with factor phi, then (g o f)^(k) = g o f^(k) is continuous / differentiable
   with factor g o phi.  Hence g o f is scalar-Taylor-differentiable to order n.")
(category! 'gof-taylor-diff 'analysis)

;;; KEY commutation 2: g of the remainder = the scalar remainder of g o f.
(add-to-pss 'g-of-remainder
  `(FORALL m (FORALL f (FORALL g (FORALL a (FORALL x (FORALL n
     (IMPLIES (IS-BOUNDED-LINEAR-FUNCTIONAL m g)
     (IMPLIES (IN f (FUN RR (VEC m)))
     (IMPLIES (IN a RR) (IMPLIES (IN x RR) (IMPLIES (IN n NN)
       (= (g ,REMV)
          (- ((COMPOSE g f) x) (TAYLOR-POLY (COMPOSE g f) a n x)))))))))))))))
(warrant! 'g-of-remainder 'reference
  "g linear: g(f(x) (-) p) = g(f(x)) - g(p) = (g o f)(x) - g(TAYLOR-POLY-V).  g
   commutes with the finite VADD/ACT sum and with f^(k)(a), so
   g(TAYLOR-POLY-V(f,a,x,n)) = Sum ((x-a)^k/k!) g(f^(k)(a))
   = Sum ((x-a)^k/k!) (g o f)^(k)(a) = TAYLOR-POLY(g o f, a, n, x).")
(category! 'g-of-remainder 'analysis)

;;; KEY commutation 3: the (n+1)-st derivative of g o f is g of f^(n+1).
(add-to-pss 'gof-nth-deriv
  '(FORALL m (FORALL f (FORALL g (FORALL n (FORALL t
     (IMPLIES (IS-BOUNDED-LINEAR-FUNCTIONAL m g)
     (IMPLIES (IN f (FUN RR (VEC m)))
     (IMPLIES (IN n NN) (IMPLIES (IN t RR)
       (= ((NTH-DERIV (COMPOSE g f) (succ n)) t)
          (g ((NTH-DERIV-V m f (succ n)) t)))))))))))))
(warrant! 'gof-nth-deriv 'reference
  "By induction on k using commutation 1's factor identity, (g o f)^(k) = g o f^(k)
   as functions; evaluating the (n+1)-st at t gives (g o f)^(n+1)(t) = g(f^(n+1)(t)).")
(category! 'gof-nth-deriv 'analysis)

;;; g(v) <= |g(v)| (a real inequality; g(v) is real).
(add-to-pss 'rr-le-abs-self
  '(FORALL c (IMPLIES (IN c RR) (<= c (abs c)))))
(warrant! 'rr-le-abs-self 'well-known "c <= |c| for real c.")
(category! 'rr-le-abs-self 'analysis)

;;; the elementary clearing step: from an equality and a monotone bound with a
;;; nonnegative multiplier, get the remainder-norm inequality.
;;;   (n+1)! rR = gv * pw,   gv <= nv,   0 <= pw   =>   (n+1)! rR <= nv * pw.
(add-to-pss 'vtaylor-clear
  '(FORALL rR (IMPLIES (IN rR RR)
   (FORALL gv (IMPLIES (IN gv RR)
   (FORALL nv (IMPLIES (IN nv RR)
   (FORALL pw (IMPLIES (IN pw RR)
   (FORALL n (IMPLIES (IN n NN)
     (IMPLIES (= (* (FACTORIAL (succ n)) rR) (* gv pw))
     (IMPLIES (<= gv nv)
     (IMPLIES (<= 0 pw)
       (<= (* (FACTORIAL (succ n)) rR) (* nv pw))))))))))))))))
(warrant! 'vtaylor-clear 'well-known
  "(n+1)! rR = gv*pw and gv<=nv with pw>=0 give gv*pw <= nv*pw, so
   (n+1)! rR <= nv*pw.  Pure real arithmetic (monotonicity of *pw for pw>=0).")
(category! 'vtaylor-clear 'analysis)

;;; g(v) is a real for a bounded linear functional g and a vector v.
(add-to-pss 'blf-app-real
  '(FORALL m (FORALL g (FORALL v
     (IMPLIES (IS-BOUNDED-LINEAR-FUNCTIONAL m g) (IMPLIES (IN v (VEC m))
        (IN (g v) RR)))))))
(warrant! 'blf-app-real 'reference
  "A bounded linear functional g maps VEC(m) into RR, so g(v) is a real.")
(category! 'blf-app-real 'analysis)

;;; right-monotonicity of multiplication by a nonnegative factor.
(add-to-pss 'rr-mul-le-right
  '(FORALL a (IMPLIES (IN a RR) (FORALL b (IMPLIES (IN b RR) (FORALL c (IMPLIES (IN c RR)
     (IMPLIES (<= a b) (IMPLIES (<= 0 c) (<= (* a c) (* b c)))))))))))
(warrant! 'rr-mul-le-right 'well-known "a<=b and 0<=c give a*c <= b*c.")
(category! 'rr-mul-le-right 'analysis)

;;; ====================================================================
;;; THEOREM: vector-taylor-remainder-bound
;;;   (n+1)! ||f(x) (-) TAYLOR-POLY-V(f,a,x,n)||  <=  ||f^(n+1)(theta)|| (x-a)^(n+1)
;;; for some theta in (a,x).  The reduction to scalar via a norm-attaining g.
;;; ====================================================================
(sp `(FORALL m (FORALL f (FORALL a (FORALL x (FORALL n
     (IMPLIES (AND (IS-NORMED-VECTOR-SPACE m)
               (AND (IS-FINITE-DIMENSIONAL m)
               (AND (IN f (FUN RR (VEC m)))
               (AND (IN a RR) (AND (IN x RR) (AND (IN n NN) (< a x)))))))
     (IMPLIES (TAYLOR-DIFFERENTIABLE-V m f a x n)
       (FORSOME theta (AND (< a theta) (AND (< theta x)
         (<= (* (FACTORIAL (succ n)) ((VNRM m) ,REMV))
             (* ((VNRM m) ((NTH-DERIV-V m f (succ n)) theta))
                (power (- x a) (succ n)))))))))))))))
(quietly (lambda () (di)(di)(di)(di)(di)(di)))   ; m,f,a,x,n ; ANT1
(dc-split)
(quietly (lambda () (di)))                        ; TAYLOR-DIFFERENTIABLE-V
(define GOAL (dc-gf))

;; R is a vector
(quietly (lambda () (fact 'vtaylor-remainder-in-vec 'm 'f 'a 'x 'n)))

;; norm-attained: g bounded, ||g||<=1, g(R) = ||R||
(define NAANT (conjuncts->and (list '(IS-NORMED-VECTOR-SPACE m) '(IS-FINITE-DIMENSIONAL m)
                                    (list 'IN REMV '(VEC m)))))
(cut NAANT) (dc-grind!) (dc-focus! GOAL)
(quietly (lambda () (fact 'norm-attained-by-functional 'm REMV)))
(ai (dc-find (lambda (z) (and ((dc-head? 'FORSOME) z) (dc-ment? 'is-bounded-linear-functional z) (dc-ment? 'vnrm z)))))
(dc-split)
(define G (caddr (dc-find (lambda (z) ((dc-head? 'IS-BOUNDED-LINEAR-FUNCTIONAL) z)))))
(define GOF (list 'COMPOSE G 'f))

;; g o f is a real function, and scalar-Taylor-differentiable
(quietly (lambda () (fact 'gof-in-fun 'm 'f G)))
(quietly (lambda () (fact 'gof-taylor-diff 'm 'f G 'a 'x 'n)))

;; scalar Taylor (Lagrange) on g o f : theta and the cleared equality
(define TLANT (conjuncts->and (list (list 'IN GOF '(FUN RR RR))
                                    '(IN a RR) '(IN x RR) '(IN n NN) '(< a x))))
(cut TLANT) (dc-grind!) (dc-focus! GOAL)
(quietly (lambda () (fact 'taylor-lagrange GOF 'a 'x 'n)))
(ai (dc-find (lambda (z) (and ((dc-head? 'FORSOME) z) (dc-ment? 'taylor-poly z) (dc-ment? 'nth-deriv z)))))
(dc-split)
(define THETA (caddr (dc-find (lambda (z) (and ((dc-head? '<) z) (eq? (cadr z) 'a) (symbol? (caddr z))
                 (dc-find (lambda (y) (and ((dc-head? '<) y) (equal? (cadr y) (caddr z)) (eq? (caddr y) 'x)))))))))
;; --- names for the endgame ---
(define SF '(FACTORIAL (succ n)))
(define PW '(power (- x a) (succ n)))
(define SR (list '- (list GOF 'x) (list 'TAYLOR-POLY GOF 'a 'n 'x)))
(define NTHGOF (list (list 'NTH-DERIV GOF '(succ n)) THETA))
(define FN1 (list (list 'NTH-DERIV-V 'm 'f '(succ n)) THETA))
(define NR (list (list 'VNRM 'm) REMV))
(define NFN1 (list (list 'VNRM 'm) FN1))
(define GRr (list G REMV))
(define GFN1 (list G FN1))

;; theta in RR ; (succ n) in NN
(quietly (lambda () (fact 'rr-strict-between-real 'a 'x THETA)))
(quietly (lambda () (fact 'nn-succ-closed 'n)))

;; commutation facts:  g(R) = scalar remainder ;  (g o f)^(n+1)(theta) = g(f^(n+1)(theta))
(quietly (lambda () (fact 'g-of-remainder 'm 'f G 'a 'x 'n)))    ; (= GRr SR)
(quietly (lambda () (fact 'gof-nth-deriv 'm 'f G 'n THETA)))     ; (= NTHGOF GFN1)

;; typings
(quietly (lambda () (fact 'nth-deriv-v-in-vec 'm 'f '(succ n) THETA)))  ; IN FN1 (VEC m)
(quietly (lambda () (fact 'vnrm-real 'm REMV)))                  ; IN NR RR
(quietly (lambda () (fact 'vnrm-real 'm FN1)))                   ; IN NFN1 RR
(quietly (lambda () (fact 'blf-app-real 'm G FN1)))             ; IN GFN1 RR

;; EQ1 :  (n+1)! ||R|| = g(fn1) * pw   -- rewrite the scalar Taylor equality
(quietly (lambda () (fact 'eq-sym GRr NR)))            ; (= NR GRr)  [from gReq (= GRr NR)]
(cut (list '= NR SR))                                  ; ||R|| = SR
(subst (list '= NR GRr)) (quietly (lambda () (ass)))   ; -> (= GRr SR) = g-of-remainder
(dc-focus! GOAL)
(quietly (lambda () (fact 'eq-sym NTHGOF GFN1)))       ; (= GFN1 NTHGOF)  [from gof-nth-deriv]
(cut (list '= (list '* SF NR) (list '* GFN1 PW)))      ; EQ1
(subst (list '= NR SR))                                ; NR -> SR
(subst (list '= GFN1 NTHGOF))                          ; g(fn1) -> (g o f)^(n+1)(theta)
(quietly (lambda () (ass)))                            ; = the taylor-lagrange equality
(dc-focus! GOAL)

;; LE1 :  g(fn1) <= ||fn1||   (norm-bounded-by-functionals + g <= |g|)
(define NBANT (conjuncts->and (list '(IS-NORMED-VECTOR-SPACE m)
                                    (list 'IS-BOUNDED-LINEAR-FUNCTIONAL 'm G)
                                    (list 'IN FN1 '(VEC m))
                                    (list '<= (list 'DUAL-NORM 'm G) 1))))
(cut NBANT) (dc-grind!) (dc-focus! GOAL)
(quietly (lambda () (fact 'norm-bounded-by-functionals 'm G FN1)))  ; (<= (abs GFN1) NFN1)
(quietly (lambda () (fact 'bdd-linfun-abs-real 'm G FN1)))          ; IN (abs GFN1) RR
(quietly (lambda () (fact 'rr-le-abs-self GFN1)))                   ; (<= GFN1 (abs GFN1))
(quietly (lambda () (fact 'rr-le-trans-c GFN1 (list 'abs GFN1) NFN1)))  ; (<= GFN1 NFN1)

;; pw in RR and 0 <= pw
(quietly (lambda () (fact 'rr-zero-in)))                           ; IN 0 RR
(dc-have! '(IN (- x a) RR) GOAL)                                   ; IN (x-a) RR
(quietly (lambda () (fact 'power-in-rr '(- x a) '(succ n))))       ; IN pw RR
(quietly (lambda () (fact 'rr-lt-diff-pos 'a 'x)))                  ; (< 0 (- x a))
(quietly (lambda () (fact 'rr-power-pos '(- x a) '(succ n))))       ; (< 0 pw)
(quietly (lambda () (fact 'rr-lt-implies-le 0 PW)))                 ; (<= 0 pw)

;; clear :  (n+1)! ||R|| <= ||fn1|| * pw.  Rewrite (n+1)!||R|| = g(fn1)*pw (EQ1),
;; then g(fn1)*pw <= ||fn1||*pw by right-monotonicity (LE1, 0<=pw).
(cut (list '<= (list '* SF NR) (list '* NFN1 PW)))
(subst (list '= (list '* SF NR) (list '* GFN1 PW)))     ; (n+1)!||R|| -> g(fn1)*pw
(quietly (lambda () (fact 'rr-mul-le-right GFN1 NFN1 PW)))   ; g(fn1)*pw <= ||fn1||*pw
(quietly (lambda () (ass)))
(dc-focus! GOAL)

;; witness theta, close the three conjuncts
(ew THETA)
(quietly (lambda () (dc-grind!) (ass-all)))
(qed 'vector-taylor-remainder-bound)
(category! 'vector-taylor-remainder-bound 'analysis)

;;; -----------------------------------------------------------------------
;;; Notation -- the ENGLISH of these predicates, declared beside their
;;; definitions and read by wff->english / the proof reader (operators.scm).
;;; A def-predicate's reading cannot be derived the way a structure's noun can
;;; (noun vs adjective: IS-COMPLETE wants "s is complete", not "s is a complete"),
;;; so it is written here, once, next to what it means.
(notation! 'IS-DIFF-AT-V 'kind 'predicate 'arity 4
           'english "$2 is differentiable at $3 with derivative $4, as a curve in $1")
(notation! 'TAYLOR-DIFFERENTIABLE-V 'kind 'predicate 'arity 5
           'english "$2 is $5 times differentiable from $3 to $4, as a curve in $1")
