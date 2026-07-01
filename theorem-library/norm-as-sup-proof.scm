;;; norm-as-sup-proof.scm -- the norm as a supremum of bounded functionals:
;;; for a finite-dimensional real NVS m and x in VEC(m),
;;;   ||x|| = sup { |f(x)| : f a bounded linear functional, ||f|| <= 1 }.
;;;
;;; The <= direction is elementary (the dual norm is a bound); the "attained"
;;; direction is the Hahn-Banach payoff: seed the functional r.x |-> r.||x|| on
;;; the line RR.x (norm 1) and extend it to all of m via `hahn-banach', giving a
;;; bounded g with ||g|| <= 1 and g(x) = ||x||.  It is `norm-attained' that the
;;; vector-valued Taylor remainder bound reduces to the scalar case with.
;;;
;;; Loads after hahn-banach-full-proof (uses hahn-banach, DUAL-NORM(-ON),
;;; dual-norm-on-le-bound, IS-(BOUNDED-)LINEAR-FUNCTIONAL[-ON]).  Scaffolding
;;; first (vocabulary + warranted routine cores); the three theorems follow.

;;; ====================================================================
;;; vocabulary: the line RR.v spanned by a single vector
;;; ====================================================================

;;; LINE(m, v) = { r.v : r in RR } -- the one-dimensional subspace through v.
;;; (SPAN-ADD-ONE(m, s, v) adds v to an existing submodule s; here s is the
;;; trivial one, so we give the single-vector span its own name.)
(def-functoid 'LINE '(m v)
  '(SEP y_ (VEC m)
     (FORSOME r_ (AND (IN r_ RR) (= y_ ((ACT m) r_ v))))))

;;; ====================================================================
;;; warranted routine cores
;;; ====================================================================

;;; RR.v is a submodule (closed under +, negation, scalar action; contains 0).
(add-to-pss 'line-is-submodule
  '(FORALL m (FORALL v
     (IMPLIES (IS-NORMED-VECTOR-SPACE m) (IMPLIES (IN v (VEC m))
        (IS-SUBMODULE m (LINE m v)))))))
(warrant! 'line-is-submodule 'reference
  "RR.v is the image of the scalar action, closed under addition, negation and
   the action, and contains 0 = 0.v; so it is a submodule.")
(category! 'line-is-submodule 'analysis)

;;; v itself lies on its line (v = 1.v).
(add-to-pss 'line-has-v
  '(FORALL m (FORALL v
     (IMPLIES (IS-NORMED-VECTOR-SPACE m) (IMPLIES (IN v (VEC m))
        (IN v (LINE m v)))))))
(warrant! 'line-has-v 'reference
  "v = 1.v, so v is in RR.v = LINE(m,v).")
(category! 'line-has-v 'analysis)

;;; The seed functional exists: a norm-<=1 bounded linear functional on the line
;;; RR.v that hits ||v|| at v.  (On a one-dimensional space r.v |-> r.||v|| is
;;; linear with operator norm exactly 1 when v /= 0, and the 0 functional works
;;; when v = 0; either way DUAL-NORM-ON <= 1 and the value at v is ||v||.)
(add-to-pss 'line-functional-exists
  '(FORALL m (FORALL v
     (IMPLIES (IS-NORMED-VECTOR-SPACE m) (IMPLIES (IN v (VEC m))
       (FORSOME f_ (AND (IS-BOUNDED-LINEAR-FUNCTIONAL-ON m (LINE m v) f_)
                   (AND (<= (DUAL-NORM-ON m (LINE m v) f_) 1)
                        (= (f_ v) ((VNRM m) v))))))))))
(warrant! 'line-functional-exists 'reference
  "On the one-dimensional subspace RR.v the map r.v |-> r.||v|| is a bounded
   linear functional of operator norm <= 1 (=1 for v/=0) taking the value ||v||
   at v; for v=0 the zero functional serves.")
(category! 'line-functional-exists 'analysis)

;;; DUAL-NORM is a genuine bound: |f(x)| <= ||f|| ||x|| on all of VEC(m).
(add-to-pss 'dual-norm-is-bound
  '(FORALL m (FORALL f (FORALL x
     (IMPLIES (IS-BOUNDED-LINEAR-FUNCTIONAL m f) (IMPLIES (IN x (VEC m))
        (<= (abs (f x)) (* (DUAL-NORM m f) ((VNRM m) x)))))))))
(warrant! 'dual-norm-is-bound 'reference
  "The operator norm DUAL-NORM(m,f) satisfies |f(x)| <= ||f|| ||x|| for every x
   (it is defined as the least such bound; in particular it IS a bound).")
(category! 'dual-norm-is-bound 'analysis)

;;; DUAL-NORM is a nonnegative real (whole-space companion of dual-norm-on-nonneg).
(add-to-pss 'dual-norm-nonneg
  '(FORALL m (FORALL f
     (IMPLIES (IS-BOUNDED-LINEAR-FUNCTIONAL m f)
       (AND (IN (DUAL-NORM m f) RR) (<= 0 (DUAL-NORM m f)))))))
(warrant! 'dual-norm-nonneg 'reference
  "DUAL-NORM is defined by IOTA over c in RR with 0<=c, so for a bounded f it is
   a nonnegative real.")
(category! 'dual-norm-nonneg 'analysis)

;;; |f(x)| is a real for a bounded functional (whole-space typing helper).
(add-to-pss 'bdd-linfun-abs-real
  '(FORALL m (FORALL f (FORALL x
     (IMPLIES (IS-BOUNDED-LINEAR-FUNCTIONAL m f) (IMPLIES (IN x (VEC m))
        (IN (abs (f x)) RR)))))))
(warrant! 'bdd-linfun-abs-real 'reference
  "A bounded linear functional maps VEC(m) into RR, so |f(x)| is a real.")
(category! 'bdd-linfun-abs-real 'analysis)

;;; A linear functional ON the whole carrier IS a linear functional (the two
;;; predicates have identical bodies when the subspace s is VEC(m)).
(add-to-pss 'linfun-on-vec-is-linfun
  '(FORALL m (FORALL f
     (IMPLIES (IS-LINEAR-FUNCTIONAL-ON m (VEC m) f) (IS-LINEAR-FUNCTIONAL m f)))))
(warrant! 'linfun-on-vec-is-linfun 'reference
  "IS-LINEAR-FUNCTIONAL-ON m (VEC m) f and IS-LINEAR-FUNCTIONAL m f unfold to the
   same conjunction (f in FUN(VEC m,RR), additive, homogeneous over VEC m).")
(category! 'linfun-on-vec-is-linfun 'analysis)

;;; Whole-space companion of dual-norm-on-le-bound: the operator norm is <= any
;;; nonnegative bound c that dominates |f| on all of VEC(m).
(add-to-pss 'dual-norm-le-bound
  '(FORALL m (FORALL f (FORALL c
     (IMPLIES (IS-LINEAR-FUNCTIONAL m f)
      (IMPLIES (IN c RR)
       (IMPLIES (<= 0 c)
        (IMPLIES (FORALL w_ (IMPLIES (IN w_ (VEC m))
                   (<= (abs (f w_)) (* c ((VNRM m) w_)))))
          (<= (DUAL-NORM m f) c)))))))))
(warrant! 'dual-norm-le-bound 'reference
  "DUAL-NORM(m,f) is the least c>=0 bounding |f(w)| by c*||w|| on VEC(m) (IOTA
   least-upper-bound), hence <= any such bound c.")
(category! 'dual-norm-le-bound 'analysis)

;;; ====================================================================
;;; THEOREM 1: norm-bounded-by-functionals -- |f(x)| <= ||x|| when ||f|| <= 1.
;;; ====================================================================
(sp '(FORALL m (FORALL f (FORALL x
     (IMPLIES (AND (IS-NORMED-VECTOR-SPACE m)
               (AND (IS-BOUNDED-LINEAR-FUNCTIONAL m f)
                (AND (IN x (VEC m)) (<= (DUAL-NORM m f) 1))))
       (<= (abs (f x)) ((VNRM m) x)))))))
(quietly (lambda () (di)(di)(di)(di)))
(dc-split)
(define NBGOAL (dc-gf))
(quietly (lambda () (fact 'dual-norm-is-bound 'm 'f 'x)))    ; |f x| <= DUAL*||x||
(quietly (lambda () (fact 'vnrm-nonneg 'm 'x)))              ; 0 <= ||x||
(quietly (lambda () (fact 'vnrm-real 'm 'x)))                ; ||x|| in RR
(quietly (lambda () (fact 'bdd-linfun-abs-real 'm 'f 'x)))   ; |f x| in RR
(quietly (lambda () (fact 'dual-norm-nonneg 'm 'f))) (dc-split)   ; DUAL in RR
(quietly (lambda () (fact 'rr-one-in)))                     ; 1 in RR
;; le-bound-mono: |f x| <= DUAL*||x||, DUAL <= 1, 0<=||x||  =>  |f x| <= 1*||x||
(quietly (lambda () (fact 'le-bound-mono
                      (list 'abs (list 'f 'x)) (list 'DUAL-NORM 'm 'f) 1 (list (list 'VNRM 'm) 'x))))
;; 1*||x|| = ||x|| : rewrite the goal to match
(cut (list '= (list (list 'VNRM 'm) 'x) (list '* 1 (list (list 'VNRM 'm) 'x))))
(crs)
(dc-focus! NBGOAL)
(subst (list '= (list (list 'VNRM 'm) 'x) (list '* 1 (list (list 'VNRM 'm) 'x))))
(quietly (lambda () (ass-all)))
(qed 'norm-bounded-by-functionals)
(category! 'norm-bounded-by-functionals 'analysis)

;;; ====================================================================
;;; THEOREM 2: norm-attained-by-functional -- some bounded g with ||g|| <= 1
;;; attains g(x) = ||x||.  The Hahn-Banach direction (finite-dimensional m).
;;; ====================================================================
(sp `(FORALL m (FORALL x
     (IMPLIES (AND (IS-NORMED-VECTOR-SPACE m)
               (AND (IS-FINITE-DIMENSIONAL m) (IN x (VEC m))))
       (FORSOME g (AND (IS-BOUNDED-LINEAR-FUNCTIONAL m g)
                  (AND (<= (DUAL-NORM m g) 1)
                       (= (g x) ((VNRM m) x)))))))))
(quietly (lambda () (di)(di)(di)))
(dc-split)
(define NAGOAL (dc-gf))
(define LINEx '(LINE m x))

;; seed functional on the line RR.x
(quietly (lambda () (fact 'line-functional-exists 'm 'x)))
(ai (dc-find (lambda (z) (and ((dc-head? 'FORSOME) z) (dc-ment? 'line z) (dc-ment? 'dual-norm-on z)))))
(dc-split)
(define F0 (cadddr (dc-find (lambda (z) (and ((dc-head? 'IS-BOUNDED-LINEAR-FUNCTIONAL-ON) z) (dc-ment? 'line z))))))
(define C (list 'DUAL-NORM-ON 'm LINEx F0))
(define F0X (dc-find (lambda (z) (and ((dc-head? '=) z) (dc-ment? F0 z) (dc-ment? 'vnrm z)))))   ; (= (F0 x)(VNRM x))

;; apply hahn-banach: extend F0 to g on all of VEC(m)
(quietly (lambda () (fact 'line-is-submodule 'm 'x)))
(define HBANT (conjuncts->and (list '(IS-NORMED-VECTOR-SPACE m)
                                    '(IS-FINITE-DIMENSIONAL m)
                                    (list 'IS-SUBMODULE 'm LINEx)
                                    (list 'IS-BOUNDED-LINEAR-FUNCTIONAL-ON 'm LINEx F0))))
(cut HBANT) (dc-grind!) (dc-focus! NAGOAL)
(quietly (lambda () (fact 'hahn-banach 'm LINEx F0)))
(ai (dc-find (lambda (z) (and ((dc-head? 'FORSOME) z) (dc-ment? 'extends-on z) (dc-ment? F0 z)))))
(dc-split)
(define G (cadddr (dc-find (lambda (z) (and ((dc-head? 'IS-LINEAR-FUNCTIONAL-ON) z) (equal? (caddr z) '(VEC m)))))))
(define BND (dc-find (lambda (z) (and ((dc-head? 'FORALL) z) (dc-ment? G z) (dc-ment? 'dual-norm-on z)))))
(define EXT (dc-find (lambda (z) (and ((dc-head? 'EXTENDS-ON) z) (dc-ment? G z) (dc-ment? F0 z)))))

;; C = ||f0||_line is a nonnegative real; G is linear on the whole space
(quietly (lambda () (fact 'dual-norm-on-nonneg 'm LINEx F0))) (dc-split)   ; (IN C RR),(<= 0 C)
(quietly (lambda () (fact 'linfun-on-vec-is-linfun 'm G)))                 ; IS-LINEAR-FUNCTIONAL m G

;; (A) G is a bounded linear functional (witness bound c = C)
(define BGG (list 'IS-BOUNDED-LINEAR-FUNCTIONAL 'm G))
(cut BGG)
(mac 'IS-BOUNDED-LINEAR-FUNCTIONAL)
(quietly (lambda () (dc-grind!)))                    ; closes LINEAR; stalls at FORSOME c
(hbf-focus-open! (lambda (g) (and (pair? g) (eq? (car g) 'FORSOME) (dc-ment? 'abs g))))
(ew C)
(quietly (lambda () (dc-grind!)))                    ; (IN C RR),(<=0 C),(bound = BND)
(define (focus-main!) (hbf-focus-open! (lambda (z) (and (pair? z) (eq? (car z) 'FORSOME) (dc-ment? 'is-bounded-linear-functional z)))))
(focus-main!)

;; (B) ||G|| <= 1 :  ||G|| <= C  and  C <= 1
(quietly (lambda () (fact 'dual-norm-le-bound 'm G C)))     ; (<= (DUAL-NORM m G) C)
(quietly (lambda () (fact 'dual-norm-nonneg 'm G))) (dc-split)   ; (IN (DUAL-NORM m G) RR)
(quietly (lambda () (fact 'rr-one-in)))
(quietly (lambda () (fact 'rr-le-trans-c (list 'DUAL-NORM 'm G) C 1)))   ; (<= (DUAL-NORM m G) 1)

;; (C) G(x) = ||x|| :  G(x) = F0(x) (extends) and F0(x) = ||x||
(quietly (lambda () (fact 'line-has-v 'm 'x)))              ; (IN x (LINE m x))
(mac-h 'EXTENDS-ON EXT)
(let ((ef (dc-find (lambda (z) (and ((dc-head? 'FORALL) z) (dc-ment? G z) (dc-ment? F0 z) (dc-ment? '= z))))))
  (quietly (lambda () (inst+ ef 'x))))
(hb-detach-opt! (list 'IN 'x LINEx))                       ; (= (G x)(F0 x))
(define GXF0 (dc-find (lambda (z) (and ((dc-head? '=) z) (dc-ment? G z) (dc-ment? F0 z)))))

;; assemble the witness (focus is already on the main goal; the (B)/(C) facts
;; kept it there -- it is no longer a proof-LEAF after dc-split, but IS the focus)
(ew G)
;; make G(x) = ||x|| a standalone assumption (G(x)=F0(x)=||x||), so dc-grind!'s
;; global ass-all closes all three conjuncts of the witnessed goal
(cut (list '= (list G 'x) (list (list 'VNRM 'm) 'x)))
(subst GXF0)                                               ; (= (G x) ||x||) -> (= (F0 x) ||x||)
(quietly (lambda () (ass-all)))
(quietly (lambda () (dc-grind!)))
(qed 'norm-attained-by-functional)
(category! 'norm-attained-by-functional 'analysis)

;;; ====================================================================
;;; THEOREM 3: norm-as-sup -- ||x|| is the least upper bound of
;;;   { |f(x)| : f bounded linear, ||f|| <= 1 }.
;;; (No SUP functoid: the LUB is stated as upper-bound + least, mirroring the
;;; body of DUAL-NORM's IOTA.)  Assembles theorems 1 and 2.
;;; ====================================================================
(add-to-pss 'eq-sym '(FORALL a (FORALL b (IMPLIES (= a b) (= b a)))))
(warrant! 'eq-sym 'well-known "Symmetry of (partial) equality.")
(category! 'eq-sym 'plumbing)
(add-to-pss 'abs-nonneg-le
  '(FORALL a (FORALL c (IMPLIES (IN a RR) (IMPLIES (<= 0 a) (IMPLIES (<= (abs a) c) (<= a c)))))))
(warrant! 'abs-nonneg-le 'well-known "For a real a >= 0, |a| = a, so |a| <= c gives a <= c.")
(category! 'abs-nonneg-le 'analysis)

;; The functional-bound antecedents are CURRIED (BLF => ||f||<=1 => ...) so intros
;; and detaches are single-premise: no AND to build, hence no dc-grind!/ass-all
;; (global, focus-scattering) is needed after the norm-attained ai+dc-split.
(define UB-CLAUSE
  '(FORALL f (IMPLIES (IS-BOUNDED-LINEAR-FUNCTIONAL m f) (IMPLIES (<= (DUAL-NORM m f) 1)
     (<= (abs (f x)) ((VNRM m) x))))))
(define LEAST-CLAUSE
  '(FORALL d (IMPLIES (AND (IN d RR)
                       (FORALL f (IMPLIES (IS-BOUNDED-LINEAR-FUNCTIONAL m f) (IMPLIES (<= (DUAL-NORM m f) 1)
                                   (<= (abs (f x)) d)))))
     (<= ((VNRM m) x) d))))

(sp (list 'FORALL 'm (list 'FORALL 'x
     (list 'IMPLIES (conjuncts->and '((IS-NORMED-VECTOR-SPACE m) (IS-FINITE-DIMENSIONAL m) (IN x (VEC m))))
       (list 'AND UB-CLAUSE LEAST-CLAUSE)))))
(quietly (lambda () (di)(di)(di)))
(dc-split)                    ; splits antecedent (NVS,FINDIM,INx) AND the goal (UB | LEAST)
(define VNRMx '((VNRM m) x))

;; ---- upper-bound clause (focused leaf: ||x|| bounds every |f(x)|) ----
(quietly (lambda () (di)(di)(di)))           ; f ; BLF ; (<= DN 1)
(define UBf (caddr (dc-find (lambda (z) (and ((dc-head? 'IS-BOUNDED-LINEAR-FUNCTIONAL) z))))))
(define UBBODY (dc-gf))
(define NBANT (conjuncts->and (list '(IS-NORMED-VECTOR-SPACE m)
                                    (list 'IS-BOUNDED-LINEAR-FUNCTIONAL 'm UBf)
                                    '(IN x (VEC m))
                                    (list '<= (list 'DUAL-NORM 'm UBf) 1))))
(cut NBANT) (dc-grind!) (dc-focus! UBBODY)
(quietly (lambda () (fact 'norm-bounded-by-functionals 'm UBf 'x)))
(quietly (lambda () (ass-all)))

;; ---- least clause (other leaf: ||x|| <= any upper bound d) ----
(hbf-focus-open! (lambda (z) (and (pair? z) (eq? (car z) 'FORALL) (dc-ment? 'rr z) (dc-ment? 'is-bounded-linear-functional z))))
(quietly (lambda () (di)(di)))                ; d ; (AND (IN d RR) UBd)
(dc-split)
(define LEASTBODY (dc-gf))                    ; (<= ((VNRM m) x) d)
(define UBd (dc-find (lambda (z) (and ((dc-head? 'FORALL) z) (dc-ment? 'is-bounded-linear-functional z) (not (dc-ment? 'vnrm z))))))
;; obtain the norm-attaining functional g
(define NAANT (conjuncts->and '((IS-NORMED-VECTOR-SPACE m) (IS-FINITE-DIMENSIONAL m) (IN x (VEC m)))))
(cut NAANT) (dc-grind!) (dc-focus! LEASTBODY)
(quietly (lambda () (fact 'norm-attained-by-functional 'm 'x)))
(ai (dc-find (lambda (z) (and ((dc-head? 'FORSOME) z) (dc-ment? 'is-bounded-linear-functional z) (dc-ment? 'vnrm z)))))
(dc-split)                                    ; BLF-g, (<= DN 1), (= (g x) ||x||)   [quirk from here]
(define GG (caddr (dc-find (lambda (z) (and ((dc-head? 'IS-BOUNDED-LINEAR-FUNCTIONAL) z))))))
(define GXeq (dc-find (lambda (z) (and ((dc-head? '=) z) (dc-ment? 'vnrm z) (dc-ment? GG z)))))  ; (= (g x) ||x||)
;; |g(x)| <= d : instantiate the (curried) upper bound at g and detach twice
(quietly (lambda () (inst+ UBd GG)))          ; (IMPLIES BLF-g (IMPLIES (<= DN 1) (<= (abs (g x)) d)))
(dc-detach-impl! (list 'IS-BOUNDED-LINEAR-FUNCTIONAL 'm GG))   ; (IMPLIES (<= DN 1) (<= (abs (g x)) d))
(dc-detach-impl! (list '<= (list 'DUAL-NORM 'm GG) 1))         ; (<= (abs (g x)) d)
;; ||x|| typing and ||x|| = g(x)
(quietly (lambda () (fact 'vnrm-real 'm 'x)))
(quietly (lambda () (fact 'vnrm-nonneg 'm 'x)))
(quietly (lambda () (fact 'eq-sym (list GG 'x) VNRMx)))           ; (= ||x|| (g x))  [GXeq present]
;; (<= (abs ||x||) d) from |g(x)| <= d by rewriting ||x|| -> g(x)
(cut (list '<= (list 'abs VNRMx) 'd))             ; goal (<= (abs ||x||) d)
(subst (list '= VNRMx (list GG 'x)))              ; ||x|| -> g(x): goal (<= (abs (g x)) d)
(quietly (lambda () (ass)))                        ; matches detached |g(x)| <= d
;; abs-nonneg-le on ||x|| (>= 0): ||x|| <= d
(quietly (lambda () (fact 'abs-nonneg-le VNRMx 'd)))   ; (<= ||x|| d) = goal
(quietly (lambda () (ass)))
(qed 'norm-as-sup)
(category! 'norm-as-sup 'analysis)
