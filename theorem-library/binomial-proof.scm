;;; binomial-proof.scm -- machine proof of the Binomial Theorem (SUM form),
;;; PROVEN by ordinary induction, IMPS-style (docs/algebra.t).
;;;
;;;   sum-expansion  : SUM(R, k->x*g(k-1)+y*g(k), succ N)
;;;                       = (x+y)*SUM(R,g,N) + x*g(-1) + y*g(N)   [multiply-and-shift]
;;;   binomial-theorem : (x+y)^n = SUM(R, COMB-KK(R,x,y,n), succ n)
;;;
;;; sum-expansion is proved by induction on the sum length N, PEELING one term
;;; with sum-succ (no higher-order summand matching: sum-succ binds f to the
;;; whole summand and lam-b reduces f(N)); per-step ring algebra is discharged
;;; by the commutative-ring oracle crs.  binomial-theorem is then a short
;;; induction on n: ring-power-succ + IH reduce the LHS to (x+y)*SUM(.,succ n);
;;; comb-kk-succ reshapes the RHS summand; sum-expansion collapses it;
;;; comb-kk-null / comb-kk-above kill the two boundary terms; crs closes.
;;; Vocabulary + warranted COMB-KK / arithmetic bricks live in binomial.scm.
;;;
;;; Depends on: binomial.scm, sequences.scm (SUM), ring-power.scm.
;;;
;;; NOTE: helper names avoid MIT Scheme's case-folding collisions -- the IH
;;; VALUE is `the-ih`, the search FUNCTION is `find-forall-hyp` (an earlier
;;; `bnm-IH` / `bnm-ih` pair silently aliased and clobbered the function to #f).

;; local FORALL/IMPLIES builder (tf lives in finsum-additive.scm, not in scope here)
(define (tf v type body) (list 'FORALL v (list 'IMPLIES type body)))

;; ---- proof drivers ----
(define (bnm-goal) (wff-formula (sequent-node-assertion (proof-state-focus *ps*))))
(define (bnm-leaves)
  (filter (lambda (s)(and (not (sequent-node-grounded? s))(null? (sequent-node-in-arrows s))))
          (dg-ungrounded-nodes (proof-state-dg *ps*))))
(define (bnm-focus pred)
  (dk-focus!
    (car (filter (lambda(nd)(pred (expression->string (wff-formula (sequent-node-assertion nd)))))
                 (bnm-leaves)))))
(define (find-forall-hyp sub)
  (let lp((as (map wff-formula (sequent-node-assumptions (proof-state-focus *ps*)))))
    (cond ((null? as) #f)
          ((and (pair?(car as))(eq?(caar as)'FORALL)(substring? sub (expression->string(car as))))(car as))
          (else (lp (cdr as))))))
(define (bnm-gmem i) (fact 'fun-apply-type-c 'g 'ZZ '(CARR r) i))

(define bnm-dffg '(VNB-LAMBDA k ZZ ((ADD R)((MUL R) x (g (- k 1)))((MUL R) y (g k)))))
(define (bnm-rhs nn)
  (list '(ADD R)(list '(ADD R)(list '(MUL R) '((ADD R) x y)(list 'SUM 'R 'g nn))
                                    (list '(MUL R) 'x '(g (- 0 1))))
                (list '(MUL R) 'y (list 'g nn))))
(define the-ih #f)

;; ==== sum-expansion (multiply-and-shift; induction on N) ====
(sp (make-wff (list 'FORALL 'N (list 'IMPLIES '(IN N NN)
     (tf 'R '(IS-COMMUTATIVE-RING R)(tf 'x '(IN x (CARR R))(tf 'y '(IN y (CARR R))(tf 'g '(IN g (FUN ZZ (CARR R)))
       (list '= (list 'SUM 'R bnm-dffg '(succ N))(bnm-rhs 'N))))))))))
(ni)
(bnm-focus (lambda (s)(substring? "succ(0)" s)))
(quietly (lambda ()
  (di)(di)(di)
  (fact 'nn-zero-in)(fact 'zz-zero-in)(fact 'bt-neg1-in-zz)(bnm-gmem 0)(bnm-gmem '(- 0 1))
  (macm 'sum-succ)(mac 'sum-zero)(lam-b)(crs)))
(bnm-focus (lambda (s)(and (substring? "implies" s)(not (substring? "succ(0)" s)))))
(di)(di)(set! the-ih (find-forall-hyp "is-commutative-ring"))(di)(di)(di)
(quietly (lambda ()
  (fact 'bt-nn-in-zz 'n)(fact 'bt-succ-in-nn 'n)(fact 'bt-nn-in-zz '(succ n))(fact 'bt-neg1-in-zz)
  (bnm-gmem '(- 0 1))(bnm-gmem 'n)(bnm-gmem '(succ n))(fact 'bt-sum-in-carr-zz 'r 'g 'n)
  (macm 'sum-succ)
  (inst+ the-ih 'r)(inst+ (find-forall-hyp "in carr(r), y in carr(r), g in fun") 'x)
  (inst+ (find-forall-hyp "y in carr(r), g in fun") 'y)(inst+ (find-forall-hyp "g in fun(zz") 'g)
  (subst (list '= (list 'SUM 'r bnm-dffg '(succ n)) (bnm-rhs 'n)))
  (lam-b)(macm 'bt-succ-minus-1)(macm 'sum-succ)(crs)))
(qed 'sum-expansion)
(topic! 'sum-expansion 'algebra)

;; ==== binomial-theorem (induction on n, via sum-expansion + Pascal) ====
(sp (make-wff (list 'FORALL 'n (list 'IMPLIES '(IN n NN)
     (tf 'R '(IS-COMMUTATIVE-RING R)(tf 'x '(IN x (CARR R))(tf 'y '(IN y (CARR R))
       (list '= '(RING-POWER R ((ADD R) x y) n) '(SUM R (COMB-KK R x y n)(succ n))))))))))
(ni)
(bnm-focus (lambda (s)(substring? ", 0) = " s)))
(quietly (lambda ()
  (di)(di)(di)
  (fact 'nn-zero-in)(fact 'commutative-ring-is-ring 'r)(fact 'ring-one-in 'r)
  (macm 'ring-power-zero)(macm 'sum-succ)(mac 'sum-zero)
  (fact 'comb-kk-0-0 'r 'x 'y)(subst (list '= (list (list 'COMB-KK 'r 'x 'y 0) 0) '(ONE r)))
  (macm 'ring-add-left-id)(crs)))
(set! the-ih #f)
(bnm-focus (lambda (s)(and (substring? "implies" s)(not (substring? ", 0) = " s)))))
(di)(di)(set! the-ih (find-forall-hyp "ring-power(r, (add(r))(x, y), n)"))(di)(di)(di)
(quietly (lambda ()
  (fact 'comb-kk-in-fun 'r 'x 'y 'n)(fact 'bt-succ-in-nn 'n)(fact 'bt-neg1-in-zz)
  (fact 'bt-nn-in-zz 'n)(fact 'bt-nn-in-zz '(succ n))
  (fact 'commutative-ring-is-ring 'r)(fact 'bt-add-in-carr 'r 'x 'y)
  (fact 'bt-sum-in-carr-zz 'r '(COMB-KK r x y n) '(succ n))(fact 'bt-neg1-neg)(fact 'bt-lt-succ 'n)
  (macm 'ring-power-succ)
  (inst+ the-ih 'r)(inst+ (find-forall-hyp "in carr(r), y in carr(r)], ring-power") 'x)
  (inst+ (find-forall-hyp "y in carr(r)], ring-power") 'y)
  (subst '(= (RING-POWER r ((ADD r) x y) n)(SUM r (COMB-KK r x y n)(succ n))))
  (subst (list '= (list '(MUL r) '(SUM r (COMB-KK r x y n)(succ n)) '((ADD r) x y))
                  (list '(MUL r) '((ADD r) x y) '(SUM r (COMB-KK r x y n)(succ n)))))
  (mac 'comb-kk-succ)
  (fact 'sum-expansion '(succ n) 'r 'x 'y '(COMB-KK r x y n))
  (subst (list '= (list 'SUM 'r '(VNB-LAMBDA k ZZ ((ADD r)((MUL r) x ((COMB-KK r x y n)(- k 1)))((MUL r) y ((COMB-KK r x y n) k)))) '(succ (succ n)))
               (list '(ADD r)(list '(ADD r)(list '(MUL r) '((ADD r) x y)(list 'SUM 'r '(COMB-KK r x y n) '(succ n)))(list '(MUL r) 'x '((COMB-KK r x y n)(- 0 1))))(list '(MUL r) 'y '((COMB-KK r x y n)(succ n))))))
  (fact 'comb-kk-null 'r 'x 'y 'n '(- 0 1))(subst (list '= '((COMB-KK r x y n)(- 0 1)) '(ZERO r)))
  (fact 'comb-kk-above 'r 'x 'y 'n '(succ n))(subst (list '= '((COMB-KK r x y n)(succ n)) '(ZERO r)))
  (crs)))
(qed 'binomial-theorem)
(topic! 'binomial-theorem 'algebra)
