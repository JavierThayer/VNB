;;; ringoid-quotient-ring-proof.scm -- IS-RING(RINGOID-QUOTIENT-RING r).
;;;
;;; ROUTE VALIDATION (2026-07-21): rq-add-assoc over class representatives.  This
;;; is the compute-down pattern every lifted ring law follows:
;;;   push each descended (ADD RQ) down to a class of a representative sum
;;;   (rq-add-computes), reduce to the ring's own law (ring-add-assoc via the
;;;   RINGOID-AS-RING view), and the two sides become the SAME class.
;;; Stated over a,b,c in CARR(r) directly; the full IS-RING conjunct wraps this
;;; with quotient-rep to reach every x,y,z in the quotient.

;; term builders (file-local, rqa- prefix)
(define (rqa-cls t)    (list 'CLASS '(RINGOID-SETOID r) t))        ; [t]
(define (rqa-add p q)  (list '(ADD (RINGOID-QUOTIENT-RING r)) p q)); [p] +/I [q] style
(define (rqa-radd p q) (list '(ADD r) p q))                       ; (ADD r) p q
;; the rq-add-computes instance equation:  (ADD RQ)[p][q] = [(ADD r) p q]
(define (rqa-ceq p q)
  (list '= (rqa-add (rqa-cls p) (rqa-cls q)) (rqa-cls (rqa-radd p q))))

(sp (make-wff
  (forall-guarded '(r) '((IS-RINGOID r))
    (forall-guarded '(a b c) '((IN a (CARR r)) (IN b (CARR r)) (IN c (CARR r)))
      (list '= (rqa-add (rqa-add (rqa-cls 'a) (rqa-cls 'b)) (rqa-cls 'c))
               (rqa-add (rqa-cls 'a) (rqa-add (rqa-cls 'b) (rqa-cls 'c))))))))

(di)(di)(di)(di)(di)(di)(di)(di)     ; r, IS-RINGOID r ; a,b,c in CARR r ; goal = equation

;; intermediate carrier typings for the two sums
(fact 'ring-add-closed-ringoid-as-ring 'r 'a 'b)   ; (ADD r) a b in CARR r
(fact 'ring-add-closed-ringoid-as-ring 'r 'b 'c)   ; (ADD r) b c in CARR r

;; compute the inner descended adds down to classes of sums
(fact 'rq-add-computes 'r 'a 'b)(subst (rqa-ceq 'a 'b))
(fact 'rq-add-computes 'r 'b 'c)(subst (rqa-ceq 'b 'c))
;; compute the outer descended adds
(fact 'rq-add-computes 'r (rqa-radd 'a 'b) 'c)(subst (rqa-ceq (rqa-radd 'a 'b) 'c))
(fact 'rq-add-computes 'r 'a (rqa-radd 'b 'c))(subst (rqa-ceq 'a (rqa-radd 'b 'c)))

;; goal now:  [ (a+b)+c ] = [ a+(b+c) ] ; the ring's own associativity closes it
(fact 'ring-add-assoc-ringoid-as-ring 'r 'a 'b 'c)
(subst (list '= (rqa-radd (rqa-radd 'a 'b) 'c) (rqa-radd 'a (rqa-radd 'b 'c))))
(rfl)

(qed 'rq-add-assoc-classes)
