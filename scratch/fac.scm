(define (gf) (and *ps* (not (proof-done? *ps*)) (wff-formula (sequent-node-assertion (proof-state-focus *ps*)))))
;; pure-algebra: the Caratheodory factor of a sum (curried antecedents)
(support 'caratheodory-sum-factor
  '(FORALL u1 (FORALL u2 (FORALL v1 (FORALL v2 (FORALL p (FORALL q (FORALL d
     (IMPLIES (= (- u1 v1) (* p d))
     (IMPLIES (= (- u2 v2) (* q d))
       (= (- (+ u1 u2) (+ v1 v2)) (* (+ p q) d))))))))))))
(sp '(FORALL f (FORALL g (FORALL pf (FORALL pg (FORALL x (FORALL a (IMPLIES
   (= (- (f x) (f a)) (* (pf x) (- x a)))
   (IMPLIES (= (- (g x) (g a)) (* (pg x) (- x a)))
     (= (- (+ (f x) (g x)) (+ (f a) (g a))) (* (+ (pf x) (pg x)) (- x a))))))))))))
(grind)
(display "GOAL: ") (write (gf)) (newline)
(bc* 'caratheodory-sum-factor () (ass) (ass))
(display "factorization DONE? ") (display (proof-done? *ps*)) (display "  focus: ") (write (gf)) (newline)
