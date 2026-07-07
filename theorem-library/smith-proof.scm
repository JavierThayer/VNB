;;; smith-proof.scm -- Brick B3 (LA Phase B): the Smith normal-form reduction,
;;; built on the ~ equivalence infrastructure (mat-equiv-proof.scm).
;;;   equiv-mul-both  -- A ~ U.A.V for U,V invertible (sandwiching preserves ~);
;;;   swap-to-corner  -- bring any entry (i0,j0) to position (1,1) preserving ~
;;;                      (row swap F[1,i0] on the left, col swap F[1,j0] on the
;;;                      right; the (1,1) value is A_{i0,j0} by the elem-f actions).
;;; Local mq-* proof helpers (leaf focus by goal head, etc.).

(define (mq-goal) (wff-formula (sequent-node-assertion (proof-state-focus *ps*))))
(define (mq-di*) (let lp () (let* ((g (mq-goal)) (h (and (pair? g) (car g))))
                   (when (memq h '(FORALL IMPLIES)) (di) (lp)))))
(define (mq-last) (car (reverse (dg-sequent-nodes (proof-state-dg *ps*)))))
(define (mq-node! n) (set-proof-state-focus! *ps* n))
(define (mq-foc! pred)
  (let ((s (any-pred (lambda (s) (pred (wff-formula (sequent-node-assertion s)))) (proof-leaves))))
    (and s (set-proof-state-focus! *ps* s) s)))
(define (H? h) (lambda (g) (and (pair? g) (eq? (car g) h))))

;; ---- equiv-mul-both ----
(sp (make-wff '(FORALL R (IMPLIES (IS-RING R) (FORALL m (FORALL n (FORALL A (FORALL U (FORALL V (IMPLIES (IN A (MAT m n (CARR R))) (IMPLIES (IS-INVERTIBLE-MAT R m U) (IMPLIES (IS-INVERTIBLE-MAT R n V) (MAT-EQUIV R m n A (MATMUL R (MATMUL R U A) V))))))))))))))
(mq-di*)
(fact 'invertible-mat-is-mat 'R 'm 'U)
(fact 'matmul-type 'R 'm 'm 'n 'U 'A)
(fact 'mat-equiv-left-mult 'R 'm 'n 'A 'U)
(fact 'mat-equiv-right-mult 'R 'm 'n '(MATMUL R U A) 'V)
(fact 'mat-equiv-trans 'R 'm 'n 'A '(MATMUL R U A) '(MATMUL R (MATMUL R U A) V))
(ass)
 (qed 'equiv-mul-both)
(category! 'equiv-mul-both 'algebra)

;; ---- swap-to-corner ----
(define Fm '(ELEM-F R m 1 i0))
(define Fn '(ELEM-F R n 1 j0))
(define P  (list 'MATMUL 'R Fm 'A))
(define B  (list 'MATMUL 'R P Fn))
(define IFo (list 'IF '(= 1 1) (list 'ENTRY P 1 'j0) (list 'IF '(= 1 j0) (list 'ENTRY P 1 1) (list 'ENTRY P 1 1))))
(define IFr (list 'IF '(= 1 1) '(ENTRY A i0 j0) (list 'IF '(= 1 i0) '(ENTRY A 1 j0) '(ENTRY A 1 j0))))
(sp (make-wff '(FORALL R (IMPLIES (IS-RING R) (FORALL m (FORALL n (FORALL A (FORALL i0 (FORALL j0 (IMPLIES (IN A (MAT m n (CARR R))) (IMPLIES (IN 1 (INTERVAL 1 m)) (IMPLIES (IN 1 (INTERVAL 1 n)) (IMPLIES (IN i0 (INTERVAL 1 m)) (IMPLIES (IN j0 (INTERVAL 1 n)) (IMPLIES (NOT (= 1 i0)) (IMPLIES (NOT (= 1 j0)) (FORSOME B (AND (MAT-EQUIV R m n A B) (= (ENTRY B 1 1) (ENTRY A i0 j0))))))))))))))))))))
(mq-di*)
(fact 'elem-f-invertible 'R 'm 1 'i0)
(fact 'elem-f-invertible 'R 'n 1 'j0)
(fact 'equiv-mul-both 'R 'm 'n 'A Fm Fn)
(fact 'elem-f-type 'R 'm 1 'i0)
(fact 'matmul-type 'R 'm 'm 'n Fm 'A)
(fact 'entry-in-carrier 'm 'n '(CARR R) 'A 'i0 'j0)
(ew B)
(di)
;; L1: MAT-EQUIV -- from equiv-mul-both ; L2: the (1,1) value
(mq-foc! (H? 'MAT-EQUIV))
(ass)
(mq-foc! (H? '=))
(fact 'elem-f-action 'R 'm 'n P 1 'j0 1 1)
(subst (list '= (list 'ENTRY B 1 1) IFo))
(if-true IFo) (define c1 (mq-last)) (rfl) (mq-node! c1)
(subst (list '= IFo (list 'ENTRY P 1 'j0)))
(fact 'elem-f-row-action 'R 'm 'n 'A 1 'i0 1 'j0)
(subst (list '= (list 'ENTRY P 1 'j0) IFr))
(if-true IFr) (define c2 (mq-last)) (rfl) (mq-node! c2)
(subst (list '= IFr '(ENTRY A i0 j0)))
(rfl)
(qed 'swap-to-corner)
(category! 'swap-to-corner 'algebra)
