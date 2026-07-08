(set! *vnb-quiet* #t)
(define (mq-goal) (wff-formula (sequent-node-assertion (proof-state-focus *ps*))))
(define (mq-di*) (let lp () (let* ((g (mq-goal)) (h (and (pair? g) (car g))))
                   (when (memq h '(FORALL IMPLIES)) (di) (lp)))))
(define (mq-last) (car (reverse (dg-sequent-nodes (proof-state-dg *ps*)))))
(define (mq-node! n) (set-proof-state-focus! *ps* n))
(define (mq-foc! pred)
  (let ((s (any-pred (lambda (s) (pred (wff-formula (sequent-node-assertion s)))) (proof-leaves))))
    (and s (set-proof-state-focus! *ps* s) s)))
(define (H? h) (lambda (g) (and (pair? g) (eq? (car g) h))))
(define (rep nm) (display nm)(display " done? ")(display (proof-done? *ps*))(newline)
  (when (not (proof-done? *ps*))
    (for-each (lambda (s) (display "  OPEN: ")(write (wff-formula (sequent-node-assertion s)))(newline)) (proof-leaves))))

;; invertible-mat-is-mat (projection, non-destructive typing)
(sp (make-wff '(FORALL A (FORALL n (FORALL U (IMPLIES (IS-INVERTIBLE-MAT A n U) (IN U (MAT n n (CARR A)))))))))
(mq-di*) (mac-h 'IS-INVERTIBLE-MAT '(IS-INVERTIBLE-MAT A n U)) (ai 1) (ass)
(rep 'invertible-mat-is-mat) (qed 'invertible-mat-is-mat)

;; identmat-invertible
(sp (make-wff '(FORALL A (IMPLIES (IS-RING A) (FORALL n (IS-INVERTIBLE-MAT A n (IDENTMAT A n)))))))
(mq-di*) (fact 'identmat-type 'A 'n) (fact 'identmat-left-identity 'A 'n 'n '(IDENTMAT A n))
(mac 'IS-INVERTIBLE-MAT) (di) (mq-foc! (H? 'FORSOME)) (ew '(IDENTMAT A n)) (di) (mq-foc! (H? 'AND)) (di) (ass-all)
(rep 'identmat-invertible) (qed 'identmat-invertible)

;; mat-equiv-refl
(sp (make-wff '(FORALL A (IMPLIES (IS-RING A) (FORALL m (FORALL n (FORALL C
     (IMPLIES (IN C (MAT m n (CARR A))) (MAT-EQUIV A m n C C)))))))))
(mq-di*) (fact 'identmat-left-identity 'A 'm 'n 'C) (fact 'identmat-right-identity 'A 'm 'n 'C)
(fact 'identmat-invertible 'A 'm) (fact 'identmat-invertible 'A 'n)
(mac 'MAT-EQUIV) (ew '(IDENTMAT A m)) (di) (mq-foc! (H? 'FORSOME)) (ew '(IDENTMAT A n)) (di)
(mq-foc! (H? '=)) (subst '(= (MATMUL A (IDENTMAT A m) C) C)) (subst '(= (MATMUL A C (IDENTMAT A n)) C)) (rfl) (ass-all)
(rep 'mat-equiv-refl) (qed 'mat-equiv-refl)

;; mat-equiv-right-mult
(sp (make-wff '(FORALL A (IMPLIES (IS-RING A) (FORALL m (FORALL n (FORALL C (FORALL V
     (IMPLIES (IN C (MAT m n (CARR A))) (IMPLIES (IS-INVERTIBLE-MAT A n V)
       (MAT-EQUIV A m n C (MATMUL A C V))))))))))))
(mq-di*)
(fact 'invertible-mat-is-mat 'A 'n 'V)
(fact 'identmat-left-identity 'A 'm 'n 'C) (fact 'identmat-invertible 'A 'm) (fact 'matmul-type 'A 'm 'n 'n 'C 'V)
(mac 'MAT-EQUIV) (ew '(IDENTMAT A m)) (di) (mq-foc! (H? 'FORSOME)) (ew 'V) (di)
(mq-foc! (H? '=)) (subst '(= (MATMUL A (IDENTMAT A m) C) C)) (rfl) (ass-all)
(rep 'mat-equiv-right-mult) (qed 'mat-equiv-right-mult)

;; mat-equiv-left-mult
(sp (make-wff '(FORALL A (IMPLIES (IS-RING A) (FORALL m (FORALL n (FORALL C (FORALL U
     (IMPLIES (IN C (MAT m n (CARR A))) (IMPLIES (IS-INVERTIBLE-MAT A m U)
       (MAT-EQUIV A m n C (MATMUL A U C))))))))))))
(mq-di*)
(fact 'invertible-mat-is-mat 'A 'm 'U)
(fact 'matmul-type 'A 'm 'm 'n 'U 'C)
(fact 'identmat-right-identity 'A 'm 'n '(MATMUL A U C)) (fact 'identmat-invertible 'A 'n)
(mac 'MAT-EQUIV) (ew 'U) (di) (mq-foc! (H? 'FORSOME)) (ew '(IDENTMAT A n)) (di)
(mq-foc! (H? '=)) (subst '(= (MATMUL A (MATMUL A U C) (IDENTMAT A n)) (MATMUL A U C))) (rfl) (ass-all)
(rep 'mat-equiv-left-mult) (qed 'mat-equiv-left-mult)

;; elem-f-invertible
(sp (make-wff '(FORALL A (IMPLIES (IS-RING A) (FORALL n (FORALL k (FORALL l
     (IMPLIES (IN k (INTERVAL 1 n)) (IMPLIES (IN l (INTERVAL 1 n)) (IMPLIES (NOT (= k l))
       (IS-INVERTIBLE-MAT A n (ELEM-F A n k l))))))))))))
(mq-di*)
(fact 'elem-f-type 'A 'n 'k 'l) (fact 'elem-f-type 'A 'n 'l 'k) (fact 'elem-f-inverse 'A 'n 'k 'l)
(cut '(NOT (= l k))) (define fcont (mq-last)) (di) (fact 'eq-sym 'l 'k) (ai '(NOT (= k l))) (mq-node! fcont)
(fact 'elem-f-inverse 'A 'n 'l 'k)
(mac 'IS-INVERTIBLE-MAT) (di) (mq-foc! (H? 'FORSOME)) (ew '(ELEM-F A n l k)) (di) (mq-foc! (H? 'AND)) (di) (ass-all)
(rep 'elem-f-invertible)
(%exit 0)
