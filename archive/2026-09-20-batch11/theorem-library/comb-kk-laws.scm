;;; comb-kk-laws.scm -- the six COMB-KK / Bernstein plumbing supports of
;;; theorem-library/binomial.scm, PROVEN.
;;;
;;; COMB-KK(R,x,y,m) is the weighted binomial coefficient family
;;;
;;;     COMB-KK(R,x,y,0)        =  k |-> IF k = 0 THEN ONE(R) ELSE ZERO(R)
;;;     COMB-KK(R,x,y,succ m)   =  k |-> x * COMB-KK(.,m)(k-1) + y * COMB-KK(.,m)(k)
;;;
;;; installed by `def-by-nn-recursion' (ordinals.scm) as the two DEFINITIONAL
;;; quasi-equations comb-kk-zero / comb-kk-succ.  Its index k runs over ZZ --
;;; that is what makes k-1 total at k = 0 and makes the Pascal step a rewrite
;;; rather than a case split -- and every theorem below is the one-step NN
;;; induction on m that binomial.scm's warrants describe in prose.
;;;
;;; SHAPE OF EACH PROOF.  `ni' (pi-nn-induction!) tests the goal's SHAPE: it
;;; wants (FORALL m (IMPLIES (IN m NN) body)) at the top.  Every statement below
;;; is spelled with the RING first, so the induction variable is not outermost
;;; and `ni' does not fire on the statement as written.  Rather than re-order
;;; anybody's statement, each law is proved twice: an `-ind' auxiliary with m
;;; outermost, which is what the induction runs on, and then the literal
;;; statement, closed from it by one `fact'.  The auxiliaries are ordinary
;;; theorems and are named here so the script is re-runnable; they are not
;;; cited anywhere else.
;;;
;;; Helper prefix: ckl-.
;;;
;;; LOAD WINDOW, by FILE NAME.
;;;   after   theorem-library/ring-zero-one-power   (bt-one-in-carr)
;;;           theorem-library/op-typing             (bt-add-in-carr,
;;;                                                  ring-carrier-closed-mul)
;;;           theorem-library/binary-minus-laws     (zz-sub-in-zz)
;;;           theorem-library/fun-apply-type-proof  (fun-apply-type-c)
;;;           theorem-library/nn-parity-proof       (nn-succ-plus-one)
;;;           theorem-library/nn-order-basics       (nn-in-rr)
;;;           theorem-library/binomial              (the supports it replaces,
;;;                                                  comb-kk-zero / comb-kk-succ)
;;;   before  theorem-library/binomial-proof        (first citer)

(define (ckl-tf v type body) (list 'FORALL v (list 'IMPLIES type body)))

;; 1-based index of FORM in the focus context (what `ineq' wants).
(define (ckl-idx form)
  (let loop ((as (dk-asms)) (i 1))
    (cond ((null? as) (error "ckl-idx: not in context" (expression->string form)))
          ((equal? (car as) form) i)
          (#t (loop (cdr as) (+ i 1))))))

;; Land (IN t RR) for a term already typed in ZZ.
(define (ckl-zz->rr! t)
  (fact 'zz-subset-qq t)
  (fact 'qq-subset-rr t))

;;; =======================================================================
;;; bt-succ-minus-1  --  (succ n) - 1 = n
;;;
;;; RESTATED, and this is the one statement below that is NOT binomial.scm's.
;;; The support reads `forall n in ZZ. (succ n) - 1 = n'.  Over ZZ that is not a
;;; theorem of this tree: `succ' is the NN successor (arith-eval.scm:87) and the
;;; only fact relating it to `+' is nn-succ-plus-one, guarded on (IN n NN).
;;; Nothing constrains (succ n) for a negative n, so the ZZ form asserts
;;; something about succ off its characterised domain.  Measured, with the goal
;;; peeled and n typed all the way into RR: nn-succ-plus-one does not detach,
;;; and crs / arith / ineq / prop each decline, prop with the countermodel
;;; "succ(n) - 1 = n FALSE, everything else TRUE".
;;;
;;; The guard is therefore (IN n NN).  All three citers already supply it --
;;; binomial-proof (the SUM index, an NN induction variable), series-linearity
;;; (`(fact 'bt-succ-minus-1 n)' with n the NN induction variable) and
;;; bernstein-density (which lands `(fact 'nn-subset-zz q)' on the line above,
;;; so q is NN-typed) -- and all three were re-run against this statement.
;;; =======================================================================
(sp (make-wff (ckl-tf 'n '(IN n NN) '(= (- (succ n) 1) n))))
(dk-peel!)
(fact 'nn-succ-plus-one 'n)
(subst '(= (succ n) (+ n 1)))
(fact 'nn-in-rr 'n)
(crs)
(qed 'bt-succ-minus-1)
(topic! 'bt-succ-minus-1 'plumbing)

;;; =======================================================================
;;; bt-sum-in-carr-zz  --  SUM(R,g,N) in CARR(R) for a ZZ-indexed g
;;; =======================================================================
(sp (make-wff
      (ckl-tf 'n_ '(IN n_ NN)
        (ckl-tf 'R '(IS-COMMUTATIVE-RING R)
          (ckl-tf 'g '(IN g (FUN ZZ (CARR R)))
            '(IN (SUM R g n_) (CARR R)))))))
(let* ((br (use-induction))
       (iv (cdr (assq 'var br)))
       (ih (cdr (assq 'ih  br)))
       (st (cdr (assq 'step br)))
       (bs (cdr (assq 'base br))))
  ;; ---- base: SUM(R,g,0) ----
  (dk-focus! bs)
  (dk-peel!)
  (let* ((goal (dk-goal))                       ; (IN (SUM r g 0) (CARR r))
         (r (cadr (cadr goal))))
    (fact 'commutative-ring-is-ring r)
    (mac 'sum-zero)
    (fact 'ring-zero-in r)
    (ass))
  ;; ---- step: SUM(R,g,succ n) ----
  (dk-focus! st)
  (dk-peel!)
  (let* ((goal (dk-goal))                       ; (IN (SUM r g (succ n)) (CARR r))
         (r (cadr (cadr goal)))
         (g (caddr (cadr goal))))
    (fact 'commutative-ring-is-ring r)
    (mac 'sum-succ)
    (fact 'nn-subset-zz iv)
    (fact 'fun-apply-type-c g 'ZZ (list 'CARR r) iv)
    (dk-apply! ih r g)
    (fact 'bt-add-in-carr r (list 'SUM r g iv) (list g iv))
    (ass)))
(qed 'sum-in-carr-zz-ind)
(topic! 'sum-in-carr-zz-ind 'algebra)

(sp (make-wff
      (ckl-tf 'R '(IS-COMMUTATIVE-RING R)
        (ckl-tf 'g '(IN g (FUN ZZ (CARR R)))
          (ckl-tf 'N '(IN N NN) '(IN (SUM R g N) (CARR R)))))))
(dk-peel!)
(let* ((goal (dk-goal))
       (r (cadr (cadr goal)))
       (g (caddr (cadr goal)))
       (n (cadddr (cadr goal))))
  (fact 'sum-in-carr-zz-ind n r g)
  (ass))
(qed 'bt-sum-in-carr-zz)
(topic! 'bt-sum-in-carr-zz 'algebra)

;;; =======================================================================
;;; comb-kk-0-0  --  COMB-KK(R,x,y,0)(0) = ONE(R)
;;; =======================================================================
(sp (make-wff
      (ckl-tf 'R '(IS-COMMUTATIVE-RING R)
        (ckl-tf 'x '(IN x (CARR R))
          (ckl-tf 'y '(IN y (CARR R))
            (list '= (list (list 'COMB-KK 'R 'x 'y 0) 0) '(ONE R)))))))
(dk-peel!)
(fact 'zz-zero-in)
(mac 'comb-kk-zero)
(lam-b)
(let ((ifterm (cadr (dk-goal))))
  (for-each (lambda (s)
              (dk-focus! s)
              (if (eq? (car (dk-goal)) 'IF-PLACEHOLDER) #t #t)
              (if (equal? (car (dk-goal)) '=)
                  (if (equal? (cadr (dk-goal)) ifterm) (ass) (arith))
                  (ass)))
            (dk-opened (lambda () (if-true ifterm)))))
(qed 'comb-kk-0-0)
(topic! 'comb-kk-0-0 'algebra)


;;; =======================================================================
;;; comb-kk-in-fun  --  COMB-KK(R,x,y,m) : ZZ -> CARR(R), total
;;; =======================================================================
(sp (make-wff
      (ckl-tf 'm_ '(IN m_ NN)
        (ckl-tf 'R '(IS-COMMUTATIVE-RING R)
          (ckl-tf 'x '(IN x (CARR R))
            (ckl-tf 'y '(IN y (CARR R))
              '(IN (COMB-KK R x y m_) (FUN ZZ (CARR R)))))))))
(let* ((br (use-induction))
       (iv (cdr (assq 'var br)))
       (ih (cdr (assq 'ih  br)))
       (st (cdr (assq 'step br)))
       (bs (cdr (assq 'base br))))
  ;; ---- base:  k |-> IF k = 0 THEN ONE ELSE ZERO ----
  (dk-focus! bs)
  (dk-peel!)
  (let* ((goal (dk-goal))                    ; (IN (COMB-KK r x y 0) (FUN ZZ (CARR r)))
         (r (cadr (cadr goal))))
    (mac 'comb-kk-zero)
    (dk-lam-t!)
    (dk-peel!)
    (let ((ifterm (cadr (dk-goal))))         ; (IF (= k 0) (ONE r) (ZERO r))
      (fact 'commutative-ring-is-ring r)
      (fact 'bt-one-in-carr r)
      (fact 'ring-zero-in r)
      (for-each
       (lambda (cs)
         (dk-focus! cs)
         (let ((true? (member (cadr ifterm) (dk-asms-of cs))))
           (for-each
            (lambda (s)
              (dk-focus! s)
              (if (memq (car (dk-goal-of s)) '(IN))
                  (begin (subst (list '= ifterm
                                      (if true? (caddr ifterm) (cadddr ifterm))))
                         (ass))
                  (ass)))
            (dk-opened (lambda ()
                         (if true? (if-true ifterm) (if-false ifterm)))))))
       (dk-opened (lambda () (use-em (cadr ifterm)))))))
  ;; ---- step:  k |-> x*g(k-1) + y*g(k) ----
  (dk-focus! st)
  (dk-peel!)
  (let* ((goal (dk-goal))                    ; (IN (COMB-KK r x y (succ m)) (FUN ZZ (CARR r)))
         (r (cadr (cadr goal)))
         (x (caddr (cadr goal)))
         (y (cadddr (cadr goal)))
         (g (list 'COMB-KK r x y iv)))
    (mac 'comb-kk-succ)
    (dk-lam-t!)
    (dk-peel!)
    (let* ((body (cadr (dk-goal)))
           (mul1 (cadr body))
           (mul2 (caddr body))
           (a1   (caddr mul1))               ; g(k-1)
           (a2   (caddr mul2))               ; g(k)
           (kk   (cadr a2)))
      (fact 'commutative-ring-is-ring r)
      (fact 'zz-one-in)
      (fact 'zz-sub-in-zz kk 1)
      (dk-apply! ih r x y)
      (fact 'fun-apply-type-c g 'ZZ (list 'CARR r) (cadr a1))
      (fact 'fun-apply-type-c g 'ZZ (list 'CARR r) kk)
      (fact 'ring-carrier-closed-mul r x a1)
      (fact 'ring-carrier-closed-mul r y a2)
      (fact 'bt-add-in-carr r mul1 mul2)
      (ass))))
(qed 'comb-kk-in-fun-ind)
(topic! 'comb-kk-in-fun-ind 'algebra)

(sp (make-wff
      (ckl-tf 'R '(IS-COMMUTATIVE-RING R)
        (ckl-tf 'x '(IN x (CARR R))
          (ckl-tf 'y '(IN y (CARR R))
            (ckl-tf 'm '(IN m NN)
              '(IN (COMB-KK R x y m) (FUN ZZ (CARR R)))))))))
(dk-peel!)
(let* ((goal (dk-goal))
       (t (cadr goal)))
  (fact 'comb-kk-in-fun-ind (car (cddddr t)) (cadr t) (caddr t) (cadddr t))
  (ass))
(qed 'comb-kk-in-fun)
(topic! 'comb-kk-in-fun 'algebra)


;;; =======================================================================
;;; comb-kk-null / comb-kk-above -- the two vanishing laws
;;;
;;; Both are the SAME induction: the base clause is a conditional whose test
;;; `k = 0' the hypothesis refutes, and the step is `x*g(k-1) + y*g(k)' with
;;; the induction hypothesis applicable at BOTH indices.  The only difference
;;; is the arithmetic that gets k-1 back inside the range.
;;; =======================================================================

;; Read (r x y k) off a goal of the form (= ((COMB-KK r x y m) k) (ZERO r)).
(define (ckl-parts)
  (let* ((app  (cadr (dk-goal)))
         (head (car app)))
    (list (cadr head) (caddr head) (cadddr head) (cadr app))))

;; Close (= IFTERM branch) by if-true / if-false, both leaves by `ass'.
(define (ckl-if-close! ifterm true?)
  (for-each (lambda (s) (dk-focus! s) (ass))
            (dk-opened (lambda ()
                         (if true? (if-true ifterm) (if-false ifterm))))))

;;; ---- comb-kk-null ------------------------------------------------------
(sp (make-wff
      (ckl-tf 'm_ '(IN m_ NN)
        (ckl-tf 'R '(IS-COMMUTATIVE-RING R)
          (ckl-tf 'x '(IN x (CARR R))
            (ckl-tf 'y '(IN y (CARR R))
              (ckl-tf 'k_ '(IN k_ ZZ)
                (list 'IMPLIES '(< k_ 0)
                      (list '= (list (list 'COMB-KK 'R 'x 'y 'm_) 'k_)
                            '(ZERO R))))))))))
(let* ((br (use-induction))
       (iv (cdr (assq 'var br)))
       (ih (cdr (assq 'ih  br)))
       (st (cdr (assq 'step br)))
       (bs (cdr (assq 'base br))))
  ;; ---- base:  k < 0 refutes k = 0 ----
  (dk-focus! bs)
  (dk-peel!)
  (let* ((pp (ckl-parts)) (r (car pp)) (k (cadddr pp)))
    (mac 'comb-kk-zero)
    (lam-b)
    (dk-split! (dk-landed-1 (lambda () (mac-h '< (list '< k 0)))))
    (ckl-if-close! (cadr (dk-goal)) #f))
  ;; ---- step:  both k-1 and k are below the range ----
  (dk-focus! st)
  (dk-peel!)
  (let* ((pp (ckl-parts)) (r (car pp)) (x (cadr pp)) (y (caddr pp)) (k (cadddr pp))
         (k-1 (list '- k 1)))
    (mac 'comb-kk-succ)
    (lam-b)
    (fact 'commutative-ring-is-ring r)
    (fact 'zz-one-in)
    (fact 'zz-sub-in-zz k 1)
    (ckl-zz->rr! k)
    (ckl-zz->rr! k-1)
    (have! (list '< k-1 0) (lambda () (ineq (ckl-idx (list '< k 0)))))
    ;; Instantiate the IH at R,x,y ONCE: `inst*!' errors when a step lands
    ;; nothing, and re-running the same three instantiations lands nothing the
    ;; second time round.  Peel to the k-universal, then apply it twice.
    (let ((ihk (dk-apply! ih r x y)))
      (subst (dk-apply! ihk k-1))
      (subst (dk-apply! ihk k)))
    (crs)))
(qed 'comb-kk-null-ind)
(topic! 'comb-kk-null-ind 'algebra)

(sp (make-wff
      (ckl-tf 'R '(IS-COMMUTATIVE-RING R)
        (ckl-tf 'x '(IN x (CARR R))
          (ckl-tf 'y '(IN y (CARR R))
            (ckl-tf 'm '(IN m NN)
              (ckl-tf 'k '(IN k ZZ)
                (list 'IMPLIES '(< k 0)
                      (list '= (list (list 'COMB-KK 'R 'x 'y 'm) 'k)
                            '(ZERO R))))))))))
(dk-peel!)
(let* ((pp (ckl-parts)) (r (car pp)) (x (cadr pp)) (y (caddr pp)) (k (cadddr pp))
       (m (car (cddddr (car (cadr (dk-goal)))))))
  (fact 'comb-kk-null-ind m r x y k)
  (ass))
(qed 'comb-kk-null)
(topic! 'comb-kk-null 'algebra)

;;; ---- comb-kk-above -----------------------------------------------------
(sp (make-wff
      (ckl-tf 'm_ '(IN m_ NN)
        (ckl-tf 'R '(IS-COMMUTATIVE-RING R)
          (ckl-tf 'x '(IN x (CARR R))
            (ckl-tf 'y '(IN y (CARR R))
              (ckl-tf 'k_ '(IN k_ ZZ)
                (list 'IMPLIES '(< m_ k_)
                      (list '= (list (list 'COMB-KK 'R 'x 'y 'm_) 'k_)
                            '(ZERO R))))))))))
(let* ((br (use-induction))
       (iv (cdr (assq 'var br)))
       (ih (cdr (assq 'ih  br)))
       (st (cdr (assq 'step br)))
       (bs (cdr (assq 'base br))))
  ;; ---- base:  0 < k refutes k = 0 ----
  (dk-focus! bs)
  (dk-peel!)
  (let* ((pp (ckl-parts)) (r (car pp)) (k (cadddr pp)))
    (mac 'comb-kk-zero)
    (lam-b)
    (dk-split! (dk-landed-1 (lambda () (mac-h '< (list '< 0 k)))))
    (fact 'neq-sym 0 k)
    (ckl-if-close! (cadr (dk-goal)) #f))
  ;; ---- step:  succ m < k gives m < k-1 and m < k ----
  (dk-focus! st)
  (dk-peel!)
  (let* ((pp (ckl-parts)) (r (car pp)) (x (cadr pp)) (y (caddr pp)) (k (cadddr pp))
         (k-1 (list '- k 1))
         (sm  (list 'succ iv)))
    (mac 'comb-kk-succ)
    (lam-b)
    (fact 'commutative-ring-is-ring r)
    (fact 'zz-one-in)
    (fact 'zz-sub-in-zz k 1)
    (ckl-zz->rr! k)
    (ckl-zz->rr! k-1)
    (fact 'nn-in-rr iv)
    (have! (list '< (list '+ iv 1) k)
           (lambda ()
             (fact 'nn-succ-plus-one iv)
             (fact 'eq-sym sm (list '+ iv 1))
             (subst (list '= (list '+ iv 1) sm))
             (ass)))
    (have! (list '< iv k-1)
           (lambda () (ineq (ckl-idx (list '< (list '+ iv 1) k)))))
    (have! (list '< iv k)
           (lambda () (ineq (ckl-idx (list '< (list '+ iv 1) k)))))
    (let ((ihk (dk-apply! ih r x y)))
      (subst (dk-apply! ihk k-1))
      (subst (dk-apply! ihk k)))
    (crs)))
(qed 'comb-kk-above-ind)
(topic! 'comb-kk-above-ind 'algebra)

(sp (make-wff
      (ckl-tf 'R '(IS-COMMUTATIVE-RING R)
        (ckl-tf 'x '(IN x (CARR R))
          (ckl-tf 'y '(IN y (CARR R))
            (ckl-tf 'm '(IN m NN)
              (ckl-tf 'k '(IN k ZZ)
                (list 'IMPLIES '(< m k)
                      (list '= (list (list 'COMB-KK 'R 'x 'y 'm) 'k)
                            '(ZERO R))))))))))
(dk-peel!)
(let* ((pp (ckl-parts)) (r (car pp)) (x (cadr pp)) (y (caddr pp)) (k (cadddr pp))
       (m (car (cddddr (car (cadr (dk-goal)))))))
  (fact 'comb-kk-above-ind m r x y k)
  (ass))
(qed 'comb-kk-above)
(topic! 'comb-kk-above 'algebra)

