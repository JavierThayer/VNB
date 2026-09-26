;;; mat-equiv-proof.scm -- Brick B3 infrastructure: basic laws of ~ (mat-equiv.scm).
;;; invertible-mat-is-mat, identmat-invertible, mat-equiv-refl, mat-equiv-right-mult,
;;; mat-equiv-left-mult, elem-f-invertible.  ~ is reflexive and each elementary swap
;;; (row/col) yields an equivalent matrix.  elem-g-invertible + transitivity + submatrix
;;; are follow-ups.  Defs unfolded by mac/mac-h; identmat-*-identity + Cor 3.6 inverses.

(define (mq-goal) (wff-formula (sequent-node-assertion (proof-state-focus *ps*))))
(define (mq-di*) (let lp () (let* ((g (mq-goal)) (h (and (pair? g) (car g))))
                   (when (memq h '(FORALL IMPLIES)) (di) (lp)))))
(define (mq-last) (car (reverse (dg-sequent-nodes (proof-state-dg *ps*)))))
(define (mq-node! n) (dk-focus! n))
(define (mq-foc! pred)
  (let ((s (any-pred (lambda (s) (pred (wff-formula (sequent-node-assertion s)))) (proof-leaves))))
    (and s (dk-focus! s) s)))
(define (H? h) (lambda (g) (and (pair? g) (eq? (car g) h))))
;; Product guards (SIZE/MAT surgery, 2026-09-16; SPEC.md's shapes).  At the
;; square / one-sided-square dimensions used in this file each guard is a
;; propositional tautology, so `dk-have-prop!' lands it before the citation.
(define (me-mt! m n k)                        ; matmul-type at P:m x n, Q:n x k
  (dk-have-prop! `(IMPLIES (= ,n 0) (OR (= ,m 0) (= ,k 0)))))
(define (me-assoc! m n k l)                   ; matmul-assoc's G1 and G2
  (dk-have-prop! `(IMPLIES (= ,n 0) (OR (= ,m 0) (AND (= ,k 0) (= ,l 0)))))
  (dk-have-prop! `(IMPLIES (= ,k 0) (OR (= ,l 0) (AND (= ,n 0) (= ,m 0))))))

;; invertible-mat-is-mat (projection, non-destructive typing)
(sp (make-wff '(FORALL A (FORALL n (FORALL U (IMPLIES (IS-INVERTIBLE-MAT A n U) (IN U (MAT n n (CARR A)))))))))
(mq-di*) (mac-h 'IS-INVERTIBLE-MAT '(IS-INVERTIBLE-MAT A n U)) (ai 1) (ass)
(qed 'invertible-mat-is-mat)
(topic! 'invertible-mat-is-mat 'algebra)

;; identmat-invertible
;; GUARDED 2026-09-16 on (IN n NN), after the binder.  Unguarded it is FALSE:
;; for n := 3/2, IDENTMAT(A, 3/2) is a tabulation over the empty MAT(3/2, 3/2, ..)
;; and has no value, so it is in no MAT and not invertible.  (identmat-type now
;; carries the same guard.)
(sp (make-wff '(FORALL A (IMPLIES (IS-RING A) (FORALL n (IMPLIES (IN n NN) (IS-INVERTIBLE-MAT A n (IDENTMAT A n))))))))
(mq-di*) (fact 'identmat-type 'A 'n) (fact 'identmat-left-identity 'A 'n 'n '(IDENTMAT A n))
(mac 'IS-INVERTIBLE-MAT) (di) (mq-foc! (H? 'FORSOME)) (ew '(IDENTMAT A n)) (di) (mq-foc! (H? 'AND)) (di) (ass-all)
(qed 'identmat-invertible)
(topic! 'identmat-invertible 'algebra)

;; mat-equiv-refl
(sp (make-wff '(FORALL A (IMPLIES (IS-RING A) (FORALL m (FORALL n (FORALL C
     (IMPLIES (IN C (MAT m n (CARR A))) (MAT-EQUIV A m n C C)))))))))
(mq-di*) (fact 'identmat-left-identity 'A 'm 'n 'C) (fact 'identmat-right-identity 'A 'm 'n 'C)
(fact 'mat-rows-in-nn 'm 'n '(CARR A) 'C) (fact 'mat-cols-in-nn 'm 'n '(CARR A) 'C)
(fact 'identmat-invertible 'A 'm) (fact 'identmat-invertible 'A 'n)
(mac 'MAT-EQUIV) (ew '(IDENTMAT A m)) (di) (mq-foc! (H? 'FORSOME)) (ew '(IDENTMAT A n)) (di)
(mq-foc! (H? '=)) (subst '(= (MATMUL A (IDENTMAT A m) C) C)) (subst '(= (MATMUL A C (IDENTMAT A n)) C)) (rfl) (ass-all)
(qed 'mat-equiv-refl)
(topic! 'mat-equiv-refl 'algebra)

;; mat-equiv-right-mult
(sp (make-wff '(FORALL A (IMPLIES (IS-RING A) (FORALL m (FORALL n (FORALL C (FORALL V
     (IMPLIES (IN C (MAT m n (CARR A))) (IMPLIES (IS-INVERTIBLE-MAT A n V)
       (MAT-EQUIV A m n C (MATMUL A C V))))))))))))
(mq-di*)
(fact 'invertible-mat-is-mat 'A 'n 'V)
(fact 'mat-rows-in-nn 'm 'n '(CARR A) 'C)
(me-mt! 'm 'n 'n)
(fact 'identmat-left-identity 'A 'm 'n 'C) (fact 'identmat-invertible 'A 'm) (fact 'matmul-type 'A 'm 'n 'n 'C 'V)
(mac 'MAT-EQUIV) (ew '(IDENTMAT A m)) (di) (mq-foc! (H? 'FORSOME)) (ew 'V) (di)
(mq-foc! (H? '=)) (subst '(= (MATMUL A (IDENTMAT A m) C) C)) (rfl) (ass-all)
(qed 'mat-equiv-right-mult)
(topic! 'mat-equiv-right-mult 'algebra)

;; mat-equiv-left-mult
(sp (make-wff '(FORALL A (IMPLIES (IS-RING A) (FORALL m (FORALL n (FORALL C (FORALL U
     (IMPLIES (IN C (MAT m n (CARR A))) (IMPLIES (IS-INVERTIBLE-MAT A m U)
       (MAT-EQUIV A m n C (MATMUL A U C))))))))))))
(mq-di*)
(fact 'invertible-mat-is-mat 'A 'm 'U)
(fact 'mat-cols-in-nn 'm 'n '(CARR A) 'C)
(me-mt! 'm 'm 'n)
(fact 'matmul-type 'A 'm 'm 'n 'U 'C)
(fact 'identmat-right-identity 'A 'm 'n '(MATMUL A U C)) (fact 'identmat-invertible 'A 'n)
(mac 'MAT-EQUIV) (ew 'U) (di) (mq-foc! (H? 'FORSOME)) (ew '(IDENTMAT A n)) (di)
(mq-foc! (H? '=)) (subst '(= (MATMUL A (MATMUL A U C) (IDENTMAT A n)) (MATMUL A U C))) (rfl) (ass-all)
(qed 'mat-equiv-left-mult)
(topic! 'mat-equiv-left-mult 'algebra)

;; elem-f-invertible
;; GUARDED 2026-09-16 on (IN n NN), after the binders (elem-f-inverse's shape).
;; Unguarded it is FALSE: INTERVAL(1, 5/2) = {1, 2}, so n := 5/2, k := 1, l := 2
;; meets every premise, while ELEM-F(A, 5/2, 1, 2) is a tabulation over the empty
;; MAT(5/2, 5/2, ..) and has no value.
(sp (make-wff '(FORALL A (IMPLIES (IS-RING A) (FORALL n (FORALL k (FORALL l
     (IMPLIES (IN n NN)
     (IMPLIES (IN k (INTERVAL 1 n)) (IMPLIES (IN l (INTERVAL 1 n)) (IMPLIES (NOT (= k l))
       (IS-INVERTIBLE-MAT A n (ELEM-F A n k l)))))))))))))
(mq-di*)
(fact 'elem-f-type 'A 'n 'k 'l) (fact 'elem-f-type 'A 'n 'l 'k) (fact 'elem-f-inverse 'A 'n 'k 'l)
(cut '(NOT (= l k))) (define fcont (mq-last)) (di) (fact 'eq-sym 'l 'k) (ai '(NOT (= k l))) (mq-node! fcont)
(fact 'elem-f-inverse 'A 'n 'l 'k)
(mac 'IS-INVERTIBLE-MAT) (di) (mq-foc! (H? 'FORSOME)) (ew '(ELEM-F A n l k)) (di) (mq-foc! (H? 'AND)) (di) (ass-all)
(qed 'elem-f-invertible)
(topic! 'elem-f-invertible 'algebra)

;;; --- elem-g-invertible (via the param-congruence trick for -(-r)=r) ---
;; elem-g-param-cong GUARDED 2026-09-16 on (IN n NN), after the binders.
;; Unguarded it is FALSE: `=' is the definedness predicate, and for n := 3/2
;; ELEM-G(A, 3/2, s, k, l) has no value (a tabulation over the empty
;; MAT(3/2, 3/2, ..)), so the equation fails although s in CARR A and r = s hold.
(sp (make-wff (quote (FORALL A (IMPLIES (IS-RING A) (FORALL n (FORALL r (FORALL s (FORALL k (FORALL l (IMPLIES (IN n NN) (IMPLIES (IN s (CARR A)) (IMPLIES (= r s) (= (ELEM-G A n r k l) (ELEM-G A n s k l)))))))))))))))
(mq-di*) (subst '(= r s)) (fact 'elem-g-type 'A 'n 's 'k 'l) (rfl)
 (qed 'elem-g-param-cong)
(topic! 'elem-g-param-cong 'algebra)
;; elem-g-invertible GUARDED 2026-09-16 on (IN n NN), after the binders
;; (elem-g-inverse's shape).  Unguarded it is FALSE: n := 5/2, k := 1, l := 2
;; (INTERVAL(1, 5/2) = {1, 2}), where ELEM-G(A, 5/2, r, 1, 2) has no value.
(sp (make-wff (quote (FORALL A (IMPLIES (IS-RING A) (FORALL n (FORALL r (FORALL k (FORALL l (IMPLIES (IN n NN) (IMPLIES (IN r (CARR A)) (IMPLIES (IN k (INTERVAL 1 n)) (IMPLIES (IN l (INTERVAL 1 n)) (IMPLIES (NOT (= k l)) (IS-INVERTIBLE-MAT A n (ELEM-G A n r k l))))))))))))))))
(mq-di*)
(fact 'ring-neg-in-carr 'A 'r) (fact 'ring-neg-in-carr 'A '((NEG A) r))
(fact 'elem-g-type 'A 'n 'r 'k 'l) (fact 'elem-g-type 'A 'n '((NEG A) r) 'k 'l)
(fact 'elem-g-inverse 'A 'n 'r 'k 'l) (fact 'elem-g-inverse 'A 'n '((NEG A) r) 'k 'l)
(fact 'ring-neg-neg 'A 'r) (fact 'eq-sym '((NEG A) ((NEG A) r)) 'r)
(fact 'elem-g-param-cong 'A 'n 'r '((NEG A) ((NEG A) r)) 'k 'l)
(mac 'IS-INVERTIBLE-MAT) (di) (mq-foc! (H? 'FORSOME)) (ew '(ELEM-G A n ((NEG A) r) k l)) (di) (mq-foc! (H? 'AND)) (di)
(mq-foc! (lambda (g) (and (pair? g) (eq? (car g) '=) (pair? (cadr g)) (eq? (car (cadr g)) 'MATMUL)
                          (let ((ff (caddr (cadr g)))) (and (pair? ff) (eq? (car ff) 'ELEM-G) (pair? (list-ref ff 3)))))))
(subst '(= (ELEM-G A n r k l) (ELEM-G A n ((NEG A) ((NEG A) r)) k l)))
(ass-all)
(qed 'elem-g-invertible)
(topic! 'elem-g-invertible 'algebra)

;;; --- transitivity of ~ (product of invertibles is invertible + matmul-assoc) ---
;; ME-IDMAT: a file-local alias for IDENTMAT.  It was called `ID', which
;; case-folds onto what was then the abelian-group identity accessor `ID'
;; (renamed IDEN).  A top-level Scheme define named after a REGISTERED CONSTANT
;; slips past constant-binder-audit, which only checks WFF binders, not Scheme
;; defines -- the same blind spot that let (define BC ...) clobber the `bc' tactic.
(define ME-IDMAT '(IDENTMAT A n))
(define (mm a b) (list 'MATMUL 'A a b))
(define (mq-asms) (map wff-formula (sequent-node-assumptions (proof-state-focus *ps*))))
(define (mq-find pred) (let lp ((as (mq-asms))) (cond ((null? as) #f)((pred (car as))(car as))(else (lp (cdr as))))))

(sp (make-wff '(FORALL A (IMPLIES (IS-RING A) (FORALL n (FORALL U1 (FORALL U2
     (IMPLIES (IS-INVERTIBLE-MAT A n U1) (IMPLIES (IS-INVERTIBLE-MAT A n U2)
       (IS-INVERTIBLE-MAT A n (MATMUL A U1 U2)))))))))))
(mq-di*)
(fact 'invertible-mat-is-mat 'A 'n 'U1) (fact 'invertible-mat-is-mat 'A 'n 'U2)
(mac-h 'IS-INVERTIBLE-MAT '(IS-INVERTIBLE-MAT A n U1)) (ai 1)(ai 1)(ai 1)(ai 1)
(define eq1 (mq-find (lambda (z)(and (pair? z)(eq?(car z)'=)(pair?(cadr z))(eq?(car(cadr z))'MATMUL)(eq?(caddr(cadr z))'U1)))))
(define V1 (cadddr (cadr eq1)))
(mac-h 'IS-INVERTIBLE-MAT '(IS-INVERTIBLE-MAT A n U2)) (ai 1)(ai 1)(ai 1)(ai 1)
(define eq2 (mq-find (lambda (z)(and (pair? z)(eq?(car z)'=)(pair?(cadr z))(eq?(car(cadr z))'MATMUL)(eq?(caddr(cadr z))'U2)))))
(define V2 (cadddr (cadr eq2)))
;; the four unit equations (reconstructed)
(define U1V1 (list '= (list 'MATMUL 'A 'U1 V1) ME-IDMAT))
(define V1U1 (list '= (list 'MATMUL 'A V1 'U1) ME-IDMAT))
(define U2V2 (list '= (list 'MATMUL 'A 'U2 V2) ME-IDMAT))
(define V2U2 (list '= (list 'MATMUL 'A V2 'U2) ME-IDMAT))
;; typings
(fact 'mat-rows-in-nn 'n 'n '(CARR A) 'U1)
(me-mt! 'n 'n 'n)
(me-assoc! 'n 'n 'n 'n)
(fact 'matmul-type 'A 'n 'n 'n 'U1 'U2)
(fact 'matmul-type 'A 'n 'n 'n V2 V1)
(fact 'identmat-type 'A 'n)
(mac 'IS-INVERTIBLE-MAT) (di) (mq-foc! (H? 'FORSOME)) (ew (list 'MATMUL 'A V2 V1)) (di) (mq-foc! (H? 'AND)) (di)
;; L5 : (U1U2)(V2V1) = I  -- first factor caddr = U1
(mq-foc! (lambda (g)(and (pair? g)(eq?(car g)'=)(pair?(cadr g))(eq?(car(cadr g))'MATMUL)
                         (let ((ff (caddr (cadr g))))(and (pair? ff)(eq?(car ff)'MATMUL)(eq?(caddr ff)'U1))))))
(fact 'matmul-assoc-rev 'A 'n 'n 'n 'n '(MATMUL A U1 U2) V2 V1)
(subst (list '= (list 'MATMUL 'A '(MATMUL A U1 U2)(list 'MATMUL 'A V2 V1))
                (list 'MATMUL 'A (list 'MATMUL 'A '(MATMUL A U1 U2) V2) V1)))
(fact 'matmul-assoc 'A 'n 'n 'n 'n 'U1 'U2 V2)
(subst (list '= (list 'MATMUL 'A '(MATMUL A U1 U2) V2) (list 'MATMUL 'A 'U1 (list 'MATMUL 'A 'U2 V2))))
(subst U2V2)
(fact 'identmat-right-identity 'A 'n 'n 'U1)
(subst '(= (MATMUL A U1 (IDENTMAT A n)) U1))
(subst U1V1)
(rfl)
;; L6 : (V2V1)(U1U2) = I  -- first factor caddr = V2
(mq-foc! (lambda (g)(and (pair? g)(eq?(car g)'=)(pair?(cadr g))(eq?(car(cadr g))'MATMUL)
                         (let ((ff (caddr (cadr g))))(and (pair? ff)(eq?(car ff)'MATMUL)(equal?(caddr ff) V2))))))
(fact 'matmul-assoc-rev 'A 'n 'n 'n 'n (list 'MATMUL 'A V2 V1) 'U1 'U2)
(subst (list '= (list 'MATMUL 'A (list 'MATMUL 'A V2 V1) '(MATMUL A U1 U2))
                (list 'MATMUL 'A (list 'MATMUL 'A (list 'MATMUL 'A V2 V1) 'U1) 'U2)))
(fact 'matmul-assoc 'A 'n 'n 'n 'n V2 V1 'U1)
(subst (list '= (list 'MATMUL 'A (list 'MATMUL 'A V2 V1) 'U1) (list 'MATMUL 'A V2 (list 'MATMUL 'A V1 'U1))))
(subst V1U1)
(fact 'identmat-right-identity 'A 'n 'n V2)
(subst (list '= (list 'MATMUL 'A V2 '(IDENTMAT A n)) V2))
(subst V2U2)
(rfl)
(ass-all)
(qed 'product-of-invertibles-is-invertible)
(topic! 'product-of-invertibles-is-invertible 'algebra)

;; ---- mat-equiv-trans ----
(define (mm a b) (list 'MATMUL 'A a b))
(sp (make-wff '(FORALL A (IMPLIES (IS-RING A) (FORALL m (FORALL n (FORALL C (FORALL D (FORALL E
     (IMPLIES (IN C (MAT m n (CARR A)))
     (IMPLIES (MAT-EQUIV A m n C D) (IMPLIES (MAT-EQUIV A m n D E)
       (MAT-EQUIV A m n C E)))))))))))))
(mq-di*)
(mac-h 'MAT-EQUIV '(MAT-EQUIV A m n C D)) (ai 1)(ai 1)(ai 1)(ai 1)
(define eqD (mq-find (lambda(z)(and (pair? z)(eq?(car z)'=)(eq?(cadr z)'D)))))
(define rhsD (caddr eqD)) (define U1 (caddr (caddr rhsD))) (define V1 (cadddr rhsD))
(mac-h 'MAT-EQUIV '(MAT-EQUIV A m n D E)) (ai 1)(ai 1)(ai 1)(ai 1)
(define eqE (mq-find (lambda(z)(and (pair? z)(eq?(car z)'=)(eq?(cadr z)'E)))))
(define rhsE (caddr eqE)) (define U2 (caddr (caddr rhsE))) (define V2 (cadddr rhsE))
;; typings
(me-mt! 'm 'm 'm) (me-mt! 'n 'n 'n) (me-mt! 'm 'n 'n) (me-mt! 'm 'm 'n)
(me-assoc! 'm 'm 'n 'n) (me-assoc! 'm 'm 'm 'n) (me-assoc! 'm 'n 'n 'n)
(fact 'invertible-mat-is-mat 'A 'm U1) (fact 'invertible-mat-is-mat 'A 'm U2)
(fact 'invertible-mat-is-mat 'A 'n V1) (fact 'invertible-mat-is-mat 'A 'n V2)
(fact 'matmul-type 'A 'm 'm 'm U2 U1)          ; U2U1 : m x m
(fact 'matmul-type 'A 'n 'n 'n V1 V2)          ; V1V2 : n x n
(fact 'matmul-type 'A 'm 'n 'n 'C V1)          ; CV1 : m x n
(fact 'matmul-type 'A 'm 'm 'n (mm U2 U1) 'C)  ; (U2U1)C : m x n
;; invertibility of the composed factors
(fact 'product-of-invertibles-is-invertible 'A 'm U2 U1)
(fact 'product-of-invertibles-is-invertible 'A 'n V1 V2)
(mac 'MAT-EQUIV) (ew (mm U2 U1)) (di) (mq-foc! (H? 'FORSOME)) (ew (mm V1 V2)) (di)
(mq-foc! (H? '=))
;; substitute the two equivalence equations, then reassociate to the target
(subst eqE) (subst eqD)
(fact 'matmul-assoc 'A 'm 'm 'n 'n U1 'C V1)
(subst (list '= (mm (mm U1 'C) V1) (mm U1 (mm 'C V1))))
(fact 'matmul-assoc-rev 'A 'm 'm 'm 'n U2 U1 (mm 'C V1))
(subst (list '= (mm U2 (mm U1 (mm 'C V1))) (mm (mm U2 U1) (mm 'C V1))))
(fact 'matmul-assoc-rev 'A 'm 'm 'n 'n (mm U2 U1) 'C V1)
(subst (list '= (mm (mm U2 U1) (mm 'C V1)) (mm (mm (mm U2 U1) 'C) V1)))
(fact 'matmul-assoc 'A 'm 'n 'n 'n (mm (mm U2 U1) 'C) V1 V2)
(subst (list '= (mm (mm (mm (mm U2 U1) 'C) V1) V2) (mm (mm (mm U2 U1) 'C) (mm V1 V2))))
(rfl)
(ass-all)
(qed 'mat-equiv-trans)
(topic! 'mat-equiv-trans 'algebra)
