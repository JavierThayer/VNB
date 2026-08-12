;;; pivot-col-reduce-proof.scm -- Brick B2b (LA Phase B, algebraic-numbers.pdf
;;; ch.3): ONE elementary column operation reduces a first-row entry against the
;;; pivot.  Over a euclidean ring A, for P with nonzero pivot P_{1,1} and target
;;; column j/=1, there are q,r with (P . G[-q,1,j])_{1,j} = r and (r=0 or
;;; deg(r) < deg(P_{1,1})) -- the column op ELEM-G subtracts q.(col 1) from col j.
;;; This is the reduction STEP of the Smith/normal-form induction (Prop 3.36):
;;; it shrinks the (1,j) entry below the pivot degree.  Proof = euclidean-division
;;; (b = q.a + r) + elem-g-action ((P.G)_{1j} = P_1j + P_11.(-q)) + comm-ring
;;; arithmetic (crs closes q.a + r + a.(-q) = r).  Coercions IS-EUCLIDEAN-RING ->
;;; IS-INTEGRAL-DOMAIN -> IS-COMMUTATIVE-RING -> IS-RING give the ring structure.
(define (pc-goal) (wff-formula (sequent-node-assertion (proof-state-focus *ps*))))
(define (pc-di*) (let lp () (let* ((g (pc-goal)) (h (and (pair? g) (car g))))
                   (when (memq h '(FORALL IMPLIES)) (di) (lp)))))
(define (pc-last) (car (reverse (dg-sequent-nodes (proof-state-dg *ps*)))))
(define (pc-foc! n) (set-proof-state-focus! *ps* n))
(define (pc-asms) (map wff-formula (sequent-node-assumptions (proof-state-focus *ps*))))
(define (pc-find pred) (let lp ((as (pc-asms)))
  (cond ((null? as) #f) ((pred (car as)) (car as)) (else (lp (cdr as))))))
(define (pc-foc-goal! pred)
  (let ((s (any-pred (lambda (s) (pred (wff-formula (sequent-node-assertion s)))) (proof-leaves))))
    (and s (set-proof-state-focus! *ps* s) s)))
(sp (make-wff (quote (FORALL A (IMPLIES (IS-EUCLIDEAN-RING A) (FORALL m (FORALL n (FORALL P (FORALL j (IMPLIES (IN P (MAT m n (CARR A))) (IMPLIES (IN 1 (INTERVAL 1 m)) (IMPLIES (IN 1 (INTERVAL 1 n)) (IMPLIES (IN j (INTERVAL 1 n)) (IMPLIES (NOT (= 1 j)) (IMPLIES (NOT (= (ENTRY P 1 1) (ZERO A))) (FORSOME q (AND (IN q (CARR A)) (FORSOME r (AND (IN r (CARR A)) (AND (= (ENTRY (MATMUL A P (ELEM-G A n ((NEG A) q) 1 j)) 1 j) r) (OR (= r (ZERO A)) (<= (succ ((GAUGE A) r)) ((GAUGE A) (ENTRY P 1 1))))))))))))))))))))))))
(pc-di*)
(fact 'euclidean-ring-is-integral-domain 'A)
(fact 'integral-domain-is-commutative-ring 'A)
(fact 'commutative-ring-is-ring 'A)
(fact 'entry-in-carrier 'm 'n '(CARR A) 'P '1 '1)
(fact 'entry-in-carrier 'm 'n '(CARR A) 'P '1 'j)
(fact 'euclidean-division 'A '(ENTRY P 1 j) '(ENTRY P 1 1))
(ai 1) (ai 1) (ai 1) (ai 1) (ai 1)
(define DIV (pc-find (lambda (z) (and (pair? z) (eq? (car z) '=) (equal? (cadr z) '(ENTRY P 1 j))))))
(define Q (cadr (cadr (caddr DIV))))
(define R (caddr (caddr DIV)))
(define NEGQ (list (list 'NEG 'A) Q))
(define P1j '(ENTRY P 1 j))
(define P11 '(ENTRY P 1 1))
(define NEWENT (list 'ENTRY (list 'MATMUL 'A 'P (list 'ELEM-G 'A 'n NEGQ 1 'j)) 1 'j))
(define GRHS (list (list 'ADD 'A) P1j (list (list 'MUL 'A) P11 NEGQ)))
(define GIF (list 'IF '(= j j) GRHS P1j))
(fact 'ring-neg-in-carr 'A Q)
(ew Q)
(di)
(pc-foc-goal! (lambda (g) (and (pair? g) (eq? (car g) 'FORSOME))))
(ew R)
(di)
(pc-foc-goal! (lambda (g) (and (pair? g) (eq? (car g) 'AND))))
(di)
;; close the matmul equation leaf
(pc-foc-goal! (lambda (g) (and (pair? g) (eq? (car g) '=) (pair? (cadr g))
                               (eq? (car (cadr g)) 'ENTRY) (pair? (cadr (cadr g)))
                               (eq? (car (cadr (cadr g))) 'MATMUL))))
(fact 'elem-g-action 'A 'm 'n 'P NEGQ 1 'j 1 'j)
(subst (list '= NEWENT GIF))
(if-true GIF)
(define cont (pc-last)) (rfl) (pc-foc! cont)
(subst (list '= GIF GRHS))
(subst DIV)
(crs)
;; close the trivial leaves
(pc-foc-goal! (lambda (g) (and (pair? g) (eq? (car g) 'IN) (equal? (cadr g) Q)))) (ass)
(pc-foc-goal! (lambda (g) (and (pair? g) (eq? (car g) 'IN) (equal? (cadr g) R)))) (ass)
(pc-foc-goal! (lambda (g) (and (pair? g) (eq? (car g) 'OR)))) (ass)
(qed 'pivot-col-reduce)
(topic! 'pivot-col-reduce 'algebra)
