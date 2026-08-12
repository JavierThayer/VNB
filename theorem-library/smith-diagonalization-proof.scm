;;; smith-diagonalization -- every matrix P in MAT(m,n) over a euclidean ring is
;;; ~-equivalent to a DIAGONAL matrix (Smith normal form, DIAGONALIZATION ONLY --
;;; no divisibility chain).  The capstone of the LA arc.  Induction (ni) on the
;;; row dim k, inner statement INNER(k) = forall n P over MAT(k,n) exists diagonal
;;; D ~ P.  BASE k=0: P is vacuously diagonal (empty row range).  STEP k=succ k:
;;;   - n=0 side (EM on 1<=n): P vacuously diagonal (empty column range);
;;;   - n=succ q, P=0: P already diagonal (any nonzero entry would witness the
;;;     excluded nonzero-exists);
;;;   - n=succ q, P has a nonzero entry: clear-pivot-cross => C2 = BORDER(b, SUBMAT C2)
;;;     with C2 ~ P; IH on the (k,q) sub-block SUBMAT C2 => D' diagonal; bordering
;;;     lifts C2 ~ BORDER(b, D'); border-is-diagonal makes it diagonal; trans P ~ that.
;;; Dims: row-ni-var k, matrix var P (no dim p to collide).  fact detaches simple
;;; guards; a def-predicate / forsome guard (nonzero-exists, IN SUBMAT) needs detach!.
(define (cc-goal) (wff-formula (sequent-node-assertion (proof-state-focus *ps*))))
(define (cc-last) (car (reverse (dg-sequent-nodes (proof-state-dg *ps*)))))
(define (cc-foc! n) (set-proof-state-focus! *ps* n))
(define (cc-find pred) (let lp ((as (map wff-formula (sequent-node-assumptions (proof-state-focus *ps*)))))
  (cond ((null? as) #f) ((pred (car as)) (car as)) (else (lp (cdr as))))))
(define (cc-foc-goal! pred)
  (let ((s (any-pred (lambda (s) (pred (wff-formula (sequent-node-assertion s)))) (proof-leaves))))
    (and s (set-proof-state-focus! *ps* s) s)))
(define (H? h) (lambda (g) (and (pair? g) (eq? (car g) h))))
(define (cc-di*) (let lp () (let* ((g (cc-goal)) (h (and (pair? g) (car g))))
                   (when (memq h '(FORALL IMPLIES)) (di) (lp)))))
(define (cc-em P)
  (cut `(OR ,P (NOT ,P)))
  (let ((use-or (cc-last)))
    (pbc) (cut `(NOT ,P))
    (let ((use-notp (cc-last)))
      (di) (cut `(OR ,P (NOT ,P)))
      (let ((u2 (cc-last))) (oi-l) (ass) (cc-foc! u2))
      (ai `(NOT (OR ,P (NOT ,P)))) (cc-foc! use-notp))
    (cut `(OR ,P (NOT ,P)))
    (let ((u3 (cc-last))) (oi-r) (ass) (cc-foc! u3))
    (ai `(NOT (OR ,P (NOT ,P)))) (cc-foc! use-or)))
(define (cc-cases P) (cc-em P) (ai `(OR ,P (NOT ,P))) (cc-last))

;; INNER(K): forall n P, IN n NN => IN P (MAT K n carr) => exists diagonal D ~ P
(define (INNER K)
  (list 'FORALL 'n (list 'FORALL 'P
    (list 'IMPLIES (list 'IN 'n 'NN)
      (list 'IMPLIES (list 'IN 'P (list 'MAT K 'n '(CARR A)))
        (list 'FORSOME 'D
          (list 'AND (list 'MAT-EQUIV 'A K 'n 'P 'D)
                     (list 'IS-DIAGONAL 'A K 'n 'D))))))))

(sp (make-wff
  (list 'FORALL 'A (list 'IMPLIES '(IS-EUCLIDEAN-RING A)
    (list 'FORALL 'k (list 'IMPLIES '(IN k NN) (INNER 'k)))))))
;; strip A, IS-EUC down to (FORALL k (IMPLIES (IN k NN) ...)), then induct
(let lp () (let* ((g (cc-goal)) (h (and (pair? g) (car g))))
  (when (and (memq h '(FORALL IMPLIES)) (not (and (eq? h 'FORALL) (eq? (cadr g) 'k))))
    (di) (lp))))
(fact 'euclidean-ring-is-integral-domain 'A)
(fact 'integral-domain-is-commutative-ring 'A)
(fact 'commutative-ring-is-ring 'A)
(ni)

;; ===== BASE : INNER(0) -- vacuously diagonal (empty row range) =====
(cc-foc-goal! (lambda (g) (and (pair? g) (eq? (car g) 'FORALL) (eq? (cadr g) 'n))))
(cc-di*)
(ew 'P) (di)
(cc-foc-goal! (H? 'MAT-EQUIV)) (fact 'mat-equiv-refl 'A 0 'n 'P) (ass)
(cc-foc-goal! (H? 'IS-DIAGONAL))
(mac 'IS-DIAGONAL) (cc-di*)                  ; goal (= (ENTRY P i j)(ZERO A)); ctx IN i (INTERVAL 1 0)
(define BIi (caddr (cadr (cc-goal))))
(fact 'interval-lo 1 0 BIi) (fact 'interval-hi 1 0 BIi) (fact 'interval-elt-in-nn 1 0 BIi)
(fact 'nn-not-le-zero-pos BIi)               ; 1<=i => NOT(i<=0), contradicts interval-hi's i<=0
(ai (list 'NOT (list '<= BIi 0)))

;; ===== STEP : INNER(k) => INNER(succ k) =====
(cc-foc-goal! (lambda (g) (and (pair? g) (eq? (car g) 'FORALL) (eq? (cadr g) 'k))))
(cc-di*)                                     ; k, IN k NN, IH, n, P, IN n NN, IN P; goal FORSOME D
(define IH (cc-find (lambda (z) (and (pair? z) (eq? (car z) 'FORALL) (eq? (cadr z) 'n)
            (pair? (caddr z)) (eq? (car (caddr z)) 'FORALL)))))
(define NLE1 (cc-cases '(<= 1 n)))
;; --- NOT(1<=n): empty column range on the j side ; D=P ---
(cc-foc! NLE1)
(ew 'P) (di)
(cc-foc-goal! (H? 'MAT-EQUIV)) (fact 'mat-equiv-refl 'A '(succ k) 'n 'P) (ass)
(cc-foc-goal! (H? 'IS-DIAGONAL))
(mac 'IS-DIAGONAL) (cc-di*)
(define SBj (cadddr (cadr (cc-goal))))
(fact 'interval-lo 1 'n SBj) (fact 'interval-hi 1 'n SBj)
(fact 'nn-one-in) (fact 'interval-elt-in-nn 1 'n SBj)
(fact 'nn-le-trans-guarded 1 SBj 'n)                 ; 1<=j, j<=n => 1<=n, contradicts NOT(1<=n)
(ai '(NOT (<= 1 n)))

;; --- 1<=n branch: n = succ q, then the pivot dance ---
(cc-foc-goal! (H? 'FORSOME))
(fact 'nn-pos-is-succ 'n)                     ; FORSOME q, IN q NN AND n=succ q
(define PSB (cc-find (lambda (z) (and (pair? z) (eq? (car z) 'FORSOME) (eq? (cadr z) 'q)))))
(ai PSB) (ai 1)
(define NEQ (cc-find (lambda (z) (and (pair? z) (eq? (car z) '=) (equal? (cadr z) 'n)
             (pair? (caddr z)) (eq? (car (caddr z)) 'succ)))))
(define Q (cadr (caddr NEQ)))                 ; NEQ = (= n (succ q))
(define SQN (list 'succ Q))
(fact 'eq-sym 'n SQN)                         ; (= (succ q) n)
(subst (list '= 'n SQN))                      ; goal n -> succ q
(cut (list 'IN 'P (list 'MAT '(succ k) SQN '(CARR A))))
(subst (list '= SQN 'n)) (ass)
(define NZk (list 'FORSOME 'i0 (list 'FORSOME 'j0
   (list 'AND (list 'IN 'i0 (list 'INTERVAL 1 '(succ k)))
     (list 'AND (list 'IN 'j0 (list 'INTERVAL 1 SQN))
       (list 'NOT (list '= '(ENTRY P i0 j0) '(ZERO A))))))))
(define NNZ (cc-cases NZk))

;; ===== nonzero: clear-pivot-cross + IH(sub-block) + bordering + border-is-diagonal =====
(fact 'clear-pivot-cross 'A 'k Q 'P)
(quietly (lambda () (detach! NZk)))
(define CPC (cc-find (lambda (z) (and (pair? z) (eq? (car z) 'FORSOME) (eq? (cadr z) 'C2)))))
(ai CPC) (ai 1) (ai 1)
(define C2 (list-ref (cc-find (lambda (z) (and (pair? z) (eq? (car z) 'MAT-EQUIV) (equal? (list-ref z 4) 'P)))) 5))
(define SUB (list 'SUBMAT C2 'k Q))
(define B11 (list 'ENTRY C2 1 1))
(fact 'mat-equiv-cod-is-mat 'A '(succ k) SQN 'P C2)
(fact 'submat-type 'A 'k Q C2)
;; IH = forall n (forall P (IN n NN => IN P (MAT k n) => forsome-d)); match on the
;; (IN n NN)/(IN Q NN) first-guard (else the finder grabs mat-equiv-cod / submat-type).
(define IHn (cc-find (lambda (z) (and (pair? z) (eq? (car z) 'FORALL) (eq? (cadr z) 'n)
   (let ((c (caddr z))) (and (pair? c) (eq? (car c) 'FORALL)
     (let ((b (caddr c))) (and (pair? b) (eq? (car b) 'IMPLIES) (equal? (cadr b) '(IN n NN))))))))))
(inst+ IHn Q)
(define IHp (cc-find (lambda (z) (and (pair? z) (eq? (car z) 'FORALL) (eq? (cadr z) 'P)
   (let ((b (caddr z))) (and (pair? b) (eq? (car b) 'IMPLIES) (equal? (cadr b) (list 'IN Q 'NN))))))))
(inst+ IHp SUB)
(define IHBODY (cc-find (lambda (z) (and (pair? z) (eq? (car z) 'FORSOME) (eq? (cadr z) 'D)))))
(ai IHBODY) (ai 1)
(define DP (list-ref (cc-find (lambda (z) (and (pair? z) (eq? (car z) 'MAT-EQUIV) (equal? (list-ref z 4) SUB)))) 5))
;; b = C2_11 in CARR A (bordering's IN b guard)
(fact 'one-in-interval 'k) (fact 'one-in-interval Q)
(fact 'entry-in-carrier '(succ k) SQN '(CARR A) C2 1 1)
(fact 'bordering 'A 'k Q B11 SUB C2 DP)       ; C2 ~ BORDER(b, D')
(fact 'border-is-diagonal 'A B11 DP 'k Q)     ; BORDER(b, D') diagonal
(define BRD (list 'BORDER 'A B11 DP 'k Q))
(fact 'mat-equiv-trans 'A '(succ k) SQN 'P C2 BRD)   ; P ~ BORDER(b, D')
(ew BRD) (di)
(cc-foc-goal! (lambda (g) (and (pair? g) (eq? (car g) 'MAT-EQUIV) (equal? (list-ref g 4) 'P)))) (ass)
(cc-foc-goal! (H? 'IS-DIAGONAL)) (ass)

;; ===== zero: no nonzero entry => P already diagonal =====
(cc-foc! NNZ)
(ew 'P) (di)
(cc-foc-goal! (H? 'MAT-EQUIV)) (fact 'mat-equiv-refl 'A '(succ k) SQN 'P) (ass)
(cc-foc-goal! (H? 'IS-DIAGONAL))
(mac 'IS-DIAGONAL) (cc-di*)                   ; goal (= P_ij 0)
(define ZI (caddr (cadr (cc-goal))))
(define ZJ (cadddr (cadr (cc-goal))))
(define PZ (cc-cases (list '= (list 'ENTRY 'P ZI ZJ) '(ZERO A))))
(ass)                                         ; P_ij=0 branch: goal is the hyp
(cc-foc! PZ)                                  ; NOT(P_ij=0) branch: (i,j) witnesses NZk
(cut NZk)
(ew ZI) (ew ZJ) (di)
(cc-foc-goal! (lambda (g) (and (pair? g) (eq? (car g) 'IN) (equal? (cadr g) ZI)))) (ass)
(cc-foc-goal! (H? 'AND)) (di)
(cc-foc-goal! (lambda (g) (and (pair? g) (eq? (car g) 'IN) (equal? (cadr g) ZJ)))) (ass)
(cc-foc-goal! (H? 'NOT)) (ass)
(cc-foc-goal! (lambda (g) (equal? g (list '= (list 'ENTRY 'P ZI ZJ) '(ZERO A)))))
(ai (list 'NOT NZk))                          ; NZk + NOT(NZk) contradiction

(qed 'smith-diagonalization)
(topic! 'smith-diagonalization 'algebra)
