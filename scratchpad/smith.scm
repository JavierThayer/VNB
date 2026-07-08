;;; scratchpad/smith.scm -- smith-diagonalization: every P in MAT(m,n) over a
;;; euclidean ring is ~ to a diagonal matrix.  ni on the row dim; step clears a
;;; class-min pivot cross (clear-pivot-cross) + IH on the SUBMAT + bordering.
;;; dims: row-ni-var = k ; inner forall n P.  Matrix var P is fine here (no dim p).
(set! *vnb-quiet* #t)
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
(define (cr-impl* gs concl) (fold-right (lambda (g acc) (list 'IMPLIES g acc)) concl gs))
(define (cr-fa* vs body) (fold-right (lambda (v acc) (list 'FORALL v acc)) body vs))
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
;; strip A, IS-EUC down to (FORALL k (IMPLIES (IN k NN) ...))
(let lp () (let* ((g (cc-goal)) (h (and (pair? g) (car g))))
  (when (and (memq h '(FORALL IMPLIES)) (not (and (eq? h 'FORALL) (eq? (cadr g) 'k))))
    (di) (lp))))
(fact 'euclidean-ring-is-integral-domain 'A)
(fact 'integral-domain-is-commutative-ring 'A)
(fact 'commutative-ring-is-ring 'A)
(define (mkg s) (call-with-output-file "scratchpad/MKG.txt" (lambda(p)(display s p))))
(ni) (mkg 1)

;; ===== BASE : INNER(0) =====
(cc-foc-goal! (lambda (g) (and (pair? g) (eq? (car g) 'FORALL) (eq? (cadr g) 'n))))
(mkg 2)
(cc-di*)                                   ; n, P, IN n NN, IN P (MAT 0 n) ; goal FORSOME D
(mkg 3)
(ew 'P) (di) (mkg 4)
(cc-foc-goal! (H? 'MAT-EQUIV)) (fact 'mat-equiv-refl 'A 0 'n 'P) (ass) (mkg 5)
;; IS-DIAGONAL(A,0,n,P): INTERVAL 1 0 empty -> vacuous
(cc-foc-goal! (H? 'IS-DIAGONAL))
(mac 'IS-DIAGONAL) (cc-di*)                 ; strip to goal (= (ENTRY P i j)(ZERO A))
;; ctx: IN i (INTERVAL 1 0), IN j (INTERVAL 1 n), NOT(i=j)
(define BIi (caddr (cadr (cc-goal))))      ; i in goal (= (ENTRY P i j)(ZERO A))
(fact 'interval-lo 1 0 BIi) (fact 'interval-hi 1 0 BIi) (fact 'interval-elt-in-nn 1 0 BIi)
(fact 'nn-not-le-zero-pos BIi)             ; i in NN, 1<=i => NOT(i<=0)
(ai (list 'NOT (list '<= BIi 0)))          ; contradiction with interval-hi's i<=0

;; ===== STEP : INNER(k) => INNER(succ k) =====
(cc-foc-goal! (lambda (g) (and (pair? g) (eq? (car g) 'FORALL) (eq? (cadr g) 'k))))
(cc-di*)                                   ; k, IN k NN, IH, n, P, IN n NN, IN P(MAT succ k n); goal FORSOME D
(define IH (cc-find (lambda (z) (and (pair? z) (eq? (car z) 'FORALL) (eq? (cadr z) 'n)
            (pair? (caddr z)) (eq? (car (caddr z)) 'FORALL)))))
(define NLE1 (cc-cases '(<= 1 n)))
;; --- NOT(1<=n): INTERVAL 1 n empty on j-side ; D=P ---
(cc-foc! NLE1)
(ew 'P) (di)
(cc-foc-goal! (H? 'MAT-EQUIV)) (fact 'mat-equiv-refl 'A '(succ k) 'n 'P) (ass)
(cc-foc-goal! (H? 'IS-DIAGONAL))
(mac 'IS-DIAGONAL) (cc-di*)
(define SBj (cadddr (cadr (cc-goal))))     ; j in (= (ENTRY P i j)(ZERO A))
(fact 'interval-lo 1 'n SBj) (fact 'interval-hi 1 'n SBj)
(fact 'nn-le-trans 1 SBj 'n)                ; 1<=j, j<=n => 1<=n
(ai '(NOT (<= 1 n)))                        ; contradict NOT(1<=n)

;; --- 1<=n branch: n = succ q, then pivot dance ---
(cc-foc-goal! (H? 'FORSOME))
(fact 'nn-pos-is-succ 'n)                    ; FORSOME q, IN q NN AND n=succ q  [n in NN, 1<=n]
(define PSB (cc-find (lambda (z) (and (pair? z) (eq? (car z) 'FORSOME) (eq? (cadr z) 'q)))))
(call-with-output-file "scratchpad/DBGA.txt" (lambda(p)
  (display (list 'PSB (and PSB (expression->string PSB))) p)(newline p)))
(ai PSB) (ai 1)
(define NEQ (cc-find (lambda (z) (and (pair? z) (eq? (car z) '=) (equal? (cadr z) 'n)
             (pair? (caddr z)) (eq? (car (caddr z)) 'succ)))))
(call-with-output-file "scratchpad/DBGB.txt" (lambda(p)
  (display (list 'NEQ (and NEQ (expression->string NEQ))) p)(newline p)))
(define Q (cadr (caddr NEQ)))               ; NEQ = (= n (succ q)) ; q = eigenvar
(define SQN (list 'succ Q))
(fact 'eq-sym 'n SQN)                        ; (= (succ q) n)
(subst (list '= 'n SQN))                     ; goal n -> succ q
;; P typed over (succ k, succ q)
(cut (list 'IN 'P (list 'MAT '(succ k) SQN '(CARR A))))
(subst (list '= SQN 'n)) (ass)
;; nonzero-exists over (succ k, succ q) for clear-pivot-cross
(define NZk (list 'FORSOME 'i0 (list 'FORSOME 'j0
   (list 'AND (list 'IN 'i0 (list 'INTERVAL 1 '(succ k)))
     (list 'AND (list 'IN 'j0 (list 'INTERVAL 1 SQN))
       (list 'NOT (list '= '(ENTRY P i0 j0) '(ZERO A))))))))
(define NNZ (cc-cases NZk))
;; ===== nonzero: clear-pivot-cross + IH + bordering + border-is-diagonal =====
(fact 'clear-pivot-cross 'A 'k Q 'P)
(quietly (lambda () (detach! NZk)))         ; nonzero-exists forsome guard
(define CPC (cc-find (lambda (z) (and (pair? z) (eq? (car z) 'FORSOME) (eq? (cadr z) 'C2)))))
(call-with-output-file "scratchpad/DBGC.txt" (lambda(p)(display (list 'CPC (and CPC (expression->string CPC))) p)))
(ai CPC) (ai 1) (ai 1)
(define C2M (cc-find (lambda (z) (and (pair? z) (eq? (car z) 'MAT-EQUIV) (equal? (list-ref z 4) 'P)))))
(call-with-output-file "scratchpad/DBGD.txt" (lambda(p)(display (list 'C2M (and C2M (expression->string C2M))) p)))
(define C2 (list-ref C2M 5))
(define SUB (list 'SUBMAT C2 'k Q))
(define B11 (list 'ENTRY C2 1 1))
;; C2 in MAT (for submat-type + bordering) + SUBMAT typing
(fact 'mat-equiv-cod-is-mat 'A '(succ k) SQN 'P C2)
(fact 'submat-type 'A 'k Q C2)
;; IH = forall n (forall P (IN n NN => IN P (MAT k n) => forsome-d)).  Match by the
;; distinctive (IN n NN) / (IN Q NN) first-guard (else the finder grabs mat-equiv-cod /
;; submat-type, which also have forall-n / forall-P shapes).
(define IHn (cc-find (lambda (z) (and (pair? z) (eq? (car z) 'FORALL) (eq? (cadr z) 'n)
   (let ((c (caddr z))) (and (pair? c) (eq? (car c) 'FORALL)
     (let ((b (caddr c))) (and (pair? b) (eq? (car b) 'IMPLIES) (equal? (cadr b) '(IN n NN))))))))))
(inst+ IHn Q)
(define IHp (cc-find (lambda (z) (and (pair? z) (eq? (car z) 'FORALL) (eq? (cadr z) 'P)
   (let ((b (caddr z))) (and (pair? b) (eq? (car b) 'IMPLIES) (equal? (cadr b) (list 'IN Q 'NN))))))))
(inst+ IHp SUB)
(define IHBODY (cc-find (lambda (z) (and (pair? z) (eq? (car z) 'FORSOME) (eq? (cadr z) 'D)))))
(ai IHBODY) (ai 1)
(define DPM (cc-find (lambda (z) (and (pair? z) (eq? (car z) 'MAT-EQUIV) (equal? (list-ref z 4) SUB)))))
(call-with-output-file "scratchpad/DBGF.txt" (lambda(p)
  (display (list 'SUB SUB) p)(newline p)
  (display (list 'GOAL (expression->string (cc-goal))) p)(newline p)
  (for-each (lambda(a)(let ((w (wff-formula a)))
    (when (and (pair? w)(or (memq (car w) '(MAT-EQUIV FORSOME IS-DIAGONAL))
                            (and (eq? (car w) 'IN)(pair? (caddr w))(eq? (car (caddr w)) 'MAT))))
      (display "  - " p)(display (expression->string w) p)(newline p))))
   (sequent-node-assumptions (proof-state-focus *ps*)))))
(define DP (list-ref DPM 5))
;; b = C2_11 in CARR A (bordering's IN b guard)
(fact 'one-in-interval 'k) (fact 'one-in-interval Q)
(fact 'entry-in-carrier '(succ k) SQN '(CARR A) C2 1 1)
;; bordering: C2 ~ BORDER(b, D')
(fact 'bordering 'A 'k Q B11 SUB C2 DP)
;; border-is-diagonal: BORDER(b,D') diagonal
(fact 'border-is-diagonal 'A B11 DP 'k Q)
;; MEQ(P, BORDER(b,D')) by trans of MEQ(P,C2), MEQ(C2, BORDER)
(define BRD (list 'BORDER 'A B11 DP 'k Q))
(fact 'mat-equiv-trans 'A '(succ k) SQN 'P C2 BRD)
(call-with-output-file "scratchpad/DBGW.txt" (lambda(p)
  (for-each (lambda(a)(let ((w (expression->string (wff-formula a))))
    (when (or (substring? "border(a" w)(substring? "is-diagonal(a, succ" w))
      (display "  - " p)(display w p)(newline p))))
   (sequent-node-assumptions (proof-state-focus *ps*)))))
;; witness D = BORDER(b,D') (focus already on the nonzero goal), split, close
(ew BRD) (di)
(cc-foc-goal! (lambda (g) (and (pair? g) (eq? (car g) 'MAT-EQUIV) (equal? (list-ref g 4) 'P)))) (ass)
(cc-foc-goal! (H? 'IS-DIAGONAL)) (ass)
;; ===== zero: no nonzero entry => P already diagonal =====
(cc-foc! NNZ)
(ew 'P) (di)
(cc-foc-goal! (H? 'MAT-EQUIV)) (fact 'mat-equiv-refl 'A '(succ k) SQN 'P) (ass)
(cc-foc-goal! (H? 'IS-DIAGONAL))
(mac 'IS-DIAGONAL) (cc-di*)                  ; goal (= P_ij 0); ctx IN i, IN j, NOT(i=j)
(define ZI (caddr (cadr (cc-goal))))
(define ZJ (cadddr (cadr (cc-goal))))
;; (= P_ij 0) by EM: if not, (i,j) witnesses nonzero-exists, contradicting NOT(NZk)
(define PZ (cc-cases (list '= (list 'ENTRY 'P ZI ZJ) '(ZERO A))))
(ass)                                        ; P_ij=0 branch: goal is the hyp
(cc-foc! PZ)                                 ; NOT(P_ij=0) branch
(cut NZk)
(ew ZI) (ew ZJ) (di)                         ; -> IN ZI leaf + AND(IN ZJ, NOT) leaf
(cc-foc-goal! (lambda (g) (and (pair? g) (eq? (car g) 'IN) (equal? (cadr g) ZI)))) (ass)
(cc-foc-goal! (H? 'AND)) (di)                ; split AND(IN ZJ, NOT)
(cc-foc-goal! (lambda (g) (and (pair? g) (eq? (car g) 'IN) (equal? (cadr g) ZJ)))) (ass)
(cc-foc-goal! (H? 'NOT)) (ass)
;; NZk proven; contradict NOT(NZk) to close (= P_ij 0)
(cc-foc-goal! (lambda (g) (equal? g (list '= (list 'ENTRY 'P ZI ZJ) '(ZERO A)))))
(ai (list 'NOT NZk))

(call-with-output-file "scratchpad/SM.txt" (lambda (port)
  (display (list 'done (proof-done? *ps*) 'open (length (proof-leaves))) port)(newline port)
  (for-each (lambda (s)(display "GOAL: " port)
     (display (expression->string (wff-formula (sequent-node-assertion s))) port)(newline port))
   (proof-leaves))))
(display (list 'DONE (proof-done? *ps*) 'leaves (length (proof-leaves))))(newline)
