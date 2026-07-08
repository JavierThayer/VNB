;;; scratchpad/cpc.scm -- clear-pivot-cross (piece 2). PHASE 1 probe:
;;; setup -> class-min-pivot -> B ; derive cr-pcm(B) ; clear-first-row -> C1.
;;; matrix var = M (MIT case-folds P->p, colliding with dim p).
;;; dims named SUCCP/SUCCQ, NOT SP/SQ -- SP case-folds to `sp`, clobbering the
;;; prover's start-proof command (that was the "(succ p) not applicable" at sp).
(set! *vnb-quiet* #t)
(define (cc-goal) (wff-formula (sequent-node-assertion (proof-state-focus *ps*))))
(define (cc-last) (car (reverse (dg-sequent-nodes (proof-state-dg *ps*)))))
(define (cc-foc! n) (set-proof-state-focus! *ps* n))
(define (cc-asms) (map wff-formula (sequent-node-assumptions (proof-state-focus *ps*))))
(define (cc-find pred) (let lp ((as (cc-asms)))
  (cond ((null? as) #f) ((pred (car as)) (car as)) (else (lp (cdr as))))))
(define (cc-foc-goal! pred)
  (let ((s (any-pred (lambda (s) (pred (wff-formula (sequent-node-assertion s)))) (proof-leaves))))
    (and s (set-proof-state-focus! *ps* s) s)))
(define (H? h) (lambda (g) (and (pair? g) (eq? (car g) h))))
(define (cc-di*) (let lp () (let* ((g (cc-goal)) (h (and (pair? g) (car g))))
                   (when (memq h '(FORALL IMPLIES)) (di) (lp)))))
(define (cr-impl* gs concl) (fold-right (lambda (g acc) (list 'IMPLIES g acc)) concl gs))
(define (cr-fa* vs body) (fold-right (lambda (v acc) (list 'FORALL v acc)) body vs))

(define SUCCP '(succ p))
(define SUCCQ '(succ q))
(define (MEQ X Y) (list 'MAT-EQUIV 'A SUCCP SUCCQ X Y))
(define (pcm X)
  (list 'FORALL 'C (list 'IMPLIES (MEQ X 'C)
    (list 'FORALL 'ii (list 'FORALL 'jj
      (list 'IMPLIES (list 'IN 'ii (list 'INTERVAL 1 SUCCP))
        (list 'IMPLIES (list 'IN 'jj (list 'INTERVAL 1 SUCCQ))
          (list 'IMPLIES (list 'NOT (list '= '(ENTRY C ii jj) '(ZERO A)))
            (list '<= (list (list 'GAUGE 'A) (list 'ENTRY X 1 1))
                      (list (list 'GAUGE 'A) (list 'ENTRY 'C 'ii 'jj)))))))))))
(define NONZERO-EXISTS
  (list 'FORSOME 'i0 (list 'FORSOME 'j0
    (list 'AND (list 'IN 'i0 (list 'INTERVAL 1 SUCCP))
      (list 'AND (list 'IN 'j0 (list 'INTERVAL 1 SUCCQ))
        (list 'NOT (list '= '(ENTRY M i0 j0) '(ZERO A))))))))

(sp (make-wff
  (list 'FORALL 'A
    (list 'IMPLIES '(IS-EUCLIDEAN-RING A)
      (cr-fa* '(p q M)
        (cr-impl*
          (list '(IN p NN) '(IN q NN) (list 'IN 'M (list 'MAT SUCCP SUCCQ '(CARR A))) NONZERO-EXISTS)
          (list 'FORSOME 'C2
            (list 'AND (MEQ 'M 'C2)
              (list 'AND
                (list '= 'C2 (list 'BORDER 'A '(ENTRY C2 1 1) '(SUBMAT C2 p q) 'p 'q))
                '(NOT (= (ENTRY C2 1 1) (ZERO A))))))))))))
(cc-di*)
;; coercions
(fact 'euclidean-ring-is-integral-domain 'A)
(fact 'integral-domain-is-commutative-ring 'A)
(fact 'commutative-ring-is-ring 'A)
(fact 'one-in-interval 'p) (fact 'one-in-interval 'q)
(fact 'nn-succ-closed 'p) (fact 'nn-succ-closed 'q)   ; (succ p),(succ q) in NN for clear-first-row/col

;; --- class-min-pivot -> B ---
(fact 'class-min-pivot 'A SUCCP SUCCQ 'M)
(define CMP-BODY (cc-find (lambda (z) (and (pair? z) (eq? (car z) 'FORSOME) (eq? (cadr z) 'B)))))
(ai CMP-BODY) (ai 1) (ai 1)
(define MEQMB (cc-find (lambda (z) (and (pair? z) (eq? (car z) 'MAT-EQUIV) (equal? (list-ref z 4) 'M)))))
(define B (list-ref MEQMB 5))
(define CONJ3 (cc-find (lambda (z) (and (pair? z) (eq? (car z) 'FORALL) (eq? (cadr z) 'C)
               (let ((b (caddr z))) (and (pair? b) (eq? (car b) 'IMPLIES)
                 (equal? (list-ref (cadr b) 4) 'M)))))))

;; --- derive cr-pcm(B) --- (cut leaves focus on the subgoal-to-prove)
(cut (pcm B))
(cc-di*)
(define PG (cc-goal))
(define RHS (caddr PG))
(define ECIJ (cadr RHS))
(define CX (cadr ECIJ)) (define IIX (caddr ECIJ)) (define JJX (cadddr ECIJ))
(fact 'mat-equiv-trans 'A SUCCP SUCCQ 'M B CX)
(inst+ CONJ3 CX)
(define FI (cc-find (lambda (z) (and (pair? z) (eq? (car z) 'FORALL) (eq? (cadr z) 'i)
            (let ((b (caddr z))) (and (pair? b) (eq? (car b) 'FORALL) (eq? (cadr b) 'j)))))))
(inst+ FI IIX)
(define FJ (cc-find (lambda (z) (and (pair? z) (eq? (car z) 'FORALL) (eq? (cadr z) 'j)))))
(inst+ FJ JJX)
(ass)

;; --- clear-first-row(B) -> C1 ---
(cc-foc-goal! (H? 'FORSOME))
(fact 'mat-equiv-cod-is-mat 'A SUCCP SUCCQ 'M B)
(fact 'clear-first-row 'A SUCCP SUCCQ B)
(detach! (pcm B))   ; fact leaves the cr-pcm(B) forall guard; discharge it (it's in ctx)
(define (meq-body-of? subj z)   ; FORSOME v (AND (MAT-EQUIV A .. subj v) ...)
  (and (pair? z) (eq? (car z) 'FORSOME)
       (let ((b (caddr z))) (and (pair? b) (eq? (car b) 'AND)
         (let ((me (cadr b))) (and (pair? me) (eq? (car me) 'MAT-EQUIV) (equal? (list-ref me 4) subj)))))))
(define (meq-4th-is? subj z) (and (pair? z) (eq? (car z) 'MAT-EQUIV) (equal? (list-ref z 4) subj)))
(define CFR-BODY (cc-find (lambda (z) (meq-body-of? B z))))

;; --- exists-elim C1 (row-cleared) from clear-first-row ---
(ai CFR-BODY) (ai 1) (ai 1)
(define C1 (list-ref (cc-find (lambda (z) (meq-4th-is? B z))) 5))
;; ctx now has: MEQ(B,C1), C1_11=B_11, forall j (row1 cleared)
;; --- classmin-transport B->C1 : cr-pcm(C1) ---
(fact 'classmin-transport 'A SUCCP SUCCQ B C1)
(detach! (pcm B))
;; --- C1 in MAT ; C1_11 nonzero (from C1_11=B_11, B_11/=0) ---
(fact 'mat-equiv-cod-is-mat 'A SUCCP SUCCQ B C1)
(cut (list 'NOT (list '= (list 'ENTRY C1 1 1) '(ZERO A))))
(subst (list '= (list 'ENTRY C1 1 1) (list 'ENTRY B 1 1)))
(ass)
;; --- clear-first-col(C1) -> C2 (col cleared + row1 preserved) ---
(cc-foc-goal! (H? 'FORSOME))
(fact 'clear-first-col 'A SUCCP SUCCQ C1)
(detach! (pcm C1))
(define CFC-BODY (cc-find (lambda (z) (meq-body-of? C1 z))))

;; --- exists-elim C2 (col cleared + row1 preserved) ---
(ai CFC-BODY) (ai 1) (ai 1) (ai 1)
(define C2 (list-ref (cc-find (lambda (z) (meq-4th-is? C1 z))) 5))
;; --- MEQ(M,C2) via trans chain ---
(fact 'mat-equiv-trans 'A SUCCP SUCCQ 'M B C1)   ; MEQ(M,C1)
(fact 'mat-equiv-trans 'A SUCCP SUCCQ 'M C1 C2)  ; MEQ(M,C2)
;; --- C2 in MAT ; C2_11 nonzero ---
(fact 'mat-equiv-cod-is-mat 'A SUCCP SUCCQ C1 C2)
(cut (list 'NOT (list '= (list 'ENTRY C2 1 1) '(ZERO A))))
(subst (list '= (list 'ENTRY C2 1 1) (list 'ENTRY C1 1 1)))
(subst (list '= (list 'ENTRY C1 1 1) (list 'ENTRY B 1 1)))
(ass)
;; --- ROWH(C2): forall j in [1,succ q], j/=1 => C2_1j=0  (row1-preserved o C1-cleared) ---
(cc-foc-goal! (H? 'FORSOME))
;; ROWPRES = forall c, IN c [1,succ q] => C2_1c = C1_1c   (conjunct of CFC-BODY)
(define ROWPRES (cc-find (lambda (z) (and (pair? z) (eq? (car z) 'FORALL)
   (let ((cc (caddr z))) (and (pair? cc) (eq? (car cc) 'IMPLIES)
     (let ((k (caddr cc))) (and (pair? k) (eq? (car k) '=)
       (equal? (cadr k) (list 'ENTRY C2 1 (cadr z)))))))))))
;; C1ROW = forall j, IN j [1,succ q] => NOT(j=1) => C1_1j = 0   (conjunct of CFR-BODY)
(define C1ROW (cc-find (lambda (z) (and (pair? z) (eq? (car z) 'FORALL)
   (let ((cc (caddr z))) (and (pair? cc) (eq? (car cc) 'IMPLIES)
     (let ((c2 (caddr cc))) (and (pair? c2) (eq? (car c2) 'IMPLIES)
       (let ((k (caddr c2))) (and (pair? k) (eq? (car k) '=)
         (equal? (cadr k) (list 'ENTRY C1 1 (cadr z))) (equal? (caddr k) '(ZERO A))))))))))))
(define ROWH2 (list 'FORALL 'jr (cr-impl* (list (list 'IN 'jr (list 'INTERVAL 1 SUCCQ)) '(NOT (= jr 1)))
                    (list '= (list 'ENTRY C2 1 'jr) '(ZERO A)))))
(cut ROWH2)
(cc-di*)
(define JE (list-ref (cadr (cc-goal)) 3))    ; goal = (= (ENTRY C2 1 JE) (ZERO A))
(inst+ ROWPRES JE)                            ; C2_1JE = C1_1JE
(inst+ C1ROW JE)                              ; C1_1JE = 0
(subst (list '= (list 'ENTRY C2 1 JE) (list 'ENTRY C1 1 JE)))
(ass)
;; --- bordered-eq-border(C2): C2 = BORDER(C2_11, SUBMAT C2) ---
(cc-foc-goal! (H? 'FORSOME))
(fact 'bordered-eq-border 'A 'p 'q C2)
(detach! ROWH2)
;; COLH(C2) is the col-cleared conjunct already in ctx
(define COLH2 (cc-find (lambda (z) (and (pair? z) (eq? (car z) 'FORALL)
   (let ((cc (caddr z))) (and (pair? cc) (eq? (car cc) 'IMPLIES)
     (let ((c2 (caddr cc))) (and (pair? c2) (eq? (car c2) 'IMPLIES)
       (let ((k (caddr c2))) (and (pair? k) (eq? (car k) '=)
         (equal? (cadr k) (list 'ENTRY C2 (cadr z) 1)) (equal? (caddr k) '(ZERO A))))))))))))
(detach! COLH2)
(define BEQ (cc-find (lambda (z) (and (pair? z) (eq? (car z) '=) (equal? (cadr z) C2)
             (pair? (caddr z)) (eq? (car (caddr z)) 'BORDER)))))
;; --- witness C2, split, close ---
(ew C2)
(di)
(cc-foc-goal! (lambda (g) (meq-4th-is? C2 g))) (ass)
(di)
(cc-foc-goal! (lambda (g) (and (pair? g) (eq? (car g) '=) (equal? (cadr g) C2)))) (ass)
(cc-foc-goal! (lambda (g) (and (pair? g) (eq? (car g) 'NOT)))) (ass)

(call-with-output-file "scratchpad/CPC.txt" (lambda (port)
  (display (list 'B B 'C1 C1) port)(newline port)
  (display (list 'CFR-BODY (and CFR-BODY #t) 'CFC-BODY (and CFC-BODY (expression->string CFC-BODY))) port)(newline port)
  (display (list 'done (proof-done? *ps*) 'open (length (proof-leaves))) port)(newline port)
  (for-each (lambda (s)(display "GOAL: " port)
     (display (expression->string (wff-formula (sequent-node-assertion s))) port)(newline port)
     (when (substring? "forsome([c2]" (expression->string (wff-formula (sequent-node-assertion s))))
       (for-each (lambda (a)
          (let ((w (expression->string (wff-formula a))))
            (when (or (substring? "forsome([q]" w)(substring? "in mat(succ(p), succ(q)" w)
                      (substring? "(gauge(a))(entry(b_626, 1, 1))" w)(substring? "not(entry(b_626, 1, 1)" w))
              (display "   - " port)(display w port)(newline port))))
        (sequent-node-assumptions s))))
   (proof-leaves))))
(display (list 'DONE (proof-done? *ps*) 'leaves (length (proof-leaves))))(newline)
