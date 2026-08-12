;;; clear-pivot-cross -- over a euclidean ring, a matrix P (in MAT(succ p, succ q))
;;; with a nonzero entry is ~-equivalent to a matrix C2 in BORDER block form
;;; [[b,0],[0,C']] with b = C2_{1,1} nonzero.  This is the per-level Smith step:
;;; place a class-minimal pivot at (1,1), clear its row and column, and read the
;;; result off as BORDER(C2_{1,1}, SUBMAT C2) so the recursion can descend on the
;;; (p,q) sub-block.  Assembles the proven bricks:
;;;   class-min-pivot -> B (~P, pivot minimal over the whole ~-class)
;;;   derive cr-pcm(B) from class-min-pivot's conjunct (~P) via mat-equiv-trans
;;;   clear-first-row(B) -> C1 ; classmin-transport(B->C1) ; clear-first-col(C1) -> C2
;;;   MEQ(M,C2) by two mat-equiv-trans ; ROWH(C2) = row1-preserved o C1-row-cleared
;;;   bordered-eq-border(C2).
;;; NOTE: dims are SUCCP/SUCCQ (NOT SP/SQ -- `SP` case-folds to the `sp` command);
;;; matrix var is M (NOT P -- folds to dim p).  fact detaches simple guards but
;;; leaves a cr-pcm(.) forall guard -> discharge it with detach!.
(define (cc-goal) (wff-formula (sequent-node-assertion (proof-state-focus *ps*))))
(define (cc-foc-goal! pred)
  (let ((s (any-pred (lambda (s) (pred (wff-formula (sequent-node-assertion s)))) (proof-leaves))))
    (and s (set-proof-state-focus! *ps* s) s)))
(define (cc-find pred) (let lp ((as (map wff-formula (sequent-node-assumptions (proof-state-focus *ps*)))))
  (cond ((null? as) #f) ((pred (car as)) (car as)) (else (lp (cdr as))))))
(define (H? h) (lambda (g) (and (pair? g) (eq? (car g) h))))
(define (cc-di*) (let lp () (let* ((g (cc-goal)) (h (and (pair? g) (car g))))
                   (when (memq h '(FORALL IMPLIES)) (di) (lp)))))
(define (cr-impl* gs concl) (fold-right (lambda (g acc) (list 'IMPLIES g acc)) concl gs))
(define (cr-fa* vs body) (fold-right (lambda (v acc) (list 'FORALL v acc)) body vs))
(define (meq-4th-is? subj z) (and (pair? z) (eq? (car z) 'MAT-EQUIV) (equal? (list-ref z 4) subj)))
(define (meq-body-of? subj z)   ; FORSOME v (AND (MAT-EQUIV A .. subj v) ...)
  (and (pair? z) (eq? (car z) 'FORSOME)
       (let ((b (caddr z))) (and (pair? b) (eq? (car b) 'AND)
         (let ((me (cadr b))) (meq-4th-is? subj me))))))

(define SUCCP '(succ p))
(define SUCCQ '(succ q))
(define (MEQ X Y) (list 'MAT-EQUIV 'A SUCCP SUCCQ X Y))
;; class-minimal-pivot predicate for subject X over the (succ p, succ q) ~-class.
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
;; coercions: euclidean -> ring; (succ p),(succ q) in NN; 1 in the intervals
(fact 'euclidean-ring-is-integral-domain 'A)
(fact 'integral-domain-is-commutative-ring 'A)
(fact 'commutative-ring-is-ring 'A)
(fact 'one-in-interval 'p) (fact 'one-in-interval 'q)
(fact 'nn-succ-closed 'p) (fact 'nn-succ-closed 'q)

;; --- class-min-pivot -> B (~P, class-minimal pivot) ---
(fact 'class-min-pivot 'A SUCCP SUCCQ 'M)
(define CMP-BODY (cc-find (lambda (z) (and (pair? z) (eq? (car z) 'FORSOME) (eq? (cadr z) 'B)))))
(ai CMP-BODY) (ai 1) (ai 1)
(define MEQMB (cc-find (lambda (z) (meq-4th-is? 'M z))))
(define B (list-ref MEQMB 5))
(define CONJ3 (cc-find (lambda (z) (and (pair? z) (eq? (car z) 'FORALL) (eq? (cadr z) 'C)
               (let ((b (caddr z))) (and (pair? b) (eq? (car b) 'IMPLIES)
                 (equal? (list-ref (cadr b) 4) 'M)))))))

;; --- derive cr-pcm(B): class-min-pivot's conjunct is over ~P; bridge to ~B by trans ---
(cut (pcm B))
(cc-di*)
(define ECIJ (cadr (caddr (cc-goal))))   ; goal (<= _ ((GAUGE A)(ENTRY Cx iix jjx)))
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
(quietly (lambda () (detach! (pcm B))))
(define CFR-BODY (cc-find (lambda (z) (meq-body-of? B z))))
(ai CFR-BODY) (ai 1) (ai 1)
(define C1 (list-ref (cc-find (lambda (z) (meq-4th-is? B z))) 5))

;; --- classmin-transport(B->C1): cr-pcm(C1) ---
(fact 'classmin-transport 'A SUCCP SUCCQ B C1)
(quietly (lambda () (detach! (pcm B))))
(fact 'mat-equiv-cod-is-mat 'A SUCCP SUCCQ B C1)
;; C1_{1,1} nonzero (from C1_11 = B_11 and B_11 /= 0)
(cut (list 'NOT (list '= (list 'ENTRY C1 1 1) '(ZERO A))))
(subst (list '= (list 'ENTRY C1 1 1) (list 'ENTRY B 1 1)))
(ass)

;; --- clear-first-col(C1) -> C2 (col cleared + row 1 preserved) ---
(cc-foc-goal! (H? 'FORSOME))
(fact 'clear-first-col 'A SUCCP SUCCQ C1)
(quietly (lambda () (detach! (pcm C1))))
(define CFC-BODY (cc-find (lambda (z) (meq-body-of? C1 z))))
(ai CFC-BODY) (ai 1) (ai 1) (ai 1)
(define C2 (list-ref (cc-find (lambda (z) (meq-4th-is? C1 z))) 5))

;; --- MEQ(M,C2) via the trans chain M~B~C1~C2 ---
(fact 'mat-equiv-trans 'A SUCCP SUCCQ 'M B C1)
(fact 'mat-equiv-trans 'A SUCCP SUCCQ 'M C1 C2)
;; --- C2 in MAT ; C2_{1,1} nonzero ---
(fact 'mat-equiv-cod-is-mat 'A SUCCP SUCCQ C1 C2)
(cut (list 'NOT (list '= (list 'ENTRY C2 1 1) '(ZERO A))))
(subst (list '= (list 'ENTRY C2 1 1) (list 'ENTRY C1 1 1)))
(subst (list '= (list 'ENTRY C1 1 1) (list 'ENTRY B 1 1)))
(ass)

;; --- ROWH(C2): forall j in [1,succ q], j/=1 => C2_1j = 0 (row1-preserved o C1-row-cleared) ---
(cc-foc-goal! (H? 'FORSOME))
(define ROWPRES (cc-find (lambda (z) (and (pair? z) (eq? (car z) 'FORALL)
   (let ((cc (caddr z))) (and (pair? cc) (eq? (car cc) 'IMPLIES)
     (let ((k (caddr cc))) (and (pair? k) (eq? (car k) '=)
       (equal? (cadr k) (list 'ENTRY C2 1 (cadr z)))))))))))
(define C1ROW (cc-find (lambda (z) (and (pair? z) (eq? (car z) 'FORALL)
   (let ((cc (caddr z))) (and (pair? cc) (eq? (car cc) 'IMPLIES)
     (let ((c2 (caddr cc))) (and (pair? c2) (eq? (car c2) 'IMPLIES)
       (let ((k (caddr c2))) (and (pair? k) (eq? (car k) '=)
         (equal? (cadr k) (list 'ENTRY C1 1 (cadr z))) (equal? (caddr k) '(ZERO A))))))))))))
(define ROWH2 (list 'FORALL 'jr (cr-impl* (list (list 'IN 'jr (list 'INTERVAL 1 SUCCQ)) '(NOT (= jr 1)))
                    (list '= (list 'ENTRY C2 1 'jr) '(ZERO A)))))
(cut ROWH2)
(cc-di*)
(define JE (list-ref (cadr (cc-goal)) 3))
(inst+ ROWPRES JE)
(inst+ C1ROW JE)
(subst (list '= (list 'ENTRY C2 1 JE) (list 'ENTRY C1 1 JE)))
(ass)

;; --- bordered-eq-border(C2): C2 = BORDER(C2_11, SUBMAT C2) ---
(cc-foc-goal! (H? 'FORSOME))
(fact 'bordered-eq-border 'A 'p 'q C2)
(detach! ROWH2)
(define COLH2 (cc-find (lambda (z) (and (pair? z) (eq? (car z) 'FORALL)
   (let ((cc (caddr z))) (and (pair? cc) (eq? (car cc) 'IMPLIES)
     (let ((c2 (caddr cc))) (and (pair? c2) (eq? (car c2) 'IMPLIES)
       (let ((k (caddr c2))) (and (pair? k) (eq? (car k) '=)
         (equal? (cadr k) (list 'ENTRY C2 (cadr z) 1)) (equal? (caddr k) '(ZERO A))))))))))))
(detach! COLH2)

;; --- witness C2, split the conjunction, close each ---
(ew C2)
(di)
(cc-foc-goal! (lambda (g) (meq-4th-is? C2 g))) (ass)
(di)
(cc-foc-goal! (lambda (g) (and (pair? g) (eq? (car g) '=) (equal? (cadr g) C2)))) (ass)
(cc-foc-goal! (H? 'NOT)) (ass)

(qed 'clear-pivot-cross)
(topic! 'clear-pivot-cross 'algebra)
