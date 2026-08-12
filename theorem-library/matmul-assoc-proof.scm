;;; matmul-assoc-proof.scm -- matrix multiplication is associative, via Fubini.
;;;
;;;   IS-RING A, P:MAT(m,n), Q:MAT(n,k), R:MAT(k,l)  |-  (PQ)R = P(QR)
;;;
;;; matrix-entry-extensionality reduces the matrix identity to an entry identity;
;;; both entries are expanded to the SAME canonical double sum
;;;   sum_{c in [1,k]} sum_{j in [1,n]} (P_{row,j} Q_{j,c}) R_{c,col}
;;; by triple-entry-left / triple-entry-right (matmul-entry twice + ring
;;; distribution, warranted in matrix.scm); the two differ only in summation
;;; order, and finsum-fubini interchanges them -- the load-bearing step.
;;;
;;; Index naming: the free entry indices are `row'/`col' (NOT i/j/c), so they do
;;; not collide under case-folding with finsum-fubini's bound i/j or the sum
;;; indices c/j (a captured free `i' would break the fubini match).

(define (ma-pg) (wff-formula (sequent-node-assertion (proof-state-focus *ps*))))
(define (ma-asms) (map wff-formula (sequent-node-assumptions (proof-state-focus *ps*))))
(define (ma-leaves) (filter (lambda (nd)(and (not (sequent-node-grounded? nd))(null? (sequent-node-in-arrows nd)))) (dg-ungrounded-nodes (proof-state-dg *ps*))))
(define (ma-wf vars body) (fold-right (lambda (v b) `(FORALL ,v ,b)) body vars))
(define (ma-wi prems body) (fold-right (lambda (p b) `(IMPLIES ,p ,b)) body prems))
(define (ma-di*) (let lp () (let* ((g (ma-pg))(h (and (pair? g)(car g)))) (when (memq h '(FORALL IMPLIES))(di)(lp)))))
(define (ma-eqasm hd) (car (filter (lambda (f) (and (pair? f) (eq? (car f) '=) (pair? (cadr f)) (eq? (caadr f) hd))) (ma-asms))))
(define (ma-focus! pred) (let lp ((ls (ma-leaves))) (cond ((null? ls)(error "matmul-assoc: no leaf")) ((pred (wff-formula (sequent-node-assertion (car ls))))(set-proof-state-focus! *ps* (car ls))(car ls))(else (lp (cdr ls))))))

(define MA-AG  '(RING-ADDITIVE-AG A))
(define MA-LHS '(MATMUL A (MATMUL A P Q) R))
(define MA-RHS '(MATMUL A P (MATMUL A Q R)))
(define MA-FF  '(VNB-LAMBDA z (CARTESIAN (INTERVAL 1 k) (INTERVAL 1 n)) ((MUL A) ((MUL A) (ENTRY P row (NTH 2 z)) (ENTRY Q (NTH 2 z) (NTH 1 z))) (ENTRY R (NTH 1 z) col))))
(define MA-PREMS '((IN P (MAT m n (CARR A))) (IN Q (MAT n k (CARR A))) (IN R (MAT k l (CARR A)))))

(sp (ma-wf '(A) (ma-wi '((IS-RING A))
      (ma-wf '(m n k l P Q R) (ma-wi MA-PREMS `(= ,MA-LHS ,MA-RHS))))))
(ma-di*)                          ; asms: IS-RING A, IN P/Q/R ; goal = LHS RHS

;; typings of the two triple products (both m-by-l over CARR A)
(fact 'matmul-type 'A 'm 'n 'k 'P 'Q)                  ; PQ : m x k
(fact 'matmul-type 'A 'm 'k 'l '(MATMUL A P Q) 'R)     ; (PQ)R : m x l
(fact 'matmul-type 'A 'n 'k 'l 'Q 'R)                  ; QR : n x l
(fact 'matmul-type 'A 'm 'n 'l 'P '(MATMUL A Q R))     ; P(QR) : m x l

;; the entry identity (cut, proved next; then fed to matrix-entry-extensionality)
(cut (ma-wf '(row) (ma-wi '((IN row (INTERVAL 1 m)))
       (ma-wf '(col) (ma-wi '((IN col (INTERVAL 1 l)))
         `(= (ENTRY ,MA-LHS row col) (ENTRY ,MA-RHS row col)))))))

;; ----- prove the entry identity (cut auto-focuses this subgoal) -----
(ma-di*)                          ; intro row, col
(fact 'triple-entry-left  'A 'm 'n 'k 'l 'P 'Q 'R 'row 'col)
(subst (ma-eqasm 'ENTRY))         ; LHS entry -> canonical double sum (c outer)
(fact 'triple-entry-right 'A 'm 'n 'k 'l 'P 'Q 'R 'row 'col)
(subst (ma-eqasm 'ENTRY))         ; RHS entry -> canonical double sum (j outer)
;; interchange the summation order (finsum-fubini) -- the crux
(fact 'ring-additive-ag-is-abelian-group 'A)
;; the dimensions are untyped in the statement, so interval-card-in-nn's guard
;; comes off the matrices: k is R's row count, n is Q's.
(fact 'mat-rows-in-nn 'k 'l '(CARR A) 'R)
(fact 'mat-rows-in-nn 'n 'k '(CARR A) 'Q)
(fact 'interval-in-set 1 'k)(fact 'interval-card-in-nn 1 'k)
(fact 'interval-in-set 1 'n)(fact 'interval-card-in-nn 1 'n)
(fact 'matmul-assoc-summand-type 'A 'm 'n 'k 'l 'P 'Q 'R 'row 'col)
(fact 'finsum-fubini-c MA-AG '(INTERVAL 1 k) '(INTERVAL 1 n) MA-FF)
(ass)

;; ----- back in the main goal: matrix-entry-extensionality -----
(ma-focus! (lambda (g) (and (pair? g) (eq? (car g) '=) (equal? (cadr g) MA-LHS))))
(fact 'matrix-entry-extensionality 'm 'l '(CARR A) MA-LHS MA-RHS)
(ass)

(qed 'matmul-assoc)
(topic! 'matmul-assoc 'algebra)
