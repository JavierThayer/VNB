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
(define (ma-focus! pred) (let lp ((ls (ma-leaves))) (cond ((null? ls)(error "matmul-assoc: no leaf")) ((pred (wff-formula (sequent-node-assertion (car ls))))(dk-focus! (car ls))(car ls))(else (lp (cdr ls))))))

(define MA-AG  '(RING-ADDITIVE-AG A))
(define MA-LHS '(MATMUL A (MATMUL A P Q) R))
(define MA-RHS '(MATMUL A P (MATMUL A Q R)))
(define MA-FF  '(VNB-LAMBDA z (CARTESIAN (INTERVAL 1 k) (INTERVAL 1 n)) ((MUL A) ((MUL A) (ENTRY P row (NTH 2 z)) (ENTRY Q (NTH 2 z) (NTH 1 z))) (ENTRY R (NTH 1 z) col))))
(define MA-PREMS '((IN P (MAT m n (CARR A))) (IN Q (MAT n k (CARR A))) (IN R (MAT k l (CARR A)))))

;; GUARDS (2026-09-16, the SIZE/MAT change): G1 and G2 (SPEC.md's shapes)
;; after the three membership premises.  A product reads its column count off
;; SIZE of its RIGHT factor, and SIZE([]) = [0,0].
;;   Counterexample without guards: n = 0, m = k = l = 1.  P = [[]] is 1-by-0,
;;   Q = [] is in MAT(0,1), R is 1-by-1.  PQ is 1-by-0, so (PQ)R is 1-by-1 with
;;   entry the empty sum 0; QR = MATMUL(A,[],R) has no rows, so P(QR) is
;;   1-by-0.  The two sides differ.  G1 excludes it.
;;   NOTE: G1 and G2 are stronger than the equation needs.  With k = 0 both
;;   sides are m-by-0 (every column count is read off a row-less or column-less
;;   factor), hence equal, and likewise when n = 0 and k = 0 or l = 0; the
;;   exact condition is `n = 0 implies (m = 0 or k = 0 or l = 0)'.  G1/G2 are
;;   the shapes the matrix-entry-extensionality route below can use (it needs
;;   both sides typed m-by-l), and the shapes the citers were written against.
;; Proof: the four product typings follow from G1, G2 by prop.  The entry
;; identity is vacuous when m = 0 or l = 0 (the row or column index lies in
;; [1,0]); otherwise G1, G2 give n /= 0 and k /= 0, hence 1 <= n and 1 <= k,
;; and the old route (triple-entry-left/right, Fubini) runs unchanged.
(define MA-G1 '(IMPLIES (= n 0) (OR (= m 0) (AND (= k 0) (= l 0)))))
(define MA-G2 '(IMPLIES (= k 0) (OR (= l 0) (AND (= n 0) (= m 0)))))

(define (ma-have-prop! f) (dk-have-prop! f))


;; iv in [1,v], v in NN, v = 0 in context: close the focus goal (vacuous).
;; (dk-vacuous! moved to driver-kit.scm as dk-vacuous!, 2026-09-16.)

(sp (ma-wf '(A) (ma-wi '((IS-RING A))
      (ma-wf '(m n k l P Q R) (ma-wi (append MA-PREMS (list MA-G1 MA-G2)) `(= ,MA-LHS ,MA-RHS))))))
(ma-di*)                          ; asms: IS-RING A, IN P/Q/R, G1, G2 ; goal = LHS RHS

;; the four product guards, from G1 and G2
(ma-have-prop! '(IMPLIES (= n 0) (OR (= m 0) (= k 0))))    ; PQ
(ma-have-prop! '(IMPLIES (= k 0) (OR (= m 0) (= l 0))))    ; (PQ)R
(ma-have-prop! '(IMPLIES (= k 0) (OR (= n 0) (= l 0))))    ; QR
(ma-have-prop! '(IMPLIES (= n 0) (OR (= m 0) (= l 0))))    ; P(QR)
;; and the two inner non-degeneracies, for the case m /= 0, l /= 0.  Landed
;; HERE, while the context is small: `prop' caps its atom count, and the
;; branch below has far too many.
(define MA-H1 '(IMPLIES (NOT (= m 0)) (IMPLIES (NOT (= l 0)) (NOT (= n 0)))))
(define MA-H2 '(IMPLIES (NOT (= m 0)) (IMPLIES (NOT (= l 0)) (NOT (= k 0)))))
(ma-have-prop! MA-H1)
(ma-have-prop! MA-H2)

;; typings of the two triple products (both m-by-l over CARR A)
(fact 'matmul-type 'A 'm 'n 'k 'P 'Q)                  ; PQ : m x k
(fact 'matmul-type 'A 'm 'k 'l '(MATMUL A P Q) 'R)     ; (PQ)R : m x l
(fact 'matmul-type 'A 'n 'k 'l 'Q 'R)                  ; QR : n x l
(fact 'matmul-type 'A 'm 'n 'l 'P '(MATMUL A Q R))     ; P(QR) : m x l
;; every dimension is a natural
(fact 'mat-rows-in-nn 'm 'n '(CARR A) 'P)
(fact 'mat-rows-in-nn 'n 'k '(CARR A) 'Q)
(fact 'mat-rows-in-nn 'k 'l '(CARR A) 'R)
(fact 'mat-cols-in-nn 'k 'l '(CARR A) 'R)

(define MA-ENTRY-ID
  (ma-wf '(row) (ma-wi '((IN row (INTERVAL 1 m)))
    (ma-wf '(col) (ma-wi '((IN col (INTERVAL 1 l)))
      `(= (ENTRY ,MA-LHS row col) (ENTRY ,MA-RHS row col)))))))

;; the entry identity (cut, proved first; then fed to matrix-entry-extensionality)
(define ma-cut-leaves (dk-opened (lambda () (cut MA-ENTRY-ID))))
(dk-focus! (find-first (lambda (l) (equal? (dk-goal-of l) MA-ENTRY-ID)) ma-cut-leaves))

;; ----- prove the entry identity -----
(ma-di*)                          ; intro row, col
(use-em '(= m 0)
  (lambda () (dk-vacuous! 'row 'm))
  (lambda ()
    (use-em '(= l 0)
      (lambda () (dk-vacuous! 'col 'l))
      (lambda ()
        (detach! MA-H1) (detach! '(IMPLIES (NOT (= l 0)) (NOT (= n 0))))
        (detach! MA-H2) (detach! '(IMPLIES (NOT (= l 0)) (NOT (= k 0))))
        (dk-one-le! 'n)
        (dk-one-le! 'k)
        (fact 'triple-entry-left  'A 'm 'n 'k 'l 'P 'Q 'R 'row 'col)
        (subst (ma-eqasm 'ENTRY))         ; LHS entry -> canonical double sum (c outer)
        (fact 'triple-entry-right 'A 'm 'n 'k 'l 'P 'Q 'R 'row 'col)
        (subst (ma-eqasm 'ENTRY))         ; RHS entry -> canonical double sum (j outer)
        ;; interchange the summation order (finsum-fubini) -- the crux
        (fact 'ring-additive-ag-is-abelian-group 'A)
        (fact 'interval-in-set 1 'k)(fact 'interval-card-in-nn 1 'k)
        (fact 'interval-in-set 1 'n)(fact 'interval-card-in-nn 1 'n)
        (fact 'matmul-assoc-summand-type 'A 'm 'n 'k 'l 'P 'Q 'R 'row 'col)
        (fact 'finsum-fubini-c MA-AG '(INTERVAL 1 k) '(INTERVAL 1 n) MA-FF)
        (ass)))))

;; ----- back in the main goal: matrix-entry-extensionality -----
(ma-focus! (lambda (g) (and (pair? g) (eq? (car g) '=) (equal? (cadr g) MA-LHS))))
(fact 'matrix-entry-extensionality 'm 'l '(CARR A) MA-LHS MA-RHS)
(ass)

(qed 'matmul-assoc)
(topic! 'matmul-assoc 'algebra)
