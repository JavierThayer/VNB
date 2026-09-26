;;; smith-clear-proof.scm -- Brick B3 (LA Phase B): the DESCENT step of the Smith
;;; reduction.  pivot-clears-col: over a euclidean ring, if P's pivot P_{1,1} is
;;; nonzero and of MINIMAL degree over the whole equivalence class of P
;;; (class-min-pivot supplies such a P), then a single elementary COLUMN op zeroes
;;; any off-pivot row-1 entry (1,j) -- the euclidean remainder is forced to vanish,
;;; because a nonzero remainder would sit in a matrix Q ~ P with degree strictly
;;; below deg(P_{1,1}), contradicting minimality.  The op preserves the pivot and
;;; every other column, so iterating it (clear-first-row) clears the whole row.
;;;
;;;   pivot-col-reduce   -- one op gives (P.G)_{1,j} = r with r=0 or deg r < deg pivot
;;;   class-min hyp       -- deg pivot <= deg(any nonzero entry of any C ~ P)
;;;   elem-g-action       -- (P.G[-q,1,j])_{ic} = P_ic for c/=j  (pivot + cols kept)
;;;   nn-succ-le-antisym  -- succ a <= b => not(b <= a): the degree contradiction
;;; Proof route mirrors pivot-col-reduce; the r/=0 branch closes by contradiction.

(define (cc-goal) (wff-formula (sequent-node-assertion (proof-state-focus *ps*))))
(define (cc-di*) (let lp () (let* ((g (cc-goal)) (h (and (pair? g) (car g))))
                   (when (memq h '(FORALL IMPLIES)) (di) (lp)))))
(define (cc-last) (car (reverse (dg-sequent-nodes (proof-state-dg *ps*)))))
(define (cc-foc! n) (dk-focus! n))
(define (cc-asms) (map wff-formula (sequent-node-assumptions (proof-state-focus *ps*))))
(define (cc-find pred) (let lp ((as (cc-asms)))
  (cond ((null? as) #f) ((pred (car as)) (car as)) (else (lp (cdr as))))))
(define (cc-foc-goal! pred)
  (let ((s (any-pred (lambda (s) (pred (wff-formula (sequent-node-assertion s)))) (proof-leaves))))
    (and s (dk-focus! s) s)))
(define (cc-leaf-asms s) (map wff-formula (sequent-node-assumptions s)))
(define (cc-foc-by-asm! f)
  (let ((s (any-pred (lambda (s) (member f (cc-leaf-asms s))) (proof-leaves))))
    (and s (dk-focus! s) s)))
(define (cc-H? h) (lambda (g) (and (pair? g) (eq? (car g) h))))
;; excluded-middle case split (inline pbc of (OR P (NOT P))); returns (NOT P) node.
(define (cc-em P)
  (cut `(OR ,P (NOT ,P)))
  (let ((use-or (cc-last)))
    (pbc)
    (cut `(NOT ,P))
    (let ((use-notp (cc-last)))
      (di)
      (cut `(OR ,P (NOT ,P)))
      (let ((use-or2 (cc-last))) (oi-l) (ass) (cc-foc! use-or2))
      (ai `(NOT (OR ,P (NOT ,P))))
      (cc-foc! use-notp))
    (cut `(OR ,P (NOT ,P)))
    (let ((use-or3 (cc-last))) (oi-r) (ass) (cc-foc! use-or3))
    (ai `(NOT (OR ,P (NOT ,P))))
    (cc-foc! use-or)))
(define (cc-cases P) (cc-em P) (ai `(OR ,P (NOT ,P))) (cc-last))
(define (cc-impl* gs concl) (fold-right (lambda (g acc) (list 'IMPLIES g acc)) concl gs))
(define (cc-fa* vs body) (fold-right (lambda (v acc) (list 'FORALL v acc)) body vs))

(define CC-CLASSMIN
  '(FORALL C (IMPLIES (MAT-EQUIV A m n P C)
      (FORALL ii (FORALL jj (IMPLIES (IN ii (INTERVAL 1 m)) (IMPLIES (IN jj (INTERVAL 1 n))
        (IMPLIES (NOT (= (ENTRY C ii jj) (ZERO A)))
          (<= ((GAUGE A) (ENTRY P 1 1)) ((GAUGE A) (ENTRY C ii jj)))))))))))
(define CC-CONCL
  (list 'FORSOME 'Q
    (list 'AND '(MAT-EQUIV A m n P Q)
      (list 'AND '(= (ENTRY Q 1 1) (ENTRY P 1 1))
        (list 'AND '(= (ENTRY Q 1 j) (ZERO A))
          (cc-fa* '(ii c)
            (cc-impl* (list '(IN ii (INTERVAL 1 m)) '(IN c (INTERVAL 1 n)) '(NOT (= c j)))
                      '(= (ENTRY Q ii c) (ENTRY P ii c)))))))))
(define CC-STMT
  (list 'FORALL 'A (list 'IMPLIES '(IS-EUCLIDEAN-RING A)
    (cc-fa* '(m n P j)
      (cc-impl* (list '(IN P (MAT m n (CARR A)))
                      '(IN 1 (INTERVAL 1 m))
                      '(IN 1 (INTERVAL 1 n))
                      '(IN j (INTERVAL 1 n))
                      '(NOT (= 1 j))
                      '(NOT (= (ENTRY P 1 1) (ZERO A)))
                      CC-CLASSMIN)
                CC-CONCL)))))

(sp (make-wff CC-STMT))
(cc-di*)
(define CC-MINH (cc-find (lambda (z) (and (pair? z) (eq? (car z) 'FORALL) (eq? (cadr z) 'C)))))

;; coerce to a ring, invoke the proven single-column reduction, decompose
(fact 'euclidean-ring-is-integral-domain 'A)
(fact 'integral-domain-is-commutative-ring 'A)
(fact 'commutative-ring-is-ring 'A)
(fact 'pivot-col-reduce 'A 'm 'n 'P 'j)
(ai 1) (ai 1) (ai 1) (ai 1) (ai 1)
(define CC-DIV (cc-find (lambda (z) (and (pair? z) (eq? (car z) '=) (pair? (cadr z))
             (eq? (car (cadr z)) 'ENTRY) (pair? (cadr (cadr z))) (eq? (car (cadr (cadr z))) 'MATMUL)))))
(define CC-Q    (cadr (cadr CC-DIV)))     ; (MATMUL A P (ELEM-G A n ((NEG A) q) 1 j))
(define CC-R    (caddr CC-DIV))
(define CC-G    (cadddr CC-Q))            ; (ELEM-G A n ((NEG A) q) 1 j)
(define CC-NEGQ (list-ref CC-G 3))        ; ((NEG A) q)
(define CC-QE   (cadr CC-NEGQ))           ; q
(define CC-ORASM (cc-find (cc-H? 'OR)))
(define CC-GR   (list '(GAUGE A) CC-R))
(define CC-GP11 (list '(GAUGE A) '(ENTRY P 1 1)))
(define CC-SUCCLE (list '<= (list 'succ CC-GR) CC-GP11))
(define CC-GLE  (list '<= CC-GP11 CC-GR))
(define CC-Q1j  (list 'ENTRY CC-Q 1 'j))

;; MAT-EQUIV(P, Q) : right-mult by the invertible column op
(fact 'ring-neg-in-carr 'A CC-QE)
(fact 'mat-cols-in-nn 'm 'n '(CARR A) 'P)     ; elem-g-invertible wants n natural (2026-09-16)
(fact 'elem-g-invertible 'A 'n CC-NEGQ 1 'j)
(fact 'mat-equiv-right-mult 'A 'm 'n 'P CC-G)

;; witness Q, split the conjunction
(ew CC-Q) (di)
(cc-foc-goal! (cc-H? 'MAT-EQUIV)) (ass)
(cc-foc-goal! (cc-H? 'AND)) (di)

;; ---- E11: (ENTRY Q 1 1) = (ENTRY P 1 1)  (c=1 /= j: elem-g leaves it alone) ----
(cc-foc-goal! (lambda (g) (and (pair? g) (eq? (car g) '=) (equal? (cadr g) (list 'ENTRY CC-Q 1 1)))))
(fact 'elem-g-action 'A 'm 'n 'P CC-NEGQ 1 'j 1 1)
(define CC-IF11 (list 'IF '(= 1 j)
   (list '(ADD A) '(ENTRY P 1 j) (list '(MUL A) '(ENTRY P 1 1) CC-NEGQ))
   '(ENTRY P 1 1)))
(subst (list '= (list 'ENTRY CC-Q 1 1) CC-IF11))
(if-false CC-IF11) (define CC-K11 (cc-last)) (ass) (cc-foc! CC-K11)
(subst (list '= CC-IF11 '(ENTRY P 1 1)))
(fact 'entry-in-carrier 'm 'n '(CARR A) 'P 1 1)
(rfl)

;; ---- split E1J and COLPRES ----
(cc-foc-goal! (cc-H? 'AND)) (di)

;; ---- E1J: (ENTRY Q 1 j) = (ZERO A)  (the remainder vanishes) ----
(cc-foc-goal! (lambda (g) (and (pair? g) (eq? (car g) '=) (equal? (cadr g) CC-Q1j))))
(define CC-NOTR0 (cc-cases (list '= CC-R '(ZERO A))))
;; r = 0 branch
(subst CC-DIV)
(ass)
;; r /= 0 branch -> contradiction with class-minimality
(cc-foc! CC-NOTR0)
(cut (list 'NOT (list '= CC-Q1j '(ZERO A))))
(define CC-CONTMAIN (cc-last))
(subst CC-DIV) (ass)
(cc-foc! CC-CONTMAIN)
;; extract deg r < deg pivot from the OR (r=0 disjunct is impossible here)
(ai CC-ORASM)
(cc-foc-by-asm! (list '= CC-R '(ZERO A)))
(ai (list 'NOT (list '= CC-R '(ZERO A))))
(cc-foc-by-asm! CC-SUCCLE)
;; class-minimality at C = Q, (1,j) : deg pivot <= deg(Q_{1,j})
(inst+ CC-MINH CC-Q)
(define CC-M2 (cc-find (lambda (z) (and (pair? z) (eq? (car z) 'FORALL) (eq? (cadr z) 'ii)))))
(inst+ CC-M2 1)
(define CC-M3 (cc-find (lambda (z) (and (pair? z) (eq? (car z) 'FORALL) (eq? (cadr z) 'jj)))))
(inst+ CC-M3 'j)
;; degrees live in NN
(fact 'entry-in-carrier 'm 'n '(CARR A) 'P 1 1)
(fact 'gauge-is-degree 'A) (ai 1)
(fact 'fun-apply-type-c '(GAUGE A) '(CARR A) 'NN CC-R)
(fact 'fun-apply-type-c '(GAUGE A) '(CARR A) 'NN '(ENTRY P 1 1))
;; deg pivot <= deg r, by congruence (ENTRY Q 1 j) = r
(fact 'eq-sym CC-Q1j CC-R)
(cut CC-GLE)
(define CC-CONT (cc-last))
(subst (list '= CC-R CC-Q1j))
(ass)
(cc-foc! CC-CONT)
;; succ(deg r) <= deg pivot  AND  deg pivot <= deg r  is absurd
(fact 'nn-succ-le-antisym CC-GR CC-GP11)
(ai (list 'NOT CC-GLE))

;; ---- COLPRES: every column c /= j is preserved ----
(cc-foc-goal! (cc-H? 'FORALL))
(cc-di*)
(define CC-GC (cc-goal))                  ; (= (ENTRY Q ROW COL) (ENTRY P ROW COL))
(define CC-ROW (list-ref (cadr CC-GC) 2))
(define CC-COL (list-ref (cadr CC-GC) 3))
(fact 'elem-g-action 'A 'm 'n 'P CC-NEGQ 1 'j CC-ROW CC-COL)
(define CC-IFIC (list 'IF (list '= CC-COL 'j)
   (list '(ADD A) (list 'ENTRY 'P CC-ROW 'j) (list '(MUL A) (list 'ENTRY 'P CC-ROW 1) CC-NEGQ))
   (list 'ENTRY 'P CC-ROW CC-COL)))
(subst (list '= (list 'ENTRY CC-Q CC-ROW CC-COL) CC-IFIC))
(if-false CC-IFIC) (define CC-KC (cc-last)) (ass) (cc-foc! CC-KC)
(subst (list '= CC-IFIC (list 'ENTRY 'P CC-ROW CC-COL)))
(fact 'entry-in-carrier 'm 'n '(CARR A) 'P CC-ROW CC-COL)
(rfl)

(qed 'pivot-clears-col)
(topic! 'pivot-clears-col 'algebra)
;; categorize the support introduced for this brick (topic! is unavailable
;; in structure-library/mat-equiv.scm, which loads before the PSS layer).
;; class-min-pivot categorizes itself now that it is proven, in
;; theorem-library/class-min-pivot-proof.scm.
(topic! 'nn-succ-le-antisym 'inequalities)
