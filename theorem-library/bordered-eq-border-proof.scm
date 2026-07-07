;;; bordered-eq-border -- a matrix C whose first row and first column are cleared
;;; off the pivot IS literally BORDER(C_{1,1}, SUBMAT(C)): C = [[C11,0],[0,C']].
;;; The bridge from "cleared cross" (clear-first-row + clear-first-col) to the
;;; BORDER block form, so the Smith recursion can border a sub-block equivalence
;;; back to the full matrix.  Pure entry proof via matrix-entry-extensionality:
;;; a 2x2 EM on (row=1?)x(col=1?) -- three cleared/pivot cases read off the BORDER
;;; corners, the interior (>=2,>=2) case is SUBMAT_{row-1,col-1} = C_{row,col}.
(define (bm-goal) (wff-formula (sequent-node-assertion (proof-state-focus *ps*))))
(define (bm-di*) (let lp () (let* ((g (bm-goal)) (h (and (pair? g) (car g))))
                   (when (memq h '(FORALL IMPLIES)) (di) (lp)))))
(define (bm-last) (car (reverse (dg-sequent-nodes (proof-state-dg *ps*)))))
(define (bm-foc! n) (set-proof-state-focus! *ps* n))
(define (bm-foc-goal! pred)
  (let ((s (any-pred (lambda (s) (pred (wff-formula (sequent-node-assertion s)))) (proof-leaves))))
    (and s (set-proof-state-focus! *ps* s) s)))
(define (fa* vs body) (fold-right (lambda (v acc) (list 'FORALL v acc)) body vs))
(define (impl* gs concl) (fold-right (lambda (g acc) (list 'IMPLIES g acc)) concl gs))
(define (bm-em P)
  (cut `(OR ,P (NOT ,P)))
  (let ((use-or (bm-last)))
    (pbc) (cut `(NOT ,P))
    (let ((use-notp (bm-last)))
      (di) (cut `(OR ,P (NOT ,P)))
      (let ((u2 (bm-last))) (oi-l) (ass) (bm-foc! u2))
      (ai `(NOT (OR ,P (NOT ,P)))) (bm-foc! use-notp))
    (cut `(OR ,P (NOT ,P)))
    (let ((u3 (bm-last))) (oi-r) (ass) (bm-foc! u3))
    (ai `(NOT (OR ,P (NOT ,P)))) (bm-foc! use-or)))
(define (bm-cases P) (bm-em P) (ai `(OR ,P (NOT ,P))) (bm-last))

(define C11 '(ENTRY C 1 1))
(define SC '(SUBMAT C p q))
(define BC (list 'BORDER 'A C11 SC 'p 'q))
;; the cleared-row / cleared-col hypotheses, kept as literal sexps so we can
;; inst+ them directly (scraping context by bound var mis-grabbed the
;; entry-in-carrier typing lemma's forall ancestor).
(define ROWH (list 'FORALL 'j (impl* (list '(IN j (INTERVAL 1 (succ q))) '(NOT (= j 1)))
                    (list '= '(ENTRY C 1 j) '(ZERO A)))))
(define COLH (list 'FORALL 'i (impl* (list '(IN i (INTERVAL 1 (succ p))) '(NOT (= i 1)))
                    (list '= '(ENTRY C i 1) '(ZERO A)))))

(sp (make-wff (list 'FORALL 'A (list 'IMPLIES '(IS-RING A) (fa* '(p q C)
    (impl* (list '(IN p NN) '(IN q NN) '(IN C (MAT (succ p) (succ q) (CARR A))) ROWH COLH)
      (list '= 'C BC)))))))
(bm-di*)
(fact 'submat-type 'A 'p 'q 'C)
(fact 'one-in-interval 'p) (fact 'one-in-interval 'q)   ; 1 in interval(1,succ p/q) -> C11-in-carr + border-type bare
(fact 'entry-in-carrier '(succ p) '(succ q) '(CARR A) 'C 1 1)
(fact 'border-type 'A C11 SC 'p 'q)

;; reduce C = BORDER(...) to an entrywise identity.
(cut (fa* '(row) (impl* '((IN row (INTERVAL 1 (succ p))))
       (fa* '(col) (impl* '((IN col (INTERVAL 1 (succ q))))
         (list '= (list 'ENTRY 'C 'row 'col) (list 'ENTRY BC 'row 'col)))))))
(bm-di*)
(fact 'interval-elt-in-nn 1 '(succ p) 'row) (fact 'interval-lo 1 '(succ p) 'row)
(fact 'interval-elt-in-nn 1 '(succ q) 'col) (fact 'interval-lo 1 '(succ q) 'col)
(define NEQi1 (bm-cases '(= row 1)))
;; ---- row = 1 ----
(subst '(= row 1))
(define NEQj1a (bm-cases '(= col 1)))
;; row=1,col=1 : the pivot corner
(subst '(= col 1))
(fact 'border-entry-11 'A C11 SC 'p 'q) (subst (list '= (list 'ENTRY BC 1 1) C11)) (rfl)
(bm-foc! NEQj1a)
;; row=1,col/=1 : both 0 (BORDER top border + cleared row)
(fact 'border-entry-1j 'A C11 SC 'p 'q 'col) (subst (list '= (list 'ENTRY BC 1 'col) '(ZERO A)))
(inst+ ROWH 'col) (ass)
;; ---- row /= 1 ----
(bm-foc! NEQi1)
(define NEQj1b (bm-cases '(= col 1)))
;; row/=1,col=1 : both 0 (BORDER left border + cleared col)
(subst '(= col 1))
(fact 'border-entry-i1 'A C11 SC 'p 'q 'row) (subst (list '= (list 'ENTRY BC 'row 1) '(ZERO A)))
(inst+ COLH 'row) (ass)
(bm-foc! NEQj1b)
;; row/=1,col/=1 : block = SUBMAT_{row-1,col-1} = C_{row,col}
(fact 'border-entry-block2 'A C11 SC 'p 'q 'row 'col)
(subst (list '= (list 'ENTRY BC 'row 'col) (list 'ENTRY SC '(NN-MINUS row 1) '(NN-MINUS col 1))))
(fact 'pred-in-interval 'p 'row) (fact 'pred-in-interval 'q 'col)
(fact 'entry-of-submat 'C 'p 'q '(NN-MINUS row 1) '(NN-MINUS col 1))
(subst (list '= (list 'ENTRY SC '(NN-MINUS row 1) '(NN-MINUS col 1))
             (list 'ENTRY 'C '(succ (NN-MINUS row 1)) '(succ (NN-MINUS col 1)))))
(fact 'succ-nn-minus-1 'row) (subst '(= (succ (NN-MINUS row 1)) row))
(fact 'succ-nn-minus-1 'col) (subst '(= (succ (NN-MINUS col 1)) col))
(fact 'entry-in-carrier '(succ p) '(succ q) '(CARR A) 'C 'row 'col)
(rfl)
;; ---- back to main goal: matrix-entry-extensionality ----
(bm-foc-goal! (lambda (g) (and (pair? g) (eq? (car g) '=) (equal? (cadr g) 'C))))
(fact 'matrix-entry-extensionality '(succ p) '(succ q) '(CARR A) 'C BC)
(ass)

(qed 'bordered-eq-border)
(category! 'bordered-eq-border 'algebra)
