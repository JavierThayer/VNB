;;; triple-entry-proof.scm -- the two matrix-product entry-expansion lemmas that
;;; matmul-assoc rests on, PROVEN (were warranted in matrix.scm) from the (B)
;;; finite-sum bricks (finsum-additive.scm): finsum-congruence, and general-ring
;;; distribution of a scalar into a finite sum (finsum-ring-distrib-left/right-gen).
;;;
;;;   triple-entry-left:  ((PQ)R)_{row,col} = sum_c sum_j (P_{row,j} Q_{j,c}) R_{c,col}
;;;   triple-entry-right: (P(QR))_{row,col} = sum_j sum_c (P_{row,j} Q_{j,c}) R_{c,col}
;;;
;;; Both reduce, via matrix-entry-extensionality downstream, to the SAME canonical
;;; double sum (the summand written in the fubini-tupled FF(LIST c j) form), so
;;; finsum-fubini interchanges them in matmul-assoc-proof.
;;;
;;; Method (per side): matmul-entry expands the outer product; finsum-congruence
;;; rewrites the outer summand pointwise (its premise expands the inner product by
;;; matmul-entry again, distributes the outer factor into the inner sum with
;;; distrib-right-gen [left side] / distrib-left-gen + ring-mul-assoc [right side],
;;; and a second congruence beta/nth-reduces the FF-tupled summand).  The nested
;;; cuts are driven by leaf-OBJECT capture (with-cut) -- never by re-finding a
;;; leaf by its goal formula, which collides and scatters.  The lambda FUN-typings
;;; are warranted (well-known: entries lie in CARR A and MUL closes).

;; ---- proof-driver helpers (te- prefix) ----
(define (te-pg)(wff-formula (sequent-node-assertion (proof-state-focus *ps*))))
(define (te-asms)(map wff-formula (sequent-node-assumptions (proof-state-focus *ps*))))
(define (te-wf v b)(fold-right (lambda(x y)`(FORALL ,x ,y)) b v))
(define (te-wi p b)(fold-right (lambda(x y)`(IMPLIES ,x ,y)) b p))
(define (te-di*)(let lp()(let*((g(te-pg))(h(and(pair? g)(car g))))(when(memq h '(FORALL IMPLIES))(di)(lp)))))
(define (te-leaves)(filter (lambda(nd)(and(not(sequent-node-grounded? nd))(null?(sequent-node-in-arrows nd))))(dg-ungrounded-nodes(proof-state-dg *ps*))))
(define (te-goalof l)(wff-formula(sequent-node-assertion l)))
(define (te-lastvar cls)(let lp((a(te-asms)))(cond((null? a)#f)((and(pair?(car a))(eq?(caar a)'IN)(equal?(caddr(car a)) cls))(cadr(car a)))(else(lp(cdr a))))))
;; cut P, prove the P-subgoal and the continuation, each focused by its CAPTURED
;; LEAF OBJECT (set-difference on node identity) -- not re-found by formula.
(define (te-with-cut P prove-sub prove-cont)
  (let ((before (te-leaves)))
    (cut P)
    (let* ((new  (filter (lambda(l)(not(memq l before)))(te-leaves)))
           (sub  (car(filter (lambda(l)(equal?(te-goalof l) P)) new)))
           (cont (car(filter (lambda(l)(not(eq? l sub))) new))))
      (set-proof-state-focus! *ps* sub)  (prove-sub)
      (set-proof-state-focus! *ps* cont) (prove-cont))))

(define TE-RAG '(RING-ADDITIVE-AG A))
(define TE-FF '(VNB-LAMBDA z (CARTESIAN (INTERVAL 1 k) (INTERVAL 1 n)) ((MUL A) ((MUL A) (ENTRY P row (NTH 2 z)) (ENTRY Q (NTH 2 z) (NTH 1 z))) (ENTRY R (NTH 1 z) col))))
(define TE-PREMS '((IN P (MAT m n (CARR A))) (IN Q (MAT n k (CARR A))) (IN R (MAT k l (CARR A))) (IN row (INTERVAL 1 m)) (IN col (INTERVAL 1 l))))
;; warranted lambda FUN-typing brick, explicit interval upper bound
(define (te-typ name lam carr bound ev ep)
  (support name (te-wf '(A)(te-wi '((IS-RING A))(te-wf (append '(m n k l P Q R row col) ev)(te-wi (append TE-PREMS ep)`(IN ,lam (FUN (INTERVAL 1 ,bound) ,carr)))))))
  (warrant! name 'well-known "the summand lambda is a function into CARR A / the additive AG's carrier (entry-in-carrier + MUL closure)."))

;; =====================================================================
;; triple-entry-left : ((PQ)R)_{row,col} = sum_{c in [1,k]} sum_{j in [1,n]} FF(c,j)
;; =====================================================================
(define TEL-LHSM '(MATMUL A (MATMUL A P Q) R))
(define TEL-OUTF '(VNB-LAMBDA j (INTERVAL 1 k) ((MUL A) (ENTRY (MATMUL A P Q) row j) (ENTRY R j col))))
(define TEL-TOUT `(VNB-LAMBDA c (INTERVAL 1 k) (FINSUM ,TE-RAG (VNB-LAMBDA j (INTERVAL 1 n) (,TE-FF (LIST c j))) (INTERVAL 1 n))))
(define TEL-TSUM `(FINSUM ,TE-RAG ,TEL-TOUT (INTERVAL 1 k)))
(te-typ 'tel-outf-type TEL-OUTF `(CARR ,TE-RAG) 'k '() '())
(te-typ 'tel-tout-type TEL-TOUT `(CARR ,TE-RAG) 'k '() '())
(te-typ 'tel-inf-type '(VNB-LAMBDA j (INTERVAL 1 n) ((MUL A) (ENTRY P row j) (ENTRY Q j x))) '(CARR A) 'n '(x) '((IN x (INTERVAL 1 k))))
(te-typ 'tel-dist-type '(VNB-LAMBDA z (INTERVAL 1 n) ((MUL A) ((VNB-LAMBDA j (INTERVAL 1 n) ((MUL A) (ENTRY P row j) (ENTRY Q j x))) z) (ENTRY R x col))) `(CARR ,TE-RAG) 'n '(x) '((IN x (INTERVAL 1 k))))
(te-typ 'tel-red-type '(VNB-LAMBDA j (INTERVAL 1 n) ((MUL A) ((MUL A) (ENTRY P row j) (ENTRY Q j x)) (ENTRY R x col))) `(CARR ,TE-RAG) 'n '(x) '((IN x (INTERVAL 1 k))))

(sp (te-wf '(A)(te-wi '((IS-RING A))(te-wf '(m n k l P Q R row col)(te-wi TE-PREMS `(= (ENTRY ,TEL-LHSM row col) ,TEL-TSUM))))))
(te-di*)
(fact 'matmul-type 'A 'm 'n 'k 'P 'Q)
(fact 'matmul-entry 'A 'm 'k 'l '(MATMUL A P Q) 'R 'row 'col)
(subst `(= (ENTRY ,TEL-LHSM row col) (FINSUM ,TE-RAG ,TEL-OUTF (INTERVAL 1 k))))
(fact 'ring-additive-ag-is-abelian-group 'A)
(fact 'interval-in-set 1 'k)(fact 'interval-card-in-nn 1 'k)
(fact 'tel-outf-type 'A 'm 'n 'k 'l 'P 'Q 'R 'row 'col)
(fact 'tel-tout-type 'A 'm 'n 'k 'l 'P 'Q 'R 'row 'col)
(te-with-cut `(FORALL x (IMPLIES (IN x (INTERVAL 1 k)) (= (,TEL-OUTF x) (,TEL-TOUT x))))
  (lambda ()
    (di)(di)
    (let ((xv (te-lastvar '(INTERVAL 1 k))))
      (lam-b)(nth-r)
      (fact 'matmul-entry 'A 'm 'n 'k 'P 'Q 'row xv)
      (subst `(= (ENTRY (MATMUL A P Q) row ,xv) (FINSUM ,TE-RAG (VNB-LAMBDA j (INTERVAL 1 n) ((MUL A) (ENTRY P row j) (ENTRY Q j ,xv))) (INTERVAL 1 n))))
      (fact 'interval-in-set 1 'n)(fact 'interval-card-in-nn 1 'n)
      (fact 'tel-inf-type 'A 'm 'n 'k 'l 'P 'Q 'R 'row 'col xv)
      (fact 'entry-in-carrier 'k 'l '(CARR A) 'R xv 'col)
      (fact 'finsum-ring-distrib-right-gen 'A `(ENTRY R ,xv col) '(INTERVAL 1 n) `(VNB-LAMBDA j (INTERVAL 1 n) ((MUL A) (ENTRY P row j) (ENTRY Q j ,xv))))
      (subst `(= ((MUL A) (FINSUM ,TE-RAG (VNB-LAMBDA j (INTERVAL 1 n) ((MUL A) (ENTRY P row j) (ENTRY Q j ,xv))) (INTERVAL 1 n)) (ENTRY R ,xv col))
                 (FINSUM ,TE-RAG (VNB-LAMBDA z (INTERVAL 1 n) ((MUL A) ((VNB-LAMBDA j (INTERVAL 1 n) ((MUL A) (ENTRY P row j) (ENTRY Q j ,xv))) z) (ENTRY R ,xv col))) (INTERVAL 1 n))))
      (fact 'tel-dist-type 'A 'm 'n 'k 'l 'P 'Q 'R 'row 'col xv)
      (fact 'tel-red-type 'A 'm 'n 'k 'l 'P 'Q 'R 'row 'col xv)
      (let ((DISTxv `(VNB-LAMBDA z (INTERVAL 1 n) ((MUL A) ((VNB-LAMBDA j (INTERVAL 1 n) ((MUL A) (ENTRY P row j) (ENTRY Q j ,xv))) z) (ENTRY R ,xv col))))
            (REDxv  `(VNB-LAMBDA j (INTERVAL 1 n) ((MUL A) ((MUL A) (ENTRY P row j) (ENTRY Q j ,xv)) (ENTRY R ,xv col)))))
        (te-with-cut `(FORALL w (IMPLIES (IN w (INTERVAL 1 n)) (= (,DISTxv w) (,REDxv w))))
          (lambda ()
            (di)(di)
            (let ((wv (te-lastvar '(INTERVAL 1 n))))
              (lam-b)
              (fact 'entry-in-carrier 'm 'n '(CARR A) 'P 'row wv)
              (fact 'entry-in-carrier 'n 'k '(CARR A) 'Q wv xv)
              (fact 'ring-carrier-closed-mul 'A `(ENTRY P row ,wv) `(ENTRY Q ,wv ,xv))
              (fact 'entry-in-carrier 'k 'l '(CARR A) 'R xv 'col)
              (fact 'ring-carrier-closed-mul 'A `((MUL A) (ENTRY P row ,wv) (ENTRY Q ,wv ,xv)) `(ENTRY R ,xv col))
              (rfl)))
          (lambda ()
            (fact 'finsum-congruence TE-RAG '(INTERVAL 1 n) DISTxv REDxv)
            (ass))))))
  (lambda ()
    (fact 'finsum-congruence TE-RAG '(INTERVAL 1 k) TEL-OUTF TEL-TOUT)
    (ass)))
(qed 'triple-entry-left)
(category! 'triple-entry-left 'algebra)

;; =====================================================================
;; triple-entry-right : (P(QR))_{row,col} = sum_{j in [1,n]} sum_{c in [1,k]} FF(c,j)
;; =====================================================================
(define TER-LHSM '(MATMUL A P (MATMUL A Q R)))
(define TER-OUTF '(VNB-LAMBDA j (INTERVAL 1 n) ((MUL A) (ENTRY P row j) (ENTRY (MATMUL A Q R) j col))))
(define TER-TOUT `(VNB-LAMBDA j (INTERVAL 1 n) (FINSUM ,TE-RAG (VNB-LAMBDA c (INTERVAL 1 k) (,TE-FF (LIST c j))) (INTERVAL 1 k))))
(define TER-TSUM `(FINSUM ,TE-RAG ,TER-TOUT (INTERVAL 1 n)))
(te-typ 'ter-outf-type TER-OUTF `(CARR ,TE-RAG) 'n '() '())
(te-typ 'ter-tout-type TER-TOUT `(CARR ,TE-RAG) 'n '() '())
(te-typ 'ter-gj-type '(VNB-LAMBDA j (INTERVAL 1 k) ((MUL A) (ENTRY Q x j) (ENTRY R j col))) '(CARR A) 'k '(x) '((IN x (INTERVAL 1 n))))
(te-typ 'ter-dist-type '(VNB-LAMBDA z (INTERVAL 1 k) ((MUL A) (ENTRY P row x) ((VNB-LAMBDA j (INTERVAL 1 k) ((MUL A) (ENTRY Q x j) (ENTRY R j col))) z))) `(CARR ,TE-RAG) 'k '(x) '((IN x (INTERVAL 1 n))))
(te-typ 'ter-red-type '(VNB-LAMBDA c (INTERVAL 1 k) ((MUL A) ((MUL A) (ENTRY P row x) (ENTRY Q x c)) (ENTRY R c col))) `(CARR ,TE-RAG) 'k '(x) '((IN x (INTERVAL 1 n))))

(sp (te-wf '(A)(te-wi '((IS-RING A))(te-wf '(m n k l P Q R row col)(te-wi TE-PREMS `(= (ENTRY ,TER-LHSM row col) ,TER-TSUM))))))
(te-di*)
(fact 'matmul-type 'A 'n 'k 'l 'Q 'R)
(fact 'matmul-entry 'A 'm 'n 'l 'P '(MATMUL A Q R) 'row 'col)
(subst `(= (ENTRY ,TER-LHSM row col) (FINSUM ,TE-RAG ,TER-OUTF (INTERVAL 1 n))))
(fact 'ring-additive-ag-is-abelian-group 'A)
(fact 'interval-in-set 1 'n)(fact 'interval-card-in-nn 1 'n)
(fact 'ter-outf-type 'A 'm 'n 'k 'l 'P 'Q 'R 'row 'col)
(fact 'ter-tout-type 'A 'm 'n 'k 'l 'P 'Q 'R 'row 'col)
(te-with-cut `(FORALL x (IMPLIES (IN x (INTERVAL 1 n)) (= (,TER-OUTF x) (,TER-TOUT x))))
  (lambda ()
    (di)(di)
    (let ((xv (te-lastvar '(INTERVAL 1 n))))
      (lam-b)(nth-r)
      (fact 'matmul-entry 'A 'n 'k 'l 'Q 'R xv 'col)
      (subst `(= (ENTRY (MATMUL A Q R) ,xv col) (FINSUM ,TE-RAG (VNB-LAMBDA j (INTERVAL 1 k) ((MUL A) (ENTRY Q ,xv j) (ENTRY R j col))) (INTERVAL 1 k))))
      (fact 'interval-in-set 1 'k)(fact 'interval-card-in-nn 1 'k)
      (fact 'ter-gj-type 'A 'm 'n 'k 'l 'P 'Q 'R 'row 'col xv)
      (fact 'entry-in-carrier 'm 'n '(CARR A) 'P 'row xv)
      (fact 'finsum-ring-distrib-left-gen 'A `(ENTRY P row ,xv) '(INTERVAL 1 k) `(VNB-LAMBDA j (INTERVAL 1 k) ((MUL A) (ENTRY Q ,xv j) (ENTRY R j col))))
      (subst `(= ((MUL A) (ENTRY P row ,xv) (FINSUM ,TE-RAG (VNB-LAMBDA j (INTERVAL 1 k) ((MUL A) (ENTRY Q ,xv j) (ENTRY R j col))) (INTERVAL 1 k)))
                 (FINSUM ,TE-RAG (VNB-LAMBDA z (INTERVAL 1 k) ((MUL A) (ENTRY P row ,xv) ((VNB-LAMBDA j (INTERVAL 1 k) ((MUL A) (ENTRY Q ,xv j) (ENTRY R j col))) z))) (INTERVAL 1 k))))
      (fact 'ter-dist-type 'A 'm 'n 'k 'l 'P 'Q 'R 'row 'col xv)
      (fact 'ter-red-type 'A 'm 'n 'k 'l 'P 'Q 'R 'row 'col xv)
      (let ((DISTxv `(VNB-LAMBDA z (INTERVAL 1 k) ((MUL A) (ENTRY P row ,xv) ((VNB-LAMBDA j (INTERVAL 1 k) ((MUL A) (ENTRY Q ,xv j) (ENTRY R j col))) z))))
            (REDxv  `(VNB-LAMBDA c (INTERVAL 1 k) ((MUL A) ((MUL A) (ENTRY P row ,xv) (ENTRY Q ,xv c)) (ENTRY R c col)))))
        (te-with-cut `(FORALL w (IMPLIES (IN w (INTERVAL 1 k)) (= (,DISTxv w) (,REDxv w))))
          (lambda ()
            (di)(di)
            (let ((wv (te-lastvar '(INTERVAL 1 k))))
              (lam-b)
              (fact 'entry-in-carrier 'm 'n '(CARR A) 'P 'row xv)
              (fact 'entry-in-carrier 'n 'k '(CARR A) 'Q xv wv)
              (fact 'entry-in-carrier 'k 'l '(CARR A) 'R wv 'col)
              (fact 'ring-carrier-closed-mul 'A `(ENTRY P row ,xv) `(ENTRY Q ,xv ,wv))
              (fact 'ring-mul-assoc 'A `(ENTRY P row ,xv) `(ENTRY Q ,xv ,wv) `(ENTRY R ,wv col))
              (subst `(= ((MUL A) ((MUL A) (ENTRY P row ,xv) (ENTRY Q ,xv ,wv)) (ENTRY R ,wv col))
                         ((MUL A) (ENTRY P row ,xv) ((MUL A) (ENTRY Q ,xv ,wv) (ENTRY R ,wv col)))))
              (rfl)))
          (lambda ()
            (fact 'finsum-congruence TE-RAG '(INTERVAL 1 k) DISTxv REDxv)
            (ass))))))
  (lambda ()
    (fact 'finsum-congruence TE-RAG '(INTERVAL 1 n) TER-OUTF TER-TOUT)
    (ass)))
(qed 'triple-entry-right)
(category! 'triple-entry-right 'algebra)
