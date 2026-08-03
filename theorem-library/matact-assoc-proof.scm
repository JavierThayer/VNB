;;; matact-assoc-proof.scm -- Remark 3.39: the matrix action on a sequence of
;;; module elements is associative.
;;;
;;;   IS-MODULE md,  P:MAT(m,n,CARR(SCAL md)),  Q:MAT(n,k,CARR(SCAL md)),
;;;   u:MAT(k,l,VEC md)   |-   (P Q) . u  =  P . (Q . u)
;;;
;;; The book calls this "trivial" and then makes explicit use of it; it is the
;;; only real lemma standing between the Smith normal form and the structure
;;; theory of finitely generated modules (sec 8.2).  It is NOT trivial here: the
;;; left side sums a RING product against a vector, the right side nests two
;;; module actions, and reconciling them is a Fubini interchange plus the module
;;; law (r*s).x = r.(s.x).
;;;
;;; This file is the exact mirror of triple-entry-proof.scm + matmul-assoc-proof.scm
;;; with the substitutions
;;;
;;;     (MUL A)              -->  (ACT md)          [outer factor: scalar . vector]
;;;     R : MAT(k,l,CARR A)  -->  u : MAT(k,l,VEC md)
;;;     RING-ADDITIVE-AG A   -->  MODULE-VECTOR-AG md   [where the sum lives]
;;;     ring-mul-assoc       -->  module-act-mul-compat
;;;     finsum-ring-distrib-right-gen --> finsum-act-collect-gen   [(sum c).x]
;;;     finsum-ring-distrib-left-gen  --> finsum-act-distrib-gen   [r.(sum f)]
;;;
;;; and the scalar ring is A = (SCAL md) throughout.  Both sides are expanded to
;;; the SAME canonical double sum
;;;
;;;     sum_{c in [1,k]} sum_{j in [1,n]}  (P_{row,j} * Q_{j,c}) . u_{c,col}
;;;
;;; written in the fubini-tupled MS-FF(LIST c j) form; finsum-fubini interchanges
;;; the two summation orders.  Note the INNER sums differ in WHICH group they
;;; live in on the left: matmul-entry produces a sum in RING-ADDITIVE-AG(SCAL md)
;;; that is then acted on the vector u_{c,col}, and finsum-act-collect-gen is
;;; precisely the homomorphism  r |-> r . u_{c,col}  that pushes the action in.
;;;
;;; Index naming follows matmul-assoc-proof: the free entry indices are `row'/`col'
;;; so they cannot capture finsum-fubini's bound i/j under case-folding.

;; ---- proof-driver helpers (ms- prefix) ----
(define (ms-pg)(wff-formula (sequent-node-assertion (proof-state-focus *ps*))))
(define (ms-asms)(map wff-formula (sequent-node-assumptions (proof-state-focus *ps*))))
(define (ms-wf v b)(fold-right (lambda(x y)`(FORALL ,x ,y)) b v))
(define (ms-wi p b)(fold-right (lambda(x y)`(IMPLIES ,x ,y)) b p))
(define (ms-di*)(let lp()(let*((g(ms-pg))(h(and(pair? g)(car g))))(when(memq h '(FORALL IMPLIES))(di)(lp)))))
(define (ms-leaves)(filter (lambda(nd)(and(not(sequent-node-grounded? nd))(null?(sequent-node-in-arrows nd))))(dg-ungrounded-nodes(proof-state-dg *ps*))))
(define (ms-goalof l)(wff-formula(sequent-node-assertion l)))
(define (ms-lastvar cls)(let lp((a(ms-asms)))(cond((null? a)#f)((and(pair?(car a))(eq?(caar a)'IN)(equal?(caddr(car a)) cls))(cadr(car a)))(else(lp(cdr a))))))
(define (ms-focus! pred)(let lp((ls(ms-leaves)))(cond((null? ls)(error "matact-assoc: no leaf"))((pred(ms-goalof(car ls)))(set-proof-state-focus! *ps* (car ls))(car ls))(else(lp(cdr ls))))))
;; cut P, then prove the P-subgoal and the continuation, each focused by its
;; CAPTURED LEAF OBJECT -- never re-found by goal formula (they collide).
(define (ms-with-cut P prove-sub prove-cont)
  (let ((before (ms-leaves)))
    (cut P)
    (let* ((new  (filter (lambda(l)(not(memq l before)))(ms-leaves)))
           (sub  (car(filter (lambda(l)(equal?(ms-goalof l) P)) new)))
           (cont (car(filter (lambda(l)(not(eq? l sub))) new))))
      (set-proof-state-focus! *ps* sub)  (prove-sub)
      (set-proof-state-focus! *ps* cont) (prove-cont))))

(define MS-RAG '(RING-ADDITIVE-AG (SCAL md)))
(define MS-VAG '(MODULE-VECTOR-AG md))
(define MS-SC  '(CARR (SCAL md)))
(define MS-VC  '(CARR (MODULE-VECTOR-AG md)))
(define MS-FF '(VNB-LAMBDA z (CARTESIAN (INTERVAL 1 k) (INTERVAL 1 n)) ((ACT md) ((MUL (SCAL md)) (ENTRY P row (NTH 2 z)) (ENTRY Q (NTH 2 z) (NTH 1 z))) (ENTRY u (NTH 1 z) col))))
(define MS-MPREMS '((IN P (MAT m n (CARR (SCAL md)))) (IN Q (MAT n k (CARR (SCAL md)))) (IN u (MAT k l (VEC md)))))
(define MS-PREMS (append MS-MPREMS '((IN row (INTERVAL 1 m)) (IN col (INTERVAL 1 l)))))

;; warranted lambda FUN-typing brick, explicit interval upper bound
(define (ms-typ name lam carr bound ev ep)
  (support name (ms-wf '(md)(ms-wi '((IS-MODULE md))(ms-wf (append '(m n k l P Q u row col) ev)(ms-wi (append MS-PREMS ep)`(IN ,lam (FUN (INTERVAL 1 ,bound) ,carr)))))))
  (warrant! name 'well-known "the summand lambda is a function into the scalar ring's carrier / the vector abelian group's carrier (entry-in-carrier + MUL closure + module-act-type; mvag-carr identifies CARR(MODULE-VECTOR-AG md) with VEC md)."))

;; =====================================================================
;; matact-triple-left : ((PQ).u)_{row,col} = sum_{c in [1,k]} sum_{j in [1,n]} FF(c,j)
;; =====================================================================
(define MAL-LHSM '(MATACT md (MATMUL (SCAL md) P Q) u))
(define MAL-OUTF '(VNB-LAMBDA j (INTERVAL 1 k) ((ACT md) (ENTRY (MATMUL (SCAL md) P Q) row j) (ENTRY u j col))))
(define MAL-TOUT `(VNB-LAMBDA c (INTERVAL 1 k) (FINSUM ,MS-VAG (VNB-LAMBDA j (INTERVAL 1 n) (,MS-FF (LIST c j))) (INTERVAL 1 n))))
(define MAL-TSUM `(FINSUM ,MS-VAG ,MAL-TOUT (INTERVAL 1 k)))
(ms-typ 'mal-outf-type MAL-OUTF MS-VC 'k '() '())
(ms-typ 'mal-tout-type MAL-TOUT MS-VC 'k '() '())
(ms-typ 'mal-inf-type '(VNB-LAMBDA j (INTERVAL 1 n) ((MUL (SCAL md)) (ENTRY P row j) (ENTRY Q j x))) MS-SC 'n '(x) '((IN x (INTERVAL 1 k))))
(ms-typ 'mal-dist-type '(VNB-LAMBDA z (INTERVAL 1 n) ((ACT md) ((VNB-LAMBDA j (INTERVAL 1 n) ((MUL (SCAL md)) (ENTRY P row j) (ENTRY Q j x))) z) (ENTRY u x col))) MS-VC 'n '(x) '((IN x (INTERVAL 1 k))))
(ms-typ 'mal-red-type '(VNB-LAMBDA j (INTERVAL 1 n) ((ACT md) ((MUL (SCAL md)) (ENTRY P row j) (ENTRY Q j x)) (ENTRY u x col))) MS-VC 'n '(x) '((IN x (INTERVAL 1 k))))

(sp (ms-wf '(md)(ms-wi '((IS-MODULE md))(ms-wf '(m n k l P Q u row col)(ms-wi MS-PREMS `(= (ENTRY ,MAL-LHSM row col) ,MAL-TSUM))))))
(ms-di*)
(fact 'module-scalar-ring 'md)                       ; IS-RING (SCAL md)
(fact 'matmul-type '(SCAL md) 'm 'n 'k 'P 'Q)        ; PQ : m x k over CARR(SCAL md)
(fact 'matact-entry 'md 'm 'k 'l '(MATMUL (SCAL md) P Q) 'u 'row 'col)
(subst `(= (ENTRY ,MAL-LHSM row col) (FINSUM ,MS-VAG ,MAL-OUTF (INTERVAL 1 k))))
(fact 'module-vector-ag-is-abelian-group 'md)
(fact 'interval-in-set 1 'k)(fact 'interval-card-in-nn 1 'k)
(fact 'mal-outf-type 'md 'm 'n 'k 'l 'P 'Q 'u 'row 'col)
(fact 'mal-tout-type 'md 'm 'n 'k 'l 'P 'Q 'u 'row 'col)
(ms-with-cut `(FORALL x (IMPLIES (IN x (INTERVAL 1 k)) (= (,MAL-OUTF x) (,MAL-TOUT x))))
  (lambda ()
    (di)(di)
    (let ((xv (ms-lastvar '(INTERVAL 1 k))))
      (lam-b)(nth-r)
      (fact 'matmul-entry '(SCAL md) 'm 'n 'k 'P 'Q 'row xv)
      (subst `(= (ENTRY (MATMUL (SCAL md) P Q) row ,xv)
                 (FINSUM ,MS-RAG (VNB-LAMBDA j (INTERVAL 1 n) ((MUL (SCAL md)) (ENTRY P row j) (ENTRY Q j ,xv))) (INTERVAL 1 n))))
      (fact 'interval-in-set 1 'n)(fact 'interval-card-in-nn 1 'n)
      (fact 'mal-inf-type 'md 'm 'n 'k 'l 'P 'Q 'u 'row 'col xv)
      (fact 'entry-in-carrier 'k 'l '(VEC md) 'u xv 'col)
      ;; push the action into the ring sum: (sum_j P_rj Q_jx) . u_xc = sum_j (...) . u_xc
      (fact 'finsum-act-collect-gen 'md `(ENTRY u ,xv col) '(INTERVAL 1 n)
            `(VNB-LAMBDA j (INTERVAL 1 n) ((MUL (SCAL md)) (ENTRY P row j) (ENTRY Q j ,xv))))
      (subst `(= ((ACT md) (FINSUM ,MS-RAG (VNB-LAMBDA j (INTERVAL 1 n) ((MUL (SCAL md)) (ENTRY P row j) (ENTRY Q j ,xv))) (INTERVAL 1 n)) (ENTRY u ,xv col))
                 (FINSUM ,MS-VAG (VNB-LAMBDA z (INTERVAL 1 n) ((ACT md) ((VNB-LAMBDA j (INTERVAL 1 n) ((MUL (SCAL md)) (ENTRY P row j) (ENTRY Q j ,xv))) z) (ENTRY u ,xv col))) (INTERVAL 1 n))))
      (fact 'mal-dist-type 'md 'm 'n 'k 'l 'P 'Q 'u 'row 'col xv)
      (fact 'mal-red-type 'md 'm 'n 'k 'l 'P 'Q 'u 'row 'col xv)
      (let ((DISTxv `(VNB-LAMBDA z (INTERVAL 1 n) ((ACT md) ((VNB-LAMBDA j (INTERVAL 1 n) ((MUL (SCAL md)) (ENTRY P row j) (ENTRY Q j ,xv))) z) (ENTRY u ,xv col))))
            (REDxv  `(VNB-LAMBDA j (INTERVAL 1 n) ((ACT md) ((MUL (SCAL md)) (ENTRY P row j) (ENTRY Q j ,xv)) (ENTRY u ,xv col)))))
        (ms-with-cut `(FORALL w (IMPLIES (IN w (INTERVAL 1 n)) (= (,DISTxv w) (,REDxv w))))
          (lambda ()
            (di)(di)
            (let ((wv (ms-lastvar '(INTERVAL 1 n))))
              (lam-b)
              (fact 'entry-in-carrier 'm 'n MS-SC 'P 'row wv)
              (fact 'entry-in-carrier 'n 'k MS-SC 'Q wv xv)
              (fact 'ring-carrier-closed-mul '(SCAL md) `(ENTRY P row ,wv) `(ENTRY Q ,wv ,xv))
              (fact 'entry-in-carrier 'k 'l '(VEC md) 'u xv 'col)
              (fact 'module-act-type 'md `((MUL (SCAL md)) (ENTRY P row ,wv) (ENTRY Q ,wv ,xv)) `(ENTRY u ,xv col))
              (rfl)))
          (lambda ()
            (fact 'finsum-congruence MS-VAG '(INTERVAL 1 n) DISTxv REDxv)
            (ass))))))
  (lambda ()
    (fact 'finsum-congruence MS-VAG '(INTERVAL 1 k) MAL-OUTF MAL-TOUT)
    (ass)))
(qed 'matact-triple-left)
(category! 'matact-triple-left 'algebra)

;; =====================================================================
;; matact-triple-right : (P.(Q.u))_{row,col} = sum_{j in [1,n]} sum_{c in [1,k]} FF(c,j)
;; =====================================================================
(define MAR-RHSM '(MATACT md P (MATACT md Q u)))
(define MAR-OUTF '(VNB-LAMBDA j (INTERVAL 1 n) ((ACT md) (ENTRY P row j) (ENTRY (MATACT md Q u) j col))))
(define MAR-TOUT `(VNB-LAMBDA j (INTERVAL 1 n) (FINSUM ,MS-VAG (VNB-LAMBDA c (INTERVAL 1 k) (,MS-FF (LIST c j))) (INTERVAL 1 k))))
(define MAR-TSUM `(FINSUM ,MS-VAG ,MAR-TOUT (INTERVAL 1 n)))
(ms-typ 'mar-outf-type MAR-OUTF MS-VC 'n '() '())
(ms-typ 'mar-tout-type MAR-TOUT MS-VC 'n '() '())
(ms-typ 'mar-gj-type '(VNB-LAMBDA j (INTERVAL 1 k) ((ACT md) (ENTRY Q x j) (ENTRY u j col))) MS-VC 'k '(x) '((IN x (INTERVAL 1 n))))
(ms-typ 'mar-dist-type '(VNB-LAMBDA z (INTERVAL 1 k) ((ACT md) (ENTRY P row x) ((VNB-LAMBDA j (INTERVAL 1 k) ((ACT md) (ENTRY Q x j) (ENTRY u j col))) z))) MS-VC 'k '(x) '((IN x (INTERVAL 1 n))))
(ms-typ 'mar-red-type '(VNB-LAMBDA c (INTERVAL 1 k) ((ACT md) ((MUL (SCAL md)) (ENTRY P row x) (ENTRY Q x c)) (ENTRY u c col))) MS-VC 'k '(x) '((IN x (INTERVAL 1 n))))

(sp (ms-wf '(md)(ms-wi '((IS-MODULE md))(ms-wf '(m n k l P Q u row col)(ms-wi MS-PREMS `(= (ENTRY ,MAR-RHSM row col) ,MAR-TSUM))))))
(ms-di*)
(fact 'module-scalar-ring 'md)
(fact 'matact-type 'md 'n 'k 'l 'Q 'u)               ; Q.u : n x l over VEC md
(fact 'matact-entry 'md 'm 'n 'l 'P '(MATACT md Q u) 'row 'col)
(subst `(= (ENTRY ,MAR-RHSM row col) (FINSUM ,MS-VAG ,MAR-OUTF (INTERVAL 1 n))))
(fact 'module-vector-ag-is-abelian-group 'md)
(fact 'interval-in-set 1 'n)(fact 'interval-card-in-nn 1 'n)
(fact 'mar-outf-type 'md 'm 'n 'k 'l 'P 'Q 'u 'row 'col)
(fact 'mar-tout-type 'md 'm 'n 'k 'l 'P 'Q 'u 'row 'col)
(ms-with-cut `(FORALL x (IMPLIES (IN x (INTERVAL 1 n)) (= (,MAR-OUTF x) (,MAR-TOUT x))))
  (lambda ()
    (di)(di)
    (let ((xv (ms-lastvar '(INTERVAL 1 n))))
      (lam-b)(nth-r)
      (fact 'matact-entry 'md 'n 'k 'l 'Q 'u xv 'col)
      (subst `(= (ENTRY (MATACT md Q u) ,xv col)
                 (FINSUM ,MS-VAG (VNB-LAMBDA j (INTERVAL 1 k) ((ACT md) (ENTRY Q ,xv j) (ENTRY u j col))) (INTERVAL 1 k))))
      (fact 'interval-in-set 1 'k)(fact 'interval-card-in-nn 1 'k)
      (fact 'mar-gj-type 'md 'm 'n 'k 'l 'P 'Q 'u 'row 'col xv)
      (fact 'entry-in-carrier 'm 'n MS-SC 'P 'row xv)
      ;; push the fixed scalar into the vector sum
      (fact 'finsum-act-distrib-gen 'md `(ENTRY P row ,xv) '(INTERVAL 1 k)
            `(VNB-LAMBDA j (INTERVAL 1 k) ((ACT md) (ENTRY Q ,xv j) (ENTRY u j col))))
      (subst `(= ((ACT md) (ENTRY P row ,xv) (FINSUM ,MS-VAG (VNB-LAMBDA j (INTERVAL 1 k) ((ACT md) (ENTRY Q ,xv j) (ENTRY u j col))) (INTERVAL 1 k)))
                 (FINSUM ,MS-VAG (VNB-LAMBDA z (INTERVAL 1 k) ((ACT md) (ENTRY P row ,xv) ((VNB-LAMBDA j (INTERVAL 1 k) ((ACT md) (ENTRY Q ,xv j) (ENTRY u j col))) z))) (INTERVAL 1 k))))
      (fact 'mar-dist-type 'md 'm 'n 'k 'l 'P 'Q 'u 'row 'col xv)
      (fact 'mar-red-type 'md 'm 'n 'k 'l 'P 'Q 'u 'row 'col xv)
      (let ((DISTxv `(VNB-LAMBDA z (INTERVAL 1 k) ((ACT md) (ENTRY P row ,xv) ((VNB-LAMBDA j (INTERVAL 1 k) ((ACT md) (ENTRY Q ,xv j) (ENTRY u j col))) z))))
            (REDxv  `(VNB-LAMBDA c (INTERVAL 1 k) ((ACT md) ((MUL (SCAL md)) (ENTRY P row ,xv) (ENTRY Q ,xv c)) (ENTRY u c col)))))
        (ms-with-cut `(FORALL w (IMPLIES (IN w (INTERVAL 1 k)) (= (,DISTxv w) (,REDxv w))))
          (lambda ()
            (di)(di)
            (let ((wv (ms-lastvar '(INTERVAL 1 k))))
              (lam-b)
              (fact 'entry-in-carrier 'm 'n MS-SC 'P 'row xv)
              (fact 'entry-in-carrier 'n 'k MS-SC 'Q xv wv)
              (fact 'entry-in-carrier 'k 'l '(VEC md) 'u wv 'col)
              (fact 'ring-carrier-closed-mul '(SCAL md) `(ENTRY P row ,xv) `(ENTRY Q ,xv ,wv))
              (fact 'module-act-type 'md `(ENTRY Q ,xv ,wv) `(ENTRY u ,wv col))
              (fact 'module-act-type 'md `((MUL (SCAL md)) (ENTRY P row ,xv) (ENTRY Q ,xv ,wv)) `(ENTRY u ,wv col))
              ;; (r*s).x = r.(s.x)
              (fact 'module-act-mul-compat 'md `(ENTRY P row ,xv) `(ENTRY Q ,xv ,wv) `(ENTRY u ,wv col))
              (subst `(= ((ACT md) ((MUL (SCAL md)) (ENTRY P row ,xv) (ENTRY Q ,xv ,wv)) (ENTRY u ,wv col))
                         ((ACT md) (ENTRY P row ,xv) ((ACT md) (ENTRY Q ,xv ,wv) (ENTRY u ,wv col)))))
              (rfl)))
          (lambda ()
            (fact 'finsum-congruence MS-VAG '(INTERVAL 1 k) DISTxv REDxv)
            (ass))))))
  (lambda ()
    (fact 'finsum-congruence MS-VAG '(INTERVAL 1 n) MAR-OUTF MAR-TOUT)
    (ass)))
(qed 'matact-triple-right)
(category! 'matact-triple-right 'algebra)

;; =====================================================================
;; matact-assoc (Remark 3.39):  (P Q) . u  =  P . (Q . u)
;; =====================================================================
(support 'matact-assoc-summand-type
  (ms-wf '(md)(ms-wi '((IS-MODULE md))
    (ms-wf '(m n k l P Q u row col)(ms-wi MS-PREMS
      `(IN ,MS-FF (FUN (CARTESIAN (INTERVAL 1 k) (INTERVAL 1 n)) ,MS-VC)))))))
(warrant! 'matact-assoc-summand-type 'well-known
  "(c,j) |-> (P_{row,j} * Q_{j,c}) . u_{c,col} is a function on [1,k] x [1,n] into
   the vector abelian group's carrier (entry-in-carrier, ring MUL closure,
   module-act-type, mvag-carr).")

(sp (ms-wf '(md)(ms-wi '((IS-MODULE md))(ms-wf '(m n k l P Q u)(ms-wi MS-MPREMS `(= ,MAL-LHSM ,MAR-RHSM))))))
(ms-di*)
(fact 'module-scalar-ring 'md)
(fact 'matmul-type '(SCAL md) 'm 'n 'k 'P 'Q)
(fact 'matact-type 'md 'm 'k 'l '(MATMUL (SCAL md) P Q) 'u)   ; (PQ).u : m x l
(fact 'matact-type 'md 'n 'k 'l 'Q 'u)                        ; Q.u    : n x l
(fact 'matact-type 'md 'm 'n 'l 'P '(MATACT md Q u))          ; P.(Q.u): m x l

(cut (ms-wf '(row) (ms-wi '((IN row (INTERVAL 1 m)))
       (ms-wf '(col) (ms-wi '((IN col (INTERVAL 1 l)))
         `(= (ENTRY ,MAL-LHSM row col) (ENTRY ,MAR-RHSM row col)))))))

;; ----- the entry identity (cut auto-focuses this subgoal) -----
(ms-di*)
(fact 'matact-triple-left  'md 'm 'n 'k 'l 'P 'Q 'u 'row 'col)
(subst `(= (ENTRY ,MAL-LHSM row col) ,MAL-TSUM))
(fact 'matact-triple-right 'md 'm 'n 'k 'l 'P 'Q 'u 'row 'col)
(subst `(= (ENTRY ,MAR-RHSM row col) ,MAR-TSUM))
;; interchange the summation order -- the crux
(fact 'module-vector-ag-is-abelian-group 'md)
(fact 'interval-in-set 1 'k)(fact 'interval-card-in-nn 1 'k)
(fact 'interval-in-set 1 'n)(fact 'interval-card-in-nn 1 'n)
(fact 'matact-assoc-summand-type 'md 'm 'n 'k 'l 'P 'Q 'u 'row 'col)
(fact 'finsum-fubini-c MS-VAG '(INTERVAL 1 k) '(INTERVAL 1 n) MS-FF)
(ass)

;; ----- back in the main goal: matrix-entry-extensionality -----
(ms-focus! (lambda (g) (and (pair? g) (eq? (car g) '=) (equal? (cadr g) MAL-LHSM))))
(fact 'matrix-entry-extensionality 'm 'l '(VEC md) MAL-LHSM MAR-RHSM)
(ass)

(qed 'matact-assoc)
(category! 'matact-assoc 'algebra)

;; ----- categorize the Phase C PSS bricks declared in mod-seq.scm -----
;; (structure-library loads before the PSS layer, so category! must run here.)
(category! 'mvag-carr 'algebra)
(category! 'mvag-op 'algebra)
(category! 'mvag-id 'algebra)
(category! 'matact-type 'algebra)
(category! 'matact-entry 'algebra)
(category! 'matact-summand-type 'algebra)
(category! 'finsum-act-distrib-gen 'algebra)
(category! 'finsum-act-collect-gen 'algebra)
(category! 'matact-assoc-summand-type 'algebra)
(for-each (lambda (n) (category! n 'algebra))
          '(mal-outf-type mal-tout-type mal-inf-type mal-dist-type mal-red-type
            mar-outf-type mar-tout-type mar-gj-type mar-dist-type mar-red-type))
