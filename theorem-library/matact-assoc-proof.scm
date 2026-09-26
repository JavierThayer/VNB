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
;;; RETIRED 2026-09-14 (proven): matact-assoc-summand-type -- theorem-library/lam-fun-bricks.scm (dk-lam-fun!)
;;; RETIRED 2026-09-14 (proven): mal-outf-type -- theorem-library/lam-fun-bricks.scm (dk-lam-fun!)
;;; RETIRED 2026-09-14 (proven): mal-tout-type -- theorem-library/lam-fun-bricks.scm (dk-lam-fun!)
;;; RETIRED 2026-09-14 (proven): mal-inf-type -- theorem-library/lam-fun-bricks.scm (dk-lam-fun!)
;;; RETIRED 2026-09-14 (proven): mal-dist-type -- theorem-library/lam-fun-bricks.scm (dk-lam-fun!)
;;; RETIRED 2026-09-14 (proven): mal-red-type -- theorem-library/lam-fun-bricks.scm (dk-lam-fun!)
;;; RETIRED 2026-09-14 (proven): mar-outf-type -- theorem-library/lam-fun-bricks.scm (dk-lam-fun!)
;;; RETIRED 2026-09-14 (proven): mar-tout-type -- theorem-library/lam-fun-bricks.scm (dk-lam-fun!)
;;; RETIRED 2026-09-14 (proven): mar-gj-type -- theorem-library/lam-fun-bricks.scm (dk-lam-fun!)
;;; RETIRED 2026-09-14 (proven): mar-dist-type -- theorem-library/lam-fun-bricks.scm (dk-lam-fun!)
;;; RETIRED 2026-09-14 (proven): mar-red-type -- theorem-library/lam-fun-bricks.scm (dk-lam-fun!)

;; ---- proof-driver helpers (ms- prefix) ----
(define (ms-pg)(wff-formula (sequent-node-assertion (proof-state-focus *ps*))))
(define (ms-asms)(map wff-formula (sequent-node-assumptions (proof-state-focus *ps*))))
(define (ms-wf v b)(fold-right (lambda(x y)`(FORALL ,x ,y)) b v))
(define (ms-wi p b)(fold-right (lambda(x y)`(IMPLIES ,x ,y)) b p))
(define (ms-di*)(let lp()(let*((g(ms-pg))(h(and(pair? g)(car g))))(when(memq h '(FORALL IMPLIES))(di)(lp)))))
(define (ms-leaves)(filter (lambda(nd)(and(not(sequent-node-grounded? nd))(null?(sequent-node-in-arrows nd))))(dg-ungrounded-nodes(proof-state-dg *ps*))))
(define (ms-goalof l)(wff-formula(sequent-node-assertion l)))
(define (ms-lastvar cls)(let lp((a(ms-asms)))(cond((null? a)#f)((and(pair?(car a))(eq?(caar a)'IN)(equal?(caddr(car a)) cls))(cadr(car a)))(else(lp(cdr a))))))
(define (ms-focus! pred)(let lp((ls(ms-leaves)))(cond((null? ls)(error "matact-assoc: no leaf"))((pred(ms-goalof(car ls)))(dk-focus! (car ls))(car ls))(else(lp(cdr ls))))))
;; cut P, then prove the P-subgoal and the continuation, each focused by its
;; CAPTURED LEAF OBJECT -- never re-found by goal formula (they collide).
(define (ms-with-cut P prove-sub prove-cont)
  (let ((before (ms-leaves)))
    (cut P)
    (let* ((new  (filter (lambda(l)(not(memq l before)))(ms-leaves)))
           (sub  (car(filter (lambda(l)(equal?(ms-goalof l) P)) new)))
           (cont (car(filter (lambda(l)(not(eq? l sub))) new))))
      (dk-focus! sub)  (prove-sub)
      (dk-focus! cont) (prove-cont))))

(define MS-RAG '(RING-ADDITIVE-AG (SCAL md)))
(define MS-VAG '(MODULE-VECTOR-AG md))
(define MS-SC  '(CARR (SCAL md)))
(define MS-VC  '(CARR (MODULE-VECTOR-AG md)))
(define MS-FF '(VNB-LAMBDA z (CARTESIAN (INTERVAL 1 k) (INTERVAL 1 n)) ((ACT md) ((MUL (SCAL md)) (ENTRY P row (NTH 2 z)) (ENTRY Q (NTH 2 z) (NTH 1 z))) (ENTRY u (NTH 1 z) col))))
(define MS-MPREMS '((IN P (MAT m n (CARR (SCAL md)))) (IN Q (MAT n k (CARR (SCAL md)))) (IN u (MAT k l (VEC md)))))
(define MS-PREMS (append MS-MPREMS '((IN row (INTERVAL 1 m)) (IN col (INTERVAL 1 l)))))

;; (ms-typ, a generator of warranted FUN-typing supports, was removed 2026-09-16:
;; nothing called it; the bricks are PROVEN in lam-fun-bricks.scm.)

;; GUARDED 2026-09-16 (the SIZE/MAT change): the two triple-entry lemmas carry
;; (<= 1 n) and (<= 1 k), right after the u premise, as triple-entry-left/right
;; do (triple-entry-proof.scm).
(define MS-PREMS-G (append MS-MPREMS '((<= 1 n) (<= 1 k) (IN row (INTERVAL 1 m)) (IN col (INTERVAL 1 l)))))
;; (<= 1 v) in context: land (NOT (= v 0)), then the product guard G by prop.
(define (ms-guard! v g)
  (if (not (dk-asm? (list 'NOT (list '= v 0)))) (dk-nonzero! v))
  (dk-have-prop! g))
;; The restated finsum-congruence (2026-09-17, the user's "shape 1") carries a
;; SECOND antecedent -- the POINTWISE typing `forall z in S. f z in CARR(ag)' --
;; placed AFTER the equality.  At all four citation sites in this file the
;; summand's FUN typing is already in context (the lam-fun-bricks
;; mal-outf-type / mal-dist-type / mar-outf-type / mar-dist-type), so the
;; pointwise form is one `fun-apply-type-c' on a peeled index.  Landing it
;; BEFORE the `fact' lets that citation auto-detach BOTH antecedents exactly as
;; it used to auto-detach the one.  Mirrors te-ptwise! in triple-entry-proof.scm.
(define (ms-ptwise! f ivl carr)
  (have! (list 'FORALL 'z_ (list 'IMPLIES (list 'IN 'z_ ivl) (list 'IN (list f 'z_) carr)))
         (lambda ()
           ;; a guarded universal peels whole in one di; read the eigenvariable
           ;; off the LANDING, never off the context by shape
           (let* ((landed (dk-peel!))
                  (hits (filter (lambda (a) (and (pair? a) (eq? (car a) 'IN)
                                                 (equal? (caddr a) ivl)))
                                landed)))
             (if (null? hits) (error "ms-ptwise!: the peel landed no index typing"))
             (fact 'fun-apply-type-c f ivl carr (cadr (car hits)))
             (ass)))))

;; =====================================================================
;; matact-triple-left : ((PQ).u)_{row,col} = sum_{c in [1,k]} sum_{j in [1,n]} FF(c,j)
;; =====================================================================
(define MAL-LHSM '(MATACT md (MATMUL (SCAL md) P Q) u))
(define MAL-OUTF '(VNB-LAMBDA j (INTERVAL 1 k) ((ACT md) (ENTRY (MATMUL (SCAL md) P Q) row j) (ENTRY u j col))))
(define MAL-TOUT `(VNB-LAMBDA c (INTERVAL 1 k) (FINSUM ,MS-VAG (VNB-LAMBDA j (INTERVAL 1 n) (,MS-FF (LIST c j))) (INTERVAL 1 n))))
(define MAL-TSUM `(FINSUM ,MS-VAG ,MAL-TOUT (INTERVAL 1 k)))

;; GUARDS (2026-09-16).  (<= 1 k) is FORCED: k = 0, m = n = l = 1, u = [] in
;; MAT(0,1,VEC md), Q = [[]] 1-by-0: (PQ).u is 1-by-0 (MATACT reads its column
;; count off SIZE([]) = [0,0]), so its (1,1) entry is undefined while the right
;; side is the empty sum VZERO(md).  (<= 1 n) is NOT forced by a counterexample
;; (at n = 0 with k >= 1 both sides are VZERO) but this route needs it -- it
;; expands PQ by matmul-entry and types PQ by matmul-type -- and the only citer,
;; matact-assoc, holds it.  Mirrors triple-entry-left.
(sp (ms-wf '(md)(ms-wi '((IS-MODULE md))(ms-wf '(m n k l P Q u row col)(ms-wi MS-PREMS-G `(= (ENTRY ,MAL-LHSM row col) ,MAL-TSUM))))))
(ms-di*)
(fact 'module-scalar-ring 'md)                       ; IS-RING (SCAL md)
(ms-guard! 'n '(IMPLIES (= n 0) (OR (= m 0) (= k 0))))
(fact 'matmul-type '(SCAL md) 'm 'n 'k 'P 'Q)        ; PQ : m x k over CARR(SCAL md)
(fact 'matact-entry 'md 'm 'k 'l '(MATMUL (SCAL md) P Q) 'u 'row 'col)
(subst `(= (ENTRY ,MAL-LHSM row col) (FINSUM ,MS-VAG ,MAL-OUTF (INTERVAL 1 k))))
(fact 'module-vector-ag-is-abelian-group 'md)
;; interval-card-in-nn's guard: the dimensions are untyped in the statement, so
;; k comes off u : MAT k l and n off Q : MAT n k (mat-rows-in-nn).
(fact 'mat-rows-in-nn 'k 'l '(VEC md) 'u)
(fact 'interval-in-set 1 'k)(fact 'interval-card-in-nn 1 'k)
(fact 'mal-outf-type 'md 'm 'n 'k 'l 'P 'Q 'u 'row 'col)
(fact 'mal-tout-type 'md 'm 'n 'k 'l 'P 'Q 'u 'row 'col)
(ms-with-cut `(FORALL x (IMPLIES (IN x (INTERVAL 1 k)) (= (,MAL-OUTF x) (,MAL-TOUT x))))
  (lambda ()
    (ms-di*)                 ; a guarded universal peels whole in one di
    (let ((xv (ms-lastvar '(INTERVAL 1 k))))
      (lam-b)(nth-r)
      (fact 'matmul-entry '(SCAL md) 'm 'n 'k 'P 'Q 'row xv)
      (subst `(= (ENTRY (MATMUL (SCAL md) P Q) row ,xv)
                 (FINSUM ,MS-RAG (VNB-LAMBDA j (INTERVAL 1 n) ((MUL (SCAL md)) (ENTRY P row j) (ENTRY Q j ,xv))) (INTERVAL 1 n))))
      (fact 'mat-rows-in-nn 'n 'k MS-SC 'Q)
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
            (ms-di*)                 ; a guarded universal peels whole in one di
            (let ((wv (ms-lastvar '(INTERVAL 1 n))))
              (lam-b)
              (fact 'entry-in-carrier 'm 'n MS-SC 'P 'row wv)
              (fact 'entry-in-carrier 'n 'k MS-SC 'Q wv xv)
              (fact 'ring-carrier-closed-mul '(SCAL md) `(ENTRY P row ,wv) `(ENTRY Q ,wv ,xv))
              (fact 'entry-in-carrier 'k 'l '(VEC md) 'u xv 'col)
              (fact 'module-act-type 'md `((MUL (SCAL md)) (ENTRY P row ,wv) (ENTRY Q ,wv ,xv)) `(ENTRY u ,xv col))
              (rfl)))
          (lambda ()
            (ms-ptwise! DISTxv '(INTERVAL 1 n) MS-VC)
            (fact 'finsum-congruence MS-VAG '(INTERVAL 1 n) DISTxv REDxv)
            (ass))))))
  (lambda ()
    (ms-ptwise! MAL-OUTF '(INTERVAL 1 k) MS-VC)
    (fact 'finsum-congruence MS-VAG '(INTERVAL 1 k) MAL-OUTF MAL-TOUT)
    (ass)))
(qed 'matact-triple-left)
(topic! 'matact-triple-left 'algebra)

;; =====================================================================
;; matact-triple-right : (P.(Q.u))_{row,col} = sum_{j in [1,n]} sum_{c in [1,k]} FF(c,j)
;; =====================================================================
(define MAR-RHSM '(MATACT md P (MATACT md Q u)))
(define MAR-OUTF '(VNB-LAMBDA j (INTERVAL 1 n) ((ACT md) (ENTRY P row j) (ENTRY (MATACT md Q u) j col))))
(define MAR-TOUT `(VNB-LAMBDA j (INTERVAL 1 n) (FINSUM ,MS-VAG (VNB-LAMBDA c (INTERVAL 1 k) (,MS-FF (LIST c j))) (INTERVAL 1 k))))
(define MAR-TSUM `(FINSUM ,MS-VAG ,MAR-TOUT (INTERVAL 1 n)))

;; GUARDS (2026-09-16), both FORCED.  k = 0, m = n = l = 1: u = [], Q = [[]]
;; is 1-by-0, Q.u is 1-by-0 and ENTRY(Q.u, 1, 1) is undefined.  n = 0,
;; m = k = l = 1: Q = [], P = [[]] is 1-by-0, Q.u = MATACT(md,[],u) has no rows,
;; so P.(Q.u) is 1-by-0 and its (1,1) entry is undefined; the right side is the
;; empty sum VZERO(md).  Mirrors triple-entry-right.
(sp (ms-wf '(md)(ms-wi '((IS-MODULE md))(ms-wf '(m n k l P Q u row col)(ms-wi MS-PREMS-G `(= (ENTRY ,MAR-RHSM row col) ,MAR-TSUM))))))
(ms-di*)
(fact 'module-scalar-ring 'md)
(ms-guard! 'k '(IMPLIES (= k 0) (OR (= n 0) (= l 0))))
(fact 'matact-type 'md 'n 'k 'l 'Q 'u)               ; Q.u : n x l over VEC md
(fact 'matact-entry 'md 'm 'n 'l 'P '(MATACT md Q u) 'row 'col)
(subst `(= (ENTRY ,MAR-RHSM row col) (FINSUM ,MS-VAG ,MAR-OUTF (INTERVAL 1 n))))
(fact 'module-vector-ag-is-abelian-group 'md)
(fact 'mat-rows-in-nn 'n 'k MS-SC 'Q)
(fact 'interval-in-set 1 'n)(fact 'interval-card-in-nn 1 'n)
(fact 'mar-outf-type 'md 'm 'n 'k 'l 'P 'Q 'u 'row 'col)
(fact 'mar-tout-type 'md 'm 'n 'k 'l 'P 'Q 'u 'row 'col)
(ms-with-cut `(FORALL x (IMPLIES (IN x (INTERVAL 1 n)) (= (,MAR-OUTF x) (,MAR-TOUT x))))
  (lambda ()
    (ms-di*)                 ; a guarded universal peels whole in one di
    (let ((xv (ms-lastvar '(INTERVAL 1 n))))
      (lam-b)(nth-r)
      (fact 'matact-entry 'md 'n 'k 'l 'Q 'u xv 'col)
      (subst `(= (ENTRY (MATACT md Q u) ,xv col)
                 (FINSUM ,MS-VAG (VNB-LAMBDA j (INTERVAL 1 k) ((ACT md) (ENTRY Q ,xv j) (ENTRY u j col))) (INTERVAL 1 k))))
      (fact 'mat-rows-in-nn 'k 'l '(VEC md) 'u)
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
            (ms-di*)                 ; a guarded universal peels whole in one di
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
            (ms-ptwise! DISTxv '(INTERVAL 1 k) MS-VC)
            (fact 'finsum-congruence MS-VAG '(INTERVAL 1 k) DISTxv REDxv)
            (ass))))))
  (lambda ()
    (ms-ptwise! MAR-OUTF '(INTERVAL 1 n) MS-VC)
    (fact 'finsum-congruence MS-VAG '(INTERVAL 1 n) MAR-OUTF MAR-TOUT)
    (ass)))
(qed 'matact-triple-right)
(topic! 'matact-triple-right 'algebra)

;; =====================================================================
;; matact-assoc (Remark 3.39):  (P Q) . u  =  P . (Q . u)
;; =====================================================================

;; GUARDS (2026-09-16, the SIZE/MAT change): G1 and G2 (SPEC.md's shapes)
;; after the three membership premises, exactly as matmul-assoc.  A product
;; reads its column count off SIZE of its RIGHT factor, and SIZE([]) = [0,0].
;;   Counterexample without guards: n = 0, m = k = l = 1.  P = [[]] is 1-by-0,
;;   Q = [] is in MAT(0,1,CARR(SCAL md)), u is 1-by-1.  PQ is 1-by-0, so (PQ).u
;;   is 1-by-1 with entry the empty sum VZERO(md); Q.u = MATACT(md,[],u) has no
;;   rows, so P.(Q.u) is 1-by-0.  The two sides differ.  G1 excludes it.
;;   As for matmul-assoc, G1/G2 are stronger than the equation needs (the exact
;;   condition is `n = 0 implies (m = 0 or k = 0 or l = 0)'); they are the
;;   shapes the extensionality route below can use.  NOTE for citers: at
;;   (m,n,k,l) = (1,n,n,1) -- the transports -- G1 is NOT a tautology (it reads
;;   n = 0 => (1 = 0 or (n = 0 and 1 = 0))); the citers case-split on n = 0,
;;   and in the n /= 0 branch both guards follow by prop.
;; Proof: matmul-assoc's split.  The entry identity is vacuous when m = 0 or
;; l = 0; otherwise G1, G2 give n /= 0 and k /= 0, hence 1 <= n and 1 <= k,
;; and the old route (matact-triple-left/right, Fubini) runs unchanged.
(define MS-G1 '(IMPLIES (= n 0) (OR (= m 0) (AND (= k 0) (= l 0)))))
(define MS-G2 '(IMPLIES (= k 0) (OR (= l 0) (AND (= n 0) (= m 0)))))

;; iv in [1,v], v in NN, v = 0 in context: close the focus goal (vacuous).
;; (dk-vacuous! moved to driver-kit.scm as dk-vacuous!, 2026-09-16.)

(sp (ms-wf '(md)(ms-wi '((IS-MODULE md))(ms-wf '(m n k l P Q u)(ms-wi (append MS-MPREMS (list MS-G1 MS-G2)) `(= ,MAL-LHSM ,MAR-RHSM))))))
(ms-di*)
(fact 'module-scalar-ring 'md)
;; the four product guards, from G1 and G2
(dk-have-prop! '(IMPLIES (= n 0) (OR (= m 0) (= k 0))))    ; PQ
(dk-have-prop! '(IMPLIES (= k 0) (OR (= m 0) (= l 0))))    ; (PQ).u
(dk-have-prop! '(IMPLIES (= k 0) (OR (= n 0) (= l 0))))    ; Q.u
(dk-have-prop! '(IMPLIES (= n 0) (OR (= m 0) (= l 0))))    ; P.(Q.u)
;; the two inner non-degeneracies, landed while the context is small
(define MS-H1 '(IMPLIES (NOT (= m 0)) (IMPLIES (NOT (= l 0)) (NOT (= n 0)))))
(define MS-H2 '(IMPLIES (NOT (= m 0)) (IMPLIES (NOT (= l 0)) (NOT (= k 0)))))
(dk-have-prop! MS-H1)
(dk-have-prop! MS-H2)
(fact 'matmul-type '(SCAL md) 'm 'n 'k 'P 'Q)
(fact 'matact-type 'md 'm 'k 'l '(MATMUL (SCAL md) P Q) 'u)   ; (PQ).u : m x l
(fact 'matact-type 'md 'n 'k 'l 'Q 'u)                        ; Q.u    : n x l
(fact 'matact-type 'md 'm 'n 'l 'P '(MATACT md Q u))          ; P.(Q.u): m x l
;; every dimension is a natural
(fact 'mat-rows-in-nn 'm 'n MS-SC 'P)
(fact 'mat-rows-in-nn 'n 'k MS-SC 'Q)
(fact 'mat-rows-in-nn 'k 'l '(VEC md) 'u)
(fact 'mat-cols-in-nn 'k 'l '(VEC md) 'u)

(define MS-ENTRY-ID
  (ms-wf '(row) (ms-wi '((IN row (INTERVAL 1 m)))
    (ms-wf '(col) (ms-wi '((IN col (INTERVAL 1 l)))
      `(= (ENTRY ,MAL-LHSM row col) (ENTRY ,MAR-RHSM row col)))))))
(define ms-cut-leaves (dk-opened (lambda () (cut MS-ENTRY-ID))))
(dk-focus! (find-first (lambda (l) (equal? (dk-goal-of l) MS-ENTRY-ID)) ms-cut-leaves))

;; ----- the entry identity -----
(ms-di*)
(use-em '(= m 0)
  (lambda () (dk-vacuous! 'row 'm))
  (lambda ()
    (use-em '(= l 0)
      (lambda () (dk-vacuous! 'col 'l))
      (lambda ()
        (detach! MS-H1) (detach! '(IMPLIES (NOT (= l 0)) (NOT (= n 0))))
        (detach! MS-H2) (detach! '(IMPLIES (NOT (= l 0)) (NOT (= k 0))))
        (dk-one-le! 'n)
        (dk-one-le! 'k)
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
        (ass)))))

;; ----- back in the main goal: matrix-entry-extensionality -----
(ms-focus! (lambda (g) (and (pair? g) (eq? (car g) '=) (equal? (cadr g) MAL-LHSM))))
(fact 'matrix-entry-extensionality 'm 'l '(VEC md) MAL-LHSM MAR-RHSM)
(ass)

(qed 'matact-assoc)
(topic! 'matact-assoc 'algebra)

;; ----- categorize the Phase C PSS bricks declared in mod-seq.scm -----
;; (structure-library loads before the PSS layer, so topic! must run here.)
(topic! 'mvag-carr 'algebra)
(topic! 'mvag-op 'algebra)
(topic! 'mvag-id 'algebra)
(topic! 'matact-type 'algebra)
(topic! 'matact-entry 'algebra)
(topic! 'matact-summand-type 'algebra)
(topic! 'finsum-act-distrib-gen 'algebra)
(topic! 'finsum-act-collect-gen 'algebra)
(for-each (lambda (n) (topic! n 'algebra))
          '(mal-outf-type mal-tout-type mal-inf-type mal-dist-type mal-red-type
            mar-outf-type mar-tout-type mar-gj-type mar-dist-type mar-red-type))
