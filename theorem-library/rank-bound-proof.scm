;;; rank-bound-proof.scm -- Proposition 3.41 (algebraic-numbers.pdf ch.3 sec 8.2),
;;; the payoff of the whole Smith arc:
;;;
;;;   md a module over a EUCLIDEAN ring, u a length-n generating sequence,
;;;   v a length-m relation-free sequence   |-   m <= n.
;;;
;;; In particular any two free generating sequences have the same length, so the
;;; RANK of a free module is well defined (Def 3.42).
;;;
;;; THE ARGUMENT.  Write v = cm . u for an m-by-n coefficient matrix cm
;;; (generates-coeff-matrix: the one choice step).  smith-diagonalization gives
;;; invertible U (m-by-m), V (n-by-n) with D = U.cm.V diagonal.  Put
;;;
;;;     W = V^-1,     u' = W . u,     v' = U . v.
;;;
;;; Then v' is relation-free (free-transport), and
;;;
;;;     D . u' = (D W) . u = ((U cm V) W) . u = ((U cm) (V W)) . u
;;;            = (U cm) . u = U . (cm . u) = U . v = v'
;;;
;;; -- three matact-assoc steps and one identmat-right-identity.  Suppose m > n.
;;; Row succ n of D is entirely off-diagonal (every column index j <= n is /= succ n),
;;; so D_{succ n, j} = 0 and v'_{succ n} = sum_j 0 . u'_j = 0 (module-zero-act +
;;; finsum-all-id).  Test relation-freeness of v' against the unit coefficient row
;;; e_{succ n} = UNITROW(A, m, succ n): its combination is 1 . v'_{succ n} = 0
;;; (finsum-single-support + module-act-unital), so REL-FREE forces the entry
;;; e_{succ n}[succ n] = 0.  But that entry is ONE.  So ONE = ZERO in the scalar
;;; ring, contradicting the nontriviality of an integral domain (a euclidean ring
;;; is one).  Hence m <= n.
;;;
;;; Note the divisibility chain of the full Smith form is NOT used -- only the
;;; DIAGONAL shape.  That is why dropping the chain in Phase B cost nothing here.
;;;
;;; REPAIRED 2026-09-16 (the SIZE/MAT change).  The statement is unchanged.
;;; generates-coeff-matrix now owes (n = 0 => m = 0), so the proof splits on
;;; n = 0 first.  If n = 0 and m = 0, m <= n is 0 <= 0.  If n = 0 and m >= 1,
;;; every vector is the empty combination LINCOMB(md,0,c,u) = 0 (lincomb-empty),
;;; so v_{1,1} = 0 and the same unit-row ending (rb-tail!, at row 1, against v
;;; itself) contradicts REL-FREE.  If n /= 0, the product guards of matact-type,
;;; matmul-type, matact-assoc and matmul-assoc at the shapes used below follow
;;; from NOT (n = 0) by `prop' (landed first, while the context is small), and
;;; matact-entry's (<= 1 n) comes from dk-one-le!.  REL-FREE now reads
;;; LINCOMB(md,m,e,W), reached by lincomb-unfold instead of matact-entry.

;; ---- proof-driver helpers (rb- prefix) ----
(define (rb-pg)(wff-formula (sequent-node-assertion (proof-state-focus *ps*))))
(define (rb-asms)(map wff-formula (sequent-node-assumptions (proof-state-focus *ps*))))
(define (rb-wf v b)(fold-right (lambda(x y)`(FORALL ,x ,y)) b v))
(define (rb-wi p b)(fold-right (lambda(x y)`(IMPLIES ,x ,y)) b p))
(define (rb-di*)(let lp()(let*((g(rb-pg))(h(and(pair? g)(car g))))(when(memq h '(FORALL IMPLIES))(di)(lp)))))
(define (rb-last)(car (reverse (dg-sequent-nodes (proof-state-dg *ps*)))))
(define (rb-goto! n)(dk-focus! n))
(define (rb-leaves)(filter (lambda(nd)(and(not(sequent-node-grounded? nd))(null?(sequent-node-in-arrows nd))))(dg-ungrounded-nodes(proof-state-dg *ps*))))
(define (rb-goalof l)(wff-formula(sequent-node-assertion l)))
(define (rb-focus! pred)(let lp((ls(rb-leaves)))(cond((null? ls)(error "rank-bound: no leaf"))((pred(rb-goalof(car ls)))(rb-goto! (car ls))(car ls))(else(lp(cdr ls))))))
(define (rb-find pred)
  (let ((r (filter pred (rb-asms))))
    (if (null? r) (error "rank-bound: no assumption matching") (car r))))
(define (rb-ai! pred) (ai (rb-find pred)))
(define (rH? h) (lambda (f) (and (pair? f) (eq? (car f) h))))

;; excluded middle on P (inline pbc + or-elim); returns the (NOT P) branch node,
;; leaving focus on the P branch.  (Same helper as matunit-shift-proof's mu-em.)
(define (rb-em P)
  (cut `(OR ,P (NOT ,P)))
  (let ((use-or (rb-last)))
    (pbc)
    (cut `(NOT ,P))
    (let ((use-notp (rb-last)))
      (di)
      (cut `(OR ,P (NOT ,P)))
      (let ((use-or2 (rb-last))) (oi-l) (ass) (rb-goto! use-or2))
      (ai `(NOT (OR ,P (NOT ,P))))
      (rb-goto! use-notp))
    (cut `(OR ,P (NOT ,P)))
    (let ((use-or3 (rb-last))) (oi-r) (ass) (rb-goto! use-or3))
    (ai `(NOT (OR ,P (NOT ,P))))
    (rb-goto! use-or)))
(define (rb-cases P) (rb-em P) (ai `(OR ,P (NOT ,P))) (rb-last))

;; the standard IS-INVERTIBLE-MAT decomposition (see mod-basis-proof.scm)
(define (rb-crack-inverse! X)
  (rb-ai! (lambda (f) (and (pair? f) (eq? (car f) 'AND)
                           (pair? (cadr f)) (eq? (caadr f) 'IN)
                           (eq? (cadr (cadr f)) X))))
  (rb-ai! (rH? 'FORSOME))
  (rb-ai! (lambda (f) (and (pair? f) (eq? (car f) 'AND)
                           (pair? (cadr f)) (eq? (caadr f) 'IN)
                           (pair? (caddr f)) (eq? (car (caddr f)) 'AND))))
  (rb-ai! (lambda (f) (and (pair? f) (eq? (car f) 'AND)
                           (pair? (cadr f)) (eq? (caadr f) '=)))))

(define RB-VAG '(MODULE-VECTOR-AG md))
(define (mm a b) `(MATMUL (SCAL md) ,a ,b))
(define (ma a b) `(MATACT md ,a ,b))
(define (invertible? d) (lambda (f) (and (pair? f) (eq? (car f) 'IS-INVERTIBLE-MAT)
                                         (eq? (caddr f) d))))

;; ---- the facts both cases land -------------------------------------------
(define (rb-common!)
  (fact 'module-scalar-ring 'md)
  (fact 'euclidean-ring-is-integral-domain '(SCAL md))
  (fact 'integral-domain-nontrivial '(SCAL md))
  (fact 'module-vector-ag-is-abelian-group 'md)
  (fact 'module-vzero-in 'md)
  (fact 'one-in-interval-1)
  (fact 'interval-in-set 1 'n)(fact 'interval-card-in-nn 1 'n)
  (fact 'interval-in-set 1 'm)(fact 'interval-card-in-nn 1 'm))

;; ---- the shared ending: a zero entry contradicts relation-freeness -------
;; Context: W in MAT(m,1,VEC md), (REL-FREE md m W), IDX in INTERVAL(1,m),
;; (= (ENTRY W IDX 1) (VZERO md)), and rb-common!'s facts.  The unit row
;; e = UNITROW(A,m,IDX) combines W to e_IDX . W_IDX = 1 . 0 = 0, so REL-FREE
;; forces e[1,IDX] = 0, i.e. ONE = ZERO in the scalar ring.  Closes the goal.
;; (2026-09-16: the combination is LINCOMB(md,m,e,W), reached by lincomb-unfold;
;; it was the (1,1) entry of MATACT(md,e,W), reached by matact-entry.  Factored
;; out of the m > n branch so that the n = 0 case can use it at IDX = 1.)
(define (rb-tail! W IDX)
  (let* ((ER `(UNITROW (SCAL md) m ,IDX))
         (FE `(VNB-LAMBDA j (INTERVAL 1 m) ((ACT md) (ENTRY ,ER 1 j) (ENTRY ,W j 1))))
         (LC `(LINCOMB md m ,ER ,W)))
    (fact 'unitrow-type '(SCAL md) 'm IDX)
    (cut `(= ,LC (VZERO md)))
    (let ((main5 (rb-last)))
      (fact 'lincomb-unfold 'md 'm ER W)
      (subst `(== ,LC (FINSUM ,RB-VAG ,FE (INTERVAL 1 m))))
      (fact 'matact-summand-type 'md 1 'm 1 ER W 1 1)
      (cut `(FORALL jz (IMPLIES (IN jz (INTERVAL 1 m))
              (IMPLIES (NOT (= jz ,IDX)) (= (,FE jz) (IDEN ,RB-VAG))))))
      (let ((main5b (rb-last)))
        (rb-di*)
        (lam-b)
        (fact 'unitrow-entry-off '(SCAL md) 'm IDX 'jz)
        (subst `(= (ENTRY ,ER 1 jz) (ZERO (SCAL md))))
        (fact 'entry-in-carrier 'm 1 '(VEC md) W 'jz 1)
        (fact 'module-zero-act 'md `(ENTRY ,W jz 1))
        (subst `(= ((ACT md) (ZERO (SCAL md)) (ENTRY ,W jz 1)) (VZERO md)))
        (fact 'mvag-id 'md)
        (subst `(= (IDEN ,RB-VAG) (VZERO md)))
        (rfl)
        (rb-goto! main5b))
      (fact 'finsum-single-support RB-VAG '(INTERVAL 1 m) FE IDX)
      (subst `(= (FINSUM ,RB-VAG ,FE (INTERVAL 1 m)) (,FE ,IDX)))
      (lam-b)
      (fact 'unitrow-entry-at '(SCAL md) 'm IDX)
      (subst `(= (ENTRY ,ER 1 ,IDX) (ONE (SCAL md))))
      (fact 'entry-in-carrier 'm 1 '(VEC md) W IDX 1)
      (fact 'module-act-unital 'md `(ENTRY ,W ,IDX 1))
      (subst `(= ((ACT md) (ONE (SCAL md)) (ENTRY ,W ,IDX 1)) (ENTRY ,W ,IDX 1)))
      (ass)
      (rb-goto! main5))
    ;; so e[1,IDX] = 0, i.e. ONE = ZERO.  Contradiction.
    (mac-h 'REL-FREE `(REL-FREE md m ,W))
    (inst+ (rb-find (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                     (let ((b (caddr f)))
                                       (and (pair? b) (eq? (car b) 'IMPLIES)
                                            (equal? (cadr b) `(IN ,(cadr f) (MAT 1 m (CARR (SCAL md))))))))))
           ER)
    (inst+ (rb-find (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                     (let ((b (caddr f)))
                                       (and (pair? b) (eq? (car b) 'IMPLIES)
                                            (pair? (caddr b)) (eq? (car (caddr b)) '=)
                                            (pair? (cadr (caddr b)))
                                            (eq? (car (cadr (caddr b))) 'ENTRY)
                                            (equal? (cadr (cadr (caddr b))) ER))))))
           IDX)
    (fact 'unitrow-entry-at '(SCAL md) 'm IDX)
    (fact 'eq-sym `(ENTRY ,ER 1 ,IDX) '(ONE (SCAL md)))
    (fact 'eq-trans '(ONE (SCAL md)) `(ENTRY ,ER 1 ,IDX) '(ZERO (SCAL md)))
    (ai '(NOT (= (ONE (SCAL md)) (ZERO (SCAL md)))))))

(sp (make-wff
  (rb-wf '(md) (rb-wi '((IS-MODULE md) (IS-EUCLIDEAN-RING (SCAL md)))
    (rb-wf '(n m u v) (rb-wi '((IN n NN) (IN m NN)
                               (IN u (MAT n 1 (VEC md)))
                               (IN v (MAT m 1 (VEC md)))
                               (GENERATES md n u)
                               (REL-FREE md m v))
      '(<= m n)))))))
(rb-di*)

;; ---- 2026-09-16: case n = 0 ----------------------------------------------
;; generates-coeff-matrix now owes (n = 0 => m = 0), so the empty generating
;; sequence is handled first.  If m = 0 too, m <= n is 0 <= 0.  Otherwise every
;; vector is the empty combination LINCOMB(md,0,c,u) = 0 (lincomb-empty), in
;; particular v_{1,1} = 0, and the shared ending at IDX = 1 refutes REL-FREE.
(use-em '(= n 0)
  (lambda ()
    (rb-common!)
    (use-em '(= m 0)
      (lambda ()
        (subst '(= m 0))
        (subst '(= n 0))
        (arith))
      (lambda ()
        (dk-one-le! 'm)
        (fact 'nn-one-in)
        (fact 'nn-le-refl 1)
        (fact 'interval-mem-intro 1 'm 1)
        (let ((RB-V11 '(ENTRY v 1 1)))
        (have! `(= ,RB-V11 (VZERO md))
          (lambda ()
            (fact 'entry-in-carrier 'm 1 '(VEC md) 'v 1 1)
            (mac-h 'GENERATES '(GENERATES md n u))
            (inst+ (rb-find (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                             (let ((b (caddr f)))
                                               (and (pair? b) (eq? (car b) 'IMPLIES)
                                                    (equal? (cadr b) `(IN ,(cadr f) (VEC md))))))))
                   RB-V11)
            (let ((c (dk-skolem! (rb-find (rH? 'FORSOME)))))
              (subst `(= ,RB-V11 (LINCOMB md n ,c u)))
              (subst '(= n 0))
              (fact 'lincomb-empty 'md c 'u)
              (ass))))
        (dk-focus-having! `(= ,RB-V11 (VZERO md)))
        (rb-tail! 'v 1)))))
  (lambda () #t))
(dk-focus-having! '(NOT (= n 0)))

;; ---- case n /= 0: the product guards, landed while the context is small ---
;; (matact-type at (n,n,1), (m,n,1), (m,m,1); matmul-type at (m,n,n), (m,m,n);
;; matact-assoc G1/G2 at (m,n,n,1) and (m,m,n,1); matmul-assoc G1/G2 at
;; (m,n,n,n); generates-coeff-matrix's (n = 0 => m = 0).)  All follow from
;; NOT (= n 0) or are tautologies.
(for-each dk-have-prop!
  '((IMPLIES (= n 0) (= m 0))
    (IMPLIES (= n 0) (OR (= n 0) (= 1 0)))
    (IMPLIES (= n 0) (OR (= m 0) (= 1 0)))
    (IMPLIES (= m 0) (OR (= m 0) (= 1 0)))
    (IMPLIES (= n 0) (OR (= m 0) (= n 0)))
    (IMPLIES (= m 0) (OR (= m 0) (= n 0)))
    (IMPLIES (= n 0) (OR (= m 0) (AND (= n 0) (= 1 0))))
    (IMPLIES (= n 0) (OR (= 1 0) (AND (= n 0) (= m 0))))
    (IMPLIES (= n 0) (OR (= m 0) (AND (= n 0) (= n 0))))
    (IMPLIES (= n 0) (OR (= n 0) (AND (= n 0) (= m 0))))
    (IMPLIES (= m 0) (OR (= m 0) (AND (= n 0) (= 1 0))))
    (IMPLIES (= n 0) (OR (= 1 0) (AND (= m 0) (= m 0))))))
(rb-common!)
(dk-one-le! 'n)                                    ; matact-entry's (<= 1 n)

;; ---- v = cm . u ----------------------------------------------------------
(fact 'generates-coeff-matrix 'md 'n 'm 'u 'v)
(rb-ai! (rH? 'FORSOME))
(rb-ai! (rH? 'AND))
(define RB-CM (cadr (rb-find (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                              (pair? (caddr f)) (eq? (car (caddr f)) 'MAT)
                                              (eq? (cadr (caddr f)) 'm)
                                              (eq? (caddr (caddr f)) 'n))))))
(define RB-VEQ (rb-find (lambda (f) (and (pair? f) (eq? (car f) '=) (eq? (cadr f) 'v)))))

;; ---- Smith: D = U.cm.V diagonal ------------------------------------------
(fact 'smith-diagonalization '(SCAL md) 'm 'n RB-CM)
(rb-ai! (rH? 'FORSOME))
(rb-ai! (rH? 'AND))
(define RB-MEQ (rb-find (rH? 'MAT-EQUIV)))
(define RB-D   (list-ref RB-MEQ 5))
(fact 'mat-equiv-target-is-mat '(SCAL md) 'm 'n RB-CM RB-D)
(mac-h 'MAT-EQUIV RB-MEQ)
(rb-ai! (rH? 'FORSOME))
(rb-ai! (lambda (f) (and (pair? f) (eq? (car f) 'AND)
                         (pair? (cadr f)) (eq? (caadr f) 'IS-INVERTIBLE-MAT)
                         (eq? (caddr (cadr f)) 'm))))
(rb-ai! (rH? 'FORSOME))
(rb-ai! (lambda (f) (and (pair? f) (eq? (car f) 'AND)
                         (pair? (cadr f)) (eq? (caadr f) 'IS-INVERTIBLE-MAT)
                         (eq? (caddr (cadr f)) 'n))))
(define RB-U (cadddr (rb-find (invertible? 'm))))
(define RB-V (cadddr (rb-find (invertible? 'n))))
(define RB-DEQ (rb-find (lambda (f) (and (pair? f) (eq? (car f) '=) (eq? (cadr f) RB-D)))))
;; typings of U and V (non-destructive projections; only V gets cracked below)
(fact 'invertible-mat-is-mat '(SCAL md) 'm RB-U)
(fact 'invertible-mat-is-mat '(SCAL md) 'n RB-V)

;; ---- W = V^-1, and W is invertible ---------------------------------------
(mac-h 'IS-INVERTIBLE-MAT (rb-find (invertible? 'n)))
(rb-crack-inverse! RB-V)
(define RB-W
  (let ((eq (rb-find (lambda (f) (and (pair? f) (eq? (car f) '=)
                                      (pair? (caddr f)) (eq? (car (caddr f)) 'IDENTMAT)
                                      (pair? (cadr f)) (eq? (caadr f) 'MATMUL)
                                      (eq? (caddr (cadr f)) RB-V))))))
    (cadddr (cadr eq))))                          ; (MATMUL A V W) = I

(cut `(IS-INVERTIBLE-MAT (SCAL md) n ,RB-W))
(define RB-MAIN1 (rb-last))
  (mac 'IS-INVERTIBLE-MAT)
  (di)
  (rb-focus! (rH? 'IN)) (ass)
  (rb-focus! (rH? 'FORSOME))
  (ew RB-V)
  (di)
  (rb-focus! (rH? 'IN)) (ass)
  (rb-focus! (rH? 'AND))
  (di)
  (rb-focus! (lambda (g) (and (pair? g) (eq? (car g) '=) (eq? (caddr (cadr g)) RB-W)))) (ass)
  (rb-focus! (lambda (g) (and (pair? g) (eq? (car g) '=) (eq? (caddr (cadr g)) RB-V)))) (ass)
(rb-goto! RB-MAIN1)

;; ---- u' = W.u, v' = U.v --------------------------------------------------
(define RB-UU (ma RB-W 'u))
(define RB-VP (ma RB-D RB-UU))
(define RB-VV (ma RB-U 'v))
(fact 'matact-type 'md 'n 'n 1 RB-W 'u)
(fact 'matact-type 'md 'm 'n 1 RB-D RB-UU)
(fact 'matact-type 'md 'm 'm 1 RB-U 'v)
(fact 'free-transport 'md 'm 'v RB-U)              ; v' is relation-free

;; ---- KEY:  D . u' = v' ---------------------------------------------------
(cut `(= ,RB-VP ,RB-VV))
(define RB-MAIN2 (rb-last))
  (fact 'matmul-type '(SCAL md) 'm 'n 'n RB-D RB-W)
  (fact 'matmul-type '(SCAL md) 'm 'm 'n RB-U RB-CM)
  (fact 'matact-assoc 'md 'm 'n 'n 1 RB-D RB-W 'u)
  (fact 'eq-sym (ma (mm RB-D RB-W) 'u) RB-VP)
  (subst `(= ,RB-VP ,(ma (mm RB-D RB-W) 'u)))
  (subst RB-DEQ)                                   ; D -> (U cm) V
  (fact 'matmul-assoc '(SCAL md) 'm 'n 'n 'n (mm RB-U RB-CM) RB-V RB-W)
  (subst `(= ,(mm (mm (mm RB-U RB-CM) RB-V) RB-W) ,(mm (mm RB-U RB-CM) (mm RB-V RB-W))))
  (subst `(= ,(mm RB-V RB-W) (IDENTMAT (SCAL md) n)))
  (fact 'identmat-right-identity '(SCAL md) 'm 'n (mm RB-U RB-CM))
  (subst `(= ,(mm (mm RB-U RB-CM) '(IDENTMAT (SCAL md) n)) ,(mm RB-U RB-CM)))
  (fact 'matact-assoc 'md 'm 'm 'n 1 RB-U RB-CM 'u)
  (subst `(= ,(ma (mm RB-U RB-CM) 'u) ,(ma RB-U (ma RB-CM 'u))))
  (subst RB-VEQ)                                   ; v -> cm . u
  (rfl)
(rb-goto! RB-MAIN2)

;; ---- excluded middle on (<= m n) -----------------------------------------
(define RB-NOTLE (rb-cases '(<= m n)))
(ass)                                              ; the (<= m n) branch
(rb-goto! RB-NOTLE)

(fact 'nn-not-le-succ-le 'm 'n)                    ; succ n <= m
(fact 'nn-succ-closed 'n)
(fact 'nn-one-le-succ 'n)
(fact 'interval-mem-intro 1 'm '(succ n))          ; succ n is a legal row index

;; ---- row succ n of D is zero, so v'_{succ n} = 0 -------------------------
(define RB-FD `(VNB-LAMBDA j (INTERVAL 1 n) ((ACT md) (ENTRY ,RB-D (succ n) j) (ENTRY ,RB-UU j 1))))
(cut `(= (ENTRY ,RB-VP (succ n) 1) (VZERO md)))
(define RB-MAIN3 (rb-last))
  (fact 'matact-entry 'md 'm 'n 1 RB-D RB-UU '(succ n) 1)
  (subst `(= (ENTRY ,RB-VP (succ n) 1) (FINSUM ,RB-VAG ,RB-FD (INTERVAL 1 n))))
  (fact 'matact-summand-type 'md 'm 'n 1 RB-D RB-UU '(succ n) 1)
  (cut `(FORALL jz (IMPLIES (IN jz (INTERVAL 1 n)) (= (,RB-FD jz) (IDEN ,RB-VAG)))))
  (define RB-MAIN3b (rb-last))
    (rb-di*)
    (lam-b)
    (fact 'interval-elt-in-nn 1 'n 'jz)
    (fact 'interval-hi 1 'n 'jz)
    (fact 'nn-le-imp-neq-succ 'n 'jz)              ; NOT (= jz (succ n))
    (fact 'neq-sym 'jz '(succ n))                  ; NOT (= (succ n) jz)
    (fact 'diagonal-off-entry '(SCAL md) 'm 'n RB-D '(succ n) 'jz)
    (subst `(= (ENTRY ,RB-D (succ n) jz) (ZERO (SCAL md))))
    (fact 'entry-in-carrier 'n 1 '(VEC md) RB-UU 'jz 1)
    (fact 'module-zero-act 'md `(ENTRY ,RB-UU jz 1))
    (subst `(= ((ACT md) (ZERO (SCAL md)) (ENTRY ,RB-UU jz 1)) (VZERO md)))
    (fact 'mvag-id 'md)
    (subst `(= (IDEN ,RB-VAG) (VZERO md)))
    (rfl)
  (rb-goto! RB-MAIN3b)
  (fact 'finsum-all-id RB-VAG '(INTERVAL 1 n) RB-FD)
  (subst `(= (FINSUM ,RB-VAG ,RB-FD (INTERVAL 1 n)) (IDEN ,RB-VAG)))
  (fact 'mvag-id 'md)
  (ass)
(rb-goto! RB-MAIN3)

(cut `(= (ENTRY ,RB-VV (succ n) 1) (VZERO md)))
(define RB-MAIN4 (rb-last))
  (fact 'eq-sym RB-VP RB-VV)
  (subst `(= ,RB-VV ,RB-VP))
  (ass)
(rb-goto! RB-MAIN4)

;; ---- test relation-freeness of v' against the unit row e_{succ n} --------
(rb-tail! RB-VV '(succ n))

(qed 'free-length-le-generators)
(topic! 'free-length-le-generators 'algebra)
(topic! 'integral-domain-nontrivial 'algebra)
(topic! 'interval-mem-intro 'plumbing)
(topic! 'nn-not-le-succ-le 'inequalities)
(topic! 'nn-one-le-succ 'inequalities)
