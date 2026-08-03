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

;; ---- proof-driver helpers (rb- prefix) ----
(define (rb-pg)(wff-formula (sequent-node-assertion (proof-state-focus *ps*))))
(define (rb-asms)(map wff-formula (sequent-node-assumptions (proof-state-focus *ps*))))
(define (rb-wf v b)(fold-right (lambda(x y)`(FORALL ,x ,y)) b v))
(define (rb-wi p b)(fold-right (lambda(x y)`(IMPLIES ,x ,y)) b p))
(define (rb-di*)(let lp()(let*((g(rb-pg))(h(and(pair? g)(car g))))(when(memq h '(FORALL IMPLIES))(di)(lp)))))
(define (rb-last)(car (reverse (dg-sequent-nodes (proof-state-dg *ps*)))))
(define (rb-goto! n)(set-proof-state-focus! *ps* n))
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

(sp (make-wff
  (rb-wf '(md) (rb-wi '((IS-MODULE md) (IS-EUCLIDEAN-RING (SCAL md)))
    (rb-wf '(n m u v) (rb-wi '((IN n NN) (IN m NN)
                               (IN u (MAT n 1 (VEC md)))
                               (IN v (MAT m 1 (VEC md)))
                               (GENERATES md n u)
                               (REL-FREE md m v))
      '(<= m n)))))))
(rb-di*)
(fact 'module-scalar-ring 'md)
(fact 'euclidean-ring-is-integral-domain '(SCAL md))
(fact 'integral-domain-nontrivial '(SCAL md))
(fact 'module-vector-ag-is-abelian-group 'md)
(fact 'module-vzero-in 'md)
(fact 'one-in-interval-1)
(fact 'interval-in-set 1 'n)(fact 'interval-card-in-nn 1 'n)
(fact 'interval-in-set 1 'm)(fact 'interval-card-in-nn 1 'm)

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
(fact 'mat-equiv-cod-is-mat '(SCAL md) 'm 'n RB-CM RB-D)
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
    (di)(di)
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
(define RB-ER `(UNITROW (SCAL md) m (succ n)))
(define RB-FE `(VNB-LAMBDA j (INTERVAL 1 m) ((ACT md) (ENTRY ,RB-ER 1 j) (ENTRY ,RB-VV j 1))))
(fact 'unitrow-type '(SCAL md) 'm '(succ n))

(cut `(= (ENTRY ,(ma RB-ER RB-VV) 1 1) (VZERO md)))
(define RB-MAIN5 (rb-last))
  (fact 'matact-entry 'md 1 'm 1 RB-ER RB-VV 1 1)
  (subst `(= (ENTRY ,(ma RB-ER RB-VV) 1 1) (FINSUM ,RB-VAG ,RB-FE (INTERVAL 1 m))))
  (fact 'matact-summand-type 'md 1 'm 1 RB-ER RB-VV 1 1)
  (cut `(FORALL jz (IMPLIES (IN jz (INTERVAL 1 m))
          (IMPLIES (NOT (= jz (succ n))) (= (,RB-FE jz) (IDEN ,RB-VAG))))))
  (define RB-MAIN5b (rb-last))
    (di)(di)(di)
    (lam-b)
    (fact 'unitrow-entry-off '(SCAL md) 'm '(succ n) 'jz)
    (subst `(= (ENTRY ,RB-ER 1 jz) (ZERO (SCAL md))))
    (fact 'entry-in-carrier 'm 1 '(VEC md) RB-VV 'jz 1)
    (fact 'module-zero-act 'md `(ENTRY ,RB-VV jz 1))
    (subst `(= ((ACT md) (ZERO (SCAL md)) (ENTRY ,RB-VV jz 1)) (VZERO md)))
    (fact 'mvag-id 'md)
    (subst `(= (IDEN ,RB-VAG) (VZERO md)))
    (rfl)
  (rb-goto! RB-MAIN5b)
  (fact 'finsum-single-support RB-VAG '(INTERVAL 1 m) RB-FE '(succ n))
  (subst `(= (FINSUM ,RB-VAG ,RB-FE (INTERVAL 1 m)) (,RB-FE (succ n))))
  (lam-b)
  (fact 'unitrow-entry-at '(SCAL md) 'm '(succ n))
  (subst `(= (ENTRY ,RB-ER 1 (succ n)) (ONE (SCAL md))))
  (fact 'entry-in-carrier 'm 1 '(VEC md) RB-VV '(succ n) 1)
  (fact 'module-act-unital 'md `(ENTRY ,RB-VV (succ n) 1))
  (subst `(= ((ACT md) (ONE (SCAL md)) (ENTRY ,RB-VV (succ n) 1)) (ENTRY ,RB-VV (succ n) 1)))
  (ass)
(rb-goto! RB-MAIN5)

;; ---- so e_{succ n}[succ n] = 0, i.e. ONE = ZERO.  Contradiction. --------
(mac-h 'REL-FREE `(REL-FREE md m ,RB-VV))
(inst+ (rb-find (lambda (f) (and (pair? f) (eq? (car f) 'FORALL) (pair? (caddr f))
                                 (eq? (car (caddr f)) 'IMPLIES)
                                 (pair? (cadr (caddr f)))
                                 (eq? (car (cadr (caddr f))) 'IN)
                                 (pair? (caddr (cadr (caddr f))))
                                 (eq? (car (caddr (cadr (caddr f)))) 'MAT))))
       RB-ER)
(inst+ (rb-find (lambda (f) (and (pair? f) (eq? (car f) 'FORALL) (pair? (caddr f))
                                 (eq? (car (caddr f)) 'IMPLIES)
                                 (pair? (caddr (caddr f)))
                                 (eq? (car (caddr (caddr f))) '=)
                                 (pair? (cadr (caddr (caddr f))))
                                 (eq? (car (cadr (caddr (caddr f)))) 'ENTRY))))
       '(succ n))
(fact 'unitrow-entry-at '(SCAL md) 'm '(succ n))
(fact 'eq-sym `(ENTRY ,RB-ER 1 (succ n)) '(ONE (SCAL md)))
(fact 'eq-trans '(ONE (SCAL md)) `(ENTRY ,RB-ER 1 (succ n)) '(ZERO (SCAL md)))
(ai '(NOT (= (ONE (SCAL md)) (ZERO (SCAL md)))))

(qed 'free-length-le-generators)
(category! 'free-length-le-generators 'algebra)
(category! 'integral-domain-nontrivial 'algebra)
(category! 'interval-mem-intro 'plumbing)
(category! 'nn-not-le-succ-le 'inequalities)
(category! 'nn-one-le-succ 'inequalities)
