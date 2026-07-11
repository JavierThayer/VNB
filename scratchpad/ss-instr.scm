;;; smith-staircase-proof.scm -- the Smith normal form with its nonzero diagonal
;;; entries recorded as an INITIAL SEGMENT.
;;;
;;;   border-staircase   D' staircase at k', b /= 0  =>  BORDER(A,b,D',p,q) staircase
;;;                      at succ k'
;;;   smith-staircase    every P in MAT(m,n) over a euclidean ring is ~-equivalent to
;;;                      a D with SMITH-STAIRCASE(A,m,n,D,k) for some k
;;;
;;; This is smith-diagonalization with a strengthened induction invariant.  The
;;; property was ALREADY true of the construction -- clear-pivot-cross always selects
;;; a NONZERO pivot, so each BORDER level contributes a nonzero diagonal entry at the
;;; front and the zeros are pushed to the tail -- the old statement simply did not
;;; record it.  Recording it is what lets a caller take the leading k rows of D
;;; without having to enumerate {i : D_ii /= 0} in increasing order.
;;;
;;; INNER(K) = forall n P, exists D and kk in NN with P ~ D and SMITH-STAIRCASE(A,K,n,D,kk).
;;; Both degenerate branches (K=0; n=0) and the all-zero branch give kk = 0; the
;;; recursive branch gives kk = succ kk' from the IH's kk'.
;;;
;;; The three "kk = 0" branches share conj2..conj4 of SMITH-STAIRCASE (0 <= m, 0 <= n,
;;; and the vacuous nonzero-clause over the empty interval [1,0]); only conj1
;;; (IS-DIAGONAL) and conj5 (rows past 0 vanish) are branch-specific.

;; ---- proof-driver helpers (ss- prefix) ----
(define (ss-goal) (wff-formula (sequent-node-assertion (proof-state-focus *ps*))))
(define (ss-last) (car (reverse (dg-sequent-nodes (proof-state-dg *ps*)))))
(define (ss-foc! n) (set-proof-state-focus! *ps* n))
(define (ss-find pred) (let lp ((as (map wff-formula (sequent-node-assumptions (proof-state-focus *ps*)))))
  (cond ((null? as) #f) ((pred (car as)) (car as)) (else (lp (cdr as))))))
(define (ss-foc-goal! pred)
  (let ((s (any-pred (lambda (s) (pred (wff-formula (sequent-node-assertion s)))) (proof-leaves))))
    (and s (set-proof-state-focus! *ps* s) s)))
(define (SH? h) (lambda (g) (and (pair? g) (eq? (car g) h))))
(define (ss-di*) (let lp () (let* ((g (ss-goal)) (h (and (pair? g) (car g))))
                   (when (memq h '(FORALL IMPLIES)) (di) (lp)))))
(define (ss-em P)
  (cut `(OR ,P (NOT ,P)))
  (let ((use-or (ss-last)))
    (pbc) (cut `(NOT ,P))
    (let ((use-notp (ss-last)))
      (di) (cut `(OR ,P (NOT ,P)))
      (let ((u2 (ss-last))) (oi-l) (ass) (ss-foc! u2))
      (ai `(NOT (OR ,P (NOT ,P)))) (ss-foc! use-notp))
    (cut `(OR ,P (NOT ,P)))
    (let ((u3 (ss-last))) (oi-r) (ass) (ss-foc! u3))
    (ai `(NOT (OR ,P (NOT ,P)))) (ss-foc! use-or)))
(define (ss-cases P) (ss-em P) (ai `(OR ,P (NOT ,P))) (ss-last))
(define BCPORT (open-output-file "/home/ubuntu/prover/scratchpad/BC.txt"))
(define (BC tag) (write-string tag BCPORT)(newline BCPORT)(flush-output BCPORT))

;; the two FORALL conjuncts of an unfolded SMITH-STAIRCASE hypothesis
(define (ss-nz-forall? f)                  ; forall i_ in [1,k]: D_ii /= 0
  (and (pair? f) (eq? (car f) 'FORALL) (pair? (caddr f)) (eq? (car (caddr f)) 'IMPLIES)
       (pair? (caddr (caddr f))) (eq? (car (caddr (caddr f))) 'NOT)))
(define (ss-row-forall? f)                 ; forall i_ in [1,m]: i_ > k => row i_ zero
  (and (pair? f) (eq? (car f) 'FORALL) (pair? (caddr f)) (eq? (car (caddr f)) 'IMPLIES)
       (pair? (caddr (caddr f))) (eq? (car (caddr (caddr f))) 'IMPLIES)))
;; the corresponding GOAL leaves after (mac 'SMITH-STAIRCASE)
(define (ss-nz-goal? g) (ss-nz-forall? g))
(define (ss-row-goal? g) (ss-row-forall? g))

;; the contradiction closing any goal under an index in the empty interval [1,0]
(define (ss-empty-interval! iv)
  (fact 'interval-lo 1 0 iv) (fact 'interval-hi 1 0 iv) (fact 'interval-elt-in-nn 1 0 iv)
  (fact 'nn-not-le-zero-pos iv)
  (ai (list 'NOT (list '<= iv 0))))

;; =====================================================================
;; border-staircase
;; =====================================================================
(define BS-BRD '(BORDER A b W p q))

(sp (make-wff
  '(FORALL A (IMPLIES (IS-RING A)
     (FORALL b (FORALL W (FORALL p (FORALL q (FORALL kp
       (IMPLIES (IN p NN)
       (IMPLIES (IN q NN)
       (IMPLIES (IN kp NN)
       (IMPLIES (IN b (CARR A))
       (IMPLIES (NOT (= b (ZERO A)))
       (IMPLIES (SMITH-STAIRCASE A p q W kp)
         (SMITH-STAIRCASE A (succ p) (succ q) (BORDER A b W p q) (succ kp)))))))))))))))))
(ss-di*)
(fact 'nn-succ-closed 'p) (fact 'nn-succ-closed 'q) (fact 'nn-succ-closed 'kp)

;; decompose the staircase hypothesis on W
(mac-h 'SMITH-STAIRCASE '(SMITH-STAIRCASE A p q W kp))
(ai (ss-find (lambda (f) (and (pair? f) (eq? (car f) 'AND) (pair? (cadr f)) (eq? (caadr f) 'IS-DIAGONAL)))))
(ai (ss-find (lambda (f) (and (pair? f) (eq? (car f) 'AND) (equal? (cadr f) '(<= kp p))))))
(ai (ss-find (lambda (f) (and (pair? f) (eq? (car f) 'AND) (equal? (cadr f) '(<= kp q))))))
(ai (ss-find (lambda (f) (and (pair? f) (eq? (car f) 'AND) (ss-nz-forall? (cadr f))))))
(define BS-F1 (ss-find ss-nz-forall?))
(define BS-F2 (ss-find ss-row-forall?))

(mac 'SMITH-STAIRCASE)
(di)
;; conj 1: diagonal
(ss-foc-goal! (SH? 'IS-DIAGONAL))
(fact 'border-is-diagonal 'A 'b 'W 'p 'q)
(ass)
;; conj 2: succ kp <= succ p
(ss-foc-goal! (SH? 'AND)) (di)
(ss-foc-goal! (lambda (g) (and (pair? g) (eq? (car g) '<=) (equal? (caddr g) '(succ p)))))
(fact 'nn-succ-mono 'kp 'p) (ass)
;; conj 3: succ kp <= succ q
(ss-foc-goal! (SH? 'AND)) (di)
(ss-foc-goal! (lambda (g) (and (pair? g) (eq? (car g) '<=) (equal? (caddr g) '(succ q)))))
(fact 'nn-succ-mono 'kp 'q) (ass)
(ss-foc-goal! (SH? 'AND)) (di)

;; conj 4: the leading succ kp diagonal entries are nonzero
(ss-foc-goal! ss-nz-goal?)
(di)(di)
(fact 'interval-elt-in-nn 1 '(succ kp) 'i_)
(fact 'interval-lo 1 '(succ kp) 'i_)
(fact 'interval-hi 1 '(succ kp) 'i_)
(fact 'nn-succ-mono 'kp 'p) (fact 'nn-succ-mono 'kp 'q)
(fact 'nn-le-trans 'i_ '(succ kp) '(succ p))
(fact 'nn-le-trans 'i_ '(succ kp) '(succ q))
(fact 'interval-mem-intro 1 '(succ p) 'i_)
(fact 'interval-mem-intro 1 '(succ q) 'i_)
;; NOTE: the two (di)s above ALREADY landed on `falsity'.  VNB's di on
;; (IMPLIES guard (NOT X)) introduces the guard AND X, so E1 : BRD_{i_,i_} = 0 is
;; already a hypothesis and the goal is falsity.  Do NOT add a third (di), and do
;; not aim subst/ass at a NOT-shaped goal here -- both branches close by not-elim.
(define BS-NB1 (ss-cases '(= i_ 1)))
;; i_ = 1: the corner is b, which is nonzero by hypothesis
(fact 'border-entry-11 'A 'b 'W 'p 'q)   ; (= BRD_{1,1} b)
(fact 'eq-sym 'i_ 1)                     ; (= 1 i_)
(cut `(= (ENTRY ,BS-BRD 1 1) (ZERO A)))
(define BS-CB1 (ss-last))
  (subst '(= 1 i_))                      ; goal -> (= BRD_{i_,i_} 0), which is E1
  (ass)
(ss-foc! BS-CB1)
(fact 'eq-sym `(ENTRY ,BS-BRD 1 1) 'b)   ; (= b BRD_{1,1})
(fact 'eq-trans 'b `(ENTRY ,BS-BRD 1 1) '(ZERO A))
(ai '(NOT (= b (ZERO A))))
;; i_ /= 1: the entry is W_{i-1,i-1}, nonzero since i-1 in [1,kp]
(ss-foc! BS-NB1)
(fact 'pred-in-interval 'kp 'i_)
(fact 'border-entry-block2 'A 'b 'W 'p 'q 'i_ 'i_)
(inst+ BS-F1 '(NN-MINUS i_ 1))           ; NOT (= W_{z,z} 0)
(fact 'eq-sym `(ENTRY ,BS-BRD i_ i_) `(ENTRY W (NN-MINUS i_ 1) (NN-MINUS i_ 1)))
(fact 'eq-trans `(ENTRY W (NN-MINUS i_ 1) (NN-MINUS i_ 1)) `(ENTRY ,BS-BRD i_ i_) '(ZERO A))
(ai `(NOT (= (ENTRY W (NN-MINUS i_ 1) (NN-MINUS i_ 1)) (ZERO A))))

;; conj 5: every row past succ kp vanishes
(ss-foc-goal! ss-row-goal?)
(di)(di)(di)(di)(di)                     ; i_, IN i_, NOT(i_ <= succ kp), j_, IN j_
(fact 'interval-elt-in-nn 1 '(succ p) 'i_)
(fact 'interval-lo 1 '(succ p) 'i_)
;; i_ /= 1 (else i_ = 1 <= succ kp)
(define BS-NB2 (ss-cases '(= i_ 1)))
(cut '(<= i_ (succ kp)))
(define BS-C1 (ss-last))
  (subst '(= i_ 1)) (fact 'nn-one-le-succ 'kp) (ass)
(ss-foc! BS-C1)
(ai '(NOT (<= i_ (succ kp))))
;; the real branch
(ss-foc! BS-NB2)
(fact 'pred-in-interval 'p 'i_)
(fact 'interval-elt-in-nn 1 'p '(NN-MINUS i_ 1))
;; NOT (i_-1 <= kp)  (else succ(i_-1) = i_ <= succ kp)
(define BS-NB3 (ss-cases '(<= (NN-MINUS i_ 1) kp)))
(fact 'nn-succ-mono '(NN-MINUS i_ 1) 'kp)
(fact 'succ-nn-minus-1 'i_)
(cut '(<= i_ (succ kp)))
(define BS-C2 (ss-last))
  (fact 'eq-sym '(succ (NN-MINUS i_ 1)) 'i_)
  (subst '(= i_ (succ (NN-MINUS i_ 1))))
  (ass)
(ss-foc! BS-C2)
(ai '(NOT (<= i_ (succ kp))))
;; NOT (i_-1 <= kp): split on the column
(ss-foc! BS-NB3)
(define BS-NB4 (ss-cases '(= j_ 1)))
;; j_ = 1: first column below the corner is zero
(subst '(= j_ 1))
(fact 'border-entry-i1 'A 'b 'W 'p 'q 'i_)
(ass)
;; j_ /= 1: the entry is M_{i-1,j-1}, zero by W's row clause
(ss-foc! BS-NB4)
(fact 'pred-in-interval 'q 'j_)
(fact 'border-entry-block2 'A 'b 'W 'p 'q 'i_ 'j_)
(subst `(= (ENTRY ,BS-BRD i_ j_) (ENTRY W (NN-MINUS i_ 1) (NN-MINUS j_ 1))))
(inst+ BS-F2 '(NN-MINUS i_ 1))
(inst+ (ss-find (lambda (f) (and (pair? f) (eq? (car f) 'FORALL) (eq? (cadr f) 'j_)
                                 (pair? (caddr f)) (eq? (car (caddr f)) 'IMPLIES)
                                 (pair? (caddr (caddr f))) (eq? (car (caddr (caddr f))) '=))))
       '(NN-MINUS j_ 1))
(ass)
(qed 'border-staircase)
(category! 'border-staircase 'algebra)

;; =====================================================================
;; smith-staircase
;; =====================================================================
;; INNER(K): forall n P, IN n NN => IN P (MAT K n carr) =>
;;             exists D, exists kk in NN, P ~ D and SMITH-STAIRCASE(A,K,n,D,kk)
(define (INNER2 K)
  (list 'FORALL 'n (list 'FORALL 'P
    (list 'IMPLIES (list 'IN 'n 'NN)
      (list 'IMPLIES (list 'IN 'P (list 'MAT K 'n '(CARR A)))
        (list 'FORSOME 'D (list 'FORSOME 'kk
          (list 'AND (list 'IN 'kk 'NN)
            (list 'AND (list 'MAT-EQUIV 'A K 'n 'P 'D)
                       (list 'SMITH-STAIRCASE 'A K 'n 'D 'kk))))))))))

;; the shared "kk = 0" conjuncts: (IN 0 NN), (<= 0 rowdim), (<= 0 coldim), and the
;; vacuous nonzero-clause over [1,0].  Leaves conj1/conj5 focused for the caller.
(define (ss-zero-witness! rowdim coldim)
  (ew 'P) (ew 0) (di)
  (ss-foc-goal! (lambda (g) (equal? g '(IN 0 NN))))
  (fact 'nn-zero-in) (ass)
  (ss-foc-goal! (SH? 'AND)) (di)
  (ss-foc-goal! (SH? 'MAT-EQUIV))
  (fact 'mat-equiv-refl 'A rowdim coldim 'P) (ass)
  (ss-foc-goal! (SH? 'SMITH-STAIRCASE))
  (mac 'SMITH-STAIRCASE)
  (di)
  (ss-foc-goal! (SH? 'AND)) (di)
  (ss-foc-goal! (lambda (g) (and (pair? g) (eq? (car g) '<=) (equal? (caddr g) rowdim))))
  (fact 'nn-zero-le rowdim) (ass)
  (ss-foc-goal! (SH? 'AND)) (di)
  (ss-foc-goal! (lambda (g) (and (pair? g) (eq? (car g) '<=) (equal? (caddr g) coldim))))
  (fact 'nn-zero-le coldim) (ass)
  (ss-foc-goal! (SH? 'AND)) (di)
  (ss-foc-goal! ss-nz-goal?)
  (di)(di)
  (ss-empty-interval! 'i_))

(sp (make-wff
  (list 'FORALL 'A (list 'IMPLIES '(IS-EUCLIDEAN-RING A)
    (list 'FORALL 'k (list 'IMPLIES '(IN k NN) (INNER2 'k)))))))
(let lp () (let* ((g (ss-goal)) (h (and (pair? g) (car g))))
  (when (and (memq h '(FORALL IMPLIES)) (not (and (eq? h 'FORALL) (eq? (cadr g) 'k))))
    (di) (lp))))
(fact 'euclidean-ring-is-integral-domain 'A)
(fact 'integral-domain-is-commutative-ring 'A)
(fact 'commutative-ring-is-ring 'A)
(ni)

(BC "phase-BASE")
;; ===== BASE : INNER2(0) -- no rows at all, kk = 0 =====
(ss-foc-goal! (lambda (g) (and (pair? g) (eq? (car g) 'FORALL) (eq? (cadr g) 'n))))
(ss-di*)
(fact 'nn-zero-in)
(ss-zero-witness! 0 'n)
;; conj1: IS-DIAGONAL over an empty row range
(ss-foc-goal! (SH? 'IS-DIAGONAL))
(mac 'IS-DIAGONAL) (ss-di*)
(ss-empty-interval! (caddr (cadr (ss-goal))))
;; conj5: rows past 0 -- also an empty row range
(ss-foc-goal! ss-row-goal?)
(di)(di)
(ss-empty-interval! 'i_)

(BC "phase-STEP")
;; ===== STEP : INNER2(k) => INNER2(succ k) =====
(ss-foc-goal! (lambda (g) (and (pair? g) (eq? (car g) 'FORALL) (eq? (cadr g) 'k))))
(ss-di*)
(fact 'nn-succ-closed 'k)
(fact 'nn-zero-in)
(define SS-IH (ss-find (lambda (z) (and (pair? z) (eq? (car z) 'FORALL) (eq? (cadr z) 'n)
            (pair? (caddr z)) (eq? (car (caddr z)) 'FORALL)))))
(define SS-NLE1 (ss-cases '(<= 1 n)))

(BC "phase-NLE1")
;; --- NOT(1<=n): no columns.  D = P, kk = 0 ---
(ss-foc! SS-NLE1)
(ss-zero-witness! '(succ k) 'n)
(ss-foc-goal! (SH? 'IS-DIAGONAL))
(mac 'IS-DIAGONAL) (ss-di*)
(define SS-SBj (cadddr (cadr (ss-goal))))
(fact 'interval-lo 1 'n SS-SBj) (fact 'interval-hi 1 'n SS-SBj)
(fact 'nn-le-trans 1 SS-SBj 'n)
(ai '(NOT (<= 1 n)))
(ss-foc-goal! ss-row-goal?)
(di)(di)(di)(di)(di)                     ; i_, IN i_, NOT(i_<=0), j_, IN j_ [1,n]
(fact 'interval-lo 1 'n 'j_) (fact 'interval-hi 1 'n 'j_)
(fact 'nn-le-trans 1 'j_ 'n)
(ai '(NOT (<= 1 n)))

(BC "phase-1len")
;; --- 1<=n : n = succ q, then the pivot dance ---
(ss-foc-goal! (SH? 'FORSOME))
(fact 'nn-pos-is-succ 'n)
(define SS-PSB (ss-find (lambda (z) (and (pair? z) (eq? (car z) 'FORSOME) (eq? (cadr z) 'q)))))
(ai SS-PSB) (ai 1)
(BC "before-SS-NEQ")
(define SS-NEQ (ss-find (lambda (z) (and (pair? z) (eq? (car z) '=) (equal? (cadr z) 'n)
             (pair? (caddr z)) (eq? (car (caddr z)) 'succ)))))
(BC "before-SS-Q(cadr-caddr-NEQ)")
(define SS-Q (cadr (caddr SS-NEQ)))
(define SS-SQN (list 'succ SS-Q))
(fact 'eq-sym 'n SS-SQN)
(subst (list '= 'n SS-SQN))
(cut (list 'IN 'P (list 'MAT '(succ k) SS-SQN '(CARR A))))
(subst (list '= SS-SQN 'n)) (ass)
(define SS-NZk (list 'FORSOME 'i0 (list 'FORSOME 'j0
   (list 'AND (list 'IN 'i0 (list 'INTERVAL 1 '(succ k)))
     (list 'AND (list 'IN 'j0 (list 'INTERVAL 1 SS-SQN))
       (list 'NOT (list '= '(ENTRY P i0 j0) '(ZERO A))))))))
(define SS-NNZ (ss-cases SS-NZk))

(BC "phase-nonzero")
;; ===== nonzero: clear-pivot-cross + IH + bordering + border-staircase =====
(fact 'clear-pivot-cross 'A 'k SS-Q 'P)
(quietly (lambda () (detach! SS-NZk)))
(BC "before-SS-CPC")
(define SS-CPC (ss-find (lambda (z) (and (pair? z) (eq? (car z) 'FORSOME) (eq? (cadr z) 'C2)))))
(ai SS-CPC) (ai 1) (ai 1)
(BC "before-SS-C2(listref)")
(begin
  (write-string "--- ASMS at SS-C2 ---" BCPORT)(newline BCPORT)
  (for-each (lambda (f)
    (when (and (pair? f) (memq (car f) '(MAT-EQUIV FORSOME AND)))
      (write f BCPORT)(newline BCPORT)))
    (map wff-formula (sequent-node-assumptions (proof-state-focus *ps*))))
  (write-string "--- end ---" BCPORT)(newline BCPORT)(flush-output BCPORT))
(define SS-C2 (list-ref (ss-find (lambda (z) (and (pair? z) (eq? (car z) 'MAT-EQUIV) (equal? (list-ref z 4) 'P)))) 5))
(define SS-SUB (list 'SUBMAT SS-C2 'k SS-Q))
(define SS-B11 (list 'ENTRY SS-C2 1 1))
(fact 'mat-equiv-cod-is-mat 'A '(succ k) SS-SQN 'P SS-C2)
(fact 'submat-type 'A 'k SS-Q SS-C2)
(BC "before-SS-IHn")
(define SS-IHn (ss-find (lambda (z) (and (pair? z) (eq? (car z) 'FORALL) (eq? (cadr z) 'n)
   (let ((c (caddr z))) (and (pair? c) (eq? (car c) 'FORALL)
     (let ((b (caddr c))) (and (pair? b) (eq? (car b) 'IMPLIES) (equal? (cadr b) '(IN n NN))))))))))
(inst+ SS-IHn SS-Q)
(BC "before-SS-IHp")
(define SS-IHp (ss-find (lambda (z) (and (pair? z) (eq? (car z) 'FORALL) (eq? (cadr z) 'P)
   (let ((b (caddr z))) (and (pair? b) (eq? (car b) 'IMPLIES) (equal? (cadr b) (list 'IN SS-Q 'NN))))))))
(inst+ SS-IHp SS-SUB)
(BC "before-SS-IHBODY")
(define SS-IHBODY (ss-find (lambda (z) (and (pair? z) (eq? (car z) 'FORSOME) (eq? (cadr z) 'D)))))
(ai SS-IHBODY)
(BC "before-SS-IHKK")
(define SS-IHKK (ss-find (lambda (z) (and (pair? z) (eq? (car z) 'FORSOME) (eq? (cadr z) 'kk)))))
(ai SS-IHKK) (ai 1) (ai 1)
(BC "before-SS-DP(listref)")
(define SS-DP (list-ref (ss-find (lambda (z) (and (pair? z) (eq? (car z) 'MAT-EQUIV) (equal? (list-ref z 4) SS-SUB)))) 5))
(BC "before-SS-KP(listref)")
(define SS-KP (list-ref (ss-find (lambda (z) (and (pair? z) (eq? (car z) 'SMITH-STAIRCASE) (equal? (list-ref z 4) SS-DP)))) 5))
;; b = C2_11 nonzero, in CARR A ; D' typed by mat-equiv-cod-is-mat
(fact 'one-in-interval 'k) (fact 'one-in-interval SS-Q)
(fact 'entry-in-carrier '(succ k) SS-SQN '(CARR A) SS-C2 1 1)
(fact 'mat-equiv-cod-is-mat 'A 'k SS-Q SS-SUB SS-DP)
(fact 'nn-succ-closed SS-KP)
;; C2 ~ BORDER(b, D') ~ P, and the border is a staircase at succ kk'
(fact 'bordering 'A 'k SS-Q SS-B11 SS-SUB SS-C2 SS-DP)
(define SS-BRD (list 'BORDER 'A SS-B11 SS-DP 'k SS-Q))
(fact 'mat-equiv-trans 'A '(succ k) SS-SQN 'P SS-C2 SS-BRD)
(fact 'border-staircase 'A SS-B11 SS-DP 'k SS-Q SS-KP)
(ew SS-BRD) (ew (list 'succ SS-KP)) (di)
(ss-foc-goal! (lambda (g) (and (pair? g) (eq? (car g) 'IN) (equal? (caddr g) 'NN)))) (ass)
(ss-foc-goal! (SH? 'AND)) (di)
(ss-foc-goal! (lambda (g) (and (pair? g) (eq? (car g) 'MAT-EQUIV) (equal? (list-ref g 4) 'P)))) (ass)
(ss-foc-goal! (SH? 'SMITH-STAIRCASE)) (ass)

(BC "phase-zero")
;; ===== zero: no nonzero entry => P is already a staircase at 0 =====
(ss-foc! SS-NNZ)
(ss-zero-witness! '(succ k) SS-SQN)
;; conj1: IS-DIAGONAL -- every entry is zero
(ss-foc-goal! (SH? 'IS-DIAGONAL))
(mac 'IS-DIAGONAL) (ss-di*)
(define SS-ZI (caddr (cadr (ss-goal))))
(define SS-ZJ (cadddr (cadr (ss-goal))))
(define SS-PZ (ss-cases (list '= (list 'ENTRY 'P SS-ZI SS-ZJ) '(ZERO A))))
(ass)
(ss-foc! SS-PZ)
(cut SS-NZk)
(ew SS-ZI) (ew SS-ZJ) (di)
(ss-foc-goal! (lambda (g) (and (pair? g) (eq? (car g) 'IN) (equal? (cadr g) SS-ZI)))) (ass)
(ss-foc-goal! (SH? 'AND)) (di)
(ss-foc-goal! (lambda (g) (and (pair? g) (eq? (car g) 'IN) (equal? (cadr g) SS-ZJ)))) (ass)
(ss-foc-goal! (SH? 'NOT)) (ass)
(ss-foc-goal! (lambda (g) (equal? g (list '= (list 'ENTRY 'P SS-ZI SS-ZJ) '(ZERO A)))))
(ai (list 'NOT SS-NZk))
;; conj5: rows past 0 -- same all-entries-zero argument
(ss-foc-goal! ss-row-goal?)
(di)(di)(di)(di)(di)                     ; i_, IN i_, NOT(i_<=0), j_, IN j_
(define SS-RZ (ss-cases '(= (ENTRY P i_ j_) (ZERO A))))
(ass)
(ss-foc! SS-RZ)
(cut SS-NZk)
(ew 'i_) (ew 'j_) (di)
(ss-foc-goal! (lambda (g) (and (pair? g) (eq? (car g) 'IN) (equal? (cadr g) 'i_)))) (ass)
(ss-foc-goal! (SH? 'AND)) (di)
(ss-foc-goal! (lambda (g) (and (pair? g) (eq? (car g) 'IN) (equal? (cadr g) 'j_)))) (ass)
(ss-foc-goal! (SH? 'NOT)) (ass)
(ss-foc-goal! (lambda (g) (equal? g '(= (ENTRY P i_ j_) (ZERO A)))))
(ai (list 'NOT SS-NZk))

(BC "before-qed-smith")
(qed 'smith-staircase)
(category! 'smith-staircase 'algebra)
(category! 'nn-zero-le 'inequalities)
(category! 'nn-succ-mono 'inequalities)
(category! 'nn-succ-le-cancel 'inequalities)
(category! 'block-type 'algebra)
(category! 'entry-of-block 'algebra)
(category! 'submodule-finsum-closed 'algebra)
