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
(call-with-output-file "/home/ubuntu/prover/scratchpad/LEAVES3.txt"
  (lambda (p)
    (write-string (string-append "OPEN LEAVES: " (number->string (length (proof-leaves)))) p)(newline p)
    (for-each (lambda (nd)
                (write-string "---- GOAL: " p)(write (wff-formula (sequent-node-assertion nd)) p)(newline p)
                (let lp ((fs (map wff-formula (sequent-node-assumptions nd))) (n 0))
                  (when (and (pair? fs) (< n 3))
                    (write-string "    " p)(write (car fs) p)(newline p)
                    (lp (cdr fs) (+ n 1)))))
              (proof-leaves))))
