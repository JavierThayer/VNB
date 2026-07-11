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
(define BS-BRD '(BORDER A b M p q))

(sp (make-wff
  '(FORALL A (IMPLIES (IS-RING A)
     (FORALL b (FORALL M (FORALL p (FORALL q (FORALL kp
       (IMPLIES (IN p NN)
       (IMPLIES (IN q NN)
       (IMPLIES (IN kp NN)
       (IMPLIES (IN b (CARR A))
       (IMPLIES (NOT (= b (ZERO A)))
       (IMPLIES (SMITH-STAIRCASE A p q M kp)
         (SMITH-STAIRCASE A (succ p) (succ q) (BORDER A b M p q) (succ kp)))))))))))))))))
(ss-di*)
(fact 'nn-succ-closed 'p) (fact 'nn-succ-closed 'q) (fact 'nn-succ-closed 'kp)

;; decompose the staircase hypothesis on M
(mac-h 'SMITH-STAIRCASE '(SMITH-STAIRCASE A p q M kp))
(ai (ss-find (lambda (f) (and (pair? f) (eq? (car f) 'AND) (pair? (cadr f)) (eq? (caadr f) 'IS-DIAGONAL)))))
(ai (ss-find (lambda (f) (and (pair? f) (eq? (car f) 'AND) (equal? (cadr f) '(<= kp p))))))
(ai (ss-find (lambda (f) (and (pair? f) (eq? (car f) 'AND) (equal? (cadr f) '(<= kp q))))))
(ai (ss-find (lambda (f) (and (pair? f) (eq? (car f) 'AND) (ss-nz-forall? (cadr f))))))
(define BS-F1 (ss-find ss-nz-forall?))
(define BS-F2 (ss-find ss-row-forall?))
(call-with-output-file "/home/ubuntu/prover/scratchpad/DBG.txt"
  (lambda (p)
    (write-string "--- ASSUMPTIONS after mac-h + ai chain ---" p)(newline p)
    (for-each (lambda (f) (write f p)(newline p))
              (map wff-formula (sequent-node-assumptions (proof-state-focus *ps*))))
    (newline p)
    (write-string "BS-F1 = " p)(write BS-F1 p)(newline p)
    (write-string "BS-F2 = " p)(write BS-F2 p)(newline p)
    (newline p)
    (mac 'SMITH-STAIRCASE)
    (write-string "GOAL after mac = " p)(write (ss-goal) p)(newline p)))
(display "DBG2-OK")(newline)
