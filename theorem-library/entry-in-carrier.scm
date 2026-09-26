;;; entry-in-carrier.scm -- the entries of an m-by-n matrix over X lie in X.
;;;
;;;   forall m, n, X, P, i, j.
;;;     P in MAT(m,n,X)  =>  i in INTERVAL(1,m)  =>  j in INTERVAL(1,n)
;;;       =>  ENTRY(P,i,j) in X
;;;
;;; PROVEN here from the definitions; the statement is matrix.scm's
;;; `entry-in-carrier' support, unchanged (63 bills).
;;;
;;; PLAN.  ENTRY(P,i,j) = NTH(j, NTH(i, P)).  Two applications of the base
;;; axiom `nth-in-range' -- row i is a tuple over X, then its j-th entry is in X
;;; -- each of which owes the index range 1 <= k <= LENGTH(list).  The two
;;; lengths come off the matrix:
;;;
;;;   * LENGTH(P) = m         -- `mat-length' (mat-basics.scm);
;;;   * LENGTH(NTH(1,P)) = n  -- `mat-cols' (mat-basics.scm), whose guard
;;;                              1 <= m comes from 1 <= i <= m;
;;;   * LENGTH(NTH(i,P)) = LENGTH(NTH(1,P))  -- matrix-membership's equilong
;;;                              clause at (i, 1), which owes 1 <= LENGTH(P):
;;;                              1 <= i <= m = LENGTH(P), nn-le-trans-guarded.
;;;
;;; The column read-off is guarded (a matrix with no rows does not determine
;;; its column count; matrix.scm), and the guard is free here: everything is
;;; under i in [1,m], so m >= 1 and NTH(1,P) is a genuine row.  No `n in NN'
;;; appears anywhere -- nth-in-range's range condition on the row is
;;; j <= LENGTH(NTH(i,P)), which is j <= n by the equations above, and `j in NN'
;;; comes from j's own interval.
;;;
;;; LOAD WINDOW [lo, hi):
;;;   lo -- after theorem-library/nn-order-basics (nn-le-trans-guarded,
;;;         nn-le-refl) and theorem-library/nn-order-ord (nn-one-in); both sit
;;;         just below mat-basics and interval-basics (mat-unfold, size-unfold,
;;;         nth1-pair, interval-elt-in-nn, interval-lo, interval-hi).
;;;   hi -- before theorem-library/triple-entry-proof, the earliest citer.
;;; Base axioms: matrix-membership (definitional), nth-in-range, length-in-nn.
;;;
;;; Helper prefix: eic-.

;; Close an AND goal conjunct by conjunct from the context, with `ass' only.
;; (`have!' with no thunk does the same through `from-context!', but that
;; routes a numeric-literal membership such as `1 in NN' to the `arith' oracle
;; even when the fact is in context; `nn-one-in' is a theorem, so use it.)
(define (eic-and-from-ctx!)
  (let ((g (dk-goal)))
    (if (and (pair? g) (eq? (car g) 'AND))
        (for-each (lambda (k) (dk-focus! k) (eic-and-from-ctx!))
                  (dk-opened (lambda () (di))))
        (ass))))

;; Peel the FORALL/IMPLIES prefix until the head changes (di is greedy and its
;; grouping is not worth counting).
(define (eic-peel!)
  (let loop ()
    (let ((g (dk-goal)))
      (if (and (pair? g) (memq (car g) '(FORALL IMPLIES)))
          (begin (di) (loop))))))

(sp (make-wff '(FORALL m (FORALL n (FORALL X (FORALL P (FORALL i (FORALL j
     (IMPLIES (IN P (MAT m n X))
     (IMPLIES (IN i (INTERVAL 1 m))
     (IMPLIES (IN j (INTERVAL 1 n))
       (IN (ENTRY P i j) X))))))))))))
(eic-peel!)
(mac 'ENTRY)                                   ; goal: NTH(j, NTH(i, P)) in X

;; ---- P as a matrix: P in MATRIX(X), LENGTH(P) = m  (mat-basics) ------------
(fact 'mat-in-matrix 'm 'n 'X 'P)
;; P is a tuple of tuples, and its rows are equilong
(define eic-mm
  (dk-split! (dk-landed-1 (lambda () (mac-h 'matrix-membership '(IN P (MATRIX X)))))))
(define eic-equilong
  (or (find-first (dk-head? 'FORALL) eic-mm)
      (error "entry-in-carrier: matrix-membership landed no equilong clause" eic-mm)))
(fact 'mat-length 'm 'n 'X 'P)                 ; LENGTH(P) = m
(fact 'mat-rows-in-nn 'm 'n 'X 'P)             ; m in NN

;; ---- the index facts off the two intervals --------------------------------
(fact 'interval-elt-in-nn 1 'm 'i)             ; i in NN
(fact 'interval-lo 1 'm 'i)                    ; 1 <= i
(fact 'interval-hi 1 'm 'i)                    ; i <= m
(fact 'interval-elt-in-nn 1 'n 'j)
(fact 'interval-lo 1 'n 'j)
(fact 'interval-hi 1 'n 'j)
;; ---- LENGTH(NTH(1,P)) = n: P has a row, since 1 <= i <= m --------------------
(fact 'nn-one-in)
(fact 'nn-le-trans-guarded 1 'i 'm)            ; 1 <= m
(fact 'mat-cols 'm 'n 'X 'P)                   ; LENGTH(NTH(1, P)) = n
(have! '(<= i (LENGTH P)) (lambda () (subst '(= (LENGTH P) m)) (ass)))
;; 1 <= LENGTH(P): 1 <= i <= LENGTH(P), transitivity on NN
(fact 'nn-one-in)
(fact 'length-in-nn '(TUPLES X) 'P)            ; LENGTH(P) in NN
(fact 'nn-le-trans-guarded 1 'i '(LENGTH P))   ; 1 <= LENGTH(P)

;; ---- row i is a tuple over X ----------------------------------------------
(have! '(AND (IN i NN) (AND (IN P (TUPLES (TUPLES X))) (AND (<= 1 i) (<= i (LENGTH P))))))
(fact 'nth-in-range '(TUPLES X) 'i 'P)          ; NTH(i, P) in TUPLES(X)

;; ---- row i has n entries: the equilong clause at (i, 1) --------------------
(have! '(AND (IN i NN) (AND (<= 1 i) (<= i (LENGTH P)))))
(define eic-row-clause (dk-deepest (lambda () (inst+ eic-equilong 'i))))
(fact 'nn-le-refl 1)                           ; 1 <= 1
(have! '(AND (IN 1 NN) (AND (<= 1 1) (<= 1 (LENGTH P)))) eic-and-from-ctx!)
(define eic-row-eq (dk-deepest (lambda () (inst+ eic-row-clause 1))))
;; eic-row-eq is LENGTH(NTH(i,P)) = LENGTH(NTH(1,P))
(have! '(= (LENGTH (NTH i P)) n)
  (lambda () (subst eic-row-eq) (ass)))
(have! '(<= j (LENGTH (NTH i P)))
  (lambda () (subst '(= (LENGTH (NTH i P)) n)) (ass)))

;; ---- the entry -------------------------------------------------------------
(have! '(AND (IN j NN) (AND (IN (NTH i P) (TUPLES X)) (AND (<= 1 j) (<= j (LENGTH (NTH i P)))))))
(fact 'nth-in-range 'X 'j '(NTH i P))          ; NTH(j, NTH(i, P)) in X
(ass)

(if (proof-done? *ps*)
    (qed 'entry-in-carrier)
    (begin
      (display "\n*** entry-in-carrier did NOT close.  Open goals:\n")
      (for-each (lambda (l)
                  (display "   GOAL: ")
                  (display (expression->string (sequent-node-assertion l)))
                  (newline))
                (proof-leaves))
      (error "entry-in-carrier: unfinished")))
