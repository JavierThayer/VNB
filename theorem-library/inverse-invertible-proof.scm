;;; inverse-invertible-proof.scm -- the inverse of an invertible matrix is
;;; invertible.
;;;
;;;   inverse-is-invertible   pm qm = I, qm pm = I  =>  qm is invertible
;;;
;;; IS-INVERTIBLE-MAT(A,n,U) is  U in MAT(n,n) AND exists V. V in MAT(n,n)
;;; AND U V = I AND V U = I -- symmetric in U and V, so the witness for qm is
;;; just pm with the two equations read in the other order.  Trivial, but Cor
;;; 3.46 cannot get started without it: Smith gives D = pm . C . qm with pm, qm
;;; invertible, and the assembly transports the free generating sequence u
;;; BACKWARDS along qm, i.e. by qm^-1, which must itself be invertible before
;;; generates-transport / free-transport will accept it.
;;;
;;; NAMING.  The matrices are `pm' / `qm', never `U' / `V': IS-INVERTIBLE-MAT
;;; binds its own U and V and MIT case-folds, so a same-named free variable
;;; would shadow-collide when the predicate is unfolded.  (mod-basis-proof.scm
;;; makes the same point.)  And no top-level define here may be named like a
;;; tactic -- everything carries the `ii-' prefix.
;;;
;;; Loads after mat-equiv (IS-INVERTIBLE-MAT) + interactive/proof-debt.

;; ---- proof-driver helpers (ii- prefix) ----
(define (ii-pg) (wff-formula (sequent-node-assertion (proof-state-focus *ps*))))
(define (ii-wf v b) (fold-right (lambda (x y) `(FORALL ,x ,y)) b v))
(define (ii-wi p b) (fold-right (lambda (x y) `(IMPLIES ,x ,y)) b p))
(define (ii-di*) (let lp () (let* ((g (ii-pg)) (h (and (pair? g) (car g))))
                   (when (memq h '(FORALL IMPLIES)) (di) (lp)))))
(define (ii-leaves)
  (filter (lambda (nd) (and (not (sequent-node-grounded? nd))
                            (null? (sequent-node-in-arrows nd))))
          (dg-ungrounded-nodes (proof-state-dg *ps*))))
(define (ii-goalof l) (wff-formula (sequent-node-assertion l)))
;; focus by goal; ERRORS on a miss -- never silently leave focus put.
(define (ii-focus! pred)
  (let lp ((ls (ii-leaves)))
    (cond ((null? ls) (error "inverse-invertible: no leaf matches"))
          ((pred (ii-goalof (car ls))) (set-proof-state-focus! *ps* (car ls)) (car ls))
          (else (lp (cdr ls))))))
;; split every AND goal and close each leaf by an in-context assumption.
(define (ii-split-and-close!)
  (let lp ((n 0))
    (when (< n 8)
      (let ((g (ii-pg)))
        (cond ((and (pair? g) (eq? (car g) 'AND)) (di) (lp (+ n 1)))
              (else (ass)
                    (let ((open (ii-leaves)))
                      (when (pair? open)
                        (set-proof-state-focus! *ps* (car open))
                        (lp (+ n 1))))))))))

(sp (make-wff
  (ii-wf '(A) (ii-wi '((IS-RING A))
    (ii-wf '(n pm qm)
      (ii-wi '((IN pm (MAT n n (CARR A)))
               (IN qm (MAT n n (CARR A)))
               (= (MATMUL A pm qm) (IDENTMAT A n))
               (= (MATMUL A qm pm) (IDENTMAT A n)))
        '(IS-INVERTIBLE-MAT A n qm)))))))
(ii-di*)

;; goal: IS-INVERTIBLE-MAT A n qm  =  qm in MAT(n,n) AND exists V. ...
(mac 'IS-INVERTIBLE-MAT)
(di)                                    ; [a] qm typed   [b] the existential

;; [a] qm's typing is a hypothesis
(ii-focus! (lambda (g) (equal? g '(IN qm (MAT n n (CARR A))))))
(ass)

;; [b] witness V := pm; the two equations are the hypotheses, swapped
(ii-focus! (lambda (g) (and (pair? g) (eq? (car g) 'FORSOME))))
(ew 'pm)
(ii-split-and-close!)

(if (proof-done? *ps*)
    (begin (qed 'inverse-is-invertible)
           (topic! 'inverse-is-invertible 'algebra))
    (error "inverse-invertible-proof: proof did not complete"))
