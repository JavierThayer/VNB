;;; spans-transport-proof.scm -- the SPANS-relativized generates-transport.
;;;
;;;   spans-transport   pm invertible, u spans the submodule sm
;;;                     =>  pm.u spans sm
;;;
;;; mod-basis-proof.scm's generates-transport says an invertible matrix carries a
;;; generating sequence of the WHOLE module to a generating sequence.  Cor 3.46
;;; needs the same for a SUBMODULE: the sequence v generating F <= E is carried
;;; by Smith's left factor.  SPANS has one conjunct generates-transport does not
;;; -- that the sequence's own entries lie in sm -- and that is the only new work:
;;;
;;;   (A) entries stay in sm.  (pm . u)_{i1} = SUM_j pm_{ij} . u_{j1} (matact-entry).
;;;       Each u_{j1} is in sm, sm is closed under the scalar action, and a
;;;       submodule contains its finite sums (submodule-finsum-closed).
;;;   (B) sm is still covered.  x = c . u = (c pm^-1) . (pm . u), verbatim
;;;       generates-transport with GENERATES's guard (IN x (VEC md)) relativized
;;;       to (IN x sm).
;;;
;;; NAMING.  The invertible matrix is `pm', never `U'/`V' (IS-INVERTIBLE-MAT binds
;;; those and MIT case-folds).  The submodule is `sm', never `S' (the finsum index
;;; set).  No top-level define is named like a tactic; everything carries `st-'.
;;;
;;; Loads after mod-basis-proof (the transports it mirrors) + mod-seq
;;; (SPANS/matact-entry/matact-summand-type/submodule-finsum-closed).

;; ---- proof-driver helpers (st- prefix) ----
(define (st-pg) (wff-formula (sequent-node-assertion (proof-state-focus *ps*))))
(define (st-asms) (map wff-formula (sequent-node-assumptions (proof-state-focus *ps*))))
(define (st-wf v b) (fold-right (lambda (x y) `(FORALL ,x ,y)) b v))
(define (st-wi p b) (fold-right (lambda (x y) `(IMPLIES ,x ,y)) b p))
(define (st-di*) (let lp () (let* ((g (st-pg)) (h (and (pair? g) (car g))))
                   (when (memq h '(FORALL IMPLIES)) (di) (lp)))))
(define (st-leaves)
  (filter (lambda (nd) (and (not (sequent-node-grounded? nd))
                            (null? (sequent-node-in-arrows nd))))
          (dg-ungrounded-nodes (proof-state-dg *ps*))))
(define (st-goalof l) (wff-formula (sequent-node-assertion l)))
(define (st-focus! pred)                       ; ERRORS on a miss
  (let lp ((ls (st-leaves)))
    (cond ((null? ls) (error "spans-transport: no leaf matches"))
          ((pred (st-goalof (car ls))) (set-proof-state-focus! *ps* (car ls)) (car ls))
          (else (lp (cdr ls))))))
(define (st-find pred)
  (let ((r (filter pred (st-asms))))
    (if (null? r) (error "spans-transport: no assumption matching") (car r))))
(define (st-ai! pred) (ai (st-find pred)))
(define (SH? h) (lambda (f) (and (pair? f) (eq? (car f) h))))
(define (st-row-typing? f)
  (and (pair? f) (eq? (car f) 'IN) (pair? (caddr f))
       (eq? (car (caddr f)) 'MAT) (equal? (cadr (caddr f)) 1)))
(define (st-guarded-forall? cls)
  (lambda (f) (and (pair? f) (eq? (car f) 'FORALL) (pair? (caddr f))
                   (eq? (car (caddr f)) 'IMPLIES)
                   (pair? (cadr (caddr f)))
                   (eq? (car (cadr (caddr f))) 'IN)
                   (equal? (caddr (cadr (caddr f))) cls))))
;; cut P; prove the P-subgoal, then the continuation.  Focus by the CAPTURED LEAF
;; OBJECT -- never re-found by goal formula, they collide.
(define (st-with-cut P prove-sub prove-cont)
  (let ((before (st-leaves)))
    (cut P)
    (let* ((new  (filter (lambda (l) (not (memq l before))) (st-leaves)))
           (sub  (car (filter (lambda (l) (equal? (st-goalof l) P)) new)))
           (cont (car (filter (lambda (l) (not (eq? l sub))) new))))
      (set-proof-state-focus! *ps* sub)  (prove-sub)
      (set-proof-state-focus! *ps* cont) (prove-cont))))
(define (st-crack-inverse! X)
  (st-ai! (lambda (f) (and (pair? f) (eq? (car f) 'AND)
                           (pair? (cadr f)) (eq? (caadr f) 'IN)
                           (eq? (cadr (cadr f)) X))))
  (st-ai! (SH? 'FORSOME))
  (st-ai! (lambda (f) (and (pair? f) (eq? (car f) 'AND)
                           (pair? (cadr f)) (eq? (caadr f) 'IN)
                           (pair? (caddr f)) (eq? (car (caddr f)) 'AND))))
  (st-ai! (lambda (f) (and (pair? f) (eq? (car f) 'AND)
                           (pair? (cadr f)) (eq? (caadr f) '=)))))
(define (st-inverse-of X side)
  (let ((eq (st-find (lambda (f)
              (and (pair? f) (eq? (car f) '=)
                   (pair? (caddr f)) (eq? (car (caddr f)) 'IDENTMAT)
                   (pair? (cadr f)) (eq? (caadr f) 'MATMUL)
                   (eq? (if (eq? side 'left) (cadddr (cadr f)) (caddr (cadr f))) X))))))
    (if (eq? side 'left) (caddr (cadr eq)) (cadddr (cadr eq)))))

(define ST-VAG '(MODULE-VECTOR-AG md))
(define (st-mm a b) `(MATMUL (SCAL md) ,a ,b))
(define (st-ma a b) `(MATACT md ,a ,b))

;; =====================================================================
(sp (make-wff
  (st-wf '(md) (st-wi '((IS-MODULE md))
    (st-wf '(n u pm sm)
      (st-wi '((IN u (MAT n 1 (VEC md)))
               (IS-INVERTIBLE-MAT (SCAL md) n pm)
               (IS-SUBMODULE md sm)
               (SPANS md n u sm))
        '(SPANS md n (MATACT md pm u) sm)))))))
(st-di*)
(fact 'module-scalar-ring 'md)
(fact 'one-in-interval-1)
(fact 'interval-in-set 1 'n) (fact 'interval-card-in-nn 1 'n)
(mac-h 'IS-INVERTIBLE-MAT '(IS-INVERTIBLE-MAT (SCAL md) n pm))
(st-crack-inverse! 'pm)
(define ST-W (st-inverse-of 'pm 'left))          ; (MATMUL A ST-W pm) = I

;; unfold the SPANS hypothesis on u into its two conjuncts
(mac-h 'SPANS '(SPANS md n u sm))
(st-ai! (SH? 'AND))
(define ST-ENT (st-find (st-guarded-forall? '(INTERVAL 1 n))))   ; u's entries in sm
(define ST-COV (st-find (st-guarded-forall? 'sm)))               ; sm is covered by u

(mac 'SPANS)
(di)                                             ; [A] entries   [B] coverage

;; ---------------------------------------------------------------------
;; [A]  (pm . u)_{i1} in sm
;; ---------------------------------------------------------------------
(st-focus! (st-guarded-forall? '(INTERVAL 1 n)))
(di) (di)                                        ; i_, IN i_ [1,n]
(define ST-I (cadr (st-find (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                             (equal? (caddr f) '(INTERVAL 1 n)))))))
(define ST-FS `(VNB-LAMBDA j (INTERVAL 1 n) ((ACT md) (ENTRY pm ,ST-I j) (ENTRY u j 1))))
(fact 'matact-entry 'md 'n 'n 1 'pm 'u ST-I 1)
(subst `(= (ENTRY ,(st-ma 'pm 'u) ,ST-I 1) (FINSUM ,ST-VAG ,ST-FS (INTERVAL 1 n))))
(fact 'matact-summand-type 'md 'n 'n 1 'pm 'u ST-I 1)
;; every summand lies in sm: u_{j1} in sm and sm is closed under the action
(st-with-cut `(FORALL z (IMPLIES (IN z (INTERVAL 1 n)) (IN (,ST-FS z) sm)))
  (lambda ()
    (di) (di) (lam-b)
    (let ((ST-Z (cadr (st-find (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                                (equal? (caddr f) '(INTERVAL 1 n))
                                                (not (equal? (cadr f) ST-I))))))))
      (inst+ ST-ENT ST-Z)                        ; (ENTRY u z 1) in sm
      (fact 'entry-in-carrier 'n 'n '(CARR (SCAL md)) 'pm ST-I ST-Z)
      (mac-h 'IS-SUBMODULE '(IS-SUBMODULE md sm))
      (st-ai! (SH? 'AND)) (st-ai! (SH? 'AND)) (st-ai! (SH? 'AND)) (st-ai! (SH? 'AND))
      (let ((ST-ACT (st-find (st-guarded-forall? '(CARR (SCAL md))))))
        (inst+ ST-ACT `(ENTRY pm ,ST-I ,ST-Z))
        (inst+ (st-find (st-guarded-forall? 'sm)) `(ENTRY u ,ST-Z 1)))
      (ass)))
  (lambda ()
    (fact 'submodule-finsum-closed 'md 'sm '(INTERVAL 1 n) ST-FS)
    (ass)))

;; ---------------------------------------------------------------------
;; [B]  every x in sm is a combination of pm . u   (generates-transport, relativized)
;; ---------------------------------------------------------------------
(st-focus! (st-guarded-forall? 'sm))
(di) (di)
(define ST-X (cadr (st-find (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                             (equal? (caddr f) 'sm))))))
(inst+ ST-COV ST-X)
(st-ai! (SH? 'FORSOME))
(st-ai! (SH? 'AND))
(define ST-C (cadr (st-find st-row-typing?)))

(fact 'matmul-type '(SCAL md) 1 'n 'n ST-C ST-W)
(ew (st-mm ST-C ST-W))
(di)
(st-focus! (SH? 'IN))
(ass)
(st-focus! (lambda (g) (and (pair? g) (eq? (car g) '=) (eq? (cadr g) ST-X))))
(fact 'matact-assoc 'md 1 'n 'n 1 (st-mm ST-C ST-W) 'pm 'u)
(fact 'eq-sym (st-ma (st-mm (st-mm ST-C ST-W) 'pm) 'u)
              (st-ma (st-mm ST-C ST-W) (st-ma 'pm 'u)))
(subst `(= ,(st-ma (st-mm ST-C ST-W) (st-ma 'pm 'u))
           ,(st-ma (st-mm (st-mm ST-C ST-W) 'pm) 'u)))
(fact 'matmul-assoc '(SCAL md) 1 'n 'n 'n ST-C ST-W 'pm)
(subst `(= ,(st-mm (st-mm ST-C ST-W) 'pm) ,(st-mm ST-C (st-mm ST-W 'pm))))
(subst `(= ,(st-mm ST-W 'pm) (IDENTMAT (SCAL md) n)))
(fact 'identmat-right-identity '(SCAL md) 1 'n ST-C)
(subst `(= ,(st-mm ST-C '(IDENTMAT (SCAL md) n)) ,ST-C))
(ass)

(if (proof-done? *ps*)
    (begin (qed 'spans-transport)
           (category! 'spans-transport 'algebra))
    (begin (display "@@@ INCOMPLETE -- open leaves:")(newline)
           (for-each (lambda (l) (display "@@@   ")(write (st-goalof l))(newline))
                     (st-leaves))
           (error "spans-transport-proof: proof did not complete")))
