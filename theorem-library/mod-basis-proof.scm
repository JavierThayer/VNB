;;; mod-basis-proof.scm -- Lemma 3.40 (algebraic-numbers.pdf ch.3 sec 8.2):
;;; an invertible matrix carries generating sequences to generating sequences
;;; and relation-free sequences to relation-free sequences.  Plus the identity
;;; action I . u = u that says MATACT is a genuine action.
;;;
;;;   matact-identmat      IDENTMAT(SCAL md, n) . u = u
;;;   generates-transport  pm invertible, u generates  =>  pm.u generates
;;;   free-transport       qm invertible, v rel-free   =>  qm.v rel-free
;;;
;;; Both transports are pure matact-assoc; the book's proof is the one-liner
;;;
;;;     x = c . u = (c pm^-1) . (pm . u)                            [generating]
;;;     c . (qm . v) = (c qm) . v = 0  =>  c qm = 0  =>  c = (c qm) qm^-1 = 0  [free]
;;;
;;; and "=" between the two readings of a triple product is exactly matact-assoc
;;; + matmul-assoc, with identmat-right-identity closing the loop.
;;;
;;; NAMING.  The invertible matrix is `pm' / `qm', never `U' / `V': IS-INVERTIBLE-MAT
;;; binds its own U and V, and MIT case-folds, so a same-named free variable would
;;; shadow-collide when the predicate is unfolded.  The sequences stay u / v.

;; ---- proof-driver helpers (mb- prefix) ----
(define (mb-pg)(wff-formula (sequent-node-assertion (proof-state-focus *ps*))))
(define (mb-asms)(map wff-formula (sequent-node-assumptions (proof-state-focus *ps*))))
(define (mb-wf v b)(fold-right (lambda(x y)`(FORALL ,x ,y)) b v))
(define (mb-wi p b)(fold-right (lambda(x y)`(IMPLIES ,x ,y)) b p))
(define (mb-di*)(let lp()(let*((g(mb-pg))(h(and(pair? g)(car g))))(when(memq h '(FORALL IMPLIES))(di)(lp)))))
(define (mb-leaves)(filter (lambda(nd)(and(not(sequent-node-grounded? nd))(null?(sequent-node-in-arrows nd))))(dg-ungrounded-nodes(proof-state-dg *ps*))))
(define (mb-goalof l)(wff-formula(sequent-node-assertion l)))
(define (mb-focus! pred)(let lp((ls(mb-leaves)))(cond((null? ls)(error "mod-basis: no leaf"))((pred(mb-goalof(car ls)))(set-proof-state-focus! *ps* (car ls))(car ls))(else(lp(cdr ls))))))
(define (mb-find pred)
  (let ((r (filter pred (mb-asms))))
    (if (null? r) (error "mod-basis: no assumption matching") (car r))))
(define (mb-ai! pred) (ai (mb-find pred)))
(define (H? h) (lambda (f) (and (pair? f) (eq? (car f) h))))
;; the m-by-n typing assumption whose ROW count is 1 (the coefficient row)
(define (row-typing? f)
  (and (pair? f) (eq? (car f) 'IN) (pair? (caddr f))
       (eq? (car (caddr f)) 'MAT) (equal? (cadr (caddr f)) 1)))
;; a FORALL assumption whose single guard has the given shape
(define (guarded-forall? cls)
  (lambda (f) (and (pair? f) (eq? (car f) 'FORALL) (pair? (caddr f))
                   (eq? (car (caddr f)) 'IMPLIES)
                   (pair? (cadr (caddr f)))
                   (eq? (car (cadr (caddr f))) 'IN)
                   (equal? (caddr (cadr (caddr f))) cls))))
;; cut P, prove the P-subgoal then the continuation, each focused by its
;; CAPTURED LEAF OBJECT (never re-found by goal formula -- they collide).
(define (mb-with-cut P prove-sub prove-cont)
  (let ((before (mb-leaves)))
    (cut P)
    (let* ((new  (filter (lambda(l)(not(memq l before)))(mb-leaves)))
           (sub  (car(filter (lambda(l)(equal?(mb-goalof l) P)) new)))
           (cont (car(filter (lambda(l)(not(eq? l sub))) new))))
      (set-proof-state-focus! *ps* sub)  (prove-sub)
      (set-proof-state-focus! *ps* cont) (prove-cont))))

(define MB-VAG '(MODULE-VECTOR-AG md))
(define MB-RAG '(RING-ADDITIVE-AG (SCAL md)))
(define (mm a b) `(MATMUL (SCAL md) ,a ,b))
(define (ma a b) `(MATACT md ,a ,b))

;; the four-step decomposition of  IS-INVERTIBLE-MAT(A, d, X)  once unfolded:
;;   AND(IN X ..,  FORSOME V (AND (IN V ..) (AND (X V = I) (V X = I))))
(define (mb-crack-inverse! X)
  (mb-ai! (lambda (f) (and (pair? f) (eq? (car f) 'AND)
                           (pair? (cadr f)) (eq? (caadr f) 'IN)
                           (eq? (cadr (cadr f)) X))))
  (mb-ai! (H? 'FORSOME))
  (mb-ai! (lambda (f) (and (pair? f) (eq? (car f) 'AND)
                           (pair? (cadr f)) (eq? (caadr f) 'IN)
                           (pair? (caddr f)) (eq? (car (caddr f)) 'AND))))
  (mb-ai! (lambda (f) (and (pair? f) (eq? (car f) 'AND)
                           (pair? (cadr f)) (eq? (caadr f) '=)))))
;; the inverse W read off  (MATMUL A W X) = I   [side 'left]  or (MATMUL A X W) = I
(define (mb-inverse-of X side)
  (let ((eq (mb-find (lambda (f)
              (and (pair? f) (eq? (car f) '=)
                   (pair? (caddr f)) (eq? (car (caddr f)) 'IDENTMAT)
                   (pair? (cadr f)) (eq? (caadr f) 'MATMUL)
                   (eq? (if (eq? side 'left) (cadddr (cadr f)) (caddr (cadr f))) X))))))
    (if (eq? side 'left) (caddr (cadr eq)) (cadddr (cadr eq)))))

;; =====================================================================
;; matact-identmat :  I_n . u = u
;; =====================================================================
(define MI-LHS '(MATACT md (IDENTMAT (SCAL md) n) u))
(define MI-FF  '(VNB-LAMBDA j (INTERVAL 1 n) ((ACT md) (ENTRY (IDENTMAT (SCAL md) n) row j) (ENTRY u j col))))
(define MI-INT '(INTERVAL 1 n))

(sp (make-wff
  (mb-wf '(md) (mb-wi '((IS-MODULE md))
    (mb-wf '(n q u) (mb-wi '((IN u (MAT n q (VEC md)))) `(= ,MI-LHS u)))))))
(mb-di*)
(fact 'module-scalar-ring 'md)
(fact 'identmat-type '(SCAL md) 'n)
(fact 'matact-type 'md 'n 'n 'q '(IDENTMAT (SCAL md) n) 'u)
(fact 'module-vector-ag-is-abelian-group 'md)
(fact 'module-vzero-in 'md)
(fact 'interval-in-set 1 'n)(fact 'interval-card-in-nn 1 'n)

(mb-with-cut
  (mb-wf '(row) (mb-wi '((IN row (INTERVAL 1 n)))
    (mb-wf '(col) (mb-wi '((IN col (INTERVAL 1 q)))
      `(= (ENTRY ,MI-LHS row col) (ENTRY u row col))))))
  (lambda ()
    (mb-di*)
    (fact 'matact-entry 'md 'n 'n 'q '(IDENTMAT (SCAL md) n) 'u 'row 'col)
    (subst `(= (ENTRY ,MI-LHS row col) (FINSUM ,MB-VAG ,MI-FF ,MI-INT)))
    (fact 'matact-summand-type 'md 'n 'n 'q '(IDENTMAT (SCAL md) n) 'u 'row 'col)
    ;; VANISH: off the diagonal the summand is 0 . u_{jc} = 0
    (mb-with-cut `(FORALL jz (IMPLIES (IN jz ,MI-INT)
                    (IMPLIES (NOT (= jz row)) (= (,MI-FF jz) (IDEN ,MB-VAG)))))
      (lambda ()
        (di)(di)(di)
        (lam-b)
        (fact 'neq-sym 'jz 'row)
        (fact 'identmat-entry-off '(SCAL md) 'n 'row 'jz)
        (subst '(= (ENTRY (IDENTMAT (SCAL md) n) row jz) (ZERO (SCAL md))))
        (fact 'entry-in-carrier 'n 'q '(VEC md) 'u 'jz 'col)
        (fact 'module-zero-act 'md '(ENTRY u jz col))
        (subst '(= ((ACT md) (ZERO (SCAL md)) (ENTRY u jz col)) (VZERO md)))
        (fact 'mvag-id 'md)
        (subst `(= (IDEN ,MB-VAG) (VZERO md)))
        (rfl))
      (lambda ()
        (fact 'finsum-single-support MB-VAG MI-INT MI-FF 'row)
        (subst `(= (FINSUM ,MB-VAG ,MI-FF ,MI-INT) (,MI-FF row)))
        (lam-b)
        (fact 'identmat-entry-diag '(SCAL md) 'n 'row)
        (subst '(= (ENTRY (IDENTMAT (SCAL md) n) row row) (ONE (SCAL md))))
        (fact 'entry-in-carrier 'n 'q '(VEC md) 'u 'row 'col)
        (fact 'module-act-unital 'md '(ENTRY u row col))
        (subst '(= ((ACT md) (ONE (SCAL md)) (ENTRY u row col)) (ENTRY u row col)))
        (rfl))))
  (lambda ()
    (fact 'matrix-entry-extensionality 'n 'q '(VEC md) MI-LHS 'u)
    (ass)))
(qed 'matact-identmat)
(category! 'matact-identmat 'algebra)

;; =====================================================================
;; generates-transport :  pm invertible, u generates  =>  pm.u generates
;; =====================================================================
(sp (make-wff
  (mb-wf '(md) (mb-wi '((IS-MODULE md))
    (mb-wf '(n u pm) (mb-wi '((IN u (MAT n 1 (VEC md)))
                              (IS-INVERTIBLE-MAT (SCAL md) n pm)
                              (GENERATES md n u))
      '(GENERATES md n (MATACT md pm u))))))))
(mb-di*)
(fact 'module-scalar-ring 'md)
(mac-h 'IS-INVERTIBLE-MAT '(IS-INVERTIBLE-MAT (SCAL md) n pm))
(mb-crack-inverse! 'pm)
(define GT-W (mb-inverse-of 'pm 'left))          ; (MATMUL A GT-W pm) = I

(mac 'GENERATES)
(di)(di)
(define GT-X (cadr (mb-find (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                             (equal? (caddr f) '(VEC md)))))))
(mac-h 'GENERATES '(GENERATES md n u))
(inst+ (mb-find (guarded-forall? '(VEC md))) GT-X)
(mb-ai! (H? 'FORSOME))
(mb-ai! (H? 'AND))
(define GT-C (cadr (mb-find row-typing?)))

(fact 'matmul-type '(SCAL md) 1 'n 'n GT-C GT-W)
(ew (mm GT-C GT-W))
(di)
;; leaf 1: the witness is a 1-by-n coefficient row
(mb-focus! (H? 'IN))
(ass)
;; leaf 2: x = ((c W) . (pm . u))_{11}
(mb-focus! (lambda (g) (and (pair? g) (eq? (car g) '=) (eq? (cadr g) GT-X))))
(fact 'matact-assoc 'md 1 'n 'n 1 (mm GT-C GT-W) 'pm 'u)
(fact 'eq-sym (ma (mm (mm GT-C GT-W) 'pm) 'u) (ma (mm GT-C GT-W) (ma 'pm 'u)))
(subst `(= ,(ma (mm GT-C GT-W) (ma 'pm 'u)) ,(ma (mm (mm GT-C GT-W) 'pm) 'u)))
(fact 'matmul-assoc '(SCAL md) 1 'n 'n 'n GT-C GT-W 'pm)
(subst `(= ,(mm (mm GT-C GT-W) 'pm) ,(mm GT-C (mm GT-W 'pm))))
(subst `(= ,(mm GT-W 'pm) (IDENTMAT (SCAL md) n)))
(fact 'identmat-right-identity '(SCAL md) 1 'n GT-C)
(subst `(= ,(mm GT-C '(IDENTMAT (SCAL md) n)) ,GT-C))
(ass)
(qed 'generates-transport)
(category! 'generates-transport 'algebra)

;; =====================================================================
;; free-transport :  qm invertible, v rel-free  =>  qm.v rel-free
;; =====================================================================
(sp (make-wff
  (mb-wf '(md) (mb-wi '((IS-MODULE md))
    (mb-wf '(m v qm) (mb-wi '((IN v (MAT m 1 (VEC md)))
                              (IS-INVERTIBLE-MAT (SCAL md) m qm)
                              (REL-FREE md m v))
      '(REL-FREE md m (MATACT md qm v))))))))
(mb-di*)
(fact 'module-scalar-ring 'md)
(fact 'ring-additive-ag-is-abelian-group '(SCAL md))
(fact 'one-in-interval-1)
(fact 'interval-in-set 1 'm)(fact 'interval-card-in-nn 1 'm)
(mac-h 'IS-INVERTIBLE-MAT '(IS-INVERTIBLE-MAT (SCAL md) m qm))
(mb-crack-inverse! 'qm)
(define FT-W (mb-inverse-of 'qm 'right))         ; (MATMUL A qm FT-W) = I

(mac 'REL-FREE)
(di)(di)(di)                                     ; c, IN c, the zero-combination hyp
(define FT-C (cadr (mb-find row-typing?)))
(define FT-D (mm FT-C 'qm))
(fact 'matmul-type '(SCAL md) 1 'm 'm FT-C 'qm)

(mb-with-cut `(= (ENTRY ,(ma FT-D 'v) 1 1) (VZERO md))
  (lambda ()                                     ; d annihilates v
    (fact 'matact-assoc 'md 1 'm 'm 1 FT-C 'qm 'v)
    (subst `(= ,(ma FT-D 'v) ,(ma FT-C (ma 'qm 'v))))
    (ass))
  (lambda ()                                     ; so every entry of d vanishes
    (mac-h 'REL-FREE '(REL-FREE md m v))
    (inst+ (mb-find (guarded-forall? `(MAT 1 m (CARR (SCAL md))))) FT-D)
    (di)(di)
    (let* ((FT-J  (cadr (mb-find (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                                  (equal? (caddr f) '(INTERVAL 1 m)))))))
           (FT-ZH (mb-find (guarded-forall? '(INTERVAL 1 m))))
           (FS `(VNB-LAMBDA j (INTERVAL 1 m) ((MUL (SCAL md)) (ENTRY ,FT-D 1 j) (ENTRY ,FT-W j ,FT-J)))))
      ;; c = (c qm) qm^-1
      (mb-with-cut `(= ,(mm FT-D FT-W) ,FT-C)
        (lambda ()
          (fact 'matmul-assoc '(SCAL md) 1 'm 'm 'm FT-C 'qm FT-W)
          (subst `(= ,(mm FT-D FT-W) ,(mm FT-C (mm 'qm FT-W))))
          (subst `(= ,(mm 'qm FT-W) (IDENTMAT (SCAL md) m)))
          (fact 'identmat-right-identity '(SCAL md) 1 'm FT-C)
          (ass))
        (lambda ()
          (fact 'eq-sym (mm FT-D FT-W) FT-C)
          (subst `(= ,FT-C ,(mm FT-D FT-W)))
          (fact 'matmul-entry '(SCAL md) 1 'm 'm FT-D FT-W 1 FT-J)
          (subst `(= (ENTRY ,(mm FT-D FT-W) 1 ,FT-J) (FINSUM ,MB-RAG ,FS (INTERVAL 1 m))))
          (fact 'matprod-summand-type '(SCAL md) 1 'm 'm FT-D FT-W 1 FT-J)
          (mb-with-cut `(FORALL jz (IMPLIES (IN jz (INTERVAL 1 m)) (= (,FS jz) (IDEN ,MB-RAG))))
            (lambda ()
              (di)(di)
              (lam-b)
              (inst+ FT-ZH 'jz)
              (subst `(= (ENTRY ,FT-D 1 jz) (ZERO (SCAL md))))
              (fact 'entry-in-carrier 'm 'm '(CARR (SCAL md)) FT-W 'jz FT-J)
              (fact 'ring-mul-zero-left '(SCAL md) `(ENTRY ,FT-W jz ,FT-J))
              (subst `(= ((MUL (SCAL md)) (ZERO (SCAL md)) (ENTRY ,FT-W jz ,FT-J)) (ZERO (SCAL md))))
              (fact 'ras-id '(SCAL md))
              (subst `(= (IDEN ,MB-RAG) (ZERO (SCAL md))))
              (rfl))
            (lambda ()
              (fact 'finsum-all-id MB-RAG '(INTERVAL 1 m) FS)
              (subst `(= (FINSUM ,MB-RAG ,FS (INTERVAL 1 m)) (IDEN ,MB-RAG)))
              (fact 'ras-id '(SCAL md))
              (ass))))))))
(qed 'free-transport)
(category! 'free-transport 'algebra)

;; ----- categorize the PSS bricks these proofs introduced -----
(category! 'identmat-entry-diag 'algebra)
(category! 'identmat-entry-off 'algebra)
(category! 'unitrow-type 'algebra)
(category! 'unitrow-entry-at 'algebra)
(category! 'unitrow-entry-off 'algebra)
(category! 'finsum-all-id 'algebra)
(category! 'diagonal-off-entry 'algebra)
(category! 'generates-coeff-matrix 'algebra)
