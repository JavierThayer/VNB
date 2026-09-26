;;; mat-typing-bundle.scm -- three MATOF typings, PROVEN from the definitions.
;;;
;;;   matmul-type    forall A. IS-RING(A) => forall m n k P Q.
;;;                    P in MAT(m,n,CARR A) => Q in MAT(n,k,CARR A)
;;;                      => (n = 0 => m = 0 or k = 0)
;;;                      => MATMUL(A,P,Q) in MAT(m,k,CARR A)
;;;   identmat-type  forall A. IS-RING(A) => forall n. n in NN
;;;                      => IDENTMAT(A,n) in MAT(n,n,CARR A)
;;;   elem-g-type    forall A. IS-RING(A) => forall n r k l. n in NN => r in CARR A
;;;                      => ELEM-G(A,n,r,k,l) in MAT(n,n,CARR A)
;;;   mat-colcount-transfer   the column-count bookkeeping both product
;;;                      typings need (see its block)
;;;   zeromat-type, unitrow-type, elem-h-type   (added 2026-09-16; see their
;;;                      block)
;;;
;;; The statements were matrix.scm's / elementary-matrix.scm's supports; the
;;; guards were added 2026-09-16 (the SIZE/MAT change), each forced -- see the
;;; blocks.  The MATMUL paragraph of the PLAN below describes the pre-guard
;;; driver; the block itself is current.
;;;
;;; PLAN.  Every one is a MATOF, so every one is `matof-in-mat' (asserted,
;;; well-known; being proven separately -- this bundle CHAINS TO IT) applied to
;;; the tabulator: unfold the constructor, `bc*' matof-in-mat, peel the two
;;; index binders, `lam-b' the pair-lambda (licensed componentwise by the two
;;; interval typings the peel landed), and type what is left:
;;;
;;;   * IDENTMAT / ELEM-G: an IF tower over (= i j) and (AND (= i k) (= j l)).
;;;     `use-em' on the condition, `if-true' / `if-false' to resolve the IF into
;;;     an equation, `subst' it into the goal, and the value is ONE(A)
;;;     (ring-one-in, PROVEN), ZERO(A) (ring-zero-in, definitional) or r
;;;     (hypothesis).  mtb-close-if! does this recursively, so the two files'
;;;     conditions need no separate driver.
;;;   * MATMUL: the tabulator's dimensions are NTH(1,SIZE P), NTH(2,SIZE Q),
;;;     NTH(2,SIZE P).  SIZE(P) = [m,n] and SIZE(Q) = [n,k] come out of the
;;;     MAT hypotheses by mat-basics' chain (mat-unfold, a `have!' across the
;;;     unfolding equation, sep-me); two `subst's put the literal pairs into the
;;;     goal and ONE `nth-r' reduces every NTH-on-a-literal-pair at once
;;;     (reduce-nth-in-expr walks the whole goal).  The entry is then a FINSUM
;;;     over [1,n] in RING-ADDITIVE-AG(A), typed by
;;;     `finsum-type-ring-additive-ag' -- the view companion cancellation.scm's
;;;     re-run of the specializer installed, which states the codomain as
;;;     CARR(A) directly, so `ras-carr' is never needed.  Its premises:
;;;     [1,n] in SET (interval-in-set), CARD[1,n] in NN (interval-card-in-nn,
;;;     guarded on n in NN -- n is Q's ROW count: mat-rows-in-nn), and the
;;;     summand j |-> P_ij * Q_jc in FUN([1,n], CARR A) by `lam-t' +
;;;     entry-in-carrier x2 + ring-carrier-closed-mul.  No matprod-summand-type.
;;;
;;; LOAD WINDOW [lo, hi):
;;;   lo -- after theorem-library/interval-card-in-nn (the LATEST citation;
;;;         the others -- entry-in-carrier, mat-basics, ring-zero-one-power,
;;;         cancellation (finsum-type-ring-additive-ag), op-typing
;;;         (ring-carrier-closed-mul), interval-basics, matrix (matof-in-mat,
;;;         mat-rows-in-nn is mat-basics) -- all load earlier).
;;;   hi -- before theorem-library/triple-entry-proof, the earliest citer of
;;;         matmul-type (mat-ring-proof and elem-actions-proof, the earliest
;;;         citers of the other two, come after it).
;;;
;;; Helper prefix: mtb-.

;;; ---- helpers ----------------------------------------------------------

;; Resolve an IF tower in a goal (IN (IF c a b) X): case on c, reduce the IF
;; to an equation on each side, substitute, recurse; a goal that is not an IF
;; is closed from the context.  The ONE/ZERO/r typings must already be in
;; context.
(define (mtb-close-if!)
  (let ((g (dk-goal)))
    (if (and (pair? g) (eq? (car g) 'IN)
             (pair? (cadr g)) (eq? (car (cadr g)) 'IF))
        (let* ((ifterm (cadr g))
               (c      (cadr ifterm)))
          (use-em c
            (lambda () (mtb-if-branch! #t ifterm))
            (lambda () (mtb-if-branch! #f ifterm))))
        (ass))))

;; if-true / if-false open two leaves: the CONDITION (or its negation), which
;; the case split put in context, and the MAIN goal with (= (IF c a b) val)
;; added.  Discriminate them on the goal, never on where focus landed.
(define (mtb-if-branch! true? ifterm)
  (let* ((c      (cadr ifterm))
         (val    (if true? (caddr ifterm) (cadddr ifterm)))
         (want   (if true? c (list 'NOT c)))
         (opened (dk-opened (lambda () (if true? (if-true ifterm) (if-false ifterm)))))
         (conds  (filter (lambda (l) (alpha-equiv? (dk-goal-of l) want)) opened))
         (mains  (filter (lambda (l) (not (memq l conds))) opened)))
    (if (not (and (= 1 (length conds)) (= 1 (length mains))))
        (error "mtb-if-branch!: expected one condition leaf and one main leaf, got"
               (map (lambda (l) (expression->string (dk-goal-of l))) opened)))
    (dk-focus! (car conds)) (ass)
    (dk-focus! (car mains))
    (subst (list '= ifterm val))
    (mtb-close-if!)))

;; The standard finish: report open goals loudly rather than qed a half-proof.
(define (mtb-qed! name)
  (if (proof-done? *ps*)
      (qed name)
      (begin
        (display "\n*** mat-typing-bundle: ") (display name)
        (display " did NOT close.  Open goals:\n")
        (for-each (lambda (l)
                    (display "   GOAL: ")
                    (display (expression->string (sequent-node-assertion l)))
                    (newline)
                    (for-each (lambda (a)
                                (display "      asm: ")
                                (display (expression->string a)) (newline))
                              (dk-asms-of l)))
                  (proof-leaves))
        (error "mat-typing-bundle: unfinished" name))))


;;; ---- mat-colcount-transfer -------------------------------------------
;;;
;;; A product P.Q with P : m x n, Q : n x k is a MATOF whose column count is
;;; read off Q -- NTH(2, SIZE Q) -- and that is k only when Q has rows.  When
;;; n = 0, Q is [] and NTH(2, SIZE Q) = 0.  So the product lands in
;;; MAT(m, NTH(2, SIZE Q), X), and this moves it to MAT(m, k, X) under the
;;; product guard `n = 0 implies (m = 0 or k = 0)': for n >= 1 the two column
;;; counts agree; for n = 0 either k = 0 = NTH(2, SIZE Q), or m = 0 and a
;;; matrix with no rows is a 0-by-k matrix for every natural k.

(sp (make-wff '(FORALL n (FORALL k (FORALL Y (FORALL Q (FORALL m (FORALL X (FORALL R
   (IMPLIES (IN Q (MAT n k Y))
   (IMPLIES (IMPLIES (= n 0) (OR (= m 0) (= k 0)))
   (IMPLIES (IN R (MAT m (NTH 2 (SIZE Q)) X))
     (IN R (MAT m k X))))))))))))))
(dk-peel!)
(fact 'mat-rows-in-nn 'n 'k 'Y 'Q)             ; n in NN
(fact 'mat-cols-in-nn 'n 'k 'Y 'Q)             ; k in NN
(use-em '(= n 0)
  (lambda ()
    (fact 'mat-length 'n 'k 'Y 'Q)             ; LENGTH(Q) = n
    (have! '(= (LENGTH Q) 0) (lambda () (subst '(= 0 n)) (ass)))
    (dk-focus-having! '(= (LENGTH Q) 0))
    (let ((ift '(IF (= (LENGTH Q) 0) 0 (LENGTH (NTH 1 Q)))))
      (fact 'size-unfold 'Q)
      (let ((ls (dk-opened (lambda () (if-true ift)))))
        (for-each (lambda (l)
                    (if (equal? (dk-goal-of l) '(= (LENGTH Q) 0)) (begin (dk-focus! l) (ass))))
                  ls)
        (dk-focus! (find-first (lambda (l) (not (equal? (dk-goal-of l) '(= (LENGTH Q) 0)))) ls)))
      (have! '(= (NTH 2 (SIZE Q)) 0)
        (lambda ()
          (subst (list '== '(SIZE Q) (list 'LIST '(LENGTH Q) ift)))
          (nth-r)
          (subst (list '= ift 0))
          (rfl))))
    (dk-focus! (find-first (lambda (l) (member '(= (NTH 2 (SIZE Q)) 0) (dk-asms-of l)))
                           (proof-leaves)))
    (fact 'nn-zero-in)
    (use-em '(= m 0)
      (lambda ()                               ; no rows in the product
        (have! '(IN R (MAT 0 (NTH 2 (SIZE Q)) X))
          (lambda () (subst '(= 0 m)) (ass)))
        (dk-focus! (find-first (lambda (l) (member '(IN R (MAT 0 (NTH 2 (SIZE Q)) X)) (dk-asms-of l)))
                               (proof-leaves)))
        (fact 'mat-size-cols-in-nn 'n 'k 'Y 'Q)
        (fact 'mat-empty-any-cols '(NTH 2 (SIZE Q)) 'X 'R 'k)
        (subst '(= m 0))
        (ass))
      (lambda ()                               ; so k = 0, the column counts agree
        (detach! '(IMPLIES (= n 0) (OR (= m 0) (= k 0))))
        (have! '(= k 0) (lambda () (prop)))
        (dk-focus! (find-first (lambda (l) (member '(= k 0) (dk-asms-of l))) (proof-leaves)))
        (subst '(= k 0))
        (subst '(= 0 (NTH 2 (SIZE Q))))
        (ass))))
  (lambda ()                                   ; Q has rows: its column count is k
    (dk-one-le! 'n)
    (fact 'mat-size-cols 'n 'k 'Y 'Q)          ; NTH(2, SIZE Q) = k
    (subst '(= k (NTH 2 (SIZE Q))))
    (ass)))
(mtb-qed! 'mat-colcount-transfer)
(topic! 'mat-colcount-transfer 'plumbing)

;;; ---- identmat-type ----------------------------------------------------

(sp (make-wff '(FORALL A (IMPLIES (IS-RING A) (FORALL n (IMPLIES (IN n NN)
     (IN (IDENTMAT A n) (MAT n n (CARR A)))))))))
(dk-peel!)                                     ; IS-RING A, n in NN
(mac 'IDENTMAT)
(dk-matof!)
(dk-peel!)                                     ; i in [1,n], j in [1,n]
(lam-b)                                        ; (IN (IF (= i j) (ONE A) (ZERO A)) (CARR A))
(fact 'ring-one-in 'A)
(fact 'ring-zero-in 'A)
(mtb-close-if!)
(mtb-qed! 'identmat-type)
(topic! 'identmat-type 'algebra)

;;; ---- elem-g-type ------------------------------------------------------

(sp (make-wff '(FORALL A (IMPLIES (IS-RING A) (FORALL n (FORALL r (FORALL k (FORALL l
     (IMPLIES (IN n NN)
     (IMPLIES (IN r (CARR A))
       (IN (ELEM-G A n r k l) (MAT n n (CARR A)))))))))))))
(dk-peel!)                                     ; IS-RING A, n in NN, r in CARR A
(mac 'ELEM-G)
(dk-matof!)
(dk-peel!)                                     ; i in [1,n], j in [1,n]
(lam-b)
(fact 'ring-one-in 'A)
(fact 'ring-zero-in 'A)
(mtb-close-if!)
(mtb-qed! 'elem-g-type)
(topic! 'elem-g-type 'algebra)

;;; ---- zeromat-type, unitrow-type, elem-h-type (2026-09-16) ---------------
;;;
;;; Three more MATOF typings, asserted in structure-library/matrix.scm and
;;; elementary-matrix.scm until the FALSE-DEF sweep (2026-09-16) guarded them on
;;; the dimensions being natural -- (IN m NN), (IN n NN) -- and they became
;;; this driver verbatim.  (elem-f-type, whose IF condition is a DISJUNCTION,
;;; is proven in theorem-library/elem-entry-readoffs.scm, whose resolver splits
;;; on equality atoms; `mtb-close-if!' splits on the whole condition.)
;;; Earliest citers: mat-ring-proof (zeromat-type), elem-actions-proof
;;; (elem-h-type), span-bricks-proof (unitrow-type) -- all after this file.

(sp (make-wff '(FORALL A (IMPLIES (IS-RING A) (FORALL m (FORALL n
     (IMPLIES (IN m NN) (IMPLIES (IN n NN)
       (IN (ZEROMAT A m n) (MAT m n (CARR A)))))))))))
(dk-peel!)                                     ; IS-RING A, m, n in NN
(mac 'ZEROMAT)
(dk-matof!)
(dk-peel!)                                     ; i in [1,m], j in [1,n]
(lam-b)                                        ; (IN (ZERO A) (CARR A))
(fact 'ring-zero-in 'A)
(ass)
(mtb-qed! 'zeromat-type)
(topic! 'zeromat-type 'algebra)

(sp (make-wff '(FORALL A (IMPLIES (IS-RING A) (FORALL n (FORALL i (IMPLIES (IN n NN)
     (IN (UNITROW A n i) (MAT 1 n (CARR A))))))))))
(dk-peel!)                                     ; IS-RING A, n in NN
(fact 'nn-one-in)                              ; the row count 1, for dk-matof!
(mac 'UNITROW)
(dk-matof!)
(dk-peel!)                                     ; row in [1,1], col in [1,n]
(lam-b)                                        ; (IN (IF (= col i) (ONE A) (ZERO A)) (CARR A))
(fact 'ring-one-in 'A)
(fact 'ring-zero-in 'A)
(mtb-close-if!)
(mtb-qed! 'unitrow-type)
(topic! 'unitrow-type 'algebra)

(sp (make-wff '(FORALL A (IMPLIES (IS-RING A) (FORALL n (FORALL r (FORALL k
     (IMPLIES (IN n NN)
     (IMPLIES (IN r (CARR A))
       (IN (ELEM-H A n r k) (MAT n n (CARR A))))))))))))
(dk-peel!)                                     ; IS-RING A, n in NN, r in CARR A
(mac 'ELEM-H)
(dk-matof!)
(dk-peel!)                                     ; i in [1,n], j in [1,n]
(lam-b)                                        ; (IN (IF (= i j) (IF (= i k) r ONE) ZERO) (CARR A))
(fact 'ring-one-in 'A)
(fact 'ring-zero-in 'A)
(mtb-close-if!)
(mtb-qed! 'elem-h-type)
(topic! 'elem-h-type 'algebra)

;;; ---- matmul-type ------------------------------------------------------
;;;
;;; GUARDED 2026-09-16 on `n = 0 implies (m = 0 or k = 0)'.  Without it the
;;; statement is FALSE: with n = 0, Q = [] is in MAT(0, k, CARR A) for every
;;; natural k, MATMUL reads its column count off SIZE([]) = [0, 0], and an
;;; m-by-0 P times [] is m-by-0, not m-by-k.  Square and one-sided-square
;;; citers ((n,n,n), (m,m,n), (m,n,n)) discharge the guard by `prop'.

(sp (make-wff '(FORALL A (IMPLIES (IS-RING A)
     (FORALL m (FORALL n (FORALL k (FORALL P (FORALL Q
       (IMPLIES (IN P (MAT m n (CARR A)))
       (IMPLIES (IN Q (MAT n k (CARR A)))
       (IMPLIES (IMPLIES (= n 0) (OR (= m 0) (= k 0)))
         (IN (MATMUL A P Q) (MAT m k (CARR A)))))))))))))))
(dk-peel!)                                     ; IS-RING A, P, Q, the guard
(mac 'MATMUL)
;; the row count of the product is m, always
(fact 'mat-rows-in-nn 'm 'n '(CARR A) 'P)
(fact 'mat-size-rows 'm 'n '(CARR A) 'P)
(subst '(= (NTH 1 (SIZE P)) m))
;; the column count is NTH(2, SIZE Q), a natural; the product is a MATOF of
;; that shape, and mat-colcount-transfer moves it to MAT(m, k)
(fact 'mat-size-cols-in-nn 'n 'k '(CARR A) 'Q)
(define mtb-prod (cadr (dk-goal)))
(have! (list 'IN mtb-prod '(MAT m (NTH 2 (SIZE Q)) (CARR A)))
  (lambda ()
    (dk-matof!)
    (dk-peel!)                                 ; i in [1,m], c in [1, NTH(2, SIZE Q)]
    (let* ((ivl (lambda (hi) (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                                        (equal? (caddr f) (list 'INTERVAL 1 hi))))
                                      "an index")))
           (i0  (cadr (ivl 'm)))
           (c0  (cadr (ivl '(NTH 2 (SIZE Q))))))
      ;; P has rows (1 <= i <= m): its column count is n.  The sum below runs
      ;; over [1, NTH(2, SIZE P)]; that term sits inside the pair-lambda, which
      ;; is in OPERATOR position of the goal ((VNB-LAMBDA ...) i c), and `subst'
      ;; does not rewrite in operator position (replace-term walks arguments
      ;; only; CLAUDE.md).  So the matrices are restated at that dimension.
      (dk-one-le-from! i0 'm)
      (fact 'mat-size-cols 'm 'n '(CARR A) 'P)
      ;; the product has columns (1 <= c <= NTH(2, SIZE Q)): that count is k
      (dk-one-le-from! c0 '(NTH 2 (SIZE Q)))
      (fact 'mat-size-cols-pos 'n 'k '(CARR A) 'Q)
      (have! (list 'IN c0 '(INTERVAL 1 k))
        (lambda () (subst '(= k (NTH 2 (SIZE Q)))) (ass)))
      (lam-b)                                  ; (IN (FINSUM (RAS A) LAM [1,n]) (CARR A))
      (let ((lam (let ((g (dk-goal)))
                   (if (and (pair? g) (eq? (car g) 'IN)
                            (pair? (cadr g)) (eq? (car (cadr g)) 'FINSUM))
                       (caddr (cadr g))
                       (error "matmul-type: goal is not a FINSUM membership after lam-b"
                              (expression->string g))))))
        (let ((hi '(NTH 2 (SIZE P))))
          (have! (list 'IN 'P (list 'MAT 'm hi '(CARR A)))
            (lambda () (subst (list '= hi 'n)) (ass)))
          (dk-focus-having! (list 'IN 'P (list 'MAT 'm hi '(CARR A))))
          (have! (list 'IN 'Q (list 'MAT hi 'k '(CARR A)))
            (lambda () (subst (list '= hi 'n)) (ass)))
          (dk-focus-having! (list 'IN 'Q (list 'MAT hi 'k '(CARR A))))
          (fact 'mat-rows-in-nn hi 'k '(CARR A) 'Q)          ; hi in NN
          (fact 'interval-in-set 1 hi)
          (fact 'interval-card-in-nn 1 hi)
          ;; the summand j |-> P_ij * Q_jc is a function [1,hi] -> CARR A
          (have! (list 'IN lam (list 'FUN (list 'INTERVAL 1 hi) '(CARR A)))
            (lambda ()
              (let* ((opened (dk-opened (lambda () (lam-t))))
                     (sets   (filter (lambda (l) (let ((g (dk-goal-of l)))
                                                   (and (pair? g) (eq? (car g) 'IN) (eq? (caddr g) 'SET))))
                                     opened))
                     (typs   (filter (lambda (l) (not (memq l sets))) opened)))
                (if (not (and (= 1 (length sets)) (= 1 (length typs))))
                    (error "matmul-type: lam-t opened" (map (lambda (l) (expression->string (dk-goal-of l))) opened)))
                (dk-focus! (car sets)) (ass)   ; [1,hi] in SET
                (dk-focus! (car typs))
                (let ((z (dk-di-var!)))        ; z in [1,hi]
                  (fact 'entry-in-carrier 'm hi '(CARR A) 'P i0 z)
                  (fact 'entry-in-carrier hi 'k '(CARR A) 'Q z c0)
                  (fact 'ring-carrier-closed-mul 'A (list 'ENTRY 'P i0 z) (list 'ENTRY 'Q z c0))
                  (ass)))))
          (dk-focus-having! (list 'IN lam (list 'FUN (list 'INTERVAL 1 hi) '(CARR A))))
          (fact 'finsum-type-ring-additive-ag 'A (list 'INTERVAL 1 hi) lam))
        (ass)))))
(dk-focus-having! (list 'IN mtb-prod '(MAT m (NTH 2 (SIZE Q)) (CARR A))))
(fact 'mat-colcount-transfer 'n 'k '(CARR A) 'Q 'm '(CARR A) mtb-prod)
(ass)
(mtb-qed! 'matmul-type)
(topic! 'matmul-type 'algebra)
