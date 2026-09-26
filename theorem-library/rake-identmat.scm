;;; rake-identmat.scm -- the two IDENTMAT identity laws and the module twin of
;;; matmul-entry, PROVEN (batch K, 2026-09-17).
;;;
;;;   identmat-left-identity    structure-library/matrix.scm:484   (well-known)
;;;   identmat-right-identity   structure-library/matrix.scm:507   (well-known)
;;;   matact-entry              structure-library/mod-seq.scm:116  (reference)
;;;
;;; All three statements are copied byte-for-byte from those sites.
;;;
;;; THE TWO IDENTITIES.  matrix-entry-extensionality reduces I_m P = P to an
;;; entry identity over [1,m] x [1,n]; matmul-entry expands the entry to
;;; FINSUM_j delta_{row,j} P_{j,col}; off j = row the summand is 0.P_{jc} = 0
;;; (identmat's off-diagonal entry + ring-mul-zero-left + ras-id), so
;;; finsum-single-support collapses the sum to its j = row term, which is
;;; 1.P_{row,col} = P_{row,col} (ring-mul-left-id).  The right-handed twin is the
;;; mirror image: the surviving index is j = col, and the two ring steps are
;;; ring-mul-zero-right / ring-mul-right-id.  This is the route the retired
;;; warrants describe, and theorem-library/matunit-shift-proof.scm is the worked
;;; example of it (same collapse, MATUNIT in place of IDENTMAT).
;;;
;;; NO GUARD IS NEEDED, and that is worth stating because the 2026-09-16
;;; SIZE/MAT surgery guarded almost every neighbour.  The middle dimension of
;;; I_m . P is m and of P . I_n is n, so matmul-type's guard
;;; `middle = 0 => (rows = 0 or cols = 0)' is propositionally trivial in both
;;; cases (the middle dimension IS one of the two outer ones), and the entry
;;; identity is vacuous when m = 0 or n = 0 -- the index interval is empty and
;;; matmul-entry is never cited.  Both identities are therefore TRUE at every
;;; dimension, including the zero-row and zero-column matrices, and both proofs
;;; obtain `1 <= middle' from the row or column index rather than from a guard
;;; (dk-one-le-from!).
;;;
;;; matact-entry is matmul-entry-proof.scm's driver with the module
;;; substitutions -- (ACT md) for (MUL A), MODULE-VECTOR-AG for RING-ADDITIVE-AG,
;;; VEC md for the vector entries -- and matact-summand-type (PROVEN,
;;; theorem-library/lam-fun-bricks.scm) in place of the hand-built FUN typing.
;;;
;;; THE ONE OBSTACLE, and it is a LOAD-ORDER one.  The IDENTMAT entry read-offs
;;; the warrants name -- `entry-of-identmat', `identmat-entry-diag',
;;; `identmat-entry-off' -- are PROVEN, in theorem-library/elem-entry-readoffs
;;; (load position 333).  The earliest citer of the two identities is
;;; theorem-library/mat-ring-proof (332).  So the window those citations would
;;; force, [334, 332), is EMPTY BY ONE SLOT.  Rather than ask for a shared file
;;; to move, this file derives the entry equation inline -- `rkd-identmat-entry!'
;;; below, six lines of lane plus its definedness helper: IDENTMAT is a MATOF,
;;; `entry-of-matof' (PROVEN, theorem-library/tuple-tabulation) gives the entry
;;; as the tabulator applied to the index pair, and `lam-b-h' reduces it.  If the
;;; integrator prefers, elem-entry-readoffs CAN move: every theorem it cites
;;; loads at or below position 234 (entry-of-matof; the full list is
;;; entry-of-matof, matrix-entry-extensionality, entry-in-carrier, mat-basics'
;;; size read-offs, interval-basics, interval-membership, nn-order-*, op-typing,
;;; ring-zero-one-power, equality-symmetry, membership-implies-sethood), so it
;;; can sit anywhere in [235, 332) and then `rkd-identmat-entry!' collapses to
;;; two `fact' citations.
;;;
;;; LOAD WINDOW [298, 332) -- 0-based over load.scm's `*vnb-files*' entries.
;;;   lo = 298, immediately after theorem-library/lam-fun-bricks (297), the
;;;        LATEST citation: matprod-summand-type and matact-summand-type live
;;;        there.  The others are earlier -- matunit-matact-type 243
;;;        (matact-type), matmul-entry-proof 242 (matmul-entry),
;;;        mat-typing-bundle 240 (identmat-type, matmul-type),
;;;        interval-card-in-nn 239, tuple-tabulation 234 (entry-of-matof),
;;;        tuple-extensionality 233 (matrix-entry-extensionality),
;;;        ring-zero-one-power 210 (ring-one-in, ring-mul-zero-left/-right),
;;;        finsum-single-support 201, finsum-type-proof 199 (finsum-type),
;;;        entry-in-carrier 174, mat-basics 170, ag-view-read-offs 161
;;;        (ras-id, mvag-carr), interval-basics 151, plus the structure files
;;;        (ring, module, views, matrix, mod-seq).
;;;   hi = 332, theorem-library/mat-ring-proof, the earliest PROVEN citer of
;;;        identmat-left-identity and identmat-right-identity (mat-equiv-proof
;;;        341, mod-basis-proof 364, spans-transport 366, rank-bound 367 come
;;;        later).  matact-entry's own hi is 356 (matact-row-linear-proof), so
;;;        one position serves all three.
;;;
;;; Helper prefix: rkd-.

;;; ---- file-local drivers ------------------------------------------------

(define (rkd-wf vars body) (fold-right (lambda (v b) (list 'FORALL v b)) body vars))
(define (rkd-wi prems body) (fold-right (lambda (p b) (list 'IMPLIES p b)) body prems))

(define (rkd-done! name)
  (if (proof-done? *ps*)
      (qed name)
      (begin
        (display "\n*** rake-identmat: ") (display name)
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
        (error "rake-identmat: unfinished" name))))

;; An IF term is resolved by the kit's (dk-if-branch! TRUE? IFTERM CLOSE-COND K):
;; `if-true'/`if-false' open the CONDITION leaf and the MAIN goal, which gains
;; (= IFTERM branch) as an assumption.  (rkd-if-branch! retired 2026-09-25.)

;; (rkd-close-in!) -- goal (IN (IF c a b) SET) with c undecided: split on c,
;; resolve the IF on each side, and close from the context.
(define (rkd-close-in!)
  (let ((g (dk-goal)))
    (if (and (pair? g) (eq? (car g) 'IN) (pair? (cadr g)) (eq? (car (cadr g)) 'IF))
        (let ((ift (cadr g)))
          (use-em (cadr ift)
            (lambda () (dk-if-branch! #t  ift ass rkd-close-in!))
            (lambda () (dk-if-branch! #f ift ass rkd-close-in!))))
        (ass))))

;; (rkd-defined! DIM LAM) -- land entry-of-matof's definedness hypothesis for
;; IDENTMAT(A,DIM): the tabulated value is ONE(A) or ZERO(A), both sets.
(define (rkd-defined! dim lam)
  (let ((stmt (rkd-wf '(u_)
                (rkd-wi (list (list 'IN 'u_ (list 'INTERVAL 1 dim)))
                  (rkd-wf '(v_)
                    (rkd-wi (list (list 'IN 'v_ (list 'INTERVAL 1 dim)))
                      (list 'IN (list lam 'u_ 'v_) 'SET)))))))
    (have! stmt
      (lambda ()
        (dk-peel!)
        (fact 'ring-one-in 'A)
        (fact 'ring-zero-in 'A)
        (fact 'membership-implies-sethood '(ONE A) '(CARR A))
        (fact 'membership-implies-sethood '(ZERO A) '(CARR A))
        (lam-b)
        (rkd-close-in!)))
    (dk-focus-having! stmt)
    stmt))

;; (rkd-identmat-entry! DIM I J) -- land
;;     ENTRY(IDENTMAT(A,DIM), I, J) = IF (I = J) then ONE(A) else ZERO(A)
;; with (IN I (INTERVAL 1 DIM)), (IN J (INTERVAL 1 DIM)) and (IN DIM NN) in
;; context.  This is `entry-of-identmat' (elem-entry-readoffs.scm:878) inline;
;; see the header for why it is not cited.
(define (rkd-identmat-entry! dim i j)
  (let ((tgt (list '= (list 'ENTRY (list 'IDENTMAT 'A dim) i j)
                   (list 'IF (list '= i j) '(ONE A) '(ZERO A)))))
    (if (not (dk-asm? tgt))
        (begin
          (have! tgt
            (lambda ()
              (mac 'IDENTMAT)                    ; ENTRY of a MATOF
              (let* ((e   (cadr (dk-goal)))
                     (mf  (cadr e))
                     (lam (cadddr mf)))
                (if (not (and (pair? mf) (eq? (car mf) 'MATOF)))
                    (error "rkd-identmat-entry!: IDENTMAT did not unfold to a MATOF"
                           (expression->string (dk-goal))))
                (rkd-defined! dim lam)
                (lam-b-h (dk-fact! 'entry-of-matof dim dim lam i j))
                (ass))))
          (dk-focus-having! tgt)))
    tgt))

;; (rkd-neq-sym! X Y) -- land (NOT (= X Y)) from (NOT (= Y X)) in context.
(define (rkd-neq-sym! x y)
  (let ((tgt (list 'NOT (list '= x y))))
    (if (not (dk-asm? tgt))
        (begin
          (have! tgt
            (lambda ()
              (di)
              (fact 'equality-symmetry x y)
              (ai (list 'NOT (list '= y x)))))
          (dk-focus-having! tgt)))
    tgt))

;;; =======================================================================
;;; identmat-left-identity:  I_m . P = P.
;;; Statement: structure-library/matrix.scm:484, unchanged.
;;; =======================================================================

(define RKD-I '(IDENTMAT A m))
(define RKD-L (list 'MATMUL 'A RKD-I 'P))
(define RKD-RAG '(RING-ADDITIVE-AG A))
(define RKD-LFF (list 'VNB-LAMBDA 'j '(INTERVAL 1 m)
                      (list '(MUL A) (list 'ENTRY RKD-I 'row 'j) '(ENTRY P j col))))

(sp (make-wff
 '(FORALL A (IMPLIES (IS-RING A) (FORALL m (FORALL n (FORALL P
     (IMPLIES (IN P (MAT m n (CARR A)))
       (= (MATMUL A (IDENTMAT A m) P) P))))))))) 
(dk-peel!)                                     ; IS-RING A, P in MAT(m,n,CARR A)
(fact 'mat-rows-in-nn 'm 'n '(CARR A) 'P)      ; m in NN
(fact 'mat-cols-in-nn 'm 'n '(CARR A) 'P)      ; n in NN
(fact 'identmat-type 'A 'm)                    ; I_m in MAT(m,m,CARR A)
;; matmul-type's zero-middle guard: the middle dimension IS the row count here
(dk-have-prop! '(IMPLIES (= m 0) (OR (= m 0) (= n 0))))
(fact 'matmul-type 'A 'm 'm 'n RKD-I 'P)       ; I_m P in MAT(m,n,CARR A)

;; ---- the entry identity, cut and proved first ----
(define RKD-LENT
  (rkd-wf '(row) (rkd-wi '((IN row (INTERVAL 1 m)))
    (rkd-wf '(col) (rkd-wi '((IN col (INTERVAL 1 n)))
      (list '= (list 'ENTRY RKD-L 'row 'col) '(ENTRY P row col)))))))

(dk-focus! (find-first (lambda (l) (equal? (dk-goal-of l) RKD-LENT))
                       (dk-opened (lambda () (cut RKD-LENT)))))
(dk-peel!)                                     ; row in [1,m], col in [1,n]
(dk-one-le-from! 'row 'm)                      ; 1 <= m, matmul-entry's guard
(fact 'matmul-entry 'A 'm 'm 'n RKD-I 'P 'row 'col)
(subst (list '= (list 'ENTRY RKD-L 'row 'col)
             (list 'FINSUM RKD-RAG RKD-LFF '(INTERVAL 1 m))))
;; finsum-single-support's non-VANISH premises
(fact 'ring-additive-ag-is-abelian-group 'A)
(fact 'interval-in-set 1 'm)
(fact 'interval-card-in-nn 1 'm)
(fact 'matprod-summand-type 'A 'm 'm 'n RKD-I 'P 'row 'col)
;; VANISH: off j = row the summand is the additive identity
(define RKD-LVAN
  (rkd-wf '(jz) (rkd-wi (list '(IN jz (INTERVAL 1 m)) '(NOT (= jz row)))
                        (list '= (list RKD-LFF 'jz) (list 'IDEN RKD-RAG)))))
(dk-focus! (find-first (lambda (l) (equal? (dk-goal-of l) RKD-LVAN))
                       (dk-opened (lambda () (cut RKD-LVAN)))))
(dk-peel!)
(lam-b)
(rkd-neq-sym! 'row 'jz)
(rkd-identmat-entry! 'm 'row 'jz)
(subst (list '= (list 'ENTRY RKD-I 'row 'jz) '(IF (= row jz) (ONE A) (ZERO A))))
(dk-if-branch! #f '(IF (= row jz) (ONE A) (ZERO A)) ass
  (lambda ()
    (fact 'entry-in-carrier 'm 'n '(CARR A) 'P 'jz 'col)
    (fact 'ring-mul-zero-left 'A '(ENTRY P jz col))
    (subst '(= ((MUL A) (ZERO A) (ENTRY P jz col)) (ZERO A)))
    (fact 'ras-id 'A)
    (subst (list '= (list 'IDEN RKD-RAG) '(ZERO A)))
    (rfl)))
;; back on the entry identity: collapse the sum and reduce the surviving term
(dk-focus-having! RKD-LVAN)
(fact 'finsum-single-support RKD-RAG '(INTERVAL 1 m) RKD-LFF 'row)
(subst (list '= (list 'FINSUM RKD-RAG RKD-LFF '(INTERVAL 1 m)) (list RKD-LFF 'row)))
(lam-b)
(rkd-identmat-entry! 'm 'row 'row)
(subst (list '= (list 'ENTRY RKD-I 'row 'row) '(IF (= row row) (ONE A) (ZERO A))))
(dk-if-branch! #t '(IF (= row row) (ONE A) (ZERO A)) rfl
  (lambda ()
    (fact 'entry-in-carrier 'm 'n '(CARR A) 'P 'row 'col)
    (fact 'ring-mul-left-id 'A '(ENTRY P row col))
    (subst '(= ((MUL A) (ONE A) (ENTRY P row col)) (ENTRY P row col)))
    (rfl)))
;; ---- back in the main goal: extensionality ----
(dk-focus-having! RKD-LENT)
(fact 'matrix-entry-extensionality 'm 'n '(CARR A) RKD-L 'P)
(ass)
(rkd-done! 'identmat-left-identity)
(topic! 'identmat-left-identity 'algebra)

;;; =======================================================================
;;; identmat-right-identity:  P . I_n = P.
;;; Statement: structure-library/matrix.scm:507, unchanged.
;;; The mirror image: the surviving index is j = col, and the two ring steps
;;; are ring-mul-zero-right / ring-mul-right-id.
;;; =======================================================================

(define RKD-J '(IDENTMAT A n))
(define RKD-R (list 'MATMUL 'A 'P RKD-J))
(define RKD-RFF (list 'VNB-LAMBDA 'j '(INTERVAL 1 n)
                      (list '(MUL A) '(ENTRY P row j) (list 'ENTRY RKD-J 'j 'col))))

(sp (make-wff
 '(FORALL A (IMPLIES (IS-RING A) (FORALL m (FORALL n (FORALL P
     (IMPLIES (IN P (MAT m n (CARR A)))
       (= (MATMUL A P (IDENTMAT A n)) P)))))))))
(dk-peel!)
(fact 'mat-rows-in-nn 'm 'n '(CARR A) 'P)
(fact 'mat-cols-in-nn 'm 'n '(CARR A) 'P)
(fact 'identmat-type 'A 'n)                    ; I_n in MAT(n,n,CARR A)
;; matmul-type's zero-middle guard: the middle dimension IS the column count
(dk-have-prop! '(IMPLIES (= n 0) (OR (= m 0) (= n 0))))
(fact 'matmul-type 'A 'm 'n 'n 'P RKD-J)

(define RKD-RENT
  (rkd-wf '(row) (rkd-wi '((IN row (INTERVAL 1 m)))
    (rkd-wf '(col) (rkd-wi '((IN col (INTERVAL 1 n)))
      (list '= (list 'ENTRY RKD-R 'row 'col) '(ENTRY P row col)))))))

(dk-focus! (find-first (lambda (l) (equal? (dk-goal-of l) RKD-RENT))
                       (dk-opened (lambda () (cut RKD-RENT)))))
(dk-peel!)                                     ; row in [1,m], col in [1,n]
(dk-one-le-from! 'col 'n)                      ; 1 <= n, matmul-entry's guard
(fact 'matmul-entry 'A 'm 'n 'n 'P RKD-J 'row 'col)
(subst (list '= (list 'ENTRY RKD-R 'row 'col)
             (list 'FINSUM RKD-RAG RKD-RFF '(INTERVAL 1 n))))
(fact 'ring-additive-ag-is-abelian-group 'A)
(fact 'interval-in-set 1 'n)
(fact 'interval-card-in-nn 1 'n)
(fact 'matprod-summand-type 'A 'm 'n 'n 'P RKD-J 'row 'col)
;; VANISH: off j = col the summand is the additive identity
(define RKD-RVAN
  (rkd-wf '(jz) (rkd-wi (list '(IN jz (INTERVAL 1 n)) '(NOT (= jz col)))
                        (list '= (list RKD-RFF 'jz) (list 'IDEN RKD-RAG)))))
(dk-focus! (find-first (lambda (l) (equal? (dk-goal-of l) RKD-RVAN))
                       (dk-opened (lambda () (cut RKD-RVAN)))))
(dk-peel!)
(lam-b)
(rkd-identmat-entry! 'n 'jz 'col)
(subst (list '= (list 'ENTRY RKD-J 'jz 'col) '(IF (= jz col) (ONE A) (ZERO A))))
(dk-if-branch! #f '(IF (= jz col) (ONE A) (ZERO A)) ass
  (lambda ()
    (fact 'entry-in-carrier 'm 'n '(CARR A) 'P 'row 'jz)
    (fact 'ring-mul-zero-right 'A '(ENTRY P row jz))
    (subst '(= ((MUL A) (ENTRY P row jz) (ZERO A)) (ZERO A)))
    (fact 'ras-id 'A)
    (subst (list '= (list 'IDEN RKD-RAG) '(ZERO A)))
    (rfl)))
(dk-focus-having! RKD-RVAN)
(fact 'finsum-single-support RKD-RAG '(INTERVAL 1 n) RKD-RFF 'col)
(subst (list '= (list 'FINSUM RKD-RAG RKD-RFF '(INTERVAL 1 n)) (list RKD-RFF 'col)))
(lam-b)
(rkd-identmat-entry! 'n 'col 'col)
(subst (list '= (list 'ENTRY RKD-J 'col 'col) '(IF (= col col) (ONE A) (ZERO A))))
(dk-if-branch! #t '(IF (= col col) (ONE A) (ZERO A)) rfl
  (lambda ()
    (fact 'entry-in-carrier 'm 'n '(CARR A) 'P 'row 'col)
    (fact 'ring-mul-right-id 'A '(ENTRY P row col))
    (subst '(= ((MUL A) (ENTRY P row col) (ONE A)) (ENTRY P row col)))
    (rfl)))
(dk-focus-having! RKD-RENT)
(fact 'matrix-entry-extensionality 'm 'n '(CARR A) RKD-R 'P)
(ass)
(rkd-done! 'identmat-right-identity)
(topic! 'identmat-right-identity 'algebra)

;;; =======================================================================
;;; matact-entry:  (P.u)_{ic} = sum_{j=1}^{n} P_{ij} . u_{jc}.
;;; Statement: structure-library/mod-seq.scm:116, unchanged -- including the
;;; `1 <= n' guard the SIZE/MAT surgery added on 2026-09-16.
;;;
;;; theorem-library/matmul-entry-proof.scm's driver, with the module
;;; substitutions: (ACT md) for (MUL A), MODULE-VECTOR-AG for RING-ADDITIVE-AG,
;;; VEC(md) for the entry class of u and CARR(SCAL md) for that of P.  The three
;;; steps are its three: read the tabulator's dimensions off the two MAT
;;; hypotheses (NTH(2,SIZE u) is left as the term it is -- rewriting it to q
;;; would put a free q in the pair-lambda's own domain, beside its bound c);
;;; land entry-of-matof's definedness hypothesis (the value is the FINSUM, typed
;;; by matact-summand-type + finsum-type in the vector group); and reduce the
;;; applied pair-lambda in the HYPOTHESIS with lam-b-h.
;;;
;;; ONE WARNING IS EXPECTED, as in matmul-entry-proof, and it is about MATACT's
;;; definition rather than this proof: `symbol i is both bound (in some binder)
;;; and free in this formula' at the entry-of-matof citation -- MATACT's
;;; tabulator binds [i, c] while the statement's own indices are spelled i and c.
;;; =======================================================================

(sp (make-wff
 '(FORALL md (IMPLIES (IS-MODULE md)
     (FORALL m (FORALL n (FORALL q (FORALL P (FORALL u
       (IMPLIES (IN P (MAT m n (CARR (SCAL md))))
       (IMPLIES (IN u (MAT n q (VEC md)))
       (IMPLIES (<= 1 n)
       (FORALL i (IMPLIES (IN i (INTERVAL 1 m))
       (FORALL c (IMPLIES (IN c (INTERVAL 1 q))
         (= (ENTRY (MATACT md P u) i c)
            (FINSUM (MODULE-VECTOR-AG md)
                    (VNB-LAMBDA j (INTERVAL 1 n) ((ACT md) (ENTRY P i j) (ENTRY u j c)))
                    (INTERVAL 1 n)))))))))))))))))))
(dk-peel!)                                     ; IS-MODULE md, P, u, 1 <= n, i, c

;; 1.  The dimensions, off the two MAT hypotheses.
(fact 'mat-rows-in-nn 'm 'n '(CARR (SCAL md)) 'P)      ; m in NN
(fact 'mat-cols-in-nn 'm 'n '(CARR (SCAL md)) 'P)      ; n in NN
(fact 'mat-cols-in-nn 'n 'q '(VEC md) 'u)              ; q in NN
(fact 'mat-size-rows 'm 'n '(CARR (SCAL md)) 'P)       ; NTH(1,SIZE P) = m
(dk-one-le-from! 'i 'm)                                ; 1 <= m, off the row index
(fact 'mat-size-cols 'm 'n '(CARR (SCAL md)) 'P)       ; NTH(2,SIZE P) = n  (1 <= m)
(fact 'mat-size-cols 'n 'q '(VEC md) 'u)               ; NTH(2,SIZE u) = q  (1 <= n)
(fact 'equality-symmetry '(NTH 2 (SIZE u)) 'q)

(mac 'MATACT)                                  ; ENTRY of a MATOF
(subst '(= (NTH 1 (SIZE P)) m))                ; the row count
(subst '(= (NTH 2 (SIZE P)) n))                ; the summation bound, in place

(define rkd-cq '(NTH 2 (SIZE u)))
(define rkd-alam (cadddr (cadr (cadr (dk-goal)))))

;; entry-of-matof's index premises, at the MATOF's own column count.
(have! (list 'IN rkd-cq 'NN)
       (lambda () (subst (list '= rkd-cq 'q)) (ass)))
(dk-focus-having! (list 'IN rkd-cq 'NN))
(have! (list 'IN 'c (list 'INTERVAL 1 rkd-cq))
       (lambda () (subst (list '= rkd-cq 'q)) (ass)))
(dk-focus-having! (list 'IN 'c (list 'INTERVAL 1 rkd-cq)))

;; 2.  The definedness hypothesis: the tabulated value is the FINSUM, which
;;     lands in CARR(MODULE-VECTOR-AG md).
(define rkd-adef
  (list 'FORALL 'i_
    (list 'IMPLIES (list 'IN 'i_ '(INTERVAL 1 m))
      (list 'FORALL 'j_
        (list 'IMPLIES (list 'IN 'j_ (list 'INTERVAL 1 rkd-cq))
          (list 'IN (list rkd-alam 'i_ 'j_) 'SET))))))

(have! rkd-adef
  (lambda ()
    (dk-peel!)                                 ; i_ in [1,m], j_ in [1, NTH(2,SIZE u)]
    (have! '(IN j_ (INTERVAL 1 q))
           (lambda () (subst (list '= 'q rkd-cq)) (ass)))
    (dk-focus-having! '(IN j_ (INTERVAL 1 q)))
    (lam-b)                                    ; (IN (FINSUM ...) SET)
    (let ((fs (cadr (dk-goal))))
      (if (not (and (pair? fs) (eq? (car fs) 'FINSUM)))
          (error "matact-entry: goal is not a FINSUM membership after lam-b"
                 (expression->string (dk-goal))))
      (fact 'module-vector-ag-is-abelian-group 'md)
      (fact 'interval-in-set 1 'n)
      (fact 'interval-card-in-nn 1 'n)
      (fact 'matact-summand-type 'md 'm 'n 'q 'P 'u 'i_ 'j_)
      (fact 'finsum-type '(MODULE-VECTOR-AG md) '(INTERVAL 1 n) (caddr fs))
      (fact 'membership-implies-sethood fs '(CARR (MODULE-VECTOR-AG md)))
      (ass))))
(dk-focus-having! rkd-adef)

;; 3.  The equation, and the beta in the HYPOTHESIS (the forward route).
(lam-b-h (dk-fact! 'entry-of-matof 'm rkd-cq rkd-alam 'i 'c))
(ass)
(rkd-done! 'matact-entry)
(topic! 'matact-entry 'algebra)
