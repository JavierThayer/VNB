;;; matmul-entry-proof.scm -- the matrix-product entry formula, PROVEN.
;;;
;;;   forall A. IS-RING(A) => forall m n k P Q.
;;;     P in MAT(m,n,CARR A) => Q in MAT(n,k,CARR A) => 1 <= n =>
;;;       forall i in [1,m], c in [1,k].
;;;         ENTRY(MATMUL(A,P,Q), i, c)
;;;           = FINSUM(RING-ADDITIVE-AG A,
;;;                    j |-> (MUL A)(ENTRY(P,i,j), ENTRY(Q,j,c)),
;;;                    [1,n])
;;;
;;; The statement is structure-library/matrix.scm's `matmul-entry' support
;;; (asserted, warranted `reference'), UNCHANGED -- including the `1 <= n' guard
;;; added by the SIZE/MAT surgery of 2026-09-16.  Retire the support there.
;;;
;;; PLAN.  MATMUL(A,P,Q) is a MATOF, so the equation is `entry-of-matof'
;;; (theorem-library/tuple-tabulation.scm) applied to its tabulator.  Three
;;; steps, and the first two are matmul-type's (theorem-library/
;;; mat-typing-bundle.scm), which this file follows:
;;;
;;;   1. THE DIMENSIONS.  `mac MATMUL' leaves a MATOF whose shape is written in
;;;      SIZE terms: NTH(1,SIZE P), NTH(2,SIZE Q), and -- inside the tabulator --
;;;      NTH(2,SIZE P).  mat-basics.scm reads them off the two MAT hypotheses:
;;;      `mat-size-rows' unguarded (= m), `mat-size-cols' guarded on the row
;;;      count being at least one -- 1 <= m off the row index i (dk-one-le-from!),
;;;      1 <= n the statement's own guard.
;;;
;;;      TWO of the three go into the goal by `subst'; the third does NOT.
;;;      MATMUL's tabulator is vnb-lambda([i, k], ...), so rewriting
;;;      NTH(2,SIZE Q) to `k' would put a free `k' in the lambda's DOMAIN --
;;;      which `replace-term' walks even under capture, the domain being outside
;;;      the binder -- beside the bound `k' of its body: one formula carrying two
;;;      variables spelled `k' (CLAUDE.md, "Case folding", rule 4).  The column
;;;      count is left as the term it is and c's typing is restated at it
;;;      instead.  (Since 2026-09-16 `subst' also rewrites in OPERATOR position,
;;;      so the matrices need not be restated at the unrewritten dimension the
;;;      way matmul-type restates them; the sum's index bound NTH(2,SIZE P)
;;;      becomes `n' in place, inside the pair-lambda.)
;;;
;;;   2. THE DEFINEDNESS HYPOTHESIS.  `entry-of-matof' is guarded on the
;;;      tabulated value being a set at every index pair -- `=' is the
;;;      definedness predicate, and an arbitrary applied variable need not
;;;      denote.  Here the value is the FINSUM, which lands in CARR(A):
;;;      finsum-type-ring-additive-ag over the summand typed by dk-lam-t! +
;;;      entry-in-carrier twice + ring-carrier-closed-mul, then
;;;      membership-implies-sethood.  This is matmul-type's inner block.
;;;
;;;   3. THE EQUATION.  `entry-of-matof' lands ENTRY(MATOF(...),i,c) = LAM(i,c);
;;;      `lam-b-h' reduces the applied pair-lambda IN THE HYPOTHESIS and the
;;;      result IS the goal.  The FORWARD route, for elem-entry-readoffs.scm's
;;;      reason: goal-side the equation would end as `t = t', which `rfl'
;;;      refuses -- a FINSUM over an arbitrary ring is not syntactically
;;;      self-defined -- while entry-of-matof grants the definedness outright.
;;;
;;; LOAD WINDOW [lo, hi):
;;;   lo -- after theorem-library/interval-card-in-nn (load.scm ~1044), the
;;;         LATEST of the citations.  The others are all above it:
;;;         equality-basics (equality-symmetry), interval-basics
;;;         (interval-in-set, interval-elt-in-nn, interval-lo, interval-hi),
;;;         mat-basics (mat-rows-in-nn, mat-cols-in-nn, mat-size-rows,
;;;         mat-size-cols), entry-in-carrier, op-typing
;;;         (ring-carrier-closed-mul), cancellation (the RING-ADDITIVE-AG view
;;;         companion finsum-type-ring-additive-ag), nn-order-ord (nn-one-in),
;;;         nn-order-basics (nn-le-trans-guarded), tuple-tabulation
;;;         (entry-of-matof); membership-implies-sethood is a base axiom.
;;;   hi -- before theorem-library/triple-entry-proof (load.scm ~1585), the
;;;         earliest citer of matmul-entry.
;;;   The slot chosen is immediately after theorem-library/mat-typing-bundle.
;;;
;;; ONE WARNING IS EXPECTED and is about MATMUL's definition, not this proof:
;;; `symbol i is both bound (in some binder) and free in this formula', twice,
;;; at the entry-of-matof citation.  The tabulator binds [i, k] while the
;;; statement's row index is also spelled `i'; the two are distinct variables
;;; and every walker treats them so.  Renaming MATMUL's binders in matrix.scm
;;; would retire it.
;;;
;;; Helper prefix: me-.

(sp (make-wff
 '(FORALL A (IMPLIES (IS-RING A)
     (FORALL m (FORALL n (FORALL k (FORALL P (FORALL Q
       (IMPLIES (IN P (MAT m n (CARR A)))
       (IMPLIES (IN Q (MAT n k (CARR A)))
       (IMPLIES (<= 1 n)
       (FORALL i (IMPLIES (IN i (INTERVAL 1 m))
       (FORALL c (IMPLIES (IN c (INTERVAL 1 k))
         (= (ENTRY (MATMUL A P Q) i c)
            (FINSUM (RING-ADDITIVE-AG A)
                    (VNB-LAMBDA j (INTERVAL 1 n) ((MUL A) (ENTRY P i j) (ENTRY Q j c)))
                    (INTERVAL 1 n)))))))))))))))))))

;;; ---- helper (me-) -----------------------------------------------------

;; Report open goals loudly rather than qed a half-proof.
(define (me-qed! name)
  (if (proof-done? *ps*)
      (qed name)
      (begin
        (display ";;; *** matmul-entry-proof: ") (display name)
        (display " did NOT close.  Open goals:") (newline)
        (for-each (lambda (l)
                    (display ";;;    GOAL: ")
                    (display (expression->string (dk-goal-of l))) (newline)
                    (for-each (lambda (a)
                                (display ";;;       asm: ")
                                (display (expression->string a)) (newline))
                              (dk-asms-of l)))
                  (proof-leaves))
        (error "matmul-entry-proof: unfinished" name))))

;;; ---- the proof --------------------------------------------------------

(dk-peel!)                                     ; IS-RING A, P, Q, 1 <= n, i, c

;; 1.  The dimensions, off the two MAT hypotheses.
(fact 'mat-rows-in-nn 'm 'n '(CARR A) 'P)      ; m in NN
(fact 'mat-cols-in-nn 'm 'n '(CARR A) 'P)      ; n in NN
(fact 'mat-cols-in-nn 'n 'k '(CARR A) 'Q)      ; k in NN
(fact 'mat-size-rows 'm 'n '(CARR A) 'P)       ; NTH(1, SIZE P) = m, unguarded
(dk-one-le-from! 'i 'm)                        ; 1 <= m, off the row index
(fact 'mat-size-cols 'm 'n '(CARR A) 'P)       ; NTH(2, SIZE P) = n   (1 <= m)
(fact 'mat-size-cols 'n 'k '(CARR A) 'Q)       ; NTH(2, SIZE Q) = k   (1 <= n)
(fact 'equality-symmetry '(NTH 2 (SIZE Q)) 'k) ; k = NTH(2, SIZE Q)

(mac 'MATMUL)                                  ; ENTRY of a MATOF
(subst '(= (NTH 1 (SIZE P)) m))                ; the row count
(subst '(= (NTH 2 (SIZE P)) n))                ; the summation bound, in place
                                               ; NOT NTH(2, SIZE Q): see the header

(define me-cq '(NTH 2 (SIZE Q)))
(define me-lam (cadddr (cadr (cadr (dk-goal)))))

;; entry-of-matof's index premises, at the MATOF's own column count.
(have! (list 'IN me-cq 'NN)
       (lambda () (subst (list '= me-cq 'k)) (ass)))
(dk-focus-having! (list 'IN me-cq 'NN))
(have! (list 'IN 'c (list 'INTERVAL 1 me-cq))
       (lambda () (subst (list '= me-cq 'k)) (ass)))
(dk-focus-having! (list 'IN 'c (list 'INTERVAL 1 me-cq)))

;; 2.  The definedness hypothesis: the tabulated value is a set at every index
;;     pair, being the FINSUM, which lands in CARR(A).
(define me-defined
  (list 'FORALL 'i_
    (list 'IMPLIES (list 'IN 'i_ '(INTERVAL 1 m))
      (list 'FORALL 'j_
        (list 'IMPLIES (list 'IN 'j_ (list 'INTERVAL 1 me-cq))
          (list 'IN (list me-lam 'i_ 'j_) 'SET))))))

(have! me-defined
  (lambda ()
    (dk-peel!)                                 ; i_ in [1,m], j_ in [1, NTH(2,SIZE Q)]
    (have! '(IN j_ (INTERVAL 1 k))
           (lambda () (subst (list '= 'k me-cq)) (ass)))
    (dk-focus-having! '(IN j_ (INTERVAL 1 k)))
    (lam-b)                                    ; (IN (FINSUM ...) SET)
    (let ((fs (cadr (dk-goal))))
      (if (not (and (pair? fs) (eq? (car fs) 'FINSUM)))
          (error "matmul-entry: goal is not a FINSUM membership after lam-b"
                 (expression->string (dk-goal))))
      (let ((lam (caddr fs)))
        (fact 'interval-in-set 1 'n)
        (fact 'interval-card-in-nn 1 'n)
        (have! (list 'IN lam (list 'FUN '(INTERVAL 1 n) '(CARR A)))
          (lambda ()
            (dk-lam-t!)                        ; closes the [1,n] in SET leaf
            (let ((z (dk-di-var!)))            ; z in [1,n]
              (fact 'entry-in-carrier 'm 'n '(CARR A) 'P 'i_ z)
              (fact 'entry-in-carrier 'n 'k '(CARR A) 'Q z 'j_)
              (fact 'ring-carrier-closed-mul 'A (list 'ENTRY 'P 'i_ z) (list 'ENTRY 'Q z 'j_))
              (ass))))
        (dk-focus-having! (list 'IN lam (list 'FUN '(INTERVAL 1 n) '(CARR A))))
        (fact 'finsum-type-ring-additive-ag 'A '(INTERVAL 1 n) lam)
        (fact 'membership-implies-sethood fs '(CARR A))
        (ass)))))
(dk-focus-having! me-defined)

;; 3.  The equation, and the beta in the HYPOTHESIS (the forward route).
(define me-eqn (dk-fact! 'entry-of-matof 'm me-cq me-lam 'i 'c))
(lam-b-h me-eqn)
(ass)
(me-qed! 'matmul-entry)
(topic! 'matmul-entry 'algebra)
