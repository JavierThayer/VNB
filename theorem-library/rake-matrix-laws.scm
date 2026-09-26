;;; rake-matrix-laws.scm -- the eight matrix-algebra laws of `mat-ring-is-ring',
;;; PROVEN by ONE entrywise driver.
;;;
;;; The statements are structure-library/matrix.scm's supports, copied LITERALLY
;;; from their definition sites (matrix.scm:435-457, :492-506, :514-523):
;;;
;;;   matadd-comm        P + Q = Q + P
;;;   matadd-assoc       (P + Q) + R = P + (Q + R)
;;;   matadd-zero-left   0 + P = P          matadd-zero-right  P + 0 = P
;;;   matadd-neg-left  (-P) + P = 0         matadd-neg-right   P + (-P) = 0
;;;   matmul-left-dist   P(Q + R) = PQ + PR
;;;   matmul-right-dist  (P + Q)R = PR + QR
;;;
;;; THE MECHANISM (`rml-ext!', one procedure, eight uses).  Two matrices of the
;;; same MAT(m,n,CARR A) are equal when their entries are
;;; (`matrix-entry-extensionality', theorem-library/tuple-extensionality.scm --
;;; UNGUARDED in m, so at m = 0 its entry premise is vacuous and the law is
;;; proved with no case split).  So every law is:
;;;
;;;   1. TYPE BOTH SIDES in one MAT(m,n,CARR A)  (matadd-type, matneg-type,
;;;      zeromat-type, matmul-type -- also the LUTINS precondition for
;;;      instantiating extensionality at those compound terms);
;;;   2. CITE extensionality and prove its entry premise;
;;;   3. inside it, READ each side's entry with its constructor's entry lemma
;;;      (matadd-entry, matneg-entry, entry-of-zeromat, matmul-entry) and
;;;   4. CLOSE with the corresponding law of A at the entries, which are typed
;;;      by entry-in-carrier.
;;;
;;; The six additive laws differ from one another only in (1), (3) and the ring
;;; law of (4); each is six lines.  The two distributive laws put a FINSUM on
;;; each side and step (4) becomes ring-left/right-dist UNDER the summand
;;; (finsum-congruence-guarded) plus finsum-add-ag; the driver is unchanged.
;;;
;;; matneg-entry (the MATNEG entry read-off) DID NOT EXIST -- MATADD, MATSCALE,
;;; ZEROMAT, IDENTMAT, UNITROW and the four elementary constructors all have one
;;; (theorem-library/elem-entry-readoffs.scm) and MATNEG was the hole.  It is
;;; proven here, by that file's own route (restate the dimension and index
;;; typings at the tabulator's SIZE terms, entry-of-matof, beta in the
;;; hypothesis); its natural home is elem-entry-readoffs.scm.
;;;
;;; ------------------------------------------------------------------------
;;; THE TWO DISTRIBUTIVE LAWS ARE GUARDED, and the names change accordingly.
;;;
;;; As asserted, `matmul-left-dist' / `matmul-right-dist' carry NO guard on the
;;; inner dimension n, while every other law about a product whose middle
;;; dimension may be zero does (docs/size-mat-surgery-2026-09-16.md s.4).  The
;;; statements are not false -- at n = 0 with m, k >= 1 both sides degenerate to
;;; the same m-by-0 matrix -- but they are NOT REACHABLE by the entrywise
;;; mechanism there: `matmul-type' is guarded on `n = 0 => (m = 0 or k = 0)'
;;; exactly because an m-by-0 times [] is m-by-0 and not m-by-k, so at n = 0
;;; neither side can be typed in MAT(m,k,CARR A) and extensionality cannot be
;;; cited.  Proving the unguarded form needs a separate degenerate branch (a
;;; column-count typing `MATMUL(A,P,Q) in MAT(m, NTH 2 (SIZE Q), CARR A)', which
;;; the library does not have) and no citer needs it.
;;;
;;; So the guarded forms are installed under `matmul-left-dist-guarded' and
;;; `matmul-right-dist-guarded', with matmul-type's own guard
;;;     (IMPLIES (= n 0) (OR (= m 0) (= k 0)))
;;; as a premise placed AFTER the binders, so the citations' argument lists are
;;; unchanged.  The one citer, theorem-library/mat-ring-proof.scm:186, uses them
;;; at (n,n,n) and already holds that guard: it is MR-GUARDS' first element
;;; (mat-ring-proof.scm:107), proved there by `prop'.
;;; ------------------------------------------------------------------------
;;;
;;; LOAD WINDOW [elem-entry-readoffs, mat-ring-proof) -- see the note below.
;;;   lo -- theorem-library/elem-entry-readoffs (matadd-entry, entry-of-zeromat),
;;;         which TODAY LOADS AFTER mat-ring-proof and must be MOVED ABOVE IT.
;;;         The two are adjacent entries in load.scm (~:1795 and ~:1809), neither
;;;         cites a name the other installs, so the swap is a one-line move.
;;;         Other citations, all far below: ring.scm (ring-add-comm/-assoc/
;;;         -left-id/-left-inv/-left-dist/-right-dist, definitional), op-typing
;;;         (ring-carrier-closed-mul, ring-neg-in-carr), mat-basics
;;;         (mat-rows-in-nn, mat-cols-in-nn, mat-size-rows, mat-size-cols),
;;;         entry-in-carrier, interval-basics (interval-in-set), rake-algebra
;;;         (ring-add-right-id), rake-algebra2 (ring-add-right-inv),
;;;         tuple-extensionality (matrix-entry-extensionality), tuple-tabulation
;;;         (entry-of-matof), interval-card-in-nn, rake-finsum-laws
;;;         (finsum-add-ag, finsum-congruence-guarded, finsum-type-ptwise),
;;;         mat-typing-bundle (zeromat-type, matmul-type), rake-mat-typing
;;;         (matadd-type, matneg-type), matmul-entry-proof (matmul-entry),
;;;         views / ag-view-read-offs (ring-additive-ag-is-abelian-group, ras-op),
;;;         lam-fun-bricks (matprod-summand-type).
;;;   hi -- theorem-library/mat-ring-proof, the ONLY proof citer of all eight
;;;         (swept over structure-library/, theorem-library/ and calculus/).
;;;   Tactics: the early kit only (dk-*, have!, detach!, prop through
;;;   dk-have-prop!, arith through dk-nonzero!).
;;;
;;; RETIRES structure-library/matrix.scm:435-440 (matadd-comm), :441-447
;;; (matadd-assoc), :448-452 (matadd-zero-left), :453-457 (matadd-neg-left),
;;; :492-499 (matmul-left-dist), :500-507 (matmul-right-dist), :514-518
;;; (matadd-zero-right), :519-523 (matadd-neg-right), each with its warrant!.
;;;
;;; THE INTEGRATOR ALSO HAS TO:
;;;   * move "theorem-library/elem-entry-readoffs" in load.scm to the slot just
;;;     ABOVE "theorem-library/mat-ring-proof" (they are adjacent; neither cites
;;;     a name the other installs), and put this file between them;
;;;   * rewrite the two distributivity citations at
;;;     theorem-library/mat-ring-proof.scm:186-187 to `matmul-left-dist-guarded'
;;;     / `matmul-right-dist-guarded' -- the ARGUMENT LISTS ARE UNCHANGED, and
;;;     the guard those citations need is already in that proof's context
;;;     (MR-GUARDS, mat-ring-proof.scm:107);
;;;   * rename the same two names in theorem-library/pss-topics.scm:289-290 and
;;;     theorem-library/reference-topics.scm:169.
;;;
;;; Helper prefix: rml-.

;;; =====================================================================
;;; file-local helpers
;;; =====================================================================

(define RML-CARR '(CARR A))

(define (rml-qed! name)
  (if (proof-done? *ps*)
      (qed name)
      (begin
        (display "\n;;; *** rake-matrix-laws: ") (display name)
        (display " did NOT close.  Open goals:") (newline)
        (for-each (lambda (l)
                    (display ";;;    GOAL: ")
                    (display (expression->string (dk-goal-of l))) (newline)
                    (for-each (lambda (a)
                                (display ";;;       asm: ")
                                (display (expression->string a)) (newline))
                              (dk-asms-of l)))
                  (proof-leaves))
        (error "rake-matrix-laws: unfinished" name))))

;;; the eigenvariable of a landed guard (IN x CLS), by the class
(define (rml-eigen landed cls)
  (let loop ((l landed))
    (cond ((null? l) (error "rml-eigen: nothing landed in" (expression->string cls)))
          ((and (pair? (car l)) (eq? (caar l) 'IN) (equal? (caddr (car l)) cls))
           (cadr (car l)))
          (#t (loop (cdr l))))))

;;; land the sole undischarged antecedent of the instantiation chain CH by
;;; proving it with BODY, then detach.  The antecedent is READ OFF CH, never
;;; rebuilt from the printed statement (rake-generates-coeff.scm's rule).
(define (rml-detach-with! ch body)
  (if (not (and (pair? ch) (eq? (car ch) 'IMPLIES)))
      (error "rml-detach-with!: not an implication" (expression->string ch)))
  (let ((ante (cadr ch)))
    (have! ante body)
    (dk-focus-having! ante)
    (detach! ch)))

;;; ---------------------------------------------------------------------
;;; THE DRIVER.  Goal (= LHS RHS), both sides already typed in MAT(M,N,CARR A)
;;; in the context; ENTRY! is called on the two index eigenvariables with the
;;; goal (= (ENTRY LHS i j) (ENTRY RHS i j)).
;;; ---------------------------------------------------------------------
(define (rml-ext! m n entry!)
  (let* ((g   (dk-goal))
         (lhs (cadr g))
         (rhs (caddr g)))
    (if (not (and (pair? g) (eq? (car g) '=)))
        (error "rml-ext!: the goal is not an equation" (expression->string g)))
    (rml-detach-with!
      (dk-fact! 'matrix-entry-extensionality m n RML-CARR lhs rhs)
      (lambda ()
        (let* ((ld (dk-peel!))
               (iv (rml-eigen ld (list 'INTERVAL 1 m)))
               (jv (rml-eigen ld (list 'INTERVAL 1 n))))
          (entry! iv jv))))
    (ass)))

;;; (rml-law! NAME STMT M N TYPE! ENTRY!) -- state, peel, read the dimensions
;;; off P, land the typings, run the driver, qed.
(define (rml-law! name stmt m n type! entry!)
  (sp (make-wff stmt))
  (dk-peel!)
  (fact 'mat-rows-in-nn 'm 'n RML-CARR 'P)
  (fact 'mat-cols-in-nn 'm 'n RML-CARR 'P)
  (type!)
  (rml-ext! m n entry!)
  (rml-qed! name))

;;; the entry of P at (i,j) lies in CARR A -- said of each matrix in turn
(define (rml-entries! mm nn i j . ps)
  (for-each (lambda (p) (fact 'entry-in-carrier mm nn RML-CARR p i j)) ps))

(define (rml-e p i j) (list 'ENTRY p i j))

;;; =====================================================================
;;; matneg-entry -- the MATNEG entry read-off, the one missing member of the
;;; entry-lemma family.  Statement and route mirror `matadd-entry'
;;; (theorem-library/elem-entry-readoffs.scm:1220), with NEG for ADD.
;;;
;;; MATNEG tabulates at NTH(1,SIZE P) by NTH(2,SIZE P), not at m by n, so
;;; entry-of-matof cannot be applied at m, n: the dimension and index typings
;;; are RESTATED at the SIZE terms (the row index gives 1 <= m, which is what
;;; mat-size-cols needs), and the definedness lane carries its indices back to
;;; [1,m] x [1,n] for entry-in-carrier.
;;; =====================================================================

(define rml-r1 '(NTH 1 (SIZE P)))
(define rml-c1 '(NTH 2 (SIZE P)))

;; with (= T D) in context: land (IN T NN) and each (IN v (INTERVAL 1 T))
(define (rml-restate! t d vs)
  (have! (list 'IN t 'NN) (lambda () (subst (list '= t d)) (ass)))
  (dk-focus-having! (list 'IN t 'NN))
  (for-each (lambda (v)
              (let ((f (list 'IN v (list 'INTERVAL 1 t))))
                (have! f (lambda () (subst (list '= t d)) (ass)))
                (dk-focus-having! f)))
            vs))

;; the converse, inside the definedness lane
(define (rml-back! v t d)
  (let ((f (list 'IN v (list 'INTERVAL 1 d))))
    (have! f (lambda () (subst (list '= d t)) (ass)))
    (dk-focus-having! f)))

(define (rml-size-setup!)
  (fact 'mat-rows-in-nn 'm 'n RML-CARR 'P)
  (fact 'mat-cols-in-nn 'm 'n RML-CARR 'P)
  (dk-one-le-from! 'i 'm)
  (fact 'mat-size-rows 'm 'n RML-CARR 'P)        ; NTH(1, SIZE P) = m
  (fact 'mat-size-cols 'm 'n RML-CARR 'P)        ; NTH(2, SIZE P) = n   (1 <= m)
  (rml-restate! rml-r1 'm '(i))
  (rml-restate! rml-c1 'n '(j)))

;; the index eigenvariables a peel landed, in order
(define (rml-index-vars landed)
  (map cadr (filter (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                     (pair? (caddr f)) (eq? (car (caddr f)) 'INTERVAL)))
                    landed)))

;; Goal (= (ENTRY (MATOF M N LAM) a b) RHS), the indices typed at M, N: land
;; entry-of-matof's equation in a lane whose definedness premise DEFINED! proves,
;; `lam-b-h' it, and return the reduced equation.
(define (rml-matof-eqn! defined!)
  (let* ((e   (cadr (dk-goal)))
         (mf  (cadr e))
         (mv  (cadr mf)) (nv (caddr mf)) (lam (cadddr mf))
         (a   (caddr e)) (b (cadddr e))
         (def (list 'FORALL 'i_ (list 'IMPLIES (list 'IN 'i_ (list 'INTERVAL 1 mv))
                (list 'FORALL 'j_ (list 'IMPLIES (list 'IN 'j_ (list 'INTERVAL 1 nv))
                  (list 'IN (list lam 'i_ 'j_) 'SET))))))
         (eqn (list '= e (list lam a b))))
    (have! def
      (lambda ()
        (let ((xy (rml-index-vars (dk-peel!))))
          (lam-b)
          (defined! (car xy) (cadr xy)))))
    (dk-focus-having! def)
    (have! eqn (lambda () (fact 'entry-of-matof mv nv lam a b) (ass)))
    (dk-focus-having! eqn)
    (lam-b-h eqn)
    (let ((q (find-first (lambda (f) (and (pair? f) (eq? (car f) '=) (equal? (cadr f) e)
                                          (not (equal? f eqn))))
                         (dk-asms))))
      (if (not q) (error "rml-matof-eqn!: lam-b-h landed no reduced equation"))
      q)))

(sp (make-wff
  '(FORALL A (FORALL m (FORALL n (FORALL P
     (IMPLIES (IS-RING A)
     (IMPLIES (IN P (MAT m n (CARR A)))
     (FORALL i (IMPLIES (IN i (INTERVAL 1 m))
     (FORALL j (IMPLIES (IN j (INTERVAL 1 n))
       (= (ENTRY (MATNEG A P) i j)
          ((NEG A) (ENTRY P i j)))))))))))))))
(dk-peel!)
(rml-size-setup!)
(mac 'MATNEG)
(rml-matof-eqn!
  (lambda (x y)                                  ; goal (IN ((NEG A) P_xy) SET)
    (rml-back! x rml-r1 'm)
    (rml-back! y rml-c1 'n)
    (fact 'entry-in-carrier 'm 'n RML-CARR 'P x y)
    (fact 'ring-neg-in-carr 'A (rml-e 'P x y))
    (fact 'membership-implies-sethood (list '(NEG A) (rml-e 'P x y)) RML-CARR)
    (ass)))
(ass)
(rml-qed! 'matneg-entry)
(topic! 'matneg-entry 'algebra)

;;; =====================================================================
;;; (1) matadd-comm
;;; =====================================================================
(rml-law! 'matadd-comm
  '(FORALL A (IMPLIES (IS-RING A) (FORALL m (FORALL n (FORALL P (FORALL Q
     (IMPLIES (IN P (MAT m n (CARR A)))
     (IMPLIES (IN Q (MAT m n (CARR A)))
       (= (MATADD A P Q) (MATADD A Q P))))))))))
  'm 'n
  (lambda ()
    (fact 'matadd-type 'A 'm 'n 'P 'Q)
    (fact 'matadd-type 'A 'm 'n 'Q 'P))
  (lambda (i j)
    (subst (dk-fact! 'matadd-entry 'A 'm 'n 'P 'Q i j))
    (subst (dk-fact! 'matadd-entry 'A 'm 'n 'Q 'P i j))
    (rml-entries! 'm 'n i j 'P 'Q)
    (fact 'ring-add-comm 'A (rml-e 'P i j) (rml-e 'Q i j))
    (ass)))

;;; =====================================================================
;;; (2) matadd-assoc
;;; =====================================================================
(rml-law! 'matadd-assoc
  '(FORALL A (IMPLIES (IS-RING A) (FORALL m (FORALL n (FORALL P (FORALL Q (FORALL R
     (IMPLIES (IN P (MAT m n (CARR A)))
     (IMPLIES (IN Q (MAT m n (CARR A)))
     (IMPLIES (IN R (MAT m n (CARR A)))
       (= (MATADD A (MATADD A P Q) R) (MATADD A P (MATADD A Q R)))))))))))))
  'm 'n
  (lambda ()
    (fact 'matadd-type 'A 'm 'n 'P 'Q)
    (fact 'matadd-type 'A 'm 'n 'Q 'R)
    (fact 'matadd-type 'A 'm 'n '(MATADD A P Q) 'R)
    (fact 'matadd-type 'A 'm 'n 'P '(MATADD A Q R)))
  (lambda (i j)
    (subst (dk-fact! 'matadd-entry 'A 'm 'n '(MATADD A P Q) 'R i j))
    (subst (dk-fact! 'matadd-entry 'A 'm 'n 'P '(MATADD A Q R) i j))
    (subst (dk-fact! 'matadd-entry 'A 'm 'n 'P 'Q i j))
    (subst (dk-fact! 'matadd-entry 'A 'm 'n 'Q 'R i j))
    (rml-entries! 'm 'n i j 'P 'Q 'R)
    (fact 'ring-add-assoc 'A (rml-e 'P i j) (rml-e 'Q i j) (rml-e 'R i j))
    (ass)))

;;; =====================================================================
;;; (3) matadd-zero-left      (4) matadd-zero-right
;;; =====================================================================
(define (rml-zero-law! name stmt add-args ring-law)
  (rml-law! name stmt 'm 'n
    (lambda ()
      (fact 'zeromat-type 'A 'm 'n)
      (apply fact 'matadd-type 'A 'm 'n add-args))
    (lambda (i j)
      (subst (apply dk-fact! 'matadd-entry 'A 'm 'n (append add-args (list i j))))
      (subst (dk-fact! 'entry-of-zeromat 'A 'm 'n i j))
      (rml-entries! 'm 'n i j 'P)
      (fact ring-law 'A (rml-e 'P i j))
      (ass))))

(rml-zero-law! 'matadd-zero-left
  '(FORALL A (IMPLIES (IS-RING A) (FORALL m (FORALL n (FORALL P
     (IMPLIES (IN P (MAT m n (CARR A)))
       (= (MATADD A (ZEROMAT A m n) P) P)))))))
  '((ZEROMAT A m n) P) 'ring-add-left-id)

(rml-zero-law! 'matadd-zero-right
  '(FORALL A (IMPLIES (IS-RING A) (FORALL m (FORALL n (FORALL P
     (IMPLIES (IN P (MAT m n (CARR A)))
       (= (MATADD A P (ZEROMAT A m n)) P)))))))
  '(P (ZEROMAT A m n)) 'ring-add-right-id)

;;; =====================================================================
;;; (5) matadd-neg-left       (6) matadd-neg-right
;;; =====================================================================
(define (rml-neg-law! name stmt add-args ring-law)
  (rml-law! name stmt 'm 'n
    (lambda ()
      (fact 'zeromat-type 'A 'm 'n)
      (fact 'matneg-type 'A 'm 'n 'P)
      (apply fact 'matadd-type 'A 'm 'n add-args))
    (lambda (i j)
      (subst (apply dk-fact! 'matadd-entry 'A 'm 'n (append add-args (list i j))))
      (subst (dk-fact! 'matneg-entry 'A 'm 'n 'P i j))
      (subst (dk-fact! 'entry-of-zeromat 'A 'm 'n i j))
      (rml-entries! 'm 'n i j 'P)
      (fact ring-law 'A (rml-e 'P i j))
      (ass))))

(rml-neg-law! 'matadd-neg-left
  '(FORALL A (IMPLIES (IS-RING A) (FORALL m (FORALL n (FORALL P
     (IMPLIES (IN P (MAT m n (CARR A)))
       (= (MATADD A (MATNEG A P) P) (ZEROMAT A m n))))))))
  '((MATNEG A P) P) 'ring-add-left-inv)

(rml-neg-law! 'matadd-neg-right
  '(FORALL A (IMPLIES (IS-RING A) (FORALL m (FORALL n (FORALL P
     (IMPLIES (IN P (MAT m n (CARR A)))
       (= (MATADD A P (MATNEG A P)) (ZEROMAT A m n))))))))
  '(P (MATNEG A P)) 'ring-add-right-inv)

;;; =====================================================================
;;; (7) matmul-left-dist-guarded    (8) matmul-right-dist-guarded
;;;
;;; Same driver; the entry goal is now an equation of FINSUMs over [1,n],
;;;
;;;    sum_j  P_ij . (Q+R)_jc   =   (sum_j P_ij.Q_jc) + (sum_j P_ij.R_jc)
;;;
;;; and step (4) of the mechanism splits in two:
;;;   * UNDER the summand, matadd-entry + ring-left-dist (resp. ring-right-dist)
;;;     turn L(j) into (OPR AG)(F(j), H(j)) -- transported to the sums by
;;;     finsum-congruence-guarded, whose FUN premise is matprod-summand-type;
;;;   * finsum-add-ag then splits the sum of the pointwise sum.
;;; `ras-op' rewrites (OPR (RING-ADDITIVE-AG A)) to (ADD A); it must normalize
;;; the GOAL and the finsum-add-ag EQUATION alike, or the two sums diverge and
;;; `ass' silently fails to match (matact-row-linear-proof.scm's lesson).
;;;
;;; 1 <= n -- matmul-entry's guard -- is free inside the entry lane: the row
;;; index gives 1 <= m and the column index 1 <= k, so m /= 0 and k /= 0, and
;;; the statement's guard read backwards gives n /= 0.
;;; =====================================================================

(define RML-AG '(RING-ADDITIVE-AG A))
(define RML-DIST-GUARD '(IMPLIES (= n 0) (OR (= m 0) (= k 0))))

;;; n /= 0 from the guard and the two index bounds.  NOT `prop': its narrowing
;;; keeps only assumptions sharing an atom with the goal and drops one of the
;;; two disjunct refutations (border-mult-proof.scm:170).
(define (rml-inner-nonzero!)
  (have! '(NOT (= n 0))
    (lambda ()
      (di)
      (detach! RML-DIST-GUARD)
      (for-each (lambda (l)
                  (dk-focus! l)
                  (if (member '(= m 0) (dk-asms-of l))
                      (ai '(NOT (= m 0)))
                      (ai '(NOT (= k 0)))))
                (dk-opened (lambda () (ai '(OR (= m 0) (= k 0))))))))
  (dk-focus-having! '(NOT (= n 0)))
  (dk-one-le! 'n))

;;; Goal  FINSUM(AG,L,[1,n]) = (ADD A)(FINSUM(AG,F,[1,n]), FINSUM(AG,H,[1,n])).
;;; TYPES! lands the three matprod-summand-type FUN typings; PW! closes
;;; (= (L z) (G z)) for the eigenvariable z it is handed.
(define (rml-finsum-split! types! pw!)
  (let* ((g     (dk-goal))
         (lhs   (cadr g))
         (rhs   (caddr g))
         (lam-l (caddr lhs))
         (ivl   (cadddr lhs))
         (lam-f (caddr (cadr rhs)))
         (lam-h (caddr (caddr rhs))))
    (if (not (and (pair? lhs) (eq? (car lhs) 'FINSUM)))
        (error "rml-finsum-split!: the entry goal is not an equation of FINSUMs"
               (expression->string g)))
    (fact 'ring-additive-ag-is-abelian-group 'A)
    (fact 'interval-in-set 1 'n)
    (fact 'interval-card-in-nn 1 'n)
    (types!)
    (let* ((add   (dk-fact! 'finsum-add-ag RML-AG ivl lam-f lam-h))
           (lam-g (caddr (cadr add))))
      (rml-detach-with!
        (dk-fact! 'finsum-congruence-guarded RML-AG ivl lam-l lam-g)
        (lambda ()
          (let* ((ld (dk-peel!))
                 (zv (rml-eigen ld ivl)))
            (pw! zv))))
      (subst (list '= (list 'FINSUM RML-AG lam-l ivl)
                   (list 'FINSUM RML-AG lam-g ivl)))
      (mac 'ras-op)
      (mac-h 'ras-op add)
      (ass))))

;;; a goal carrying an unreduced ((VNB-LAMBDA ...) ...) redex
(define (rml-redex? e)
  (cond ((not (pair? e)) #f)
        ((and (pair? (car e)) (eq? (car (car e)) 'VNB-LAMBDA)) #t)
        (#t (let loop ((l e))
              (cond ((not (pair? l)) #f)
                    ((rml-redex? (car l)) #t)
                    (#t (loop (cdr l))))))))

;;; beta to a fixpoint (a fixed count of `lam-b' calls would leave inert steps)
(define (rml-beta!)
  (let loop ((k 0))
    (if (> k 8) (error "rml-beta!: the redex does not go away"))
    (if (rml-redex? (dk-goal)) (begin (lam-b) (loop (+ k 1))))))

;;; the pointwise lane, common to both laws: beta both sides, rewrite the
;;; MATADD entry, apply the ring distributive law, normalize (OPR AG) and close.
(define (rml-pointwise! add-eqn dist-eqn prods)
  (rml-beta!)
  (subst add-eqn)
  (subst dist-eqn)
  (mac 'ras-op)
  (for-each (lambda (p) (fact 'ring-carrier-closed-mul 'A (car p) (cadr p))) prods)
  (fact 'ring-add-closed 'A
        (list '(MUL A) (car (car prods)) (cadr (car prods)))
        (list '(MUL A) (car (cadr prods)) (cadr (cadr prods))))
  (rfl))

(rml-law! 'matmul-left-dist-guarded
  '(FORALL A (IMPLIES (IS-RING A) (FORALL m (FORALL n (FORALL k (FORALL P (FORALL Q (FORALL R
     (IMPLIES (IN P (MAT m n (CARR A)))
     (IMPLIES (IN Q (MAT n k (CARR A)))
     (IMPLIES (IN R (MAT n k (CARR A)))
     (IMPLIES (IMPLIES (= n 0) (OR (= m 0) (= k 0)))
       (= (MATMUL A P (MATADD A Q R)) (MATADD A (MATMUL A P Q) (MATMUL A P R)))))))))))))))
  'm 'k
  (lambda ()
    (fact 'mat-cols-in-nn 'n 'k RML-CARR 'Q)
    (fact 'matadd-type 'A 'n 'k 'Q 'R)
    (fact 'matmul-type 'A 'm 'n 'k 'P '(MATADD A Q R))
    (fact 'matmul-type 'A 'm 'n 'k 'P 'Q)
    (fact 'matmul-type 'A 'm 'n 'k 'P 'R)
    (fact 'matadd-type 'A 'm 'k '(MATMUL A P Q) '(MATMUL A P R)))
  (lambda (i c)
    (dk-one-le-from! i 'm)
    (dk-one-le-from! c 'k)
    (dk-nonzero! 'm)
    (dk-nonzero! 'k)
    (rml-inner-nonzero!)
    (subst (dk-fact! 'matmul-entry 'A 'm 'n 'k 'P '(MATADD A Q R) i c))
    (subst (dk-fact! 'matadd-entry 'A 'm 'k '(MATMUL A P Q) '(MATMUL A P R) i c))
    (subst (dk-fact! 'matmul-entry 'A 'm 'n 'k 'P 'Q i c))
    (subst (dk-fact! 'matmul-entry 'A 'm 'n 'k 'P 'R i c))
    (rml-finsum-split!
      (lambda ()
        (fact 'matprod-summand-type 'A 'm 'n 'k 'P '(MATADD A Q R) i c)
        (fact 'matprod-summand-type 'A 'm 'n 'k 'P 'Q i c)
        (fact 'matprod-summand-type 'A 'm 'n 'k 'P 'R i c))
      (lambda (z)
        (rml-entries! 'm 'n i z 'P)
        (rml-entries! 'n 'k z c 'Q 'R)
        (rml-pointwise!
          (dk-fact! 'matadd-entry 'A 'n 'k 'Q 'R z c)
          (dk-fact! 'ring-left-dist 'A (rml-e 'P i z) (rml-e 'Q z c) (rml-e 'R z c))
          (list (list (rml-e 'P i z) (rml-e 'Q z c))
                (list (rml-e 'P i z) (rml-e 'R z c))))))))

(rml-law! 'matmul-right-dist-guarded
  '(FORALL A (IMPLIES (IS-RING A) (FORALL m (FORALL n (FORALL k (FORALL P (FORALL Q (FORALL R
     (IMPLIES (IN P (MAT m n (CARR A)))
     (IMPLIES (IN Q (MAT m n (CARR A)))
     (IMPLIES (IN R (MAT n k (CARR A)))
     (IMPLIES (IMPLIES (= n 0) (OR (= m 0) (= k 0)))
       (= (MATMUL A (MATADD A P Q) R) (MATADD A (MATMUL A P R) (MATMUL A Q R)))))))))))))))
  'm 'k
  (lambda ()
    (fact 'mat-cols-in-nn 'n 'k RML-CARR 'R)
    (fact 'matadd-type 'A 'm 'n 'P 'Q)
    (fact 'matmul-type 'A 'm 'n 'k '(MATADD A P Q) 'R)
    (fact 'matmul-type 'A 'm 'n 'k 'P 'R)
    (fact 'matmul-type 'A 'm 'n 'k 'Q 'R)
    (fact 'matadd-type 'A 'm 'k '(MATMUL A P R) '(MATMUL A Q R)))
  (lambda (i c)
    (dk-one-le-from! i 'm)
    (dk-one-le-from! c 'k)
    (dk-nonzero! 'm)
    (dk-nonzero! 'k)
    (rml-inner-nonzero!)
    (subst (dk-fact! 'matmul-entry 'A 'm 'n 'k '(MATADD A P Q) 'R i c))
    (subst (dk-fact! 'matadd-entry 'A 'm 'k '(MATMUL A P R) '(MATMUL A Q R) i c))
    (subst (dk-fact! 'matmul-entry 'A 'm 'n 'k 'P 'R i c))
    (subst (dk-fact! 'matmul-entry 'A 'm 'n 'k 'Q 'R i c))
    (rml-finsum-split!
      (lambda ()
        (fact 'matprod-summand-type 'A 'm 'n 'k '(MATADD A P Q) 'R i c)
        (fact 'matprod-summand-type 'A 'm 'n 'k 'P 'R i c)
        (fact 'matprod-summand-type 'A 'm 'n 'k 'Q 'R i c))
      (lambda (z)
        (rml-entries! 'm 'n i z 'P 'Q)
        (rml-entries! 'n 'k z c 'R)
        (rml-pointwise!
          (dk-fact! 'matadd-entry 'A 'm 'n 'P 'Q i z)
          (dk-fact! 'ring-right-dist 'A (rml-e 'P i z) (rml-e 'Q i z) (rml-e 'R z c))
          (list (list (rml-e 'P i z) (rml-e 'R z c))
                (list (rml-e 'Q i z) (rml-e 'R z c))))))))
