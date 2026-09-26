;;; rake-mat-typing.scm -- the ELEVEN matrix typing / sethood supports, PROVEN.
;;;
;;; Every constructor here is a MATOF, so every typing is `matof-in-mat'
;;; (PROVEN, theorem-library/matof-in-mat.scm) applied to its tabulator:
;;; unfold the constructor, `dk-matof!' (backchain matof-in-mat, close the two
;;; dimension-in-NN premises, focus the entry leaf), peel the two index
;;; binders, `lam-b' the pair-lambda, and type the value.  The three files this
;;; copies its mechanics from are theorem-library/mat-typing-bundle.scm
;;; (identmat/zeromat/matmul), theorem-library/mat-basics.scm (every MAT
;;; membership is read ONLY through mat-rows-in-nn / mat-cols-in-nn /
;;; mat-size-rows / mat-size-cols / mat-size-cols-in-nn) and
;;; theorem-library/elem-entry-readoffs.scm.
;;;
;;; WHAT IS PROVED, and where its statement came from (copied byte-for-byte):
;;;
;;;   mat-is-set      structure-library/matrix.scm:607
;;;   block-type      structure-library/matrix.scm:307
;;;   snoc-col-type   structure-library/matrix.scm:339
;;;   snoc-row-type   structure-library/matrix.scm:349
;;;   matadd-type     structure-library/matrix.scm:435
;;;   matscale-type   structure-library/matrix.scm:461
;;;   matneg-type     structure-library/matrix.scm:470
;;;   submat-type     structure-library/mat-equiv.scm:48
;;;   border-type     structure-library/mat-equiv.scm:94
;;;   minor-type      structure-library/determinant.scm:40
;;;   det-in-carrier  structure-library/determinant.scm:88
;;;
;;; plus TWO auxiliary theorems of its own.  The first is `rmm-carr', the
;;; missing member of the ag-view-read-offs.scm family (ras-carr / mvag-carr):
;;;
;;;   forall R. IS-RING(R) => CARR(RING-MULTIPLICATIVE-MONOID R) = CARR(R)
;;;
;;; det-in-carrier needs it and nothing in the tree had it.  Its driver is
;;; theorem-library/ag-view-read-offs.scm's `avr-read-off!' verbatim, including
;;; the same-symbol-both-sides repair (the opening `slot CARR' rewrites the
;;; goal's right-hand side too, so `nth(1,R) == carr(R)' is put back by a
;;; `have!' and one `subst').  Its natural home is that file.
;;;
;;; The second is `det-in-carrier-ind', det-in-carrier with the induction
;;; variable OUTERMOST -- `ni' tests the goal's SHAPE, literally
;;; (FORALL n (IMPLIES (IN n NN) body)), and the support's binder order is
;;; (R n A) with all three guards after, so the induction cannot be run on the
;;; statement as written.  The support's own statement is one `fact' off the
;;; companion.
;;;
;;; THREE THINGS THE PROOFS TURN ON, none of them obvious:
;;;
;;; (1) mat-is-set does NOT cite `matrix-sethood'.  That axiom
;;;     (structure-library/matrix.scm:77) carries no warrant at all, so citing
;;;     it would have made every MAT sethood bill `trust: none' -- WORSE than
;;;     the `reference' support being retired.  MATRIX(X) is a subclass of the
;;;     set TUPLES(TUPLES X) (matrix-membership's first conjunct), so
;;;     `tuples-sethood' twice and `subclass-of-set-is-set' give its sethood
;;;     inline, and the SEP rule does the rest: `modulo 0'.  matrix-sethood is
;;;     therefore itself provable and should be retired; it is cited nowhere
;;;     else in the tree.
;;;
;;; (2) MATADD / MATSCALE / MATNEG tabulate at NTH(1,SIZE P), NTH(2,SIZE P),
;;;     not at the literal m, n -- so, exactly as matmul-type does, the row
;;;     count is substituted away with mat-size-rows and the column count is
;;;     carried by `mat-colcount-transfer' (mat-typing-bundle.scm), whose
;;;     zero-middle-dimension guard is here `m = 0 => (m = 0 or n = 0)', closed
;;;     by `prop'.  This is what makes the statements true for a matrix with no
;;;     rows, where SIZE([]) = [0,0] and the column count is NOT n.
;;;
;;; (3) border-type's block branch needs `i in [1,succ p], i /= 1 =>
;;;     NN-MINUS(i,1) in [1,p]', which the tree has only as the ASSERTED
;;;     support `pred-in-interval' (structure-library/order-lemmas.scm:260,
;;;     well-known).  Citing it would have put a well-known leaf on border-type,
;;;     which is `reference' today -- a worse tier -- so it is proved inline
;;;     (`rkm-pred-in-interval!'): i is a successor (nn-nonzero-is-succ), the
;;;     monus is that predecessor (nn-minus-def + bt-succ-minus-1), and
;;;     succ z <= succ p gives z <= p through nn-not-le-succ-le +
;;;     nn-succ-le-antisym.  `pred-in-interval' is now provable too.
;;;
;;; DIMENSIONS ARE NOT RE-TYPED.  No statement gained a guard: every proof gets
;;; the naturality it needs either from the statement's own premises or, where
;;; the statement types no dimension (block-type's m and n), off the MATRIX by
;;; mat-rows-in-nn / mat-cols-in-nn.
;;;
;;; LOAD WINDOW [239, 328) -- 0-based over load.scm's `prover-load' entries.
;;;   lo = 239, immediately after theorem-library/mat-typing-bundle (238), the
;;;        LATEST citation: mat-colcount-transfer lives there.  The other
;;;        citations are earlier -- interval-card-in-nn 237, matof-in-mat 233,
;;;        nn-order-via-rr 218, comb-kk-laws 212 (bt-succ-minus-1),
;;;        cancellation 208 (finsum-type-ring-additive-ag), op-typing 198
;;;        (ring-add-closed, ring-carrier-closed-mul, ring-neg-in-carr),
;;;        subset-lemmas 192, entry-in-carrier 173, mat-basics 169,
;;;        ag-view-read-offs 161, interval-mem-intro 152, interval-basics 151,
;;;        finsum-additive 118 (nn-minus-def), and the structure files.
;;;   hi = 328, theorem-library/mat-ring-proof, the earliest PROVEN citer (it
;;;        cites matadd-type, matneg-type and mat-is-set).  The other citers are
;;;        later: border-mult 346, border-assembly 347, bordered-eq-border 348,
;;;        smith-diagonalization 350, smith-staircase 351, matact-row-linear
;;;        352, span-bricks 353, span-bricks2 354, lastcoeff-ideal 355,
;;;        spans-submodule-fg 356.  minor-type and det-in-carrier have no citer
;;;        at all.  One position serves all eleven; no split is needed.
;;;
;;; Helper prefix: rkm-.

;;; ---- file-local drivers ------------------------------------------------

;; The standard finish: report open goals loudly rather than qed a half proof.
(define (rkm-done! name)
  (if (proof-done? *ps*)
      (qed name)
      (begin
        (display "\n*** rake-mat-typing: ") (display name)
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
        (error "rake-mat-typing: unfinished" name))))

;; (rkm-if-branch! TRUE? IFTERM THUNK) -- `if-true' / `if-false' open TWO
;; leaves: the CONDITION (which the enclosing case split put in context) and
;; the MAIN goal, which gains the equation IF(c,a,b) = val as an ASSUMPTION --
;; the goal itself is NOT rewritten (CLAUDE.md), hence the explicit `subst'.
;; Discriminate the two on the GOAL, never on where focus landed.
(define (rkm-if-branch! true? ifterm thunk)
  (let* ((c      (cadr ifterm))
         (val    (if true? (caddr ifterm) (cadddr ifterm)))
         (want   (if true? c (list 'NOT c)))
         (opened (dk-opened (lambda () (if true? (if-true ifterm) (if-false ifterm)))))
         (conds  (filter (lambda (l) (alpha-equiv? (dk-goal-of l) want)) opened))
         (mains  (filter (lambda (l) (not (memq l conds))) opened)))
    (if (not (and (= 1 (length conds)) (= 1 (length mains))))
        (error "rkm-if-branch!: expected one condition leaf and one main leaf, got"
               (map (lambda (l) (expression->string (dk-goal-of l))) opened)))
    (dk-focus! (car conds)) (ass)
    (dk-focus! (car mains))
    (subst (list '= ifterm val))
    (thunk)))

;; (rkm-case-if! IFTERM K) -- split on the IF's condition, resolve the IF away
;; in the goal on each side, and hand the surviving VALUE to K.  Used where the
;; IF sits inside a term (MINOR's two index maps), not at the top of the goal.
(define (rkm-case-if! ifterm k)
  (let ((c (cadr ifterm)))
    (use-em c
      (lambda () (rkm-if-branch! #t  ifterm (lambda () (k (caddr  ifterm)))))
      (lambda () (rkm-if-branch! #f ifterm (lambda () (k (cadddr ifterm))))))))

;; (rkm-close-if! FALLBACK) -- resolve an IF TOWER at the top of a membership
;; goal (IN (IF ...) X) to exhaustion; FALLBACK closes each leaf goal.
(define (rkm-close-if! fallback)
  (let ((g (dk-goal)))
    (if (and (pair? g) (eq? (car g) 'IN)
             (pair? (cadr g)) (eq? (car (cadr g)) 'IF))
        (rkm-case-if! (cadr g) (lambda (v) (rkm-close-if! fallback)))
        (fallback))))

;; (rkm-widen! I LO HI) -- from (IN I (INTERVAL 1 LO)), (<= LO HI) and
;; (IN HI NN) in context, land (IN I (INTERVAL 1 HI)).
(define (rkm-widen! i lo hi)
  (fact 'interval-elt-in-nn 1 lo i)
  (fact 'interval-lo 1 lo i)
  (fact 'interval-hi 1 lo i)
  (fact 'nn-le-trans-guarded i lo hi)
  (fact 'interval-mem-intro 1 hi i))

;; (rkm-succ-widen! I B) -- from (IN I (INTERVAL 1 B)) and (IN B NN),
;; land (IN (succ I) (INTERVAL 1 (succ B))).
(define (rkm-succ-widen! i b)
  (fact 'interval-elt-in-nn 1 b i)
  (fact 'interval-lo 1 b i)
  (fact 'interval-hi 1 b i)
  (fact 'nn-succ-closed i)
  (fact 'nn-succ-closed b)
  (fact 'nn-one-le-succ i)
  (fact 'nn-succ-mono i b)
  (fact 'interval-mem-intro 1 (list 'succ b) (list 'succ i)))

;; (rkm-skip-widen! V I N) -- MINOR's index map: V is either I (kept) or
;; (succ I) (skipped past the deleted line).  Either way it lands in [1,succ N].
(define (rkm-skip-widen! v i n)
  (if (equal? v (list 'succ i))
      (rkm-succ-widen! i n)
      (begin (fact 'nn-succ-closed n)
             (fact 'nn-le-succ n)
             (rkm-widen! v n (list 'succ n)))))

;; (rkm-pred-in-interval! I B) -- with (IN I (INTERVAL 1 (succ B))),
;; (NOT (= I 1)) and (IN B NN) in context, land (IN (NN-MINUS I 1) (INTERVAL 1 B)).
;; This is `pred-in-interval' (order-lemmas.scm:260, an ASSERTED support),
;; proved: I is a successor, the monus is its predecessor, and the bound comes
;; down one storey.
(define (rkm-pred-in-interval! i b)
  (fact 'nn-one-in)
  (fact 'interval-elt-in-nn 1 (list 'succ b) i)
  (fact 'interval-lo 1 (list 'succ b) i)
  (fact 'interval-hi 1 (list 'succ b) i)
  (dk-nonzero! i)
  (let* ((ex  (dk-fact! 'nn-nonzero-is-succ i))
         (z   (dk-skolem! ex))
         (ift (list 'IF (list '<= 1 i) (list '- i 1) 0)))
    ;; NN-MINUS(i,1) = i - 1 = z
    (fact 'nn-minus-def i 1)
    (let ((opened (dk-opened (lambda () (if-true ift)))))
      (for-each (lambda (l) (if (alpha-equiv? (dk-goal-of l) (list '<= 1 i))
                                (begin (dk-focus! l) (ass))))
                opened)
      (dk-focus! (find-first (lambda (l) (not (alpha-equiv? (dk-goal-of l) (list '<= 1 i))))
                             opened)))
    (fact 'bt-succ-minus-1 z)
    (have! (list '= (list 'NN-MINUS i 1) z)
      (lambda ()
        (subst (list '= (list 'NN-MINUS i 1) ift))
        (subst (list '= ift (list '- i 1)))
        (subst (list '= i (list 'succ z)))
        (subst (list '= (list '- (list 'succ z) 1) z))
        (rfl)))
    (dk-focus-having! (list '= (list 'NN-MINUS i 1) z))
    ;; 1 <= z: z = 0 would make i = succ 0 = 1, which the branch denies
    (have! (list 'NOT (list '= z 0))
      (lambda ()
        (di)
        (have! (list '= 1 '(succ 0)) (lambda () (arith)))
        (have! (list '= i 1)
          (lambda ()
            (subst (list '= i (list 'succ z)))
            (subst (list '= z 0))
            (subst (list '= 1 '(succ 0)))
            (rfl)))
        (dk-focus-having! (list '= i 1))
        (ai (list 'NOT (list '= i 1)))))
    (dk-focus-having! (list 'NOT (list '= z 0)))
    (dk-one-le! z)
    ;; z <= b, from succ z = i <= succ b
    (fact 'nn-succ-closed z)
    (fact 'nn-succ-closed b)
    (have! (list '<= (list 'succ z) (list 'succ b))
      (lambda () (subst (list '= (list 'succ z) i)) (ass)))
    (dk-focus-having! (list '<= (list 'succ z) (list 'succ b)))
    (have! (list '<= z b)
      (lambda ()
        (use-em (list '<= z b)
          (lambda () (ass))
          (lambda ()                             ; succ b <= z with succ z <= succ b
            (fact 'nn-not-le-succ-le z b)        ; is succ z <= z, which
            (fact 'nn-le-trans-guarded (list 'succ z) (list 'succ b) z)
            (fact 'nn-succ-le-antisym z z)       ; denies z <= z
            (fact 'nn-le-refl z)
            (ai (list 'NOT (list '<= z z)))))))
    (dk-focus-having! (list '<= z b))
    (fact 'interval-mem-intro 1 b z)
    (let ((tgt (list 'IN (list 'NN-MINUS i 1) (list 'INTERVAL 1 b))))
      (if (alpha-equiv? (dk-goal) tgt)
          (begin (subst (list '= (list 'NN-MINUS i 1) z)) (ass))
          (begin
            (have! tgt (lambda () (subst (list '= (list 'NN-MINUS i 1) z)) (ass)))
            (dk-focus-having! tgt))))))

;; (rkm-entrywise! CON CLOSE-ENTRY!) -- the MATADD / MATSCALE / MATNEG driver.
;; The tabulator's dimensions are NTH(1,SIZE P) and NTH(2,SIZE P); the first is
;; m outright (mat-size-rows), the second is n only when P has rows, so the
;; result is typed at NTH(2,SIZE P) and carried to n by mat-colcount-transfer.
;; Assumes the binders are named A m n P (and the context holds IS-RING A and
;; (IN P (MAT m n (CARR A)))).  CLOSE-ENTRY! is called on the entry goal with
;; the two index eigenvariables.
(define (rkm-entrywise! con close-entry!)
  (mac con)
  (fact 'mat-rows-in-nn 'm 'n '(CARR A) 'P)
  (fact 'mat-cols-in-nn 'm 'n '(CARR A) 'P)
  (fact 'mat-size-rows 'm 'n '(CARR A) 'P)
  (subst '(= (NTH 1 (SIZE P)) m))
  (fact 'mat-size-cols-in-nn 'm 'n '(CARR A) 'P)
  (let ((tab (cadr (dk-goal))))
    (have! (list 'IN tab '(MAT m (NTH 2 (SIZE P)) (CARR A)))
      (lambda ()
        (dk-matof!)
        (dk-peel!)
        (let* ((ivl (lambda (hi) (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                                           (equal? (caddr f) (list 'INTERVAL 1 hi))))
                                          "an index")))
               (i0 (cadr (ivl 'm)))
               (j0 (cadr (ivl '(NTH 2 (SIZE P))))))
          (dk-one-le-from! i0 'm)                ; P has rows, so its column
          (fact 'mat-size-cols 'm 'n '(CARR A) 'P)   ; count is n
          (have! (list 'IN j0 '(INTERVAL 1 n))
            (lambda () (subst '(= n (NTH 2 (SIZE P)))) (ass)))
          (dk-focus-having! (list 'IN j0 '(INTERVAL 1 n)))
          (lam-b)
          (close-entry! i0 j0))))
    (dk-focus-having! (list 'IN tab '(MAT m (NTH 2 (SIZE P)) (CARR A))))
    (have! '(IMPLIES (= m 0) (OR (= m 0) (= n 0))) (lambda () (prop)))
    (dk-focus-having! '(IMPLIES (= m 0) (OR (= m 0) (= n 0))))
    (fact 'mat-colcount-transfer 'm 'n '(CARR A) 'P 'm '(CARR A) tab)
    (ass)))

;;; =====================================================================
;;; (1) mat-is-set -- MAT(m,n,X) is a SEP over MATRIX(X), which is a subclass
;;; of the set TUPLES(TUPLES X).  matrix-sethood is NOT cited (see the header).
;;; =====================================================================
(sp (make-wff
  '(FORALL X (IMPLIES (IN X SET) (FORALL m (FORALL n (IN (MAT m n X) SET)))))))
(dk-peel-to! 'IN)
(fact 'tuples-sethood 'X)
(fact 'tuples-sethood '(TUPLES X))
(have! '(SUBSET (MATRIX X) (TUPLES (TUPLES X)))
  (lambda ()
    (mac 'subset-def)
    (let ((h (dk-landed-1 (lambda () (di)))))
      (dk-split! (dk-landed-1 (lambda () (mac-h 'matrix-membership h))))
      (ass))))
(dk-focus-having! '(SUBSET (MATRIX X) (TUPLES (TUPLES X))))
(fact 'subclass-of-set-is-set '(MATRIX X) '(TUPLES (TUPLES X)))
(mac 'MAT)
(sep-set)
(ass)
(rkm-done! 'mat-is-set)
(topic! 'mat-is-set 'algebra)

;;; =====================================================================
;;; (2) block-type -- the leading k-by-l block.  m and n are NOT typed by the
;;; statement, so their naturality is read off P (mat-rows-in-nn / mat-cols-in-nn).
;;; =====================================================================
(sp (make-wff
  '(FORALL m (FORALL n (FORALL X (FORALL P (FORALL k (FORALL l (IMPLIES (IN k NN) (IMPLIES (IN l NN) (IMPLIES (IN P (MAT m n X)) (IMPLIES (<= k m) (IMPLIES (<= l n) (IN (BLOCK P k l) (MAT k l X)))))))))))))))
(dk-peel!)
(mac 'BLOCK)
(dk-matof!)
(dk-peel!)                                     ; i in [1,k], j in [1,l]
(lam-b)                                        ; (IN (ENTRY P i j) X)
(fact 'mat-rows-in-nn 'm 'n 'X 'P)
(fact 'mat-cols-in-nn 'm 'n 'X 'P)
(let* ((e  (cadr (dk-goal)))
       (i0 (caddr e))
       (j0 (cadddr e)))
  (rkm-widen! i0 'k 'm)
  (rkm-widen! j0 'l 'n)
  (fact 'entry-in-carrier 'm 'n 'X 'P i0 j0)
  (ass))
(rkm-done! 'block-type)
(topic! 'block-type 'algebra)

;;; =====================================================================
;;; (3) snoc-col-type -- [w_1..w_n, v].  The appended row is the succ n case of
;;; the tabulator's IF; every other row is an entry of w, which needs
;;; i <= n from i <= succ n and i /= succ n (nn-le-succ-cases).
;;; =====================================================================
(sp (make-wff
  '(FORALL X (FORALL n (FORALL w (FORALL v
     (IMPLIES (IN n NN)
     (IMPLIES (IN w (MAT n 1 X))
     (IMPLIES (IN v X)
       (IN (SNOC-COL w n v) (MAT (succ n) 1 X)))))))))))
(dk-peel!)
(fact 'nn-succ-closed 'n)
(fact 'nn-one-in)
(mac 'SNOC-COL)
(dk-matof!)
(dk-peel!)
(lam-b)
(let* ((ifterm (cadr (dk-goal)))
       (cnd    (cadr ifterm))
       (i0     (cadr cnd)))
  (use-em cnd
    (lambda () (rkm-if-branch! #t ifterm (lambda () (ass))))     ; the value is v
    (lambda ()
      (rkm-if-branch! #f ifterm
        (lambda ()
          (fact 'interval-elt-in-nn 1 '(succ n) i0)
          (fact 'interval-lo 1 '(succ n) i0)
          (fact 'interval-hi 1 '(succ n) i0)
          (fact 'nn-le-succ-cases 'n i0)
          (have! (list '<= i0 'n)
            (lambda ()
              (dk-only! (list 'OR (list '<= i0 'n) (list '= i0 '(succ n)))
                        (list 'NOT (list '= i0 '(succ n))))
              (prop)))
          (dk-focus-having! (list '<= i0 'n))
          (fact 'interval-mem-intro 1 'n i0)
          (fact 'one-in-interval-1)
          (fact 'entry-in-carrier 'n 1 'X 'w i0 1)
          (ass))))))
(rkm-done! 'snoc-col-type)
(topic! 'snoc-col-type 'algebra)

;;; =====================================================================
;;; (4) snoc-row-type -- the mirror image, in the column index.
;;; =====================================================================
(sp (make-wff
  '(FORALL X (FORALL n (FORALL c (FORALL r
     (IMPLIES (IN n NN)
     (IMPLIES (IN c (MAT 1 n X))
     (IMPLIES (IN r X)
       (IN (SNOC-ROW c n r) (MAT 1 (succ n) X)))))))))))
(dk-peel!)
(fact 'nn-succ-closed 'n)
(fact 'nn-one-in)
(mac 'SNOC-ROW)
(dk-matof!)
(dk-peel!)
(lam-b)
(let* ((ifterm (cadr (dk-goal)))
       (cnd    (cadr ifterm))
       (j0     (cadr cnd)))
  (use-em cnd
    (lambda () (rkm-if-branch! #t ifterm (lambda () (ass))))
    (lambda ()
      (rkm-if-branch! #f ifterm
        (lambda ()
          (fact 'interval-elt-in-nn 1 '(succ n) j0)
          (fact 'interval-lo 1 '(succ n) j0)
          (fact 'interval-hi 1 '(succ n) j0)
          (fact 'nn-le-succ-cases 'n j0)
          (have! (list '<= j0 'n)
            (lambda ()
              (dk-only! (list 'OR (list '<= j0 'n) (list '= j0 '(succ n)))
                        (list 'NOT (list '= j0 '(succ n))))
              (prop)))
          (dk-focus-having! (list '<= j0 'n))
          (fact 'interval-mem-intro 1 'n j0)
          (fact 'one-in-interval-1)
          (fact 'entry-in-carrier 1 'n 'X 'c 1 j0)
          (ass))))))
(rkm-done! 'snoc-row-type)
(topic! 'snoc-row-type 'algebra)

;;; =====================================================================
;;; (5) matadd-type -- entrywise sum.  See note (2) in the header.
;;; =====================================================================
(sp (make-wff
  '(FORALL A (IMPLIES (IS-RING A) (FORALL m (FORALL n (FORALL P (FORALL Q
     (IMPLIES (IN P (MAT m n (CARR A)))
     (IMPLIES (IN Q (MAT m n (CARR A)))
       (IN (MATADD A P Q) (MAT m n (CARR A)))))))))))))
(dk-peel!)
(rkm-entrywise! 'MATADD
  (lambda (i0 j0)
    (fact 'entry-in-carrier 'm 'n '(CARR A) 'P i0 j0)
    (fact 'entry-in-carrier 'm 'n '(CARR A) 'Q i0 j0)
    (fact 'ring-add-closed 'A (list 'ENTRY 'P i0 j0) (list 'ENTRY 'Q i0 j0))
    (ass)))
(rkm-done! 'matadd-type)
(topic! 'matadd-type 'algebra)

;;; =====================================================================
;;; (6) matscale-type -- entrywise scalar multiple.
;;; =====================================================================
(sp (make-wff
  '(FORALL A (IMPLIES (IS-RING A) (FORALL m (FORALL n (FORALL r (FORALL P
     (IMPLIES (IN r (CARR A))
     (IMPLIES (IN P (MAT m n (CARR A)))
       (IN (MATSCALE A r P) (MAT m n (CARR A)))))))))))))
(dk-peel!)
(rkm-entrywise! 'MATSCALE
  (lambda (i0 j0)
    (fact 'entry-in-carrier 'm 'n '(CARR A) 'P i0 j0)
    (fact 'ring-carrier-closed-mul 'A 'r (list 'ENTRY 'P i0 j0))
    (ass)))
(rkm-done! 'matscale-type)
(topic! 'matscale-type 'algebra)

;;; =====================================================================
;;; (7) matneg-type -- entrywise negation.
;;; =====================================================================
(sp (make-wff
  '(FORALL A (IMPLIES (IS-RING A) (FORALL m (FORALL n (FORALL P
     (IMPLIES (IN P (MAT m n (CARR A)))
       (IN (MATNEG A P) (MAT m n (CARR A)))))))))))
(dk-peel!)
(rkm-entrywise! 'MATNEG
  (lambda (i0 j0)
    (fact 'entry-in-carrier 'm 'n '(CARR A) 'P i0 j0)
    (fact 'ring-neg-in-carr 'A (list 'ENTRY 'P i0 j0))
    (ass)))
(rkm-done! 'matneg-type)
(topic! 'matneg-type 'algebra)

;;; =====================================================================
;;; (8) submat-type -- the lower-right block: index (i,j) is S_{succ i, succ j},
;;; and succ carries [1,p] into [1,succ p] (nn-succ-mono, nn-one-le-succ).
;;; =====================================================================
(sp (make-wff
  '(FORALL A (FORALL p (FORALL q (FORALL S
     (IMPLIES (IN p NN) (IMPLIES (IN q NN)
       (IMPLIES (IN S (MAT (succ p) (succ q) (CARR A)))
         (IN (SUBMAT S p q) (MAT p q (CARR A))))))))))))
(dk-peel!)
(mac 'SUBMAT)
(dk-matof!)
(dk-peel!)
(lam-b)
(let* ((e  (cadr (dk-goal)))
       (i0 (cadr (caddr e)))
       (j0 (cadr (cadddr e))))
  (rkm-succ-widen! i0 'p)
  (rkm-succ-widen! j0 'q)
  (fact 'entry-in-carrier '(succ p) '(succ q) '(CARR A) 'S (list 'succ i0) (list 'succ j0))
  (ass))
(rkm-done! 'submat-type)
(topic! 'submat-type 'algebra)

;;; =====================================================================
;;; (9) border-type -- [[b,0],[0,M]].  The IF tower has four leaves: b, ZERO A
;;; twice, and the block entry, whose index needs note (3) of the header.
;;; =====================================================================
(sp (make-wff
  '(FORALL A (FORALL b (FORALL M (FORALL p (FORALL q
     (IMPLIES (IS-RING A)
     (IMPLIES (IN p NN) (IMPLIES (IN q NN)
       (IMPLIES (IN b (CARR A))
       (IMPLIES (IN M (MAT p q (CARR A)))
         (IN (BORDER A b M p q) (MAT (succ p) (succ q) (CARR A)))))))))))))))
(dk-peel!)
(fact 'nn-succ-closed 'p)
(fact 'nn-succ-closed 'q)
(fact 'ring-zero-in 'A)
(mac 'BORDER)
(dk-matof!)
(dk-peel!)
(lam-b)
(let* ((ifterm (cadr (dk-goal)))
       (i0     (cadr (cadr ifterm)))            ; the (= i 1) condition
       (j0     (cadr (cadr (caddr ifterm)))))   ; the (= j 1) condition inside
  (rkm-close-if!
   (lambda ()
     (let ((v (cadr (dk-goal))))
       (if (and (pair? v) (eq? (car v) 'ENTRY))
           (begin
             (rkm-pred-in-interval! i0 'p)
             (rkm-pred-in-interval! j0 'q)
             (fact 'entry-in-carrier 'p 'q '(CARR A) 'M
                   (list 'NN-MINUS i0 1) (list 'NN-MINUS j0 1))
             (ass))
           (ass))))))                           ; b, or ZERO A
(rkm-done! 'border-type)
(topic! 'border-type 'algebra)

;;; =====================================================================
;;; (10) minor-type -- delete row p and column q.  Each index map is an IF
;;; inside a term, so it is resolved by `rkm-case-if!' and the surviving value
;;; (i or succ i) widened into [1, succ n].
;;; =====================================================================
(sp (make-wff
  '(FORALL R (FORALL S (FORALL p (FORALL q (FORALL n
     (IMPLIES (IS-RING R)
     (IMPLIES (IN p NN)
     (IMPLIES (IN q NN)
     (IMPLIES (IN n NN)
     (IMPLIES (IN S (MAT (succ n) (succ n) (CARR R)))
       (IN (MINOR S p q n) (MAT n n (CARR R)))))))))))))))
(dk-peel!)
(mac 'MINOR)
(dk-matof!)
(dk-peel!)
(lam-b)
(let* ((e   (cadr (dk-goal)))
       (rif (caddr e))                          ; (IF (< i p) i (succ i))
       (cif (cadddr e))                         ; (IF (< j q) j (succ j))
       (i0  (caddr rif))
       (j0  (caddr cif)))
  (rkm-case-if! rif
    (lambda (ri)
      (let ((cif2 (cadddr (cadr (dk-goal)))))   ; re-read: the goal was rewritten
        (rkm-case-if! cif2
          (lambda (ci)
            (rkm-skip-widen! ri i0 'n)
            (rkm-skip-widen! ci j0 'n)
            (fact 'entry-in-carrier '(succ n) '(succ n) '(CARR R) 'S ri ci)
            (ass)))))))
(rkm-done! 'minor-type)
(topic! 'minor-type 'algebra)

;;; =====================================================================
;;; (11) rmm-carr -- CARR(RING-MULTIPLICATIVE-MONOID R) = CARR(R).  The
;;; missing sibling of ras-carr / mvag-carr (ag-view-read-offs.scm); its
;;; driver is that file's `avr-read-off!' verbatim.  det-in-carrier needs it
;;; both ways round, to feed mpow-type its argument and to read its result.
;;; =====================================================================
(sp (make-wff
  '(FORALL R (IMPLIES (IS-RING R)
   (= (CARR (RING-MULTIPLICATIVE-MONOID R)) (CARR R))))))
(di)                                    ; the binder
(di)                                    ; the guard
(mac-h 'is-ring '(IS-RING R))
(dk-split-all!)
(slot 'CARR)
(mac 'RING-MULTIPLICATIVE-MONOID)
(nth-r)
(let ((proj (caddr (dk-goal))))         ; (NTH 1 R) -- `slot' rewrote the RHS too
  (have! (list '== proj '(CARR R)) (lambda () (slot 'CARR) (qrfl)))
  (subst (list '== proj '(CARR R))))
(rfl)
(rkm-done! 'rmm-carr)
(topic! 'rmm-carr 'plumbing)

;;; =====================================================================
;;; (12) det-in-carrier -- NN induction on the SIZE, with the matrix
;;; universally quantified INSIDE the induction (the minor of A is a different
;;; matrix, so the IH has to be available at every n-by-n matrix).  The
;;; support's own binder order (R n A, guards after) does not have the NN
;;; variable outermost, so `ni' cannot see it: the induction is run on a
;;; COMPANION statement and the support's statement is `fact'ed off it.
;;;
;;; Base: DET(R,0,A) == ONE(R) (det-zero, definitional).
;;; Step: det-cofactor turns DET(R,succ n,A) into a FINSUM over [1,succ n] in
;;; RING-ADDITIVE-AG(R); finsum-type-ring-additive-ag types it once the summand
;;; is a function into CARR(R), which `lam-t' reduces to typing
;;;    (-1)^(1+j) * (A_{1j} * det(minor)),
;;; i.e. mpow-type (through rmm-carr), entry-in-carrier, minor-type and the IH.
;;;
;;; BILL: `mpow-type' (structure-library/monoid-power.scm:43, ASSERTED,
;;; `informal') -- the monoid power stays in the carrier, an NN induction
;;; nobody has run.  It is the whole bill; batch G's ring-power-type is the
;;; same fact one view up.
;;; =====================================================================
(define rkm-rmm  '(RING-MULTIPLICATIVE-MONOID R))
(define rkm-sign '((NEG R) (ONE R)))

(sp (make-wff
  '(FORALL R (IMPLIES (IS-RING R)
     (FORALL n (IMPLIES (IN n NN)
       (FORALL A (IMPLIES (IN A (MAT n n (CARR R)))
         (IN (DET R n A) (CARR R))))))))))
(di) (di)
(define rkm-ind (use-induction))

;; ---- base ----
(dk-focus! (cdr (assq 'base rkm-ind)))
(let ((a0 (dk-di-var!)))
  (fact 'det-zero 'R a0)
  (fact 'ring-one-in 'R)
  (subst (list '== (list 'DET 'R 0 a0) '(ONE R)))
  (ass))

;; ---- step ----
(dk-focus! (cdr (assq 'step rkm-ind)))
(let ((a0 (dk-di-var!))
      (ih (cdr (assq 'ih rkm-ind))))
  (mac 'det-cofactor)
  (fact 'nn-succ-closed 'n)
  (fact 'interval-in-set 1 '(succ n))
  (fact 'interval-card-in-nn 1 '(succ n))
  (fact 'ring-one-in 'R)
  (fact 'ring-neg-in-carr 'R '(ONE R))
  (fact 'ring-multiplicative-monoid-is-monoid 'R)
  (fact 'rmm-carr 'R)
  (fact 'eq-sym (list 'CARR rkm-rmm) '(CARR R))
  (fact 'nn-one-in)
  (fact 'nn-le-refl 1)
  (fact 'nn-one-le-succ 'n)
  (fact 'interval-mem-intro 1 '(succ n) 1)      ; row 1 is a legal row index
  (have! (list 'IN rkm-sign (list 'CARR rkm-rmm))
    (lambda () (subst (list '= (list 'CARR rkm-rmm) '(CARR R))) (ass)))
  (dk-focus-having! (list 'IN rkm-sign (list 'CARR rkm-rmm)))
  (let ((lam (caddr (cadr (dk-goal)))))         ; the FINSUM's summand
    (have! (list 'IN lam (list 'FUN '(INTERVAL 1 (succ n)) '(CARR R)))
      (lambda ()
        (let* ((opened (dk-opened (lambda () (lam-t))))   ; TWO leaves: SET, pointwise
               (sets (filter (lambda (l) (let ((g (dk-goal-of l)))
                                           (and (pair? g) (eq? (car g) 'IN) (eq? (caddr g) 'SET))))
                             opened))
               (typs (filter (lambda (l) (not (memq l sets))) opened)))
          (if (not (and (= 1 (length sets)) (= 1 (length typs))))
              (error "det-in-carrier: lam-t opened"
                     (map (lambda (l) (expression->string (dk-goal-of l))) opened)))
          (dk-focus! (car sets)) (ass)
          (dk-focus! (car typs))
          (let ((j (dk-di-var!)))
            (fact 'interval-elt-in-nn 1 '(succ n) j)
            (fact 'nn-succ-closed j)
            (fact 'mpow-type rkm-rmm rkm-sign (list 'succ j))
            (have! (list 'IN (list 'MPOW rkm-rmm rkm-sign (list 'succ j)) '(CARR R))
              (lambda () (subst (list '= '(CARR R) (list 'CARR rkm-rmm))) (ass)))
            (dk-focus-having! (list 'IN (list 'MPOW rkm-rmm rkm-sign (list 'succ j)) '(CARR R)))
            (fact 'entry-in-carrier '(succ n) '(succ n) '(CARR R) a0 1 j)
            (fact 'minor-type 'R a0 1 j 'n)
            (dk-apply! ih (list 'MINOR a0 1 j 'n))       ; the IH at the minor
            (fact 'ring-carrier-closed-mul 'R (list 'ENTRY a0 1 j)
                  (list 'DET 'R 'n (list 'MINOR a0 1 j 'n)))
            (fact 'ring-carrier-closed-mul 'R (list 'MPOW rkm-rmm rkm-sign (list 'succ j))
                  (list '(MUL R) (list 'ENTRY a0 1 j)
                        (list 'DET 'R 'n (list 'MINOR a0 1 j 'n))))
            (ass)))))
    (dk-focus-having! (list 'IN lam (list 'FUN '(INTERVAL 1 (succ n)) '(CARR R))))
    (fact 'finsum-type-ring-additive-ag 'R '(INTERVAL 1 (succ n)) lam)
    (ass)))
(rkm-done! 'det-in-carrier-ind)
(topic! 'det-in-carrier-ind 'algebra)

;;; the support's own statement, binders and guards in ITS order
(sp (make-wff
  '(FORALL R (FORALL n (FORALL A
     (IMPLIES (IS-RING R)
     (IMPLIES (IN n NN)
     (IMPLIES (IN A (MAT n n (CARR R)))
       (IN (DET R n A) (CARR R))))))))))
(dk-peel!)
(fact 'det-in-carrier-ind 'R 'n 'A)
(ass)
(rkm-done! 'det-in-carrier)
(topic! 'det-in-carrier 'algebra)
