;;; rake-generates-coeff.scm -- generates-coeff-matrix, proven.
;;;
;;; STATEMENT (copied verbatim from the support at structure-library/mod-seq.scm:191):
;;;
;;;   md a module, u in MAT(n,1,VEC md), v in MAT(m,1,VEC md), n = 0 => m = 0,
;;;   GENERATES(md,n,u)  =>  some cm in MAT(m,n,CARR(SCAL md)) has v = cm . u.
;;;
;;; THE PLAN.  This is a CONSTRUCTION, not a read-off: GENERATES gives, for each
;;; row index i SEPARATELY, some coefficient row for the vector ENTRY(v,i,1),
;;; and the statement asks for one matrix.  Four stages.
;;;
;;;  (1) THE ROW FAMILY.  For i in [1,m] put
;;;        r(i) = CHOICE(SEP c_ in MAT(1,n,CARR(SCAL md)). ENTRY(v,i,1) = LINCOMB(md,n,c_,u)).
;;;      The SEP is inhabited: ENTRY(v,i,1) is a vector (entry-in-carrier) and
;;;      GENERATES, unfolded and instantiated there, hands over a member.
;;;      `choose!' (driver-kit) lands (IN (CHOICE S) S) against that witness and
;;;      splits the SEP membership, which is exactly the family fact
;;;        RGC-FAM:  forall i in [1,m].  r(i) in MAT(1,n,CARR(SCAL md))
;;;                                      and ENTRY(v,i,1) = LINCOMB(md,n,r(i),u).
;;;      The CHOICE never escapes: the conclusion is a FORSOME.
;;;
;;;  (2) THE MATRIX.  cm = MATOF(m, n, lam (i_,j_). ENTRY(r(i_), 1, j_)), typed by
;;;      matof-in-mat (through `dk-matof!') from entry-in-carrier on the row.
;;;
;;;  (3) BOTH SIDES ARE m-by-1.  v by hypothesis; MATACT(md,cm,u) by matact-type,
;;;      whose guard (n = 0 => m = 0 or 1 = 0) is the statement's own guard.
;;;
;;;  (4) THE ENTRIES AGREE, hence v = MATACT(md,cm,u) by matrix-entry-extensionality.
;;;      At (i,j) with j in [1,1] we have j = 1 (nn-le-antisym), and
;;;        ENTRY(v,i,1)            = LINCOMB(md,n,r(i),u)                 (RGC-FAM)
;;;                                = FINSUM(.. ACT(md)(ENTRY(r(i),1,j), ENTRY(u,j,1)) ..)
;;;                                                                      (mac LINCOMB)
;;;        ENTRY(MATACT(md,cm,u),i,1)
;;;                                = FINSUM(.. ACT(md)(ENTRY(cm,i,j), ENTRY(u,j,1)) ..)
;;;                                                                      (matact-entry)
;;;      and the two summands agree pointwise because ENTRY(cm,i,j) = ENTRY(r(i),1,j)
;;;      (entry-of-matof).  finsum-congruence-guarded closes it; the typed side is
;;;      the row's summand, typed by matact-summand-type at the shape (1,n,1).
;;;
;;; WHY 1 <= n IS AVAILABLE WHERE IT IS NEEDED.  matact-entry is guarded on
;;; 1 <= n (the 2026-09-16 SIZE/MAT surgery: at n = 0 it is false).  It is cited
;;; only under a row index i in [1,m], which gives 1 <= m, hence m /= 0, hence
;;; n /= 0 by the statement's guard, hence 1 <= n.  No case split on m is needed:
;;; matrix-entry-extensionality is unguarded, and at m = 0 its entry premise is
;;; vacuous.
;;;
;;; DEFINEDNESS (the LUTINS rule).  Neither a CHOICE term nor a MATOF/MATACT is
;;; certified defined, so every one of them is TYPED IN CONTEXT before any
;;; theorem is instantiated at it: RGC-FAM before entry-in-carrier on a row, the
;;; matof-in-mat typing before matact-type, the matact-type typing before
;;; matrix-entry-extensionality.
;;;
;;; The antecedent of a cited theorem that has to be PROVEN (rather than found in
;;; context) is read off the landed instantiation chain -- never rebuilt from the
;;; printed statement -- so a binder name in the library cannot silently break
;;; the detach.
;;;
;;; LOAD WINDOW [333, 404): lo is rake-identmat (332), which proves matact-entry;
;;; hi is rank-bound-proof (404), the one citer.  Everything else is far below:
;;; module 54 (module-act-type, the GENERATES/LINCOMB macetes at mod-seq 102),
;;; interval-basics 149 (interval-lo/-hi/-elt-in-nn/-in-set), nn-order-ord 165,
;;; nn-order-basics 167, mat-basics 168 (mat-rows-in-nn), interval-membership 170
;;; (one-in-interval-1), entry-in-carrier 172, nn-parity-proof 218 and
;;; nn-order-proof 231 (nn-nonzero-is-succ, nn-le-antisym), tuple-extensionality
;;; 247 (matrix-entry-extensionality), tuple-tabulation 248 (entry-of-matof),
;;; matof-in-mat 251, interval-card-in-nn 255, rake-finsum-laws 256
;;; (finsum-congruence-guarded), matunit-matact-type 265, lam-fun-bricks 331
;;; (matact-summand-type).  Tactics: only the early kit (dk-*, have!, choose!,
;;; in-sep!, prop through dk-have-prop!, arith through dk-nonzero!).
;;;
;;; RETIRES the support at structure-library/mod-seq.scm:191 (with its warrant!
;;; at :200).  The `topic!' for the name at theorem-library/mod-basis-proof.scm:327
;;; becomes redundant -- this file sets it.
;;; =====================================================================

;;; ---- file-local helpers (the `rgc-' prefix) --------------------------

(define RGC-SCAL '(CARR (SCAL md)))

;;; the coefficient rows that express the i-th entry of v
(define (rgc-sep i)
  (list 'SEP 'c_ (list 'MAT 1 'n RGC-SCAL)
        (list '= (list 'ENTRY 'v i 1) (list 'LINCOMB 'md 'n 'c_ 'u))))
(define (rgc-row i) (list 'CHOICE (rgc-sep i)))

;;; the tabulator and the matrix it builds
(define RGC-G (list 'VNB-LAMBDA '(LIST i_ j_)
                    '(CARTESIAN (INTERVAL 1 m) (INTERVAL 1 n))
                    (list 'ENTRY (rgc-row 'i_) 1 'j_)))
(define RGC-CM (list 'MATOF 'm 'n RGC-G))
(define RGC-MA (list 'MATACT 'md RGC-CM 'u))

(define (rgc-fam-body i)
  (list 'AND (list 'IN (rgc-row i) (list 'MAT 1 'n RGC-SCAL))
             (list '= (list 'ENTRY 'v i 1) (list 'LINCOMB 'md 'n (rgc-row i) 'u))))
(define RGC-FAM
  (list 'FORALL 'i_ (list 'IMPLIES '(IN i_ (INTERVAL 1 m)) (rgc-fam-body 'i_))))

(define RGC-CM-TYPE (list 'IN RGC-CM (list 'MAT 'm 'n RGC-SCAL)))

;;; The unfold of LINCOMB, with the coefficient row QUANTIFIED.  `mac LINCOMB'
;;; on the goal itself is NOT usable here: a macete rewrites EVERY occurrence,
;;; and the goal carries cm, whose tabulator contains a CHOICE over a SEP whose
;;; condition is itself a LINCOMB -- unfolding that one leaves the matrix term
;;; no longer syntactically equal to the cm of the other citations, and the
;;; entry-of-matof rewrite then finds nothing.  Instantiating this at the row
;;; substitutes only at the two ENTRY sites and leaves the SEP alone.
(define (rgc-lincomb-finsum c)
  (list 'FINSUM '(MODULE-VECTOR-AG md)
        (list 'VNB-LAMBDA 'j '(INTERVAL 1 n)
              (list '(ACT md) (list 'ENTRY c 1 'j) '(ENTRY u j 1)))
        '(INTERVAL 1 n)))
(define RGC-UNFOLD
  (list 'FORALL 'c_ (list '== (list 'LINCOMB 'md 'n 'c_ 'u)
                          (rgc-lincomb-finsum 'c_))))

;;; the ONE assumption of the focus leaf matching PRED
(define (rgc-find what pred)
  (let loop ((l (dk-asms)))
    (cond ((null? l) (error "rgc-find: no context formula" what))
          ((pred (car l)) (car l))
          (#t (loop (cdr l))))))

;;; the eigenvariable of a landed guard (IN x <cls>), by the class
(define (rgc-eigen landed cls)
  (let loop ((l landed))
    (cond ((null? l) (error "rgc-eigen: nothing landed in" cls))
          ((and (pair? (car l)) (eq? (caar l) 'IN) (equal? (caddr (car l)) cls))
           (cadr (car l)))
          (#t (loop (cdr l))))))

;;; land the sole undischarged antecedent of the instantiation chain CH by
;;; proving it with BODY, then detach.  The antecedent is read off CH.
(define (rgc-detach-with! ch body)
  (if (not (and (pair? ch) (eq? (car ch) 'IMPLIES)))
      (error "rgc-detach-with!: not an implication" (expression->string ch)))
  (let ((ante (cadr ch)))
    (have! ante body)
    (dk-focus-having! ante)
    (detach! ch)))

;;; =====================================================================

(sp (make-wff
  '(FORALL md (IMPLIES (IS-MODULE md)
     (FORALL n (FORALL m (FORALL u (FORALL v
       (IMPLIES (IN u (MAT n 1 (VEC md)))
       (IMPLIES (IN v (MAT m 1 (VEC md)))
       (IMPLIES (IMPLIES (= n 0) (= m 0))
       (IMPLIES (GENERATES md n u)
         (FORSOME cm (AND (IN cm (MAT m n (CARR (SCAL md))))
                          (= v (MATACT md cm u))))))))))))))))

(dk-peel!)

;;; the dimensions are naturals, read off the two matrices
(fact 'mat-rows-in-nn 'n 1 '(VEC md) 'u)
(fact 'mat-rows-in-nn 'm 1 '(VEC md) 'v)
(fact 'one-in-interval-1)                      ; 1 in [1,1] -- the column index

(have! RGC-UNFOLD (lambda () (di) (mac 'LINCOMB) (qrfl)))
(dk-focus-having! RGC-UNFOLD)

;;; ---- (1) the row family ----------------------------------------------
(have! RGC-FAM
  (lambda ()
    (let* ((ld (dk-peel!))
           (iv (rgc-eigen ld '(INTERVAL 1 m))))
      (fact 'entry-in-carrier 'm 1 '(VEC md) 'v iv 1)      ; ENTRY(v,iv,1) in VEC md
      (let* ((gen (dk-landed-1
                    (lambda () (mac-h 'GENERATES '(GENERATES md n u)))))
             (ex  (dk-deepest
                    (lambda () (inst+ gen (list 'ENTRY 'v iv 1)))))
             (w   (dk-skolem! ex)))
        (choose! (rgc-sep iv) w
                 (lambda () (in-sep! (lambda () (ass)) (lambda () (ass)))))
        (both! (lambda () (ass)) (lambda () (ass)))))))
(dk-focus-having! RGC-FAM)

;;; ---- (2) cm is an m-by-n matrix of scalars ---------------------------
(have! RGC-CM-TYPE
  (lambda ()
    (dk-matof!)                                  ; leaves the entry leaf in focus
    (let* ((ld (dk-peel!))
           (iv (rgc-eigen ld '(INTERVAL 1 m)))
           (jv (rgc-eigen ld '(INTERVAL 1 n))))
      (lam-b)                                    ; both indices are typed
      (dk-split! (dk-deepest (lambda () (inst+ RGC-FAM iv))))
      (fact 'entry-in-carrier 1 'n RGC-SCAL (rgc-row iv) 1 jv)
      (ass))))
(dk-focus-having! RGC-CM-TYPE)

;;; ---- (3) entry-of-matof's definedness premise, read off the chain ----
;;; The premise does not mention the indices, so any instantiation of them will
;;; do to read it; (1,1) is the cheapest.
(define RGC-EOM0 (dk-fact! 'entry-of-matof 'm 'n RGC-G 1 1))
(if (not (and (pair? RGC-EOM0) (eq? (car RGC-EOM0) 'IMPLIES)))
    (error "rgc: entry-of-matof's chain is not an implication"
           (expression->string RGC-EOM0)))
(define RGC-DEFSET (cadr RGC-EOM0))
(have! RGC-DEFSET
  (lambda ()
    (let* ((ld (dk-peel!))
           (iv (rgc-eigen ld '(INTERVAL 1 m)))
           (jv (rgc-eigen ld '(INTERVAL 1 n))))
      (lam-b)
      (dk-split! (dk-deepest (lambda () (inst+ RGC-FAM iv))))
      (fact 'entry-in-carrier 1 'n RGC-SCAL (rgc-row iv) 1 jv)
      (fact 'membership-implies-sethood (list 'ENTRY (rgc-row iv) 1 jv) RGC-SCAL)
      (ass))))
(dk-focus-having! RGC-DEFSET)

;;; ---- (4) the action is m-by-1, and its entries are v's ---------------
(dk-have-prop! '(IMPLIES (= n 0) (OR (= m 0) (= 1 0))))
(fact 'matact-type 'md 'm 'n 1 RGC-CM 'u)

(rgc-detach-with! (dk-fact! 'matrix-entry-extensionality 'm 1 '(VEC md) 'v RGC-MA)
  (lambda ()
    (let* ((ld (dk-peel!))
           (iv (rgc-eigen ld '(INTERVAL 1 m)))
           (jv (rgc-eigen ld '(INTERVAL 1 1))))
      ;; the column index of a column vector is 1
      (fact 'interval-elt-in-nn 1 1 jv)
      (fact 'interval-hi 1 1 jv)
      (fact 'interval-lo 1 1 jv)
      (fact 'nn-one-in)
      (fact 'nn-le-antisym jv 1)
      (subst (list '= jv 1))
      ;; 1 <= n, matact-entry's guard: 1 <= m off the row index, then the
      ;; statement's own guard read backwards.
      (dk-one-le-from! iv 'm)
      (dk-nonzero! 'm)
      (dk-have-prop! '(NOT (= n 0)))
      (dk-one-le! 'n)
      ;; the two readings of the (iv,1) entry
      (let* ((mae (dk-fact! 'matact-entry 'md 'm 'n 1 RGC-CM 'u iv 1))
             (fam (dk-deepest (lambda () (inst+ RGC-FAM iv)))))
        (dk-split! fam)
        (subst (list '= (list 'ENTRY 'v iv 1)
                     (list 'LINCOMB 'md 'n (rgc-row iv) 'u)))
        (subst mae)
        (subst (dk-deepest (lambda () (inst+ RGC-UNFOLD (rgc-row iv)))))
        ;; FINSUM(ag,f,S) = FINSUM(ag,g,S): read both lambdas off the goal
        (let* ((g    (dk-goal))
               (lhs  (cadr g))
               (rhs  (caddr g))
               (fl   (caddr lhs))
               (gl   (caddr rhs)))
          (if (not (and (pair? lhs) (eq? (car lhs) 'FINSUM)
                        (pair? rhs) (eq? (car rhs) 'FINSUM)))
              (error "rgc: the entry goal is not an equation of FINSUMs"
                     (expression->string g)))
          (fact 'module-vector-ag-is-abelian-group 'md)
          (fact 'interval-in-set 1 'n)
          (fact 'interval-card-in-nn 1 'n)
          (fact 'matact-summand-type 'md 1 'n 1 (rgc-row iv) 'u 1 1)
          (rgc-detach-with!
            (dk-fact! 'finsum-congruence-guarded '(MODULE-VECTOR-AG md)
                      '(INTERVAL 1 n) fl gl)
            (lambda ()
              (let* ((ld2 (dk-peel!))
                     (zv  (rgc-eigen ld2 '(INTERVAL 1 n))))
                (fact 'entry-in-carrier 1 'n RGC-SCAL (rgc-row iv) 1 zv)
                (fact 'entry-in-carrier 'n 1 '(VEC md) 'u zv 1)
                ;; `rfl' is strict: the common value of the two sides must be
                ;; CERTIFIED defined, and an action applied to typed arguments
                ;; is certified only once the product itself is typed.
                (fact 'module-act-type 'md (list 'ENTRY (rgc-row iv) 1 zv)
                                           (list 'ENTRY 'u zv 1))
                (lam-b)
                (let ((eo (dk-fact! 'entry-of-matof 'm 'n RGC-G iv zv)))
                  (lam-b-h eo)
                  (subst (rgc-find 'entry-of-matof
                           (lambda (f) (and (pair? f) (eq? (car f) '=)
                                            (equal? (cadr f)
                                                    (list 'ENTRY RGC-CM iv zv))))))
                  (rfl)))))
          (ass))))))

;;; ---- the witness ------------------------------------------------------
(ew RGC-CM)
(both! (lambda () (ass)) (lambda () (ass)))

(qed 'generates-coeff-matrix)
(topic! 'generates-coeff-matrix 'algebra)
