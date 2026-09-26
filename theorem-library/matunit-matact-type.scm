;;; matunit-matact-type.scm -- two MATOF typings, PROVEN from the definitions.
;;;
;;;   matunit-type   forall A. IS-RING(A) => forall n k l. n in NN =>
;;;                    MATUNIT(A,n,k,l) in MAT(n,n,CARR A)
;;;   matact-type    forall md. IS-MODULE(md) => forall m n q P u.
;;;                    P in MAT(m,n,CARR(SCAL md)) => u in MAT(n,q,VEC md)
;;;                      => (n = 0 => m = 0 or q = 0)
;;;                      => MATACT(md,P,u) in MAT(m,q,VEC md)
;;;
;;; GUARDED 2026-09-16 (the SIZE/MAT change): matunit-type on `n in NN',
;;; matact-type on `n = 0 implies (m = 0 or q = 0)'; see each block.
;;;
;;; This is the pattern of theorem-library/mat-typing-bundle.scm, one file on:
;;; both constructors are a MATOF, so both are `matof-in-mat' (PROVEN) applied to
;;; the tabulator -- unfold, `bc*' matof-in-mat, peel the two index binders,
;;; `lam-b' the pair-lambda (licensed componentwise by the two interval typings
;;; the peel landed), and type what is left.
;;;
;;;   * MATUNIT: identmat-type's driver exactly, with an AND condition.  The IF
;;;     tower is over (AND (= i k) (= j l)); `use-em' on the condition, if-true /
;;;     if-false to resolve the IF into an equation, `subst' it, and the value is
;;;     ONE(A) (ring-one-in, PROVEN) or ZERO(A) (ring-zero-in, definitional).
;;;     mmt-close-if! recurses, so the AND needs no separate driver -- the case
;;;     split is on the whole condition, which `ass' then closes on both branches.
;;;   * MATACT: matmul-type's driver, with the module's vector abelian group in
;;;     place of RING-ADDITIVE-AG.  The tabulator's dimensions are NTH(1,SIZE P),
;;;     NTH(2,SIZE u), NTH(2,SIZE P); SIZE(P) = [m,n] and SIZE(u) = [n,q] come out
;;;     of the MAT hypotheses by mat-basics' chain (mat-unfold, a `have!' across
;;;     the unfolding equation, sep-me), two `subst's put the literal pairs in and
;;;     ONE `nth-r' reduces every NTH-on-a-literal-pair at once.  The entry is then
;;;     a FINSUM over [1,n] in MODULE-VECTOR-AG(md), and `dk-typ-close!'
;;;     (driver-kit) owns the rest of it: its FINSUM branch cites
;;;     module-vector-ag-is-abelian-group, interval-in-set, mat-rows-in-nn (on u,
;;;     whose ROW count n is the guard interval-card-in-nn wants) and finsum-type,
;;;     types the summand by a recursive dk-lam-fun! (entry-in-carrier twice, then
;;;     module-act-type), and bridges CARR(MODULE-VECTOR-AG md) to VEC(md) by
;;;     mvag-carr.  No matact-summand-type is needed.
;;;
;;; BILL.  matact-type cites finsum-type and mvag-carr, which are ASSERTED at the
;;; time of writing (both are under proof elsewhere in this wave), so its bill is
;;; expected to read `modulo {finsum-type, mvag-carr, ...}' until those land.
;;; matunit-type cites only PROVEN / `definitional' facts.
;;;
;;; LOAD WINDOW [lo, hi):
;;;   lo -- after theorem-library/interval-card-in-nn (the LATEST citation; the
;;;         others -- matof-in-mat, mat-basics (mat-unfold, mat-rows-in-nn),
;;;         entry-in-carrier, ring-zero-one-power (ring-one-in), interval-basics,
;;;         module (module-act-type), views (module-vector-ag-is-abelian-group),
;;;         mod-seq (MATACT, mvag-carr), finsum-type -- all load earlier).
;;;   hi -- before theorem-library/matunit-shift-proof, the earliest citer of
;;;         matunit-type (lastcoeff-ideal-proof, the earliest citer of
;;;         matact-type, comes after it).
;;;   Suggested slot: immediately after theorem-library/mat-typing-bundle.
;;;
;;; Helper prefix: mmt-.

;;; ---- helpers ----------------------------------------------------------
;;; mmt-close-if! / mmt-if-branch! are mat-typing-bundle.scm's mtb- pair
;;; verbatim, and mmt-size! is its mtb-size! with the matrix name a parameter.
;;; TWO files need them now, so by CLAUDE.md's own rule they belong in
;;; driver-kit.scm -- or this block belongs spliced into mat-typing-bundle.scm
;;; as its fourth and fifth entries.  Flagged, not decided here.

;; Resolve an IF tower in a goal (IN (IF c a b) X): case on c, reduce the IF to
;; an equation on each side, substitute, recurse; a goal that is not an IF is
;; closed from the context.  The ONE/ZERO typings must already be in context.
(define (mmt-close-if!)
  (let ((g (dk-goal)))
    (if (and (pair? g) (eq? (car g) 'IN)
             (pair? (cadr g)) (eq? (car (cadr g)) 'IF))
        (let* ((ifterm (cadr g))
               (c      (cadr ifterm)))
          (use-em c
            (lambda () (mmt-if-branch! #t ifterm))
            (lambda () (mmt-if-branch! #f ifterm))))
        (ass))))

;; if-true / if-false open two leaves: the CONDITION (or its negation), which
;; the case split put in context, and the MAIN goal with (= (IF c a b) val)
;; added.  Discriminate them on the goal, never on where focus landed.
(define (mmt-if-branch! true? ifterm)
  (let* ((c      (cadr ifterm))
         (val    (if true? (caddr ifterm) (cadddr ifterm)))
         (want   (if true? c (list 'NOT c)))
         (opened (dk-opened (lambda () (if true? (if-true ifterm) (if-false ifterm)))))
         (conds  (filter (lambda (l) (alpha-equiv? (dk-goal-of l) want)) opened))
         (mains  (filter (lambda (l) (not (memq l conds))) opened)))
    (if (not (and (= 1 (length conds)) (= 1 (length mains))))
        (error "mmt-if-branch!: expected one condition leaf and one main leaf, got"
               (map (lambda (l) (expression->string (dk-goal-of l))) opened)))
    (dk-focus! (car conds)) (ass)
    (dk-focus! (car mains))
    (subst (list '= ifterm val))
    (mmt-close-if!)))

;; The standard finish: report open goals loudly rather than qed a half-proof.
(define (mmt-qed! name)
  (if (proof-done? *ps*)
      (qed name)
      (begin
        (display "\n*** matunit-matact-type: ") (display name)
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
        (error "matunit-matact-type: unfinished" name))))

;;; ---- matunit-type -----------------------------------------------------

(sp (make-wff '(FORALL A (IMPLIES (IS-RING A) (FORALL n (FORALL k (FORALL l
     (IMPLIES (IN n NN)
       (IN (MATUNIT A n k l) (MAT n n (CARR A)))))))))))
(dk-peel!)                                     ; IS-RING A, then n, k, l, n in NN
(mac 'MATUNIT)
(dk-matof!)
(dk-peel!)                                     ; i in [1,n], j in [1,n]
(lam-b)                     ; (IN (IF (AND (= i k) (= j l)) (ONE A) (ZERO A)) (CARR A))
(fact 'ring-one-in 'A)
(fact 'ring-zero-in 'A)
(mmt-close-if!)
(mmt-qed! 'matunit-type)
(topic! 'matunit-type 'algebra)

;;; ---- matact-type ------------------------------------------------------
;;;
;;; GUARDED 2026-09-16 on `n = 0 implies (m = 0 or q = 0)', for matmul-type's
;;; reason (mat-typing-bundle.scm): MATACT reads its column count off SIZE(u),
;;; and a u with no rows is [] with SIZE [0, 0].  The driver is matmul-type's,
;;; with dk-typ-close! typing the FINSUM in the module's vector group.

(sp (make-wff '(FORALL md (IMPLIES (IS-MODULE md)
     (FORALL m (FORALL n (FORALL q (FORALL P (FORALL u
       (IMPLIES (IN P (MAT m n (CARR (SCAL md))))
       (IMPLIES (IN u (MAT n q (VEC md)))
       (IMPLIES (IMPLIES (= n 0) (OR (= m 0) (= q 0)))
         (IN (MATACT md P u) (MAT m q (VEC md)))))))))))))))
(dk-peel!)                                     ; IS-MODULE md, P, u, the guard
(mac 'MATACT)
(fact 'mat-rows-in-nn 'm 'n '(CARR (SCAL md)) 'P)
(fact 'mat-size-rows 'm 'n '(CARR (SCAL md)) 'P)
(subst '(= (NTH 1 (SIZE P)) m))
(fact 'mat-size-cols-in-nn 'n 'q '(VEC md) 'u)
(define mmt-prod (cadr (dk-goal)))
(have! (list 'IN mmt-prod '(MAT m (NTH 2 (SIZE u)) (VEC md)))
  (lambda ()
    (dk-matof!)
    (dk-peel!)                                 ; i in [1,m], c in [1, NTH(2, SIZE u)]
    (let* ((ivl (lambda (hi) (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                                        (equal? (caddr f) (list 'INTERVAL 1 hi))))
                                      "an index")))
           (i0  (cadr (ivl 'm)))
           (c0  (cadr (ivl '(NTH 2 (SIZE u))))))
      ;; the sum runs over [1, NTH(2, SIZE P)], inside the pair-lambda, which is
      ;; in operator position of the goal, where `subst' does not rewrite;
      ;; restate the matrices at that dimension (matmul-type does the same) so
      ;; dk-typ-close! finds them.
      (dk-one-le-from! i0 'm)
      (fact 'mat-size-cols 'm 'n '(CARR (SCAL md)) 'P)
      (let ((hi '(NTH 2 (SIZE P))))
        (have! (list 'IN 'P (list 'MAT 'm hi '(CARR (SCAL md))))
          (lambda () (subst (list '= hi 'n)) (ass)))
        (dk-focus-having! (list 'IN 'P (list 'MAT 'm hi '(CARR (SCAL md)))))
        (have! (list 'IN 'u (list 'MAT hi 'q '(VEC md)))
          (lambda () (subst (list '= hi 'n)) (ass)))
        (dk-focus-having! (list 'IN 'u (list 'MAT hi 'q '(VEC md)))))
      (dk-one-le-from! c0 '(NTH 2 (SIZE u)))
      (fact 'mat-size-cols-pos 'n 'q '(VEC md) 'u)
      (have! (list 'IN c0 '(INTERVAL 1 q))
        (lambda () (subst '(= q (NTH 2 (SIZE u)))) (ass)))
      (lam-b)                 ; (IN (FINSUM (MODULE-VECTOR-AG md) LAM [1,n]) (VEC md))
      (dk-typ-close!))))
(dk-focus-having! (list 'IN mmt-prod '(MAT m (NTH 2 (SIZE u)) (VEC md))))
(fact 'mat-colcount-transfer 'n 'q '(VEC md) 'u 'm '(VEC md) mmt-prod)
(ass)
(mmt-qed! 'matact-type)
(topic! 'matact-type 'algebra)
