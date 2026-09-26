;;; finsum-single-support.scm -- a finite sum whose summand vanishes off a
;;; single index equals its value there.  Both theorems `modulo 0'.
;;;
;;;     sum-ag-single-ind   (NEW)  the induction form, over a fold length
;;;     finsum-single-support      formerly a `well-known' support
;;;                                (structure-library/matrix.scm:398-407)
;;;
;;; STATEMENT (copied literally from the support's definition site):
;;;
;;;   ag an abelian group, S a finite set, f in FUN(S, CARR ag), i0 in S, and
;;;   f(j) = IDEN(ag) for every j in S with j /= i0
;;;     =>  FINSUM(ag, f, S) = f(i0).
;;;
;;; THE ROUTE, AND WHY IT IS NOT THE OBVIOUS ONE.  The obvious route writes
;;; S = X u {i0} with X = S \ {i0} and peels i0 with finsum-insert-ag.  It does
;;; not close: finsum-all-id at X wants f in FUN(X, CARR ag), and f -- a set of
;;; pairs with domain exactly S -- is not that.  The tree has no restriction
;;; machinery, and CARD(S \ {i0}) in NN would additionally need a converse of
;;; card-insert (succ_ORD(CARD X) in NN => CARD X in NN), which it also lacks.
;;;
;;; So the proof goes the way theorem-library/finsum-type-proof.scm goes for
;;; finsum-all-id: FINSUM is DEFINED as a SUM-AG along the chosen enumeration,
;;; and the induction that is available -- `ni' on the fold LENGTH -- does the
;;; whole job.  sum-ag-single-ind is that induction; the FINSUM statement is then
;;; a transfer along FIN-ENUM(S), whose injectivity turns "j /= i0" into
;;; "index /= p" and whose surjectivity produces the index p with
;;; FIN-ENUM(S)(p) = i0.
;;;
;;; sum-ag-single-ind's step is a case split on whether the index p lies below n:
;;;   p in ORD-SEGMENT(n): the top summand g(n) vanishes (n /= p, since p is in
;;;     the segment and n is not -- ord-segment-self), the rest is the IH, and
;;;     g(p) * IDEN = g(p) by abelian-group-opr-comm + group-left-id.
;;;   otherwise: ord-segment-nn-succ forces p = n, everything below vanishes
;;;     (sum-ag-all-id-ind), and IDEN * g(n) = g(n) by group-left-id.
;;; The hypothesis (IN (g_ p_) (CARR ag)) is what group-left-id needs; at the
;;; FINSUM level it comes from fun-apply-type-c on f at i0.
;;;
;;; LOAD WINDOW, by FILE NAME:
;;;   lo -- AFTER theorem-library/finsum-type-proof (position 198), which proves
;;;         sum-ag-all-id-ind.  That is the latest citation; everything else
;;;         (finsum-insert 154, ord-segment-nn-subset-proof 153, subtype-laws 196,
;;;         fun-apply-type-proof 162, equality-basics 148) loads earlier.
;;;   hi -- BEFORE theorem-library/finsum-fiber (position 286), the earliest
;;;         citer of finsum-single-support.
;;;   i.e. [199, 286).  No view companion of finsum-single-support is cited
;;;   anywhere, so the view-specializer constraint that binds finsum-type-proof
;;;   (hi < cancellation) does not apply here.
;;;
;;; Helper prefix: fss-.

;;; ---------------------------------------------------------------------------
;;; helpers

(define (fss-check! name)
  (if (not (proof-done? *ps*))
      (begin
        (display ";; fss: OPEN LEAVES before qed ") (display name) (newline)
        (for-each (lambda (l)
                    (display ";;   ") (display (expression->string (dk-goal-of l))) (newline))
                  (proof-leaves))
        (error "fss: proof not complete" name))))

;; Among LEAVES (as dk-opened returns them), the unique one whose GOAL satisfies PRED.
(define (fss-leaf leaves pred what)
  (let ((hits (filter (lambda (l) (pred (dk-goal-of l))) leaves)))
    (cond ((null? hits) (error "fss-leaf: no leaf for" what))
          ((pair? (cdr hits)) (error "fss-leaf: ambiguous leaf for" what))
          (#t (car hits)))))

;; the NN-typed eigenvariable in context: (IN v NN) with v a symbol.
(define (fss-nn-var)
  (cadr (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'IN) (symbol? (cadr f))
                                  (eq? (caddr f) 'NN)))
                 "n in NN")))

;; the agreement hypothesis: a FORALL whose antecedent is an ORD-SEGMENT
;; membership.  Discriminated on the ANTECEDENT, never on the head: the IH is a
;; FORALL too (CLAUDE.md, "never name an ASSUMPTION by shape").
;; (fss-guarded-forall? F DOM HEAD) -- F is (FORALL v (IMPLIES (IN v DOM) BODY))
;; with BODY's head HEAD.  EVERY accessor is length-guarded: the predicate runs
;; over the WHOLE context, where a two-element antecedent like (IS-GROUP ag)
;; makes a bare `caddr' die with "() passed to safe-car".
(define (fss-guarded-forall? f dom head)
  (and (pair? f) (eq? (car f) 'FORALL) (= (length f) 3)
       (let ((b (caddr f)))
         (and (pair? b) (eq? (car b) 'IMPLIES) (= (length b) 3)
              (let ((a (cadr b)) (inner (caddr b)))
                (and (pair? a) (eq? (car a) 'IN) (= (length a) 3)
                     (if (procedure? dom) (dom (caddr a)) (equal? (caddr a) dom))
                     (pair? inner) (eq? (car inner) head)))))))

;; the agreement hypothesis of sum-ag-single-ind: the guarded FORALL whose
;; domain is an ORD-SEGMENT.  Discriminated on the ANTECEDENT, never on the
;; head: the IH is a FORALL too (CLAUDE.md).
(define (fss-agreement? f)
  (fss-guarded-forall? f
                       (lambda (d) (and (pair? d) (eq? (car d) 'ORD-SEGMENT)))
                       'IMPLIES))

;; the eigenvariable of the ORD-SEGMENT typing among LANDED (what dk-peel! returned).
(define (fss-seg-var landed)
  (let ((f (any-pred (lambda (f) (and (pair? f) (eq? (car f) 'IN) (symbol? (cadr f))
                                      (pair? (caddr f)) (eq? (car (caddr f)) 'ORD-SEGMENT)))
                     landed)))
    (if f (cadr f)
        (error "fss-seg-var: no ORD-SEGMENT typing landed"
               (map expression->string landed)))))

;;; ---------------------------------------------------------------------------
;;; sum-ag-single-ind -- the induction form, the fold length OUTERMOST.
;;;
;;;   n in NN => forall ag. IS-ABELIAN-GROUP ag => forall g_, p_.
;;;     p_ in ORD-SEGMENT(n) => g_(p_) in CARR(ag) =>
;;;     (forall i_ in ORD-SEGMENT n. i_ /= p_ => g_(i_) = IDEN ag)
;;;     => SUM-AG(ag, g_, n) = g_(p_)
;;;
;;; n OUTERMOST because `ni' tests the goal's SHAPE (CLAUDE.md), and `di' is
;;; greedy, so there is no peeling down to an inner n-universal.

(define fss-ind-stmt
  '(FORALL n (IMPLIES (IN n NN)
     (FORALL ag (IMPLIES (IS-ABELIAN-GROUP ag)
     (FORALL g_ (FORALL p_ (IMPLIES (IN p_ (ORD-SEGMENT n))
       (IMPLIES (IN (g_ p_) (CARR ag))
         (IMPLIES (FORALL i_ (IMPLIES (IN i_ (ORD-SEGMENT n))
                     (IMPLIES (NOT (= i_ p_)) (= (g_ i_) (IDEN ag)))))
           (= (SUM-AG ag g_ n) (g_ p_))))))))))))

(sp (make-wff fss-ind-stmt))
(let* ((leaves (dk-opened (lambda () (ni))))
       (base (fss-leaf leaves (lambda (g) (not (dk-contains? g 'succ))) "induction base"))
       (step (fss-leaf leaves (lambda (g) (dk-contains? g 'succ))       "induction step")))
  ;; ---- base: ORD-SEGMENT(0) is empty, so the index hypothesis is absurd ----
  (dk-focus! base)
  (dk-peel!)
  (let ((pv (cadr (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                            (equal? (caddr f) '(ORD-SEGMENT 0))))
                           "p_ in ORD-SEGMENT(0)"))))
    (fact 'ord-segment-zero-no-members pv)
    (ai (list 'NOT (list 'IN pv '(ORD-SEGMENT 0)))))
  ;; ---- step ---------------------------------------------------------------
  (dk-focus! step)
  (dk-peel!)
  (let* ((nv    (fss-nn-var))
         (gl    (dk-goal))                    ; (= (SUM-AG ag g_ (succ n)) (g_ p_))
         (agv   (cadr (cadr gl)))
         (gv    (caddr (cadr gl)))
         (pv    (cadr (caddr gl)))
         (agree (dk-pick fss-agreement? "the agreement hypothesis on OS(succ n)"))
         (ih    (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                          (not (fss-agreement? f))))
                         "the IH")))
    (mac 'sum-ag-succ)                        ; (= ((OPR ag) (SUM-AG ag g_ n) (g_ n)) (g_ p_))
    (dk-fact! 'abelian-group-is-group agv)
    (dk-fact! 'group-identity-in agv)
    (use-em (list 'IN pv (list 'ORD-SEGMENT nv))
      ;; ---- p_ below n: the top summand vanishes, the rest is the IH -------
      (lambda ()
        ;; n /= p_: p_ is in ORD-SEGMENT(n) and n is not (ord-segment-self)
        (have! (list 'NOT (list '= nv pv))
               (lambda ()
                 (di)                                      ; assume (= n p_)
                 (have! (list 'AND (list '= nv pv) (list 'IN pv (list 'ORD-SEGMENT nv))))
                 (dk-fact! 'eq-subst-membership nv pv (list 'ORD-SEGMENT nv))
                 (ai (dk-fact! 'ord-segment-self nv))))
        (have! (list 'IN nv (list 'ORD-SEGMENT (list 'succ nv)))
               (lambda () (mac 'ord-segment-nn-succ) (oi-r) (rfl)))
        (dk-apply! agree nv)                                ; (= (g_ n) (IDEN ag))
        (subst (list '= (list gv nv) (list 'IDEN agv)))
        ;; the rest: the IH at p_, whose agreement is this one cut down to OS(n)
        (have! (list 'FORALL 'i_
                 (list 'IMPLIES (list 'IN 'i_ (list 'ORD-SEGMENT nv))
                   (list 'IMPLIES (list 'NOT (list '= 'i_ pv))
                     (list '= (list gv 'i_) (list 'IDEN agv)))))
               (lambda ()
                 (let* ((landed (dk-peel!))
                        (iv     (fss-seg-var landed)))
                   (have! (list 'IN iv (list 'ORD-SEGMENT (list 'succ nv)))
                          (lambda () (mac 'ord-segment-nn-succ) (oi-l) (ass)))
                   (dk-apply! agree iv)
                   (ass))))
        (dk-apply! ih agv gv pv)                            ; (= (SUM-AG ag g_ n) (g_ p_))
        (subst (list '= (list 'SUM-AG agv gv nv) (list gv pv)))
        ;; g_(p_) * IDEN = IDEN * g_(p_) = g_(p_)
        (dk-fact! 'abelian-group-opr-comm agv (list gv pv) (list 'IDEN agv))
        (subst (list '= (list (list 'OPR agv) (list gv pv) (list 'IDEN agv))
                        (list (list 'OPR agv) (list 'IDEN agv) (list gv pv))))
        (dk-fact! 'group-left-id agv (list gv pv))
        (ass))
      ;; ---- p_ = n: everything below vanishes ------------------------------
      (lambda ()
        (have! (list '= pv nv)
               (lambda ()
                 ;; `prop' counts every quantified formula as an opaque atom and
                 ;; has an atom cap, so the context is trimmed to the three
                 ;; formulas the step actually uses (CLAUDE.md / dk-only!).
                 (let ((iffp (dk-fact! 'ord-segment-nn-succ nv pv)))
                   (dk-only! iffp
                             (list 'IN pv (list 'ORD-SEGMENT (list 'succ nv)))
                             (list 'NOT (list 'IN pv (list 'ORD-SEGMENT nv))))
                   (prop))))
        (have! (list 'FORALL 'i_
                 (list 'IMPLIES (list 'IN 'i_ (list 'ORD-SEGMENT nv))
                   (list '= (list gv 'i_) (list 'IDEN agv))))
               (lambda ()
                 (let* ((landed (dk-peel!))
                        (iv     (fss-seg-var landed)))
                   (have! (list 'IN iv (list 'ORD-SEGMENT (list 'succ nv)))
                          (lambda () (mac 'ord-segment-nn-succ) (oi-l) (ass)))
                   (have! (list 'NOT (list '= iv pv))
                          (lambda ()
                            (di)                            ; assume (= i_ p_)
                            (dk-fact! 'eq-trans iv pv nv)   ; (= i_ n)
                            (dk-fact! 'equality-symmetry iv nv)  ; (= n i_)
                            (have! (list 'AND (list '= nv iv)
                                        (list 'IN iv (list 'ORD-SEGMENT nv))))
                            (dk-fact! 'eq-subst-membership nv iv (list 'ORD-SEGMENT nv))
                            (ai (dk-fact! 'ord-segment-self nv))))
                   (dk-apply! agree iv)
                   (ass))))
        (dk-fact! 'sum-ag-all-id-ind nv agv gv)             ; (= (SUM-AG ag g_ n) (IDEN ag))
        (subst (list '= (list 'SUM-AG agv gv nv) (list 'IDEN agv)))
        (subst (list '= pv nv))                             ; p_ := n in the goal
        (have! (list 'IN (list gv nv) (list 'CARR agv))
               (lambda ()
                 (dk-fact! 'equality-symmetry pv nv)        ; (= n p_)
                 (subst (list '= nv pv))
                 (ass)))
        (dk-fact! 'group-left-id agv (list gv nv))
        (ass)))))
(fss-check! 'sum-ag-single-ind)
(qed 'sum-ag-single-ind)
(topic! 'sum-ag-single-ind 'algebra)

;;; ---------------------------------------------------------------------------
;;; finsum-single-support -- the statement as structure-library/matrix.scm
;;; spells it, copied literally.
;;;
;;; FINSUM(ag,f,S) is SUM-AG over ENUM-FAM of the chosen enumeration phi =
;;; FIN-ENUM(S).  Surjectivity gives the index p with phi(p) = i0; injectivity
;;; turns "i_ /= p" into "phi(i_) /= i0", where the hypothesis applies.  The
;;; ENUM-FAM beta needs its argument TYPED FIRST (CLAUDE.md), which is what the
;;; ord-segment-nn-subset citations are for: an index in the segment is in NN,
;;; the lambda's own domain.

(define fss-stmt
  '(FORALL ag (IMPLIES (IS-ABELIAN-GROUP ag)
     (FORALL S (IMPLIES (IN S SET) (IMPLIES (IN (CARD S) NN)
     (FORALL f (IMPLIES (IN f (FUN S (CARR ag)))
     (FORALL i0 (IMPLIES (IN i0 S)
       (IMPLIES (FORALL j (IMPLIES (IN j S)
                  (IMPLIES (NOT (= j i0)) (= (f j) (IDEN ag)))))
         (= (FINSUM ag f S) (f i0)))))))))))))

(sp (make-wff fss-stmt))
(dk-peel!)
(let* ((agv (cadr (dk-pick (dk-head? 'IS-ABELIAN-GROUP) "IS-ABELIAN-GROUP ag")))
       (sv  (cadr (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'IN) (eq? (caddr f) 'SET)))
                           "S in SET")))
       (fv  (cadr (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                            (pair? (caddr f)) (eq? (car (caddr f)) 'FUN)
                                            (equal? (cadr (caddr f)) sv)))
                           "f in FUN(S, CARR ag)")))
       (i0v (cadr (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'IN) (symbol? (cadr f))
                                            (eq? (caddr f) sv)))
                           "i0 in S")))
       (agree (dk-pick (lambda (f) (fss-guarded-forall? f sv 'IMPLIES))
                       "forall j in S. j /= i0 => f j = IDEN ag"))
       (phi (list 'FIN-ENUM sv))
       (seg (list 'ORD-SEGMENT (list 'CARD sv)))
       (fam (list 'ENUM-FAM agv fv phi (list 'CARD sv))))
  (mac 'FINSUM)                          ; (= (SUM-AG ag FAM (CARD S)) (f i0))
  (dk-fact! 'abelian-group-is-group agv)
  (dk-fact! 'group-identity-in agv)
  (dk-fact! 'fun-apply-type-c fv sv (list 'CARR agv) i0v)     ; (IN (f i0) (CARR ag))
  ;; the enumeration, opened
  (let ((bij (dk-fact! 'fin-enum-is-bijection sv)))
    (mac-h 'bijection-membership-iff bij)
    (dk-split-all!))
  (let* ((inj  (dk-pick (lambda (f) (fss-guarded-forall? f seg 'FORALL))
                        "injectivity of FIN-ENUM(S)"))
         (surj (dk-pick (lambda (f) (fss-guarded-forall? f sv 'FORSOME))
                        "surjectivity of FIN-ENUM(S)"))
         (ex   (dk-apply! surj i0v))                          ; (FORSOME z (AND ...))
         (pv   (dk-skolem! ex)))                              ; phi(p) = i0, p in seg
    (dk-fact! 'ord-segment-nn-subset (list 'CARD sv) pv)       ; (IN p NN): type before the beta
    ;; 1.  the family at p IS f(i0)
    (have! (list '= (list fam pv) (list fv i0v))
           (lambda ()
             (let ((ift (list 'IF (list 'IN pv seg) (list fv (list phi pv))
                              (list 'IDEN agv))))
               (mac 'ENUM-FAM)
               (lam-b)
               (let* ((ls (dk-opened (lambda () (if-true ift))))
                      (cnd (fss-leaf ls (lambda (g) (and (pair? g) (eq? (car g) 'IN)))
                                     "if-true condition"))
                      (mn  (fss-leaf ls (lambda (g) (and (pair? g) (eq? (car g) '=)))
                                     "if-true main")))
                 (dk-focus! cnd) (ass)
                 (dk-focus! mn)
                 ;; if-true leaves the goal alone and hands the equation
                 ;; (= IF(...) then) as an ASSUMPTION; rewrite with it.
                 (subst (list '= ift (list fv (list phi pv))))
                 (subst (list '= (list phi pv) i0v))
                 (rfl)))))
    ;; 2.  its typing, which is what group-left-id needs inside the induction
    (have! (list 'IN (list fam pv) (list 'CARR agv))
           (lambda () (subst (list '= (list fam pv) (list fv i0v))) (ass)))
    ;; 3.  the family vanishes off p
    (have! (list 'FORALL 'i_
             (list 'IMPLIES (list 'IN 'i_ seg)
               (list 'IMPLIES (list 'NOT (list '= 'i_ pv))
                 (list '= (list fam 'i_) (list 'IDEN agv)))))
           (lambda ()
             (let* ((landed (dk-peel!))
                    (iv     (fss-seg-var landed)))
               (dk-fact! 'ord-segment-nn-subset (list 'CARD sv) iv)
               (dk-fact! 'fun-apply-type-c phi seg sv iv)        ; (IN (phi i_) S)
               ;; phi(i_) /= i0, by injectivity
               (have! (list 'NOT (list '= (list phi iv) i0v))
                      (lambda ()
                        (di)                                     ; assume (= (phi i_) i0)
                        (dk-fact! 'equality-symmetry (list phi pv) i0v)   ; (= i0 (phi p))
                        (dk-fact! 'eq-trans (list phi iv) i0v (list phi pv))
                        (dk-apply! inj iv pv)                    ; (= i_ p)
                        (ai (list 'NOT (list '= iv pv)))))
               (dk-apply! agree (list phi iv))                   ; (= (f (phi i_)) (IDEN ag))
               (let ((ift (list 'IF (list 'IN iv seg) (list fv (list phi iv))
                                (list 'IDEN agv))))
                 (mac 'ENUM-FAM)
                 (lam-b)
                 (let* ((ls (dk-opened (lambda () (if-true ift))))
                        (cnd (fss-leaf ls (lambda (g) (and (pair? g) (eq? (car g) 'IN)))
                                       "if-true condition"))
                        (mn  (fss-leaf ls (lambda (g) (and (pair? g) (eq? (car g) '=)))
                                       "if-true main")))
                   (dk-focus! cnd) (ass)
                   (dk-focus! mn)
                   (subst (list '= ift (list fv (list phi iv))))
                   (ass))))))
    ;; 4.  the induction
    (dk-fact! 'sum-ag-single-ind (list 'CARD sv) agv fam pv)
    (subst (list '= (list 'SUM-AG agv fam (list 'CARD sv)) (list fam pv)))
    (ass)))
(fss-check! 'finsum-single-support)
(qed 'finsum-single-support)
(topic! 'finsum-single-support 'algebra)
