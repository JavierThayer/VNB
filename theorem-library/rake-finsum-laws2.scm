;;; theorem-library/rake-finsum-laws2.scm -- rake batch J, part 2: the three
;;; DISTRIBUTION laws of FINSUM (a ring element on either side, a module scalar)
;;; and the interval back-peel.  Part 1 is theorem-library/rake-finsum-laws.scm,
;;; which must load FIRST: this file cites its `enum-fam-value' and
;;; `sum-ag-type-ptwise'.  The two files are split only because one file of
;;; 68 KB exceeds what `vnb-probe' can ship in one SSM command; the load window
;;; is the same for both.
;;;
;;; Each distribution is "FINSUM commutes with an abelian-group endomorphism",
;;; and each is proved the same way: a fold-length induction (`ni' on n) in
;;; which the image family is given POINTWISE -- never as a lambda, since a
;;; VNB-LAMBDA under the ENUM-FAM binder owes an unprovable typing leaf
;;; (CLAUDE.md, 2026-08-17) -- and then one FINSUM-level driver,
;;; `rkj-distrib-finsum!', shared by all three.  The view read-offs
;;; (ras-carr/op/id, mvag-carr/op/id, theorem-library/ag-view-read-offs) carry
;;; the statement's carrier to the abelian group the fold lives in.
;;;
;;; finsum-interval-peel is the one law here relating TWO index sets, so it is
;;; the one that goes through finsum-insert-ag and bills its leaf,
;;; finsum-well-defined.  `interval-succ-insert' (NEW, modulo 0) is the set
;;; equation [1, succ n] = [1,n] u {succ n} it needs; both inclusions are `prop'
;;; over implications proved by one interval citation each, so no case-split
;;; tactic appears.
;;;
;;; RESULTS (probe on the band):
;;;   module-act-zero-vec, sum-ag-ring-left-ind, sum-ag-ring-right-ind,
;;;   sum-ag-act-ind, interval-succ-insert                    -- proven modulo 0
;;;   finsum-ring-distrib-left-gen, finsum-ring-distrib-right-gen,
;;;   finsum-act-distrib-gen                                  -- proven modulo 0
;;;   finsum-interval-peel -- proven modulo {finsum-well-defined}  [informal]
;;;
;;; LOAD WINDOW: [240, 296), as part 1 -- see that file's header for the
;;; citation that forces each end.  Within the window this file loads AFTER
;;; part 1.
;;;
;;; Helper prefix: rkj-.
;;; rkj probe -- batch J

(define (rkj-check! name)
  (if (not (proof-done? *ps*))
      (begin
        (display ";; rkj: OPEN LEAVES before qed ") (display name) (newline)
        (for-each (lambda (l)
                    (display ";;   ") (display (expression->string (dk-goal-of l))) (newline))
                  (proof-leaves))
        (error "rkj: proof not complete" name))))

(define (rkj-pick-head head what) (dk-pick (dk-head? head) what))

;; the unique context formula (IN v SET) whose v is a symbol
(define (rkj-set-var what)
  (cadr (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'IN) (symbol? (cadr f))
                                  (eq? (caddr f) 'SET)))
                 what)))

;; (IN v (FUN DOM _)) with DOM equal? to dom
(define (rkj-fun-var dom what)
  (cadr (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                  (pair? (caddr f)) (eq? (car (caddr f)) 'FUN)
                                  (equal? (cadr (caddr f)) dom)))
                 what)))

;; (FORALL v (IMPLIES (IN v DOM) BODY)), DOM a term or a predicate on terms
(define (rkj-guarded-forall? f dom)
  (and (pair? f) (eq? (car f) 'FORALL) (= (length f) 3)
       (let ((b (caddr f)))
         (and (pair? b) (eq? (car b) 'IMPLIES) (= (length b) 3)
              (let ((a (cadr b)))
                (and (pair? a) (eq? (car a) 'IN) (= (length a) 3)
                     (if (procedure? dom) (dom (caddr a)) (equal? (caddr a) dom))))))))

;; the eigenvariable of the ORD-SEGMENT typing among LANDED
(define (rkj-seg-var landed)
  (let ((f (any-pred (lambda (f) (and (pair? f) (eq? (car f) 'IN) (symbol? (cadr f))
                                      (pair? (caddr f)) (eq? (car (caddr f)) 'ORD-SEGMENT)))
                     landed)))
    (if f (cadr f)
        (error "rkj-seg-var: no ORD-SEGMENT typing landed"
               (map expression->string landed)))))

;; the statement builders of theorem-library/finsum-additive.scm, under the
;; file's own prefix (the supports below are copied through them, so the
;; S-expression installed is byte-identical to the support's).
(define (rkj-tf v type body) (list 'FORALL v (list 'IMPLIES type body)))
(define (rkj-tfin S body)
  (list 'FORALL S (list 'IMPLIES (list 'IN S 'SET)
    (list 'IMPLIES (list 'IN (list 'CARD S) 'NN) body))))

;; The first (IF c a b) subterm of EXPR, in pre-order, whose condition satisfies PRED.
(define (rkj-find-if expr pred)
  (cond ((not (pair? expr)) #f)
        ((and (eq? (car expr) 'IF) (= (length expr) 4) (pred (cadr expr))) expr)
        (#t (let loop ((es expr))
              (cond ((null? es) #f)
                    ((not (pair? es)) #f)
                    (#t (or (rkj-find-if (car es) pred) (loop (cdr es)))))))))

;; Among LEAVES (as dk-opened returns them), the unique one whose GOAL satisfies PRED.
(define (rkj-leaf leaves pred what)
  (let ((hits (filter (lambda (l) (pred (dk-goal-of l))) leaves)))
    (cond ((null? hits) (error "rkj-leaf: no leaf for" what))
          ((pair? (cdr hits)) (error "rkj-leaf: ambiguous leaf for" what))
          (#t (car hits)))))

;; `if-true'/`if-false' on IFT: the kernel spawns the condition (resp. its negation)
;; as a SIDE leaf and lands (= IFT branch) in the MAIN branch.  Returns the equation.
(define (rkj-if-land! which ift . opt)
  (let* ((closer (if (pair? opt) (car opt) ass))
         (p      (cadr ift))
         (want   (if (eq? which 'true) p (list 'NOT p)))
         (val    (if (eq? which 'true) (caddr ift) (cadddr ift)))
         (new    (dk-opened (lambda () (if (eq? which 'true) (if-true ift) (if-false ift)))))
         (side   (rkj-leaf new (lambda (g) (alpha-equiv? g want)) "if side condition"))
         (main   (rkj-leaf new (lambda (g) (not (alpha-equiv? g want))) "if main branch")))
    (dk-focus! side) (closer)
    (if (not (sequent-node-grounded? side)) (error "rkj-if-land!: side leaf left open"))
    (dk-focus! main)
    (list '= ift val)))

;; Reduce, IN THE GOAL, the first IF whose condition satisfies PRED, and substitute.
(define (rkj-reduce-if! which pred . opt)
  (let ((ift (or (rkj-find-if (dk-goal) pred)
                 (error "rkj-reduce-if!: no IF with the wanted condition in"
                        (expression->string (dk-goal))))))
    (subst (apply rkj-if-land! which ift opt))))

;; the NN-typed eigenvariable in context: (IN v NN) with v a symbol.
(define (rkj-nn-var)
  (cadr (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'IN) (symbol? (cadr f))
                                  (eq? (caddr f) 'NN)))
                 "n in NN")))

;; (FORALL v (IMPLIES (IN v DOM) INNER)) with INNER satisfying PRED.
(define (rkj-guarded-forall-inner? f dom pred)
  (and (rkj-guarded-forall? f dom)
       (pred (caddr (caddr f)))))

(define (rkj-seg-dom? d) (and (pair? d) (eq? (car d) 'ORD-SEGMENT)))

;; H is a guarded universal over ORD-SEGMENT(succ n); land its restriction to
;; ORD-SEGMENT(n).  BODY-AT builds the inner formula from a variable.
(define (rkj-restrict! h nv body-at)
  (let ((segN (list 'ORD-SEGMENT nv))
        (segS (list 'ORD-SEGMENT (list 'succ nv))))
    (have! (list 'FORALL 'i_ (list 'IMPLIES (list 'IN 'i_ segN) (body-at 'i_)))
           (lambda ()
             (let* ((landed (dk-peel!))
                    (iv     (rkj-seg-var landed)))
               (have! (list 'IN iv segS)
                      (lambda () (mac 'ord-segment-nn-succ) (oi-l) (ass)))
               (dk-apply! h iv)
               (ass))))))

;; (rkj-imps h1 h2 ... concl) -- a curried implication chain.
(define (rkj-imps . args)
  (let loop ((a args))
    (if (null? (cdr a)) (car a) (list 'IMPLIES (car a) (loop (cdr a))))))
;; (rkj-foralls '(x y) BODY)
(define (rkj-foralls vars body)
  (fold-right (lambda (v b) (list 'FORALL v b)) body vars))

;; from (IN FAM (FUN NN (CARR ag))) in context, land the pointwise typing on
;; ORD-SEGMENT(NC) that the fold-length lemmas want.
(define (rkj-ptwise-from-fun! fam nc agv)
  (have! (list 'FORALL 'i_ (list 'IMPLIES (list 'IN 'i_ (list 'ORD-SEGMENT nc))
                                 (list 'IN (list fam 'i_) (list 'CARR agv))))
         (lambda ()
           (let* ((landed (dk-peel!))
                  (iv     (rkj-seg-var landed)))
             (dk-fact! 'ord-segment-nn-subset nc iv)
             (dk-fact! 'fun-apply-type-c fam 'NN (list 'CARR agv) iv)
             (ass)))))

(define (rkj-o ag x y) (list (list 'OPR ag) x y))

;;; ------------------------------------------------- ring distribution, LEFT
;;; sum-ag-ring-left-ind: the fold-length induction behind
;;; finsum-ring-distrib-left-gen.  ga_ is the summand family, gb_ its image
;;; under x |-> r*x, given POINTWISE (never as a lambda: a lambda under the
;;; ENUM-FAM binder is the unprovable-owed-leaf trap).
(define rkj-rl-ind-stmt
  (rkj-foralls '(n)
    (rkj-imps '(IN n NN)
      (rkj-foralls '(rng)
        (rkj-imps '(IS-RING rng)
          (rkj-foralls '(r)
            (rkj-imps '(IN r (CARR rng))
              (rkj-foralls '(ga_ gb_)
                (rkj-imps '(FORALL i_ (IMPLIES (IN i_ (ORD-SEGMENT n))
                             (IN (ga_ i_) (CARR rng))))
                          '(FORALL i_ (IMPLIES (IN i_ (ORD-SEGMENT n))
                             (== (gb_ i_) ((MUL rng) r (ga_ i_)))))
                          '(= (SUM-AG (RING-ADDITIVE-AG rng) gb_ n)
                              ((MUL rng) r (SUM-AG (RING-ADDITIVE-AG rng) ga_ n))))))))))))

;; the four view read-offs of RING-ADDITIVE-AG, plus the group facts
(define (rkj-ras-prep! rngv rag)
  (dk-fact! 'ring-additive-ag-is-abelian-group rngv)
  (dk-fact! 'abelian-group-is-group rag)
  (dk-fact! 'group-identity-in rag)
  (dk-fact! 'ras-carr rngv)
  (dk-fact! 'ras-op rngv)
  (dk-fact! 'ras-id rngv))

;; (IN t (CARR rag)) in context, want (IN t (CARR rng)) -- or the other way.
(define (rkj-carr-bridge! t from to)
  (have! (list 'IN t to)
         (lambda () (subst (list '= to from)) (ass))))

(sp (make-wff rkj-rl-ind-stmt))
(let* ((leaves (dk-opened (lambda () (ni))))
       (base (rkj-leaf leaves (lambda (g) (not (dk-contains? g 'succ))) "induction base"))
       (step (rkj-leaf leaves (lambda (g) (dk-contains? g 'succ))       "induction step")))
  ;; ---- base --------------------------------------------------------------
  (dk-focus! base)
  (dk-peel!)
  (let* ((gl  (dk-goal))
         (rag (cadr (cadr gl)))
         (rngv (cadr rag))
         (rv  (cadr (caddr gl))))
    (rkj-ras-prep! rngv rag)
    (mac 'sum-ag-zero)                 ; (= (IDEN rag) ((MUL rng) r (IDEN rag)))
    (have! (list '= (list (list 'MUL rngv) rv (list 'IDEN rag)) (list 'IDEN rag))
           (lambda ()
             (subst (list '= (list 'IDEN rag) (list 'ZERO rngv)))
             (dk-fact! 'ring-mul-zero-right rngv rv)
             (ass)))
    (subst (list '= (list (list 'MUL rngv) rv (list 'IDEN rag)) (list 'IDEN rag)))
    (rfl))
  ;; ---- step --------------------------------------------------------------
  (dk-focus! step)
  (dk-peel!)
  (let* ((nv  (rkj-nn-var))
         (gl  (dk-goal))
         (rag (cadr (cadr gl)))
         (rngv (cadr rag))
         (gbv (caddr (cadr gl)))
         (rv  (cadr (caddr gl)))
         (gav (caddr (caddr (caddr gl))))
         (cr  (list 'CARR rngv))
         (ca  (list 'CARR rag))
         (segS (list 'ORD-SEGMENT (list 'succ nv)))
         (sa  (list 'SUM-AG rag gav nv))
         (typA (dk-pick (lambda (f) (rkj-guarded-forall-inner? f rkj-seg-dom?
                  (lambda (i) (and (pair? i) (eq? (car i) 'IN)))))
                        "the typing of ga_"))
         (agree (dk-pick (lambda (f) (rkj-guarded-forall-inner? f rkj-seg-dom?
                  (lambda (i) (and (pair? i) (eq? (car i) '==)))))
                         "the pointwise hypothesis"))
         (ih  (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                        (not (rkj-guarded-forall? f rkj-seg-dom?))))
                       "the IH")))
    (display ";; rkj rl-ind step: ") (display (list nv rngv rv gav gbv)) (newline)
    (rkj-ras-prep! rngv rag)
    (have! (list 'IN nv segS) (lambda () (mac 'ord-segment-nn-succ) (oi-r) (rfl)))
    (dk-apply! typA nv)                       ; (IN (ga_ n) (CARR rng))
    (dk-apply! agree nv)                      ; (== (gb_ n) ((MUL rng) r (ga_ n)))
    (rkj-restrict! typA nv (lambda (i) (list 'IN (list gav i) cr)))
    (rkj-restrict! agree nv (lambda (i) (list '== (list gbv i)
                                              (list (list 'MUL rngv) rv (list gav i)))))
    ;; the fold's own typing, through the view carrier
    (have! (list 'FORALL 'i_ (list 'IMPLIES (list 'IN 'i_ (list 'ORD-SEGMENT nv))
                                   (list 'IN (list gav 'i_) ca)))
           (lambda ()
             (let* ((landed (dk-peel!)) (iv (rkj-seg-var landed)))
               (subst (list '= ca cr))
               (dk-apply! (dk-pick (lambda (f) (rkj-guarded-forall-inner? f rkj-seg-dom?
                                     (lambda (i) (and (pair? i) (eq? (car i) 'IN)
                                                      (equal? (caddr i) cr)
                                                      (pair? (cadr i))
                                                      (eq? (car (cadr i)) gav)))))
                                   "the restricted typing of ga_")
                          iv)
               (ass))))
    (dk-fact! 'sum-ag-type-ptwise nv rag gav)  ; (IN sa (CARR rag))
    (rkj-carr-bridge! sa ca cr)                ; (IN sa (CARR rng))
    (mac 'sum-ag-succ)
    (subst (list '== (list gbv nv) (list (list 'MUL rngv) rv (list gav nv))))
    (dk-apply! ih rngv rv gav gbv)
    (subst (list '= (list 'SUM-AG rag gbv nv) (list (list 'MUL rngv) rv sa)))
    (mac 'ras-op)
    (dk-fact! 'ring-left-dist rngv rv sa (list gav nv))
    (dk-fact! 'equality-symmetry
              (list (list 'MUL rngv) rv (list (list 'ADD rngv) sa (list gav nv)))
              (list (list 'ADD rngv) (list (list 'MUL rngv) rv sa)
                                     (list (list 'MUL rngv) rv (list gav nv))))
    (ass)))
(rkj-check! 'sum-ag-ring-left-ind)
(qed 'sum-ag-ring-left-ind)
(topic! 'sum-ag-ring-left-ind 'algebra)

;;; finsum-ring-distrib-left-gen -- finsum-additive.scm:217, copied literally.
(define rkj-rag '(RING-ADDITIVE-AG rng))
(define rkj-rl-stmt
  (rkj-tf 'rng '(IS-RING rng)
    (rkj-tf 'r '(IN r (CARR rng))
      (rkj-tfin 'S
        (rkj-tf 'f '(IN f (FUN S (CARR rng)))
          (list '=
            (list '(MUL rng) 'r (list 'FINSUM rkj-rag 'f 'S))
            (list 'FINSUM rkj-rag
                  (list 'VNB-LAMBDA 'z 'S (list '(MUL rng) 'r '(f z))) 'S)))))))

;; The FINSUM-level driver, shared by the two ring distributions and the module
;; action.  IND is the fold-length lemma; MK-IMG builds the image term from the
;; summand value; SIDE says which side of the goal the FINSUM-of-images is on.
(define (rkj-distrib-finsum! stmt ind mk-img prep!)
  (sp (make-wff stmt))
  (dk-peel!)
  (let* ((gl  (dk-goal))
         (mul (cadr gl))                   ; the applied map at the FINSUM
         (rhs (caddr gl))                  ; (FINSUM ag LAM S)
         (agv (cadr rhs)) (lam (caddr rhs)) (sv (cadddr rhs))
         (fs  (or (any-pred (lambda (t) (and (pair? t) (eq? (car t) 'FINSUM))) (cdr mul))
                  (error "rkj-distrib-finsum!: no FINSUM on the left")))
         (fv  (caddr fs))
         (strv (cadr (car mul)))           ; the structure, off (MUL rng) / (ACT md)
         (rv  (or (any-pred (lambda (t) (not (equal? t fs))) (cdr mul))
                  (error "no scalar")))
         (nc  (list 'CARD sv)) (phi (list 'FIN-ENUM sv))
         (seg (list 'ORD-SEGMENT nc))
         (ca  (list 'CARR agv))
         (cr  (caddr (caddr (dk-pick (lambda (a) (and (pair? a) (eq? (car a) 'IN)
                                                      (eq? (cadr a) fv)
                                                      (pair? (caddr a))
                                                      (eq? (car (caddr a)) 'FUN)))
                                     "f's typing"))))   ; the statement's carrier
         (fam (lambda (u) (list 'ENUM-FAM agv u phi nc))))
    (display ";; rkj distrib vars: ") (display (list strv rv sv fv agv cr)) (newline)
    (prep! strv agv)
    (mac 'FINSUM)
    (let ((bij (dk-fact! 'fin-enum-is-bijection sv)))
      (mac-h 'bijection-membership-iff bij)
      (dk-split-all!))
    (if (not (equal? ca cr))
        (have! (list 'IN fv (list 'FUN sv ca))
               (lambda () (subst (list '= ca cr)) (ass))))
    (dk-fact! 'enum-fam-in-fun nc agv sv phi fv)
    (have! (list 'FORALL 'i_ (list 'IMPLIES (list 'IN 'i_ seg)
                                   (list 'IN (list (fam fv) 'i_) cr)))
           (lambda ()
             (let* ((landed (dk-peel!)) (iv (rkj-seg-var landed)))
               (dk-fact! 'ord-segment-nn-subset nc iv)
               (dk-fact! 'fun-apply-type-c (fam fv) 'NN ca iv)
               (if (not (equal? ca cr)) (subst (list '= cr ca)))
               (ass))))
    (have! (list 'FORALL 'i_ (list 'IMPLIES (list 'IN 'i_ seg)
                                   (list '== (list (fam lam) 'i_)
                                             (mk-img strv rv (list (fam fv) 'i_)))))
           (lambda ()
             (let* ((landed (dk-peel!)) (iv (rkj-seg-var landed)))
               (dk-fact! 'ord-segment-nn-subset nc iv)
               (dk-fact! 'fun-apply-type-c phi seg sv iv)
               (dk-fact! 'enum-fam-value nc agv lam phi iv)
               (dk-fact! 'enum-fam-value nc agv fv  phi iv)
               (subst (list '== (list (fam lam) iv) (list lam (list phi iv))))
               (subst (list '== (list (fam fv) iv) (list fv (list phi iv))))
               (lam-b)
               (qrfl))))
    (dk-fact! ind nc strv rv (fam fv) (fam lam))
    (dk-fact! 'equality-symmetry
              (list 'SUM-AG agv (fam lam) nc)
              (mk-img strv rv (list 'SUM-AG agv (fam fv) nc)))
    (ass)))

(rkj-distrib-finsum! rkj-rl-stmt 'sum-ag-ring-left-ind
                     (lambda (str r x) (list (list 'MUL str) r x))
                     rkj-ras-prep!)
(rkj-check! 'finsum-ring-distrib-left-gen)
(qed 'finsum-ring-distrib-left-gen)

;;; ------------------------------------------------ ring distribution, RIGHT
(define rkj-rr-ind-stmt
  (rkj-foralls '(n)
    (rkj-imps '(IN n NN)
      (rkj-foralls '(rng)
        (rkj-imps '(IS-RING rng)
          (rkj-foralls '(r)
            (rkj-imps '(IN r (CARR rng))
              (rkj-foralls '(ga_ gb_)
                (rkj-imps '(FORALL i_ (IMPLIES (IN i_ (ORD-SEGMENT n))
                             (IN (ga_ i_) (CARR rng))))
                          '(FORALL i_ (IMPLIES (IN i_ (ORD-SEGMENT n))
                             (== (gb_ i_) ((MUL rng) (ga_ i_) r))))
                          '(= (SUM-AG (RING-ADDITIVE-AG rng) gb_ n)
                              ((MUL rng) (SUM-AG (RING-ADDITIVE-AG rng) ga_ n) r)))))))))))

(sp (make-wff rkj-rr-ind-stmt))
(let* ((leaves (dk-opened (lambda () (ni))))
       (base (rkj-leaf leaves (lambda (g) (not (dk-contains? g 'succ))) "induction base"))
       (step (rkj-leaf leaves (lambda (g) (dk-contains? g 'succ))       "induction step")))
  ;; ---- base --------------------------------------------------------------
  (dk-focus! base)
  (dk-peel!)
  (let* ((gl  (dk-goal))
         (rag (cadr (cadr gl)))
         (rngv (cadr rag))
         (rv  (caddr (caddr gl))))
    (rkj-ras-prep! rngv rag)
    (mac 'sum-ag-zero)
    (have! (list '= (list (list 'MUL rngv) (list 'IDEN rag) rv) (list 'IDEN rag))
           (lambda ()
             (subst (list '= (list 'IDEN rag) (list 'ZERO rngv)))
             (dk-fact! 'ring-mul-zero-left rngv rv)
             (ass)))
    (subst (list '= (list (list 'MUL rngv) (list 'IDEN rag) rv) (list 'IDEN rag)))
    (rfl))
  ;; ---- step --------------------------------------------------------------
  (dk-focus! step)
  (dk-peel!)
  (let* ((nv  (rkj-nn-var))
         (gl  (dk-goal))
         (rag (cadr (cadr gl)))
         (rngv (cadr rag))
         (gbv (caddr (cadr gl)))
         (rv  (caddr (caddr gl)))
         (gav (caddr (cadr (caddr gl))))
         (cr  (list 'CARR rngv))
         (ca  (list 'CARR rag))
         (segS (list 'ORD-SEGMENT (list 'succ nv)))
         (sa  (list 'SUM-AG rag gav nv))
         (typA (dk-pick (lambda (f) (rkj-guarded-forall-inner? f rkj-seg-dom?
                  (lambda (i) (and (pair? i) (eq? (car i) 'IN)))))
                        "the typing of ga_"))
         (agree (dk-pick (lambda (f) (rkj-guarded-forall-inner? f rkj-seg-dom?
                  (lambda (i) (and (pair? i) (eq? (car i) '==)))))
                         "the pointwise hypothesis"))
         (ih  (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                        (not (rkj-guarded-forall? f rkj-seg-dom?))))
                       "the IH")))
    (display ";; rkj rr-ind step: ") (display (list nv rngv rv gav gbv)) (newline)
    (rkj-ras-prep! rngv rag)
    (have! (list 'IN nv segS) (lambda () (mac 'ord-segment-nn-succ) (oi-r) (rfl)))
    (dk-apply! typA nv)
    (dk-apply! agree nv)
    (rkj-restrict! typA nv (lambda (i) (list 'IN (list gav i) cr)))
    (rkj-restrict! agree nv (lambda (i) (list '== (list gbv i)
                                              (list (list 'MUL rngv) (list gav i) rv))))
    (have! (list 'FORALL 'i_ (list 'IMPLIES (list 'IN 'i_ (list 'ORD-SEGMENT nv))
                                   (list 'IN (list gav 'i_) ca)))
           (lambda ()
             (let* ((landed (dk-peel!)) (iv (rkj-seg-var landed)))
               (subst (list '= ca cr))
               (dk-apply! (dk-pick (lambda (f) (rkj-guarded-forall-inner? f rkj-seg-dom?
                                     (lambda (i) (and (pair? i) (eq? (car i) 'IN)
                                                      (equal? (caddr i) cr)
                                                      (pair? (cadr i))
                                                      (eq? (car (cadr i)) gav)))))
                                   "the restricted typing of ga_")
                          iv)
               (ass))))
    (dk-fact! 'sum-ag-type-ptwise nv rag gav)
    (rkj-carr-bridge! sa ca cr)
    (mac 'sum-ag-succ)
    (subst (list '== (list gbv nv) (list (list 'MUL rngv) (list gav nv) rv)))
    (dk-apply! ih rngv rv gav gbv)
    (subst (list '= (list 'SUM-AG rag gbv nv) (list (list 'MUL rngv) sa rv)))
    (mac 'ras-op)
    (dk-fact! 'ring-right-dist rngv sa (list gav nv) rv)
    (dk-fact! 'equality-symmetry
              (list (list 'MUL rngv) (list (list 'ADD rngv) sa (list gav nv)) rv)
              (list (list 'ADD rngv) (list (list 'MUL rngv) sa rv)
                                     (list (list 'MUL rngv) (list gav nv) rv)))
    (ass)))
(rkj-check! 'sum-ag-ring-right-ind)
(qed 'sum-ag-ring-right-ind)
(topic! 'sum-ag-ring-right-ind 'algebra)

;;; finsum-ring-distrib-right-gen -- finsum-additive.scm:233, copied literally.
(define rkj-rr-stmt
  (rkj-tf 'rng '(IS-RING rng)
    (rkj-tf 'r '(IN r (CARR rng))
      (rkj-tfin 'S
        (rkj-tf 'f '(IN f (FUN S (CARR rng)))
          (list '=
            (list '(MUL rng) (list 'FINSUM rkj-rag 'f 'S) 'r)
            (list 'FINSUM rkj-rag
                  (list 'VNB-LAMBDA 'z 'S (list '(MUL rng) '(f z) 'r)) 'S)))))))
(rkj-distrib-finsum! rkj-rr-stmt 'sum-ag-ring-right-ind
                     (lambda (str r x) (list (list 'MUL str) x r))
                     rkj-ras-prep!)
(rkj-check! 'finsum-ring-distrib-right-gen)
(qed 'finsum-ring-distrib-right-gen)

;;; ----------------------------------------------------- the module action
(define (rkj-mvag-prep! mdv mvag)
  (dk-fact! 'module-vector-ag-is-abelian-group mdv)
  (dk-fact! 'abelian-group-is-group mvag)
  (dk-fact! 'group-identity-in mvag)
  (dk-fact! 'mvag-carr mdv)
  (dk-fact! 'mvag-op mdv)
  (dk-fact! 'mvag-id mdv))

;;; module-act-zero-vec: r . 0_V = 0_V.  The vector-side twin of module-zero-act
;;; (0_R . x = 0_V): r.0 is idempotent under VADD, so it is the zero.
(sp (make-wff
     (rkj-tf 'md '(IS-MODULE md)
       (rkj-tf 'r '(IN r (CARR (SCAL md)))
         '(= ((ACT md) r (VZERO md)) (VZERO md))))))
(dk-peel!)
(let* ((gl (dk-goal))
       (aa (cadr gl))                       ; ((ACT md) r (VZERO md))
       (mdv (cadr (car aa)))
       (rv  (cadr aa))
       (mvag (list 'MODULE-VECTOR-AG mdv))
       (zz  (list 'VZERO mdv))
       (V   (lambda (x y) (list (list 'VADD mdv) x y))))
  (rkj-mvag-prep! mdv mvag)
  (dk-fact! 'module-vzero-in mdv)                       ; (IN 0_V (VEC md))
  (dk-fact! 'module-act-type mdv rv zz)                 ; (IN A (VEC md))
  (have! (list '= (V zz zz) zz)
         (lambda ()
           (subst (list '= (list 'VADD mdv) (list 'OPR mvag)))   ; operator position
           (subst (list '= zz (list 'IDEN mvag)))
           (dk-fact! 'group-left-id mvag (list 'IDEN mvag))
           (ass)))
  (dk-fact! 'module-act-distrib-vec mdv rv zz zz)
  (have! (list '= (V aa aa) aa)
         (lambda ()
           (subst (list '= (V aa aa) (list (list 'ACT mdv) rv (V zz zz))))
           (subst (list '= (V zz zz) zz))
           (rfl)))
  (dk-fact! 'abelian-group-idempotent-is-id-module-vector-ag mdv aa)
  (ass))
(rkj-check! 'module-act-zero-vec)
(qed 'module-act-zero-vec)
(topic! 'module-act-zero-vec 'algebra)

;;; sum-ag-act-ind: the fold-length induction behind finsum-act-distrib-gen.
(define rkj-ac-ind-stmt
  (rkj-foralls '(n)
    (rkj-imps '(IN n NN)
      (rkj-foralls '(md)
        (rkj-imps '(IS-MODULE md)
          (rkj-foralls '(r)
            (rkj-imps '(IN r (CARR (SCAL md)))
              (rkj-foralls '(ga_ gb_)
                (rkj-imps '(FORALL i_ (IMPLIES (IN i_ (ORD-SEGMENT n))
                             (IN (ga_ i_) (CARR (MODULE-VECTOR-AG md)))))
                          '(FORALL i_ (IMPLIES (IN i_ (ORD-SEGMENT n))
                             (== (gb_ i_) ((ACT md) r (ga_ i_)))))
                          '(= (SUM-AG (MODULE-VECTOR-AG md) gb_ n)
                              ((ACT md) r (SUM-AG (MODULE-VECTOR-AG md) ga_ n))))))))))))

(sp (make-wff rkj-ac-ind-stmt))
(let* ((leaves (dk-opened (lambda () (ni))))
       (base (rkj-leaf leaves (lambda (g) (not (dk-contains? g 'succ))) "induction base"))
       (step (rkj-leaf leaves (lambda (g) (dk-contains? g 'succ))       "induction step")))
  ;; ---- base --------------------------------------------------------------
  (dk-focus! base)
  (dk-peel!)
  (let* ((gl  (dk-goal))
         (mvag (cadr (cadr gl)))
         (mdv (cadr mvag))
         (rv  (cadr (caddr gl))))
    (rkj-mvag-prep! mdv mvag)
    (mac 'sum-ag-zero)
    (have! (list '= (list (list 'ACT mdv) rv (list 'IDEN mvag)) (list 'IDEN mvag))
           (lambda ()
             (subst (list '= (list 'IDEN mvag) (list 'VZERO mdv)))
             (dk-fact! 'module-act-zero-vec mdv rv)
             (ass)))
    (subst (list '= (list (list 'ACT mdv) rv (list 'IDEN mvag)) (list 'IDEN mvag)))
    (rfl))
  ;; ---- step --------------------------------------------------------------
  (dk-focus! step)
  (dk-peel!)
  (let* ((nv  (rkj-nn-var))
         (gl  (dk-goal))
         (mvag (cadr (cadr gl)))
         (mdv (cadr mvag))
         (gbv (caddr (cadr gl)))
         (rv  (cadr (caddr gl)))
         (gav (caddr (caddr (caddr gl))))
         (ca  (list 'CARR mvag))
         (vm  (list 'VEC mdv))
         (segS (list 'ORD-SEGMENT (list 'succ nv)))
         (sa  (list 'SUM-AG mvag gav nv))
         (typA (dk-pick (lambda (f) (rkj-guarded-forall-inner? f rkj-seg-dom?
                  (lambda (i) (and (pair? i) (eq? (car i) 'IN)))))
                        "the typing of ga_"))
         (agree (dk-pick (lambda (f) (rkj-guarded-forall-inner? f rkj-seg-dom?
                  (lambda (i) (and (pair? i) (eq? (car i) '==)))))
                         "the pointwise hypothesis"))
         (ih  (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                        (not (rkj-guarded-forall? f rkj-seg-dom?))))
                       "the IH")))
    (display ";; rkj ac-ind step: ") (display (list nv mdv rv gav gbv)) (newline)
    (rkj-mvag-prep! mdv mvag)
    (have! (list 'IN nv segS) (lambda () (mac 'ord-segment-nn-succ) (oi-r) (rfl)))
    (dk-apply! typA nv)
    (dk-apply! agree nv)
    (rkj-restrict! typA nv (lambda (i) (list 'IN (list gav i) ca)))
    (rkj-restrict! agree nv (lambda (i) (list '== (list gbv i)
                                              (list (list 'ACT mdv) rv (list gav i)))))
    (dk-fact! 'sum-ag-type-ptwise nv mvag gav)
    (rkj-carr-bridge! sa ca vm)
    (rkj-carr-bridge! (list gav nv) ca vm)
    (mac 'sum-ag-succ)
    (subst (list '== (list gbv nv) (list (list 'ACT mdv) rv (list gav nv))))
    (dk-apply! ih mdv rv gav gbv)
    (subst (list '= (list 'SUM-AG mvag gbv nv) (list (list 'ACT mdv) rv sa)))
    (mac 'mvag-op)
    (dk-fact! 'module-act-distrib-vec mdv rv sa (list gav nv))
    (dk-fact! 'equality-symmetry
              (list (list 'ACT mdv) rv (list (list 'VADD mdv) sa (list gav nv)))
              (list (list 'VADD mdv) (list (list 'ACT mdv) rv sa)
                                     (list (list 'ACT mdv) rv (list gav nv))))
    (ass)))
(rkj-check! 'sum-ag-act-ind)
(qed 'sum-ag-act-ind)
(topic! 'sum-ag-act-ind 'algebra)

;;; finsum-act-distrib-gen -- structure-library/mod-seq.scm:162, copied literally.
(define rkj-ac-stmt
  '(FORALL md (IMPLIES (IS-MODULE md)
     (FORALL r (IMPLIES (IN r (CARR (SCAL md)))
     (FORALL S (IMPLIES (IN S SET) (IMPLIES (IN (CARD S) NN)
     (FORALL f (IMPLIES (IN f (FUN S (CARR (MODULE-VECTOR-AG md))))
       (= ((ACT md) r (FINSUM (MODULE-VECTOR-AG md) f S))
          (FINSUM (MODULE-VECTOR-AG md)
                  (VNB-LAMBDA z S ((ACT md) r (f z)))
                  S))))))))))))
(rkj-distrib-finsum! rkj-ac-stmt 'sum-ag-act-ind
                     (lambda (str r x) (list (list 'ACT str) r x))
                     rkj-mvag-prep!)
(rkj-check! 'finsum-act-distrib-gen)
(qed 'finsum-act-distrib-gen)

;;; ================================================= the interval back-peel
;;; interval-succ-insert: [1, succ n] = [1,n] u {succ n}.  Set extensionality;
;;; the two inclusions are `prop' over three implications each proved by one
;;; interval citation, so no case-split tactic is needed.
(sp (make-wff
     (rkj-tf 'n '(IN n NN)
       '(= (INTERVAL 1 (succ n)) (UNION (INTERVAL 1 n) (PAIR (succ n) (succ n)))))))
(dk-peel!)
(let* ((nv  (rkj-nn-var))
       (sn  (list 'succ nv))
       (i1n (list 'INTERVAL 1 nv))
       (i1s (list 'INTERVAL 1 sn))
       (pr  (list 'PAIR sn sn))
       (un  (list 'UNION i1n pr)))
  (dk-fact! 'nn-succ-closed nv)
  (dk-fact! 'membership-implies-sethood sn 'NN)
  (dk-fact! 'interval-in-set 1 sn)
  (dk-fact! 'interval-in-set 1 nv)
  (have! (list 'AND (list 'IN sn 'SET) (list 'IN sn 'SET)))
  (dk-fact! 'pairing sn sn)
  (have! (list 'AND (list 'IN i1n 'SET) (list 'IN pr 'SET)))
  (dk-fact! 'union-set-closure i1n pr)
  (have! (list 'AND (list 'IN i1s 'SET) (list 'IN un 'SET)))
  (dk-fact! 'nn-one-le-succ nv)                        ; (<= 1 (succ n))
  (dk-fact! 'nn-le-refl sn)                            ; (<= (succ n) (succ n))
  (dk-fact! 'nn-le-succ nv)                            ; (<= n (succ n))
  (let ((ext (dk-fact! 'extensionality i1s un)))
    (have! (list 'FORALL 'x_ (list 'IFF (list 'IN 'x_ i1s) (list 'IN 'x_ un)))
           (lambda ()
             (let* ((xv (dk-di-var! (lambda (g) (cadr (cadr g))))))
               ;; ->
               (have! (list 'IMPLIES (list 'IN xv i1s) (list 'IN xv un))
                      (lambda ()
                        (di)
                        (dk-fact! 'interval-elt-in-nn 1 sn xv)
                        (dk-fact! 'interval-lo 1 sn xv)
                        (dk-fact! 'interval-hi 1 sn xv)
                        (let ((cases (dk-fact! 'nn-le-succ-cases nv xv)))
                          (have! (list 'IMPLIES (list '<= xv nv) (list 'IN xv i1n))
                                 (lambda () (di) (dk-fact! 'interval-mem-intro 1 nv xv) (ass)))
                          (have! (list 'IMPLIES (list '= xv sn) (list 'IN xv pr))
                                 (lambda ()
                                   (di)
                                   (let ((pm (dk-fact! 'pairing-membership sn sn xv)))
                                     (dk-only! pm (list '= xv sn))
                                     (prop))))
                          (mac 'union-membership)
                          (dk-only! cases
                                    (list 'IMPLIES (list '<= xv nv) (list 'IN xv i1n))
                                    (list 'IMPLIES (list '= xv sn) (list 'IN xv pr)))
                          (prop))))
               ;; <-
               (have! (list 'IMPLIES (list 'IN xv un) (list 'IN xv i1s))
                      (lambda ()
                        (di)
                        (let ((um (dk-fact! 'union-membership i1n pr xv)))
                          (have! (list 'IMPLIES (list 'IN xv i1n) (list 'IN xv i1s))
                                 (lambda ()
                                   (di)
                                   (dk-fact! 'interval-elt-in-nn 1 nv xv)
                                   (dk-fact! 'interval-lo 1 nv xv)
                                   (dk-fact! 'interval-hi 1 nv xv)
                                   (dk-fact! 'nn-le-trans-guarded xv nv sn)
                                   (dk-fact! 'interval-mem-intro 1 sn xv)
                                   (ass)))
                          (have! (list 'IMPLIES (list 'IN xv pr) (list 'IN xv i1s))
                                 (lambda ()
                                   (di)
                                   (let ((pm (dk-fact! 'pairing-membership sn sn xv)))
                                     (have! (list '= xv sn)
                                            (lambda ()
                                              (dk-only! pm (list 'IN xv pr))
                                              (prop))))
                                   (subst (list '= xv sn))
                                   (dk-fact! 'interval-mem-intro 1 sn sn)
                                   (ass)))
                          (dk-only! um
                                    (list 'IMPLIES (list 'IN xv i1n) (list 'IN xv i1s))
                                    (list 'IMPLIES (list 'IN xv pr) (list 'IN xv i1s))
                                    (list 'IN xv un))
                          (prop))))
               (dk-only! (list 'IMPLIES (list 'IN xv i1s) (list 'IN xv un))
                         (list 'IMPLIES (list 'IN xv un) (list 'IN xv i1s)))
               (prop))))
    (dk-only! ext (list 'FORALL 'x_ (list 'IFF (list 'IN 'x_ i1s) (list 'IN 'x_ un))))
    (prop)))
(rkj-check! 'interval-succ-insert)
(qed 'interval-succ-insert)
(topic! 'interval-succ-insert 'combinatorial)

;;; finsum-interval-peel -- finsum-additive.scm:411, copied literally.
;;; finsum-insert-ag at X = [1,n], k = succ n, through interval-succ-insert.
(define rkj-peel-stmt
  '(FORALL ag (IMPLIES (IS-ABELIAN-GROUP ag)
     (FORALL n (IMPLIES (IN n NN)
       (FORALL f (IMPLIES (IN f (FUN (INTERVAL 1 (succ n)) (CARR ag)))
         (= (FINSUM ag f (INTERVAL 1 (succ n)))
            ((OPR ag) (FINSUM ag f (INTERVAL 1 n)) (f (succ n)))))))))))

(sp (make-wff rkj-peel-stmt))
(dk-peel!)
(let* ((nv  (rkj-nn-var))
       (gl  (dk-goal))
       (agv (cadr (cadr gl)))
       (fv  (caddr (cadr gl)))
       (sn  (list 'succ nv))
       (i1n (list 'INTERVAL 1 nv))
       (i1s (list 'INTERVAL 1 sn))
       (pr  (list 'PAIR sn sn))
       (un  (list 'UNION i1n pr)))
  (dk-fact! 'nn-succ-closed nv)
  (dk-fact! 'membership-implies-sethood sn 'NN)
  (dk-fact! 'interval-in-set 1 nv)
  (dk-fact! 'interval-card-in-nn 1 nv)
  (have! (list 'NOT (list 'IN sn i1n))
         (lambda ()
           (di)
           (dk-fact! 'interval-hi 1 nv sn)
           (dk-fact! 'nn-succ-le-antisym nv nv)          ; succ n <= n => not(n <= n)
           (dk-fact! 'nn-le-refl nv)
           (ai (list 'NOT (list '<= nv nv)))))
  (dk-fact! 'interval-succ-insert nv)                  ; (= i1s un)
  (have! (list 'IN fv (list 'FUN un (list 'CARR agv)))
         (lambda () (subst (list '= un i1s)) (ass)))
  (dk-fact! 'finsum-insert-ag agv i1n sn fv)
  (subst (list '= i1s un))
  (ass))
(rkj-check! 'finsum-interval-peel)
(qed 'finsum-interval-peel)
