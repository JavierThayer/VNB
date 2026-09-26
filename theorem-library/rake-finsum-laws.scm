;;; theorem-library/rake-finsum-laws.scm -- the ADDITIVE algebra of FINSUM,
;;; proven.  Rake batch J (2026-09-17), part 1 of 2; part 2 is
;;; theorem-library/rake-finsum-laws2.scm (the three distribution laws and the
;;; interval back-peel), which loads AFTER this file and cites two of its
;;; lemmas.  The split is a shipping limit, not a window: both files want the
;;; same slot range.
;;;
;;; Every statement marked "-- copied literally" is the support's own
;;; S-expression from its definition site (finsum-additive.scm's `tf' / `tfin'
;;; builders are reproduced here as rkj-tf / rkj-tfin, so the installed formula
;;; is byte-identical; checked against the band before the supports are retired).
;;;
;;; THE ROUTE, for all of them.  A FINSUM is DEFINED as a SUM-AG along the
;;; CHOSEN enumeration FIN-ENUM(S):
;;;     FINSUM(ag,f,S) = SUM-AG(ag, ENUM-FAM(ag,f,FIN-ENUM S,|S|), |S|).
;;; So every law about ONE index set is a law about a FOLD, and the induction
;;; that is available -- `ni' on the fold LENGTH -- does the whole job, exactly
;;; as theorem-library/finsum-single-support.scm and finsum-type-proof.scm do.
;;; No finite-set induction and no restriction of a function is used; only
;;; finsum-interval-peel (part 2) relates TWO index sets, and it is the only one
;;; that goes through finsum-insert-ag and bills its leaf.
;;;
;;; THE REUSABLE BRICK is `enum-fam-value' (NEW):
;;;     n in NN, i in ORD-SEGMENT(n)  =>  (ENUM-FAM ag u phi n)(i) == u(phi i)
;;; stated with u and phi VARIABLES, so `lam-b' has exactly one redex and the
;;; unprovable-owed-leaf trap (CLAUDE.md, 2026-08-17) cannot fire.  With it a
;;; FINSUM law reduces to a POINTWISE relation between two ENUM-FAMs, which is
;;; what each fold-length lemma consumes; the old if-true/if-false dance at the
;;; ENUM-FAM guard happens once, here, instead of once per law.
;;; `sum-ag-type-ptwise' (NEW) is the matching typing: a fold whose summands lie
;;; in the carrier ON THE SEGMENT lies in the carrier.  sum-ag-type wants
;;; f in FUN(NN, CARR ag), which a back-peeled family never is.
;;;
;;; RESULTS in this file (probe on the band):
;;;   enum-fam-value, sum-ag-type-ptwise, finsum-type-ptwise,
;;;   abelian-group-opr-interchange, sum-ag-add-ind,
;;;   sum-ag-two-support-ind                                  -- proven modulo 0
;;;   finsum-congruence, finsum-congruence-q,
;;;   finsum-congruence-guarded                               -- proven modulo 0
;;;   finsum-add-ag, finsum-two-support                       -- proven modulo 0
;;;   finsum-fubini-c    -- proven modulo {finsum-fubini}          [informal]
;;;
;;; finsum-congruence AS IT USED TO BE STATED WAS FALSE -- untyped summands under
;;; a STRICT `=' conclusion, which asserts a definedness nothing supplies.  The
;;; support was RESTATED 2026-09-17 (the user's decision) with the POINTWISE
;;; typing of f as a second antecedent, and it is that statement that is proved
;;; here.  The counterexample, and why all three variants exist, are in the block
;;; above the proofs.
;;;
;;; NOT PROVEN, and the obstacle is worth keeping: `finsum-embed'
;;; (finsum-additive.scm:360) -- a sum over S2 collapses to the sum over a
;;; subset S off which the summand is the identity.  It relates two index sets
;;; with no bijection between them, so the fold route does not reach it; it
;;; wants an induction on |S2 \ S|.  `finite-set-induction' DOES exist (a
;;; class-form principle, base EMPTY-SET, step u |-> u u {x}), so the missing
;;; piece is not the induction but (i) RESTRICTION -- the step's IH needs
;;; f in FUN(u, CARR ag) while f's domain is exactly S2, the gap
;;; finsum-single-support.scm's header records -- and (ii) the surgery
;;; S = (S \ {x}) u {x} with CARD(S \ {x}) in NN.  (i) is now dissolvable:
;;; a restriction IS the VNB-LAMBDA (VNB-LAMBDA z u (f z)), typed by `lam-t',
;;; and `finsum-congruence-q' (proven here, and with NO typing hypothesis)
;;; transports the sum to it.  (ii) still wants `difference-membership' plus a
;;; converse of `card-insert'.
;;;
;;; LOAD WINDOW, by FILE NAME (the same for both files): AFTER
;;; theorem-library/interval-card-in-nn (position 239 -- part 2's latest
;;; citation) and, for this file alone, AFTER theorem-library/rake-finsum-typing
;;; (226, sum-ag-in-subset-ind).  The next-latest citations are nn-order-via-rr
;;; 219, ring-zero-one-power 210 (ring-mul-zero-left/right, part 2),
;;; cancellation 209 (abelian-group-idempotent-is-id-module-vector-ag, part 2),
;;; finsum-single-support 201 (sum-ag-single-ind), finsum-type-proof 200,
;;; subtype-laws 198, nn-order-basics 169, nn-order-ord 167,
;;; fun-apply-type-proof 163, ag-view-read-offs 161 (part 2), finsum-insert 155
;;; (sum-ag-segment-congruence, ord-segment-self, finsum-insert-ag),
;;; ord-segment-nn-subset-proof 154, interval-mem-intro 152, interval-basics 151,
;;; equality-basics 148.  BEFORE theorem-library/finsum-fiber (296), the earliest
;;; PROVEN citer of finsum-congruence and finsum-fubini-c.  I.e. [240, 296).
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

;;; ===================================================================== bricks
;;; enum-fam-value: the enumerated family at an index INSIDE the segment is the
;;; summand at the enumerated point.  `u' and `phi' are VARIABLES, so (u (phi i))
;;; stays inert and `lam-b' has exactly one redex to reduce -- the trap
;;; finsum-insert-from-enum dodges the same way.
(define rkj-efv-stmt
  '(FORALL n (IMPLIES (IN n NN)
     (FORALL ag (FORALL u (FORALL phi (FORALL i
       (IMPLIES (IN i (ORD-SEGMENT n))
         (== ((ENUM-FAM ag u phi n) i) (u (phi i)))))))))))
(sp (make-wff rkj-efv-stmt))
(dk-peel!)
(let* ((gl (dk-goal))
       (fam (car (cadr gl)))           ; (ENUM-FAM ag u phi n)
       (iv  (cadr (cadr gl)))
       (nv  (list-ref fam 4)))
  (dk-fact! 'ord-segment-nn-subset nv iv)
  (mac 'ENUM-FAM)
  (lam-b)
  (rkj-reduce-if! 'true (lambda (c) (equal? c (list 'IN iv (list 'ORD-SEGMENT nv)))))
  (qrfl))
(rkj-check! 'enum-fam-value)
(qed 'enum-fam-value)
(topic! 'enum-fam-value 'plumbing)

;;; sum-ag-type-ptwise: a fold whose summands lie in the carrier ON THE SEGMENT
;;; lies in the carrier.  sum-ag-type wants f in FUN(NN, CARR ag); a back-peeled
;;; family is only typed on the segment.  sum-ag-in-subset-ind at sm := CARR(ag).
(define rkj-satp-stmt
  '(FORALL n (IMPLIES (IN n NN)
     (FORALL ag (IMPLIES (IS-ABELIAN-GROUP ag)
     (FORALL g_ (IMPLIES (FORALL i_ (IMPLIES (IN i_ (ORD-SEGMENT n)) (IN (g_ i_) (CARR ag))))
       (IN (SUM-AG ag g_ n) (CARR ag)))))))))
(sp (make-wff rkj-satp-stmt))
(dk-peel!)
(let* ((gl (dk-goal))
       (agv (cadr (cadr gl)))
       (gv  (caddr (cadr gl)))
       (nv  (cadddr (cadr gl))))
  (dk-fact! 'abelian-group-is-group agv)
  (dk-fact! 'group-identity-in agv)
  (have! (list 'FORALL 'x_ (list 'IMPLIES (list 'IN 'x_ (list 'CARR agv))
           (list 'FORALL 'y_ (list 'IMPLIES (list 'IN 'y_ (list 'CARR agv))
             (list 'IN (list (list 'OPR agv) 'x_ 'y_) (list 'CARR agv))))))
         (lambda ()
           (dk-peel!)
           (let* ((xs (map cadr (filter (lambda (a) (and (pair? a) (eq? (car a) 'IN)
                                                         (symbol? (cadr a))
                                                         (equal? (caddr a) (list 'CARR agv))))
                                        (dk-asms))))
                  (gl2 (dk-goal))
                  (xv (cadr (cadr gl2)))
                  (yv (caddr (cadr gl2))))
             (dk-fact! 'group-carrier-closed-opr agv xv yv)
             (ass))))
  (dk-fact! 'sum-ag-in-subset-ind nv agv (list 'CARR agv) gv)
  (ass))
(rkj-check! 'sum-ag-type-ptwise)
(qed 'sum-ag-type-ptwise)
(topic! 'sum-ag-type-ptwise 'algebra)

;;; abelian-group-opr-interchange: (a.b).(c.d) = (a.c).(b.d).
;;; Five rewrites: assoc, assoc, comm, assoc, assoc.
(define rkj-inter-stmt
  (rkj-tf 's '(IS-ABELIAN-GROUP s)
    (rkj-tf 'a '(IN a (CARR s))
      (rkj-tf 'b '(IN b (CARR s))
        (rkj-tf 'c '(IN c (CARR s))
          (rkj-tf 'd '(IN d (CARR s))
            '(= ((OPR s) ((OPR s) a b) ((OPR s) c d))
                ((OPR s) ((OPR s) a c) ((OPR s) b d)))))))))
(sp (make-wff rkj-inter-stmt))
(dk-peel!)
(let* ((gl  (dk-goal))
       (lhs (cadr gl))
       (agv (cadr (car lhs)))
       (ab  (cadr lhs)) (cd (caddr lhs))
       (av (cadr ab)) (bv (caddr ab)) (cv (cadr cd)) (dv (caddr cd))
       (O  (lambda (x y) (rkj-o agv x y))))
  (dk-fact! 'abelian-group-is-group agv)
  (dk-fact! 'group-carrier-closed-opr agv cv dv)
  (dk-fact! 'group-carrier-closed-opr agv bv dv)
  (dk-fact! 'group-carrier-closed-opr agv bv cv)
  (dk-fact! 'group-carrier-closed-opr agv cv bv)
  (dk-fact! 'group-assoc agv av bv (O cv dv))
  (subst (list '= (O (O av bv) (O cv dv)) (O av (O bv (O cv dv)))))
  (dk-fact! 'group-assoc agv bv cv dv)
  (subst (list '= (O bv (O cv dv)) (O (O bv cv) dv)))
  (dk-fact! 'abelian-group-opr-comm agv bv cv)
  (subst (list '= (O bv cv) (O cv bv)))
  (dk-fact! 'group-assoc agv cv bv dv)
  (subst (list '= (O (O cv bv) dv) (O cv (O bv dv))))
  (dk-fact! 'group-assoc agv av cv (O bv dv))
  (subst (list '= (O (O av cv) (O bv dv)) (O av (O cv (O bv dv)))))
  (dk-fact! 'group-carrier-closed-opr agv cv (O bv dv))
  (dk-fact! 'group-carrier-closed-opr agv av (O cv (O bv dv)))
  (rfl))
(rkj-check! 'abelian-group-opr-interchange)
(qed 'abelian-group-opr-interchange)
(topic! 'abelian-group-opr-interchange 'algebra)

;;; ===========================================================================
;;; finsum-congruence: WHY THERE ARE THREE OF THEM, AND WHAT WENT WRONG.
;;;
;;; The support (theorem-library/finsum-additive.scm) used to read
;;;
;;;   ag an abelian group, S finite, f and g UNTYPED, f = g pointwise on S
;;;     =>  FINSUM(ag,f,S) = FINSUM(ag,g,S)
;;;
;;; and its own comment explained, correctly, why f and g carry no FUN typing: a
;;; back-peeled summand is typed on [1,succ n] and summed over [1,n], so an
;;; `f in FUN(S, CARR ag)' hypothesis could never be met.  But `=' is VNB's
;;; STRICT equality -- a term t is defined exactly when t = t (docs/ch-expressions,
;;; "Equality and quasi-equality") -- so that conclusion ASSERTED that the two sums
;;; DENOTE, and nothing in the hypotheses made them denote.  It was FALSE.
;;;
;;; COUNTEREXAMPLE.  Let ag be any abelian group whose carrier is not everything,
;;; let S = {u} be a one-point set, and let f = g be the constant map on S with a
;;; value w NOT in CARR(ag).  The hypothesis holds: f(z) = g(z) is the same
;;; DEFINED term for the one z in S.  But FINSUM(ag,f,S) = (OPR ag)(IDEN ag, w),
;;; and (OPR ag) is a FUN on CARTESIAN(CARR ag, CARR ag), so that application is
;;; UNDEFINED -- and `t = t' is FALSE at an undefined t.  Probed: the literal
;;; statement drives down to `FINSUM(ag,f,S) = FINSUM(ag,f,S)' and `rfl' declines
;;; it, which is the kernel refusing exactly this definedness.
;;;
;;; THE SUPPORT WAS RESTATED (2026-09-17, the user's decision) with the POINTWISE
;;; typing `forall z in S. f z in CARR(ag)' as a SECOND antecedent, after the
;;; equality.  A back-peeled family HAS that, which a FUN typing is what it lacks;
;;; and putting it second leaves every citer's `fact' still auto-detaching the
;;; equality it already lands.  All three forms are proved here:
;;;
;;;   finsum-congruence-q        the conclusion as `==' (quasi-equality), NO typing
;;;                              at all.  This is the mathematical content, and it
;;;                              is what the other proofs in this file cite.
;;;   finsum-congruence-guarded  the old `=' conclusion under `f in FUN(S,CARR ag)'.
;;;                              Kept because it is the form a fully-typed summand
;;;                              wants, and it is one `finsum-type' away.
;;;   finsum-congruence          the RESTATED support: `==' plus the definedness of
;;;                              the left sum, which the pointwise typing buys
;;;                              through finsum-type-ptwise.
;;; ===========================================================================

(define rkj-cong-q-stmt
  (rkj-tf 'ag '(IS-ABELIAN-GROUP ag)
    (rkj-tfin 'S
      (list 'FORALL 'f (list 'FORALL 'g
        (list 'IMPLIES '(FORALL z (IMPLIES (IN z S) (= (f z) (g z))))
                       '(== (FINSUM ag f S) (FINSUM ag g S))))))))

(sp (make-wff rkj-cong-q-stmt))
(dk-peel!)
(let* ((gl  (dk-goal))
       (agv (cadr (cadr gl)))
       (fv  (caddr (cadr gl)))
       (sv  (cadddr (cadr gl)))
       (gv  (caddr (caddr gl)))
       (agree (dk-pick (lambda (a) (rkj-guarded-forall? a sv)) "forall z in S. f z = g z"))
       (phi  (list 'FIN-ENUM sv))
       (seg  (list 'ORD-SEGMENT (list 'CARD sv)))
       (famf (list 'ENUM-FAM agv fv phi (list 'CARD sv)))
       (famg (list 'ENUM-FAM agv gv phi (list 'CARD sv))))
  (display ";; rkj cong vars: ") (display (list agv sv fv gv)) (newline)
  (mac 'FINSUM)
  (let ((bij (dk-fact! 'fin-enum-is-bijection sv)))
    (mac-h 'bijection-membership-iff bij)
    (dk-split-all!))
  (have! (list 'FORALL 'i_ (list 'IMPLIES (list 'IN 'i_ seg)
                                 (list '== (list famf 'i_) (list famg 'i_))))
         (lambda ()
           (let* ((landed (dk-peel!))
                  (iv (rkj-seg-var landed)))
             (dk-fact! 'ord-segment-nn-subset (list 'CARD sv) iv)
             (dk-fact! 'fun-apply-type-c phi seg sv iv)
             (dk-apply! agree (list phi iv))
             (mac 'ENUM-FAM)
             (lam-b)
             (subst (list '= (list fv (list phi iv)) (list gv (list phi iv))))
             (qrfl))))
  (dk-fact! 'sum-ag-segment-congruence (list 'CARD sv) agv famf famg)
  (ass))
(rkj-check! 'finsum-congruence-q)
(qed 'finsum-congruence-q)

;;; finsum-congruence-guarded -- the support's statement with f TYPED.
(define rkj-cong-g-stmt
  (rkj-tf 'ag '(IS-ABELIAN-GROUP ag)
    (rkj-tfin 'S
      (rkj-tf 'f '(IN f (FUN S (CARR ag)))
        (list 'FORALL 'g
          (list 'IMPLIES '(FORALL z (IMPLIES (IN z S) (= (f z) (g z))))
                         '(= (FINSUM ag f S) (FINSUM ag g S))))))))
(sp (make-wff rkj-cong-g-stmt))
(dk-peel!)
(let* ((gl (dk-goal)) (agv (cadr (cadr gl))) (fv (caddr (cadr gl)))
       (sv (cadddr (cadr gl))) (gv (caddr (caddr gl))))
  (dk-fact! 'finsum-congruence-q agv sv fv gv)
  (dk-fact! 'finsum-type agv sv fv)
  (subst (list '== (list 'FINSUM agv gv sv) (list 'FINSUM agv fv sv)))
  (rfl))
(rkj-check! 'finsum-congruence-guarded)
(qed 'finsum-congruence-guarded)

;;; ---------------------------------------------------------------------------
;;; finsum-type-ptwise: the FINSUM of a POINTWISE-typed summand lies in the
;;; carrier.  `finsum-type' (finsum-type-proof.scm) wants f in FUN(S, CARR ag);
;;; a back-peeled summand, typed on a larger interval, is not that, and the
;;; restated finsum-congruence supplies exactly the pointwise form instead.  The
;;; whole content is that the ENUM-FAM of the chosen enumeration lands in the
;;; carrier on ORD-SEGMENT(|S|), which `enum-fam-value' reads off in one step.
(define rkj-ftp-stmt
  (rkj-tf 'ag '(IS-ABELIAN-GROUP ag)
    (rkj-tfin 'S
      (list 'FORALL 'f
        (list 'IMPLIES '(FORALL z (IMPLIES (IN z S) (IN (f z) (CARR ag))))
                       '(IN (FINSUM ag f S) (CARR ag)))))))
(sp (make-wff rkj-ftp-stmt))
(dk-peel!)
(let* ((gl  (dk-goal))
       (fs  (cadr gl))                       ; (FINSUM ag f S)
       (agv (cadr fs)) (fv (caddr fs)) (sv (cadddr fs))
       (nc  (list 'CARD sv))
       (phi (list 'FIN-ENUM sv))
       (seg (list 'ORD-SEGMENT nc))
       (ca  (list 'CARR agv))
       (fam (list 'ENUM-FAM agv fv phi nc))
       ;; picked BEFORE the bijection is opened: surjectivity is a guarded
       ;; universal over S too (CLAUDE.md, "never name an ASSUMPTION by shape").
       (typ (dk-pick (lambda (a) (rkj-guarded-forall-inner? a sv
                                   (lambda (i) (and (pair? i) (eq? (car i) 'IN)))))
                     "forall z in S. f z in CARR(ag)")))
  (mac 'FINSUM)
  (let ((bij (dk-fact! 'fin-enum-is-bijection sv)))
    (mac-h 'bijection-membership-iff bij)
    (dk-split-all!))
  (have! (list 'FORALL 'i_ (list 'IMPLIES (list 'IN 'i_ seg)
                                 (list 'IN (list fam 'i_) ca)))
         (lambda ()
           (let* ((landed (dk-peel!))
                  (iv     (rkj-seg-var landed)))
             (dk-fact! 'ord-segment-nn-subset nc iv)
             (dk-fact! 'fun-apply-type-c phi seg sv iv)      ; (IN (phi i_) S)
             (dk-fact! 'enum-fam-value nc agv fv phi iv)
             (dk-apply! typ (list phi iv))                   ; (IN (f (phi i_)) (CARR ag))
             (subst (list '== (list fam iv) (list fv (list phi iv))))
             (ass))))
  (dk-fact! 'sum-ag-type-ptwise nc agv fam)
  (ass))
(rkj-check! 'finsum-type-ptwise)
(qed 'finsum-type-ptwise)
(topic! 'finsum-type-ptwise 'algebra)

;;; ---------------------------------------------------------------------------
;;; finsum-congruence -- the RESTATED support (theorem-library/finsum-additive.scm,
;;; 2026-09-17, the user's decision), copied literally through tf / tfin.
;;;
;;; The `=' conclusion with the POINTWISE typing of f as a SECOND antecedent.
;;; The equality half is finsum-congruence-q, which is unconditional and gives
;;; `=='; the pointwise typing is exactly what makes the LEFT sum DENOTE
;;; (finsum-type-ptwise), and `== plus definedness of one side' is `='.  So the
;;; proof is three lines: rewrite the right sum into the left with the
;;; quasi-equation, then `rfl' against the carrier membership.
(define rkj-cong-stmt
  (rkj-tf 'ag '(IS-ABELIAN-GROUP ag)
    (rkj-tfin 'S
      (list 'FORALL 'f (list 'FORALL 'g
        (list 'IMPLIES '(FORALL z (IMPLIES (IN z S) (= (f z) (g z))))
          (list 'IMPLIES '(FORALL z (IMPLIES (IN z S) (IN (f z) (CARR ag))))
                         '(= (FINSUM ag f S) (FINSUM ag g S)))))))))
(sp (make-wff rkj-cong-stmt))
(dk-peel!)
(let* ((gl (dk-goal)) (agv (cadr (cadr gl))) (fv (caddr (cadr gl)))
       (sv (cadddr (cadr gl))) (gv (caddr (caddr gl))))
  (dk-fact! 'finsum-congruence-q agv sv fv gv)
  (dk-fact! 'finsum-type-ptwise agv sv fv)
  (subst (list '== (list 'FINSUM agv gv sv) (list 'FINSUM agv fv sv)))
  (rfl))
(rkj-check! 'finsum-congruence)
(qed 'finsum-congruence)

;;; finsum-fubini-c MOVED 2026-09-17 to theorem-library/rake-finsum-fubini-c.scm: it cites
;;; finsum-fubini, which rake batch M PROVED in rake-finsum-core.scm, a file that loads
;;; AFTER this one; it now bills modulo 0 there.

;;; sum-ag-add-ind: the fold-length induction behind finsum-add-ag.
(define (rkj-ptwise-in v ag n)
  `(FORALL i_ (IMPLIES (IN i_ (ORD-SEGMENT ,n)) (IN (,v i_) (CARR ,ag)))))
(define rkj-add-ind-stmt
  (rkj-foralls '(n)
    (rkj-imps '(IN n NN)
      (rkj-foralls '(ag)
        (rkj-imps '(IS-ABELIAN-GROUP ag)
          (rkj-foralls '(ga_ gb_ gc_)
            (rkj-imps (rkj-ptwise-in 'ga_ 'ag 'n)
                      (rkj-ptwise-in 'gb_ 'ag 'n)
                      '(FORALL i_ (IMPLIES (IN i_ (ORD-SEGMENT n))
                                    (== (gc_ i_) ((OPR ag) (ga_ i_) (gb_ i_)))))
                      '(= (SUM-AG ag gc_ n)
                          ((OPR ag) (SUM-AG ag ga_ n) (SUM-AG ag gb_ n))))))))))

(sp (make-wff rkj-add-ind-stmt))
(let* ((leaves (dk-opened (lambda () (ni))))
       (base (rkj-leaf leaves (lambda (g) (not (dk-contains? g 'succ))) "induction base"))
       (step (rkj-leaf leaves (lambda (g) (dk-contains? g 'succ))       "induction step")))
  ;; ---- base ---------------------------------------------------------------
  (dk-focus! base)
  (dk-peel!)
  (let ((agv (cadr (rkj-pick-head 'IS-ABELIAN-GROUP "IS-ABELIAN-GROUP ag"))))
    (mac 'sum-ag-zero)
    (dk-fact! 'abelian-group-is-group agv)
    (dk-fact! 'group-identity-in agv)
    (dk-fact! 'group-left-id agv (list 'IDEN agv))
    (subst (list '= (rkj-o agv (list 'IDEN agv) (list 'IDEN agv)) (list 'IDEN agv)))
    (rfl))
  ;; ---- step ---------------------------------------------------------------
  (dk-focus! step)
  (dk-peel!)
  (let* ((nv  (rkj-nn-var))
         (gl  (dk-goal))
         (agv (cadr (cadr gl)))
         (gcv (caddr (cadr gl)))
         (rhs (caddr gl))
         (gav (caddr (cadr rhs)))
         (gbv (caddr (caddr rhs)))
         (segS (list 'ORD-SEGMENT (list 'succ nv)))
         (O   (lambda (x y) (rkj-o agv x y)))
         (typA (dk-pick (lambda (f) (rkj-guarded-forall-inner? f rkj-seg-dom?
                  (lambda (i) (and (pair? i) (eq? (car i) 'IN) (pair? (cadr i))
                                   (eq? (car (cadr i)) gav)))))
                        "the typing of ga_"))
         (typB (dk-pick (lambda (f) (rkj-guarded-forall-inner? f rkj-seg-dom?
                  (lambda (i) (and (pair? i) (eq? (car i) 'IN) (pair? (cadr i))
                                   (eq? (car (cadr i)) gbv)))))
                        "the typing of gb_"))
         (agree (dk-pick (lambda (f) (rkj-guarded-forall-inner? f rkj-seg-dom?
                  (lambda (i) (and (pair? i) (eq? (car i) '==)))))
                         "the pointwise hypothesis"))
         (ih  (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                        (not (rkj-guarded-forall? f rkj-seg-dom?))))
                       "the IH")))
    (display ";; rkj add-ind step vars: ") (display (list nv agv gav gbv gcv)) (newline)
    (have! (list 'IN nv segS) (lambda () (mac 'ord-segment-nn-succ) (oi-r) (rfl)))
    (dk-apply! typA nv)
    (dk-apply! typB nv)
    (dk-apply! agree nv)
    (rkj-restrict! typA nv (lambda (i) (list 'IN (list gav i) (list 'CARR agv))))
    (rkj-restrict! typB nv (lambda (i) (list 'IN (list gbv i) (list 'CARR agv))))
    (rkj-restrict! agree nv (lambda (i) (list '== (list gcv i)
                                              (O (list gav i) (list gbv i)))))
    (mac 'sum-ag-succ)
    (subst (list '== (list gcv nv) (O (list gav nv) (list gbv nv))))
    (dk-apply! ih agv gav gbv gcv)
    (subst (list '= (list 'SUM-AG agv gcv nv)
                    (O (list 'SUM-AG agv gav nv) (list 'SUM-AG agv gbv nv))))
    (dk-fact! 'sum-ag-type-ptwise nv agv gav)
    (dk-fact! 'sum-ag-type-ptwise nv agv gbv)
    (dk-fact! 'abelian-group-opr-interchange agv
              (list 'SUM-AG agv gav nv) (list 'SUM-AG agv gbv nv)
              (list gav nv) (list gbv nv))
    (ass)))
(rkj-check! 'sum-ag-add-ind)
(qed 'sum-ag-add-ind)
(topic! 'sum-ag-add-ind 'algebra)

;;; finsum-add-ag -- theorem-library/finsum-additive.scm:300, copied literally
;;; through the file's own tf / tfin builders.
(define rkj-add-ag-stmt
  (rkj-tf 'ag '(IS-ABELIAN-GROUP ag)
    (rkj-tfin 'S
      (rkj-tf 'f '(IN f (FUN S (CARR ag)))
        (rkj-tf 'h '(IN h (FUN S (CARR ag)))
          (list '=
            (list 'FINSUM 'ag (list 'VNB-LAMBDA 'z 'S (list '(OPR ag) '(f z) '(h z))) 'S)
            (list '(OPR ag) (list 'FINSUM 'ag 'f 'S) (list 'FINSUM 'ag 'h 'S))))))))

(sp (make-wff rkj-add-ag-stmt))
(dk-peel!)
(let* ((gl  (dk-goal))
       (lhs (cadr gl))
       (agv (cadr lhs)) (lam (caddr lhs)) (sv (cadddr lhs))
       (rhs (caddr gl))
       (fv  (caddr (cadr rhs))) (hv (caddr (caddr rhs)))
       (nc  (list 'CARD sv))
       (phi (list 'FIN-ENUM sv))
       (seg (list 'ORD-SEGMENT nc))
       (fam (lambda (u) (list 'ENUM-FAM agv u phi nc)))
       (O   (lambda (x y) (rkj-o agv x y))))
  (display ";; rkj add-ag vars: ") (display (list agv sv fv hv)) (newline)
  (mac 'FINSUM)
  (dk-fact! 'abelian-group-is-group agv)
  (let ((bij (dk-fact! 'fin-enum-is-bijection sv)))
    (mac-h 'bijection-membership-iff bij)
    (dk-split-all!))
  (dk-fact! 'enum-fam-in-fun nc agv sv phi fv)
  (dk-fact! 'enum-fam-in-fun nc agv sv phi hv)
  (rkj-ptwise-from-fun! (fam fv) nc agv)
  (rkj-ptwise-from-fun! (fam hv) nc agv)
  (have! (list 'FORALL 'i_ (list 'IMPLIES (list 'IN 'i_ seg)
           (list '== (list (fam lam) 'i_) (O (list (fam fv) 'i_) (list (fam hv) 'i_)))))
         (lambda ()
           (let* ((landed (dk-peel!))
                  (iv     (rkj-seg-var landed)))
             (dk-fact! 'ord-segment-nn-subset nc iv)
             (dk-fact! 'fun-apply-type-c phi seg sv iv)
             (dk-fact! 'enum-fam-value nc agv lam phi iv)
             (dk-fact! 'enum-fam-value nc agv fv  phi iv)
             (dk-fact! 'enum-fam-value nc agv hv  phi iv)
             (subst (list '== (list (fam lam) iv) (list lam (list phi iv))))
             (subst (list '== (list (fam fv) iv) (list fv (list phi iv))))
             (subst (list '== (list (fam hv) iv) (list hv (list phi iv))))
             (lam-b)
             (qrfl))))
  (dk-fact! 'sum-ag-add-ind nc agv (fam fv) (fam hv) (fam lam))
  (ass))
(rkj-check! 'finsum-add-ag)
(qed 'finsum-add-ag)

;;; ==================================================== two-point support
;;; x in OS(succ n) and not in OS(n)  =>  x = n.
(define (rkj-eq-n! xv nv)
  (have! (list '= xv nv)
         (lambda ()
           (let ((iffp (dk-fact! 'ord-segment-nn-succ nv xv)))
             (dk-only! iffp
                       (list 'IN xv (list 'ORD-SEGMENT (list 'succ nv)))
                       (list 'NOT (list 'IN xv (list 'ORD-SEGMENT nv))))
             (prop)))))

;;; x in OS(n)  =>  n /= x   (ord-segment-self).
(define (rkj-n-neq! nv xv)
  (have! (list 'NOT (list '= nv xv))
         (lambda ()
           (di)
           (have! (list 'AND (list '= nv xv) (list 'IN xv (list 'ORD-SEGMENT nv))))
           (dk-fact! 'eq-subst-membership nv xv (list 'ORD-SEGMENT nv))
           (ai (dk-fact! 'ord-segment-self nv)))))

(define rkj-two-ind-stmt
  (rkj-foralls '(n)
    (rkj-imps '(IN n NN)
      (rkj-foralls '(ag)
        (rkj-imps '(IS-ABELIAN-GROUP ag)
          (rkj-foralls '(g_ p_ q_)
            (rkj-imps '(IN p_ (ORD-SEGMENT n))
                      '(IN q_ (ORD-SEGMENT n))
                      '(NOT (= p_ q_))
                      '(IN (g_ p_) (CARR ag))
                      '(IN (g_ q_) (CARR ag))
                      '(FORALL i_ (IMPLIES (IN i_ (ORD-SEGMENT n))
                         (IMPLIES (NOT (= i_ p_))
                           (IMPLIES (NOT (= i_ q_)) (= (g_ i_) (IDEN ag))))))
                      '(= (SUM-AG ag g_ n) ((OPR ag) (g_ p_) (g_ q_))))))))))

(sp (make-wff rkj-two-ind-stmt))
(let* ((leaves (dk-opened (lambda () (ni))))
       (base (rkj-leaf leaves (lambda (g) (not (dk-contains? g 'succ))) "induction base"))
       (step (rkj-leaf leaves (lambda (g) (dk-contains? g 'succ))       "induction step")))
  ;; ---- base: ORD-SEGMENT(0) is empty ------------------------------------
  (dk-focus! base)
  (dk-peel!)
  (let ((pv (cadr (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                            (equal? (caddr f) '(ORD-SEGMENT 0))))
                           "p_ in ORD-SEGMENT(0)"))))
    (fact 'ord-segment-zero-no-members pv)
    (ai (list 'NOT (list 'IN pv '(ORD-SEGMENT 0)))))
  ;; ---- step --------------------------------------------------------------
  (dk-focus! step)
  (dk-peel!)
  (let* ((nv  (rkj-nn-var))
         (gl  (dk-goal))
         (agv (cadr (cadr gl)))
         (gv  (caddr (cadr gl)))
         (pv  (cadr (cadr (caddr gl))))
         (qv  (cadr (caddr (caddr gl))))
         (segN (list 'ORD-SEGMENT nv))
         (segS (list 'ORD-SEGMENT (list 'succ nv)))
         (O   (lambda (x y) (rkj-o agv x y)))
         (agree (dk-pick (lambda (f) (rkj-guarded-forall-inner? f rkj-seg-dom?
                  (lambda (i) (and (pair? i) (eq? (car i) 'IMPLIES)))))
                         "the agreement hypothesis"))
         (ih  (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                        (not (rkj-guarded-forall? f rkj-seg-dom?))))
                       "the IH"))
         ;; the single-support agreement of X on OS(n), given the OTHER index YV
         ;; is n (hence outside OS(n)): i /= x and i in OS(n) already give i /= n.
         (single-agree!
          (lambda (xv yv)
            (have! (list 'FORALL 'i_
                     (list 'IMPLIES (list 'IN 'i_ segN)
                       (list 'IMPLIES (list 'NOT (list '= 'i_ xv))
                         (list '= (list gv 'i_) (list 'IDEN agv)))))
                   (lambda ()
                     (let* ((landed (dk-peel!))
                            (iv     (rkj-seg-var landed)))
                       (have! (list 'IN iv segS)
                              (lambda () (mac 'ord-segment-nn-succ) (oi-l) (ass)))
                       (have! (list 'NOT (list '= iv yv))
                              (lambda ()
                                (di)                       ; assume (= i_ yv)
                                (dk-fact! 'eq-trans iv yv nv)
                                (dk-fact! 'equality-symmetry iv nv)
                                (have! (list 'AND (list '= nv iv)
                                             (list 'IN iv segN)))
                                (dk-fact! 'eq-subst-membership nv iv segN)
                                (ai (dk-fact! 'ord-segment-self nv))))
                       (dk-apply! agree iv)
                       (ass)))))))
    (display ";; rkj two-ind step: ") (display (list nv agv gv pv qv)) (newline)
    (mac 'sum-ag-succ)
    (dk-fact! 'abelian-group-is-group agv)
    (dk-fact! 'group-identity-in agv)
    (dk-fact! 'group-carrier-closed-opr agv (list gv pv) (list gv qv))
    (have! (list 'IN nv segS)
           (lambda () (mac 'ord-segment-nn-succ) (oi-r) (rfl)))
    (use-em (list 'IN pv segN)
      ;; ======== p_ below n ==================================================
      (lambda ()
        (use-em (list 'IN qv segN)
          ;; ---- both below n: the top summand vanishes, the rest is the IH --
          (lambda ()
            (rkj-n-neq! nv pv)
            (rkj-n-neq! nv qv)
            (dk-apply! agree nv)                     ; (= (g_ n) (IDEN ag))
            (subst (list '= (list gv nv) (list 'IDEN agv)))
            (have! (list 'FORALL 'i_
                     (list 'IMPLIES (list 'IN 'i_ segN)
                       (list 'IMPLIES (list 'NOT (list '= 'i_ pv))
                         (list 'IMPLIES (list 'NOT (list '= 'i_ qv))
                           (list '= (list gv 'i_) (list 'IDEN agv))))))
                   (lambda ()
                     (let* ((landed (dk-peel!))
                            (iv     (rkj-seg-var landed)))
                       (have! (list 'IN iv segS)
                              (lambda () (mac 'ord-segment-nn-succ) (oi-l) (ass)))
                       (dk-apply! agree iv)
                       (ass))))
            (dk-apply! ih agv gv pv qv)
            (subst (list '= (list 'SUM-AG agv gv nv) (O (list gv pv) (list gv qv))))
            (dk-fact! 'abelian-group-opr-comm agv (O (list gv pv) (list gv qv))
                      (list 'IDEN agv))
            (subst (list '= (O (O (list gv pv) (list gv qv)) (list 'IDEN agv))
                            (O (list 'IDEN agv) (O (list gv pv) (list gv qv)))))
            (dk-fact! 'group-left-id agv (O (list gv pv) (list gv qv)))
            (ass))
          ;; ---- q_ = n: single support at p_ -------------------------------
          (lambda ()
            (rkj-eq-n! qv nv)
            (single-agree! pv qv)
            (dk-fact! 'sum-ag-single-ind nv agv gv pv)
            (subst (list '= (list 'SUM-AG agv gv nv) (list gv pv)))
            (subst (list '= nv qv))
            (rfl))))
      ;; ======== p_ = n =====================================================
      (lambda ()
        (rkj-eq-n! pv nv)
        (use-em (list 'IN qv segN)
          ;; ---- q_ below n: single support at q_ ---------------------------
          (lambda ()
            (single-agree! qv pv)
            (dk-fact! 'sum-ag-single-ind nv agv gv qv)
            (subst (list '= (list 'SUM-AG agv gv nv) (list gv qv)))
            (subst (list '= nv pv))
            (dk-fact! 'abelian-group-opr-comm agv (list gv qv) (list gv pv))
            (ass))
          ;; ---- q_ = n too: p_ = q_, against the hypothesis ----------------
          (lambda ()
            (rkj-eq-n! qv nv)
            (dk-fact! 'equality-symmetry qv nv)
            (dk-fact! 'eq-trans pv nv qv)
            (ai (list 'NOT (list '= pv qv)))))))))
(rkj-check! 'sum-ag-two-support-ind)
(qed 'sum-ag-two-support-ind)
(topic! 'sum-ag-two-support-ind 'algebra)

;;; finsum-two-support -- structure-library/matrix.scm:381, copied literally.
(define rkj-two-stmt
  '(FORALL ag (IMPLIES (IS-ABELIAN-GROUP ag)
     (FORALL S (IMPLIES (IN S SET) (IMPLIES (IN (CARD S) NN)
     (FORALL f (IMPLIES (IN f (FUN S (CARR ag)))
     (FORALL i0 (IMPLIES (IN i0 S)
     (FORALL i1 (IMPLIES (IN i1 S)
     (IMPLIES (NOT (= i0 i1))
       (IMPLIES (FORALL j (IMPLIES (IN j S)
                  (IMPLIES (NOT (= j i0)) (IMPLIES (NOT (= j i1)) (= (f j) (IDEN ag))))))
         (= (FINSUM ag f S) ((OPR ag) (f i0) (f i1))))))))))))))))
)

(sp (make-wff rkj-two-stmt))
(dk-peel!)
(let* ((gl  (dk-goal))
       (agv (cadr (cadr gl)))
       (fv  (caddr (cadr gl)))
       (sv  (cadddr (cadr gl)))
       (i0v (cadr (cadr (caddr gl))))
       (i1v (cadr (caddr (caddr gl))))
       (nc  (list 'CARD sv))
       (phi (list 'FIN-ENUM sv))
       (seg (list 'ORD-SEGMENT nc))
       (ca  (list 'CARR agv))
       (fam (list 'ENUM-FAM agv fv phi nc))
       (O   (lambda (x y) (rkj-o agv x y)))
       (agree (dk-pick (lambda (f) (rkj-guarded-forall-inner? f sv
                (lambda (i) (and (pair? i) (eq? (car i) 'IMPLIES)))))
                       "forall j in S. j/=i0 => j/=i1 => f j = IDEN")))
  (display ";; rkj two vars: ") (display (list agv sv fv i0v i1v)) (newline)
  (mac 'FINSUM)
  (dk-fact! 'abelian-group-is-group agv)
  (dk-fact! 'group-identity-in agv)
  (dk-fact! 'fun-apply-type-c fv sv ca i0v)
  (dk-fact! 'fun-apply-type-c fv sv ca i1v)
  (let ((bij (dk-fact! 'fin-enum-is-bijection sv)))
    (mac-h 'bijection-membership-iff bij)
    (dk-split-all!))
  (let* ((inj  (dk-pick (lambda (f) (rkj-guarded-forall-inner? f
                          (lambda (d) (equal? d seg))
                          (lambda (i) (and (pair? i) (eq? (car i) 'FORALL)))))
                        "injectivity of FIN-ENUM(S)"))
         (surj (dk-pick (lambda (f) (rkj-guarded-forall-inner? f sv
                          (lambda (i) (and (pair? i) (eq? (car i) 'FORSOME)))))
                        "surjectivity of FIN-ENUM(S)"))
         (pv   (dk-skolem! (dk-apply! surj i0v)))
         (qv   (dk-skolem! (dk-apply! surj i1v))))
    (dk-fact! 'ord-segment-nn-subset nc pv)
    (dk-fact! 'ord-segment-nn-subset nc qv)
    (dk-fact! 'fun-apply-type-c phi seg sv pv)
    (dk-fact! 'fun-apply-type-c phi seg sv qv)
    (dk-fact! 'enum-fam-value nc agv fv phi pv)
    (dk-fact! 'enum-fam-value nc agv fv phi qv)
    ;; the family at p and q IS f(i0), f(i1)
    (have! (list '== (list fam pv) (list fv i0v))
           (lambda ()
             (subst (list '== (list fam pv) (list fv (list phi pv))))
             (subst (list '= (list phi pv) i0v))
             (qrfl)))
    (have! (list '== (list fam qv) (list fv i1v))
           (lambda ()
             (subst (list '== (list fam qv) (list fv (list phi qv))))
             (subst (list '= (list phi qv) i1v))
             (qrfl)))
    (have! (list 'IN (list fam pv) ca)
           (lambda () (subst (list '== (list fam pv) (list fv i0v))) (ass)))
    (have! (list 'IN (list fam qv) ca)
           (lambda () (subst (list '== (list fam qv) (list fv i1v))) (ass)))
    ;; p /= q, because phi is injective and i0 /= i1
    (have! (list 'NOT (list '= pv qv))
           (lambda ()
             (di)                                   ; assume (= p q)
             (have! (list '= i0v i1v)
                    (lambda ()
                      (subst (list '= i0v (list phi pv)))
                      (subst (list '= i1v (list phi qv)))
                      (subst (list '= pv qv))
                      (rfl)))
             (ai (list 'NOT (list '= i0v i1v)))))
    ;; the family vanishes off {p, q}
    (have! (list 'FORALL 'i_
             (list 'IMPLIES (list 'IN 'i_ seg)
               (list 'IMPLIES (list 'NOT (list '= 'i_ pv))
                 (list 'IMPLIES (list 'NOT (list '= 'i_ qv))
                   (list '= (list fam 'i_) (list 'IDEN agv))))))
           (lambda ()
             (let* ((landed (dk-peel!))
                    (iv     (rkj-seg-var landed)))
               (dk-fact! 'ord-segment-nn-subset nc iv)
               (dk-fact! 'fun-apply-type-c phi seg sv iv)
               (dk-fact! 'enum-fam-value nc agv fv phi iv)
               (have! (list 'NOT (list '= (list phi iv) i0v))
                      (lambda ()
                        (di)
                        (dk-fact! 'equality-symmetry (list phi pv) i0v)
                        (dk-fact! 'eq-trans (list phi iv) i0v (list phi pv))
                        (dk-apply! inj iv pv)
                        (ai (list 'NOT (list '= iv pv)))))
               (have! (list 'NOT (list '= (list phi iv) i1v))
                      (lambda ()
                        (di)
                        (dk-fact! 'equality-symmetry (list phi qv) i1v)
                        (dk-fact! 'eq-trans (list phi iv) i1v (list phi qv))
                        (dk-apply! inj iv qv)
                        (ai (list 'NOT (list '= iv qv)))))
               (dk-apply! agree (list phi iv))
               (subst (list '== (list fam iv) (list fv (list phi iv))))
               (ass))))
    (dk-fact! 'sum-ag-two-support-ind nc agv fam pv qv)
    (subst (list '== (list fv i0v) (list fam pv)))
    (subst (list '== (list fv i1v) (list fam qv)))
    (ass)))
(rkj-check! 'finsum-two-support)
(qed 'finsum-two-support)
