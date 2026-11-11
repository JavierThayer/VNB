;;; tvs-single-bound.scm -- wave of 2026-11-09/10 (agent BA-OT1), wired 2026-11-10 from scratchpad/baot1-1109/tvs-single-bound.scm.
;;; Library: analysis.

;;; tvs-single-bound.scm -- continuity of a linear map between two seminorm topologies from ONE
;;; seminorm bound per target seminorm: for each q_j there are an index i and c >= 0 with
;;; q_j(T x) <= c p_i(x).  The shape every argument of Thayer, Banach Algebras ch. 5 uses
;;; (Prop 5.11's proof: "the seminorm continuity condition for linear maps").  A corollary of
;;; sn-cont-of-bound (tvs-continuity.scm) with the finite set {i} and the constant c + 1.
;;; Agent BA-OT1, 2026-11-10.  DESTINATION: theorem-library/, after tvs-continuity.scm.
;;; Library: analysis.  Helper prefix: tsb-.

(define (tsb-done?) (sequent-node-grounded? (proof-state-focus *ps*)))
(define (tsb-qed! name)
  (if (not (proof-done? *ps*))
      (begin
        (display "\n*** tvs-single-bound: ") (display name) (display " did NOT close.\n")
        (for-each (lambda (l) (display "   GOAL: ") (display (expression->string (dk-goal-of l))) (newline))
                  (dk-open-leaves))))
  (qed name)
  (topic! name 'analysis))

;;; ---------------------------------------------------------------------------------------------
;;; ;;; THE SINGLE-SEMINORM BOUND
(define tsb-fam1 '(IS-SEMINORM-FAMILY-ON fld m1 ix1 pf1))
(define tsb-fam2 '(IS-SEMINORM-FAMILY-ON fld m2 ix2 pf2))
(define tsb-lin '(IS-LINEAR-MAP m1 m2 tt))
(define tsb-hom '(IS-HOM-TOP-SPACE (SEMINORM-TOP m1 ix1 pf1) (SEMINORM-TOP m2 ix2 pf2) tt))
(define tsb-sbh
  '(FORALL otj_ (IMPLIES (IN otj_ ix2)
     (FORSOME oti_ (AND (IN oti_ ix1)
       (FORSOME otc_ (AND (IN otc_ RR) (AND (<= 0 otc_)
         (FORALL otx_ (IMPLIES (IN otx_ (VEC m1))
           (<= ((pf2 otj_) (tt otx_)) (* otc_ ((pf1 oti_) otx_)))))))))))))

;;; {j} as a finite subset of ix (tbc-single!, tvs-continuity.scm)
(define (tsb-single! j ix)
  (let ((pp (list 'PAIR j j)))
    (dk-cite! 'membership-implies-sethood j ix)
    (dk-have! (list 'AND (list 'IN j 'SET) (list 'IN j 'SET)))
    (dk-cite! 'pairing j j)
    (dk-cite! 'card-singleton j)
    (dk-cite! 'nn-zero-in)
    (dk-cite! 'nn-succ-closed 0)
    (dk-have! (list 'IN (list 'CARD pp) 'NN) (lambda () (subst (list '= (list 'CARD pp) '(succ 0))) (ass)))
    (dk-have! (list 'SUBSET pp ix)
      (lambda ()
        (mac 'subset-def)
        (let ((w (dk-di-var!)))
          (dk-cite! 'pair-self-eq j w)
          (subst (list '= w j))
          (ass))))
    (dk-cite! 'pair-self-member j)
    pp))

(define (tsb-rename-h! f prs)
  (fold-left (lambda (f pr) (if (dk-contains? f (car pr)) (dk-rewrite-h! f (car pr) (cdr pr)) f)) f prs))

(sp (make-wff (forall-guarded '(fld m1 ix1 pf1 m2 ix2 pf2 tt) (list tsb-fam1 tsb-fam2 tsb-lin tsb-sbh) tsb-hom)))
(dk-peel!)
(dk-have! '(IN pf1 (FUN ix1 (FUN (VEC m1) RR)))
  (lambda () (mac-h 'IS-SEMINORM-FAMILY-ON tsb-fam1) (dk-split-all!) (ass)))
(dk-have! '(IN pf2 (FUN ix2 (FUN (VEC m2) RR)))
  (lambda () (mac-h 'IS-SEMINORM-FAMILY-ON tsb-fam2) (dk-split-all!) (ass)))
(dk-have! '(IN tt (FUN (VEC m1) (VEC m2)))
  (lambda () (mac-h 'IS-LINEAR-MAP tsb-lin) (dk-split-all!) (ass)))
(dk-cite! 'sn-cont-of-bound 'fld 'm1 'ix1 'pf1 'm2 'ix2 'pf2 'tt)
(let* ((imp (dk-pick (lambda (f) (and (dk-head-is? f 'IMPLIES) (equal? (caddr f) tsb-hom) (dk-head-is? (cadr f) 'FORALL)))
                     "the bound implication"))
       (allb (cadr imp)))
  (dk-have! allb
    (lambda ()
      (let* ((j  (dk-di-var!))
             (hj (dk-apply! tsb-sbh j))
             (i  (dk-skolem! hj))
             (c  (dk-skolem! (dk-pick (lambda (f) (and (dk-head-is? f 'FORSOME) (dk-contains? f i))) "the constant")))
             (bd (dk-pick (lambda (f) (and (dk-head-is? f 'FORALL) (dk-contains? f c))) "the bound"))
             (pp (tsb-single! i 'ix1))
             (cb (list '+ c 1)))
        (dk-cite! 'rr-one-in)
        (dk-have! (list 'AND (list 'IN c 'RR) '(IN 1 RR)))
        (dk-cite! 'rr-add-closed c 1)
        (dk-have! (list '< 0 cb) (lambda () (dk-ineq! (list '<= 0 c) (list 'IN c 'RR))))
        (dk-cite! 'rr-pos-rr-of-lt cb)
        (dk-cite! 'fun-apply-type-c 'pf1 'ix1 '(FUN (VEC m1) RR) i)
        (dk-cite! 'fun-apply-type-c 'pf2 'ix2 '(FUN (VEC m2) RR) j)
        (ew pp)
        (dk-conj-close!
          (lambda ()
            (cond
              ((tsb-done?) #t)
              ((dk-asm? (dk-goal)) (ass))
              (#t
               (ew cb)
               (dk-conj-close!
                 (lambda ()
                   (cond
                     ((tsb-done?) #t)
                     ((dk-asm? (dk-goal)) (ass))
                     (#t
                      (dk-peel!)
                      (let* ((g (dk-goal)) (tx (cadr (cadr g))) (x (cadr tx)) (t (caddr (caddr g)))
                             (p (list (list 'pf1 i) x)) (q (list (list 'pf2 j) tx))
                             (hall (dk-pick (lambda (f) (and (dk-head-is? f 'FORALL) (dk-contains? f pp) (dk-contains? f x)))
                                            "the hypothesis on {i}")))
                        (dk-apply! hall i)
                        (dk-apply! bd x)
                        (dk-cite! 'fun-apply-type-c (list 'pf1 i) '(VEC m1) 'RR x)
                        (dk-cite! 'fun-apply-type-c 'tt '(VEC m1) '(VEC m2) x)
                        (dk-cite! 'fun-apply-type-c (list 'pf2 j) '(VEC m2) 'RR tx)
                        (dk-cite! 'rr-mul-le-right p t c)
                        (dk-have! (list 'AND (list 'IN c 'RR) (list 'IN p 'RR)))
                        (dk-cite! 'rr-mul-comm c p)
                        (dk-have! (list '= (list '* cb t) (list '+ (list '* t c) t)) (lambda () (crs)))
                        (for-each dk-real! (list (list '* c p) (list '* p c) (list '* t c) (list '* cb t)))
                        (let* ((n1 (dk-name! (list '* c p)))
                               (n2 (dk-name! (list '* p c)))
                               (n3 (dk-name! (list '* t c)))
                               (n4 (dk-name! (list '* cb t)))
                               (prs (list (cons (list '* c p) n1) (cons (list '* p c) n2)
                                          (cons (list '* t c) n3) (cons (list '* cb t) n4))))
                          (subst (list '= (list '* cb t) n4))
                          (apply dk-ineq!
                                 (append (map (lambda (f) (tsb-rename-h! f prs))
                                              (list (list '<= q (list '* c p))
                                                    (list '= (list '* c p) (list '* p c))
                                                    (list '<= (list '* p c) (list '* t c))
                                                    (list '= (list '* cb t) (list '+ (list '* t c) t))))
                                         (list (list '<= 0 t) (list 'IN q 'RR) (list 'IN t 'RR)
                                               (list 'IN n1 'RR) (list 'IN n2 'RR) (list 'IN n3 'RR) (list 'IN n4 'RR)))))))))))))))))
  (detach! imp)
  (if (not (tsb-done?)) (ass)))
(tsb-qed! 'sn-cont-of-single-bound)

