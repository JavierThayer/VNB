;;; matact-row-linear-proof.scm -- the coefficient row acts LINEARLY.
;;;
;;;   lincomb-unfold    LINCOMB(md,n,c,u) == sum_j c_{1j} . u_{j1}  [the definition]
;;;   lincomb-type      LINCOMB(md,n,c,u) in VEC md
;;;   matact-lincomb    1 <= n  =>  ENTRY(MATACT md c u, 1, 1) = LINCOMB(md,n,c,u)
;;;   lincomb-row-add   (c1 + c2) . u  =  c1.u + c2.u        [row addition]
;;;   lincomb-row-scale (r * c)  . u  =  r . (c.u)           [row scaling]
;;;
;;; where c, c1, c2 are coefficient ROWS in MAT(1,n,CARR(SCAL md)), r is a
;;; scalar, u is a sequence in MAT(n,1,VEC md), row addition and scaling are the
;;; entrywise MATADD / MATSCALE over the scalar ring, and `c . u' abbreviates
;;; LINCOMB(md, n, c, u) = sum_j c_{1j} . u_{j1} (structure-library/mod-seq.scm).
;;;
;;; RENAMED 2026-09-16: lincomb-row-add / lincomb-row-scale were matact-row-add /
;;; matact-row-scale, stated with (ENTRY (MATACT md c u) 1 1).  That entry is not
;;; the linear combination when n = 0 (MATACT reads its column count off
;;; SIZE([]) = [0, 0]); LINCOMB is, for every n.  The proofs are unchanged except
;;; that the FINSUM is reached by lincomb-unfold instead of matact-entry, which
;;; is what removes the `1 <= n' matact-entry now owes.  matact-lincomb is the
;;; bridge for the n >= 1 users of MATACT (mod-basis, rank-bound, spans-transport).
;;;
;;; BRICKS 1 and 2 of the six under `spans-submodule-fg' (submodule-free.scm).
;;; Together they say the coefficient row acts LINEARLY, and they are what makes
;;; SPAN(md,n,u) a submodule (closed under VADD by brick 1, under ACT by brick 2)
;;; and what makes the last-coefficient set S an IDEAL of the scalar ring
;;; (closed under + by brick 1, under ring multiples by brick 2).
;;;
;;; The argument is one line of mathematics and three of plumbing:
;;;   (c1+c2).u = sum_j ((c1)_{1j} + (c2)_{1j}) . u_{j1}        [lincomb-unfold]
;;;             = sum_j ( (c1)_{1j}.u_{j1}  +  (c2)_{1j}.u_{j1} )
;;;                                                   [module-act-distrib-scalar]
;;;             = sum_j (c1)_{1j}.u_{j1} + sum_j (c2)_{1j}.u_{j1}  [finsum-add-ag]
;;;             = c1.u + c2.u                                   [lincomb-unfold x2]
;;; The middle rewrite is under the summand, so it goes through finsum-congruence
;;; with a cut proving pointwise equality -- the idiom of matact-assoc-proof.scm.
;;;
;;; This is the FIRST consumer of finsum-add-ag (theorem-library/finsum-additive).
;;;
;;; Needs: mod-seq (LINCOMB, MATACT, matact-entry, matact-summand-type, mvag-carr/op),
;;; matrix.scm (MATADD, matadd-type, entry-of-matof, entry-in-carrier),
;;; module.scm (module-scalar-ring, module-act-type, module-act-distrib-scalar),
;;; finsum-additive (finsum-congruence, finsum-add-ag), views (MODULE-VECTOR-AG).
;;; RETIRED 2026-09-14 (proven): mra-combined-summand-type -- theorem-library/lam-fun-bricks.scm (dk-lam-fun!)
;;; RETIRED 2026-09-14 (proven): mrs-scaled-summand-type -- theorem-library/lam-fun-bricks.scm (dk-lam-fun!)

;;; ===================================================================
;;; lincomb-unfold -- the def-functoid's unfold, as a citable equation
;;; (`mac-h' cannot unfold a functoid by its own name; see CLAUDE.md).
;;; ===================================================================
(define lcu-sum
  '(FINSUM (MODULE-VECTOR-AG md)
           (VNB-LAMBDA j (INTERVAL 1 n) ((ACT md) (ENTRY c 1 j) (ENTRY u j 1)))
           (INTERVAL 1 n)))
(sp (make-wff
  (list 'FORALL 'md (list 'FORALL 'n (list 'FORALL 'c (list 'FORALL 'u
    (list '== '(LINCOMB md n c u) lcu-sum)))))))
(dk-peel!)
(mac 'LINCOMB)
(qrfl)
(qed 'lincomb-unfold)
(topic! 'lincomb-unfold 'plumbing)

;;; ===================================================================
;;; lincomb-type -- a linear combination is a vector.
;;; ===================================================================
(sp (make-wff
  '(FORALL md (IMPLIES (IS-MODULE md)
     (FORALL n (FORALL c (FORALL u
       (IMPLIES (IN c (MAT 1 n (CARR (SCAL md))))
       (IMPLIES (IN u (MAT n 1 (VEC md)))
         (IN (LINCOMB md n c u) (VEC md)))))))))))
(dk-peel!)
(fact 'module-vector-ag-is-abelian-group 'md)
(fact 'one-in-interval-1)
(fact 'mat-rows-in-nn 'n 1 '(VEC md) 'u)
(fact 'interval-in-set 1 'n)
(fact 'interval-card-in-nn 1 'n)
(fact 'matact-summand-type 'md 1 'n 1 'c 'u 1 1)
(fact 'finsum-type '(MODULE-VECTOR-AG md) '(INTERVAL 1 n) (caddr lcu-sum))
(mac-h 'mvag-carr (list 'IN lcu-sum '(CARR (MODULE-VECTOR-AG md))))
(fact 'lincomb-unfold 'md 'n 'c 'u)
(subst (list '== '(LINCOMB md n c u) lcu-sum))
(ass)
(qed 'lincomb-type)
(topic! 'lincomb-type 'algebra)

;;; ===================================================================
;;; matact-lincomb -- for n >= 1 the (1,1) entry of the 1-by-1 product c.u IS
;;; the linear combination.  (At n = 0 it is not: see LINCOMB in mod-seq.scm.)
;;; ===================================================================
(sp (make-wff
  '(FORALL md (IMPLIES (IS-MODULE md)
     (FORALL n (FORALL c (FORALL u
       (IMPLIES (IN c (MAT 1 n (CARR (SCAL md))))
       (IMPLIES (IN u (MAT n 1 (VEC md)))
       (IMPLIES (<= 1 n)
         (= (ENTRY (MATACT md c u) 1 1) (LINCOMB md n c u))))))))))))
(dk-peel!)
(fact 'one-in-interval-1)
(fact 'matact-entry 'md 1 'n 1 'c 'u 1 1)
(fact 'lincomb-unfold 'md 'n 'c 'u)
(subst (list '== '(LINCOMB md n c u) lcu-sum))
(ass)
(qed 'matact-lincomb)
(topic! 'matact-lincomb 'algebra)

;;; ---- driver helpers (mra- prefix)
(define (mra-goal) (wff-formula (sequent-node-assertion (proof-state-focus *ps*))))
(define (mra-foc! n) (dk-focus! n))
(define (mra-foc-goal! g)                ; ERRORS on a miss, by design
  (let loop ((ls (proof-leaves)))
    (cond ((null? ls) (error "mra-foc-goal!: no open leaf with goal" g))
          ((equal? (wff-formula (sequent-node-assertion (car ls))) g)
           (mra-foc! (car ls)) (car ls))
          (else (loop (cdr ls))))))
(define (mra-di*)
  (let lp () (let* ((g (mra-goal)) (h (and (pair? g) (car g))))
               (when (memq h '(FORALL IMPLIES)) (di) (lp)))))
;; cut P; prove the P-subgoal, then continue on the main branch (mb-with-cut of
;; mod-basis-proof.scm, inlined -- this file loads before it).
(define (mra-with-cut p prove-sub prove-cont)
  (let ((before (proof-leaves)))
    (cut p)
    (let* ((new (filter (lambda (l) (not (memq l before))) (proof-leaves)))
           (sub (car (filter (lambda (l) (equal? (wff-formula (sequent-node-assertion l)) p))
                             new)))
           (cont (car (filter (lambda (l) (not (eq? l sub))) new))))
      (mra-foc! sub) (prove-sub)
      (mra-foc! cont) (prove-cont))))

;;; ---- the shape
(define mra-vag '(MODULE-VECTOR-AG md))
(define mra-vc  '(CARR (MODULE-VECTOR-AG md)))
(define mra-sc  '(CARR (SCAL md)))
(define mra-ivl '(INTERVAL 1 n))
(define mra-cs  '(MATADD (SCAL md) c1 c2))          ; the summed row
(define (mra-row c) (list 'VNB-LAMBDA 'j mra-ivl (list '(ACT md) (list 'ENTRY c 1 'j) '(ENTRY u j 1))))
(define mra-f (mra-row 'c1))                        ; j |-> c1_{1j} . u_{j1}
(define mra-h (mra-row 'c2))                        ; j |-> c2_{1j} . u_{j1}
(define mra-l (mra-row mra-cs))                     ; j |-> (c1+c2)_{1j} . u_{j1}
(define mra-g (list 'VNB-LAMBDA 'z mra-ivl                  ; j |-> f(j) (+) h(j)
                    (list '(OPR (MODULE-VECTOR-AG md))
                          (list mra-f 'z) (list mra-h 'z))))
(define (mra-sum f) (list 'FINSUM mra-vag f mra-ivl))

;;; The combined summand j |-> f(j) (+) h(j) is a function [1,n] -> VEC md.
;;; matact-summand-type covers f and h separately; their pointwise VADD needs the
;;; abelian group's closure.  Same read-off, warranted the same way.
(define mra-prems
  '((IN c1 (MAT 1 n (CARR (SCAL md)))) (IN c2 (MAT 1 n (CARR (SCAL md))))
    (IN u (MAT n 1 (VEC md)))))
(define (mra-wf vs body) (if (null? vs) body (list 'FORALL (car vs) (mra-wf (cdr vs) body))))
(define (mra-wi ps body) (if (null? ps) body (list 'IMPLIES (car ps) (mra-wi (cdr ps) body))))


;;; (No support is needed for the summand j |-> (c1+c2)_{1j} . u_{j1}: it is
;;; matact-summand-type at P := MATADD(SCAL md, c1, c2), whose MAT-typing
;;; matadd-type has already put in context.  `fact' instantiates P at a compound
;;; matrix term as happily as at a variable.)

;;; ===================================================================
(sp (make-wff
  (mra-wf '(md) (mra-wi '((IS-MODULE md))
    (mra-wf '(n c1 c2 u) (mra-wi mra-prems
      (list '= (list 'LINCOMB 'md 'n mra-cs 'u)
               (list '(VADD md)
                     '(LINCOMB md n c1 u)
                     '(LINCOMB md n c2 u)))))))))
(mra-di*)

;;; ---- coercions and typings
(fact 'module-scalar-ring 'md)                       ; IS-RING (SCAL md)
(fact 'module-vector-ag-is-abelian-group 'md)
(fact 'matadd-type '(SCAL md) 1 'n 'c1 'c2)          ; c1+c2 is a 1-by-n row
(fact 'one-in-interval-1)                            ; 1 in [1,1]
(fact 'interval-in-set 1 'n)
;; interval-card-in-nn's guard: n is the row count of the column u : MAT n 1.
(fact 'mat-rows-in-nn 'n 1 '(VEC md) 'u)
(fact 'interval-card-in-nn 1 'n)
(fact 'mra-combined-summand-type 'md 'n 'c1 'c2 'u)
(fact 'matact-summand-type 'md 1 'n 1 mra-cs 'u 1 1) ; L is a function
(fact 'matact-summand-type 'md 1 'n 1 'c1 'u 1 1)    ; f is a function
(fact 'matact-summand-type 'md 1 'n 1 'c2 'u 1 1)    ; h is a function

;;; ---- unfold all three linear combinations into FINSUMs
(fact 'lincomb-unfold 'md 'n mra-cs 'u)
(fact 'lincomb-unfold 'md 'n 'c1 'u)
(fact 'lincomb-unfold 'md 'n 'c2 'u)
(subst (list '== (list 'LINCOMB 'md 'n mra-cs 'u) (mra-sum mra-l)))
(subst (list '== '(LINCOMB md n c1 u) (mra-sum mra-f)))
(subst (list '== '(LINCOMB md n c2 u) (mra-sum mra-h)))

;;; Goal is now   SUM_j L(j)  =  (SUM_j F(j)) (VADD md) (SUM_j H(j)),
;;; while finsum-add-ag speaks the abelian group's (OPR VAG).
;;;
;;; `subst' CANNOT bridge the two.  Its Leibniz walk rewrites subterms in
;;; ARGUMENT position, and here (VADD md) sits in OPERATOR position -- the goal
;;; is ((VADD md) x y), whose car is the term to replace.  mvag-op is an
;;; unconditional equation, hence a rewrite MACETE, and macetes rewrite the term
;;; structure including operators.  So: `mac'/`mac-h', never `subst'.

;;; ---- the summand rewrite:  L(j) = F(j) (+) H(j)  pointwise
(mra-with-cut
  (list 'FORALL 'w (list 'IMPLIES (list 'IN 'w mra-ivl)
                         (list '= (list mra-l 'w) (list mra-g 'w))))
  (lambda ()
    (di)                                             ; peel w, absorb its bound
    (let ((wv (cadr (cadr (mra-goal)))))             ; goal (= (L w) (G w))
      ;; Both sides are lambda applications, and G's are NESTED ((f z) inside the
      ;; group operation), so one beta is not enough.  lam-b is a no-op warning
      ;; once there is no redex left.
      (lam-b) (lam-b) (lam-b) (lam-b)
      (fact 'entry-in-carrier 1 'n mra-sc 'c1 1 wv)
      (fact 'entry-in-carrier 1 'n mra-sc 'c2 1 wv)
      (fact 'entry-in-carrier 'n 1 '(VEC md) 'u wv 1)
      ;; (c1+c2)_{1w} = c1_{1w} + c2_{1w}
      (fact 'matadd-entry '(SCAL md) 1 'n 'c1 'c2 1 wv)
      (subst (list '= (list 'ENTRY mra-cs 1 wv)
                   (list '(ADD (SCAL md)) (list 'ENTRY 'c1 1 wv) (list 'ENTRY 'c2 1 wv))))
      ;; (r+s).x = r.x + s.x
      (fact 'module-act-distrib-scalar 'md
            (list 'ENTRY 'c1 1 wv) (list 'ENTRY 'c2 1 wv) (list 'ENTRY 'u wv 1))
      (subst (list '= (list '(ACT md) (list '(ADD (SCAL md)) (list 'ENTRY 'c1 1 wv)
                                            (list 'ENTRY 'c2 1 wv))
                            (list 'ENTRY 'u wv 1))
                   (list '(VADD md)
                         (list '(ACT md) (list 'ENTRY 'c1 1 wv) (list 'ENTRY 'u wv 1))
                         (list '(ACT md) (list 'ENTRY 'c2 1 wv) (list 'ENTRY 'u wv 1)))))
      ;; goal: (VADD md)(A,B) = (OPR VAG)(A,B).  Rewrite the OPERATOR.
      (mac 'mvag-op)
      ;; rfl needs the term defined: type both actions and their sum
      (fact 'module-act-type 'md (list 'ENTRY 'c1 1 wv) (list 'ENTRY 'u wv 1))
      (fact 'module-act-type 'md (list 'ENTRY 'c2 1 wv) (list 'ENTRY 'u wv 1))
      (fact 'module-vadd-type 'md
            (list '(ACT md) (list 'ENTRY 'c1 1 wv) (list 'ENTRY 'u wv 1))
            (list '(ACT md) (list 'ENTRY 'c2 1 wv) (list 'ENTRY 'u wv 1)))
      (rfl)))
  (lambda ()
    ;; finsum-congruence was RESTATED 2026-09-17 with a SECOND antecedent, the
    ;; POINTWISE typing of its first summand on the index set.  L is FUN-typed on
    ;; [1,n] by matact-summand-type above, so the lane is one fun-apply-type-c.
    (have! (list 'FORALL 'z_ (list 'IMPLIES (list 'IN 'z_ mra-ivl)
                                   (list 'IN (list mra-l 'z_) mra-vc)))
      (lambda ()
        (let ((mra-zv (dk-di-var!)))
          (fact 'fun-apply-type-c mra-l mra-ivl mra-vc mra-zv)
          (ass))))
    (fact 'finsum-congruence mra-vag mra-ivl mra-l mra-g)
    (subst (list '= (mra-sum mra-l) (mra-sum mra-g)))
    ;; ---- and now the sum of a pointwise sum splits.  finsum-add-ag lands its
    ;; equation with (OPR VAG) in TWO places: the outer operator, and inside the
    ;; summand lambda.  mvag-op rewrites both.  So normalize the GOAL and the
    ;; ASSUMPTION with the same macete -- rewriting only one of them makes the
    ;; two SUM_G's diverge (one keeps (OPR VAG) inside its lambda) and `ass'
    ;; silently fails to match.
    (fact 'finsum-add-ag mra-vag mra-ivl mra-f mra-h)
    (mac 'mvag-op)
    (mac-h 'mvag-op
           (list '= (mra-sum mra-g)
                 (list '(OPR (MODULE-VECTOR-AG md))
                       (mra-sum mra-f) (mra-sum mra-h))))
    (ass)))

(qed 'lincomb-row-add)
(topic! 'lincomb-row-add 'algebra)
(topic! 'matadd-entry 'algebra)       ; matrix.scm loads before the PSS layer


;;; ===================================================================
;;; BRICK 2:  lincomb-row-scale    (r*c) . u  =  r . (c . u)
;;;
;;; A near-copy of brick 1 with MATSCALE for MATADD, module-act-mul-compat for
;;; module-act-distrib-scalar, and finsum-act-distrib-gen for finsum-add-ag:
;;;
;;;   (r*c).u = sum_j (r * c_{1j}) . u_{j1}                [lincomb-unfold,
;;;                                                         matscale-entry]
;;;           = sum_j r . (c_{1j} . u_{j1})                [module-act-mul-compat]
;;;           = r . sum_j c_{1j} . u_{j1}                  [finsum-act-distrib-gen]
;;;           = r . (c.u)                                  [lincomb-unfold]
;;;
;;; Simpler than brick 1 in one respect: finsum-act-distrib-gen is already
;;; phrased in (ACT md) and FINSUM, so no (OPR VAG) ever appears and the mvag-op
;;; normalization dance of brick 1 is not needed.
;;;
;;; With brick 1 this closes the ring-module structure of the last-coefficient
;;; set S: brick 1 gives its closure under +, brick 2 its closure under scalar
;;; multiples.  S is then an IDEAL of SCAL md, which is what
;;; euclidean-ideal-has-generator consumes.
;;; ===================================================================

(define mrs-as  '(MATSCALE (SCAL md) r c))          ; the scaled row  r*c
(define mrs-l   (mra-row mrs-as))                   ; j |-> (r*c)_{1j} . u_{j1}
(define mrs-f   (mra-row 'c))                       ; j |-> c_{1j} . u_{j1}
(define mrs-g   (list 'VNB-LAMBDA 'z mra-ivl                ; z |-> r . (F z)
                      (list '(ACT md) 'r (list mrs-f 'z))))
(define mrs-prems
  '((IN r (CARR (SCAL md))) (IN c (MAT 1 n (CARR (SCAL md))))
    (IN u (MAT n 1 (VEC md)))))

;;; z |-> r . (F z) is the summand finsum-act-distrib-gen hands back, and
;;; finsum-congruence wants it typed.  The brick-1 analogue of
;;; mra-combined-summand-type: a warranted lambda FUN-typing read-off.

;;; ===================================================================
(sp (make-wff
  (mra-wf '(md) (mra-wi '((IS-MODULE md))
    (mra-wf '(n r c u) (mra-wi mrs-prems
      (list '= (list 'LINCOMB 'md 'n mrs-as 'u)
               (list '(ACT md) 'r '(LINCOMB md n c u)))))))))
(mra-di*)

;;; ---- coercions and typings
(fact 'module-scalar-ring 'md)                       ; IS-RING (SCAL md)
(fact 'module-vector-ag-is-abelian-group 'md)
(fact 'matscale-type '(SCAL md) 1 'n 'r 'c)          ; r*c is a 1-by-n row
(fact 'one-in-interval-1)                            ; 1 in [1,1]
(fact 'interval-in-set 1 'n)
(fact 'mat-rows-in-nn 'n 1 '(VEC md) 'u)
(fact 'interval-card-in-nn 1 'n)
(fact 'matact-summand-type 'md 1 'n 1 'c 'u 1 1)     ; F is a function
(fact 'matact-summand-type 'md 1 'n 1 mrs-as 'u 1 1) ; L is a function
(fact 'mrs-scaled-summand-type 'md 'n 'r 'c 'u)      ; G is a function

;;; ---- unfold both linear combinations into FINSUMs
(fact 'lincomb-unfold 'md 'n mrs-as 'u)
(fact 'lincomb-unfold 'md 'n 'c 'u)
(subst (list '== (list 'LINCOMB 'md 'n mrs-as 'u) (mra-sum mrs-l)))
(subst (list '== '(LINCOMB md n c u) (mra-sum mrs-f)))

;;; ---- pull the scalar out of the sum:  r . SUM_j F(j) = SUM_z r . F(z)
(fact 'finsum-act-distrib-gen 'md 'r mra-ivl mrs-f)
(subst (list '= (list '(ACT md) 'r (mra-sum mrs-f)) (mra-sum mrs-g)))

;;; Goal is now   SUM_j L(j)  =  SUM_z G(z),  pointwise-equal summands.
(mra-with-cut
  (list 'FORALL 'w (list 'IMPLIES (list 'IN 'w mra-ivl)
                         (list '= (list mrs-l 'w) (list mrs-g 'w))))
  (lambda ()
    (di)                                             ; peel w, absorb its bound
    (let ((wv (cadr (cadr (mra-goal)))))             ; goal (= (L w) (G w))
      (lam-b) (lam-b) (lam-b) (lam-b)                ; G's redex is nested
      (fact 'entry-in-carrier 1 'n mra-sc 'c 1 wv)
      (fact 'entry-in-carrier 'n 1 '(VEC md) 'u wv 1)
      ;; (r*c)_{1w} = r * c_{1w}
      (fact 'matscale-entry '(SCAL md) 1 'n 'r 'c 1 wv)
      (subst (list '= (list 'ENTRY mrs-as 1 wv)
                   (list '(MUL (SCAL md)) 'r (list 'ENTRY 'c 1 wv))))
      ;; (r*s).x = r.(s.x)
      (fact 'module-act-mul-compat 'md 'r (list 'ENTRY 'c 1 wv) (list 'ENTRY 'u wv 1))
      (subst (list '= (list '(ACT md) (list '(MUL (SCAL md)) 'r (list 'ENTRY 'c 1 wv))
                            (list 'ENTRY 'u wv 1))
                   (list '(ACT md) 'r
                         (list '(ACT md) (list 'ENTRY 'c 1 wv) (list 'ENTRY 'u wv 1)))))
      ;; rfl needs the term defined: type the inner and the outer action
      (fact 'module-act-type 'md (list 'ENTRY 'c 1 wv) (list 'ENTRY 'u wv 1))
      (fact 'module-act-type 'md 'r
            (list '(ACT md) (list 'ENTRY 'c 1 wv) (list 'ENTRY 'u wv 1)))
      (rfl)))
  (lambda ()
    ;; the restated finsum-congruence's pointwise typing of L (see brick 1);
    ;; L is FUN-typed on [1,n] by matact-summand-type above.
    (have! (list 'FORALL 'z_ (list 'IMPLIES (list 'IN 'z_ mra-ivl)
                                   (list 'IN (list mrs-l 'z_) mra-vc)))
      (lambda ()
        (let ((mrs-zv (dk-di-var!)))
          (fact 'fun-apply-type-c mrs-l mra-ivl mra-vc mrs-zv)
          (ass))))
    (fact 'finsum-congruence mra-vag mra-ivl mrs-l mrs-g)
    (ass)))

(qed 'lincomb-row-scale)
(topic! 'lincomb-row-scale 'algebra)
(topic! 'matscale-type 'algebra)      ; matrix.scm loads before the PSS layer
(topic! 'matscale-entry 'algebra)
