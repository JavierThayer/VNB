;;; matact-row-linear-proof.scm -- the coefficient row acts LINEARLY.
;;;
;;;   matact-row-add    (c1 + c2) . u  =  c1.u + c2.u        [row addition]
;;;   matact-row-scale  (r * c)  . u  =  r . (c.u)           [row scaling]
;;;
;;; where c, c1, c2 are coefficient ROWS in MAT(1,n,CARR(SCAL md)), r is a
;;; scalar, u is a sequence in MAT(n,1,VEC md), row addition and scaling are the
;;; entrywise MATADD / MATSCALE over the scalar ring, and `c . u' abbreviates
;;; (ENTRY (MATACT md c u) 1 1) -- the single entry of the 1-by-1 product, i.e.
;;; sum_j c_{1j} . u_{j1}.
;;;
;;; BRICKS 1 and 2 of the six under `spans-submodule-fg' (submodule-free.scm).
;;; Together they say the coefficient row acts LINEARLY, and they are what makes
;;; SPAN(md,n,u) a submodule (closed under VADD by brick 1, under ACT by brick 2)
;;; and what makes the last-coefficient set S an IDEAL of the scalar ring
;;; (closed under + by brick 1, under ring multiples by brick 2).
;;;
;;; The argument is one line of mathematics and three of plumbing:
;;;   (c1+c2).u = sum_j ((c1)_{1j} + (c2)_{1j}) . u_{j1}        [matact-entry]
;;;             = sum_j ( (c1)_{1j}.u_{j1}  +  (c2)_{1j}.u_{j1} )
;;;                                                   [module-act-distrib-scalar]
;;;             = sum_j (c1)_{1j}.u_{j1} + sum_j (c2)_{1j}.u_{j1}  [finsum-add-ag]
;;;             = c1.u + c2.u                                   [matact-entry x2]
;;; The middle rewrite is under the summand, so it goes through finsum-congruence
;;; with a cut proving pointwise equality -- the idiom of matact-assoc-proof.scm.
;;;
;;; This is the FIRST consumer of finsum-add-ag (theorem-library/finsum-additive).
;;;
;;; Needs: mod-seq (MATACT, matact-entry, matact-summand-type, mvag-carr/op),
;;; matrix.scm (MATADD, matadd-type, entry-of-matof, entry-in-carrier),
;;; module.scm (module-scalar-ring, module-act-type, module-act-distrib-scalar),
;;; finsum-additive (finsum-congruence, finsum-add-ag), views (MODULE-VECTOR-AG).

;;; ---- driver helpers (mra- prefix)
(define (mra-goal) (wff-formula (sequent-node-assertion (proof-state-focus *ps*))))
(define (mra-foc! n) (set-proof-state-focus! *ps* n))
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
(define (mra-row c) (list 'VNB-LAMBDA 'j (list '(ACT md) (list 'ENTRY c 1 'j) '(ENTRY u j 1))))
(define mra-f (mra-row 'c1))                        ; j |-> c1_{1j} . u_{j1}
(define mra-h (mra-row 'c2))                        ; j |-> c2_{1j} . u_{j1}
(define mra-l (mra-row mra-cs))                     ; j |-> (c1+c2)_{1j} . u_{j1}
(define mra-g (list 'VNB-LAMBDA 'z                  ; j |-> f(j) (+) h(j)
                    (list '(MUL (MODULE-VECTOR-AG md))
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

(support 'mra-combined-summand-type
  (mra-wf '(md) (mra-wi '((IS-MODULE md))
    (mra-wf '(n c1 c2 u) (mra-wi mra-prems
      (list 'IN mra-g (list 'FUN mra-ivl mra-vc)))))))
(warrant! 'mra-combined-summand-type 'well-known
  "j |-> (c1_{1j}.u_{j1}) (+) (c2_{1j}.u_{j1}) is a function [1,n] -> VEC md:
   each summand is (matact-summand-type), and the vector abelian group's
   operation closes on its carrier (mvag-carr, mvag-op, module-vadd-type).")
(category! 'mra-combined-summand-type 'algebra)

;;; (No support is needed for the summand j |-> (c1+c2)_{1j} . u_{j1}: it is
;;; matact-summand-type at P := MATADD(SCAL md, c1, c2), whose MAT-typing
;;; matadd-type has already put in context.  `fact' instantiates P at a compound
;;; matrix term as happily as at a variable.)

;;; ===================================================================
(sp (make-wff
  (mra-wf '(md) (mra-wi '((IS-MODULE md))
    (mra-wf '(n c1 c2 u) (mra-wi mra-prems
      (list '= (list 'ENTRY (list 'MATACT 'md mra-cs 'u) 1 1)
               (list '(VADD md)
                     '(ENTRY (MATACT md c1 u) 1 1)
                     '(ENTRY (MATACT md c2 u) 1 1)))))))))
(mra-di*)

;;; ---- coercions and typings
(fact 'module-scalar-ring 'md)                       ; IS-RING (SCAL md)
(fact 'module-vector-ag-is-abelian-group 'md)
(fact 'matadd-type '(SCAL md) 1 'n 'c1 'c2)          ; c1+c2 is a 1-by-n row
(fact 'one-in-interval-1)                            ; 1 in [1,1]
(fact 'interval-in-set 1 'n)
(fact 'interval-card-in-nn 1 'n)
(fact 'mra-combined-summand-type 'md 'n 'c1 'c2 'u)
(fact 'matact-summand-type 'md 1 'n 1 mra-cs 'u 1 1) ; L is a function
(fact 'matact-summand-type 'md 1 'n 1 'c1 'u 1 1)    ; f is a function
(fact 'matact-summand-type 'md 1 'n 1 'c2 'u 1 1)    ; h is a function

;;; ---- unfold all three matrix actions into FINSUMs
(fact 'matact-entry 'md 1 'n 1 mra-cs 'u 1 1)
(fact 'matact-entry 'md 1 'n 1 'c1 'u 1 1)
(fact 'matact-entry 'md 1 'n 1 'c2 'u 1 1)
(subst (list '= (list 'ENTRY (list 'MATACT 'md mra-cs 'u) 1 1) (mra-sum mra-l)))
(subst (list '= '(ENTRY (MATACT md c1 u) 1 1) (mra-sum mra-f)))
(subst (list '= '(ENTRY (MATACT md c2 u) 1 1) (mra-sum mra-h)))

;;; Goal is now   SUM_j L(j)  =  (SUM_j F(j)) (VADD md) (SUM_j H(j)),
;;; while finsum-add-ag speaks the abelian group's (MUL VAG).
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
      ;; goal: (VADD md)(A,B) = (MUL VAG)(A,B).  Rewrite the OPERATOR.
      (mac 'mvag-op)
      ;; rfl needs the term defined: type both actions and their sum
      (fact 'module-act-type 'md (list 'ENTRY 'c1 1 wv) (list 'ENTRY 'u wv 1))
      (fact 'module-act-type 'md (list 'ENTRY 'c2 1 wv) (list 'ENTRY 'u wv 1))
      (fact 'module-vadd-type 'md
            (list '(ACT md) (list 'ENTRY 'c1 1 wv) (list 'ENTRY 'u wv 1))
            (list '(ACT md) (list 'ENTRY 'c2 1 wv) (list 'ENTRY 'u wv 1)))
      (rfl)))
  (lambda ()
    (fact 'finsum-congruence mra-vag mra-ivl mra-l mra-g)
    (subst (list '= (mra-sum mra-l) (mra-sum mra-g)))
    ;; ---- and now the sum of a pointwise sum splits.  finsum-add-ag lands its
    ;; equation with (MUL VAG) in TWO places: the outer operator, and inside the
    ;; summand lambda.  mvag-op rewrites both.  So normalize the GOAL and the
    ;; ASSUMPTION with the same macete -- rewriting only one of them makes the
    ;; two SUM_G's diverge (one keeps (MUL VAG) inside its lambda) and `ass'
    ;; silently fails to match.
    (fact 'finsum-add-ag mra-vag mra-ivl mra-f mra-h)
    (mac 'mvag-op)
    (mac-h 'mvag-op
           (list '= (mra-sum mra-g)
                 (list '(MUL (MODULE-VECTOR-AG md))
                       (mra-sum mra-f) (mra-sum mra-h))))
    (ass)))

(qed 'matact-row-add)
(category! 'matact-row-add 'algebra)
(category! 'matadd-entry 'algebra)       ; matrix.scm loads before the PSS layer


;;; ===================================================================
;;; BRICK 2:  matact-row-scale     (r*c) . u  =  r . (c . u)
;;;
;;; A near-copy of brick 1 with MATSCALE for MATADD, module-act-mul-compat for
;;; module-act-distrib-scalar, and finsum-act-distrib-gen for finsum-add-ag:
;;;
;;;   (r*c).u = sum_j (r * c_{1j}) . u_{j1}                [matact-entry,
;;;                                                         matscale-entry]
;;;           = sum_j r . (c_{1j} . u_{j1})                [module-act-mul-compat]
;;;           = r . sum_j c_{1j} . u_{j1}                  [finsum-act-distrib-gen]
;;;           = r . (c.u)                                  [matact-entry]
;;;
;;; Simpler than brick 1 in one respect: finsum-act-distrib-gen is already
;;; phrased in (ACT md) and FINSUM, so no (MUL VAG) ever appears and the mvag-op
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
(define mrs-g   (list 'VNB-LAMBDA 'z                ; z |-> r . (F z)
                      (list '(ACT md) 'r (list mrs-f 'z))))
(define mrs-prems
  '((IN r (CARR (SCAL md))) (IN c (MAT 1 n (CARR (SCAL md))))
    (IN u (MAT n 1 (VEC md)))))

;;; z |-> r . (F z) is the summand finsum-act-distrib-gen hands back, and
;;; finsum-congruence wants it typed.  The brick-1 analogue of
;;; mra-combined-summand-type: a warranted lambda FUN-typing read-off.
(support 'mrs-scaled-summand-type
  (mra-wf '(md) (mra-wi '((IS-MODULE md))
    (mra-wf '(n r c u) (mra-wi mrs-prems
      (list 'IN mrs-g (list 'FUN mra-ivl mra-vc)))))))
(warrant! 'mrs-scaled-summand-type 'well-known
  "z |-> r . (c_{1z} . u_{z1}) is a function [1,n] -> VEC md: the inner action is
   (matact-summand-type), module-act-type closes the outer action, and mvag-carr
   identifies CARR(MODULE-VECTOR-AG md) = VEC md.")
(category! 'mrs-scaled-summand-type 'algebra)

;;; ===================================================================
(sp (make-wff
  (mra-wf '(md) (mra-wi '((IS-MODULE md))
    (mra-wf '(n r c u) (mra-wi mrs-prems
      (list '= (list 'ENTRY (list 'MATACT 'md mrs-as 'u) 1 1)
               (list '(ACT md) 'r '(ENTRY (MATACT md c u) 1 1)))))))))
(mra-di*)

;;; ---- coercions and typings
(fact 'module-scalar-ring 'md)                       ; IS-RING (SCAL md)
(fact 'module-vector-ag-is-abelian-group 'md)
(fact 'matscale-type '(SCAL md) 1 'n 'r 'c)          ; r*c is a 1-by-n row
(fact 'one-in-interval-1)                            ; 1 in [1,1]
(fact 'interval-in-set 1 'n)
(fact 'interval-card-in-nn 1 'n)
(fact 'matact-summand-type 'md 1 'n 1 'c 'u 1 1)     ; F is a function
(fact 'matact-summand-type 'md 1 'n 1 mrs-as 'u 1 1) ; L is a function
(fact 'mrs-scaled-summand-type 'md 'n 'r 'c 'u)      ; G is a function

;;; ---- unfold both matrix actions into FINSUMs
(fact 'matact-entry 'md 1 'n 1 mrs-as 'u 1 1)
(fact 'matact-entry 'md 1 'n 1 'c 'u 1 1)
(subst (list '= (list 'ENTRY (list 'MATACT 'md mrs-as 'u) 1 1) (mra-sum mrs-l)))
(subst (list '= '(ENTRY (MATACT md c u) 1 1) (mra-sum mrs-f)))

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
    (fact 'finsum-congruence mra-vag mra-ivl mrs-l mrs-g)
    (ass)))

(qed 'matact-row-scale)
(category! 'matact-row-scale 'algebra)
(category! 'matscale-type 'algebra)      ; matrix.scm loads before the PSS layer
(category! 'matscale-entry 'algebra)
