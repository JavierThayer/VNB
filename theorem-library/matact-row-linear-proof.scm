;;; matact-row-linear-proof.scm -- the coefficient row acts LINEARLY.
;;;
;;;   matact-row-add    (c1 + c2) . u  =  c1.u + c2.u        [row addition]
;;;
;;; where c1, c2 are coefficient ROWS in MAT(1,n,CARR(SCAL md)), u is a sequence
;;; in MAT(n,1,VEC md), row addition is the entrywise MATADD over the scalar
;;; ring, and `c . u' abbreviates (ENTRY (MATACT md c u) 1 1) -- the single entry
;;; of the 1-by-1 product, i.e. sum_j c_{1j} . u_{j1}.
;;;
;;; BRICK 1 of the six under `spans-submodule-fg' (submodule-free.scm).  It is
;;; the keystone: SPAN(md,n,u) is closed under VADD because of exactly this, and
;;; the last-coefficient set S is closed under + because of exactly this.
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

(support 'mra-sum-row-summand-type
  (mra-wf '(md) (mra-wi '((IS-MODULE md))
    (mra-wf '(n c1 c2 u) (mra-wi mra-prems
      (list 'IN mra-l (list 'FUN mra-ivl mra-vc)))))))
(warrant! 'mra-sum-row-summand-type 'well-known
  "j |-> (c1+c2)_{1j} . u_{j1} is a function [1,n] -> VEC md: matact-summand-type
   at the row MATADD(SCAL md, c1, c2), which matadd-type types as a 1-by-n matrix
   over CARR(SCAL md).")
(category! 'mra-sum-row-summand-type 'algebra)

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
(fact 'mra-sum-row-summand-type 'md 'n 'c1 'c2 'u)
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
