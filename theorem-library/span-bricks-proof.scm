;;; span-bricks-proof.scm -- the module-action bricks under spans-submodule-fg.
;;;
;;;   module-act-neg-one   (-1) . x  =  -x                    [in any module]
;;;   matact-zerorow       0 . u     =  0_V                   [the zero row]
;;;   matact-unitrow       e_i . u   =  u_{i1}                [the i-th unit row]
;;;   matact-empty-vzero   c . u     =  0_V                   [row of length 0]
;;;
;;; where `c . u' is (ENTRY (MATACT md c u) 1 1) = sum_j c_{1j} . u_{j1}, as in
;;; matact-row-linear-proof.scm (bricks 1 and 2).
;;;
;;; These are BRICK 3's prerequisites.  Together with bricks 1 and 2 they say
;;; exactly what is needed to see SPAN(md,n,u) as a submodule and u itself as a
;;; spanning sequence for it:
;;;
;;;   VZERO in SPAN            <- matact-zerorow
;;;   SPAN closed under VADD   <- matact-row-add       (brick 1)
;;;   SPAN closed under ACT    <- matact-row-scale     (brick 2)
;;;   SPAN closed under VNEG   <- brick 2 + module-act-neg-one
;;;   u_j in SPAN              <- matact-unitrow
;;;   the n = 0 degenerate case <- matact-empty-vzero
;;;
;;; module-act-neg-one is the one with content.  (-1).x + x = (-1+1).x = 0.x = 0
;;; exhibits (-1).x as an additive inverse of x; concluding it IS -x needs
;;; uniqueness of inverses, which the library did not have.  Rather than assert
;;; the module fact, abelian-group.scm now carries the GROUP fact
;;; `abelian-group-inverse-unique' next to its existing idempotent-is-id, and
;;; def-view-as auto-specializes it through MODULE-VECTOR-AG.  One general
;;; support, not one module lemma per additive structure.
;;;
;;; Needs: module.scm (module-act-unital/-mul-compat/-distrib-scalar, -act-type),
;;; module-zero-act, matrix.scm (ZEROMAT/UNITROW + their entry read-offs,
;;; interval-1-0-empty), finsum-additive (finsum-all-id), finsum-empty,
;;; mod-seq (MATACT, matact-entry, matact-summand-type, mvag-id).

;;; ---- driver helpers (sb- prefix)
(define (sb-goal) (wff-formula (sequent-node-assertion (proof-state-focus *ps*))))
(define (sb-foc! n) (set-proof-state-focus! *ps* n))
(define (sb-foc-goal! g)                 ; ERRORS on a miss, by design
  (let loop ((ls (proof-leaves)))
    (cond ((null? ls) (error "sb-foc-goal!: no open leaf with goal" g))
          ((equal? (wff-formula (sequent-node-assertion (car ls))) g)
           (sb-foc! (car ls)) (car ls))
          (else (loop (cdr ls))))))
(define (sb-di*)
  (let lp () (let* ((g (sb-goal)) (h (and (pair? g) (car g))))
               (when (memq h '(FORALL IMPLIES)) (di) (lp)))))
;; cut P; prove the P-subgoal, then continue on the main branch.
(define (sb-with-cut p prove-sub prove-cont)
  (let ((before (proof-leaves)))
    (cut p)
    (let* ((new (filter (lambda (l) (not (memq l before))) (proof-leaves)))
           (sub (car (filter (lambda (l) (equal? (wff-formula (sequent-node-assertion l)) p))
                             new)))
           (cont (car (filter (lambda (l) (not (eq? l sub))) new))))
      (sb-foc! sub) (prove-sub)
      (sb-foc! cont) (prove-cont))))

(define (sb-wf vs body) (if (null? vs) body (list 'FORALL (car vs) (sb-wf (cdr vs) body))))
(define (sb-wi ps body) (if (null? ps) body (list 'IMPLIES (car ps) (sb-wi (cdr ps) body))))

(define sb-vag '(MODULE-VECTOR-AG md))
(define sb-vc  '(CARR (MODULE-VECTOR-AG md)))
(define sb-sc  '(CARR (SCAL md)))
(define sb-ivl '(INTERVAL 1 n))
(define sb-one '(ONE (SCAL md)))
(define sb-neg1 '((NEG (SCAL md)) (ONE (SCAL md))))
;; j |-> c_{1j} . u_{j1}, for a coefficient row c
(define (sb-row c) (list 'VNB-LAMBDA 'j (list '(ACT md) (list 'ENTRY c 1 'j) '(ENTRY u j 1))))
(define (sb-sum f ivl) (list 'FINSUM sb-vag f ivl))


;;; ===================================================================
;;; module-act-neg-one:   (-1) . x  =  (VNEG md) x
;;;
;;;   x + (-1).x = 1.x + (-1).x = (1 + (-1)).x = 0.x = 0_V
;;; so (-1).x is an additive inverse of x in the vector abelian group, and
;;; inverses are unique there.
;;; ===================================================================
(define sb-ax (list '(ACT md) sb-neg1 'x))          ; (-1).x
(define sb-1x (list '(ACT md) sb-one 'x))           ;   1 .x

(sp (make-wff
  (sb-wf '(md) (sb-wi '((IS-MODULE md))
    (sb-wf '(x) (sb-wi '((IN x (VEC md)))
      (list '= sb-ax '((VNEG md) x))))))))
(sb-di*)

(fact 'module-scalar-ring 'md)                       ; IS-RING (SCAL md)
(fact 'ring-one-in '(SCAL md))                       ; 1 in CARR(SCAL md)
(fact 'ring-neg-in-carr '(SCAL md) sb-one)           ; -1 in CARR(SCAL md)
(fact 'module-act-type 'md sb-neg1 'x)               ; (-1).x in VEC md

;;; the equation  1.x + (-1).x = 0_V , then rewritten to  x + (-1).x = 0_V
(define sb-inv-eq (list '= (list '(VADD md) sb-1x sb-ax) '(VZERO md)))
(sb-with-cut sb-inv-eq
  (lambda ()
    ;; (1 + (-1)).x  =  1.x + (-1).x        [module-act-distrib-scalar]
    (fact 'module-act-distrib-scalar 'md sb-one sb-neg1 'x)
    ;; ... reversed, so the goal's LHS becomes the single action
    (fact 'eq-sym (list '(ACT md) (list '(ADD (SCAL md)) sb-one sb-neg1) 'x)
                  (list '(VADD md) sb-1x sb-ax))
    (subst (list '= (list '(VADD md) sb-1x sb-ax)
                 (list '(ACT md) (list '(ADD (SCAL md)) sb-one sb-neg1) 'x)))
    ;; 1 + (-1) = 0
    (fact 'ring-add-right-inv '(SCAL md) sb-one)
    (subst (list '= (list '(ADD (SCAL md)) sb-one sb-neg1) '(ZERO (SCAL md))))
    ;; 0.x = 0_V
    (fact 'module-zero-act 'md 'x)
    (ass))
  (lambda ()
    ;; 1.x = x, in the ASSUMPTION -- mac-h, not subst: rewriting the goal would
    ;; turn every x into 1.x.  module-act-unital is a conditional macete and its
    ;; two hypotheses (IS-MODULE md, IN x (VEC md)) are both in context.
    (mac-h 'module-act-unital sb-inv-eq)
    ;; x + a = 0_V  =>  a = -x, the view-specialized uniqueness of inverses
    (fact 'abelian-group-inverse-unique-module-vector-ag 'md 'x sb-ax)
    (ass)))

(qed 'module-act-neg-one)
(category! 'module-act-neg-one 'algebra)
(category! 'abelian-group-inverse-unique 'algebra)


;;; ===================================================================
;;; matact-zerorow:   (ZEROMAT (SCAL md) 1 n) . u  =  0_V
;;; Every summand is 0 . u_{j1} = 0_V, so finsum-all-id collapses the sum.
;;; ===================================================================
(define sb-zm '(ZEROMAT (SCAL md) 1 n))
(define sb-zl (sb-row sb-zm))

(sp (make-wff
  (sb-wf '(md) (sb-wi '((IS-MODULE md))
    (sb-wf '(n u) (sb-wi '((IN u (MAT n 1 (VEC md))))
      (list '= (list 'ENTRY (list 'MATACT 'md sb-zm 'u) 1 1) '(VZERO md))))))))
(sb-di*)

(fact 'module-scalar-ring 'md)
(fact 'module-vector-ag-is-abelian-group 'md)
(fact 'zeromat-type '(SCAL md) 1 'n)
(fact 'one-in-interval-1)
(fact 'interval-in-set 1 'n)
(fact 'interval-card-in-nn 1 'n)
(fact 'matact-summand-type 'md 1 'n 1 sb-zm 'u 1 1)
(fact 'matact-entry 'md 1 'n 1 sb-zm 'u 1 1)
(subst (list '= (list 'ENTRY (list 'MATACT 'md sb-zm 'u) 1 1) (sb-sum sb-zl sb-ivl)))

(sb-with-cut
  (list 'FORALL 'z (list 'IMPLIES (list 'IN 'z sb-ivl)
                         (list '= (list sb-zl 'z) (list 'IDEN sb-vag))))
  (lambda ()
    (di)
    (let ((zv (cadr (cadr (sb-goal)))))
      (lam-b)
      (mac 'mvag-id)                                 ; IDEN(VAG) -> VZERO md
      (fact 'entry-of-zeromat '(SCAL md) 1 'n 1 zv)
      (subst (list '= (list 'ENTRY sb-zm 1 zv) '(ZERO (SCAL md))))
      (fact 'entry-in-carrier 'n 1 '(VEC md) 'u zv 1)
      (fact 'module-zero-act 'md (list 'ENTRY 'u zv 1))
      (ass)))
  (lambda ()
    (fact 'finsum-all-id sb-vag sb-ivl sb-zl)
    ;; lands  SUM = IDEN(VAG); the goal says VZERO md.  Normalize the ASSUMPTION.
    (mac-h 'mvag-id (list '= (sb-sum sb-zl sb-ivl) (list 'IDEN sb-vag)))
    (ass)))

(qed 'matact-zerorow)
(category! 'matact-zerorow 'algebra)
(category! 'entry-of-zeromat 'algebra)


;;; ===================================================================
;;; matact-unitrow:   (UNITROW (SCAL md) n i) . u  =  u_{i1}
;;; The summand vanishes off j = i (unitrow-entry-off + module-zero-act), so
;;; finsum-single-support collapses the sum to its i-th term, which is
;;; 1 . u_{i1} = u_{i1}.
;;; ===================================================================
(define sb-ur '(UNITROW (SCAL md) n i))
(define sb-ul (sb-row sb-ur))

(sp (make-wff
  (sb-wf '(md) (sb-wi '((IS-MODULE md))
    (sb-wf '(n i u) (sb-wi '((IN u (MAT n 1 (VEC md))) (IN i (INTERVAL 1 n)))
      (list '= (list 'ENTRY (list 'MATACT 'md sb-ur 'u) 1 1) '(ENTRY u i 1))))))))
(sb-di*)

(fact 'module-scalar-ring 'md)
(fact 'module-vector-ag-is-abelian-group 'md)
(fact 'unitrow-type '(SCAL md) 'n 'i)
(fact 'one-in-interval-1)
(fact 'interval-in-set 1 'n)
(fact 'interval-card-in-nn 1 'n)
(fact 'entry-in-carrier 'n 1 '(VEC md) 'u 'i 1)
(fact 'matact-summand-type 'md 1 'n 1 sb-ur 'u 1 1)
(fact 'matact-entry 'md 1 'n 1 sb-ur 'u 1 1)
(subst (list '= (list 'ENTRY (list 'MATACT 'md sb-ur 'u) 1 1) (sb-sum sb-ul sb-ivl)))

(sb-with-cut
  (list 'FORALL 'z (list 'IMPLIES (list 'IN 'z sb-ivl)
                    (list 'IMPLIES (list 'NOT (list '= 'z 'i))
                          (list '= (list sb-ul 'z) (list 'IDEN sb-vag)))))
  (lambda ()
    (di) (di)                                        ; z ; z in [1,n] ; z /= i
    (let ((zv (cadr (cadr (sb-goal)))))
      (lam-b)
      (mac 'mvag-id)
      (fact 'unitrow-entry-off '(SCAL md) 'n 'i zv)
      (subst (list '= (list 'ENTRY sb-ur 1 zv) '(ZERO (SCAL md))))
      (fact 'entry-in-carrier 'n 1 '(VEC md) 'u zv 1)
      (fact 'module-zero-act 'md (list 'ENTRY 'u zv 1))
      (ass)))
  (lambda ()
    (fact 'finsum-single-support sb-vag sb-ivl sb-ul 'i)
    (subst (list '= (sb-sum sb-ul sb-ivl) (list sb-ul 'i)))
    (lam-b)                                          ; (L i) -> 1 . u_{i1}
    (fact 'unitrow-entry-at '(SCAL md) 'n 'i)
    (subst (list '= (list 'ENTRY sb-ur 1 'i) sb-one))
    (fact 'module-act-unital 'md '(ENTRY u i 1))
    (ass)))

(qed 'matact-unitrow)
(category! 'matact-unitrow 'algebra)


;;; ===================================================================
;;; matact-empty-vzero:   c . u  =  0_V   for c of length 0
;;; The index interval is [1,0] = EMPTY-SET, and an empty FINSUM is the
;;; identity.  The n = 0 base case of the spans-submodule-fg induction: a
;;; submodule spanned by NO vectors is {0}.
;;; ===================================================================
(sp (make-wff
  (sb-wf '(md) (sb-wi '((IS-MODULE md))
    (sb-wf '(c u) (sb-wi '((IN c (MAT 1 0 (CARR (SCAL md)))) (IN u (MAT 0 1 (VEC md))))
      '(= (ENTRY (MATACT md c u) 1 1) (VZERO md))))))))
(sb-di*)

(fact 'module-scalar-ring 'md)
(fact 'module-vector-ag-is-abelian-group 'md)
(fact 'module-vzero-in 'md)                          ; rfl's definedness obligation
(fact 'one-in-interval-1)
(fact 'matact-entry 'md 1 0 1 'c 'u 1 1)
(subst (list '= '(ENTRY (MATACT md c u) 1 1)
             (sb-sum (sb-row 'c) '(INTERVAL 1 0))))
(fact 'interval-1-0-empty)
(subst '(= (INTERVAL 1 0) EMPTY-SET))
(mac 'finsum-empty)                                  ; FINSUM(ag,f,{}) -> IDEN ag
(mac 'mvag-id)                                       ; IDEN(VAG)       -> VZERO md
(rfl)

(qed 'matact-empty-vzero)
(category! 'matact-empty-vzero 'algebra)
(category! 'interval-1-0-empty 'plumbing)
