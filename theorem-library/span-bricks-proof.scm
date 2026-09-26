;;; span-bricks-proof.scm -- the module-action bricks under spans-submodule-fg.
;;;
;;;   module-act-neg-one   (-1) . x  =  -x                    [in any module]
;;;   lincomb-zerorow      0 . u     =  0_V                   [the zero row]
;;;   lincomb-unitrow      e_i . u   =  u_{i1}                [the i-th unit row]
;;;   lincomb-empty        c . u     =  0_V                   [length 0]
;;;
;;; where `c . u' is LINCOMB(md, n, c, u) = sum_j c_{1j} . u_{j1}, as in
;;; matact-row-linear-proof.scm (bricks 1 and 2).
;;;
;;; RENAMED 2026-09-16 (the LINCOMB change, see mod-seq.scm): lincomb-zerorow,
;;; lincomb-unitrow, lincomb-empty were matact-zerorow, matact-unitrow,
;;; matact-empty-vzero, stated with (ENTRY (MATACT md c u) 1 1).  lincomb-empty
;;; is now UNCONDITIONAL in c and u: the empty combination is the empty FINSUM,
;;; whatever c and u are -- the n = 0 case is VZERO by construction.
;;;
;;; These are BRICK 3's prerequisites.  Together with bricks 1 and 2 they say
;;; exactly what is needed to see SPAN(md,n,u) as a submodule and u itself as a
;;; spanning sequence for it:
;;;
;;;   VZERO in SPAN            <- lincomb-zerorow
;;;   SPAN closed under VADD   <- lincomb-row-add      (brick 1)
;;;   SPAN closed under ACT    <- lincomb-row-scale    (brick 2)
;;;   SPAN closed under VNEG   <- brick 2 + module-act-neg-one
;;;   u_j in SPAN              <- lincomb-unitrow
;;;   the n = 0 degenerate case <- lincomb-empty
;;;
;;; module-act-neg-one is the one with content.  (-1).x + x = (-1+1).x = 0.x = 0
;;; exhibits (-1).x as an additive inverse of x; concluding it IS -x needs
;;; uniqueness of inverses, which the library did not have.  Rather than assert
;;; the module fact, abelian-group.scm now carries the GROUP fact
;;; `abelian-group-inverse-unique' next to its existing idempotent-is-id, and
;;; def-functor auto-specializes it through MODULE-VECTOR-AG.  One general
;;; support, not one module lemma per additive structure.
;;;
;;; Needs: module.scm (module-act-unital/-mul-compat/-distrib-scalar, -act-type),
;;; module-zero-act, matrix.scm (ZEROMAT/UNITROW + their entry read-offs,
;;; interval-1-0-empty), finsum-additive (finsum-all-id), finsum-empty,
;;; mod-seq (LINCOMB, matact-summand-type), matact-row-linear (lincomb-unfold),
;;; ag-view-read-offs (mvag-id).

;;; ---- driver helpers (sb- prefix)
(define (sb-goal) (wff-formula (sequent-node-assertion (proof-state-focus *ps*))))
(define (sb-foc! n) (dk-focus! n))
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
(define (sb-row c ivl) (list 'VNB-LAMBDA 'j ivl (list '(ACT md) (list 'ENTRY c 1 'j) '(ENTRY u j 1))))
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
(topic! 'module-act-neg-one 'algebra)
(topic! 'abelian-group-inverse-unique 'algebra)


;;; ===================================================================
;;; lincomb-zerorow:  (ZEROMAT (SCAL md) 1 n) . u  =  0_V
;;; Every summand is 0 . u_{j1} = 0_V, so finsum-all-id collapses the sum.
;;; ===================================================================
(define sb-zm '(ZEROMAT (SCAL md) 1 n))
(define sb-zl (sb-row sb-zm sb-ivl))

(sp (make-wff
  (sb-wf '(md) (sb-wi '((IS-MODULE md))
    (sb-wf '(n u) (sb-wi '((IN u (MAT n 1 (VEC md))))
      (list '= (list 'LINCOMB 'md 'n sb-zm 'u) '(VZERO md))))))))
(sb-di*)

(fact 'module-scalar-ring 'md)
(fact 'module-vector-ag-is-abelian-group 'md)
;; zeromat-type's dimension guards (2026-09-16): 1 in NN, and n in NN -- n is
;; the row count of the column u (also interval-card-in-nn's guard).
(fact 'nn-one-in)
(fact 'mat-rows-in-nn 'n 1 '(VEC md) 'u)
(fact 'zeromat-type '(SCAL md) 1 'n)
(fact 'one-in-interval-1)
(fact 'interval-in-set 1 'n)
(fact 'interval-card-in-nn 1 'n)
(fact 'matact-summand-type 'md 1 'n 1 sb-zm 'u 1 1)
(fact 'lincomb-unfold 'md 'n sb-zm 'u)
(subst (list '== (list 'LINCOMB 'md 'n sb-zm 'u) (sb-sum sb-zl sb-ivl)))

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

(qed 'lincomb-zerorow)
(topic! 'lincomb-zerorow 'algebra)
(topic! 'entry-of-zeromat 'algebra)


;;; ===================================================================
;;; lincomb-unitrow:  (UNITROW (SCAL md) n i) . u  =  u_{i1}
;;; The summand vanishes off j = i (unitrow-entry-off + module-zero-act), so
;;; finsum-single-support collapses the sum to its i-th term, which is
;;; 1 . u_{i1} = u_{i1}.
;;; ===================================================================
(define sb-ur '(UNITROW (SCAL md) n i))
(define sb-ul (sb-row sb-ur sb-ivl))

(sp (make-wff
  (sb-wf '(md) (sb-wi '((IS-MODULE md))
    (sb-wf '(n i u) (sb-wi '((IN u (MAT n 1 (VEC md))) (IN i (INTERVAL 1 n)))
      (list '= (list 'LINCOMB 'md 'n sb-ur 'u) '(ENTRY u i 1))))))))
(sb-di*)

(fact 'module-scalar-ring 'md)
(fact 'module-vector-ag-is-abelian-group 'md)
(fact 'mat-rows-in-nn 'n 1 '(VEC md) 'u)             ; unitrow-type's guard (2026-09-16)
(fact 'unitrow-type '(SCAL md) 'n 'i)
(fact 'one-in-interval-1)
(fact 'interval-in-set 1 'n)
(fact 'interval-card-in-nn 1 'n)
(fact 'entry-in-carrier 'n 1 '(VEC md) 'u 'i 1)
(fact 'matact-summand-type 'md 1 'n 1 sb-ur 'u 1 1)
(fact 'lincomb-unfold 'md 'n sb-ur 'u)
(subst (list '== (list 'LINCOMB 'md 'n sb-ur 'u) (sb-sum sb-ul sb-ivl)))

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

(qed 'lincomb-unitrow)
(topic! 'lincomb-unitrow 'algebra)


;;; ===================================================================
;;; lincomb-empty:   LINCOMB(md, 0, c, u)  =  0_V   for ANY c, u
;;; The index interval is [1,0] = EMPTY-SET, and an empty FINSUM is the
;;; identity.  The n = 0 base case of the spans-submodule-fg induction: a
;;; submodule spanned by NO vectors is {0}.  No hypothesis on c or u: the
;;; empty combination does not look at them.
;;; ===================================================================
(sp (make-wff
  (sb-wf '(md) (sb-wi '((IS-MODULE md))
    (sb-wf '(c u)
      '(= (LINCOMB md 0 c u) (VZERO md)))))))
(sb-di*)

(fact 'module-vzero-in 'md)                          ; rfl's definedness obligation
(fact 'lincomb-unfold 'md 0 'c 'u)
(subst (list '== '(LINCOMB md 0 c u)
             (sb-sum (sb-row 'c '(INTERVAL 1 0)) '(INTERVAL 1 0))))
(fact 'interval-1-0-empty)
(subst '(= (INTERVAL 1 0) EMPTY-SET))
(mac 'finsum-empty)                                  ; FINSUM(ag,f,{}) -> IDEN ag
(mac 'mvag-id)                                       ; IDEN(VAG)       -> VZERO md
(rfl)

(qed 'lincomb-empty)
(topic! 'lincomb-empty 'algebra)
(topic! 'interval-1-0-empty 'plumbing)


;;; ===================================================================
;;; BRICK 3 proper.
;;;
;;;   span-is-submodule   IS-SUBMODULE(md, SPAN(md,n,u))
;;;   spans-span          SPANS(md, n, u, SPAN(md,n,u))
;;;
;;; The five conjuncts of IS-SUBMODULE, one brick each:
;;;   SUBSET       span-membership: a SEP set sits inside its domain
;;;   VZERO in     lincomb-zerorow,   witness (ZEROMAT (SCAL md) 1 n)
;;;   VADD closed  lincomb-row-add,   witness (MATADD (SCAL md) c1 c2)
;;;   VNEG closed  lincomb-row-scale + module-act-neg-one,
;;;                                   witness (MATSCALE (SCAL md) (-1) c1)
;;;   ACT closed   lincomb-row-scale, witness (MATSCALE (SCAL md) r c1)
;;; and, for spans-span, lincomb-unitrow with witness (UNITROW (SCAL md) n j).
;;;
;;; Every witness is a coefficient ROW, and every proof obligation is one of the
;;; row-linearity bricks.  That is the whole point of stating bricks 1 and 2 at
;;; the level of rows rather than of the module.
;;; ===================================================================

;;; Unfolding a membership goal, and `di'-on-AND, each open exactly two leaves
;;; and rename bound variables as they go.  Do not navigate by goal shape:
;;; snapshot the leaves, and tell the two apart by which one PRED accepts.
(define (sb-two-way! act pred-a prove-a prove-b)
  (let ((before (proof-leaves)))
    (act)
    (let* ((new (filter (lambda (l) (not (memq l before))) (proof-leaves)))
           (a   (car (filter (lambda (l) (pred-a (wff-formula (sequent-node-assertion l)))) new)))
           (b   (car (filter (lambda (l) (not (eq? l a))) new))))
      (unless (= (length new) 2) (error "sb-two-way!: expected 2 new leaves" (length new)))
      (sb-foc! a) (prove-a)
      (sb-foc! b) (prove-b))))

(define (sb-head? h) (lambda (g) (and (pair? g) (eq? (car g) h))))

(define sb-span '(SPAN md n u))
;; the context equation  t = (LINCOMB md n c u) , and its row c
(define (sb-eq-for t)
  (dc-find (lambda (a) (and (pair? a) (eq? (car a) '=) (equal? (cadr a) t)
                            (pair? (caddr a)) (eq? (car (caddr a)) 'LINCOMB)))))
(define (sb-row-of eq) (list-ref (caddr eq) 3))       ; (= t (LINCOMB md n c u)) -> c
(define (sb-lc c) (list 'LINCOMB 'md 'n c 'u))

;; Unfold `t in SPAN(md,n,u)' in the CONTEXT down to its coefficient row.
;; `mac-h' needs a *theorem*, and def-functoid installs only a macete -- hence
;; span-membership (mod-seq.scm) rather than (mac-h 'SPAN ...), which warns
;; "unknown theorem/macete" and then silently leaves the assumption alone.
;; Afterwards the context holds (IN t (VEC md)), (IN c (MAT 1 n ..)) and
;; (= t (LINCOMB md n c u)).  Returns the row c.
(define (sb-open-span! t)
  (mac-h 'span-membership (list 'IN t sb-span))
  (ai (dc-find (dc-head? 'AND)))                      ; (IN t (VEC md)) ; FORSOME
  (ai (dc-find (dc-head? 'FORSOME)))                  ; eigen row c     ; AND
  (ai (dc-find (dc-head? 'AND)))                      ; typing ; the equation
  (sb-row-of (sb-eq-for t)))

;; goal `t in SPAN' -> two leaves: (IN t (VEC md)) and the FORSOME.
(define (sb-span-mi) (mac 'span-membership) (di))

;;; the body of IS-SUBMODULE(md, S)
(define (sb-submodule-body s)
  (list 'AND (list 'SUBSET s '(VEC md))
   (list 'AND (list 'IN '(VZERO md) s)
    (list 'AND (list 'FORALL 'x_ (list 'IMPLIES (list 'IN 'x_ s)
                     (list 'FORALL 'y_ (list 'IMPLIES (list 'IN 'y_ s)
                       (list 'IN '((VADD md) x_ y_) s)))))
     (list 'AND (list 'FORALL 'x_ (list 'IMPLIES (list 'IN 'x_ s)
                       (list 'IN '((VNEG md) x_) s)))
           (list 'FORALL 'r_ (list 'IMPLIES '(IN r_ (CARR (SCAL md)))
             (list 'FORALL 'x_ (list 'IMPLIES (list 'IN 'x_ s)
               (list 'IN '((ACT md) r_ x_) s))))))))))

(define (sb-split-and-goals!)
  (let lp ((n 0))
    (let ((leaf (any-pred (lambda (s)
                            (let ((g (wff-formula (sequent-node-assertion s))))
                              (and (pair? g) (eq? (car g) 'AND))))
                          (proof-leaves))))
      (when (and leaf (< n 20)) (sb-foc! leaf) (di) (lp (+ n 1))))))

;;; -------------------------------------------------------------------
(sp (make-wff
  (sb-wf '(md) (sb-wi '((IS-MODULE md))
    (sb-wf '(n u) (sb-wi '((IN u (MAT n 1 (VEC md))))
      (list 'IS-SUBMODULE 'md sb-span)))))))
(sb-di*)

(fact 'module-scalar-ring 'md)
(fact 'module-vzero-in 'md)
(fact 'ring-one-in '(SCAL md))
(fact 'ring-neg-in-carr '(SCAL md) sb-one)           ; -1 in CARR(SCAL md)
(fact 'nn-one-in)                                    ; zeromat-type's guards (2026-09-16)
(fact 'mat-rows-in-nn 'n 1 '(VEC md) 'u)
(fact 'zeromat-type '(SCAL md) 1 'n)

(mac 'IS-SUBMODULE)
(sb-split-and-goals!)                                ; five conjuncts, five leaves

;; (1) SPAN subset VEC md -- a SEP set lies in its domain.
(sb-foc-goal! (list 'SUBSET sb-span '(VEC md)))
(mac 'subset-def)
(di)
(let ((xx (cadr (sb-goal))))                         ; goal (IN xx (VEC md))
  (mac-h 'span-membership (list 'IN xx sb-span))
  (ai (dc-find (dc-head? 'AND)))
  (ass))

;; (2) VZERO md in SPAN -- the zero row.
(sb-foc-goal! (list 'IN '(VZERO md) sb-span))
(sb-two-way! sb-span-mi (sb-head? 'IN)
  (lambda () (ass))                                  ; (IN (VZERO md) (VEC md))
  (lambda ()
    (sb-two-way! (lambda () (ew sb-zm) (di)) (sb-head? 'IN)
      (lambda () (ass))                              ; (IN ZEROMAT (MAT 1 n ..))
      (lambda ()                                     ; (= (VZERO md) (ZEROMAT.u))
        (fact 'lincomb-zerorow 'md 'n 'u)
        (fact 'eq-sym (sb-lc sb-zm) '(VZERO md))
        (ass)))))

;; (3) SPAN closed under VADD -- add the coefficient rows (brick 1).
(sb-foc-goal! (list 'FORALL 'x_ (list 'IMPLIES (list 'IN 'x_ sb-span)
                 (list 'FORALL 'y_ (list 'IMPLIES (list 'IN 'y_ sb-span)
                   (list 'IN '((VADD md) x_ y_) sb-span))))))
(sb-di*)
(let* ((g  (sb-goal)) (ap (cadr g)) (xx (cadr ap)) (yy (caddr ap))
       (c1 (sb-open-span! xx)) (c2 (sb-open-span! yy))
       (c1u (sb-lc c1))
       (c2u (sb-lc c2))
       (ma  (list 'MATADD '(SCAL md) c1 c2)))
  (fact 'module-vadd-type 'md xx yy)
  (fact 'matadd-type '(SCAL md) 1 'n c1 c2)
  (sb-two-way! sb-span-mi (sb-head? 'IN)
    (lambda () (ass))                                ; (IN (VADD xx yy) (VEC md))
    (lambda ()
      (sb-two-way! (lambda () (ew ma) (di)) (sb-head? 'IN)
        (lambda () (ass))                            ; (IN (MATADD ..) (MAT 1 n ..))
        (lambda ()
          ;; goal  (VADD md)(xx,yy) = (MATADD c1 c2).u
          (fact 'lincomb-row-add 'md 'n c1 c2 'u)
          (subst (list '= (sb-lc ma)
                       (list '(VADD md) c1u c2u)))
          (fact 'eq-sym xx c1u) (subst (list '= c1u xx))
          (fact 'eq-sym yy c2u) (subst (list '= c2u yy))
          (rfl))))))

;; (4) SPAN closed under VNEG -- scale the row by -1 (brick 2 + module-act-neg-one).
(sb-foc-goal! (list 'FORALL 'x_ (list 'IMPLIES (list 'IN 'x_ sb-span)
                                      (list 'IN '((VNEG md) x_) sb-span))))
(sb-di*)
(let* ((g  (sb-goal)) (ap (cadr g)) (xx (cadr ap))
       (c1 (sb-open-span! xx))
       (c1u (sb-lc c1))
       (ms  (list 'MATSCALE '(SCAL md) sb-neg1 c1)))
  (fact 'module-vneg-type 'md xx)
  (fact 'matscale-type '(SCAL md) 1 'n sb-neg1 c1)
  (sb-two-way! sb-span-mi (sb-head? 'IN)
    (lambda () (ass))                                ; (IN (VNEG xx) (VEC md))
    (lambda ()
      (sb-two-way! (lambda () (ew ms) (di)) (sb-head? 'IN)
        (lambda () (ass))                            ; (IN (MATSCALE ..) (MAT 1 n ..))
        (lambda ()
          ;; goal  (VNEG md) xx = ((-1)*c1).u
          (fact 'lincomb-row-scale 'md 'n sb-neg1 c1 'u)
          (subst (list '= (sb-lc ms)
                       (list '(ACT md) sb-neg1 c1u)))
          (fact 'eq-sym xx c1u) (subst (list '= c1u xx))
          ;; goal  (VNEG md) xx = (-1).xx
          (fact 'module-act-neg-one 'md xx)
          (fact 'eq-sym (list '(ACT md) sb-neg1 xx) (list '(VNEG md) xx))
          (ass))))))

;; (5) SPAN closed under the scalar action -- scale the row (brick 2).
(sb-foc-goal! (list 'FORALL 'r_ (list 'IMPLIES '(IN r_ (CARR (SCAL md)))
                 (list 'FORALL 'x_ (list 'IMPLIES (list 'IN 'x_ sb-span)
                   (list 'IN '((ACT md) r_ x_) sb-span))))))
(sb-di*)
(let* ((g  (sb-goal)) (ap (cadr g)) (rr (cadr ap)) (xx (caddr ap))
       (c1 (sb-open-span! xx))
       (c1u (sb-lc c1))
       (ms  (list 'MATSCALE '(SCAL md) rr c1)))
  (fact 'module-act-type 'md rr xx)
  (fact 'matscale-type '(SCAL md) 1 'n rr c1)
  (sb-two-way! sb-span-mi (sb-head? 'IN)
    (lambda () (ass))                                ; (IN (ACT rr xx) (VEC md))
    (lambda ()
      (sb-two-way! (lambda () (ew ms) (di)) (sb-head? 'IN)
        (lambda () (ass))                            ; (IN (MATSCALE ..) (MAT 1 n ..))
        (lambda ()
          (fact 'lincomb-row-scale 'md 'n rr c1 'u)
          (subst (list '= (sb-lc ms)
                       (list '(ACT md) rr c1u)))
          (fact 'eq-sym xx c1u) (subst (list '= c1u xx))
          (rfl))))))

(qed 'span-is-submodule)
(topic! 'span-is-submodule 'algebra)


;;; ===================================================================
;;; spans-span:  u spans SPAN(md,n,u).
;;;   conjunct 1: u_{j1} in SPAN, witnessed by the unit row e_j (lincomb-unitrow)
;;;   conjunct 2: every member of SPAN is a combination -- that IS the SEP body.
;;; ===================================================================
(sp (make-wff
  (sb-wf '(md) (sb-wi '((IS-MODULE md))
    (sb-wf '(n u) (sb-wi '((IN u (MAT n 1 (VEC md))))
      (list 'SPANS 'md 'n 'u sb-span)))))))
(sb-di*)

(fact 'module-scalar-ring 'md)
(fact 'one-in-interval-1)                            ; entry-in-carrier's column bound
(fact 'mat-rows-in-nn 'n 1 '(VEC md) 'u)             ; unitrow-type's guard (2026-09-16)
(mac 'SPANS)
(sb-split-and-goals!)

;; (1) each u_{j1} lies in SPAN, via the unit row.
(sb-foc-goal! (list 'FORALL 'j_ (list 'IMPLIES '(IN j_ (INTERVAL 1 n))
                                      (list 'IN '(ENTRY u j_ 1) sb-span))))
(sb-di*)
(let* ((g  (sb-goal)) (uj (cadr g)) (jj (caddr uj))   ; goal (IN (ENTRY u jj 1) SPAN)
       (ur (list 'UNITROW '(SCAL md) 'n jj)))
  (fact 'entry-in-carrier 'n 1 '(VEC md) 'u jj 1)
  (fact 'unitrow-type '(SCAL md) 'n jj)
  (sb-two-way! sb-span-mi (sb-head? 'IN)
    (lambda () (ass))                                ; (IN (ENTRY u jj 1) (VEC md))
    (lambda ()
      (sb-two-way! (lambda () (ew ur) (di)) (sb-head? 'IN)
        (lambda () (ass))                            ; (IN (UNITROW ..) (MAT 1 n ..))
        (lambda ()
          (fact 'lincomb-unitrow 'md 'n jj 'u)
          (fact 'eq-sym (sb-lc ur) uj)
          (ass))))))

;; (2) every member of SPAN is a coefficient combination -- unpack the SEP.
(sb-foc-goal! (list 'FORALL 'x_ (list 'IMPLIES (list 'IN 'x_ sb-span)
                 '(FORSOME c_ (AND (IN c_ (MAT 1 n (CARR (SCAL md))))
                                   (= x_ (LINCOMB md n c_ u)))))))
(sb-di*)
;; read xx off the CONTEXT, not the goal: the goal's leading binder is c_.
(let ((xx (cadr (dc-find (lambda (a) (and (pair? a) (eq? (car a) 'IN)
                                          (equal? (caddr a) sb-span)))))))
  (mac-h 'span-membership (list 'IN xx sb-span))
  (ai (dc-find (dc-head? 'AND)))
  (ass))

(qed 'spans-span)
(topic! 'spans-span 'algebra)
