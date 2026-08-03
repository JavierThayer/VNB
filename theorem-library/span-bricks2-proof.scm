;;; span-bricks2-proof.scm -- bricks 4, 5, 6 under spans-submodule-fg.
;;;
;;; BRICK 4 (peel/cons of a coefficient combination):
;;;   matact-row-peel   c.u = (c|_n . u|_n) + c_{1,succ n}.u_{succ n,1}
;;;   matact-snoc       (c,r).(u,x) = c.u + r.x
;;; where c.u = (ENTRY (MATACT md c u) 1 1) = sum_j c_{1j}.u_{j1}, c|_n = BLOCK
;;; c 1 n, u|_n = BLOCK u n 1, and (c,r) = SNOC-ROW c n r, (u,x) = SNOC-COL u n x.
;;; matact-row-peel SPLITS an arbitrary length-(succ n) combination into its
;;; length-n head and last term (the descent's s=0 case, where the last term
;;; vanishes); matact-snoc BUILDS a longer combination from a shorter one plus
;;; one term (the descent's construction of the spanning sequence (w', x0) and
;;; its witnessing coefficient (d, q)).  Both are one finsum back-peel
;;; (finsum-interval-peel) plus a congruence, the idiom of matact-row-add.
;;;
;;; BRICK 5:  submodule-intersection   s1, s2 submodules => s1 INTERSECT s2 too.
;;; BRICK 6:  mat-1-0-nonempty / mat-0-1-nonempty   the zero-dimension matrix
;;;           spaces are inhabited (the n=0 base case's empty row and sequence).
;;;
;;; Needs: matrix.scm (BLOCK/SNOC-COL/SNOC-ROW + read-offs, matof-in-mat),
;;; mod-seq (MATACT, matact-entry, matact-summand-type/-le), finsum-additive
;;; (finsum-interval-peel, finsum-congruence), finite-dimensional (IS-SUBMODULE +
;;; the submodule-*-closed projections), order-lemmas (nn-le-succ, nn-one-in,
;;; the empty-interval facts).

;;; ---- driver helpers (p2- prefix)
(define (p2-goal) (wff-formula (sequent-node-assertion (proof-state-focus *ps*))))
(define (p2-foc! n) (set-proof-state-focus! *ps* n))
(define (p2-foc-goal! g)
  (let loop ((ls (proof-leaves)))
    (cond ((null? ls) (error "p2-foc-goal!: no open leaf with goal" g))
          ((equal? (wff-formula (sequent-node-assertion (car ls))) g)
           (p2-foc! (car ls)) (car ls))
          (else (loop (cdr ls))))))
(define (p2-di*)
  (let lp () (let* ((g (p2-goal)) (h (and (pair? g) (car g))))
               (when (memq h '(FORALL IMPLIES)) (di) (lp)))))
(define (p2-with-cut p prove-sub prove-cont)
  (let ((before (proof-leaves)))
    (cut p)
    (let* ((new (filter (lambda (l) (not (memq l before))) (proof-leaves)))
           (sub (car (filter (lambda (l) (equal? (wff-formula (sequent-node-assertion l)) p)) new)))
           (cont (car (filter (lambda (l) (not (eq? l sub))) new))))
      (p2-foc! sub) (prove-sub)
      (p2-foc! cont) (prove-cont))))
(define (p2-two-way! act pred-a prove-a prove-b)
  (let ((before (proof-leaves)))
    (act)
    (let* ((new (filter (lambda (l) (not (memq l before))) (proof-leaves)))
           (a   (car (filter (lambda (l) (pred-a (wff-formula (sequent-node-assertion l)))) new)))
           (b   (car (filter (lambda (l) (not (eq? l a))) new))))
      (p2-foc! a) (prove-a)
      (p2-foc! b) (prove-b))))
(define (p2-head? h) (lambda (g) (and (pair? g) (eq? (car g) h))))
(define (p2-wf vs body) (if (null? vs) body (list 'FORALL (car vs) (p2-wf (cdr vs) body))))
(define (p2-wi ps body) (if (null? ps) body (list 'IMPLIES (car ps) (p2-wi (cdr ps) body))))

(define p2-vag '(MODULE-VECTOR-AG md))
(define p2-vc  '(CARR (MODULE-VECTOR-AG md)))
(define p2-sc  '(CARR (SCAL md)))
;; the (i=1,c=1) matact summand of a scalar matrix P acting on a sequence u
(define (p2-summ P u ivl) (list 'VNB-LAMBDA 'j ivl (list '(ACT md) (list 'ENTRY P 1 'j) (list 'ENTRY u 'j 1))))
(define (p2-sum f ivl) (list 'FINSUM p2-vag f ivl))


;;; ===================================================================
;;; matact-row-peel
;;; ===================================================================
(define p2-Bc '(BLOCK c 1 n))
(define p2-Bu '(BLOCK u n 1))
(define p2-Fs (p2-summ 'c 'u '(INTERVAL 1 (succ n))))                 ; full summand, on [1,succ n] and [1,n]
(define p2-G  (p2-summ p2-Bc p2-Bu '(INTERVAL 1 n)))           ; block summand, on [1,n]

(sp (make-wff
  (p2-wf '(md) (p2-wi '((IS-MODULE md))
    (p2-wf '(n) (p2-wi '((IN n NN))
      (p2-wf '(c) (p2-wi '((IN c (MAT 1 (succ n) (CARR (SCAL md)))))
        (p2-wf '(u) (p2-wi '((IN u (MAT (succ n) 1 (VEC md))))
          (list '= '(ENTRY (MATACT md c u) 1 1)
                (list '(VADD md)
                      (list 'ENTRY (list 'MATACT 'md p2-Bc p2-Bu) 1 1)
                      (list '(ACT md) '(ENTRY c 1 (succ n)) '(ENTRY u (succ n) 1))))))))))))))
(p2-di*)

(fact 'module-scalar-ring 'md)
(fact 'module-vector-ag-is-abelian-group 'md)
(fact 'nn-one-in) (fact 'nn-le-refl 1) (fact 'nn-le-succ 'n) (fact 'nn-succ-closed 'n)
(fact 'one-in-interval-1)
(fact 'interval-in-set 1 'n) (fact 'interval-card-in-nn 1 'n)
(fact 'block-type 1 '(succ n) p2-sc 'c 1 'n)          ; Bc in MAT 1 n CARR
(fact 'block-type '(succ n) 1 '(VEC md) 'u 'n 1)      ; Bu in MAT n 1 VEC
(fact 'matact-summand-type 'md 1 '(succ n) 1 'c 'u 1 1)       ; Fs on [1,succ n]
(fact 'matact-summand-type-le 'md 1 '(succ n) 1 'c 'u 1 1 'n) ; Fs on [1,n]
(fact 'matact-summand-type 'md 1 'n 1 p2-Bc p2-Bu 1 1)       ; G on [1,n]

;; unfold c.u to a FINSUM over [1,succ n] and peel the last term
(fact 'matact-entry 'md 1 '(succ n) 1 'c 'u 1 1)
(subst (list '= '(ENTRY (MATACT md c u) 1 1) (p2-sum p2-Fs '(INTERVAL 1 (succ n)))))
(fact 'finsum-interval-peel p2-vag 'n p2-Fs)
(subst (list '= (p2-sum p2-Fs '(INTERVAL 1 (succ n)))
             (list '(OPR (MODULE-VECTOR-AG md)) (p2-sum p2-Fs '(INTERVAL 1 n)) (list p2-Fs '(succ n)))))
(mac 'mvag-op)                                        ; (OPR VAG) -> (VADD md)
;; (p2-Fs (succ n)) reduces only where succ n is in p2-Fs's domain [1,succ n].
;; These three lines used to sit in the continuation branch below, where they
;; were wanted for the final rfl; the beta needs them HERE, before the redex.
(fact 'nn-le-refl '(succ n)) (fact 'nn-one-le-succ 'n)
(fact 'interval-mem-intro 1 '(succ n) '(succ n))       ; succ n in [1,succ n]
(lam-b) (lam-b) (lam-b)                                ; reduce (p2-Fs (succ n)) -> the last action

;; rewrite the RHS block action to its FINSUM over [1,n]
(fact 'matact-entry 'md 1 'n 1 p2-Bc p2-Bu 1 1)
(subst (list '= (list 'ENTRY (list 'MATACT 'md p2-Bc p2-Bu) 1 1) (p2-sum p2-G '(INTERVAL 1 n))))

;; the two [1,n] sums agree termwise
(p2-with-cut
  (list 'FORALL 'w (list 'IMPLIES '(IN w (INTERVAL 1 n))
                         (list '= (list p2-Fs 'w) (list p2-G 'w))))
  (lambda ()
    (di)
    (let ((wv (cadr (cadr (p2-goal)))))               ; the eigenvar w, BEFORE lam-b
      ;; w comes from [1,n], but p2-Fs is the FULL summand, of domain
      ;; [1,succ n].  Carry w across before reducing (p2-Fs w) -- the same
      ;; widening matact-summand-type-le performs for the TYPING at line 92.
      (fact 'interval-widen 1 'n '(succ n) wv)
      (lam-b) (lam-b)
      ;; rewrite the c/u entries to BLOCK entries (typed at [1,n]); c is width
      ;; succ n, so entry(c,1,w) itself is only typable at [1,succ n].
      (fact 'entry-of-block 'c 1 'n 1 wv)             ; (= (BLOCK c 1 n)_{1w} c_{1w})
      (fact 'entry-of-block 'u 'n 1 wv 1)             ; (= (BLOCK u n 1)_{w1} u_{w1})
      (fact 'eq-sym (list 'ENTRY p2-Bc 1 wv) (list 'ENTRY 'c 1 wv))
      (fact 'eq-sym (list 'ENTRY p2-Bu wv 1) (list 'ENTRY 'u wv 1))
      (subst (list '= (list 'ENTRY 'c 1 wv) (list 'ENTRY p2-Bc 1 wv)))
      (subst (list '= (list 'ENTRY 'u wv 1) (list 'ENTRY p2-Bu wv 1)))
      (fact 'entry-in-carrier 1 'n p2-sc p2-Bc 1 wv)
      (fact 'entry-in-carrier 'n 1 '(VEC md) p2-Bu wv 1)
      (fact 'module-act-type 'md (list 'ENTRY p2-Bc 1 wv) (list 'ENTRY p2-Bu wv 1))
      (rfl)))
  (lambda ()
    (fact 'finsum-congruence p2-vag '(INTERVAL 1 n) p2-Fs p2-G)
    (subst (list '= (p2-sum p2-Fs '(INTERVAL 1 n)) (p2-sum p2-G '(INTERVAL 1 n))))
    ;; rfl definedness of (VADD md)(FINSUM G, last):
    (fact 'interval-in-set 1 'n) (fact 'interval-card-in-nn 1 'n)
    (fact 'finsum-type p2-vag '(INTERVAL 1 n) p2-G)
    (mac-h 'mvag-carr (list 'IN (p2-sum p2-G '(INTERVAL 1 n)) p2-vc))   ; -> in VEC md
    (fact 'nn-succ-closed 'n) (fact 'nn-le-refl '(succ n)) (fact 'nn-one-le-succ 'n)
    (fact 'interval-mem-intro 1 '(succ n) '(succ n))   ; succ n in [1,succ n]
    (fact 'entry-in-carrier 1 '(succ n) p2-sc 'c 1 '(succ n))
    (fact 'entry-in-carrier '(succ n) 1 '(VEC md) 'u '(succ n) 1)
    (fact 'module-act-type 'md '(ENTRY c 1 (succ n)) '(ENTRY u (succ n) 1))
    (fact 'module-vadd-type 'md (p2-sum p2-G '(INTERVAL 1 n))
          '((ACT md) (ENTRY c 1 (succ n)) (ENTRY u (succ n) 1)))
    (rfl)))

(qed 'matact-row-peel)
(category! 'matact-row-peel 'algebra)
(category! 'matact-summand-type-le 'algebra)
(category! 'nn-le-succ 'plumbing)
(category! 'nn-one-in 'plumbing)


;;; ===================================================================
;;; matact-snoc
;;; ===================================================================
(define p2-SR '(SNOC-ROW c n r))
(define p2-SU '(SNOC-COL u n x))
(define p2-Fss (p2-summ p2-SR p2-SU '(INTERVAL 1 (succ n))))           ; snoc summand, on [1,succ n] and [1,n]
(define p2-Fc  (p2-summ 'c 'u '(INTERVAL 1 n)))                  ; c,u summand, on [1,n]

(sp (make-wff
  (p2-wf '(md) (p2-wi '((IS-MODULE md))
    (p2-wf '(n) (p2-wi '((IN n NN))
      (p2-wf '(c) (p2-wi '((IN c (MAT 1 n (CARR (SCAL md)))))
        (p2-wf '(u) (p2-wi '((IN u (MAT n 1 (VEC md))))
          (p2-wf '(r) (p2-wi '((IN r (CARR (SCAL md))))
            (p2-wf '(x) (p2-wi '((IN x (VEC md)))
              (list '= (list 'ENTRY (list 'MATACT 'md p2-SR p2-SU) 1 1)
                    (list '(VADD md) '(ENTRY (MATACT md c u) 1 1) '((ACT md) r x)))))))))))))))))
(p2-di*)

(fact 'module-scalar-ring 'md)
(fact 'module-vector-ag-is-abelian-group 'md)
(fact 'nn-le-succ 'n) (fact 'nn-succ-closed 'n)
(fact 'one-in-interval-1)
(fact 'interval-in-set 1 'n) (fact 'interval-card-in-nn 1 'n)
(fact 'snoc-row-type p2-sc 'n 'c 'r)                  ; SR in MAT 1 (succ n) CARR
(fact 'snoc-col-type '(VEC md) 'n 'u 'x)             ; SU in MAT (succ n) 1 VEC
(fact 'matact-summand-type 'md 1 '(succ n) 1 p2-SR p2-SU 1 1)        ; Fss on [1,succ n]
(fact 'matact-summand-type-le 'md 1 '(succ n) 1 p2-SR p2-SU 1 1 'n)  ; Fss on [1,n]
(fact 'matact-summand-type 'md 1 'n 1 'c 'u 1 1)                     ; Fc on [1,n]

;; unfold the snoc action and peel the last term
(fact 'matact-entry 'md 1 '(succ n) 1 p2-SR p2-SU 1 1)
(subst (list '= (list 'ENTRY (list 'MATACT 'md p2-SR p2-SU) 1 1) (p2-sum p2-Fss '(INTERVAL 1 (succ n)))))
(fact 'finsum-interval-peel p2-vag 'n p2-Fss)
(subst (list '= (p2-sum p2-Fss '(INTERVAL 1 (succ n)))
             (list '(OPR (MODULE-VECTOR-AG md)) (p2-sum p2-Fss '(INTERVAL 1 n)) (list p2-Fss '(succ n)))))
(mac 'mvag-op)
(fact 'nn-le-refl '(succ n)) (fact 'nn-one-le-succ 'n)
(fact 'interval-mem-intro 1 '(succ n) '(succ n))       ; succ n in [1,succ n]
(lam-b) (lam-b) (lam-b)                                ; reduce (Fss (succ n))

;; the last term = r . x
(fact 'snoc-row-last 'c 'n 'r)                        ; (SR)_{1,succ n} = r
(fact 'snoc-col-last 'u 'n 'x)                        ; (SU)_{succ n,1} = x
(subst (list '= (list 'ENTRY p2-SR 1 '(succ n)) 'r))
(subst (list '= (list 'ENTRY p2-SU '(succ n) 1) 'x))

;; rewrite RHS c.u to its FINSUM over [1,n]
(fact 'matact-entry 'md 1 'n 1 'c 'u 1 1)
(subst (list '= '(ENTRY (MATACT md c u) 1 1) (p2-sum p2-Fc '(INTERVAL 1 n))))

;; the two [1,n] sums agree termwise (snoc entries below succ n are the originals)
(p2-with-cut
  (list 'FORALL 'w (list 'IMPLIES '(IN w (INTERVAL 1 n))
                         (list '= (list p2-Fss 'w) (list p2-Fc 'w))))
  (lambda ()
    (di)
    (let ((wv (cadr (cadr (p2-goal)))))               ; the eigenvar w, BEFORE lam-b
      (fact 'interval-widen 1 'n '(succ n) wv)        ; w in [1,n] c [1,succ n]
      (lam-b) (lam-b)
      (fact 'entry-of-snoc-row 'c 'n 'r wv)           ; (SR)_{1w} = c_{1w}
      (fact 'entry-of-snoc-col 'u 'n 'x wv)           ; (SU)_{w1} = u_{w1}
      (subst (list '= (list 'ENTRY p2-SR 1 wv) (list 'ENTRY 'c 1 wv)))
      (subst (list '= (list 'ENTRY p2-SU wv 1) (list 'ENTRY 'u wv 1)))
      (fact 'entry-in-carrier 1 'n p2-sc 'c 1 wv)
      (fact 'entry-in-carrier 'n 1 '(VEC md) 'u wv 1)
      (fact 'module-act-type 'md (list 'ENTRY 'c 1 wv) (list 'ENTRY 'u wv 1))
      (rfl)))
  (lambda ()
    (fact 'finsum-congruence p2-vag '(INTERVAL 1 n) p2-Fss p2-Fc)
    (subst (list '= (p2-sum p2-Fss '(INTERVAL 1 n)) (p2-sum p2-Fc '(INTERVAL 1 n))))
    ;; rfl definedness of (VADD md)(FINSUM Fc, r.x):
    (fact 'interval-in-set 1 'n) (fact 'interval-card-in-nn 1 'n)
    (fact 'finsum-type p2-vag '(INTERVAL 1 n) p2-Fc)
    (mac-h 'mvag-carr (list 'IN (p2-sum p2-Fc '(INTERVAL 1 n)) p2-vc))   ; -> in VEC md
    (fact 'module-act-type 'md 'r 'x)
    (fact 'module-vadd-type 'md (p2-sum p2-Fc '(INTERVAL 1 n)) '((ACT md) r x))
    (rfl)))

(qed 'matact-snoc)
(category! 'matact-snoc 'algebra)


;;; ===================================================================
;;; BRICK 5:  submodule-intersection
;;; ===================================================================
(define p2-inter '(INTERSECTION s1 s2))

(sp (make-wff
  '(FORALL md (IMPLIES (IS-MODULE md)
     (FORALL s1 (IMPLIES (IS-SUBMODULE md s1)
       (FORALL s2 (IMPLIES (IS-SUBMODULE md s2)
         (IS-SUBMODULE md (INTERSECTION s1 s2))))))))))
(p2-di*)

(mac 'IS-SUBMODULE)
;; split the five conjuncts into five leaves
(let lp ((k 0))
  (let ((leaf (any-pred (lambda (s) (let ((g (wff-formula (sequent-node-assertion s))))
                                      (and (pair? g) (eq? (car g) 'AND))))
                        (proof-leaves))))
    (when (and leaf (< k 10)) (p2-foc! leaf) (di) (lp (+ k 1)))))

;; (1) SUBSET (s1 INT s2) (VEC md)
(p2-foc-goal! (list 'SUBSET p2-inter '(VEC md)))
(mac 'subset-def)
(di)
(fact 'submodule-subset 'md 's1)                      ; SUBSET s1 (VEC md)
(let ((xx (cadr (p2-goal))))                          ; goal (IN xx (VEC md))
  (ie (list 'IN xx p2-inter) 1)                       ; -> IN xx s1
  (fact 'subset-mem-fwd 's1 '(VEC md) xx)
  (ass))

;; (2) VZERO in the intersection
(p2-foc-goal! (list 'IN '(VZERO md) p2-inter))
(fact 'submodule-vzero-in 'md 's1)
(fact 'submodule-vzero-in 'md 's2)
(p2-two-way! ii (lambda (g) (equal? g '(IN (VZERO md) s1)))
  (lambda () (ass)) (lambda () (ass)))

;; (3) closed under VADD
(p2-foc-goal! (list 'FORALL 'x_ (list 'IMPLIES (list 'IN 'x_ p2-inter)
                 (list 'FORALL 'y_ (list 'IMPLIES (list 'IN 'y_ p2-inter)
                   (list 'IN '((VADD md) x_ y_) p2-inter))))))
(p2-di*)
(let* ((g (p2-goal)) (ap (cadr g)) (xx (cadr ap)) (yy (caddr ap)))
  (ie (list 'IN xx p2-inter) 1) (ie (list 'IN xx p2-inter) 2)
  (ie (list 'IN yy p2-inter) 1) (ie (list 'IN yy p2-inter) 2)
  (fact 'submodule-vadd-closed 'md 's1 xx yy)
  (fact 'submodule-vadd-closed 'md 's2 xx yy)
  (p2-two-way! ii (lambda (gg) (equal? gg (list 'IN (list '(VADD md) xx yy) 's1)))
    (lambda () (ass)) (lambda () (ass))))

;; (4) closed under VNEG
(p2-foc-goal! (list 'FORALL 'x_ (list 'IMPLIES (list 'IN 'x_ p2-inter)
                                      (list 'IN '((VNEG md) x_) p2-inter))))
(p2-di*)
(let* ((g (p2-goal)) (ap (cadr g)) (xx (cadr ap)))
  (ie (list 'IN xx p2-inter) 1) (ie (list 'IN xx p2-inter) 2)
  (fact 'submodule-vneg-closed 'md 's1 xx)
  (fact 'submodule-vneg-closed 'md 's2 xx)
  (p2-two-way! ii (lambda (gg) (equal? gg (list 'IN (list '(VNEG md) xx) 's1)))
    (lambda () (ass)) (lambda () (ass))))

;; (5) closed under the scalar action
(p2-foc-goal! (list 'FORALL 'r_ (list 'IMPLIES '(IN r_ (CARR (SCAL md)))
                 (list 'FORALL 'x_ (list 'IMPLIES (list 'IN 'x_ p2-inter)
                   (list 'IN '((ACT md) r_ x_) p2-inter))))))
(p2-di*)
(let* ((g (p2-goal)) (ap (cadr g)) (rr (cadr ap)) (xx (caddr ap)))
  (ie (list 'IN xx p2-inter) 1) (ie (list 'IN xx p2-inter) 2)
  (fact 'submodule-act-closed 'md 's1 rr xx)
  (fact 'submodule-act-closed 'md 's2 rr xx)
  (p2-two-way! ii (lambda (gg) (equal? gg (list 'IN (list '(ACT md) rr xx) 's1)))
    (lambda () (ass)) (lambda () (ass))))

(qed 'submodule-intersection)
(category! 'submodule-intersection 'algebra)
(category! 'submodule-vzero-in 'algebra)
(category! 'submodule-vadd-closed 'algebra)
(category! 'submodule-vneg-closed 'algebra)
(category! 'submodule-act-closed 'algebra)


;;; ===================================================================
;;; BRICK 6:  the zero-dimension matrix spaces are inhabited
;;; ===================================================================
(define (p2-empty-close! v)              ; close a goal from (IN v (INTERVAL 1 0)) in ctx
  (fact 'interval-lo 1 0 v) (fact 'interval-hi 1 0 v)
  (fact 'interval-elt-in-nn 1 0 v) (fact 'nn-not-le-zero-pos v)
  (ai (list 'NOT (list '<= v 0))))

(sp (make-wff '(FORALL X (FORSOME P (IN P (MAT 1 0 X))))))
(di)
(ew '(MATOF 1 0 (VNB-LAMBDA (LIST i_ j_) (CARTESIAN (INTERVAL 1 1) (INTERVAL 1 0)) i_)))
(bc* 'matof-in-mat)
(di) (di)                                              ; i (in [1,1]); j (in [1,0])
(p2-empty-close! 'j)
(qed 'mat-1-0-nonempty)
(category! 'mat-1-0-nonempty 'plumbing)

(sp (make-wff '(FORALL X (FORSOME P (IN P (MAT 0 1 X))))))
(di)
(ew '(MATOF 0 1 (VNB-LAMBDA (LIST i_ j_) (CARTESIAN (INTERVAL 1 0) (INTERVAL 1 1)) i_)))
(bc* 'matof-in-mat)
(di)                                                   ; i (in [1,0])
(p2-empty-close! 'i)
(qed 'mat-0-1-nonempty)
(category! 'mat-0-1-nonempty 'plumbing)
