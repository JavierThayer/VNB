;;; span-bricks2-proof.scm -- bricks 4, 5, 6 under spans-submodule-fg.
;;;
;;; BRICK 4 (peel/cons of a coefficient combination):
;;;   lincomb-row-peel  c.u = (c|_n . u|_n) + c_{1,succ n}.u_{succ n,1}
;;;   lincomb-snoc      (c,r).(u,x) = c.u + r.x
;;; where c.u = LINCOMB(md, len, c, u) = sum_j c_{1j}.u_{j1}, c|_n = BLOCK
;;; c 1 n, u|_n = BLOCK u n 1, and (c,r) = SNOC-ROW c n r, (u,x) = SNOC-COL u n x.
;;; (RENAMED 2026-09-16 from matact-row-peel / matact-snoc, which were stated
;;; with (ENTRY (MATACT md c u) 1 1); see LINCOMB in mod-seq.scm.  At n = 0 the
;;; length-n head is the empty combination, VZERO -- the right answer, where the
;;; old MATACT entry was an unspecified value.)
;;; lincomb-row-peel SPLITS an arbitrary length-(succ n) combination into its
;;; length-n head and last term (the descent's s=0 case, where the last term
;;; vanishes); lincomb-snoc BUILDS a longer combination from a shorter one plus
;;; one term (the descent's construction of the spanning sequence (w', x0) and
;;; its witnessing coefficient (d, q)).  Both are one finsum back-peel
;;; (finsum-interval-peel) plus a congruence, the idiom of lincomb-row-add.
;;;
;;; BRICK 5:  submodule-intersection   s1, s2 submodules => s1 INTERSECT s2 too.
;;; BRICK 6:  mat-1-0-nonempty / mat-0-1-nonempty   the zero-dimension matrix
;;;           spaces are inhabited (the n=0 base case's empty row and sequence).
;;;
;;; Needs: matrix.scm (BLOCK/SNOC-COL/SNOC-ROW + read-offs, matof-in-mat),
;;; mod-seq (LINCOMB, matact-summand-type/-le), lincomb-unfold, finsum-additive
;;; (finsum-interval-peel, finsum-congruence), finite-dimensional (IS-SUBMODULE +
;;; the submodule-*-closed projections), order-lemmas (nn-le-succ, nn-one-in,
;;; the empty-interval facts).

;;; ---- driver helpers (p2- prefix)
(define (p2-goal) (wff-formula (sequent-node-assertion (proof-state-focus *ps*))))
(define (p2-foc! n) (dk-focus! n))
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
;;; lincomb-row-peel
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
          (list '= '(LINCOMB md (succ n) c u)
                (list '(VADD md)
                      (list 'LINCOMB 'md 'n p2-Bc p2-Bu)
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
(fact 'matact-summand-type-le-guarded 'md 1 '(succ n) 1 'c 'u 1 1 'n) ; Fs on [1,n]
;; REPOINTED 2026-09-15 (wave 7): the unguarded matact-summand-type-le was FALSE
;; as written -- interval-widen, its whole content, needs `k in NN' and nothing
;; in that statement typed k.  The guarded theorem is
;; theorem-library/matact-summand-type-le-proof.scm; its new antecedent (IN k NN)
;; is here `IN n NN', a premise of this theorem, so `fact' auto-detaches it and
;; the argument list is unchanged.
(fact 'matact-summand-type 'md 1 'n 1 p2-Bc p2-Bu 1 1)       ; G on [1,n]

;; unfold c.u to a FINSUM over [1,succ n] and peel the last term
(fact 'lincomb-unfold 'md '(succ n) 'c 'u)
(subst (list '== '(LINCOMB md (succ n) c u) (p2-sum p2-Fs '(INTERVAL 1 (succ n)))))
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

;; rewrite the RHS block combination to its FINSUM over [1,n]
(fact 'lincomb-unfold 'md 'n p2-Bc p2-Bu)
(subst (list '== (list 'LINCOMB 'md 'n p2-Bc p2-Bu) (p2-sum p2-G '(INTERVAL 1 n))))

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
      (fact 'interval-widen 'n '(succ n) 1 wv)
      (lam-b) (lam-b)
      ;; rewrite the c/u entries to BLOCK entries (typed at [1,n]); c is width
      ;; succ n, so entry(c,1,w) itself is only typable at [1,succ n].
      ;; entry-of-block carries block-type's premises since 2026-09-16: the
      ;; three trailing arguments are the source matrix's shape and carrier.
      (fact 'entry-of-block 'c 1 'n 1 wv 1 '(succ n) p2-sc)       ; (= (BLOCK c 1 n)_{1w} c_{1w})
      (fact 'entry-of-block 'u 'n 1 wv 1 '(succ n) 1 '(VEC md))   ; (= (BLOCK u n 1)_{w1} u_{w1})
      (fact 'eq-sym (list 'ENTRY p2-Bc 1 wv) (list 'ENTRY 'c 1 wv))
      (fact 'eq-sym (list 'ENTRY p2-Bu wv 1) (list 'ENTRY 'u wv 1))
      (subst (list '= (list 'ENTRY 'c 1 wv) (list 'ENTRY p2-Bc 1 wv)))
      (subst (list '= (list 'ENTRY 'u wv 1) (list 'ENTRY p2-Bu wv 1)))
      (fact 'entry-in-carrier 1 'n p2-sc p2-Bc 1 wv)
      (fact 'entry-in-carrier 'n 1 '(VEC md) p2-Bu wv 1)
      (fact 'module-act-type 'md (list 'ENTRY p2-Bc 1 wv) (list 'ENTRY p2-Bu wv 1))
      (rfl)))
  (lambda ()
    ;; finsum-congruence was RESTATED 2026-09-17 with a SECOND antecedent, the
    ;; POINTWISE typing of its first summand on the index set.  Its f here is the
    ;; FULL summand p2-Fs, of DOMAIN [1,succ n], summed over [1,n] -- so the point
    ;; is carried across by interval-widen first (the same widening line 133 does
    ;; for the beta), and then fun-apply-type-c off the [1,succ n] typing.
    (have! (list 'FORALL 'z_ (list 'IMPLIES '(IN z_ (INTERVAL 1 n))
                                   (list 'IN (list p2-Fs 'z_) p2-vc)))
      (lambda ()
        (let ((p2-zv (dk-di-var!)))
          (fact 'interval-widen 'n '(succ n) 1 p2-zv)
          (fact 'fun-apply-type-c p2-Fs '(INTERVAL 1 (succ n)) p2-vc p2-zv)
          (ass))))
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

(qed 'lincomb-row-peel)
(topic! 'lincomb-row-peel 'algebra)
;;; (topic! 'matact-summand-type-le 'algebra) -- REMOVED 2026-09-15: that support
;;; is retired; the guarded theorem topics itself where it is proven.
(topic! 'nn-le-succ 'plumbing)
(topic! 'nn-one-in 'plumbing)


;;; ===================================================================
;;; lincomb-snoc
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
              (list '= (list 'LINCOMB 'md '(succ n) p2-SR p2-SU)
                    (list '(VADD md) '(LINCOMB md n c u) '((ACT md) r x)))))))))))))))))
(p2-di*)

(fact 'module-scalar-ring 'md)
(fact 'module-vector-ag-is-abelian-group 'md)
(fact 'nn-le-succ 'n) (fact 'nn-succ-closed 'n)
(fact 'one-in-interval-1)
(fact 'interval-in-set 1 'n) (fact 'interval-card-in-nn 1 'n)
(fact 'snoc-row-type p2-sc 'n 'c 'r)                  ; SR in MAT 1 (succ n) CARR
(fact 'snoc-col-type '(VEC md) 'n 'u 'x)             ; SU in MAT (succ n) 1 VEC
(fact 'matact-summand-type 'md 1 '(succ n) 1 p2-SR p2-SU 1 1)        ; Fss on [1,succ n]
(fact 'matact-summand-type-le-guarded 'md 1 '(succ n) 1 p2-SR p2-SU 1 1 'n)  ; Fss on [1,n]  (guard IN n NN from this theorem's premises)
(fact 'matact-summand-type 'md 1 'n 1 'c 'u 1 1)                     ; Fc on [1,n]

;; unfold the snoc combination and peel the last term
(fact 'lincomb-unfold 'md '(succ n) p2-SR p2-SU)
(subst (list '== (list 'LINCOMB 'md '(succ n) p2-SR p2-SU) (p2-sum p2-Fss '(INTERVAL 1 (succ n)))))
(fact 'finsum-interval-peel p2-vag 'n p2-Fss)
(subst (list '= (p2-sum p2-Fss '(INTERVAL 1 (succ n)))
             (list '(OPR (MODULE-VECTOR-AG md)) (p2-sum p2-Fss '(INTERVAL 1 n)) (list p2-Fss '(succ n)))))
(mac 'mvag-op)
(fact 'nn-le-refl '(succ n)) (fact 'nn-one-le-succ 'n)
(fact 'interval-mem-intro 1 '(succ n) '(succ n))       ; succ n in [1,succ n]
(lam-b) (lam-b) (lam-b)                                ; reduce (Fss (succ n))

;; the last term = r . x
;; the SNOC read-offs carry the *-type premises since 2026-09-16; the trailing
;; argument is the carrier.
(fact 'snoc-row-last 'c 'n 'r p2-sc)                  ; (SR)_{1,succ n} = r
(fact 'snoc-col-last 'u 'n 'x '(VEC md))              ; (SU)_{succ n,1} = x
(subst (list '= (list 'ENTRY p2-SR 1 '(succ n)) 'r))
(subst (list '= (list 'ENTRY p2-SU '(succ n) 1) 'x))

;; rewrite RHS c.u to its FINSUM over [1,n]
(fact 'lincomb-unfold 'md 'n 'c 'u)
(subst (list '== '(LINCOMB md n c u) (p2-sum p2-Fc '(INTERVAL 1 n))))

;; the two [1,n] sums agree termwise (snoc entries below succ n are the originals)
(p2-with-cut
  (list 'FORALL 'w (list 'IMPLIES '(IN w (INTERVAL 1 n))
                         (list '= (list p2-Fss 'w) (list p2-Fc 'w))))
  (lambda ()
    (di)
    (let ((wv (cadr (cadr (p2-goal)))))               ; the eigenvar w, BEFORE lam-b
      (fact 'interval-widen 'n '(succ n) 1 wv)        ; w in [1,n] c [1,succ n]
      (lam-b) (lam-b)
      (fact 'entry-of-snoc-row 'c 'n 'r wv p2-sc)     ; (SR)_{1w} = c_{1w}
      (fact 'entry-of-snoc-col 'u 'n 'x wv '(VEC md)) ; (SU)_{w1} = u_{w1}
      (subst (list '= (list 'ENTRY p2-SR 1 wv) (list 'ENTRY 'c 1 wv)))
      (subst (list '= (list 'ENTRY p2-SU wv 1) (list 'ENTRY 'u wv 1)))
      (fact 'entry-in-carrier 1 'n p2-sc 'c 1 wv)
      (fact 'entry-in-carrier 'n 1 '(VEC md) 'u wv 1)
      (fact 'module-act-type 'md (list 'ENTRY 'c 1 wv) (list 'ENTRY 'u wv 1))
      (rfl)))
  (lambda ()
    ;; the restated finsum-congruence's pointwise typing of p2-Fss (see
    ;; lincomb-row-peel): domain [1,succ n], index set [1,n], so widen then apply.
    (have! (list 'FORALL 'z_ (list 'IMPLIES '(IN z_ (INTERVAL 1 n))
                                   (list 'IN (list p2-Fss 'z_) p2-vc)))
      (lambda ()
        (let ((p2-zv (dk-di-var!)))
          (fact 'interval-widen 'n '(succ n) 1 p2-zv)
          (fact 'fun-apply-type-c p2-Fss '(INTERVAL 1 (succ n)) p2-vc p2-zv)
          (ass))))
    (fact 'finsum-congruence p2-vag '(INTERVAL 1 n) p2-Fss p2-Fc)
    (subst (list '= (p2-sum p2-Fss '(INTERVAL 1 n)) (p2-sum p2-Fc '(INTERVAL 1 n))))
    ;; rfl definedness of (VADD md)(FINSUM Fc, r.x):
    (fact 'interval-in-set 1 'n) (fact 'interval-card-in-nn 1 'n)
    (fact 'finsum-type p2-vag '(INTERVAL 1 n) p2-Fc)
    (mac-h 'mvag-carr (list 'IN (p2-sum p2-Fc '(INTERVAL 1 n)) p2-vc))   ; -> in VEC md
    (fact 'module-act-type 'md 'r 'x)
    (fact 'module-vadd-type 'md (p2-sum p2-Fc '(INTERVAL 1 n)) '((ACT md) r x))
    (rfl)))

(qed 'lincomb-snoc)
(topic! 'lincomb-snoc 'algebra)


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
(topic! 'submodule-intersection 'algebra)
(topic! 'submodule-vzero-in 'algebra)
(topic! 'submodule-vadd-closed 'algebra)
(topic! 'submodule-vneg-closed 'algebra)
(topic! 'submodule-act-closed 'algebra)


;;; ===================================================================
;;; BRICK 6:  the zero-dimension matrix spaces are inhabited
;;; ===================================================================
(define (p2-empty-close! v)              ; close a goal from (IN v (INTERVAL 1 0)) in ctx
  (fact 'interval-lo 1 0 v) (fact 'interval-hi 1 0 v)
  (fact 'interval-elt-in-nn 1 0 v) (fact 'nn-not-le-zero-pos v)
  (ai (list 'NOT (list '<= v 0))))

;; A 1-by-0 matrix: tabulate one empty row.  matof-in-mat (guarded on its two
;; dimensions being natural since 2026-09-16) is reached by dk-matof!, and its
;; entry hypothesis is vacuous: there is no column index in [1,0].
(sp (make-wff '(FORALL X (FORSOME P (IN P (MAT 1 0 X))))))
(di)
(fact 'nn-one-in) (fact 'nn-zero-in)
(ew '(MATOF 1 0 (VNB-LAMBDA (LIST i_ j_) (CARTESIAN (INTERVAL 1 1) (INTERVAL 1 0)) i_)))
(dk-matof!)
(p2-di*)                                               ; i (in [1,1]); j (in [1,0])
(p2-empty-close! (cadr (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                                 (equal? (caddr f) '(INTERVAL 1 0))))
                                "j in [1,0]")))
(qed 'mat-1-0-nonempty)
(topic! 'mat-1-0-nonempty 'plumbing)

;; A 0-by-1 matrix: the empty tuple.  Before 2026-09-16 no matrix with no rows
;; had a column count at all, and this was UNPROVABLE; now [] is in MAT(0,n,X)
;; for every natural n (nil-in-mat).
(sp (make-wff '(FORALL X (FORSOME P (IN P (MAT 0 1 X))))))
(di)
(ew '(LIST))
(fact 'nn-one-in)
(fact 'nil-in-mat 1 (cadddr (caddr (p2-goal))))        ; goal (IN (LIST) (MAT 0 1 X))
(ass)
(qed 'mat-0-1-nonempty)
(topic! 'mat-0-1-nonempty 'plumbing)
