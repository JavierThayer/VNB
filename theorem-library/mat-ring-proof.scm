;;; mat-ring-proof.scm -- the n-by-n matrices over a ring form a ring.
;;;
;;;   IS-RING(a), n in NN  |-  IS-RING(MAT-RING(a,n))
;;;
;;; Headline top-down assembly: unfold the auto-generated IS-RING iff into its
;;; 14 conjuncts (a length clause, 6 slot typings, 7 property clauses), split
;;; them, and discharge each by reducing MAT-RING's slot accessors to the matrix
;;; ops (the mat-ring-* read-off macetes, matrix.scm) and citing the matching
;;; matrix-ring axiom.  Rests only on warranted bricks: the read-offs/typings
;;; (matrix.scm) and the matrix algebra axioms (matadd-*, matmul-*, identmat-*),
;;; the mathematical content earmarked to be discharged separately.
;;;
;;; See matrix.scm for why the read-offs must be warranted (accessor macetes are
;;; name-keyed and last-write-wins; the kernel has no recursive LENGTH; lam-t
;;; types only single-binder lambdas).

;; ---- local proof helpers (mr- prefix; do not leak generic names) ----
(define (mr-pg) (wff-formula (sequent-node-assertion (proof-state-focus *ps*))))
(define (mr-asms) (map wff-formula (sequent-node-assumptions (proof-state-focus *ps*))))
(define (mr-leaves)
  (filter (lambda (nd) (and (not (sequent-node-grounded? nd))
                            (null? (sequent-node-in-arrows nd))))
          (dg-ungrounded-nodes (proof-state-dg *ps*))))
(define (mr-goal-of l) (wff-formula (sequent-node-assertion l)))
(define (mr-focus! pred)
  (let lp ((ls (mr-leaves)))
    (cond ((null? ls) (error "mat-ring-proof: no open leaf matches predicate"))
          ((pred (mr-goal-of (car ls))) (set-proof-state-focus! *ps* (car ls)) (car ls))
          (else (lp (cdr ls))))))
(define (mr-di*) (let lp () (let* ((g (mr-pg)) (h (and (pair? g) (car g))))
                              (when (memq h '(FORALL IMPLIES)) (di) (lp)))))
;; leaf predicate: goal head H, and its first argument's head OPH
(define (mr-is? h oph)
  (lambda (g) (and (pair? g) (eq? (car g) h)
                   (let ((a1 (cadr g))) (and (pair? a1) (eq? (car a1) oph))))))
;; binder vars introduced by di, from the (IN v (MAT ...)) asms, in intro order
;; (robust against di renaming u -> u_198, the fresh-var gotcha)
(define (mr-vbind)
  (filter-map (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                (pair? (caddr f)) (eq? (car (caddr f)) 'MAT) (cadr f))) (mr-asms)))
;; rewrite CARR(MAT-RING a n) -> MAT(n,n,CARR a) via the read-off macete
(define (mr-rcarr) (mac 'mat-ring-carr))
;; reduce op accessors on MAT-RING to the matrix ops via the slot read-offs,
;; then beta-reduce the exposed lambda applications
(define (mr-rops . readoffs)
  (for-each (lambda (r) (mac r)) readoffs) (lam-b))
(define (mr-decomposable? l)
  (let ((g (mr-goal-of l))) (and (pair? g) (memq (car g) '(FORALL IMPLIES AND)))))
;; Fully discharge a property conjunct: decompose it into its atomic equation
;; leaves (intro every binder, split every AND -- no hand-counted di's), then
;; close each leaf by facting all candidate lemmas (parameterised by that leaf's
;; own captured binders) and ass.  facters: list of (vs -> fact ...) procedures.
(define (mr-close-conj facters)
  (let* ((focus  (proof-state-focus *ps*))
         (before (filter (lambda (l) (not (eq? l focus))) (mr-leaves)))
         (mine   (lambda () (filter (lambda (l) (not (memq l before))) (mr-leaves)))))
    (let loop ()
      (let ((ds (filter mr-decomposable? (mine))))
        (when (pair? ds) (set-proof-state-focus! *ps* (car ds)) (di) (loop))))
    (for-each (lambda (lf)
                (set-proof-state-focus! *ps* lf)
                (let ((vs (mr-vbind))) (for-each (lambda (f) (f vs)) facters))
                (ass))
              (mine))))
(define (mr-disch pred thunk) (mr-focus! pred) (thunk))

;; ========================================================================
(sp '(FORALL a (IMPLIES (IS-RING a) (FORALL n (IMPLIES (IN n NN)
       (IS-RING (MAT-RING a n)))))))
(mr-di*)                        ; asms: IS-RING a, IN n NN ; goal IS-RING(MAT-RING a n)
(mac 'IS-RING)                  ; -> the 14-conjunct AND

;; split the top-level (right-nested) AND into 14 conjunct leaves
(let lp ()
  (let ((l (let ((m (filter (lambda (nd) (let ((g (mr-goal-of nd)))
                                           (and (pair? g) (eq? (car g) 'AND))))
                            (mr-leaves))))
             (and (pair? m) (car m)))))
    (when l (set-proof-state-focus! *ps* l) (di) (lp))))

;; ---- 1. length(mat-ring(a,n)) = 6 ----
(mr-disch (mr-is? '= 'LENGTH) (lambda ()
  (fact 'mat-ring-length 'a 'n)(ass)))

;; ---- 2. carr(mat-ring(a,n)) in set ----
(mr-disch (mr-is? 'IN 'CARR) (lambda ()
  (mr-rcarr)(fact 'ring-carr-in-set 'a)(fact 'mat-is-set '(CARR a) 'n 'n)(ass)))

;; ---- 3. add(mat-ring) in FUN ----
(mr-disch (mr-is? 'IN 'ADD) (lambda ()
  (mr-rcarr)(mac 'mat-ring-add)(fact 'mat-ring-add-fun 'a 'n)(ass)))

;; ---- 4. mul(mat-ring) in FUN ----
(mr-disch (mr-is? 'IN 'MUL) (lambda ()
  (mr-rcarr)(mac 'mat-ring-mul)(fact 'mat-ring-mul-fun 'a 'n)(ass)))

;; ---- 5. neg(mat-ring) in FUN  (single-binder: genuine via lam-t) ----
(mr-disch (mr-is? 'IN 'NEG) (lambda ()
  (mr-rcarr)(mac 'mat-ring-neg)(lam-t)(di)
  (let ((v (list-ref (cadr (mr-pg)) 2))) (fact 'matneg-type 'a 'n 'n v))(ass)))

;; ---- 6. zero(mat-ring) in carr(mat-ring) ----
(mr-disch (mr-is? 'IN 'ZERO) (lambda ()
  (mr-rcarr)(mac 'mat-ring-zero)(fact 'zeromat-type 'a 'n 'n)(ass)))

;; ---- 7. one(mat-ring) in carr(mat-ring) ----
(mr-disch (mr-is? 'IN 'ONE) (lambda ()
  (mr-rcarr)(mac 'mat-ring-one)(fact 'identmat-type 'a 'n)(ass)))

;; ---- 8. is-associative(add) ----
(mr-disch (mr-is? 'is-associative 'ADD) (lambda ()
  (mac 'is-associative)(mr-rcarr)(mr-rops 'mat-ring-add)
  (mr-close-conj (list (lambda (v) (fact 'matadd-assoc 'a 'n 'n (car v) (cadr v) (caddr v)))))))

;; ---- 9. is-commutative(add) ----
(mr-disch (mr-is? 'is-commutative 'ADD) (lambda ()
  (mac 'is-commutative)(mr-rcarr)(mr-rops 'mat-ring-add)
  (mr-close-conj (list (lambda (v) (fact 'matadd-comm 'a 'n 'n (car v) (cadr v)))))))

;; ---- 10. is-identity(add, zero) ----
(mr-disch (mr-is? 'is-identity 'ADD) (lambda ()
  (mac 'is-identity)(mr-rcarr)(mr-rops 'mat-ring-add 'mat-ring-zero)
  (mr-close-conj (list (lambda (v) (fact 'matadd-zero-left  'a 'n 'n (car v)))    ; 0+u=u
                       (lambda (v) (fact 'matadd-zero-right 'a 'n 'n (car v))))))) ; u+0=u

;; ---- 11. has-inverses(add, zero, neg) ----
(mr-disch (mr-is? 'has-inverses 'ADD) (lambda ()
  (mac 'has-inverses)(mr-rcarr)(mr-rops 'mat-ring-add 'mat-ring-neg 'mat-ring-zero)
  (mr-close-conj (list (lambda (v) (fact 'matadd-neg-left  'a 'n 'n (car v)))     ; (-u)+u=0
                       (lambda (v) (fact 'matadd-neg-right 'a 'n 'n (car v))))))) ; u+(-u)=0

;; ---- 12. is-associative(mul) ----
(mr-disch (mr-is? 'is-associative 'MUL) (lambda ()
  (mac 'is-associative)(mr-rcarr)(mr-rops 'mat-ring-mul)
  (mr-close-conj (list (lambda (v) (fact 'matmul-assoc 'a 'n 'n 'n 'n (car v) (cadr v) (caddr v)))))))

;; ---- 13. is-identity(mul, one) ----
(mr-disch (mr-is? 'is-identity 'MUL) (lambda ()
  (mac 'is-identity)(mr-rcarr)(mr-rops 'mat-ring-mul 'mat-ring-one)
  (mr-close-conj (list (lambda (v) (fact 'identmat-left-identity  'a 'n 'n (car v)))   ; I u = u
                       (lambda (v) (fact 'identmat-right-identity 'a 'n 'n (car v))))))) ; u I = u

;; ---- 14. is-distributive(add, mul) ----
(mr-disch (mr-is? 'is-distributive 'ADD) (lambda ()
  (mac 'is-distributive)(mr-rcarr)(mr-rops 'mat-ring-add 'mat-ring-mul)
  (mr-close-conj (list (lambda (v) (fact 'matmul-left-dist  'a 'n 'n 'n (car v) (cadr v) (caddr v)))  ; u(v+w)
                       (lambda (v) (fact 'matmul-right-dist 'a 'n 'n 'n (car v) (cadr v) (caddr v))))))) ; (u+v)w

(qed 'mat-ring-is-ring)
(category! 'mat-ring-is-ring 'algebra)
