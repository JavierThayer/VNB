;;; la-z6-mpoly.scm -- R[x_1, ..., x_n] and linear algebra Proposition 3.15 (LA-Z6, 2026-10-25).
;;;
;;; THE SOURCE.  The user's linear-algebra notes, section "Determinants": a permutation of a set X is a
;;; bijection X -> X; sigma . p is p with sigma applied to its indeterminates; Proposition 3.15: "p |->
;;; sigma . p is an isomorphism of the ring R[x_1, x_2, ..., x_n]" (R a commutative ring there).
;;;
;;; VOCABULARY: la-z6-vocab.scm (MULTI-INDEX-MONOID, MI-ADD, MI-ZERO, MI-REINDEX, MPOLY, VAR-PERMUTE,
;;; IS-ISO-RING, MONALG-PULLBACK).
;;;
;;; THE PROOF.  The multi-indices on a set X form a commutative monoid under pointwise addition
;;; (multi-index-monoid-is-comm-monoid, by function extensionality and the NN laws).  For a bijection s
;;; of X with inverse t = INVERSE-BIJ(s, X, X), b |-> b o s preserves + and 0 and has the two-sided
;;; inverse b |-> b o t.  So it is a monoid automorphism, and monalg-pullback-iso
;;; (theorem-library/la-z6-pullback) makes p |-> sigma . p a ring automorphism of MONALG(R, M).
;;; HEADLINE: var-permute-is-ring-iso (3.15), stated for any ring R (the notes take R commutative), with
;;; sigma a bijection of [1, n] (the notes' definition of a permutation).  Also mpoly-is-ring and
;;; mpoly-is-commutative-ring (R[x_1, ..., x_n] is a ring; commutative when R is).
;;;
;;; LOAD WINDOW: after theorem-library/la-z6-pullback (monalg-pullback-iso) and after rake-monalg-comm
;;; (load.scm:1746, primary tree of 2026-10-25; monalg-comm); the other citations are early: inverse-bij-*
;;; (rake-inverse-bij, 973), comm-monoid-is-monoid (subtype-laws, 1060), interval-in-set (727), nn-add-*
;;; (number-systems), fun-set-iff (library).  Nothing cites it.
;;; Library: algebra (it cites nothing of linear algebra; 3.15 is a statement about polynomial rings).
;;; No axiom, support or stamp.  Helper prefix: lz6m-.  Statement variables ixs_ (the index set),
;;; s_ t_ (the permutation and its inverse), u_ v_ w_ b_ (multi-indices), r_ n_ (the ring, the number of
;;; indeterminates); binder mpq_ (the pointwise universal).

(define (lz6m-done! name)
  (if (not (proof-done? *ps*))
      (begin
        (display "\n*** la-z6-mpoly: ") (display name) (display " did NOT close.\n")
        (for-each (lambda (l)
                    (display ";;   leaf: ")
                    (display (expression->string (dk-goal-of l))) (newline))
                  (dk-open-leaves))))
  (qed name))

(define lz6m-F '(FUN ixs_ NN))
(define lz6m-MIM '(MULTI-INDEX-MONOID ixs_))
(define lz6m-HX '(IN ixs_ SET))
(define (lz6m-ty v) (list 'IN v lz6m-F))
(define (lz6m-add u v) (list 'MI-ADD 'ixs_ u v))
(define (lz6m-re s b) (list 'MI-REINDEX 'ixs_ s b))
(define lz6m-zero '(MI-ZERO ixs_))
(define (lz6m-setup!)
  (dk-peel!)
  (if (not (dk-asm? '(IN NN SET))) (fact 'nn-is-set)))
;; b(j) in NN from b in FUN(ixs_, NN), j in ixs_
(define (lz6m-val! b j)
  (if (not (dk-asm? (list 'IN (list b j) 'NN))) (fact 'fun-apply-type-c b 'ixs_ 'NN j)))
(define (lz6m-ix! s j)
  (if (not (dk-asm? (list 'IN (list s j) 'ixs_))) (fact 'fun-apply-type-c s 'ixs_ 'ixs_ j)))
;; rewrite the goal by the equation E (one recording call per form; see la-z6-pullback's lz6p-sub!)
(define (lz6m-sub! e) (subst (list '= (cadr e) (caddr e))))

;;; =====================================================================
;;; Read-offs of the multi-index monoid, and the pointwise values.
;;; =====================================================================
(define (lz6m-readoff! name acc rhs)
  (dk-sp-qed! (make-wff (list 'FORALL 'ixs_ (list 'IMPLIES lz6m-HX (list '== (list acc lz6m-MIM) rhs))))
    (lambda () (dk-peel!) (mac 'MULTI-INDEX-MONOID) (slot acc) (nth-r) (qrfl))
    name)
  (topic! name 'algebra))
(lz6m-readoff! 'multi-index-monoid-carr 'CARR lz6m-F)
(lz6m-readoff! 'multi-index-monoid-opr 'OPR
  (list 'VNB-LAMBDA '(LIST miu_ miv_) (list 'CARTESIAN lz6m-F lz6m-F) '(MI-ADD ixs_ miu_ miv_)))
(lz6m-readoff! 'multi-index-monoid-iden 'IDEN lz6m-zero)

(sp (make-wff (forall-guarded '(ixs_ u_ v_ j_) (list '(IN j_ ixs_))
  (list '== (list (lz6m-add 'u_ 'v_) 'j_) '(+ (u_ j_) (v_ j_))))))
(dk-peel!) (mac 'MI-ADD) (dk-lam-b!) (if (not (proof-done? *ps*)) (qrfl))
(lz6m-done! 'mi-add-apply)
(topic! 'mi-add-apply 'algebra)

(sp (make-wff (forall-guarded '(ixs_ j_) (list '(IN j_ ixs_))
  (list '== (list lz6m-zero 'j_) 0))))
(dk-peel!) (mac 'MI-ZERO) (dk-lam-b!) (if (not (proof-done? *ps*)) (qrfl))
(lz6m-done! 'mi-zero-apply)
(topic! 'mi-zero-apply 'algebra)

(sp (make-wff (forall-guarded '(ixs_ s_ b_ j_) (list '(IN j_ ixs_))
  (list '== (list (lz6m-re 's_ 'b_) 'j_) '(b_ (s_ j_))))))
(dk-peel!) (mac 'MI-REINDEX) (dk-lam-b!) (if (not (proof-done? *ps*)) (qrfl))
(lz6m-done! 'mi-reindex-apply)
(topic! 'mi-reindex-apply 'algebra)

;;; =====================================================================
;;; Typings.
;;; =====================================================================
(sp (make-wff (forall-guarded '(ixs_ u_ v_) (list lz6m-HX (lz6m-ty 'u_) (lz6m-ty 'v_))
  (lz6m-ty (lz6m-add 'u_ 'v_)))))
(lz6m-setup!)
(mac 'MI-ADD)
(dk-lam-type!
  (lambda ()
    (let ((j (dk-di-var!)))
      (lz6m-val! 'u_ j) (lz6m-val! 'v_ j)
      (dk-have! (list 'AND (list 'IN (list 'u_ j) 'NN) (list 'IN (list 'v_ j) 'NN)) (lambda () (dk-conj-close! (lambda () (ass)))))
      (fact 'nn-add-closed (list 'u_ j) (list 'v_ j))
      (ass)))
  (lambda () (ass)))
(lz6m-done! 'mi-add-fun)
(topic! 'mi-add-fun 'algebra)

(sp (make-wff (forall-guarded '(ixs_) (list lz6m-HX) (lz6m-ty lz6m-zero))))
(lz6m-setup!)
(mac 'MI-ZERO)
(dk-lam-type! (lambda () (dk-di-var!) (arith)) (lambda () (ass)))
(lz6m-done! 'mi-zero-fun)
(topic! 'mi-zero-fun 'algebra)

(sp (make-wff (forall-guarded '(ixs_ s_ b_) (list lz6m-HX '(IN s_ (FUN ixs_ ixs_)) (lz6m-ty 'b_))
  (lz6m-ty (lz6m-re 's_ 'b_)))))
(lz6m-setup!)
(mac 'MI-REINDEX)
(dk-lam-type!
  (lambda ()
    (let ((j (dk-di-var!)))
      (lz6m-ix! 's_ j)
      (lz6m-val! 'b_ (list 's_ j))
      (ass)))
  (lambda () (ass)))
(lz6m-done! 'mi-reindex-fun)
(topic! 'mi-reindex-fun 'algebra)

;;; =====================================================================
;;; The monoid laws, by function extensionality.
;;; =====================================================================
;; land (= LHS RHS), both in FUN(ixs_, NN) in context; PTWISE proves (= (LHS j) (RHS j)) for typed j
(define (lz6m-ext! lhs rhs ptwise)
  (dk-fun-ext! lhs rhs 'ixs_ 'NN #f #f ptwise))

(sp (make-wff (forall-guarded '(ixs_ u_ v_ w_) (list lz6m-HX (lz6m-ty 'u_) (lz6m-ty 'v_) (lz6m-ty 'w_))
  (list '= (lz6m-add (lz6m-add 'u_ 'v_) 'w_) (lz6m-add 'u_ (lz6m-add 'v_ 'w_))))))
(lz6m-setup!)
(fact 'mi-add-fun 'ixs_ 'u_ 'v_) (fact 'mi-add-fun 'ixs_ 'v_ 'w_)
(fact 'mi-add-fun 'ixs_ (lz6m-add 'u_ 'v_) 'w_) (fact 'mi-add-fun 'ixs_ 'u_ (lz6m-add 'v_ 'w_))
(lz6m-ext! (lz6m-add (lz6m-add 'u_ 'v_) 'w_) (lz6m-add 'u_ (lz6m-add 'v_ 'w_))
  (lambda (j)
    (lz6m-val! 'u_ j) (lz6m-val! 'v_ j) (lz6m-val! 'w_ j)
    (begin (lz6m-sub! (dk-cite! 'mi-add-apply 'ixs_ (lz6m-add 'u_ 'v_) 'w_ j))
           (lz6m-sub! (dk-cite! 'mi-add-apply 'ixs_ 'u_ 'v_ j))
           (lz6m-sub! (dk-cite! 'mi-add-apply 'ixs_ 'u_ (lz6m-add 'v_ 'w_) j))
           (lz6m-sub! (dk-cite! 'mi-add-apply 'ixs_ 'v_ 'w_ j)))
    (dk-have! (list 'AND (list 'IN (list 'u_ j) 'NN) (list 'AND (list 'IN (list 'v_ j) 'NN) (list 'IN (list 'w_ j) 'NN)))
      (lambda () (dk-conj-close! (lambda () (ass)))))
    (fact 'nn-add-assoc (list 'u_ j) (list 'v_ j) (list 'w_ j))
    (ass)))
(lz6m-done! 'mi-add-assoc)
(topic! 'mi-add-assoc 'algebra)

(sp (make-wff (forall-guarded '(ixs_ u_ v_) (list lz6m-HX (lz6m-ty 'u_) (lz6m-ty 'v_))
  (list '= (lz6m-add 'u_ 'v_) (lz6m-add 'v_ 'u_)))))
(lz6m-setup!)
(fact 'mi-add-fun 'ixs_ 'u_ 'v_) (fact 'mi-add-fun 'ixs_ 'v_ 'u_)
(lz6m-ext! (lz6m-add 'u_ 'v_) (lz6m-add 'v_ 'u_)
  (lambda (j)
    (lz6m-val! 'u_ j) (lz6m-val! 'v_ j)
    (begin (lz6m-sub! (dk-cite! 'mi-add-apply 'ixs_ 'u_ 'v_ j))
           (lz6m-sub! (dk-cite! 'mi-add-apply 'ixs_ 'v_ 'u_ j)))
    (dk-have! (list 'AND (list 'IN (list 'u_ j) 'NN) (list 'IN (list 'v_ j) 'NN)) (lambda () (dk-conj-close! (lambda () (ass)))))
    (fact 'nn-add-comm (list 'u_ j) (list 'v_ j))
    (ass)))
(lz6m-done! 'mi-add-comm)
(topic! 'mi-add-comm 'algebra)

(sp (make-wff (forall-guarded '(ixs_ u_) (list lz6m-HX (lz6m-ty 'u_))
  (list '= (lz6m-add 'u_ lz6m-zero) 'u_))))
(lz6m-setup!)
(fact 'mi-zero-fun 'ixs_)
(fact 'mi-add-fun 'ixs_ 'u_ lz6m-zero)
(lz6m-ext! (lz6m-add 'u_ lz6m-zero) 'u_
  (lambda (j)
    (lz6m-val! 'u_ j)
    (begin (lz6m-sub! (dk-cite! 'mi-add-apply 'ixs_ 'u_ lz6m-zero j))
           (lz6m-sub! (dk-cite! 'mi-zero-apply 'ixs_ j)))
    (fact 'nn-add-zero (list 'u_ j))
    (ass)))
(lz6m-done! 'mi-add-zero-right)
(topic! 'mi-add-zero-right 'algebra)

(sp (make-wff (forall-guarded '(ixs_ u_) (list lz6m-HX (lz6m-ty 'u_))
  (list '= (lz6m-add lz6m-zero 'u_) 'u_))))
(lz6m-setup!)
(fact 'mi-zero-fun 'ixs_)
(subst (dk-cite! 'mi-add-comm 'ixs_ lz6m-zero 'u_))
(fact 'mi-add-zero-right 'ixs_ 'u_)
(ass)
(lz6m-done! 'mi-add-zero-left)
(topic! 'mi-add-zero-left 'algebra)

;;; =====================================================================
;;; The multi-indices on a set form a commutative monoid.
;;; =====================================================================
(define (lz6m-peel-typed!)            ; peel; return the eigenvariables typed in FUN(ixs_, NN), in order
  (map cadr (filter (lambda (f) (and (pair? f) (eq? (car f) 'IN) (equal? (caddr f) lz6m-F))) (dk-peel!))))
(define (lz6m-cm-clause!)
  (let ((g (dk-goal)))
    (cond
      ((and (dk-head-is? g '=) (dk-head-is? (cadr g) 'LENGTH))
       (mac 'MULTI-INDEX-MONOID) (len-r) (rfl))
      ((equal? g (list 'IN lz6m-F 'SET))
       (mac 'fun-set-iff) (dk-conj-close! (lambda () (ass))))
      ((equal? g (list 'IN lz6m-zero lz6m-F))
       (fact 'mi-zero-fun 'ixs_) (ass))
      ((dk-head-is? g 'IN)                 ; the OPR typing
       (dk-lam-type!
         (lambda ()
           (dk-peel!)
           (let* ((t (cadr (dk-goal))))      ; (MI-ADD ixs_ u v)
             (fact 'mi-add-fun 'ixs_ (caddr t) (cadddr t))
             (ass)))
         (lambda () (mac 'cartesian-set-iff) (dk-conj-close! (lambda () (mac 'fun-set-iff) (dk-conj-close! (lambda () (ass))))))))
      ((dk-head-is? g 'is-associative)
       (mac 'is-associative)
       (let* ((vs (lz6m-peel-typed!)) (u (car vs)) (v (cadr vs)) (w (caddr vs)))
         (fact 'mi-add-fun 'ixs_ u v) (fact 'mi-add-fun 'ixs_ v w)
         (dk-lam-b!)
         (fact 'mi-add-assoc 'ixs_ u v w)
         (ass)))
      ((dk-head-is? g 'is-commutative)
       (mac 'is-commutative)
       (let* ((vs (lz6m-peel-typed!)))
         (dk-lam-b!)
         (fact 'mi-add-comm 'ixs_ (car vs) (cadr vs))
         (ass)))
      ((dk-head-is? g 'is-identity)
       (mac 'is-identity)
       (let* ((vs (lz6m-peel-typed!)))
         (fact 'mi-zero-fun 'ixs_)
         (dk-conj-close!
           (lambda ()
             (dk-lam-b!)
             (fact 'mi-add-zero-left 'ixs_ (car vs))
             (fact 'mi-add-zero-right 'ixs_ (car vs))
             (ass)))))
      (#t (error "lz6m-cm-clause!: unexpected conjunct" (expression->string g))))))

(sp (make-wff (forall-guarded '(ixs_) (list lz6m-HX) (list 'IS-COMM-MONOID lz6m-MIM))))
(lz6m-setup!)
(mac 'IS-COMM-MONOID)
(mac 'multi-index-monoid-carr) (mac 'multi-index-monoid-opr) (mac 'multi-index-monoid-iden)
(dk-conj-close! lz6m-cm-clause!)
(lz6m-done! 'multi-index-monoid-is-comm-monoid)
(topic! 'multi-index-monoid-is-comm-monoid 'algebra)
(gloss! 'multi-index-monoid-is-comm-monoid
  "The multi-indices on a set X -- the functions X -> NN under pointwise addition, with the zero function
   as identity -- form a commutative monoid.")

;;; =====================================================================
;;; Reindexing a multi-index along s: b |-> b o s.
;;; =====================================================================
(define lz6m-Hs '(IN s_ (FUN ixs_ ixs_)))
(sp (make-wff (forall-guarded '(ixs_ s_ u_ v_) (list lz6m-HX lz6m-Hs (lz6m-ty 'u_) (lz6m-ty 'v_))
  (list '= (lz6m-re 's_ (lz6m-add 'u_ 'v_)) (lz6m-add (lz6m-re 's_ 'u_) (lz6m-re 's_ 'v_))))))
(lz6m-setup!)
(fact 'mi-add-fun 'ixs_ 'u_ 'v_)
(fact 'mi-reindex-fun 'ixs_ 's_ (lz6m-add 'u_ 'v_))
(fact 'mi-reindex-fun 'ixs_ 's_ 'u_) (fact 'mi-reindex-fun 'ixs_ 's_ 'v_)
(fact 'mi-add-fun 'ixs_ (lz6m-re 's_ 'u_) (lz6m-re 's_ 'v_))
(lz6m-ext! (lz6m-re 's_ (lz6m-add 'u_ 'v_)) (lz6m-add (lz6m-re 's_ 'u_) (lz6m-re 's_ 'v_))
  (lambda (j)
    (let ((sj (list 's_ j)))
      (lz6m-ix! 's_ j)
      (lz6m-val! 'u_ sj) (lz6m-val! 'v_ sj)
      (begin (lz6m-sub! (dk-cite! 'mi-reindex-apply 'ixs_ 's_ (lz6m-add 'u_ 'v_) j))
             (lz6m-sub! (dk-cite! 'mi-add-apply 'ixs_ 'u_ 'v_ sj))
             (lz6m-sub! (dk-cite! 'mi-add-apply 'ixs_ (lz6m-re 's_ 'u_) (lz6m-re 's_ 'v_) j))
             (lz6m-sub! (dk-cite! 'mi-reindex-apply 'ixs_ 's_ 'u_ j))
             (lz6m-sub! (dk-cite! 'mi-reindex-apply 'ixs_ 's_ 'v_ j)))
      (rfl))))
(lz6m-done! 'mi-reindex-add)
(topic! 'mi-reindex-add 'algebra)

(sp (make-wff (forall-guarded '(ixs_ s_) (list lz6m-HX lz6m-Hs)
  (list '= (lz6m-re 's_ lz6m-zero) lz6m-zero))))
(lz6m-setup!)
(fact 'mi-zero-fun 'ixs_)
(fact 'mi-reindex-fun 'ixs_ 's_ lz6m-zero)
(lz6m-ext! (lz6m-re 's_ lz6m-zero) lz6m-zero
  (lambda (j)
    (lz6m-ix! 's_ j)
    (begin (lz6m-sub! (dk-cite! 'mi-reindex-apply 'ixs_ 's_ lz6m-zero j))
           (lz6m-sub! (dk-cite! 'mi-zero-apply 'ixs_ (list 's_ j)))
           (lz6m-sub! (dk-cite! 'mi-zero-apply 'ixs_ j)))
    (rfl)))
(lz6m-done! 'mi-reindex-zero)
(topic! 'mi-reindex-zero 'algebra)

;; (b o s) o t = b when s(t j) = j on ixs_
(define lz6m-Hst '(FORALL mpq_ (IMPLIES (IN mpq_ ixs_) (= (s_ (t_ mpq_)) mpq_))))
(sp (make-wff (forall-guarded '(ixs_ s_ t_ b_) (list lz6m-HX lz6m-Hs '(IN t_ (FUN ixs_ ixs_)) lz6m-Hst (lz6m-ty 'b_))
  (list '= (lz6m-re 't_ (lz6m-re 's_ 'b_)) 'b_))))
(lz6m-setup!)
(fact 'mi-reindex-fun 'ixs_ 's_ 'b_)
(fact 'mi-reindex-fun 'ixs_ 't_ (lz6m-re 's_ 'b_))
(lz6m-ext! (lz6m-re 't_ (lz6m-re 's_ 'b_)) 'b_
  (lambda (j)
    (lz6m-ix! 't_ j)
    (lz6m-val! 'b_ j)
    (begin (lz6m-sub! (dk-cite! 'mi-reindex-apply 'ixs_ 't_ (lz6m-re 's_ 'b_) j))
           (lz6m-sub! (dk-cite! 'mi-reindex-apply 'ixs_ 's_ 'b_ (list 't_ j)))
           (lz6m-sub! (dk-apply! lz6m-Hst j)))
    (rfl)))
(lz6m-done! 'mi-reindex-inverse)
(topic! 'mi-reindex-inverse 'algebra)

;;; =====================================================================
;;; A permutation of the index set acts on MONALG(R, multi-indices) by ring automorphisms.
;;; =====================================================================
(define (lz6m-RH s) (list 'VNB-LAMBDA 'mib_ lz6m-F (lz6m-re s 'mib_)))
(define lz6m-tau '(INVERSE-BIJ s_ ixs_ ixs_))
(define lz6m-CM (list 'CARR lz6m-MIM))
(define (lz6m-carr-lane! k)            ; rewrite the multi-index accessors in the goal, then K
  (if (dk-contains? (dk-goal) 'CARR) (mac 'multi-index-monoid-carr))
  (if (dk-contains? (dk-goal) 'OPR) (mac 'multi-index-monoid-opr))
  (if (dk-contains? (dk-goal) 'IDEN) (mac 'multi-index-monoid-iden))
  (k))
;; the inverse law k(h u) = u on the multi-indices, from the pointwise law on ixs_
(define (lz6m-inv-prover! h k pw)
  (lambda ()
    (lz6m-carr-lane!
      (lambda ()
        (let ((u (dk-di-var!)))
          (fact 'mi-reindex-fun 'ixs_ h u)
          (dk-lam-b!)
          (fact 'mi-reindex-inverse 'ixs_ h k u)
          (ass))))))
(define (lz6m-iso-prover ante)
  (cond
    ((and (dk-head-is? ante 'IN) (dk-head-is? (caddr ante) 'FUN))
     (lambda ()
       (lz6m-carr-lane!
         (lambda ()
           (dk-lam-type!
             (lambda ()
               (let ((v (dk-di-var!)))
                 (fact 'mi-reindex-fun 'ixs_ (if (equal? (cadr ante) (lz6m-RH 's_)) 's_ lz6m-tau) v)
                 (ass)))
             (lambda () (mac 'fun-set-iff) (dk-conj-close! (lambda () (ass)))))))))
    ((and (dk-head-is? ante 'FORALL) (dk-contains? ante 'OPR))
     (lambda ()
       (lz6m-carr-lane!
         (lambda ()
           (let* ((vs (lz6m-peel-typed!)) (u (car vs)) (v (cadr vs)))
             (fact 'mi-add-fun 'ixs_ u v)
             (fact 'mi-reindex-fun 'ixs_ 's_ u) (fact 'mi-reindex-fun 'ixs_ 's_ v)
             (fact 'mi-reindex-fun 'ixs_ 's_ (lz6m-add u v))
             (dk-lam-b!)
             (fact 'mi-reindex-add 'ixs_ 's_ u v)
             (ass))))))
    ((dk-head-is? ante 'FORALL)            ; an inverse law: which way round?
     (let* ((body (caddr (caddr ante)))       ; (= (k (h u)) u)
            (outer (car (cadr body))))
       (if (equal? outer (lz6m-RH lz6m-tau))
           (lambda () ((lz6m-inv-prover! 's_ lz6m-tau 'right)))
           (lambda () ((lz6m-inv-prover! lz6m-tau 's_ 'left))))))
    (#t                                    ; RH(IDEN) = IDEN
     (lambda ()
       (lz6m-carr-lane!
         (lambda ()
           (fact 'mi-zero-fun 'ixs_)
           (fact 'mi-reindex-fun 'ixs_ 's_ lz6m-zero)
           (dk-lam-b!)
           (fact 'mi-reindex-zero 'ixs_ 's_)
           (ass)))))))

(sp (make-wff (forall-guarded '(r_ ixs_ s_) (list '(IS-RING r_) lz6m-HX '(IN s_ (BIJECTION ixs_ ixs_)))
  (list 'IS-ISO-RING (list 'MONALG 'r_ lz6m-MIM) (list 'MONALG 'r_ lz6m-MIM)
        (list 'VNB-LAMBDA 'pbf_ (list 'FINSUPP 'r_ lz6m-MIM) (list 'MONALG-PULLBACK 'r_ lz6m-MIM (lz6m-RH 's_) 'pbf_))))))
(lz6m-setup!)
(fact 'bijection-in-fun 'ixs_ 'ixs_ 's_)
(fact 'inverse-bij-in-fun 'ixs_ 'ixs_ 's_)
(fact 'multi-index-monoid-is-comm-monoid 'ixs_)
(fact 'comm-monoid-is-monoid lz6m-MIM)
;; the two pointwise inverse laws on ixs_
(dk-have! (list 'FORALL 'mpq_ (list 'IMPLIES '(IN mpq_ ixs_) (list '= (list 's_ (list lz6m-tau 'mpq_)) 'mpq_)))
  (lambda () (let ((j (dk-di-var!))) (fact 'inverse-bij-right 'ixs_ 'ixs_ 's_ j) (ass))))
(dk-have! (list 'FORALL 'mpq_ (list 'IMPLIES '(IN mpq_ ixs_) (list '= (list lz6m-tau (list 's_ 'mpq_)) 'mpq_)))
  (lambda () (let ((j (dk-di-var!))) (fact 'inverse-bij-left 'ixs_ 'ixs_ 's_ j) (ass))))
(let ((ch (dk-cite! 'monalg-pullback-iso 'r_ lz6m-MIM (lz6m-RH 's_) (lz6m-RH lz6m-tau))))
  (dk-chain! ch lz6m-iso-prover)
  (ass))
(lz6m-done! 'multi-index-reindex-is-ring-iso)
(topic! 'multi-index-reindex-is-ring-iso 'algebra)
(gloss! 'multi-index-reindex-is-ring-iso
  "For a bijection s of a set X, the substitution of variables p |-> (b |-> p(b o s)) is a ring automorphism
   of the polynomial ring MONALG(R, multi-indices on X), for any ring R.")

;;; =====================================================================
;;; R[x_1, ..., x_n]: a ring, commutative when R is, and Proposition 3.15.
;;; =====================================================================
(define lz6m-MIn '(MULTI-INDEX-MONOID (INTERVAL 1 n_)))
(define (lz6m-mpoly-setup!)
  (dk-peel!)
  (fact 'interval-in-set 1 'n_)
  (fact 'multi-index-monoid-is-comm-monoid '(INTERVAL 1 n_))
  (fact 'comm-monoid-is-monoid lz6m-MIn))

(sp (make-wff (forall-guarded '(r_ n_) (list '(IS-RING r_) '(IN n_ NN)) '(IS-RING (MPOLY r_ n_)))))
(lz6m-mpoly-setup!)
(mac 'MPOLY)
(fact 'monalg-is-ring 'r_ lz6m-MIn)
(ass)
(lz6m-done! 'mpoly-is-ring)
(topic! 'mpoly-is-ring 'algebra)

(sp (make-wff (forall-guarded '(r_ n_) (list '(IS-COMMUTATIVE-RING r_) '(IN n_ NN)) '(IS-COMMUTATIVE-RING (MPOLY r_ n_)))))
(lz6m-mpoly-setup!)
(mac 'MPOLY)
(fact 'monalg-comm 'r_ lz6m-MIn)
(ass)
(lz6m-done! 'mpoly-is-commutative-ring)
(topic! 'mpoly-is-commutative-ring 'algebra)
(gloss! 'mpoly-is-commutative-ring
  "R[x_1, ..., x_n] is a commutative ring when R is.")

;; Proposition 3.15
(sp (make-wff (forall-guarded '(r_ n_ s_)
  (list '(IS-RING r_) '(IN n_ NN) '(IN s_ (BIJECTION (INTERVAL 1 n_) (INTERVAL 1 n_))))
  '(IS-ISO-RING (MPOLY r_ n_) (MPOLY r_ n_) (VNB-LAMBDA mpp_ (CARR (MPOLY r_ n_)) (VAR-PERMUTE r_ n_ s_ mpp_))))))
(lz6m-mpoly-setup!)
(mac 'MPOLY)
(mac 'VAR-PERMUTE)
(mac 'monalg-carr)
(fact 'multi-index-reindex-is-ring-iso 'r_ '(INTERVAL 1 n_) 's_)
(ass)
(lz6m-done! 'var-permute-is-ring-iso)
(topic! 'var-permute-is-ring-iso 'algebra)
(gloss! 'var-permute-is-ring-iso
  "For a permutation sigma of {1, ..., n}, p |-> sigma . p (sigma applied to the indeterminates) is a ring
   automorphism of R[x_1, ..., x_n] (linear algebra, Proposition 3.15).")
