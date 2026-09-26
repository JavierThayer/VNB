;;; theorem-library/rake-monalg-comm.scm -- rake batch 5b, assignment 5b-A.
;;;
;;;   monalg-comm   structure-library/polynomial.scm:197   (the leaf; retire it)
;;;
;;;     forall A, M.  IS-COMMUTATIVE-RING(A) => IS-COMM-MONOID(M)
;;;                   => IS-COMMUTATIVE-RING(MONALG(A, M))
;;;
;;; "A[M] is a commutative ring when A is a commutative ring and M a commutative
;;; monoid."  The statement is the support's own S-expression, built through the
;;; same `forall-guarded' call.
;;;
;;; THE PLAN, and what each piece costs.  IS-COMMUTATIVE-RING is IFF-defined
;;; (is-commutative-ring-def): IS-RING plus the commutation of (MUL s) on the
;;; carrier.  The first conjunct is `monalg-is-ring' (proven, its own bill).  The
;;; second, read through the MONALG slot read-offs, is the commutativity of the
;;; CONVOLUTION
;;;
;;;     (f*g)(x) = FINSUM over I(f,g,x) = { (p,q) in supp f x supp g : p.q = x }
;;;                of f(p).g(q),
;;;
;;; and that is the SWAP reindex (p,q) |-> (q,p) plus the commutativity of A's
;;; multiplication -- monalg-laws.scm:230 says so, and `finsum-reindex-ag'
;;; (proven in rake-algebra3.scm, batch 5) is what carries it.  No part of
;;; `monalg-mul-assoc' (still asserted) is used.
;;;
;;; FIVE results, in order, each proven modulo 0 on its own:
;;;
;;;   bijection-from-inverse   NEW, general: phi in FUN(X,Y), psi in FUN(Y,X),
;;;       psi(phi u) = u on X and phi(psi v) = v on Y  =>  phi in BIJECTION(X,Y).
;;;       The brick monalg-is-ring.scm's header asked for (it is the whole
;;;       content of the `finsum-reindex-inverse' that file wants, which is now
;;;       five lines: this plus finsum-reindex-ag).
;;;   lambda-compose-value     NEW, general: ((z in D |-> ff(ph z)) pt) == ff(ph pt)
;;;       with ff and ph VARIABLES -- see the note at its proof; it is what reads
;;;       the right-hand side of finsum-reindex-ag, whose summand is an APPLIED
;;;       lambda.
;;;   monalg-index-swap-fun / -inverse / -bijection
;;;       the swap [q2,q1] of I(f,g,x) into I(g,f,x), typed, self-inverse, and
;;;       hence a bijection.  Only comm-monoid commutativity is used: the
;;;       condition (OPR M)(q1,q2) = x survives the swap.
;;;   monalg-mul-comm-at / monalg-mul-comm
;;;       the convolution commutes, pointwise and then as functions (monalg-ext).
;;;
;;; LOAD WINDOW [314, end).  lo = 314: every citation loads at or below
;;; theorem-library/monalg-is-ring (313), which is the deepest -- monalg-carr,
;;; monalg-mul-op, monalg-mul-apply, monalg-mul-fun, monalg-ext, raag-carr,
;;; card-cartesian-nn, cartesian-pair-eq and monalg-is-ring itself all live
;;; there.  The next deepest are finsum-fiber (308, cartesian-nth),
;;; rake-algebra3 (266, finsum-reindex-ag), rake-finsum-core (248,
;;; comm-monoid-opr-comm, commutative-ring-mul-comm), rake-finsum-laws (246,
;;; finsum-congruence-q), card-subset-nn (243), finsum-type-proof (202),
;;; op-typing (201, ring-carrier-closed-mul), subtype-laws (200,
;;; commutative-ring-is-ring, comm-monoid-is-monoid), fun-apply-type-proof (162),
;;; equality-basics (148, eq-sym), poly-membership (supp-in-set,
;;; supp-membership, finsupp-membership), pair-tuple-sethood
;;; (pair-in-cartesian), monalg-laws (311, monoid-carrier-is-set), views
;;; (ring-additive-ag-is-abelian-group), bijection (81,
;;; bijection-membership-iff) and theory.scm (cartesian-set-iff, primitive).
;;; NOTHING forces hi: no proof in the tree cites monalg-comm (it is an off-bill
;;; leaf, which is why it is in batch 5).
;;;
;;; Helper prefix: r6a-.

(define (r6a-check! name)
  (if (not (proof-done? *ps*))
      (begin
        (display ";; r6a: OPEN LEAVES before qed ") (display name) (newline)
        (for-each (lambda (l)
                    (display ";;   GOAL: ")
                    (display (expression->string (dk-goal-of l))) (newline))
                  (proof-leaves))
        (error "r6a: proof not complete" name))))

(define (r6a-done! name) (r6a-check! name) (qed name) (topic! name 'algebra))

;;; ---- beta / NTH plumbing.  Both loop on the GOAL and test for a redex
;;; first, so neither can leave an inert step behind (an inert notice would
;;; move *vnb-inert-at-load*).
(define (r6a-any-subterm? pred t)
  (let loop ((x t))
    (cond ((not (pair? x)) #f)
          ((pred x) #t)
          (#t (let scan ((l x))
                (cond ((not (pair? l)) #f)
                      ((loop (car l)) #t)
                      (#t (scan (cdr l)))))))))
(define (r6a-redex? x) (and (pair? (car x)) (eq? (caar x) 'VNB-LAMBDA)))
(define (r6a-nth-redex? x)
  (and (eq? (car x) 'NTH) (= (length x) 3)
       (pair? (caddr x)) (eq? (car (caddr x)) 'LIST)))
(define (r6a-beta!)
  (let loop ((k 0))
    (if (and (< k 8) (r6a-any-subterm? r6a-redex? (dk-goal)))
        (begin (lam-b) (loop (+ k 1))))))
(define (r6a-nth-reduce!)
  (let loop ((k 0))
    (if (and (< k 8) (r6a-any-subterm? r6a-nth-redex? (dk-goal)))
        (begin (nth-r) (loop (+ k 1))))))

;;; =====================================================================
;;; bijection-from-inverse and lambda-compose-value were proven HERE by batch 5b-A and
;;; MOVED 2026-09-18 into the block spliced into theorem-library/monalg-is-ring.scm (which
;;; loads one slot earlier and needs them for monalg-mul-assoc).  The proofs are the same;
;;; this file cites them from there.  The cut text is archived in
;;; archive/retired-2026-09-18/rake-monalg-comm--two-blocks.scm.
;;; =====================================================================

;;; =====================================================================
;;; The convolution index set and its swap.
;;;
;;;   I(f,g,x) = { p in SUPP(f) x SUPP(g) : (OPR m_)(p1, p2) = x }
;;;   SW(f,g,x) = (q_ in I(f,g,x)) |-> [q_2, q_1]
;;;
;;; SW(f,g,x) maps I(f,g,x) into I(g,f,x) because (OPR m_) commutes, and
;;; SW(g,f,x) undoes it because a member of a CARTESIAN is the pair of its
;;; projections (cartesian-pair-eq).
;;; =====================================================================
(define (r6a-supp f) (list 'SUPP 'a_ 'm_ f))
(define (r6a-P f g) (list 'CARTESIAN (r6a-supp f) (r6a-supp g)))
(define (r6a-I f g x)
  (list 'SEP 'p (r6a-P f g) (list '= (list '(OPR m_) '(NTH 1 p) '(NTH 2 p)) x)))
(define (r6a-SW f g x)
  (list 'VNB-LAMBDA 'q_ (r6a-I f g x) '(LIST (NTH 2 q_) (NTH 1 q_))))
(define (r6a-opr s t) (list '(OPR m_) s t))
(define (r6a-nth k q) (list 'NTH k q))
(define (r6a-swap-term q) (list 'LIST (r6a-nth 2 q) (r6a-nth 1 q)))
(define (r6a-forall5 body)
  (list 'FORALL 'a_ (list 'FORALL 'm_ (list 'FORALL 'f_ (list 'FORALL 'g_
    (list 'FORALL 'x_ body))))))
(define (r6a-forall4 body)
  (list 'FORALL 'a_ (list 'FORALL 'm_ (list 'FORALL 'f_ (list 'FORALL 'g_ body)))))

;; sethood of the index set (needs (IN (CARR m_) SET) in context)
(define (r6a-index-set! f g x)
  (fact 'supp-in-set 'a_ 'm_ f)
  (fact 'supp-in-set 'a_ 'm_ g)
  (have! (list 'IN (r6a-P f g) 'SET)
         (lambda () (mac 'cartesian-set-iff) (dk-conj-close!)))
  (have! (list 'IN (r6a-I f g x) 'SET)
         (lambda () (sep-set) (ass))))

;; the two halves of (IN q (I f g x)), read off in LANES: `sep-me' CONSUMES the
;; membership it opens, and the membership is wanted again later.
(define (r6a-open-idx! f g x q)
  (let ((mem (list 'IN q (r6a-I f g x))))
    (have! (list 'IN q (r6a-P f g))
           (lambda () (dk-split-all! (dk-landed (lambda () (sep-me mem)))) (ass)))
    (have! (list '= (r6a-opr (r6a-nth 1 q) (r6a-nth 2 q)) x)
           (lambda () (dk-split-all! (dk-landed (lambda () (sep-me mem)))) (ass)))))

;; (IN t (CARR m_)) off (IN t (SUPP a_ m_ f)), in a lane (mac-h is destructive)
(define (r6a-carr-of! t suppterm)
  (have! (list 'IN t '(CARR m_))
         (lambda ()
           (dk-split-all! (dk-landed (lambda () (mac-h 'supp-membership (list 'IN t suppterm)))))
           (ass))))

;; everything the swap of q needs, landed in the CURRENT context
(define (r6a-swap-prep! f g x q)
  (r6a-open-idx! f g x q)
  (dk-split! (dk-fact! 'cartesian-nth q (r6a-supp f) (r6a-supp g)))
  (r6a-carr-of! (r6a-nth 1 q) (r6a-supp f))
  (r6a-carr-of! (r6a-nth 2 q) (r6a-supp g))
  (fact 'comm-monoid-opr-comm 'm_ (r6a-nth 1 q) (r6a-nth 2 q))
  (fact 'eq-sym (r6a-opr (r6a-nth 1 q) (r6a-nth 2 q)) (r6a-opr (r6a-nth 2 q) (r6a-nth 1 q))))

;; close the GOAL (IN [q2, q1] (I g f x)), after r6a-swap-prep!
(define (r6a-swap-close! f g x q)
  (for-each
   (lambda (n)
     (dk-focus! n)
     (if (eq? (car (dk-goal)) 'IN)
         (begin (fact 'pair-in-cartesian (r6a-supp g) (r6a-supp f)
                      (r6a-nth 2 q) (r6a-nth 1 q))
                (ass))
         (begin (r6a-nth-reduce!)
                (subst (list '= (r6a-opr (r6a-nth 2 q) (r6a-nth 1 q))
                             (r6a-opr (r6a-nth 1 q) (r6a-nth 2 q))))
                (ass))))
   (dk-opened (lambda () (sep-mi)))))

;; the same membership as a HYPOTHESIS
(define (r6a-swap-mem! f g x q)
  (have! (list 'IN (r6a-swap-term q) (r6a-I g f x))
         (lambda () (r6a-swap-close! f g x q))))

;;; ---- monalg-index-swap-fun --------------------------------------------
(sp (make-wff
  (r6a-forall5
   (list 'IMPLIES '(IS-COMM-MONOID m_)
     (list 'IN (r6a-SW 'f_ 'g_ 'x_)
           (list 'FUN (r6a-I 'f_ 'g_ 'x_) (r6a-I 'g_ 'f_ 'x_)))))))
(dk-peel!)
(fact 'comm-monoid-is-monoid 'm_)
(fact 'monoid-carrier-is-set 'm_)
(r6a-index-set! 'f_ 'g_ 'x_)
(dk-lam-t!)
(let ((qv (dk-di-var!)))
  (r6a-swap-prep! 'f_ 'g_ 'x_ qv)
  (r6a-swap-close! 'f_ 'g_ 'x_ qv))
(r6a-done! 'monalg-index-swap-fun)

;;; ---- monalg-index-swap-inverse ----------------------------------------
(sp (make-wff
  (r6a-forall5
   (list 'IMPLIES '(IS-COMM-MONOID m_)
     (list 'FORALL 'u_
       (list 'IMPLIES (list 'IN 'u_ (r6a-I 'f_ 'g_ 'x_))
             (list '= (list (r6a-SW 'g_ 'f_ 'x_) (list (r6a-SW 'f_ 'g_ 'x_) 'u_)) 'u_)))))))
(let* ((landed (dk-peel!))
       (uv (cadr (any-pred (lambda (f) (and (pair? f) (eq? (car f) 'IN) (symbol? (cadr f))
                                            (equal? (caddr f) (r6a-I 'f_ 'g_ 'x_))))
                           landed))))
  (fact 'comm-monoid-is-monoid 'm_)
  (fact 'monoid-carrier-is-set 'm_)
  (r6a-swap-prep! 'f_ 'g_ 'x_ uv)
  (r6a-swap-mem! 'f_ 'g_ 'x_ uv)
  ;; BOTH certificates before the betas: whichever redex `lam-b' takes first,
  ;; its argument is typed.
  (fact 'monalg-index-swap-fun 'a_ 'm_ 'f_ 'g_ 'x_)
  (fact 'fun-apply-type-c (r6a-SW 'f_ 'g_ 'x_)
        (r6a-I 'f_ 'g_ 'x_) (r6a-I 'g_ 'f_ 'x_) uv)
  (r6a-beta!)
  (r6a-nth-reduce!)
  (fact 'cartesian-pair-eq uv (r6a-supp 'f_) (r6a-supp 'g_))
  (fact 'eq-sym uv (list 'LIST (r6a-nth 1 uv) (r6a-nth 2 uv)))
  (ass))
(r6a-done! 'monalg-index-swap-inverse)

;;; ---- monalg-index-swap-bijection --------------------------------------
(sp (make-wff
  (r6a-forall5
   (list 'IMPLIES '(IS-COMM-MONOID m_)
     (list 'IN (r6a-SW 'f_ 'g_ 'x_)
           (list 'BIJECTION (r6a-I 'f_ 'g_ 'x_) (r6a-I 'g_ 'f_ 'x_)))))))
(dk-peel!)
(fact 'monalg-index-swap-fun 'a_ 'm_ 'f_ 'g_ 'x_)
(fact 'monalg-index-swap-fun 'a_ 'm_ 'g_ 'f_ 'x_)
(fact 'monalg-index-swap-inverse 'a_ 'm_ 'f_ 'g_ 'x_)
(fact 'monalg-index-swap-inverse 'a_ 'm_ 'g_ 'f_ 'x_)
(fact 'bijection-from-inverse (r6a-I 'f_ 'g_ 'x_) (r6a-I 'g_ 'f_ 'x_)
      (r6a-SW 'f_ 'g_ 'x_) (r6a-SW 'g_ 'f_ 'x_))
(ass)
(r6a-done! 'monalg-index-swap-bijection)

;;; =====================================================================
;;; monalg-mul-comm-at -- the convolution commutes at every point.
;;; =====================================================================
(define r6a-ag '(RING-ADDITIVE-AG a_))
(define r6a-F '(FINSUPP a_ m_))
(define (r6a-L f g x)
  (list 'VNB-LAMBDA 'p (r6a-I f g x)
        (list '(MUL a_) (list f '(NTH 1 p)) (list g '(NTH 2 p)))))

;; a half of (IN f (FINSUPP a_ m_)), in a lane
(define (r6a-finsupp-half! f claim)
  (have! claim
         (lambda ()
           (dk-split-all! (dk-landed (lambda () (mac-h 'finsupp-membership (list 'IN f r6a-F)))))
           (ass))))
(define (r6a-fun-of! f) (r6a-finsupp-half! f (list 'IN f '(FUN (CARR m_) (CARR a_)))))
(define (r6a-card-supp! f) (r6a-finsupp-half! f (list 'IN (list 'CARD (r6a-supp f)) 'NN)))

;; the index set of (f,g) at x is a finite set, and the summand is typed on it
(define (r6a-idx-facts! f g x)
  (let ((P (r6a-P f g)) (I (r6a-I f g x)) (L (r6a-L f g x)))
    (r6a-index-set! f g x)
    (fact 'card-cartesian-nn (r6a-supp f) (r6a-supp g))
    (have! (list 'AND (list 'IN P 'SET) (list 'IN (list 'CARD P) 'NN))
           (lambda () (dk-conj-close!)))
    ;; the inclusion's binder must not be the point x (capture): zc_ is reserved
    (if (memq 'zc_ (free-vars I)) (error "r6a-idx-facts!: zc_ is free in the index set"))
    (have! (list 'AND (list 'IN I 'SET)
                 (list 'FORALL 'zc_ (list 'IMPLIES (list 'IN 'zc_ I) (list 'IN 'zc_ P))))
           (lambda ()
             (dk-conj-close!
              (lambda ()
                (if (eq? (car (dk-goal)) 'IN)
                    (ass)
                    (let ((zv (dk-di-var!)))
                      (dk-split-all! (dk-landed (lambda () (sep-me (list 'IN zv I)))))
                      (ass)))))))
    (fact 'card-subset-nn P I)
    (have! (list 'IN L (list 'FUN I '(CARR a_)))
           (lambda ()
             (dk-lam-t!)
             (let ((pv (dk-di-var!)))
               (r6a-open-idx! f g x pv)
               (dk-split! (dk-fact! 'cartesian-nth pv (r6a-supp f) (r6a-supp g)))
               (r6a-carr-of! (r6a-nth 1 pv) (r6a-supp f))
               (r6a-carr-of! (r6a-nth 2 pv) (r6a-supp g))
               (fact 'fun-apply-type-c f '(CARR m_) '(CARR a_) (r6a-nth 1 pv))
               (fact 'fun-apply-type-c g '(CARR m_) '(CARR a_) (r6a-nth 2 pv))
               (fact 'ring-carrier-closed-mul 'a_ (list f (r6a-nth 1 pv)) (list g (r6a-nth 2 pv)))
               (ass))))
    (have! (list 'IN L (list 'FUN I (list 'CARR r6a-ag)))
           (lambda () (mac 'raag-carr) (ass)))))

(sp (make-wff
  (r6a-forall5
   (list 'IMPLIES '(IS-COMMUTATIVE-RING a_)
     (list 'IMPLIES '(IS-COMM-MONOID m_)
       (list 'IMPLIES (list 'IN 'f_ r6a-F)
         (list 'IMPLIES (list 'IN 'g_ r6a-F)
           (list 'IMPLIES '(IN x_ (CARR m_))
             (list '= (list '(MONALG-MUL a_ m_ f_ g_) 'x_)
                      (list '(MONALG-MUL a_ m_ g_ f_) 'x_))))))))))
(dk-peel!)
(fact 'commutative-ring-is-ring 'a_)
(fact 'comm-monoid-is-monoid 'm_)
(fact 'monoid-carrier-is-set 'm_)
(fact 'ring-additive-ag-is-abelian-group 'a_)
(r6a-fun-of! 'f_) (r6a-fun-of! 'g_)
(r6a-card-supp! 'f_) (r6a-card-supp! 'g_)
(r6a-idx-facts! 'f_ 'g_ 'x_)
(r6a-idx-facts! 'g_ 'f_ 'x_)
(mac 'monalg-mul-apply)
(let* ((S  (r6a-I 'f_ 'g_ 'x_))
       (T  (r6a-I 'g_ 'f_ 'x_))
       (L1 (r6a-L 'f_ 'g_ 'x_))
       (L2 (r6a-L 'g_ 'f_ 'x_))
       (SW (r6a-SW 'g_ 'f_ 'x_)))
  (fact 'monalg-index-swap-bijection 'a_ 'm_ 'g_ 'f_ 'x_)
  ;; finsum-reindex-ag's third antecedent is a CONJUNCTION -- `fact' will not
  ;; split one, so it has to be in context whole.
  (have! (list 'AND (list 'IN T 'SET) (list 'IN (list 'CARD T) 'NN))
         (lambda () (dk-conj-close!)))
  (let* ((req (dk-fact! 'finsum-reindex-ag r6a-ag S T SW L1))
         (lam (caddr (caddr req))))          ; the summand finsum-reindex-ag built
    (subst req)
    (have! (list 'FORALL 'z_
             (list 'IMPLIES (list 'IN 'z_ T)
                   (list '= (list lam 'z_) (list L2 'z_))))
      (lambda ()
        (let ((zv (dk-di-var!)))
          (r6a-swap-prep! 'g_ 'f_ 'x_ zv)
          (r6a-swap-mem! 'g_ 'f_ 'x_ zv)
          (fact 'monalg-index-swap-fun 'a_ 'm_ 'g_ 'f_ 'x_)
          (fact 'fun-apply-type-c SW T S zv)
          (fact 'fun-apply-type-c 'f_ '(CARR m_) '(CARR a_) (r6a-nth 2 zv))
          (fact 'fun-apply-type-c 'g_ '(CARR m_) '(CARR a_) (r6a-nth 1 zv))
          ;; read the reindexed summand's value BEFORE betaing: a bare
          ;; (r6a-beta!) here reduces under the binder of `lam' and owes a
          ;; membership stated where that binder is free.
          (fact 'lambda-compose-value L1 SW T zv)
          (subst (list '== (list lam zv) (list L1 (list SW zv))))
          (r6a-beta!)
          (r6a-nth-reduce!)
          (fact 'commutative-ring-mul-comm 'a_ (list 'f_ (r6a-nth 2 zv)) (list 'g_ (r6a-nth 1 zv)))
          (ass))))
    (subst (dk-fact! 'finsum-congruence-q r6a-ag T lam L2))
    (fact 'finsum-type r6a-ag T L2)          ; the sum DENOTES -- what `rfl' owes
    (rfl)))
(r6a-done! 'monalg-mul-comm-at)

;;; =====================================================================
;;; monalg-mul-comm -- and so as functions (monalg-ext).
;;; =====================================================================
(sp (make-wff
  (r6a-forall4
   (list 'IMPLIES '(IS-COMMUTATIVE-RING a_)
     (list 'IMPLIES '(IS-COMM-MONOID m_)
       (list 'IMPLIES (list 'IN 'f_ r6a-F)
         (list 'IMPLIES (list 'IN 'g_ r6a-F)
           '(= (MONALG-MUL a_ m_ f_ g_) (MONALG-MUL a_ m_ g_ f_)))))))))
(dk-peel!)
(fact 'commutative-ring-is-ring 'a_)
(fact 'comm-monoid-is-monoid 'm_)
(fact 'monalg-mul-fun 'a_ 'm_ 'f_ 'g_)
(fact 'monalg-mul-fun 'a_ 'm_ 'g_ 'f_)
(have! '(FORALL x_ (IMPLIES (IN x_ (CARR m_))
          (= ((MONALG-MUL a_ m_ f_ g_) x_) ((MONALG-MUL a_ m_ g_ f_) x_))))
       (lambda ()
         (let ((xv (dk-di-var!)))
           (fact 'monalg-mul-comm-at 'a_ 'm_ 'f_ 'g_ xv)
           (ass))))
(fact 'monalg-ext 'a_ 'm_ '(MONALG-MUL a_ m_ f_ g_) '(MONALG-MUL a_ m_ g_ f_))
(ass)
(r6a-done! 'monalg-mul-comm)
(gloss! 'monalg-mul-comm
  "Convolution in A[M] is commutative when A is a commutative ring and M a
   commutative monoid: the index set of (f*g)(x) is carried onto that of
   (g*f)(x) by the swap of the two coordinates, and the coefficient products
   commute in A.")

;;; =====================================================================
;;; monalg-comm -- the leaf.  The statement is built through the same
;;; `forall-guarded' call as structure-library/polynomial.scm:197.
;;; =====================================================================
(sp (make-wff
  (forall-guarded '(A M)
    (list '(IS-COMMUTATIVE-RING A) '(IS-COMM-MONOID M))
    '(IS-COMMUTATIVE-RING (MONALG A M)))))
(dk-peel!)
(mac 'is-commutative-ring-def)
(dk-conj-close!
 (lambda ()
   (if (eq? (car (dk-goal)) 'IS-RING)
       (begin (fact 'commutative-ring-is-ring 'a)
              (fact 'comm-monoid-is-monoid 'm)
              (fact 'monalg-is-ring 'a 'm)
              (ass))
       (begin
         (mac 'monalg-carr)
         (mac 'monalg-mul-op)
         (dk-peel!)
         ;; the eigenvariables off the GOAL, never off the context
         (let* ((g (dk-goal)) (uv (cadr (cadr g))) (vv (caddr (cadr g))))
           (r6a-beta!)
           (fact 'monalg-mul-comm 'a 'm uv vv)
           (ass))))))
(r6a-done! 'monalg-comm)

;;; =====================================================================
;;; THE SECOND LEAF OF THIS ASSIGNMENT, NOT PROVEN -- and the brick it wants.
;;; (Nothing below is code; it is the report kept beside the file.)
;;;
;;; prod-of-sums-expansion (theorem-library/prod-of-sums.scm:137).
;;;
;;;     prod_{k in X} (a k + b k)
;;;        = SUM_{S in POWER(X)} (prod_{k in S} a k) * (prod_{k in X\S} b k)
;;;
;;; rake-combinatorics2.scm's closing block says it "waits on batch V" because
;;; the reindex along S |-> S u {k0} is `finsum-reindex'.  That half is now
;;; clear: finsum-reindex / finsum-reindex-ag are PROVEN (rake-algebra3.scm),
;;; and the injectivity of S |-> S u {k0} on POWER(X) (k0 not in X) gives the
;;; BIJECTION term they want -- through `bijection-from-inverse' proved above,
;;; whose inverse is S |-> DIFFERENCE(S, {k0}) and whose two round trips are
;;; `difference-membership' (theorem-library/difference-laws.scm, PROVEN) plus
;;; class extensionality.
;;;
;;; THE OTHER HALF IS THE BLOCKER, and it is a brick the tree does not have.
;;; The induction step splits the right-hand sum along
;;;
;;;     POWER(X u {k0}) = POWER(X)  u  IMAGE(S |-> S u {k0}, POWER X)
;;;
;;; (power-insert-cover / power-insert-disjoint, both PROVEN) -- i.e. it needs
;;; the sum over a DISJOINT UNION to be the sum over the two halves:
;;;
;;;     finsum-union-disjoint:  ag abelian group; U, V finite sets with
;;;       U n V = EMPTY-SET; f in FUN(UNION U V, CARR ag)
;;;       =>  FINSUM(ag, f, UNION U V)
;;;           = (OPR ag)(FINSUM(ag, f, U), FINSUM(ag, f, V))
;;;
;;; NOTHING of that shape exists.  The whole inventory of laws relating two
;;; index sets is: finsum-insert-ag (ONE point), finsum-embed (asserted),
;;; finsum-reindex/-ag (a BIJECTION), finsum-fubini (a CARTESIAN).  Two routes
;;; to it, and each has a price:
;;;   * finsum-embed twice plus finsum-add-ag -- the `mir-embed!' device of
;;;     monalg-is-ring.scm (extend each half to the union with a summand that is
;;;     IDEN off its half, then add pointwise).  Five lines, and it CHAINS to
;;;     the asserted `finsum-embed', which batch 5's rule forbids.
;;;   * finite-set-induction on V, peeling with finsum-insert-ag.  The step's IH
;;;     wants f typed on UNION U V' for V' a subset of V, which is the
;;;     RESTRICTION wall rake-finsum-laws.scm's header records -- now
;;;     dissolvable (the restriction IS (VNB-LAMBDA z (UNION U V') (f z)), typed
;;;     by lam-t, transported by the untyped finsum-congruence-q) -- plus the
;;;     surgery V = (V \ {x}) u {x} with CARD(V \ {x}) in NN, which still wants a
;;;     converse of `card-insert'.  That is the same pair of obligations that
;;;     keeps finsum-embed asserted, so proving finsum-union-disjoint this way
;;;     would very likely retire finsum-embed too.
;;;
;;; So prod-of-sums-expansion is ONE brick away, and the brick is a leaf of its
;;; own worth more than the capstone: finsum-union-disjoint would serve the
;;; product-of-sums expansion, `choose-succ' (the Pascal split is also a
;;; disjoint union), and every later "split the index set in two" argument.
;;; Two further small set identities the capstone's step needs, both easy and
;;; both missing as named lemmas: (X u {k0}) \ S = (X \ S) u {k0} for S subset X
;;; and k0 not in X (to apply prod-ring-insert on the complement), and
;;; (X u {k0}) \ (S u {k0}) = X \ S.
;;; =====================================================================
