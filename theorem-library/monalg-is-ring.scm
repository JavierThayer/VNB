;;; monalg-is-ring.scm -- the monoid algebra A[M] is a ring (structure-library/polynomial.scm's
;;; umbrella seed), PROVEN, with every additive law, both distributive laws, both unit laws and
;;; the typing of the convolution proven on the way.  The one law still chained to its seed is
;;; the associativity of convolution, `monalg-mul-assoc' (see WHAT IS STILL OWED at the foot).
;;;
;;;   monalg-is-ring:   forall A, M.  IS-RING(A) => IS-MONOID(M) => IS-RING(MONALG(A, M))
;;;
;;; THE PLAN is mat-ring-proof.scm's: unfold the auto-generated IS-RING iff into its 14
;;; conjuncts (length, six slot typings, seven property clauses), split, and discharge each by
;;; reading MONALG's slot accessors off the 6-tuple (the read-off theorems `monalg-carr',
;;; `monalg-add-op', ... -- proven here, not warranted as MAT-RING's are) and citing a law of
;;; the algebra.  The laws are proven at two levels:
;;;
;;;   * POINTWISE, as equations between values at a point x of CARR(M) -- the pointwise value
;;;     of each operation is a guarded `==' read-off (monalg-add-apply in monalg-laws.scm;
;;;     monalg-neg-apply, monalg-one-apply, monalg-mul-apply here);
;;;   * at the FUNCTION level, by `monalg-ext': two elements of FINSUPP(A,M) that agree on
;;;     CARR(M) are equal (fun-domain-extensionality through finsupp-membership).
;;;
;;; The additive laws are then the ring laws of A applied pointwise.  The multiplicative ones
;;; are FINSUM manipulations of the convolution
;;;
;;;     (f*g)(x) = FINSUM over I(f,g,x) = { (p,q) in supp f x supp g : p.q = x } of f(p) g(q)
;;;
;;; and ONE mechanism carries all of them: `mir-embed!' -- a sum over I(A,B,x) equals the sum
;;; over I(A',B',x) for A c A', B c B' whenever the summand vanishes at the added indices
;;; (finsum-congruence to change the summand's declared domain, finsum-embed to grow the
;;; index set).  Distributivity embeds the three sums into the common index set over
;;; supp f x (supp g u supp h) and adds them there (finsum-add-ag); the unit law embeds
;;; supp(ONE) x supp f into {IDEN(M)} x supp f, where the sum has ONE index (finsum-single-
;;; support) or none (finsum-all-id) -- so the trivial ring, where supp(ONE) is EMPTY, needs
;;; no separate case.  The typing of the convolution (monalg-mul-fun) is the same embed idea
;;; read backwards: outside the image of supp f x supp g under M's multiplication the index
;;; set has no member, the sum is IDEN, so the support lies inside a finite image.
;;;
;;; TWO GENERAL BRICKS the tree lacked, proven here because nothing about MUL is provable
;;; without them:
;;;   card-cartesian-nn   the product of two finite sets is finite  (finite-set-induction,
;;;                       card-image-finite.scm's driver shape; the step is
;;;                       (S u {x}) x Y  c  (S x Y) u IMAGE(w |-> [x,w], Y))
;;;   cartesian-pair-eq   a member of a product is the pair of its projections, as an
;;;                       EQUATION (cartesian-nth gives the projections' memberships)
;;; plus the small ones: ring-neg-zero (-0 = 0), supp-add-subset, monalg-one-supp-subset,
;;; finsupp-in-set, and the RING-ADDITIVE-AG read-offs raag-carr/-opr/-iden (the `ras-*'
;;; supports in matrix.scm say the same with `=' and are warranted, not proven).
;;;
;;; BILL.  Everything additive is `modulo 0'.  The multiplicative side chains to the finsum
;;; supports finsum-type, finsum-congruence, finsum-embed, finsum-add-ag, finsum-all-id,
;;; finsum-single-support (all asserted `well-known'/`informal' tonight), to the kernel macete
;;; cartesian-decompose (warranted `well-known' in finsum-fiber.scm, see the note there), and
;;; -- for the one law not proven here -- to the seed monalg-mul-assoc.
;;;
;;; LOAD WINDOW: after theorem-library/poly-zero (monalg-zero-apply, monalg-zero-fun; itself
;;; after monalg-laws and finsum-fiber, which are also cited) and before
;;; theorem-library/poly-is-ring-proof, the leaf's only citer.  Every other citation loads
;;; earlier: card-inequalities (card-union-nn), card-image-finite, card-subset-nn,
;;; ring-zero-one-power, op-typing, pair-tuple-sethood, fun-apply-type-proof, poly-membership,
;;; card-singleton-proof, finsum-additive, finsum-type, matrix, views, polynomial.
;;;
;;; DRIVER NOTES (each cost a probe):
;;;   * `sep-me' CONSUMES the membership it opens, exactly as `mac-h' does; a `lam-b' whose
;;;     redex is licensed by that membership must come BEFORE it, or the beta owes the
;;;     membership as an extra leaf that nothing can close.
;;;   * `slot' rewrites EVERY occurrence of the accessor, so a read-off whose right-hand side
;;;     mentions CARR(a_) needs a second `slot' pass (raag-carr).
;;;   * `have!' of a claim that IS the goal has no main branch; rewrite the landing in place
;;;     (mac-h) or use dk-have!.
;;;   * MIT folds case: a Scheme parameter `u' shadows a variable `U' (card-cartesian-nn's
;;;     first draft substituted the union for its own member).
;;;   * The inclusion binder of an index set must not be the point x it is filtered by
;;;     (`zc_' is reserved for it; capture otherwise).
;;;   * monoid-identity-in / monoid-left-id / monoid-right-id are UNWARRANTED axioms in
;;;     monoid.scm; the IS-MONOID unfold gives each in three lines (mir-monoid-iden!,
;;;     mir-monoid-id!), so nothing here bills them.
;;;
;;; WHAT IS STILL OWED: monalg-mul-assoc.  ((f*g)*h)(x) and (f*(g*h))(x) are both triple sums
;;; over { (p,q,r) in supp f x supp g x supp h : p.q.r = x }, reached from the nested sums by
;;; `finsum-fiber' along phi(p,q,r) = (p.q, r) resp. (p, q.r) -- but the fiber of (u,r) is a
;;; set of TRIPLES and the inner convolution's index set I(f,g,u) is a set of PAIRS, so the two
;;; inner sums are related only by REINDEXING along (p,q) |-> ((p,q), r).  `finsum-reindex-ag'
;;; wants a BIJECTION term for that; the lemma that would make the associativity a 150-line
;;; driver instead of a 500-line one is the reindexing along an explicit two-sided inverse:
;;;
;;;   finsum-reindex-inverse:  ag abelian group; S, T finite sets; phi in FUN(T, S);
;;;     psi in FUN(S, T); (forall t in T. psi(phi t) = t); (forall s in S. phi(psi s) = s);
;;;     f in FUN(S, CARR ag)   =>   FINSUM(ag, f, S) = FINSUM(ag, LAMBDA t in T. f(phi t), T)
;;;
;;; (provable from finsum-reindex-ag + bijection-membership-iff, once).  With it and
;;; finsum-fiber the associativity is the embed of I(f*g, h, x) into
;;; I(IMAGE(mult, supp f x supp g), h, x), one finsum-ring-distrib-right-gen per outer index,
;;; one finsum-fiber, one reindex per fiber, and monoid-assoc + ring-mul-assoc under a
;;; congruence.  Not attempted here.
;;;
;;; Helper prefix: mir-  (and ccn- for the finite-product brick).

(define mir-F '(FINSUPP a_ m_))
(define mir-FF (list 'CARTESIAN mir-F mir-F))
(define (mir-readoff! name acc rhs)
  (sp (make-wff (list 'FORALL 'a_ (list 'FORALL 'm_ (list '== (list acc '(MONALG a_ m_)) rhs)))))
  (di) (mac 'MONALG) (slot acc) (nth-r) (qrfl)
  (qed name))
(mir-readoff! 'monalg-carr 'CARR mir-F)
(mir-readoff! 'monalg-add-op 'ADD (list 'VNB-LAMBDA '(LIST f g) mir-FF '(MONALG-ADD a_ m_ f g)))
(mir-readoff! 'monalg-mul-op 'MUL (list 'VNB-LAMBDA '(LIST f g) mir-FF '(MONALG-MUL a_ m_ f g)))
(mir-readoff! 'monalg-neg-op 'NEG (list 'VNB-LAMBDA 'f mir-F '(MONALG-NEG a_ m_ f)))
(mir-readoff! 'monalg-zero-slot 'ZERO '(MONALG-ZERO a_ m_))
(mir-readoff! 'monalg-one-slot 'ONE '(MONALG-ONE a_ m_))

(define (mir-split-head! first)
  (dk-split! (dk-pick (lambda (h) (and ((dk-head? 'AND) h) (equal? (cadr h) first))) "conjunction")))
;; (IN (CARR a_) SET) from IS-RING a_, without citing ring-carr-in-set (a leaf)
(define (mir-ring-carr-set!)
  (have! '(IN (CARR a_) SET)
    (lambda () (mac-h 'is-ring '(IS-RING a_))
               (dk-split! (any-pred (dk-head? 'AND) (dk-asms)))
               (ass))))
;; (IN v (FUN (CARR m_) (CARR a_))) off (IN v F), in a lane so (IN v F) survives
(define (mir-fun! v)
  (have! (list 'IN v '(FUN (CARR m_) (CARR a_)))
    (lambda () (mac-h 'finsupp-membership (list 'IN v mir-F))
               (mir-split-head! (list 'IN v '(FUN (CARR m_) (CARR a_))))
               (ass))))
(define (mir-app-of? head)
  (lambda (t) (and (pair? t) (pair? (car t)) (eq? (caar t) head))))
(define (mir-has? pred) (any-pred pred (dk-subterms (dk-goal))))
;; finsupp-in-set
(sp (make-wff '(FORALL a_ (FORALL m_ (IMPLIES (IS-RING a_) (IMPLIES (IS-MONOID m_) (IN (FINSUPP a_ m_) SET)))))))
(dk-peel!)
(fact 'monoid-carrier-is-set 'm_)
(mir-ring-carr-set!)
(mac 'FINSUPP) (sep-set)
(mac 'fun-set-iff)
(dk-conj-close!)
(qed 'finsupp-in-set)

;; monalg-ext
(sp (make-wff '(FORALL a_ (FORALL m_ (FORALL f_ (FORALL g_
   (IMPLIES (IN f_ (FINSUPP a_ m_)) (IMPLIES (IN g_ (FINSUPP a_ m_))
     (IMPLIES (FORALL x_ (IMPLIES (IN x_ (CARR m_)) (= (f_ x_) (g_ x_))))
       (= f_ g_))))))))))
(dk-peel!)
(mac-h 'finsupp-membership '(IN f_ (FINSUPP a_ m_)))
(mir-split-head! '(IN f_ (FUN (CARR m_) (CARR a_))))
(mac-h 'finsupp-membership '(IN g_ (FINSUPP a_ m_)))
(mir-split-head! '(IN g_ (FUN (CARR m_) (CARR a_))))
(mac-h 'fun-codomain-iff '(IN f_ (FUN (CARR m_) (CARR a_))))
(mir-split-head! '(IN f_ (FUN (CARR m_))))
(mac-h 'fun-codomain-iff '(IN g_ (FUN (CARR m_) (CARR a_))))
(mir-split-head! '(IN g_ (FUN (CARR m_))))
(fact 'fun-domain-extensionality '(CARR m_) 'f_ 'g_)
(ass)
(qed 'monalg-ext)

;; pointwise values of NEG and ONE
(sp (make-wff '(FORALL a_ (FORALL m_ (FORALL f_ (FORALL x_
   (IMPLIES (IN x_ (CARR m_))
     (== ((MONALG-NEG a_ m_ f_) x_) ((NEG a_) (f_ x_))))))))))
(dk-peel!) (mac 'MONALG-NEG) (lam-b) (qrfl)
(qed 'monalg-neg-apply)
(sp (make-wff '(FORALL a_ (FORALL m_ (FORALL x_
   (IMPLIES (IN x_ (CARR m_))
     (== ((MONALG-ONE a_ m_) x_) (IF (= x_ (IDEN m_)) (ONE a_) (ZERO a_)))))))))
(di) (mac 'MONALG-ONE) (lam-b) (qrfl)
(qed 'monalg-one-apply)

;; -0 = 0, as a lemma (six rewrites; nothing in the tree states it)
(sp (make-wff '(FORALL a_ (IMPLIES (IS-RING a_) (= ((NEG a_) (ZERO a_)) (ZERO a_))))))
(dk-peel!)
(fact 'ring-zero-in 'a_)
(fact 'ring-neg-in-carr 'a_ '(ZERO a_))
(fact 'ring-add-left-inv 'a_ '(ZERO a_))            ; (-0)+0 = 0
(fact 'ring-add-left-id 'a_ '((NEG a_) (ZERO a_)))   ; 0+(-0) = -0
(fact 'ring-add-comm 'a_ '(ZERO a_) '((NEG a_) (ZERO a_)))  ; 0+(-0) = (-0)+0
(have! '(= ((NEG a_) (ZERO a_)) ((ADD a_) (ZERO a_) ((NEG a_) (ZERO a_))))
  (lambda () (subst '(= ((ADD a_) (ZERO a_) ((NEG a_) (ZERO a_))) ((NEG a_) (ZERO a_)))) (rfl)))
(subst '(= ((NEG a_) (ZERO a_)) ((ADD a_) (ZERO a_) ((NEG a_) (ZERO a_)))))
(subst '(= ((ADD a_) (ZERO a_) ((NEG a_) (ZERO a_))) ((ADD a_) ((NEG a_) (ZERO a_)) (ZERO a_))))
(ass)
(qed 'ring-neg-zero)
(define (mir-both! g1 b1 b2)
  (let ((ls (dk-opened (lambda () (di)))))
    (dk-focus! (any-pred (lambda (n) (equal? (dk-goal-of n) g1)) ls)) (b1)
    (dk-focus! (any-pred (lambda (n) (not (equal? (dk-goal-of n) g1))) ls)) (b2)))
(define (mir-if! ifterm which closer)
  (let* ((cnd   (cadr ifterm))
         (val   (if (eq? which 'true) (caddr ifterm) (cadddr ifterm)))
         (cgoal (if (eq? which 'true) cnd (list 'NOT cnd)))
         (ls    (dk-opened (lambda ()
                  (if (eq? which 'true) (if-true ifterm) (if-false ifterm))))))
    (dk-focus! (any-pred (lambda (n) (equal? (dk-goal-of n) cgoal)) ls))
    (closer)
    (dk-focus! (any-pred (lambda (n) (not (equal? (dk-goal-of n) cgoal))) ls))
    (subst (list '= ifterm val))))
(define (mir-nest-forall vs body) (if (null? vs) body (list 'FORALL (car vs) (mir-nest-forall (cdr vs) body))))
(define (mir-nest-implies as body) (if (null? as) body (list 'IMPLIES (car as) (mir-nest-implies (cdr as) body))))
(define (mir-supp-finite-by-subset! sup X thunk)   ; sup in SET assumed; X finite (AND form) assumed in ctx
  (have! (list 'AND (list 'IN sup 'SET)
               (list 'FORALL 'z_ (list 'IMPLIES (list 'IN 'z_ sup) (list 'IN 'z_ X))))
    (lambda () (mir-both! (list 'IN sup 'SET) (lambda () (ass)) thunk)))
  (fact 'card-subset-nn X sup)
  (ass))

(define (mir-monoid-iden!)
  (have! '(IN (IDEN m_) (CARR m_))
    (lambda () (mac-h 'is-monoid '(IS-MONOID m_))
               (dk-split! (any-pred (dk-head? 'AND) (dk-asms)))
               (ass))))
;; ---- monalg-neg-fun ----
(define mir-negf '(MONALG-NEG a_ m_ f_))
(sp (make-wff `(FORALL a_ (FORALL m_ (FORALL f_ (IMPLIES (IS-RING a_) (IMPLIES (IS-MONOID m_) (IMPLIES (IN f_ ,mir-F) (IN ,mir-negf ,mir-F)))))))))
(dk-peel!)
(fact 'monoid-carrier-is-set 'm_) (fact 'ring-zero-in 'a_) (fact 'ring-neg-zero 'a_)
(mac-h 'finsupp-membership `(IN f_ ,mir-F))
(mir-split-head! '(IN f_ (FUN (CARR m_) (CARR a_))))
(mac 'finsupp-membership)
(mir-both! `(IN ,mir-negf (FUN (CARR m_) (CARR a_)))
  (lambda () (mac 'MONALG-NEG) (dk-lam-t!)
    (let ((xv (dk-di-var!)))
      (fact 'fun-apply-type-c 'f_ '(CARR m_) '(CARR a_) xv)
      (fact 'ring-neg-in-carr 'a_ (list 'f_ xv))
      (ass)))
  (lambda ()
    (have! '(IN (SUPP a_ m_ f_) SET) (lambda () (fact 'supp-in-set 'a_ 'm_ 'f_) (ass)))
    (have! `(IN (SUPP a_ m_ ,mir-negf) SET) (lambda () (fact 'supp-in-set 'a_ 'm_ mir-negf) (ass)))
    (have! '(AND (IN (SUPP a_ m_ f_) SET) (IN (CARD (SUPP a_ m_ f_)) NN)))
    (mir-supp-finite-by-subset! `(SUPP a_ m_ ,mir-negf) '(SUPP a_ m_ f_)
      (lambda ()
        (di)
        (mac-h 'supp-membership `(IN z_ (SUPP a_ m_ ,mir-negf)))
        (mir-split-head! '(IN z_ (CARR m_)))
        (mac-h 'monalg-neg-apply `(NOT (= (,mir-negf z_) (ZERO a_))))
        (mac 'supp-membership)
        (mir-both! '(IN z_ (CARR m_))
          (lambda () (ass))
          (lambda ()
            (di)
            (have! '(= ((NEG a_) (f_ z_)) (ZERO a_))
              (lambda () (subst '(= (f_ z_) (ZERO a_))) (ass)))
            (ai '(NOT (= ((NEG a_) (f_ z_)) (ZERO a_))))))))))
(qed 'monalg-neg-fun)

;; ---- monalg-zero-in ----
(define mir-zero '(MONALG-ZERO a_ m_))
(sp (make-wff `(FORALL a_ (FORALL m_ (IMPLIES (IS-RING a_) (IMPLIES (IS-MONOID m_) (IN ,mir-zero ,mir-F)))))))
(dk-peel!)
(fact 'monoid-carrier-is-set 'm_) (fact 'ring-zero-in 'a_)
(fact 'monalg-zero-fun 'a_ 'm_)
(fact 'empty-set-is-set) (fact 'card-empty) (fact 'nn-zero-in)
(have! '(IN (CARD EMPTY-SET) NN) (lambda () (subst '(= (CARD EMPTY-SET) 0)) (ass)))
(have! '(AND (IN EMPTY-SET SET) (IN (CARD EMPTY-SET) NN)))
(mac 'finsupp-membership)
(mir-both! `(IN ,mir-zero (FUN (CARR m_) (CARR a_)))
  (lambda () (ass))
  (lambda ()
    (have! `(IN (SUPP a_ m_ ,mir-zero) SET) (lambda () (fact 'supp-in-set 'a_ 'm_ mir-zero) (ass)))
    (mir-supp-finite-by-subset! `(SUPP a_ m_ ,mir-zero) 'EMPTY-SET
      (lambda ()
        (di)
        (mac-h 'supp-membership `(IN z_ (SUPP a_ m_ ,mir-zero)))
        (mir-split-head! '(IN z_ (CARR m_)))
        (mac-h 'monalg-zero-apply `(NOT (= (,mir-zero z_) (ZERO a_))))
        (have! '(= (ZERO a_) (ZERO a_)) (lambda () (rfl)))
        (ai '(NOT (= (ZERO a_) (ZERO a_))))))))
(qed 'monalg-zero-in)

;; ---- monalg-one-in ----
(define mir-one '(MONALG-ONE a_ m_))
(define mir-ee '(PAIR (IDEN m_) (IDEN m_)))
(sp (make-wff `(FORALL a_ (FORALL m_ (IMPLIES (IS-RING a_) (IMPLIES (IS-MONOID m_) (IN ,mir-one ,mir-F)))))))
(dk-peel!)
(fact 'monoid-carrier-is-set 'm_) (fact 'ring-zero-in 'a_) (fact 'ring-one-in 'a_) (mir-monoid-iden!)
(fact 'membership-implies-sethood '(IDEN m_) '(CARR m_))
(have! '(AND (IN (IDEN m_) SET) (IN (IDEN m_) SET)))
(fact 'pairing '(IDEN m_) '(IDEN m_))
(fact 'card-singleton '(IDEN m_))
(fact 'nn-zero-in) (fact 'nn-succ-closed 0)
(have! `(IN (CARD ,mir-ee) NN) (lambda () (subst `(= (CARD ,mir-ee) (succ 0))) (ass)))
(have! `(AND (IN ,mir-ee SET) (IN (CARD ,mir-ee) NN)))
(mac 'finsupp-membership)
(mir-both! `(IN ,mir-one (FUN (CARR m_) (CARR a_)))
  (lambda ()
    (mac 'MONALG-ONE) (dk-lam-t!)
    (let* ((xv (dk-di-var!)) (it `(IF (= ,xv (IDEN m_)) (ONE a_) (ZERO a_))))
      (use-em `(= ,xv (IDEN m_))
        (lambda () (mir-if! it 'true (lambda () (ass))) (ass))
        (lambda () (mir-if! it 'false (lambda () (ass))) (ass)))))
  (lambda ()
    (have! `(IN (SUPP a_ m_ ,mir-one) SET) (lambda () (fact 'supp-in-set 'a_ 'm_ mir-one) (ass)))
    (mir-supp-finite-by-subset! `(SUPP a_ m_ ,mir-one) mir-ee
      (lambda ()
        (di)
        (mac-h 'supp-membership `(IN z_ (SUPP a_ m_ ,mir-one)))
        (mir-split-head! '(IN z_ (CARR m_)))
        (mac-h 'monalg-one-apply `(NOT (= (,mir-one z_) (ZERO a_))))
        (let* ((pm  (dk-fact! 'pairing-membership '(IDEN m_) '(IDEN m_)))
               (iff (dk-apply! pm 'z_))
               (ifz '(IF (= z_ (IDEN m_)) (ONE a_) (ZERO a_))))
          (use-em '(= z_ (IDEN m_))
            (lambda () (dk-only! iff '(= z_ (IDEN m_))) (prop))
            (lambda ()
              (have! `(= ,ifz (ZERO a_)) (lambda () (mir-if! ifz 'false (lambda () (ass))) (rfl)))
              (ai `(NOT (= ,ifz (ZERO a_)))))))))))
(qed 'monalg-one-in)
;; ---- the additive laws, at the function level ----
;; mir-type! learns the multiplicative heads
(define (mir-type! t)
  (cond ((symbol? t) 'in-context)
        ((eq? (car t) 'MONALG-ADD)
         (mir-type! (cadddr t)) (mir-type! (car (cddddr t)))
         (fact 'monalg-add-fun 'a_ 'm_ (cadddr t) (car (cddddr t))))
        ((eq? (car t) 'MONALG-MUL)
         (mir-type! (cadddr t)) (mir-type! (car (cddddr t)))
         (fact 'monalg-mul-fun 'a_ 'm_ (cadddr t) (car (cddddr t))))
        ((eq? (car t) 'MONALG-NEG)
         (mir-type! (cadddr t)) (fact 'monalg-neg-fun 'a_ 'm_ (cadddr t)))
        ((eq? (car t) 'MONALG-ZERO) (fact 'monalg-zero-in 'a_ 'm_))
        ((eq? (car t) 'MONALG-ONE)  (fact 'monalg-one-in 'a_ 'm_))
        (#t (error "mir-type!: unknown head" t))))
;; mir-mac-all! stops (silently) when the macete declines: a guarded read-off under a
;; binder is not licensed, and the closer's `ass' is the loud check
(define (mir-mac-all! macete head)
  (let loop ((k 0))
    (when (and (< k 6) (mir-has? (mir-app-of? head)))
      (let ((g (dk-goal)))
        (quietly (lambda () (mac macete)))
        (if (not (equal? g (dk-goal))) (loop (+ k 1)))))))

(define (mir-law! name vars lhs rhs closer)
  (sp (make-wff (mir-nest-forall (append '(a_ m_) vars)
        (mir-nest-implies (append '((IS-RING a_) (IS-MONOID m_))
                                  (map (lambda (v) (list 'IN v mir-F)) vars))
          (list '= lhs rhs)))))
  (dk-peel!)
  (fact 'ring-zero-in 'a_)
  (for-each mir-fun! vars)
  (mir-type! lhs) (mir-type! rhs)
  (have! (list 'FORALL 'x_ (list 'IMPLIES '(IN x_ (CARR m_))
                              (list '= (list lhs 'x_) (list rhs 'x_))))
    (lambda ()
      (let ((x (dk-di-var!)))
        (mir-mac-all! 'monalg-add-apply 'MONALG-ADD)
        (mir-mac-all! 'monalg-neg-apply 'MONALG-NEG)
        (mir-mac-all! 'monalg-zero-apply 'MONALG-ZERO)
        (for-each (lambda (v) (fact 'fun-apply-type-c v '(CARR m_) '(CARR a_) x)) vars)
        (closer x)
        (ass))))
  (fact 'monalg-ext 'a_ 'm_ lhs rhs)
  (ass)
  (qed name))
(define (mir-add . xs) (append '(MONALG-ADD a_ m_) xs))
(define (mir-neg x) (list 'MONALG-NEG 'a_ 'm_ x))
(define (mir-at v x) (list v x))

(mir-law! 'monalg-add-assoc '(f_ g_ h_)
  (mir-add (mir-add 'f_ 'g_) 'h_) (mir-add 'f_ (mir-add 'g_ 'h_))
  (lambda (x) (fact 'ring-add-assoc 'a_ (mir-at 'f_ x) (mir-at 'g_ x) (mir-at 'h_ x))))
(mir-law! 'monalg-add-comm '(f_ g_)
  (mir-add 'f_ 'g_) (mir-add 'g_ 'f_)
  (lambda (x) (fact 'ring-add-comm 'a_ (mir-at 'f_ x) (mir-at 'g_ x))))
(mir-law! 'monalg-add-zero-left '(f_)
  (mir-add mir-zero 'f_) 'f_
  (lambda (x) (fact 'ring-add-left-id 'a_ (mir-at 'f_ x))))
(mir-law! 'monalg-add-zero-right '(f_)
  (mir-add 'f_ mir-zero) 'f_
  (lambda (x)
    (fact 'ring-add-comm 'a_ (mir-at 'f_ x) '(ZERO a_))
    (subst (list '= (list '(ADD a_) (mir-at 'f_ x) '(ZERO a_)) (list '(ADD a_) '(ZERO a_) (mir-at 'f_ x))))
    (fact 'ring-add-left-id 'a_ (mir-at 'f_ x))))
(mir-law! 'monalg-add-neg-left '(f_)
  (mir-add (mir-neg 'f_) 'f_) mir-zero
  (lambda (x) (fact 'ring-add-left-inv 'a_ (mir-at 'f_ x))))
(mir-law! 'monalg-add-neg-right '(f_)
  (mir-add 'f_ (mir-neg 'f_)) mir-zero
  (lambda (x)
    (fact 'ring-neg-in-carr 'a_ (mir-at 'f_ x))
    (fact 'ring-add-comm 'a_ (mir-at 'f_ x) (list '(NEG a_) (mir-at 'f_ x)))
    (subst (list '= (list '(ADD a_) (mir-at 'f_ x) (list '(NEG a_) (mir-at 'f_ x)))
                    (list '(ADD a_) (list '(NEG a_) (mir-at 'f_ x)) (mir-at 'f_ x))))
    (fact 'ring-add-left-inv 'a_ (mir-at 'f_ x))))
;; ---- card-cartesian-nn: the product of two finite sets is finite ----
(define ccn-prop '(FORALL y_ (IMPLIES (IN y_ SET) (IMPLIES (IN (CARD y_) NN)
                    (IN (CARD (CARTESIAN x_ y_)) NN)))))
(define ccn-class (list 'COMP 'x_ ccn-prop))
(define (ccn-sethood! X)          ; goal-side: (IN X SET) for a CARTESIAN / IMAGE / UNION / var
  (cond ((and (pair? X) (eq? (car X) 'CARTESIAN))
         (mac 'cartesian-set-iff) (dk-conj-close! (lambda () (ccn-sethood! (cadr (dk-goal))))))
        (#t (ass))))
(define (ccn-set! X) (have! (list 'IN X 'SET) (lambda () (ccn-sethood! X))))
;; goal (IN (CARD (CARTESIAN X y)) NN); BIG finite and a set in context.
;; ON-MEMBER: goal (IN (LIST u v) BIG), context (IN u X), (IN v y), (IN (LIST u v) (CARTESIAN X y))
(define (ccn-finite-by-subset! X y big on-member)
  (let* ((small (list 'CARTESIAN X y))
         (incl  (list 'FORALL 'z_ (list 'IMPLIES (list 'IN 'z_ small) (list 'IN 'z_ big)))))
    (ccn-set! small)
    (have! incl
      (lambda ()
        (mac 'cartesian-decompose)              ; BEFORE di: rewrites the antecedent in place
        (dk-peel!)
        (let lp ((k 0))
          (let ((ex (any-pred (dk-head? 'FORSOME) (dk-asms))))
            (if (and ex (< k 5)) (begin (dk-split! ex) (lp (+ k 1))))))
        (let* ((eq (dk-pick (lambda (a) (and (pair? a) (eq? (car a) '=) (eq? (cadr a) 'z_))) "z_ = [u,v]"))
               (pr (caddr eq)) (u (cadr pr)) (v (caddr pr)))
          (fact 'pair-in-cartesian X y u v)
          (subst eq)
          (on-member u v))))
    (have! (list 'AND (list 'IN big 'SET) (list 'IN (list 'CARD big) 'NN)))
    (let ((thm (dk-fact! 'card-subset-nn big)))
      (have! (list 'AND (list 'IN small 'SET) incl))
      (dk-apply! thm small)
      (ass))))
(define (ccn-base!)
  (for-each
   (lambda (leaf)
     (dk-focus! leaf)
     (cond
       ((equal? (dk-goal) '(in empty-set set)) (fact 'empty-set-is-set) (ass))
       (#t
        (dk-peel!)                                 ; (IN y SET), (IN (CARD y) NN)
        (let ((y (caddr (cadr (cadr (dk-goal))))))
          (fact 'empty-set-is-set)
          (have! '(IN (CARD EMPTY-SET) NN) (lambda () (mac 'card-empty) (fact 'nn-zero-in) (ass)))
          (ccn-finite-by-subset! 'EMPTY-SET y 'EMPTY-SET
            (lambda (cu cv)
              (dk-only! (list 'IN cu 'EMPTY-SET) (dk-fact! 'empty-set-has-no-members cu))
              (prop)))))))
   (dk-opened (lambda () (comp-mi)))))
(define ccn-step-formula
  `(FORALL S (IMPLIES (AND (IN S SET) (AND (IN (CARD S) NN) (IN S ,ccn-class)))
     (FORALL x (IMPLIES (AND (IN x SET) (NOT (IN x S)))
       (IN (UNION S (PAIR x x)) ,ccn-class))))))
(define (ccn-step!)
  (let* ((landed (dk-peel!))
         (g      (dk-goal))                        ; (in (union S (pair x x)) C)
         (S      (cadr (cadr g)))
         (x      (cadr (caddr (cadr g))))
         (un     (list 'UNION S (list 'PAIR x x))))
    (dk-split-all! landed)
    (have! (list 'AND (list 'IN x 'SET) (list 'IN x 'SET)))
    (fact 'pairing x x)
    (have! (list 'AND (list 'IN S 'SET) (list 'IN (list 'PAIR x x) 'SET)))
    (fact 'union-set-closure S (list 'PAIR x x))
    (let ((ih (dk-landed-find (lambda () (comp-me (list 'IN S ccn-class)))
                              (dk-head? 'forall))))
      (for-each
       (lambda (leaf)
         (dk-focus! leaf)
         (if (equal? (dk-goal) (list 'in un 'set))
             (ass)
             (ccn-step-property! S x un ih)))
       (dk-opened (lambda () (comp-mi)))))))
;; goal: forall y_. y_ in SET => CARD y_ in NN => CARD(CARTESIAN U y_) in NN
(define (ccn-step-property! S x un ih)
  (dk-peel!)
  (let* ((y   (caddr (cadr (cadr (dk-goal)))))
         (p   (list 'VNB-LAMBDA 'w_ y (list 'LIST x 'w_)))
         (img (list 'IMAGE p y))
         (sy  (list 'CARTESIAN S y))
         (big (list 'UNION sy img)))
    (dk-apply! ih y)                              ; (IN (CARD sy) NN)
    (ccn-set! sy)
    (fact 'image-set p y)                         ; (IN img SET)
    (fact 'card-image-finite p y)                 ; (IN (CARD img) NN)
    (have! (list 'AND (list 'IN sy 'SET) (list 'IN img 'SET)))
    (fact 'union-set-closure sy img)
    (fact 'card-union-nn sy img)
    (ccn-finite-by-subset! un y big
      (lambda (cu cv)
        (let ((cases (dk-landed-1 (lambda () (mac-h 'union-membership (list 'IN cu un))))))
          (mac 'union-membership)                 ; goal (OR (IN [u,v] sy) (IN [u,v] img))
          (use-cases cases
            (lambda () (oi-l) (fact 'pair-in-cartesian S y cu cv) (ass))
            (lambda ()
              (oi-r)
              (let* ((pm  (dk-fact! 'pairing-membership x x))
                     (pmu (inst*! pm cu)))
                (have! (list '= cu x) (lambda () (dk-only! pmu (list 'IN cu (list 'PAIR x x))) (prop))))
              (have! (list '= x cu) (lambda () (subst (list '= cu x)) (rfl)))
              (mac 'image-membership-iff)
              (ew cv)
              (dk-conj-close! (lambda ()
                (if (eq? (car (dk-goal)) '=)
                    (begin (lam-b) (subst (list '= x cu)) (rfl))
                    (ass)))))))))))

(sp (make-wff '(FORALL X (FORALL Y
      (IMPLIES (IN X SET) (IMPLIES (IN (CARD X) NN)
        (IMPLIES (IN Y SET) (IMPLIES (IN (CARD Y) NN)
          (IN (CARD (CARTESIAN X Y)) NN)))))))))
(have! (list 'IN 'EMPTY-SET ccn-class) ccn-base!)
(have! ccn-step-formula ccn-step!)
(have! (list 'AND (list 'IN 'EMPTY-SET ccn-class) ccn-step-formula))
(let ((ind (dk-fact! 'finite-set-induction ccn-class)))
  (dk-peel!)
  (let* ((g (dk-goal)) (X (cadr (cadr (cadr g)))) (Y (caddr (cadr (cadr g)))))
    (have! (list 'AND (list 'IN X 'SET) (list 'IN (list 'CARD X) 'NN)))
    (let* ((inx (dk-apply! ind X))
           (px  (dk-landed-find (lambda () (comp-me inx)) (dk-head? 'forall))))
      (dk-apply! px Y)
      (ass))))
(qed 'card-cartesian-nn)
;; ---- the additive group of a_, read off the view ----
(define mir-ag '(RING-ADDITIVE-AG a_))
(define (mir-raag! name acc rhs)
  (sp (make-wff (list 'FORALL 'a_ (list '== (list acc mir-ag) rhs))))
  (di) (slot acc) (mac 'ring-additive-ag) (nth-r)
  ;; `slot' rewrites EVERY occurrence of the accessor, so a CARR on the right-hand
  ;; side became NTH(1, a_) too; a second `slot' takes the left-hand side after it.
  (if (equal? (dk-goal) (list '== rhs (list 'NTH 1 'a_))) (slot acc))
  (if (not (or (equal? (dk-goal) (list '== rhs rhs))
               (equal? (dk-goal) (list '== (list 'NTH 1 'a_) (list 'NTH 1 'a_)))))
      (error "mir-raag!: view slot drifted" (expression->string (dk-goal))))
  (qrfl)
  (qed name))
(mir-raag! 'raag-carr 'CARR '(CARR a_))
(mir-raag! 'raag-opr  'OPR  '(ADD a_))
(mir-raag! 'raag-iden 'IDEN '(ZERO a_))

;; ---- the convolution, pointwise ----
(define (mir-supp f) (list 'SUPP 'a_ 'm_ f))
(define (mir-P f g) (list 'CARTESIAN (mir-supp f) (mir-supp g)))
(define (mir-I f g x) (list 'SEP 'p (mir-P f g) (list '= '((OPR m_) (NTH 1 p) (NTH 2 p)) x)))
(define (mir-L f g x) (list 'VNB-LAMBDA 'p (mir-I f g x) (list '(MUL a_) (list f '(NTH 1 p)) (list g '(NTH 2 p)))))
(define (mir-conv f g x) (list 'FINSUM mir-ag (mir-L f g x) (mir-I f g x)))
(define (mir-mul f g) (list 'MONALG-MUL 'a_ 'm_ f g))

(sp (make-wff `(FORALL a_ (FORALL m_ (FORALL f_ (FORALL g_ (FORALL x_
   (IMPLIES (IN x_ (CARR m_))
     (== (,(mir-mul 'f_ 'g_) x_) ,(mir-conv 'f_ 'g_ 'x_))))))))))
(dk-peel!) (mac 'MONALG-MUL) (lam-b)
(if (not (eq? (car (dk-goal)) '==)) (error "monalg-mul-apply: unexpected goal" (expression->string (dk-goal))))
(qrfl)
(qed 'monalg-mul-apply)

;; supports: (IN (SUPP f) SET) and (IN (CARD (SUPP f)) NN) for an F-typed f, in lanes
(define (mir-supp-facts! f)
  (have! (list 'IN (mir-supp f) 'SET) (lambda () (fact 'supp-in-set 'a_ 'm_ f) (ass)))
  (have! (list 'IN (list 'CARD (mir-supp f)) 'NN)
    (lambda () (mac-h 'finsupp-membership (list 'IN f mir-F))
               (mir-split-head! (list 'IN f '(FUN (CARR m_) (CARR a_))))
               (ass))))
;; the product of the supports is a finite set
(define (mir-P-facts! f g)
  (have! (list 'IN (mir-P f g) 'SET) (lambda () (mac 'cartesian-set-iff) (dk-conj-close!)))
  (fact 'card-cartesian-nn (mir-supp f) (mir-supp g)))
;; the index set at x is a finite set, and the summand is a function on it into CARR(a_)
;; needs in context: mir-P-facts!, mir-fun! f, mir-fun! g, (IN x (CARR m_)), IS-RING a_
(define (mir-conv-type! f g x)
  (let ((I (mir-I f g x)) (L (mir-L f g x)) (P (mir-P f g)))
    (have! (list 'IN I 'SET) (lambda () (sep-set) (ass)))
    (have! (list 'AND (list 'IN P 'SET) (list 'IN (list 'CARD P) 'NN)))
    ;; the inclusion's binder must not be the point x (capture): zc_ is reserved for it
    (if (memq 'zc_ (free-vars I)) (error "mir-conv-type!: zc_ is free in the index set"))
    (have! (list 'AND (list 'IN I 'SET)
                 (list 'FORALL 'zc_ (list 'IMPLIES (list 'IN 'zc_ I) (list 'IN 'zc_ P))))
      (lambda () (mir-both! (list 'IN I 'SET) (lambda () (ass))
                   (lambda () (di) (sep-me (list 'IN 'zc_ I)) (ass)))))
    (fact 'card-subset-nn P I)
    (have! (list 'IN L (list 'FUN I '(CARR a_)))
      (lambda ()
        (dk-lam-t!)
        (let ((pv (dk-di-var!)))
          (sep-me (list 'IN pv I))
          (fact 'cartesian-nth pv (mir-supp f) (mir-supp g))
          (mir-split-head! (list 'IN (list 'NTH 1 pv) (mir-supp f)))
          (mac-h 'supp-membership (list 'IN (list 'NTH 1 pv) (mir-supp f)))
          (mir-split-head! (list 'IN (list 'NTH 1 pv) '(CARR m_)))
          (mac-h 'supp-membership (list 'IN (list 'NTH 2 pv) (mir-supp g)))
          (mir-split-head! (list 'IN (list 'NTH 2 pv) '(CARR m_)))
          (fact 'fun-apply-type-c f '(CARR m_) '(CARR a_) (list 'NTH 1 pv))
          (fact 'fun-apply-type-c g '(CARR m_) '(CARR a_) (list 'NTH 2 pv))
          (fact 'ring-carrier-closed-mul 'a_ (list f (list 'NTH 1 pv)) (list g (list 'NTH 2 pv)))
          (ass))))
    (have! (list 'IN L (list 'FUN I (list 'CARR mir-ag)))
      (lambda () (mac 'raag-carr) (ass)))))
;; the value of the convolution at x lies in CARR(a_)
(define (mir-conv-in-carr! f g x)
  (mir-conv-type! f g x)
  (fact 'ring-additive-ag-is-abelian-group 'a_)
  (fact 'finsum-type mir-ag (mir-I f g x) (mir-L f g x))
  ;; rewrite the landing in place (a `have!' of a claim equal to the goal has no main branch)
  (mac-h 'raag-carr (list 'IN (mir-conv f g x) (list 'CARR mir-ag))))

(sp (make-wff `(FORALL a_ (FORALL m_ (FORALL f_ (FORALL g_ (FORALL x_
   (IMPLIES (IS-RING a_) (IMPLIES (IS-MONOID m_) (IMPLIES (IN f_ ,mir-F) (IMPLIES (IN g_ ,mir-F)
   (IMPLIES (IN x_ (CARR m_))
     (IN (,(mir-mul 'f_ 'g_) x_) (CARR a_))))))))))))))
(dk-peel!)
(fact 'monoid-carrier-is-set 'm_)
(mir-fun! 'f_) (mir-fun! 'g_)
(mir-supp-facts! 'f_) (mir-supp-facts! 'g_)
(mir-P-facts! 'f_ 'g_)
(mir-conv-in-carr! 'f_ 'g_ 'x_)
(mac 'monalg-mul-apply)
(ass)
(qed 'monalg-mul-value-in-carr)
;; ---- monalg-mul-fun: the convolution is finitely supported ----
;; supp(f*g) is contained in the image of supp(f) x supp(g) under the
;; multiplication map of M: at a point x OUTSIDE that image the index set of the
;; convolution has no member, so every summand is (vacuously) the identity and
;; finsum-all-id makes the sum ZERO(A).
(define (mir-phi f g) (list 'VNB-LAMBDA 'q (mir-P f g) '((OPR m_) (NTH 1 q) (NTH 2 q))))
(define mir-H (mir-mul 'f_ 'g_))
(sp (make-wff `(FORALL a_ (FORALL m_ (FORALL f_ (FORALL g_
   (IMPLIES (IS-RING a_) (IMPLIES (IS-MONOID m_) (IMPLIES (IN f_ ,mir-F) (IMPLIES (IN g_ ,mir-F)
     (IN ,mir-H ,mir-F)))))))))))
(dk-peel!)
(fact 'monoid-carrier-is-set 'm_) (fact 'ring-zero-in 'a_)
(mir-fun! 'f_) (mir-fun! 'g_) (mir-supp-facts! 'f_) (mir-supp-facts! 'g_) (mir-P-facts! 'f_ 'g_)
(fact 'ring-additive-ag-is-abelian-group 'a_)
(mac 'finsupp-membership)
(mir-both! `(IN ,mir-H (FUN (CARR m_) (CARR a_)))
  (lambda () (mac 'MONALG-MUL) (dk-lam-t!)
    (let ((xv (dk-di-var!))) (mir-conv-in-carr! 'f_ 'g_ xv) (ass)))
  (lambda ()
    (let* ((phi (mir-phi 'f_ 'g_)) (P (mir-P 'f_ 'g_)) (img (list 'IMAGE phi P))
           (sh (mir-supp mir-H)))
      (have! (list 'IN sh 'SET) (lambda () (fact 'supp-in-set 'a_ 'm_ mir-H) (ass)))
      (fact 'image-set phi P) (fact 'card-image-finite phi P)
      (have! (list 'AND (list 'IN img 'SET) (list 'IN (list 'CARD img) 'NN)))
      (mir-supp-finite-by-subset! sh img
        (lambda ()
          (di)
          (mac-h 'supp-membership (list 'IN 'z_ sh))
          (mir-split-head! '(IN z_ (CARR m_)))
          (mac-h 'monalg-mul-apply (list 'NOT (list '= (list mir-H 'z_) '(ZERO a_))))
          (mir-conv-type! 'f_ 'g_ 'z_)
          (let ((I (mir-I 'f_ 'g_ 'z_)) (L (mir-L 'f_ 'g_ 'z_)) (conv (mir-conv 'f_ 'g_ 'z_)))
            (use-em (list 'IN 'z_ img)
              (lambda () (ass))
              (lambda ()
                (have! (list 'FORALL 'w_ (list 'IMPLIES (list 'IN 'w_ I) (list '= (list L 'w_) (list 'IDEN mir-ag))))
                  (lambda ()
                    (di)
                    (sep-me (list 'IN 'w_ I))
                    (have! (list 'IN 'z_ img)
                      (lambda () (mac 'image-membership-iff) (ew 'w_)
                        (dk-conj-close! (lambda () (if (eq? (car (dk-goal)) '=) (begin (lam-b) (ass)) (ass))))))
                    (ai (list 'NOT (list 'IN 'z_ img)))))
                (fact 'finsum-all-id mir-ag I L)
                (have! (list '= conv '(ZERO a_))
                  (lambda () (subst (list '= conv (list 'IDEN mir-ag))) (mac 'raag-iden) (rfl)))
                (ai (list 'NOT (list '= conv '(ZERO a_))))))))))))
(qed 'monalg-mul-fun)
;; ======================================================================
;; DISTRIBUTIVITY -- bricks first
;; ======================================================================
;; a member of a cartesian product is the pair of its projections (the equation form)
(sp (make-wff '(FORALL x_ (FORALL aa (FORALL bb
   (IMPLIES (IN x_ (CARTESIAN aa bb))
     (= x_ (LIST (NTH 1 x_) (NTH 2 x_)))))))))
(mac 'cartesian-decompose)
(dk-peel!)
(let lp ((k 0))
  (let ((ex (any-pred (dk-head? 'FORSOME) (dk-asms))))
    (if (and ex (< k 5)) (begin (dk-split! ex) (lp (+ k 1))))))
(let* ((eq (dk-pick (lambda (a) (and (pair? a) (eq? (car a) '=) (eq? (cadr a) 'x_))) "x_ = [u,v]"))
       (pr (caddr eq)))
  (fact 'pair-in-cartesian 'aa 'bb (cadr pr) (caddr pr))
  (subst eq)
  (nth-r)
  (rfl))
(qed 'cartesian-pair-eq)

;; supp(g+h) is contained in supp(g) u supp(h)  (the inclusion inside monalg-add-fun, as a lemma)
(sp (make-wff `(FORALL a_ (FORALL m_ (FORALL g_ (FORALL h_ (FORALL z_
   (IMPLIES (IS-RING a_) (IMPLIES (IN g_ ,mir-F) (IMPLIES (IN h_ ,mir-F)
     (IMPLIES (IN z_ ,(mir-supp (mir-add 'g_ 'h_)))
       (IN z_ (UNION ,(mir-supp 'g_) ,(mir-supp 'h_))))))))))))))
(dk-peel!)
(fact 'ring-zero-in 'a_)
(mir-fun! 'g_) (mir-fun! 'h_)
(mac-h 'supp-membership (list 'IN 'z_ (mir-supp (mir-add 'g_ 'h_))))
(mir-split-head! '(IN z_ (CARR m_)))
(mac-h 'monalg-add-apply (list 'NOT (list '= (list (mir-add 'g_ 'h_) 'z_) '(ZERO a_))))
(mac 'union-membership)
(mac 'supp-membership)
(fact 'fun-apply-type-c 'g_ '(CARR m_) '(CARR a_) 'z_)
(fact 'fun-apply-type-c 'h_ '(CARR m_) '(CARR a_) 'z_)
(use-em '(= (g_ z_) (ZERO a_))
  (lambda ()
    (have! '(NOT (= (h_ z_) (ZERO a_)))
      (lambda ()
        (di)
        (have! '(= ((ADD a_) (g_ z_) (h_ z_)) (ZERO a_))
          (lambda () (subst '(= (g_ z_) (ZERO a_))) (subst '(= (h_ z_) (ZERO a_)))
                     (fact 'ring-add-left-id 'a_ '(ZERO a_)) (ass)))
        (ai '(NOT (= ((ADD a_) (g_ z_) (h_ z_)) (ZERO a_))))))
    (oi-r) (dk-conj-close!))
  (lambda () (oi-l) (dk-conj-close!)))
(qed 'supp-add-subset)

;; (= (fn q) (ZERO a_)) from (NOT (IN q (SUPP fn))) and (IN q (CARR m_)) in context
(define (mir-zero-off-supp! fn q)
  (let ((iff (dk-fact! 'supp-membership 'a_ 'm_ fn q))
        (eq  (list '= (list fn q) '(ZERO a_))))
    (have! eq (lambda () (dk-only! iff (list 'NOT (list 'IN q (mir-supp fn))) (list 'IN q '(CARR m_))) (prop)))
    eq))
;; (IN q (CARR m_)) off (IN q S) for S a support or a union of two supports.
;; The goal-side form closes the GOAL (IN q (CARR m_)); the lane form lands it.
(define (mir-carr-goal! q S)
  (cond ((eq? (car S) 'SUPP)
         (mac-h 'supp-membership (list 'IN q S)) (mir-split-head! (list 'IN q '(CARR m_))) (ass))
        ((eq? (car S) 'UNION)
         (let ((cases (dk-landed-1 (lambda () (mac-h 'union-membership (list 'IN q S))))))
           (use-cases cases
             (lambda () (mir-carr-goal! q (cadr S)))
             (lambda () (mir-carr-goal! q (caddr S))))))
        ;; the singleton {e}: q = e, and (IN e (CARR m_)) is in context
        ((eq? (car S) 'PAIR)
         (let* ((e (cadr S)) (pm (dk-fact! 'pairing-membership e e)) (iff (inst*! pm q)))
           (have! (list '= q e) (lambda () (dk-only! iff (list 'IN q S)) (prop)))
           (subst (list '= q e)) (ass)))
        (#t (error "mir-carr-goal!: not a support" S))))
;; the monoid's identity laws, off the IS-MONOID unfold (monoid-left-id / -right-id are
;; unwarranted axioms in monoid.scm; the unfold is free)
(define (mir-monoid-id! side t)       ; lands (= ((OPR m_) e t) t) resp. (= ((OPR m_) t e) t)
  (let ((eq (if (eq? side 'left) (list '= (list '(OPR m_) '(IDEN m_) t) t) (list '= (list '(OPR m_) t '(IDEN m_)) t))))
    (have! eq
      (lambda ()
        (mac-h 'is-monoid '(IS-MONOID m_))
        (dk-split! (any-pred (dk-head? 'AND) (dk-asms)))
        (let ((idf (dk-pick (lambda (h) (and (pair? h) (eq? (car h) 'is-identity))) "is-identity conjunct")))
          (mac-h 'is-identity idf)
          (let ((both (dk-apply! (dk-pick (lambda (h) (and ((dk-head? 'FORALL) h) (pair? (caddr h)) (eq? (car (caddr h)) 'IMPLIES)
                                                            (pair? (caddr (caddr h))) (eq? (car (caddr (caddr h))) 'AND)))
                                          "identity universal") t)))
            (dk-split! both)
            (ass)))))
    eq))

(define (mir-in-carr-off-supp! q S)
  (have! (list 'IN q '(CARR m_)) (lambda () (mir-carr-goal! q S))))

;; ---- index sets over an arbitrary product of two "support-like" sets ----
(define (mir-IQ A B x) (list 'SEP 'p (list 'CARTESIAN A B) (list '= '((OPR m_) (NTH 1 p) (NTH 2 p)) x)))
(define (mir-LQ f g A B x) (list 'VNB-LAMBDA 'p (mir-IQ A B x) (list '(MUL a_) (list f '(NTH 1 p)) (list g '(NTH 2 p)))))
;; needs in context: A, B in SET with CARD in NN; f g in FUN(CARR m_, CARR a_); IS-RING a_;
;; and every member of A, B lies in CARR(m_) (A, B supports or unions of supports)
(define (mir-IQ-facts! A B x)
  (let ((I (mir-IQ A B x)) (Q (list 'CARTESIAN A B)))
    (have! (list 'IN Q 'SET) (lambda () (mac 'cartesian-set-iff) (dk-conj-close!)))
    (fact 'card-cartesian-nn A B)
    (have! (list 'IN I 'SET) (lambda () (sep-set) (ass)))
    (have! (list 'AND (list 'IN Q 'SET) (list 'IN (list 'CARD Q) 'NN)))
    (if (memq 'zc_ (free-vars I)) (error "mir-IQ-facts!: zc_ is free in the index set"))
    (have! (list 'AND (list 'IN I 'SET)
                 (list 'FORALL 'zc_ (list 'IMPLIES (list 'IN 'zc_ I) (list 'IN 'zc_ Q))))
      (lambda () (mir-both! (list 'IN I 'SET) (lambda () (ass))
                   (lambda () (di) (sep-me (list 'IN 'zc_ I)) (ass)))))
    (fact 'card-subset-nn Q I)))
(define (mir-LQ-type! f g A B x)
  (let ((I (mir-IQ A B x)) (L (mir-LQ f g A B x)))
    (have! (list 'IN L (list 'FUN I '(CARR a_)))
      (lambda ()
        (dk-lam-t!)
        (let ((pv (dk-di-var!)))
          (sep-me (list 'IN pv I))
          (fact 'cartesian-nth pv A B)
          (mir-split-head! (list 'IN (list 'NTH 1 pv) A))
          (mir-in-carr-off-supp! (list 'NTH 1 pv) A)
          (mir-in-carr-off-supp! (list 'NTH 2 pv) B)
          (fact 'fun-apply-type-c f '(CARR m_) '(CARR a_) (list 'NTH 1 pv))
          (fact 'fun-apply-type-c g '(CARR m_) '(CARR a_) (list 'NTH 2 pv))
          (fact 'ring-carrier-closed-mul 'a_ (list f (list 'NTH 1 pv)) (list g (list 'NTH 2 pv)))
          (ass))))
    (have! (list 'IN L (list 'FUN I (list 'CARR mir-ag))) (lambda () (mac 'raag-carr) (ass)))
    (fact 'finsum-type mir-ag I L)
    (mac-h 'raag-carr (list 'IN (list 'FINSUM mir-ag L I) (list 'CARR mir-ag)))))

;; The restated `finsum-congruence' (2026-09-17) wants its FIRST summand typed
;; POINTWISE on the index set -- forall z in I. L z in CARR(ag) -- and not as a
;; FUN, because a back-peeled family never is one.  Every summand in this file
;; IS a FUN on its own index set (mir-LQ-type!), so the lane is one
;; `fun-apply-type-c' per member.  `dk-have!' rather than `have!': mir-embed! is
;; called six times in the two distributivity proofs and a `cut' of a formula
;; already in context is a silent self-loop.  Lands and returns the claim.
(define (mir-ptwise-type! L I)
  (let ((claim (list 'FORALL 'z (list 'IMPLIES (list 'IN 'z I)
                                      (list 'IN (list L 'z) (list 'CARR mir-ag))))))
    (dk-have! claim
      (lambda ()
        (let ((zv (cadr (dk-landed-1 (lambda () (di))))))
          (fact 'fun-apply-type-c L I (list 'CARR mir-ag) zv)
          (ass))))
    claim))

;; ---- THE EMBED: FINSUM over I(A,B) = FINSUM over I(A',B') when A c A', B c B' and the
;; summand vanishes at every index of the larger set outside the smaller.
;;   IN-BIG!:   goal (IN t A') from (IN t A) -- resp. B; called as (in-big! t 'left|'right)
;;   VANISH!:   goal (= ((MUL a_) (f (NTH 1 z)) (g (NTH 2 z))) (ZERO a_)) with in context
;;              (IN z (CARTESIAN A' B')), (NOT (IN z I)) and the projections typed.
;; Lands (= (FINSUM ag L I) (FINSUM ag L' I')) and returns it.
(define (mir-embed! f g A B A2 B2 x in-big! vanish!)
  (let* ((I  (mir-IQ A B x))   (L  (mir-LQ f g A B x))
         (I2 (mir-IQ A2 B2 x)) (L2 (mir-LQ f g A2 B2 x))
         (Q  (list 'CARTESIAN A B)) (Q2 (list 'CARTESIAN A2 B2))
         (incl (list 'FORALL 'zc_ (list 'IMPLIES (list 'IN 'zc_ I) (list 'IN 'zc_ I2))))
         (eqL (list '= (list 'FINSUM mir-ag L I) (list 'FINSUM mir-ag L2 I)))
         (eqE (list '= (list 'FINSUM mir-ag L2 I2) (list 'FINSUM mir-ag L2 I)))
         (goal (list '= (list 'FINSUM mir-ag L I) (list 'FINSUM mir-ag L2 I2))))
    ;; I c I2
    (have! incl
      (lambda ()
        (di)
        (sep-me (list 'IN 'zc_ I))
        (fact 'cartesian-nth 'zc_ A B)
        (mir-split-head! (list 'IN '(NTH 1 zc_) A))
        (fact 'cartesian-pair-eq 'zc_ A B)
        (have! (list 'IN 'zc_ Q2)
          (lambda () (subst (list '= 'zc_ '(LIST (NTH 1 zc_) (NTH 2 zc_))))
                     ;; dk-have!: on the unchanged side the claim is already in context
                     (dk-have! (list 'IN '(NTH 1 zc_) A2) (lambda () (in-big! '(NTH 1 zc_) 'left)))
                     (dk-have! (list 'IN '(NTH 2 zc_) B2) (lambda () (in-big! '(NTH 2 zc_) 'right)))
                     (fact 'pair-in-cartesian A2 B2 '(NTH 1 zc_) '(NTH 2 zc_)) (ass)))
        (for-each (lambda (n) (dk-focus! n) (ass)) (dk-opened (lambda () (sep-mi))))))
    (have! (list 'SUBSET I I2) (lambda () (mac 'subset-def) (ass)))
    ;; L2 vanishes on I2 \ I
    (have! (list 'FORALL 'zc_ (list 'IMPLIES (list 'AND (list 'IN 'zc_ I2) (list 'NOT (list 'IN 'zc_ I)))
                                   (list '= (list L2 'zc_) (list 'IDEN mir-ag))))
      (lambda ()
        (dk-split-all! (dk-peel!))
        (lam-b)                       ; BEFORE sep-me, which consumes the (IN zc_ I2) the beta needs
        (sep-me (list 'IN 'zc_ I2))
        (fact 'cartesian-nth 'zc_ A2 B2)
        (mir-split-head! (list 'IN '(NTH 1 zc_) A2))
        (mir-in-carr-off-supp! '(NTH 1 zc_) A2)
        (mir-in-carr-off-supp! '(NTH 2 zc_) B2)
        (fact 'fun-apply-type-c f '(CARR m_) '(CARR a_) '(NTH 1 zc_))
        (fact 'fun-apply-type-c g '(CARR m_) '(CARR a_) '(NTH 2 zc_))
        (fact 'cartesian-pair-eq 'zc_ A2 B2)
        (mac 'raag-iden)
        (vanish!)))
    ;; L = L2 on I  (the pointwise typing finsum-congruence also wants is below)
    (have! (list 'FORALL 'zc_ (list 'IMPLIES (list 'IN 'zc_ I) (list '= (list L 'zc_) (list L2 'zc_))))
      (lambda ()
        (di)
        (dk-apply! incl 'zc_)
        (fact 'fun-apply-type-c L I (list 'CARR mir-ag) 'zc_)
        (lam-b-h (list 'IN (list L 'zc_) (list 'CARR mir-ag)))
        (lam-b)
        (rfl)))
    (mir-ptwise-type! L I)
    (fact 'finsum-congruence mir-ag I L L2)
    (fact 'finsum-embed mir-ag I I2 L2)
    (have! goal (lambda () (subst eqE) (ass)))
    goal))
;; ---- left distributivity, pointwise ----
(define mir-gh (mir-add 'g_ 'h_))
(define (mir-big-right-union! fn)   ; goal (IN t (UNION Sg Sh)) from (IN t (SUPP fn)) in context
  (lambda (t side)
    (if (eq? side 'left) (ass)
        (cond ((equal? fn 'g_) (mac 'union-membership) (oi-l) (ass))
              ((equal? fn 'h_) (mac 'union-membership) (oi-r) (ass))
              (#t (fact 'supp-add-subset 'a_ 'm_ 'g_ 'h_ t) (ass))))))
;; vanish closer: the RIGHT component of zc_ lies outside SUPP(fn), so fn of it is zero
(define (mir-vanish-right! f fn A B x)
  (lambda ()
    (let ((I (mir-IQ A B x)))
      (have! (list 'NOT (list 'IN '(NTH 2 zc_) B))
        (lambda ()
          (di)
          (have! (list 'IN 'zc_ I)
            (lambda ()
              (for-each (lambda (n) (dk-focus! n)
                          (if (eq? (car (dk-goal)) '=) (ass)
                              (begin (subst '(= zc_ (LIST (NTH 1 zc_) (NTH 2 zc_))))
                                     (fact 'pair-in-cartesian A B '(NTH 1 zc_) '(NTH 2 zc_)) (ass))))
                        (dk-opened (lambda () (sep-mi))))))
          (ai (list 'NOT (list 'IN 'zc_ I)))))
      (let ((eq (mir-zero-off-supp! fn '(NTH 2 zc_))))
        (subst eq)
        (fact 'ring-mul-zero-right 'a_ (list f '(NTH 1 zc_)))
        (ass)))))
(define (mir-lam-b-all!)          ; beta every licensed redex, however nested
  (let loop ((k 0))
    (when (mir-has? (lambda (t) (and (pair? t) (pair? (car t)) (eq? (caar t) 'VNB-LAMBDA))))
      (if (> k 6) (error "mir-lam-b-all!: runaway"))
      (let ((g (dk-goal))) (lam-b) (if (equal? g (dk-goal)) (error "mir-lam-b-all!: no progress")))
      (loop (+ k 1)))))

(let* ((Sf (mir-supp 'f_)) (Sg (mir-supp 'g_)) (Sh (mir-supp 'h_)) (Sgh (mir-supp mir-gh))
       (SgUh (list 'UNION Sg Sh))
       (U  (mir-IQ Sf SgUh 'x_))
       (L1 (mir-LQ 'f_ mir-gh Sf SgUh 'x_))
       (L2 (mir-LQ 'f_ 'g_ Sf SgUh 'x_))
       (L3 (mir-LQ 'f_ 'h_ Sf SgUh 'x_))
       (LS (list 'VNB-LAMBDA 'z U (list (list 'OPR mir-ag) (list L2 'z) (list L3 'z))))
       (F2 (list 'FINSUM mir-ag L2 U)) (F3 (list 'FINSUM mir-ag L3 U)))
  (sp (make-wff `(FORALL a_ (FORALL m_ (FORALL f_ (FORALL g_ (FORALL h_ (FORALL x_
     (IMPLIES (IS-RING a_) (IMPLIES (IS-MONOID m_)
     (IMPLIES (IN f_ ,mir-F) (IMPLIES (IN g_ ,mir-F) (IMPLIES (IN h_ ,mir-F)
     (IMPLIES (IN x_ (CARR m_))
       (= ,(mir-conv 'f_ mir-gh 'x_)
          ((ADD a_) ,(mir-conv 'f_ 'g_ 'x_) ,(mir-conv 'f_ 'h_ 'x_)))))))))))))))))
  (dk-peel!)
  (fact 'monoid-carrier-is-set 'm_) (fact 'ring-zero-in 'a_) (fact 'ring-additive-ag-is-abelian-group 'a_)
  (fact 'monalg-add-fun 'a_ 'm_ 'g_ 'h_)
  (mir-fun! 'f_) (mir-fun! 'g_) (mir-fun! 'h_) (mir-fun! mir-gh)
  (mir-supp-facts! 'f_) (mir-supp-facts! 'g_) (mir-supp-facts! 'h_) (mir-supp-facts! mir-gh)
  (have! (list 'AND (list 'IN Sg 'SET) (list 'IN Sh 'SET)))
  (fact 'union-set-closure Sg Sh) (fact 'card-union-nn Sg Sh)
  (mir-IQ-facts! Sf Sgh 'x_) (mir-IQ-facts! Sf Sg 'x_) (mir-IQ-facts! Sf Sh 'x_) (mir-IQ-facts! Sf SgUh 'x_)
  (mir-LQ-type! 'f_ mir-gh Sf Sgh 'x_) (mir-LQ-type! 'f_ 'g_ Sf Sg 'x_) (mir-LQ-type! 'f_ 'h_ Sf Sh 'x_)
  (mir-LQ-type! 'f_ mir-gh Sf SgUh 'x_) (mir-LQ-type! 'f_ 'g_ Sf SgUh 'x_) (mir-LQ-type! 'f_ 'h_ Sf SgUh 'x_)
  (let ((e1 (mir-embed! 'f_ mir-gh Sf Sgh Sf SgUh 'x_ (mir-big-right-union! mir-gh) (mir-vanish-right! 'f_ mir-gh Sf Sgh 'x_)))
        (e2 (mir-embed! 'f_ 'g_ Sf Sg Sf SgUh 'x_ (mir-big-right-union! 'g_) (mir-vanish-right! 'f_ 'g_ Sf Sg 'x_)))
        (e3 (mir-embed! 'f_ 'h_ Sf Sh Sf SgUh 'x_ (mir-big-right-union! 'h_) (mir-vanish-right! 'f_ 'h_ Sf Sh 'x_))))
    ;; pointwise on U: L1 z = OPR(L2 z, L3 z), by ring-left-dist
    (have! (list 'FORALL 'zc_ (list 'IMPLIES (list 'IN 'zc_ U) (list '= (list L1 'zc_) (list LS 'zc_))))
      (lambda ()
        (di)
        (mir-lam-b-all!)              ; BEFORE sep-me, which consumes the (IN zc_ U) the betas need
        (sep-me (list 'IN 'zc_ U))
        (fact 'cartesian-nth 'zc_ Sf SgUh)
        (mir-split-head! (list 'IN '(NTH 1 zc_) Sf))
        (mir-in-carr-off-supp! '(NTH 1 zc_) Sf)
        (mir-in-carr-off-supp! '(NTH 2 zc_) SgUh)
        (fact 'fun-apply-type-c 'f_ '(CARR m_) '(CARR a_) '(NTH 1 zc_))
        (fact 'fun-apply-type-c 'g_ '(CARR m_) '(CARR a_) '(NTH 2 zc_))
        (fact 'fun-apply-type-c 'h_ '(CARR m_) '(CARR a_) '(NTH 2 zc_))
        (mac 'raag-opr)
        (mir-mac-all! 'monalg-add-apply 'MONALG-ADD)
        (fact 'ring-left-dist 'a_ '(f_ (NTH 1 zc_)) '(g_ (NTH 2 zc_)) '(h_ (NTH 2 zc_)))
        (ass)))
    (mir-ptwise-type! L1 U)
    (fact 'finsum-congruence mir-ag U L1 LS)
    (fact 'finsum-add-ag mir-ag U L2 L3)
    (fact 'ring-add-closed 'a_ F2 F3)
    (subst e1) (subst e2) (subst e3)
    (subst (list '= (list 'FINSUM mir-ag L1 U) (list 'FINSUM mir-ag LS U)))
    (subst (list '= (list 'FINSUM mir-ag LS U) (list (list 'OPR mir-ag) F2 F3)))
    (mac 'raag-opr)
    (rfl))
  (qed 'monalg-distrib-left-at))
;; ---- right distributivity, pointwise (the mirror: the LEFT factor is the sum) ----
(define mir-fg (mir-add 'f_ 'g_))
(define (mir-big-left-union! fn)    ; goal (IN t (UNION Sf Sg)) from (IN t (SUPP fn)) in context
  (lambda (t side)
    (if (eq? side 'right) (ass)
        (cond ((equal? fn 'f_) (mac 'union-membership) (oi-l) (ass))
              ((equal? fn 'g_) (mac 'union-membership) (oi-r) (ass))
              (#t (fact 'supp-add-subset 'a_ 'm_ 'f_ 'g_ t) (ass))))))
;; vanish closer: the LEFT component of zc_ lies outside SUPP(fn), so fn of it is zero
(define (mir-vanish-left! fn g A B x)
  (lambda ()
    (let ((I (mir-IQ A B x)))
      (have! (list 'NOT (list 'IN '(NTH 1 zc_) A))
        (lambda ()
          (di)
          (have! (list 'IN 'zc_ I)
            (lambda ()
              (for-each (lambda (n) (dk-focus! n)
                          (if (eq? (car (dk-goal)) '=) (ass)
                              (begin (subst '(= zc_ (LIST (NTH 1 zc_) (NTH 2 zc_))))
                                     (fact 'pair-in-cartesian A B '(NTH 1 zc_) '(NTH 2 zc_)) (ass))))
                        (dk-opened (lambda () (sep-mi))))))
          (ai (list 'NOT (list 'IN 'zc_ I)))))
      (let ((eq (mir-zero-off-supp! fn '(NTH 1 zc_))))
        (subst eq)
        (fact 'ring-mul-zero-left 'a_ (list g '(NTH 2 zc_)))
        (ass)))))

(let* ((Sf (mir-supp 'f_)) (Sg (mir-supp 'g_)) (Sh (mir-supp 'h_)) (Sfg (mir-supp mir-fg))
       (SfUg (list 'UNION Sf Sg))
       (U  (mir-IQ SfUg Sh 'x_))
       (L1 (mir-LQ mir-fg 'h_ SfUg Sh 'x_))
       (L2 (mir-LQ 'f_ 'h_ SfUg Sh 'x_))
       (L3 (mir-LQ 'g_ 'h_ SfUg Sh 'x_))
       (LS (list 'VNB-LAMBDA 'z U (list (list 'OPR mir-ag) (list L2 'z) (list L3 'z))))
       (F2 (list 'FINSUM mir-ag L2 U)) (F3 (list 'FINSUM mir-ag L3 U)))
  (sp (make-wff `(FORALL a_ (FORALL m_ (FORALL f_ (FORALL g_ (FORALL h_ (FORALL x_
     (IMPLIES (IS-RING a_) (IMPLIES (IS-MONOID m_)
     (IMPLIES (IN f_ ,mir-F) (IMPLIES (IN g_ ,mir-F) (IMPLIES (IN h_ ,mir-F)
     (IMPLIES (IN x_ (CARR m_))
       (= ,(mir-conv mir-fg 'h_ 'x_)
          ((ADD a_) ,(mir-conv 'f_ 'h_ 'x_) ,(mir-conv 'g_ 'h_ 'x_)))))))))))))))))
  (dk-peel!)
  (fact 'monoid-carrier-is-set 'm_) (fact 'ring-zero-in 'a_) (fact 'ring-additive-ag-is-abelian-group 'a_)
  (fact 'monalg-add-fun 'a_ 'm_ 'f_ 'g_)
  (mir-fun! 'f_) (mir-fun! 'g_) (mir-fun! 'h_) (mir-fun! mir-fg)
  (mir-supp-facts! 'f_) (mir-supp-facts! 'g_) (mir-supp-facts! 'h_) (mir-supp-facts! mir-fg)
  (have! (list 'AND (list 'IN Sf 'SET) (list 'IN Sg 'SET)))
  (fact 'union-set-closure Sf Sg) (fact 'card-union-nn Sf Sg)
  (mir-IQ-facts! Sfg Sh 'x_) (mir-IQ-facts! Sf Sh 'x_) (mir-IQ-facts! Sg Sh 'x_) (mir-IQ-facts! SfUg Sh 'x_)
  (mir-LQ-type! mir-fg 'h_ Sfg Sh 'x_) (mir-LQ-type! 'f_ 'h_ Sf Sh 'x_) (mir-LQ-type! 'g_ 'h_ Sg Sh 'x_)
  (mir-LQ-type! mir-fg 'h_ SfUg Sh 'x_) (mir-LQ-type! 'f_ 'h_ SfUg Sh 'x_) (mir-LQ-type! 'g_ 'h_ SfUg Sh 'x_)
  (let ((e1 (mir-embed! mir-fg 'h_ Sfg Sh SfUg Sh 'x_ (mir-big-left-union! mir-fg) (mir-vanish-left! mir-fg 'h_ Sfg Sh 'x_)))
        (e2 (mir-embed! 'f_ 'h_ Sf Sh SfUg Sh 'x_ (mir-big-left-union! 'f_) (mir-vanish-left! 'f_ 'h_ Sf Sh 'x_)))
        (e3 (mir-embed! 'g_ 'h_ Sg Sh SfUg Sh 'x_ (mir-big-left-union! 'g_) (mir-vanish-left! 'g_ 'h_ Sg Sh 'x_))))
    (have! (list 'FORALL 'zc_ (list 'IMPLIES (list 'IN 'zc_ U) (list '= (list L1 'zc_) (list LS 'zc_))))
      (lambda ()
        (di)
        (mir-lam-b-all!)              ; BEFORE sep-me, which consumes the (IN zc_ U) the betas need
        (sep-me (list 'IN 'zc_ U))
        (fact 'cartesian-nth 'zc_ SfUg Sh)
        (mir-split-head! (list 'IN '(NTH 1 zc_) SfUg))
        (mir-in-carr-off-supp! '(NTH 1 zc_) SfUg)
        (mir-in-carr-off-supp! '(NTH 2 zc_) Sh)
        (fact 'fun-apply-type-c 'f_ '(CARR m_) '(CARR a_) '(NTH 1 zc_))
        (fact 'fun-apply-type-c 'g_ '(CARR m_) '(CARR a_) '(NTH 1 zc_))
        (fact 'fun-apply-type-c 'h_ '(CARR m_) '(CARR a_) '(NTH 2 zc_))
        (mac 'raag-opr)
        (mir-mac-all! 'monalg-add-apply 'MONALG-ADD)
        (fact 'ring-right-dist 'a_ '(f_ (NTH 1 zc_)) '(g_ (NTH 1 zc_)) '(h_ (NTH 2 zc_)))
        (ass)))
    (mir-ptwise-type! L1 U)
    (fact 'finsum-congruence mir-ag U L1 LS)
    (fact 'finsum-add-ag mir-ag U L2 L3)
    (fact 'ring-add-closed 'a_ F2 F3)
    (subst e1) (subst e2) (subst e3)
    (subst (list '= (list 'FINSUM mir-ag L1 U) (list 'FINSUM mir-ag LS U)))
    (subst (list '= (list 'FINSUM mir-ag LS U) (list (list 'OPR mir-ag) F2 F3)))
    (mac 'raag-opr)
    (rfl))
  (qed 'monalg-distrib-right-at))
;; ======================================================================
;; THE UNIT LAWS -- the indicator of IDEN(M) is a two-sided identity
;; ======================================================================
(define mir-one '(MONALG-ONE a_ m_))
(define mir-ee '(PAIR (IDEN m_) (IDEN m_)))
;; supp(ONE) is contained in {IDEN(M)}  (the inclusion inside monalg-one-in, as a lemma)
(sp (make-wff `(FORALL a_ (FORALL m_ (FORALL z_
   (IMPLIES (IS-RING a_) (IMPLIES (IS-MONOID m_)
     (IMPLIES (IN z_ ,(mir-supp mir-one)) (IN z_ ,mir-ee)))))))))
(dk-peel!)
(fact 'ring-zero-in 'a_) (fact 'ring-one-in 'a_) (mir-monoid-iden!)
(fact 'membership-implies-sethood '(IDEN m_) '(CARR m_))
(have! '(AND (IN (IDEN m_) SET) (IN (IDEN m_) SET)))
(mac-h 'supp-membership (list 'IN 'z_ (mir-supp mir-one)))
(mir-split-head! '(IN z_ (CARR m_)))
(mac-h 'monalg-one-apply `(NOT (= (,mir-one z_) (ZERO a_))))
(let* ((pm  (dk-fact! 'pairing-membership '(IDEN m_) '(IDEN m_)))
       (iff (dk-apply! pm 'z_))
       (ifz '(IF (= z_ (IDEN m_)) (ONE a_) (ZERO a_))))
  (use-em '(= z_ (IDEN m_))
    (lambda () (dk-only! iff '(= z_ (IDEN m_))) (prop))
    (lambda ()
      (have! `(= ,ifz (ZERO a_)) (lambda () (mir-if! ifz 'false (lambda () (ass))) (rfl)))
      (ai `(NOT (= ,ifz (ZERO a_)))))))
(qed 'monalg-one-supp-subset)

;; (= b a) from (= a b) in context, when b does not contain a
(define (mir-sym! eq)
  (let ((r (list '= (caddr eq) (cadr eq))))
    (have! r (lambda () (subst eq) (rfl)))
    r))
;; the singleton's facts: e in SET, {e} in SET, CARD {e} in NN, e in {e}, e in CARR(m_)
(define (mir-singleton-facts!)
  (mir-monoid-iden!)
  (fact 'membership-implies-sethood '(IDEN m_) '(CARR m_))
  (have! '(AND (IN (IDEN m_) SET) (IN (IDEN m_) SET)))
  (fact 'pairing '(IDEN m_) '(IDEN m_))
  (fact 'card-singleton '(IDEN m_))
  (fact 'nn-zero-in) (fact 'nn-succ-closed 0)
  (have! `(IN (CARD ,mir-ee) NN) (lambda () (subst `(= (CARD ,mir-ee) (succ 0))) (ass)))
  (have! `(IN (IDEN m_) ,mir-ee)
    (lambda () (let* ((pm (dk-fact! 'pairing-membership '(IDEN m_) '(IDEN m_))) (iff (inst*! pm '(IDEN m_))))
                 (have! '(= (IDEN m_) (IDEN m_)) (lambda () (rfl)))
                 (dk-only! iff '(= (IDEN m_) (IDEN m_))) (prop)))))
;; (= q (IDEN m_)) from (IN q {e}) in context
(define (mir-in-singleton! q)
  (let* ((pm (dk-fact! 'pairing-membership '(IDEN m_) '(IDEN m_))) (iff (inst*! pm q))
         (eq (list '= q '(IDEN m_))))
    (have! eq (lambda () (dk-only! iff (list 'IN q mir-ee)) (prop)))
    eq))

;; SIDE = left:  (ONE * f)(x) = f(x), index sets over supp(ONE) x supp(f), embedded in {e} x supp(f)
;; SIDE = right: (f * ONE)(x) = f(x), the mirror
(define (mir-one-law-at! side name)
  (let* ((S1 (mir-supp mir-one)) (Sf (mir-supp 'f_)) (e '(IDEN m_))
         (left? (eq? side 'left))
         (fa (if left? mir-one 'f_)) (fb (if left? 'f_ mir-one))         ; the two factors
         (A  (if left? S1 Sf)) (B (if left? Sf S1))                       ; the small product
         (A2 (if left? mir-ee Sf)) (B2 (if left? Sf mir-ee))              ; the big product
         (U  (mir-IQ A2 B2 'x_)) (LU (mir-LQ fa fb A2 B2 'x_))
         (i0 (if left? (list 'LIST e 'x_) (list 'LIST 'x_ e)))
         (FU (list 'FINSUM mir-ag LU U))
         (nx (if left? '(NTH 2 j_) '(NTH 1 j_)))                          ; the f-component of j_
         (ne (if left? '(NTH 1 j_) '(NTH 2 j_)))                          ; the {e}-component of j_
         (ifee '(IF (= (IDEN m_) (IDEN m_)) (ONE a_) (ZERO a_))))
    (sp (make-wff `(FORALL a_ (FORALL m_ (FORALL f_ (FORALL x_
       (IMPLIES (IS-RING a_) (IMPLIES (IS-MONOID m_) (IMPLIES (IN f_ ,mir-F)
       (IMPLIES (IN x_ (CARR m_))
         (= ,(mir-conv fa fb 'x_) (f_ x_))))))))))))
    (dk-peel!)
    (fact 'monoid-carrier-is-set 'm_) (fact 'ring-zero-in 'a_) (fact 'ring-one-in 'a_)
    (fact 'ring-additive-ag-is-abelian-group 'a_)
    (mir-singleton-facts!)
    (fact 'monalg-one-in 'a_ 'm_)
    (mir-fun! 'f_) (mir-fun! mir-one) (mir-supp-facts! 'f_) (mir-supp-facts! mir-one)
    (fact 'fun-apply-type-c 'f_ '(CARR m_) '(CARR a_) 'x_)
    (mir-IQ-facts! A B 'x_) (mir-IQ-facts! A2 B2 'x_)
    (mir-LQ-type! fa fb A B 'x_) (mir-LQ-type! fa fb A2 B2 'x_)
    
    (let ((e1 (mir-embed! fa fb A B A2 B2 'x_
                (lambda (t sd) (if (eq? sd side) (begin (fact 'monalg-one-supp-subset 'a_ 'm_ t) (ass)) (ass)))
                (if left? (mir-vanish-left! mir-one 'f_ A B 'x_) (mir-vanish-right! 'f_ mir-one A B 'x_)))))
      ;; every index j_ of U has its {e}-component equal to e and its f-component equal to x_
      (define (mir-index-is-i0!)          ; lands (= j_ i0); context: (IN j_ U)
        (sep-me (list 'IN 'j_ U))
        (fact 'cartesian-nth 'j_ A2 B2)
        (mir-split-head! (list 'IN '(NTH 1 j_) A2))
        (fact 'cartesian-pair-eq 'j_ A2 B2)
        (mir-in-singleton! ne)                                   ; (= ne e)
        (mir-in-carr-off-supp! nx Sf)
        (mir-monoid-id! side nx)                                 ; (= (OPR e nx) nx) resp. (OPR nx e)
        (let* ((h3 (if left? (list '= (list '(OPR m_) e nx) nx) (list '= (list '(OPR m_) nx e) nx)))
               (h3r (mir-sym! h3))                                ; (= nx (OPR .. ..))
               (h2r (mir-sym! (list '= ne e))))                   ; (= e ne)
          (have! (list '= nx 'x_) (lambda () (subst h3r) (subst h2r) (ass)))
          (fact 'pair-in-cartesian A2 B2 (if left? e 'x_) (if left? 'x_ e))
          (fact 'pair-tuple-is-set '(CARR m_) '(CARR m_) (if left? e 'x_) (if left? 'x_ e))   ; rfl's definedness witness
          (have! (list '= 'j_ i0)
            (lambda () (subst '(= j_ (LIST (NTH 1 j_) (NTH 2 j_))))
                       (subst (list '= ne e)) (subst (list '= nx 'x_)) (rfl)))))
      
      (use-em (list 'IN 'x_ Sf)
        (lambda ()                                               ; x_ in supp(f): one surviving index
          (fact 'pair-in-cartesian A2 B2 (if left? e 'x_) (if left? 'x_ e))
          (mir-monoid-id! side 'x_)
          (have! (list 'IN i0 U)
            (lambda () (for-each (lambda (n) (dk-focus! n) (if (eq? (car (dk-goal)) '=) (begin (nth-r) (ass)) (ass)))
                                 (dk-opened (lambda () (sep-mi))))))
          (have! (list 'FORALL 'j_ (list 'IMPLIES (list 'IN 'j_ U) (list 'IMPLIES (list 'NOT (list '= 'j_ i0))
                                                                            (list '= (list LU 'j_) (list 'IDEN mir-ag)))))
            (lambda ()
              (dk-peel!)
              (mir-index-is-i0!)
              (dk-only! (list '= 'j_ i0) (list 'NOT (list '= 'j_ i0)))
              (prop)))
          (fact 'finsum-single-support mir-ag U LU i0)
          (subst e1)
          (subst (list '= FU (list LU i0)))
          (lam-b) (nth-r)
          (mac 'monalg-one-apply)
          (mir-if! ifee 'true (lambda () (rfl)))
          (if left? (fact 'ring-mul-left-id 'a_ '(f_ x_)) (fact 'ring-mul-right-id 'a_ '(f_ x_)))
          (ass))
        (lambda ()                                               ; x_ outside supp(f): no index at all
          (let ((fx0 (mir-zero-off-supp! 'f_ 'x_)))
            (have! (list 'FORALL 'j_ (list 'IMPLIES (list 'IN 'j_ U) (list '= (list LU 'j_) (list 'IDEN mir-ag))))
              (lambda ()
                (di)
                (mir-index-is-i0!)
                (have! (list 'IN 'x_ Sf) (lambda () (subst (mir-sym! (list '= nx 'x_))) (ass)))
                (ai (list 'NOT (list 'IN 'x_ Sf)))))
            (fact 'finsum-all-id mir-ag U LU)
            (subst e1)
            (subst (list '= FU (list 'IDEN mir-ag)))
            (mac 'raag-iden)
            (subst fx0)
            (rfl)))))
    (qed name)))
(mir-one-law-at! 'left  'monalg-one-left-at)
(mir-one-law-at! 'right 'monalg-one-right-at)
;; ======================================================================
;; THE MULTIPLICATIVE LAWS AT THE FUNCTION LEVEL, and the umbrella's last conjuncts
;; ======================================================================
(mir-law! 'monalg-distrib-left '(f_ g_ h_)
  (mir-mul 'f_ (mir-add 'g_ 'h_)) (mir-add (mir-mul 'f_ 'g_) (mir-mul 'f_ 'h_))
  (lambda (x) (mir-mac-all! 'monalg-mul-apply 'MONALG-MUL)
              (fact 'monalg-distrib-left-at 'a_ 'm_ 'f_ 'g_ 'h_ x)))
(mir-law! 'monalg-distrib-right '(f_ g_ h_)
  (mir-mul (mir-add 'f_ 'g_) 'h_) (mir-add (mir-mul 'f_ 'h_) (mir-mul 'g_ 'h_))
  (lambda (x) (mir-mac-all! 'monalg-mul-apply 'MONALG-MUL)
              (fact 'monalg-distrib-right-at 'a_ 'm_ 'f_ 'g_ 'h_ x)))
(mir-law! 'monalg-one-left-fn '(f_)
  (mir-mul mir-one 'f_) 'f_
  (lambda (x) (mir-mac-all! 'monalg-mul-apply 'MONALG-MUL)
              (fact 'monalg-one-left-at 'a_ 'm_ 'f_ x)))
(mir-law! 'monalg-one-right-fn '(f_)
  (mir-mul 'f_ mir-one) 'f_
  (lambda (x) (mir-mac-all! 'monalg-mul-apply 'MONALG-MUL)
              (fact 'monalg-one-right-at 'a_ 'm_ 'f_ x)))

;; the pointwise unit law, in the support's own spelling (structure-library/polynomial.scm)
(sp (make-wff `(FORALL a_ (FORALL m_ (FORALL f_ (FORALL x_
   (IMPLIES (IS-RING a_) (IMPLIES (IS-MONOID m_) (IMPLIES (IN f_ ,mir-F) (IMPLIES (IN x_ (CARR m_))
     (= (,(mir-mul mir-one 'f_) x_) (f_ x_))))))))))))
(dk-peel!)
(fact 'monalg-one-left-at 'a_ 'm_ 'f_ 'x_)
(mac 'monalg-mul-apply)
(ass)
(qed 'monalg-one-left)
;; ---- the umbrella ----
(define (mir-binders g)           ; binder symbols of a FORALL/IMPLIES prefix, in order
  (cond ((and (pair? g) (eq? (car g) 'FORALL)) (cons (cadr g) (mir-binders (caddr g))))
        ((and (pair? g) (eq? (car g) 'IMPLIES)) (mir-binders (caddr g)))
        (#t '())))
(define (mir-peel-binders!)       ; peel, and return the eigenvariables, checked against the context
  (let ((vs (mir-binders (dk-goal))))
    (dk-peel!)
    (for-each (lambda (v) (if (not (dk-asm? (list 'IN v '(FINSUPP a m))))
                              (error "mir-peel-binders!: eigenvariable not typed in context" v)))
              vs)
    vs))
(define (mir-is? h oph)
  (lambda (g) (and (pair? g) (eq? (car g) h)
                   (let ((a1 (cadr g))) (and (pair? a1) (eq? (car a1) oph))))))
(define (mir-focus! pred)
  (let ((hit (any-pred (lambda (l) (pred (dk-goal-of l))) (proof-leaves))))
    (if (not hit) (error "mir-focus!: no open leaf matches"))
    (dk-focus! hit)))
(define (mir-disch! pred thunk) (mir-focus! pred) (thunk))
(define (mir-lam-t!)             ; lam-t; close the sethood leaf (a CARTESIAN of F's, or F), focus the typing leaf
  (let ((new (dk-opened (lambda () (lam-t)))))
    (for-each (lambda (l)
                (dk-focus! l)
                (let ((g (dk-goal-of l)))
                  (if (and (eq? (car g) 'IN) (eq? (caddr g) 'SET))
                      (if (and (pair? (cadr g)) (eq? (car (cadr g)) 'CARTESIAN))
                          (begin (mac 'cartesian-set-iff) (dk-conj-close!))
                          (ass)))))
              new)
    (let ((typ (filter (lambda (l) (not (sequent-node-grounded? l))) new)))
      (if (null? typ) (error "mir-lam-t!: no typing leaf left open"))
      (dk-focus! (car typ)))))
(define (mir-lam-arg g)          ; the argument of the lambda in a typing goal (IN (MONALG-X a m ...) F)
  (cadr g))

;;; ======================================================================
;;; BEGIN spliced block (2026-09-18, rake batch 5c-L): monalg-mul-assoc and the bricks
;;; under it.  Spliced, not a file of its own, because its load window is EMPTY: it
;;; cites monalg-mul-apply / monalg-ext / cartesian-pair-eq / raag-* proven ABOVE in this
;;; file and is cited by the monalg-is-ring proof BELOW.  The standalone original is
;;; archive/spliced-2026-09-18/rake-monalg-assoc.scm.  Helper prefix r7l-.
;;; ======================================================================
;;; theorem-library/rake-monalg-assoc.scm -- rake batch 5c, assignment 5c-L.
;;;
;;;   monalg-mul-assoc   structure-library/polynomial.scm:160-170   (the leaf; retire
;;;                      the `support', the `warrant!', the `gloss!' and the `topic!')
;;;
;;;     forall A, M, f, g, h.  IS-RING(A) => IS-MONOID(M)
;;;        => f, g, h in FINSUPP(A,M)
;;;        => (f*g)*h = f*(g*h)
;;;
;;; PROVEN, modulo {finsum-embed} -- the one leaf monalg-is-ring already bills.
;;; Also proven here, all modulo 0 and all general: `finsum-reindex-inverse' (the
;;; brick monalg-is-ring.scm's header asks for), `finsum-reindex-inverse-ptwise',
;;; `finsum-fiber-value', `finsum-fiber-slice' and `monalg-mul-supp-in-image'.
;;;
;;; *** LOAD WINDOW: THIS FILE IS A SPLICE, NOT A FILE. ***  monalg-mul-assoc is
;;; cited at theorem-library/monalg-is-ring.scm:1289, so hi = 319 (monalg-is-ring's
;;; own load position).  But the deepest citations -- monalg-mul-apply,
;;; monalg-mul-fun, monalg-ext, cartesian-pair-eq, card-cartesian-nn and the
;;; raag-carr / raag-iden view read-offs -- are proved INSIDE monalg-is-ring.scm,
;;; i.e. AT 319 as well, so lo = 319 and the window [319, 319) is EMPTY.  The block
;;; below must therefore be SPLICED INTO theorem-library/monalg-is-ring.scm
;;; immediately before the `monalg-is-ring' proof itself (that file's line 1222),
;;; exactly as the guarded Taylor facts are spliced into taylor-proof.scm
;;; (CLAUDE.md, "When a proof's window is INSIDE another proof file, splice it
;;; there").  Nothing else in the file has to move.
;;;
;;; The other citations, with their load positions, are all far below 319:
;;;   finsum-fiber, cartesian-nth                        finsum-fiber          314
;;;   monoid-carrier-is-set                              monalg-laws           317
;;;   finsum-reindex-ag                                  rake-algebra3         271
;;;   finsum-ring-distrib-left-gen / -right-gen          rake-finsum-laws2     250
;;;   finsum-congruence, finsum-congruence-q,
;;;   finsum-type-ptwise                                 rake-finsum-laws      249
;;;   card-image-finite                                  card-image-finite     247
;;;   card-subset-nn                                     card-subset-nn        246
;;;   monoid-carrier-closed-opr                          rake-algebra2         229
;;;   ring-mul-zero-left / -right                        ring-zero-one-power   211
;;;   finsum-type, finsum-all-id                         finsum-type-proof     201
;;;   ring-zero-in, ring-carrier-closed-mul              op-typing             200
;;;   pair-in-cartesian                                  pair-tuple-sethood    162
;;;   fun-apply-type-c                                   fun-apply-type-proof  160
;;;   supp-in-set, supp-membership, finsupp-membership   poly-membership       156
;;;   eq-sym                                             equality-basics       146
;;;   finsum-embed                                       finsum-additive       116
;;;   image-set, image-membership-iff                    injection              83
;;;   ring-additive-ag-is-abelian-group                  views                  60
;;;   ring-mul-assoc, is-monoid / is-associative, cartesian-set-iff, subset-def,
;;;   cartesian-decompose (through cartesian-pair-eq)    structure library / theory
;;;
;;; Two consequences of the splice, both for the integrator:
;;;   * `bijection-from-inverse' and `lambda-compose-value' live in
;;;     theorem-library/rake-monalg-comm.scm, which loads AFTER monalg-is-ring
;;;     (position 320).  They are re-proved here, VERBATIM, under their own
;;;     names; their two blocks in rake-monalg-comm.scm must then be DELETED, or
;;;     install-duplicate-audit counts two installs each.  rake-monalg-comm's own
;;;     `fact' citations of them keep working -- they are installed earlier now.
;;;   * the helpers below duplicate monalg-is-ring.scm's `mir-' kit under the
;;;     prefix `r7l-' (so that this block probes on its own).  Spliced in they are
;;;     redundant but harmless -- distinct names in one frame; a later cleanup can
;;;     drop r7l-split-head!, r7l-both!, r7l-fun!, r7l-supp-facts!, r7l-IQ-facts!,
;;;     r7l-LQ-type!, r7l-embed!, r7l-ptwise-type!, r7l-zero-off-supp! and the two
;;;     vanish closers in favour of the mir- originals.
;;;
;;; THE ARGUMENT.  Write Sf, Sg, Sh for the three supports and
;;;
;;;   P3 = (Sf x Sg) x Sh,   T3 = { w = [[p,q],r] in P3 : (p.q).r = x },
;;;   F3L = w |-> (f(p).g(q)).h(r),     F3R = w |-> f(p).(g(q).h(r)).
;;;
;;; Both sides of the law, evaluated at x, are the sum over T3, reached the same
;;; way twice:
;;;   (1) the outer index set I(supp(f*g), Sh, x) is EMBEDDED in
;;;       I(IMAGE(mult, Sf x Sg), Sh, x) -- monalg-mul-supp-in-image says the
;;;       support of a convolution lies in that image, and the summand vanishes
;;;       at the added indices (mir-embed!'s device);
;;;   (2) `finsum-fiber' along PHIL = w |-> [p.q, r] groups the sum over T3 by
;;;       the outer index;
;;;   (3) each fiber is carried onto the inner convolution's index set I(f,g,u)
;;;       by s |-> [s, r], whose inverse is w |-> NTH 1 w -- `finsum-fiber-slice',
;;;       which is `finsum-reindex-inverse-ptwise' with the SEP plumbing hidden;
;;;   (4) the inner convolution is unfolded by monalg-mul-apply and h(r) pulled
;;;       in by finsum-ring-distrib-right-gen.
;;; The mirror uses PHIR = w |-> [p, q.r], the slice map s |-> [[p, s1], s2] and
;;; finsum-ring-distrib-left-gen.  M's associativity enters ONCE, in the typing of
;;; PHIR (T3 is cut out by (p.q).r = x and PHIR must land in a set cut out by
;;; p.(q.r) = x); the ring's associativity enters ONCE, in the final pointwise
;;; congruence F3L = F3R.  No commutativity of either is used.
;;;
;;; DRIVER NOTES (each cost a probe):
;;;   * MIT folds case, so `LAMAL' and `LAMal' are ONE Scheme variable: a `let*'
;;;     binding both silently uses the second for both.  Spell them LAM-BIG /
;;;     LAM-PLAIN (CLAUDE.md, "never distinguish two names by case" -- the rule is
;;;     about WFF binders and it is just as true of the driver's own `let's).
;;;   * `dk-lam-t!' hands its pointwise leaf the SUBSTITUTED body, so there is no
;;;     redex left: a `lam-b' after it is an inert no-op.
;;;   * `sep-me' consumes the membership it opens, and the betas of a lambda whose
;;;     domain is that SEP are licensed by it -- so both halves are read off in
;;;     `have!' LANES (r7l-open-T3!, and the two lanes at the head of every fiber
;;;     hypothesis), never by a bare sep-me.
;;;   * closing `(= u u)' after a `subst' wants `rfl', not `ass'.
;;;   * to rewrite [NTH 1 w, NTH 2 t] into w, rewrite NTH 2 t BACKWARDS into
;;;     NTH 2 w (eq-sym then subst): substituting the cartesian-pair-eq for w the
;;;     other way rewrites w inside its own projections.
;;;
;;; Helper prefix: r7l-

(define (r7l-check! name)
  (if (not (proof-done? *ps*))
      (begin
        (display ";; r7l: OPEN LEAVES before qed ") (display name) (newline)
        (for-each (lambda (l)
                    (display ";;   GOAL: ")
                    (display (expression->string (dk-goal-of l))) (newline))
                  (proof-leaves))
        (error "r7l: proof not complete" name))))
(define (r7l-done! name) (r7l-check! name) (qed name) (topic! name 'algebra))

(define (r7l-any-subterm? pred t)
  (let loop ((x t))
    (cond ((not (pair? x)) #f)
          ((pred x) #t)
          (#t (let scan ((l x))
                (cond ((not (pair? l)) #f)
                      ((loop (car l)) #t)
                      (#t (scan (cdr l)))))))))
(define (r7l-redex? x) (and (pair? (car x)) (eq? (caar x) 'VNB-LAMBDA)))
(define (r7l-nth-redex? x)
  (and (eq? (car x) 'NTH) (= (length x) 3)
       (pair? (caddr x)) (eq? (car (caddr x)) 'LIST)))
(define (r7l-beta!)
  (let loop ((k 0))
    (if (and (< k 10) (r7l-any-subterm? r7l-redex? (dk-goal)))
        (begin (lam-b) (loop (+ k 1))))))
(define (r7l-nth-reduce!)
  (let loop ((k 0))
    (if (and (< k 10) (r7l-any-subterm? r7l-nth-redex? (dk-goal)))
        (begin (nth-r) (loop (+ k 1))))))
(define (r7l-tf v type body) (list 'FORALL v (list 'IMPLIES type body)))
(define (r7l-imps as body) (if (null? as) body (list 'IMPLIES (car as) (r7l-imps (cdr as) body))))
(define (r7l-foralls vs body) (if (null? vs) body (list 'FORALL (car vs) (r7l-foralls (cdr vs) body))))

;;; =====================================================================
;;; bijection-from-inverse -- a map with a two-sided inverse is a bijection.
;;; (Verbatim from theorem-library/rake-monalg-comm.scm, which loads LATER;
;;; retire the copy there.)
;;; =====================================================================
(define r7l-bfi-stmt
  '(FORALL X (FORALL Y (FORALL phi (FORALL psi
     (IMPLIES (IN phi (FUN X Y))
      (IMPLIES (IN psi (FUN Y X))
       (IMPLIES (FORALL u_ (IMPLIES (IN u_ X) (= (psi (phi u_)) u_)))
        (IMPLIES (FORALL v_ (IMPLIES (IN v_ Y) (= (phi (psi v_)) v_)))
         (IN phi (BIJECTION X Y)))))))))))
(define (r7l-eq-head? h)
  (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                   (let ((b (caddr (caddr f))))
                     (and (pair? b) (eq? (car b) '=)
                          (pair? (cadr b)) (eq? (car (cadr b)) h))))))
(sp (make-wff r7l-bfi-stmt))
(dk-peel!)
(let ((left  (dk-pick (r7l-eq-head? 'psi) "psi(phi u) = u"))
      (right (dk-pick (r7l-eq-head? 'phi) "phi(psi v) = v")))
  (mac 'bijection-membership-iff)
  (dk-conj-close!
   (lambda ()
     (let ((g (dk-goal)))
       (cond
        ((eq? (car g) 'IN) (ass))
        ((r7l-any-subterm? (lambda (x) (eq? (car x) 'FORSOME)) g)
         (let ((wv (dk-di-var!)))
           (fact 'fun-apply-type-c 'psi 'Y 'X wv)
           (dk-apply! right wv)
           (ew (list 'psi wv))
           (dk-conj-close!)))
        (#t
         (dk-peel!)
         (let* ((gg (dk-goal)) (av (cadr gg)) (bv (caddr gg)))
           (dk-apply! left av)
           (dk-apply! left bv)
           (fact 'eq-sym (list 'psi (list 'phi av)) av)
           (subst (list '= av (list 'psi (list 'phi av))))
           (subst (list '= (list 'phi av) (list 'phi bv)))
           (ass))))))))
(r7l-done! 'bijection-from-inverse)
(gloss! 'bijection-from-inverse
  "A map with a two-sided inverse is a bijection: phi : X -> Y and psi : Y -> X
   with psi(phi u) = u on X and phi(psi v) = v on Y put phi in BIJECTION(X,Y).")

;;; =====================================================================
;;; lambda-compose-value -- ((z in D |-> ff(ph z)) pt) == ff(ph pt).
;;; (Verbatim from rake-monalg-comm.scm; retire the copy there.)
;;; =====================================================================
(sp (make-wff
  '(FORALL ff (FORALL ph (FORALL dm (FORALL pt
     (IMPLIES (IN pt dm)
       (== ((VNB-LAMBDA z dm (ff (ph z))) pt) (ff (ph pt))))))))))
(dk-peel!)
(lam-b)
(qrfl)
(r7l-done! 'lambda-compose-value)
(gloss! 'lambda-compose-value
  "The value of a reindexing lambda: (z in D |-> ff(ph z)) at pt in D is
   ff(ph pt).  Stated with ff and ph variables so a beta step can never fire
   under the binder.")

;;; =====================================================================
;;; finsum-reindex-inverse -- the statement monalg-is-ring.scm's header asks
;;; for: reindexing along an explicit two-sided inverse rather than along a
;;; BIJECTION term.  Five lines: bijection-from-inverse + finsum-reindex-ag.
;;; =====================================================================
(define r7l-fri-stmt
  (r7l-tf 'ag '(IS-ABELIAN-GROUP ag)
    (list 'FORALL 'S
      (list 'IMPLIES '(IN S SET)
        (list 'IMPLIES '(IN (CARD S) NN)
          (r7l-tf 'T '(AND (IN T SET) (IN (CARD T) NN))
            (r7l-tf 'phi '(IN phi (FUN T S))
              (r7l-tf 'psi '(IN psi (FUN S T))
                (list 'IMPLIES '(FORALL u_ (IMPLIES (IN u_ T) (= (psi (phi u_)) u_)))
                  (list 'IMPLIES '(FORALL v_ (IMPLIES (IN v_ S) (= (phi (psi v_)) v_)))
                    (r7l-tf 'f '(IN f (FUN S (CARR ag)))
                      '(= (FINSUM ag f S)
                          (FINSUM ag (VNB-LAMBDA z T (f (phi z))) T)))))))))))))
(sp (make-wff r7l-fri-stmt))
(dk-peel!)
(fact 'bijection-from-inverse 'T 'S 'phi 'psi)
(fact 'finsum-reindex-ag 'ag 'S 'T 'phi 'f)
(ass)
(r7l-done! 'finsum-reindex-inverse)
(gloss! 'finsum-reindex-inverse
  "A finite sum is invariant under a change of index given by an explicit pair
   of mutually inverse maps -- the form a reindexing argument can supply
   directly, where finsum-reindex-ag demands a BIJECTION term.")

;;; =====================================================================
;;; finsum-reindex-inverse-ptwise -- the same with the summand typed
;;; POINTWISE on S instead of as a FUN on S.  This is the form a sum over a
;;; SUBSET needs: the summand of a fibered sum is a lambda whose domain is the
;;; WHOLE index set, so it is never in FUN(fiber, CARR ag).  The restriction
;;; (VNB-LAMBDA z_ S (ff z_)) is typed by lam-t and transported by the untyped
;;; finsum-congruence-q (CLAUDE.md, rake batch J).
;;; =====================================================================
(define r7l-frip-stmt
  (r7l-tf 'ag '(IS-ABELIAN-GROUP ag)
    (list 'FORALL 'S
      (list 'IMPLIES '(IN S SET)
        (list 'IMPLIES '(IN (CARD S) NN)
          (r7l-tf 'T '(AND (IN T SET) (IN (CARD T) NN))
            (r7l-tf 'phi '(IN phi (FUN T S))
              (r7l-tf 'psi '(IN psi (FUN S T))
                (list 'IMPLIES '(FORALL u_ (IMPLIES (IN u_ T) (= (psi (phi u_)) u_)))
                  (list 'IMPLIES '(FORALL v_ (IMPLIES (IN v_ S) (= (phi (psi v_)) v_)))
                    (list 'FORALL 'ff
                      (list 'IMPLIES '(FORALL z_ (IMPLIES (IN z_ S) (IN (ff z_) (CARR ag))))
                        '(= (FINSUM ag ff S)
                            (FINSUM ag (VNB-LAMBDA z T (ff (phi z))) T))))))))))))))
(sp (make-wff r7l-frip-stmt))
(dk-peel!)
;; T's finiteness arrives as ONE conjunction (finsum-reindex-ag's shape); the
;; conjuncts are wanted separately by finsum-congruence-q / finsum-type-ptwise,
;; and `ai' REPLACES the conjunction, so it is put back whole afterwards.
(dk-split! '(AND (IN T SET) (IN (CARD T) NN)))
(have! '(AND (IN T SET) (IN (CARD T) NN)))
(let* ((R    '(VNB-LAMBDA z_ S (ff z_)))
       (LAMR (list 'VNB-LAMBDA 'z 'T (list R '(phi z))))
       (LAMF '(VNB-LAMBDA z T (ff (phi z))))
       (typ  (dk-pick (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                                       (equal? (caddr a) '(IMPLIES (IN z_ S) (IN (ff z_) (CARR ag))))))
                      "forall z_ in S. ff z_ in CARR(ag)")))
  ;; the restriction is a FUN on S
  (have! (list 'IN R '(FUN S (CARR ag)))
    (lambda ()
      (dk-lam-t!)
      (let ((zv (dk-di-var!)))
        (dk-apply! typ zv)
        (ass))))
  ;; ff = R pointwise on S
  (have! '(FORALL z_ (IMPLIES (IN z_ S) (= (ff z_) ((VNB-LAMBDA z_ S (ff z_)) z_))))
    (lambda ()
      (let ((zv (dk-di-var!)))
        (dk-apply! typ zv)
        (lam-b)
        (rfl))))
  (fact 'finsum-congruence-q 'ag 'S 'ff R)
  (fact 'finsum-reindex-inverse 'ag 'S 'T 'phi 'psi R)
  ;; the two reindexed summands agree pointwise on T
  (have! (list 'FORALL 'w_ (list 'IMPLIES '(IN w_ T)
                                 (list '= (list LAMR 'w_) (list LAMF 'w_))))
    (lambda ()
      (let ((zv (dk-di-var!)))
        (fact 'fun-apply-type-c 'phi 'T 'S zv)
        (dk-apply! typ (list 'phi zv))
        (fact 'lambda-compose-value R 'phi 'T zv)
        (fact 'lambda-compose-value 'ff 'phi 'T zv)
        (subst (list '== (list LAMR zv) (list R (list 'phi zv))))
        (subst (list '== (list LAMF zv) (list 'ff (list 'phi zv))))
        (lam-b)
        (rfl))))
  (fact 'finsum-congruence-q 'ag 'T LAMR LAMF)
  ;; the surviving term must be certified DEFINED before `rfl' (the LUTINS rule)
  (have! (list 'FORALL 'w_ (list 'IMPLIES '(IN w_ T)
                                 (list 'IN (list LAMF 'w_) '(CARR ag))))
    (lambda ()
      (let ((zv (dk-di-var!)))
        (fact 'fun-apply-type-c 'phi 'T 'S zv)
        (dk-apply! typ (list 'phi zv))
        (fact 'lambda-compose-value 'ff 'phi 'T zv)
        (subst (list '== (list LAMF zv) (list 'ff (list 'phi zv))))
        (ass))))
  (fact 'finsum-type-ptwise 'ag 'T LAMF)
  (subst (list '== (list 'FINSUM 'ag 'ff 'S) (list 'FINSUM 'ag R 'S)))
  (subst (list '= (list 'FINSUM 'ag R 'S) (list 'FINSUM 'ag LAMR 'T)))
  (subst (list '== (list 'FINSUM 'ag LAMR 'T) (list 'FINSUM 'ag LAMF 'T)))
  (rfl))
(r7l-done! 'finsum-reindex-inverse-ptwise)
(gloss! 'finsum-reindex-inverse-ptwise
  "finsum-reindex-inverse with the summand typed pointwise on the index set --
   the form a sum over a SUBSET of a lambda's domain needs.")

;;; =====================================================================
;;; finsum-fiber-value -- the VALUE of the lambda `finsum-fiber' builds.
;;; Stated with ag, ff, ph, S, T, pt all VARIABLES, so the body holds no
;;; redex and `lam-b' has exactly one (the enum-fam-value device).
;;; =====================================================================
(sp (make-wff
  (r7l-foralls '(ag ff ph S T pt)
    (r7l-imps '((IN pt T))
      '(== ((VNB-LAMBDA t_ T (FINSUM ag ff (SEP s_ S (= (ph s_) t_)))) pt)
           (FINSUM ag ff (SEP s_ S (= (ph s_) pt))))))))
(dk-peel!)
(lam-b)
(qrfl)
(r7l-done! 'finsum-fiber-value)
(gloss! 'finsum-fiber-value
  "The value at pt of the outer summand finsum-fiber builds: the sum of ff over
   the fiber of ph above pt.")

;;; =====================================================================
;;; finsum-fiber-slice -- ONE fiber of a fibered sum, reindexed along an
;;; explicitly inverted map.  This is the interface the two halves of the
;;; convolution associativity want: the caller supplies al : K -> S landing in
;;; the fiber and be : fiber -> K, as four pointwise equations, and never has
;;; to type a map INTO a SEP set or restrict ff to it.
;;;
;;;   ff pointwise typed on S;  al : K -> S with ph(al k) = tp;
;;;   be carries the fiber into K;  be(al k) = k;  al(be w) = w on the fiber
;;;     =>  SUM over {s in S : ph s = tp} of ff  =  SUM over K of ff(al k)
;;; =====================================================================
(define r7l-ffs-FIB '(SEP s_ S (= (ph s_) tp)))
(define r7l-ffs-stmt
  (r7l-foralls '(ag)
   (r7l-imps '((IS-ABELIAN-GROUP ag))
    (r7l-foralls '(S)
     (r7l-imps '((IN S SET) (IN (CARD S) NN))
      (r7l-foralls '(K)
       (r7l-imps '((IN K SET) (IN (CARD K) NN))
        (r7l-foralls '(ph tp ff al be)
         (r7l-imps '((IN al (FUN K S))
                     (FORALL k_ (IMPLIES (IN k_ K) (= (ph (al k_)) tp)))
                     (FORALL w_ (IMPLIES (IN w_ S) (IMPLIES (= (ph w_) tp) (IN (be w_) K))))
                     (FORALL k_ (IMPLIES (IN k_ K) (= (be (al k_)) k_)))
                     (FORALL w_ (IMPLIES (IN w_ S) (IMPLIES (= (ph w_) tp) (= (al (be w_)) w_))))
                     (FORALL z_ (IMPLIES (IN z_ S) (IN (ff z_) (CARR ag)))))
          (list '= (list 'FINSUM 'ag 'ff r7l-ffs-FIB)
                   '(FINSUM ag (VNB-LAMBDA z K (ff (al z))) K)))))))))))

(sp (make-wff r7l-ffs-stmt))
(dk-peel!)
(let* ((FIB r7l-ffs-FIB)
       (AL  '(VNB-LAMBDA k_ K (al k_)))
       (BE  (list 'VNB-LAMBDA 'w_ FIB '(be w_)))
       (LAM-BIG (list 'VNB-LAMBDA 'z 'K (list 'ff (list AL 'z))))
       (LAM-PLAIN '(VNB-LAMBDA z K (ff (al z))))
       (hAL  (dk-pick (lambda (a) (equal? a '(FORALL k_ (IMPLIES (IN k_ K) (= (ph (al k_)) tp)))))
                      "ph(al k) = tp"))
       (hBEK (dk-pick (lambda (a) (equal? a '(FORALL w_ (IMPLIES (IN w_ S) (IMPLIES (= (ph w_) tp) (IN (be w_) K))))))
                      "be carries the fiber into K"))
       (hBA  (dk-pick (lambda (a) (equal? a '(FORALL k_ (IMPLIES (IN k_ K) (= (be (al k_)) k_)))))
                      "be(al k) = k"))
       (hAB  (dk-pick (lambda (a) (equal? a '(FORALL w_ (IMPLIES (IN w_ S) (IMPLIES (= (ph w_) tp) (= (al (be w_)) w_))))))
                      "al(be w) = w"))
       (hTY  (dk-pick (lambda (a) (equal? a '(FORALL z_ (IMPLIES (IN z_ S) (IN (ff z_) (CARR ag))))))
                      "ff typed on S")))
  ;; --- the fiber is a finite set, and ff is typed on it
  (have! (list 'IN FIB 'SET) (lambda () (sep-set) (ass)))
  (have! '(AND (IN S SET) (IN (CARD S) NN)))
  (have! (list 'AND (list 'IN FIB 'SET)
               (list 'FORALL 'zc_ (list 'IMPLIES (list 'IN 'zc_ FIB) '(IN zc_ S))))
    (lambda ()
      (dk-conj-close!
       (lambda ()
         (if (eq? (car (dk-goal)) 'IN) (ass)
             (let ((zv (dk-di-var!)))
               (dk-split-all! (dk-landed (lambda () (sep-me (list 'IN zv FIB)))))
               (ass)))))))
  (fact 'card-subset-nn 'S FIB)
  (have! (list 'FORALL 'zc_ (list 'IMPLIES (list 'IN 'zc_ FIB) (list 'IN '(ff zc_) '(CARR ag))))
    (lambda ()
      (let ((zv (dk-di-var!)))
        (dk-split-all! (dk-landed (lambda () (sep-me (list 'IN zv FIB)))))
        (dk-apply! hTY zv)
        (ass))))
  (have! '(AND (IN K SET) (IN (CARD K) NN)))
  ;; --- AL : K -> FIB
  (have! (list 'IN AL (list 'FUN 'K FIB))
    (lambda ()
      (dk-lam-t!)
      (let ((kv (dk-di-var!)))
        (fact 'fun-apply-type-c 'al 'K 'S kv)
        (dk-apply! hAL kv)
        (for-each (lambda (n) (dk-focus! n) (ass)) (dk-opened (lambda () (sep-mi)))))))
  ;; --- BE : FIB -> K
  (have! (list 'IN BE (list 'FUN FIB 'K))
    (lambda ()
      (dk-lam-t!)
      (let ((wv (dk-di-var!)))
        (dk-split-all! (dk-landed (lambda () (sep-me (list 'IN wv FIB)))))
        (dk-apply! hBEK wv)
        (ass))))
  ;; --- the two round trips
  (have! (list 'FORALL 'u_ (list 'IMPLIES '(IN u_ K) (list '= (list BE (list AL 'u_)) 'u_)))
    (lambda ()
      (let ((kv (dk-di-var!)))
        (fact 'fun-apply-type-c 'al 'K 'S kv)
        (dk-apply! hAL kv)
        (dk-apply! hBA kv)
        (have! (list 'IN (list 'al kv) FIB)
               (lambda () (for-each (lambda (n) (dk-focus! n) (ass)) (dk-opened (lambda () (sep-mi))))))
        (r7l-beta!)
        (ass))))
  (have! (list 'FORALL 'v_ (list 'IMPLIES (list 'IN 'v_ FIB) (list '= (list AL (list BE 'v_)) 'v_)))
    (lambda ()
      (let ((wv (dk-di-var!)))
        ;; `sep-me' CONSUMES the membership, and the betas below are licensed by
        ;; it -- so the two halves are read off in LANES.
        (have! (list 'IN wv 'S)
          (lambda () (dk-split-all! (dk-landed (lambda () (sep-me (list 'IN wv FIB))))) (ass)))
        (have! (list '= (list 'ph wv) 'tp)
          (lambda () (dk-split-all! (dk-landed (lambda () (sep-me (list 'IN wv FIB))))) (ass)))
        (dk-apply! hBEK wv)
        (dk-apply! hAB wv)
        (r7l-beta!)
        (ass))))
  ;; --- the reindex, and then AL z |-> al z under the binder
  (fact 'finsum-reindex-inverse-ptwise 'ag FIB 'K AL BE 'ff)
  (have! (list 'FORALL 'w_ (list 'IMPLIES '(IN w_ K) (list '= (list LAM-BIG 'w_) (list LAM-PLAIN 'w_))))
    (lambda ()
      (let ((kv (dk-di-var!)))
        (fact 'fun-apply-type-c 'al 'K 'S kv)
        (dk-apply! hTY (list 'al kv))
        (fact 'lambda-compose-value 'ff AL 'K kv)
        (fact 'lambda-compose-value 'ff 'al 'K kv)
        (subst (list '== (list LAM-BIG kv) (list 'ff (list AL kv))))
        (subst (list '== (list LAM-PLAIN kv) (list 'ff (list 'al kv))))
        (lam-b)
        (rfl))))
  (fact 'finsum-congruence-q 'ag 'K LAM-BIG LAM-PLAIN)
  (have! (list 'FORALL 'w_ (list 'IMPLIES '(IN w_ K) (list 'IN (list LAM-PLAIN 'w_) '(CARR ag))))
    (lambda ()
      (let ((kv (dk-di-var!)))
        (fact 'fun-apply-type-c 'al 'K 'S kv)
        (dk-apply! hTY (list 'al kv))
        (fact 'lambda-compose-value 'ff 'al 'K kv)
        (subst (list '== (list LAM-PLAIN kv) (list 'ff (list 'al kv))))
        (ass))))
  (fact 'finsum-type-ptwise 'ag 'K LAM-PLAIN)
  (subst (list '= (list 'FINSUM 'ag 'ff FIB) (list 'FINSUM 'ag LAM-BIG 'K)))
  (subst (list '== (list 'FINSUM 'ag LAM-BIG 'K) (list 'FINSUM 'ag LAM-PLAIN 'K)))
  (rfl))
(r7l-done! 'finsum-fiber-slice)
(gloss! 'finsum-fiber-slice
  "One fiber of a fibered finite sum, reindexed along an explicitly inverted
   map: the caller supplies al : K -> S landing in the fiber and be on the
   fiber, as pointwise equations, and never types a map into a SEP set.")

;;; =====================================================================
;;; THE MONALG HALF.  From here the plumbing duplicates monalg-is-ring.scm's
;;; `mir-' kit (the file this block is to be spliced into); the names carry the
;;; r7l- prefix so the two can coexist.
;;; =====================================================================
(define r7l-F '(FINSUPP a_ m_))
(define r7l-ag '(RING-ADDITIVE-AG a_))
(define (r7l-supp f) (list 'SUPP 'a_ 'm_ f))
(define (r7l-mul f g) (list 'MONALG-MUL 'a_ 'm_ f g))
(define (r7l-IQ A B x)
  (list 'SEP 'p (list 'CARTESIAN A B) (list '= '((OPR m_) (NTH 1 p) (NTH 2 p)) x)))
(define (r7l-LQ f g A B x)
  (list 'VNB-LAMBDA 'p (r7l-IQ A B x)
        (list '(MUL a_) (list f '(NTH 1 p)) (list g '(NTH 2 p)))))
(define (r7l-mulmap A B)
  (list 'VNB-LAMBDA 'q (list 'CARTESIAN A B) '((OPR m_) (NTH 1 q) (NTH 2 q))))

(define (r7l-split-head! first)
  (dk-split! (dk-pick (lambda (h) (and ((dk-head? 'AND) h) (equal? (cadr h) first))) "conjunction")))
(define (r7l-both! g1 b1 b2)
  (let ((ls (dk-opened (lambda () (di)))))
    (dk-focus! (any-pred (lambda (n) (equal? (dk-goal-of n) g1)) ls)) (b1)
    (dk-focus! (any-pred (lambda (n) (not (equal? (dk-goal-of n) g1))) ls)) (b2)))
(define (r7l-fun! v)
  (have! (list 'IN v '(FUN (CARR m_) (CARR a_)))
    (lambda () (mac-h 'finsupp-membership (list 'IN v r7l-F))
               (r7l-split-head! (list 'IN v '(FUN (CARR m_) (CARR a_))))
               (ass))))
(define (r7l-supp-facts! f)
  (have! (list 'IN (r7l-supp f) 'SET) (lambda () (fact 'supp-in-set 'a_ 'm_ f) (ass)))
  (have! (list 'IN (list 'CARD (r7l-supp f)) 'NN)
    (lambda () (mac-h 'finsupp-membership (list 'IN f r7l-F))
               (r7l-split-head! (list 'IN f '(FUN (CARR m_) (CARR a_))))
               (ass))))
;; (IN t (CARR m_)) as a GOAL, from (IN t S) in context, S a SUPP or an IMAGE of
;; the multiplication map of two supports.
(define (r7l-carr-goal! q S)
  (cond ((eq? (car S) 'SUPP)
         (mac-h 'supp-membership (list 'IN q S))
         (r7l-split-head! (list 'IN q '(CARR m_))) (ass))
        ((eq? (car S) 'IMAGE)
         ;; image-membership-iff: (IN w (IMAGE phi S)) iff forsome x. x in S and phi(x) = w
         (let* ((dom (caddr S))
                (wit (dk-landed-1 (lambda () (mac-h 'image-membership-iff (list 'IN q S))))))
           (dk-split-all! (dk-landed (lambda () (ai wit))))
           (let* ((eq (dk-pick (lambda (h) (and (pair? h) (eq? (car h) '=) (equal? (caddr h) q)))
                               "mulmap(w) = q"))
                  (wv (cadr (cadr eq))))
             (fact 'cartesian-nth wv (cadr dom) (caddr dom))
             (r7l-split-head! (list 'IN (list 'NTH 1 wv) (cadr dom)))
             (r7l-in-carr-off-supp! (list 'NTH 1 wv) (cadr dom))
             (r7l-in-carr-off-supp! (list 'NTH 2 wv) (caddr dom))
             (r7l-opr-in-carr! (list 'NTH 1 wv) (list 'NTH 2 wv))
             (fact 'eq-sym (cadr eq) q)
             (subst (list '= q (cadr eq)))
             (lam-b)
             (ass))))
        (#t (error "r7l-carr-goal!: unsupported set" S))))
(define (r7l-in-carr-off-supp! q S)
  (dk-have! (list 'IN q '(CARR m_)) (lambda () (r7l-carr-goal! q S))))
;; the monoid's closure and associativity, off the IS-MONOID unfold (monoid.scm's
;; monoid-assoc / monoid-carrier-closed-opr are unwarranted axioms; the unfold is free,
;; and monoid-carrier-closed-opr is PROVEN in rake-algebra2, so it is cited)
(define (r7l-opr-in-carr! s t)
  (dk-have! (list 'AND '(IS-MONOID m_) (list 'AND (list 'IN s '(CARR m_)) (list 'IN t '(CARR m_)))))
  (fact 'monoid-carrier-closed-opr 'm_ s t))
(define (r7l-monoid-assoc! u v w)
  (let ((eq (list '= (list '(OPR m_) (list '(OPR m_) u v) w)
                  (list '(OPR m_) u (list '(OPR m_) v w)))))
    (dk-have! eq
      (lambda ()
        (mac-h 'is-monoid '(IS-MONOID m_))
        (dk-split! (any-pred (dk-head? 'AND) (dk-asms)))
        (let* ((asf (dk-pick (lambda (h) (and (pair? h) (eq? (car h) 'is-associative)))
                             "is-associative conjunct"))
               (un  (dk-landed-1 (lambda () (mac-h 'is-associative asf)))))
          (dk-apply! un u v w)
          (ass))))
    eq))

;; A, B finite sets whose members lie in CARR(m_): the index set I(A,B,x) is a
;; finite set, and the convolution summand is a function on it.
(define (r7l-IQ-facts! A B x)
  (let ((I (r7l-IQ A B x)) (Q (list 'CARTESIAN A B)))
    (dk-have! (list 'IN Q 'SET) (lambda () (mac 'cartesian-set-iff) (dk-conj-close!)))
    (fact 'card-cartesian-nn A B)
    (dk-have! (list 'IN I 'SET) (lambda () (sep-set) (ass)))
    (dk-have! (list 'AND (list 'IN Q 'SET) (list 'IN (list 'CARD Q) 'NN)))
    (if (memq 'zc_ (free-vars I)) (error "r7l-IQ-facts!: zc_ is free in the index set"))
    (dk-have! (list 'AND (list 'IN I 'SET)
                 (list 'FORALL 'zc_ (list 'IMPLIES (list 'IN 'zc_ I) (list 'IN 'zc_ Q))))
      (lambda () (r7l-both! (list 'IN I 'SET) (lambda () (ass))
                   (lambda () (di) (sep-me (list 'IN 'zc_ I)) (ass)))))
    (fact 'card-subset-nn Q I)))
(define (r7l-LQ-type! f g A B x)
  (let ((I (r7l-IQ A B x)) (L (r7l-LQ f g A B x)))
    (dk-have! (list 'IN L (list 'FUN I '(CARR a_)))
      (lambda ()
        (dk-lam-t!)
        (let ((pv (dk-di-var!)))
          (sep-me (list 'IN pv I))
          (fact 'cartesian-nth pv A B)
          (r7l-split-head! (list 'IN (list 'NTH 1 pv) A))
          (r7l-in-carr-off-supp! (list 'NTH 1 pv) A)
          (r7l-in-carr-off-supp! (list 'NTH 2 pv) B)
          (fact 'fun-apply-type-c f '(CARR m_) '(CARR a_) (list 'NTH 1 pv))
          (fact 'fun-apply-type-c g '(CARR m_) '(CARR a_) (list 'NTH 2 pv))
          (fact 'ring-carrier-closed-mul 'a_ (list f (list 'NTH 1 pv)) (list g (list 'NTH 2 pv)))
          (ass))))
    (dk-have! (list 'IN L (list 'FUN I (list 'CARR r7l-ag)))
              (lambda () (mac 'raag-carr) (ass)))))

;;; =====================================================================
;;; monalg-mul-supp-in-image -- supp(f*g) is contained in the image of
;;; supp f x supp g under the multiplication of M.  The inclusion that is
;;; buried inside monalg-mul-fun's proof, surfaced as a lemma: it is what
;;; lets the outer index set of ((f*g)*h)(x) be replaced by one built from
;;; supp f, supp g and supp h alone.
;;; =====================================================================
(define r7l-Sf (r7l-supp 'f_))
(define r7l-Sg (r7l-supp 'g_))
(define r7l-Sh (r7l-supp 'h_))
(define r7l-Pfg (list 'CARTESIAN r7l-Sf r7l-Sg))
(define r7l-mulfg (r7l-mulmap r7l-Sf r7l-Sg))
(define r7l-Ifg (list 'IMAGE r7l-mulfg r7l-Pfg))
(define r7l-FG (r7l-mul 'f_ 'g_))

(sp (make-wff
  (r7l-foralls '(a_ m_ f_ g_ z_)
    (r7l-imps (list '(IS-RING a_) '(IS-MONOID m_)
                    (list 'IN 'f_ r7l-F) (list 'IN 'g_ r7l-F)
                    (list 'IN 'z_ (r7l-supp r7l-FG)))
              (list 'IN 'z_ r7l-Ifg)))))
(dk-peel!)
(fact 'monoid-carrier-is-set 'm_) (fact 'ring-zero-in 'a_)
(fact 'ring-additive-ag-is-abelian-group 'a_)
(r7l-fun! 'f_) (r7l-fun! 'g_)
(r7l-supp-facts! 'f_) (r7l-supp-facts! 'g_)
(mac-h 'supp-membership (list 'IN 'z_ (r7l-supp r7l-FG)))
(r7l-split-head! '(IN z_ (CARR m_)))
(mac-h 'monalg-mul-apply (list 'NOT (list '= (list r7l-FG 'z_) '(ZERO a_))))
(r7l-IQ-facts! r7l-Sf r7l-Sg 'z_)
(r7l-LQ-type! 'f_ 'g_ r7l-Sf r7l-Sg 'z_)
(let ((I (r7l-IQ r7l-Sf r7l-Sg 'z_))
      (L (r7l-LQ 'f_ 'g_ r7l-Sf r7l-Sg 'z_))
      (conv (list 'FINSUM r7l-ag (r7l-LQ 'f_ 'g_ r7l-Sf r7l-Sg 'z_) (r7l-IQ r7l-Sf r7l-Sg 'z_))))
  (use-em (list 'IN 'z_ r7l-Ifg)
    (lambda () (ass))
    (lambda ()
      (have! (list 'FORALL 'w_ (list 'IMPLIES (list 'IN 'w_ I)
                                     (list '= (list L 'w_) (list 'IDEN r7l-ag))))
        (lambda ()
          (di)
          (sep-me (list 'IN 'w_ I))
          (have! (list 'IN 'z_ r7l-Ifg)
            (lambda () (mac 'image-membership-iff) (ew 'w_)
              (dk-conj-close! (lambda () (if (eq? (car (dk-goal)) '=) (begin (lam-b) (ass)) (ass))))))
          (ai (list 'NOT (list 'IN 'z_ r7l-Ifg)))))
      (fact 'finsum-all-id r7l-ag I L)
      (have! (list '= conv '(ZERO a_))
        (lambda () (subst (list '= conv (list 'IDEN r7l-ag))) (mac 'raag-iden) (rfl)))
      (ai (list 'NOT (list '= conv '(ZERO a_)))))))
(r7l-done! 'monalg-mul-supp-in-image)
(gloss! 'monalg-mul-supp-in-image
  "The support of a convolution f*g lies in the image of supp f x supp g under
   the multiplication of M: outside that image the index set of (f*g)(x) is
   empty, so the sum is ZERO(A).")

;;; =====================================================================
;;; THE TRIPLE INDEX SET.
;;;
;;;   P3 = (supp f x supp g) x supp h
;;;   T3 = { w in P3 : (p.q).r = x }        (w = [[p,q],r])
;;;   F3L = w |-> (f(p).g(q)).h(r)
;;;   PHIL = w |-> [p.q, r]                 into IL = I(IMAGE(mult), supp h, x)
;;; =====================================================================
(define r7l-P3 (list 'CARTESIAN r7l-Pfg r7l-Sh))
(define r7l-T3 (list 'SEP 'w r7l-P3
   '(= ((OPR m_) ((OPR m_) (NTH 1 (NTH 1 w)) (NTH 2 (NTH 1 w))) (NTH 2 w)) x_)))
(define r7l-F3L (list 'VNB-LAMBDA 'w r7l-T3
   '((MUL a_) ((MUL a_) (f_ (NTH 1 (NTH 1 w))) (g_ (NTH 2 (NTH 1 w)))) (h_ (NTH 2 w)))))
(define r7l-PHIL (list 'VNB-LAMBDA 'w r7l-T3
   '(LIST ((OPR m_) (NTH 1 (NTH 1 w)) (NTH 2 (NTH 1 w))) (NTH 2 w))))
(define r7l-IL (r7l-IQ r7l-Ifg r7l-Sh 'x_))
(define r7l-LQL (r7l-LQ r7l-FG 'h_ r7l-Ifg r7l-Sh 'x_))
(define (r7l-FIB t) (list 'SEP 's_ r7l-T3 (list '= (list r7l-PHIL 's_) t)))
(define r7l-TGT (list 'VNB-LAMBDA 't_ r7l-IL
                      (list 'FINSUM r7l-ag r7l-F3L (r7l-FIB 't_))))

;; the support facts of f, g, h plus the two derived finite sets
(define (r7l-base-prep!)
  (fact 'monoid-carrier-is-set 'm_) (fact 'ring-zero-in 'a_)
  (fact 'ring-additive-ag-is-abelian-group 'a_)
  (fact 'monalg-mul-fun 'a_ 'm_ 'f_ 'g_)
  (r7l-fun! 'f_) (r7l-fun! 'g_) (r7l-fun! 'h_) (r7l-fun! r7l-FG)
  (r7l-supp-facts! 'f_) (r7l-supp-facts! 'g_) (r7l-supp-facts! 'h_)
  (dk-have! (list 'IN r7l-Pfg 'SET) (lambda () (mac 'cartesian-set-iff) (dk-conj-close!)))
  (fact 'card-cartesian-nn r7l-Sf r7l-Sg)
  (dk-have! (list 'AND (list 'IN r7l-Pfg 'SET) (list 'IN (list 'CARD r7l-Pfg) 'NN)))
  (fact 'image-set r7l-mulfg r7l-Pfg)
  (fact 'card-image-finite r7l-mulfg r7l-Pfg)
  (dk-have! (list 'AND (list 'IN r7l-Ifg 'SET) (list 'IN (list 'CARD r7l-Ifg) 'NN))))

;; T3 is a finite set
(define (r7l-T3-facts!)
  (dk-have! (list 'IN r7l-P3 'SET) (lambda () (mac 'cartesian-set-iff) (dk-conj-close!)))
  (fact 'card-cartesian-nn r7l-Pfg r7l-Sh)
  (dk-have! (list 'IN r7l-T3 'SET) (lambda () (sep-set) (ass)))
  (dk-have! (list 'AND (list 'IN r7l-P3 'SET) (list 'IN (list 'CARD r7l-P3) 'NN)))
  (dk-have! (list 'AND (list 'IN r7l-T3 'SET)
                  (list 'FORALL 'zc_ (list 'IMPLIES (list 'IN 'zc_ r7l-T3) (list 'IN 'zc_ r7l-P3))))
    (lambda () (r7l-both! (list 'IN r7l-T3 'SET) (lambda () (ass))
                 (lambda () (di) (sep-me (list 'IN 'zc_ r7l-T3)) (ass)))))
  (fact 'card-subset-nn r7l-P3 r7l-T3))

;; the three coordinates of a member of T3, typed in CARR(m_), in LANES
(define (r7l-open-T3! wv)
  (dk-have! (list 'IN wv r7l-P3)
    (lambda () (dk-split-all! (dk-landed (lambda () (sep-me (list 'IN wv r7l-T3))))) (ass)))
  (dk-have! (list '= (list '(OPR m_)
                           (list '(OPR m_) (list 'NTH 1 (list 'NTH 1 wv)) (list 'NTH 2 (list 'NTH 1 wv)))
                           (list 'NTH 2 wv)) 'x_)
    (lambda () (dk-split-all! (dk-landed (lambda () (sep-me (list 'IN wv r7l-T3))))) (ass)))
  (fact 'cartesian-nth wv r7l-Pfg r7l-Sh)
  (r7l-split-head! (list 'IN (list 'NTH 1 wv) r7l-Pfg))
  (fact 'cartesian-nth (list 'NTH 1 wv) r7l-Sf r7l-Sg)
  (r7l-split-head! (list 'IN (list 'NTH 1 (list 'NTH 1 wv)) r7l-Sf))
  (r7l-in-carr-off-supp! (list 'NTH 1 (list 'NTH 1 wv)) r7l-Sf)
  (r7l-in-carr-off-supp! (list 'NTH 2 (list 'NTH 1 wv)) r7l-Sg)
  (r7l-in-carr-off-supp! (list 'NTH 2 wv) r7l-Sh))

;; F3L : T3 -> CARR(a_), and the pointwise form finsum-fiber-slice wants
(define (r7l-F3L-type!)
  (dk-have! (list 'IN r7l-F3L (list 'FUN r7l-T3 '(CARR a_)))
    (lambda ()
      (dk-lam-t!)
      (let* ((wv (dk-di-var!))
             (pp (list 'NTH 1 (list 'NTH 1 wv)))
             (qq (list 'NTH 2 (list 'NTH 1 wv)))
             (rr (list 'NTH 2 wv)))
        (r7l-open-T3! wv)
        (fact 'fun-apply-type-c 'f_ '(CARR m_) '(CARR a_) pp)
        (fact 'fun-apply-type-c 'g_ '(CARR m_) '(CARR a_) qq)
        (fact 'fun-apply-type-c 'h_ '(CARR m_) '(CARR a_) rr)
        (fact 'ring-carrier-closed-mul 'a_ (list 'f_ pp) (list 'g_ qq))
        (fact 'ring-carrier-closed-mul 'a_ (list '(MUL a_) (list 'f_ pp) (list 'g_ qq)) (list 'h_ rr))
        (ass))))
  (dk-have! (list 'IN r7l-F3L (list 'FUN r7l-T3 (list 'CARR r7l-ag)))
            (lambda () (mac 'raag-carr) (ass)))
  (dk-have! (list 'FORALL 'z_ (list 'IMPLIES (list 'IN 'z_ r7l-T3)
                                    (list 'IN (list r7l-F3L 'z_) (list 'CARR r7l-ag))))
    (lambda ()
      (let ((zv (dk-di-var!)))
        (fact 'fun-apply-type-c r7l-F3L r7l-T3 (list 'CARR r7l-ag) zv)
        (ass)))))

;; PHIL : T3 -> IL
(define (r7l-PHIL-type!)
  (dk-have! (list 'IN r7l-PHIL (list 'FUN r7l-T3 r7l-IL))
    (lambda ()
      (dk-lam-t!)
      (let* ((wv (dk-di-var!))
             (pp (list 'NTH 1 (list 'NTH 1 wv)))
             (qq (list 'NTH 2 (list 'NTH 1 wv)))
             (rr (list 'NTH 2 wv))
             (pq (list '(OPR m_) pp qq)))
        (r7l-open-T3! wv)
        (r7l-opr-in-carr! pp qq)
        (dk-have! (list 'IN pq r7l-Ifg)
          (lambda ()
            (mac 'image-membership-iff)
            (ew (list 'NTH 1 wv))
            (dk-conj-close! (lambda () (if (eq? (car (dk-goal)) '=) (begin (lam-b) (rfl)) (ass))))))
        (for-each
         (lambda (n)
           (dk-focus! n)
           (if (eq? (car (dk-goal)) 'IN)
               (begin (fact 'pair-in-cartesian r7l-Ifg r7l-Sh pq rr) (ass))
               (begin (r7l-nth-reduce!) (ass))))
         (dk-opened (lambda () (sep-mi))))))))

;;; =====================================================================
;;; monalg-mul-assoc-left-core
;;;
;;;   SUM over I(IMAGE(mult), supp h, x) of (f*g)(u).h(r)
;;;     = SUM over T3 of (f(p).g(q)).h(r)
;;;
;;; finsum-fiber along PHIL groups the triple sum by [p.q, r]; the fiber above
;;; [u,r] is carried onto the inner index set I(f,g,u) by s |-> [s,r], whose
;;; inverse is w |-> NTH 1 w (finsum-fiber-slice); and the inner convolution is
;;; pulled apart by monalg-mul-apply + finsum-ring-distrib-right-gen.
;;; =====================================================================
(sp (make-wff
  (r7l-foralls '(a_ m_ f_ g_ h_ x_)
    (r7l-imps (list '(IS-RING a_) '(IS-MONOID m_)
                    (list 'IN 'f_ r7l-F) (list 'IN 'g_ r7l-F) (list 'IN 'h_ r7l-F)
                    '(IN x_ (CARR m_)))
      (list '= (list 'FINSUM r7l-ag r7l-LQL r7l-IL)
               (list 'FINSUM r7l-ag r7l-F3L r7l-T3))))))
(dk-peel!)
(r7l-base-prep!)
(r7l-IQ-facts! r7l-Ifg r7l-Sh 'x_)
(r7l-LQ-type! r7l-FG 'h_ r7l-Ifg r7l-Sh 'x_)
(r7l-T3-facts!)
(r7l-F3L-type!)
(r7l-PHIL-type!)
(fact 'finsum-fiber r7l-ag r7l-T3 r7l-IL r7l-PHIL r7l-F3L)
(subst (list '= (list 'FINSUM r7l-ag r7l-F3L r7l-T3) (list 'FINSUM r7l-ag r7l-TGT r7l-IL)))
;; ---- the per-index identity ----------------------------------------
(have! (list 'FORALL 't_ (list 'IMPLIES (list 'IN 't_ r7l-IL)
                               (list '= (list r7l-TGT 't_) (list r7l-LQL 't_))))
 (lambda ()
  (let* ((tv   (dk-di-var!))
         (u    (list 'NTH 1 tv))
         (rr   (list 'NTH 2 tv))
         (Ifgu (r7l-IQ r7l-Sf r7l-Sg u))
         (Lfgu (r7l-LQ 'f_ 'g_ r7l-Sf r7l-Sg u))
         (AL   (list 'VNB-LAMBDA 'sa Ifgu (list 'LIST 'sa rr)))
         (BE   (list 'VNB-LAMBDA 'wb r7l-T3 '(NTH 1 wb)))
         (DD   (list 'VNB-LAMBDA 'z Ifgu (list '(MUL a_) (list Lfgu 'z) (list 'h_ rr))))
         (SL   (list 'VNB-LAMBDA 'z Ifgu (list r7l-F3L (list AL 'z)))))
    ;; open t in lanes (sep-me consumes the membership)
    (dk-have! (list 'IN tv (list 'CARTESIAN r7l-Ifg r7l-Sh))
      (lambda () (dk-split-all! (dk-landed (lambda () (sep-me (list 'IN tv r7l-IL))))) (ass)))
    (dk-have! (list '= (list '(OPR m_) u rr) 'x_)
      (lambda () (dk-split-all! (dk-landed (lambda () (sep-me (list 'IN tv r7l-IL))))) (ass)))
    (fact 'cartesian-nth tv r7l-Ifg r7l-Sh)
    (r7l-split-head! (list 'IN u r7l-Ifg))
    (r7l-in-carr-off-supp! u r7l-Ifg)
    (r7l-in-carr-off-supp! rr r7l-Sh)
    (fact 'cartesian-pair-eq tv r7l-Ifg r7l-Sh)          ; tv = [u, rr]
    (fact 'fun-apply-type-c 'h_ '(CARR m_) '(CARR a_) rr)
    (fact 'fun-apply-type-c r7l-FG '(CARR m_) '(CARR a_) u)
    (r7l-IQ-facts! r7l-Sf r7l-Sg u)
    (r7l-LQ-type! 'f_ 'g_ r7l-Sf r7l-Sg u)
    ;; the value of the outer summand at t
    (dk-have! (list '= (list r7l-LQL tv) (list '(MUL a_) (list r7l-FG u) (list 'h_ rr)))
      (lambda ()
        (lam-b)
        (fact 'ring-carrier-closed-mul 'a_ (list r7l-FG u) (list 'h_ rr))
        (rfl)))
    (fact 'finsum-fiber-value r7l-ag r7l-F3L r7l-PHIL r7l-T3 r7l-IL tv)
    (subst (list '== (list r7l-TGT tv) (list 'FINSUM r7l-ag r7l-F3L (r7l-FIB tv))))
    (subst (list '= (list r7l-LQL tv) (list '(MUL a_) (list r7l-FG u) (list 'h_ rr))))
    ;; unfold the inner convolution and pull h(r) in
    (fact 'monalg-mul-apply 'a_ 'm_ 'f_ 'g_ u)
    (subst (list '== (list r7l-FG u) (list 'FINSUM r7l-ag Lfgu Ifgu)))
    (fact 'finsum-ring-distrib-right-gen 'a_ (list 'h_ rr) Ifgu Lfgu)
    (subst (list '= (list '(MUL a_) (list 'FINSUM r7l-ag Lfgu Ifgu) (list 'h_ rr))
                    (list 'FINSUM r7l-ag DD Ifgu)))
    ;; ---- the slice: the fiber above t is I(f,g,u) ----
    ;; (IN [s, rr] T3) for s in I(f,g,u), wanted by every hypothesis below
    (dk-have! (list 'FORALL 'sc_ (list 'IMPLIES (list 'IN 'sc_ Ifgu)
                                       (list 'IN (list 'LIST 'sc_ rr) r7l-T3)))
      (lambda ()
        (let ((sv (dk-di-var!)))
          (dk-have! (list 'IN sv r7l-Pfg)
            (lambda () (dk-split-all! (dk-landed (lambda () (sep-me (list 'IN sv Ifgu))))) (ass)))
          (dk-have! (list '= (list '(OPR m_) (list 'NTH 1 sv) (list 'NTH 2 sv)) u)
            (lambda () (dk-split-all! (dk-landed (lambda () (sep-me (list 'IN sv Ifgu))))) (ass)))
          (for-each
           (lambda (n)
             (dk-focus! n)
             (if (eq? (car (dk-goal)) 'IN)
                 (begin (fact 'pair-in-cartesian r7l-Pfg r7l-Sh sv rr) (ass))
                 (begin (r7l-nth-reduce!)
                        (subst (list '= (list '(OPR m_) (list 'NTH 1 sv) (list 'NTH 2 sv)) u))
                        (ass))))
           (dk-opened (lambda () (sep-mi)))))))
    (let ((inT3 (dk-pick (lambda (h) (and (pair? h) (eq? (car h) 'FORALL)
                                          (equal? (cadr h) 'sc_)))
                         "[s, r] in T3")))
      ;; H1: AL : I(f,g,u) -> T3
      (dk-have! (list 'IN AL (list 'FUN Ifgu r7l-T3))
        (lambda ()
          (dk-lam-t!)
          (let ((sv (dk-di-var!)))
            (dk-apply! inT3 sv)
            (ass))))
      ;; H2: PHIL(AL s) = t
      (dk-have! (list 'FORALL 'k_ (list 'IMPLIES (list 'IN 'k_ Ifgu)
                                        (list '= (list r7l-PHIL (list AL 'k_)) tv)))
        (lambda ()
          (let ((sv (dk-di-var!)))
            (dk-apply! inT3 sv)
            (dk-have! (list '= (list '(OPR m_) (list 'NTH 1 sv) (list 'NTH 2 sv)) u)
              (lambda () (dk-split-all! (dk-landed (lambda () (sep-me (list 'IN sv Ifgu))))) (ass)))
            (r7l-beta!)
            (r7l-nth-reduce!)
            (subst (list '= (list '(OPR m_) (list 'NTH 1 sv) (list 'NTH 2 sv)) u))
            (fact 'eq-sym tv (list 'LIST u rr))
            (ass))))
      ;; H3: BE carries the fiber into I(f,g,u)
      (dk-have! (list 'FORALL 'w_ (list 'IMPLIES (list 'IN 'w_ r7l-T3)
                       (list 'IMPLIES (list '= (list r7l-PHIL 'w_) tv)
                             (list 'IN (list BE 'w_) Ifgu))))
        (lambda ()
          (let* ((wv (dk-di-var!)))
            (dk-landed (lambda () (di)))
            (r7l-open-T3! wv)
            (r7l-opr-in-carr! (list 'NTH 1 (list 'NTH 1 wv)) (list 'NTH 2 (list 'NTH 1 wv)))
            (let ((pe (dk-pick (lambda (h) (and (pair? h) (eq? (car h) '=)
                                                (pair? (cadr h)) (pair? (car (cadr h)))
                                                (eq? (caar (cadr h)) 'VNB-LAMBDA)))
                               "PHIL(w) = t")))
              (lam-b-h pe))
            (let* ((pq (list '(OPR m_) (list 'NTH 1 (list 'NTH 1 wv)) (list 'NTH 2 (list 'NTH 1 wv))))
                   (pe2 (dk-pick (lambda (h) (equal? h (list '= (list 'LIST pq (list 'NTH 2 wv)) tv)))
                                 "[p.q, r_w] = t")))
              (fact 'eq-sym (list 'LIST pq (list 'NTH 2 wv)) tv)
              (dk-have! (list '= pq u)
                (lambda () (subst (list '= tv (list 'LIST pq (list 'NTH 2 wv))))
                           (r7l-nth-reduce!) (rfl)))
              (r7l-beta!)
              (for-each
               (lambda (n)
                 (dk-focus! n)
                 (if (eq? (car (dk-goal)) 'IN) (ass)
                     (begin (subst (list '= pq u)) (rfl))))
               (dk-opened (lambda () (sep-mi))))))))
      ;; H4: BE(AL s) = s
      (dk-have! (list 'FORALL 'k_ (list 'IMPLIES (list 'IN 'k_ Ifgu)
                                        (list '= (list BE (list AL 'k_)) 'k_)))
        (lambda ()
          (let ((sv (dk-di-var!)))
            (dk-apply! inT3 sv)
            (r7l-beta!)
            (r7l-nth-reduce!)
            (rfl))))
      ;; H5: AL(BE w) = w on the fiber
      (dk-have! (list 'FORALL 'w_ (list 'IMPLIES (list 'IN 'w_ r7l-T3)
                       (list 'IMPLIES (list '= (list r7l-PHIL 'w_) tv)
                             (list '= (list AL (list BE 'w_)) 'w_))))
        (lambda ()
          (let* ((wv (dk-di-var!)))
            (dk-landed (lambda () (di)))
            (r7l-open-T3! wv)
            (r7l-opr-in-carr! (list 'NTH 1 (list 'NTH 1 wv)) (list 'NTH 2 (list 'NTH 1 wv)))
            (let ((pe (dk-pick (lambda (h) (and (pair? h) (eq? (car h) '=)
                                                (pair? (cadr h)) (pair? (car (cadr h)))
                                                (eq? (caar (cadr h)) 'VNB-LAMBDA)))
                               "PHIL(w) = t")))
              (lam-b-h pe))
            (let* ((pq (list '(OPR m_) (list 'NTH 1 (list 'NTH 1 wv)) (list 'NTH 2 (list 'NTH 1 wv)))))
              (fact 'eq-sym (list 'LIST pq (list 'NTH 2 wv)) tv)
              (dk-have! (list '= (list 'NTH 2 wv) rr)
                (lambda () (subst (list '= tv (list 'LIST pq (list 'NTH 2 wv))))
                           (r7l-nth-reduce!) (rfl)))
              (dk-have! (list 'IN (list 'NTH 1 wv) Ifgu)
                (lambda ()
                  (dk-have! (list '= pq u)
                    (lambda () (subst (list '= tv (list 'LIST pq (list 'NTH 2 wv))))
                               (r7l-nth-reduce!) (rfl)))
                  (for-each (lambda (n) (dk-focus! n)
                              (if (eq? (car (dk-goal)) 'IN) (ass)
                                  (begin (subst (list '= pq u)) (rfl))))
                            (dk-opened (lambda () (sep-mi))))))
              (fact 'cartesian-pair-eq wv r7l-Pfg r7l-Sh)
              (r7l-beta!)
              ;; the goal is [NTH 1 w, NTH 2 t] = w; rewrite NTH 2 t back to
              ;; NTH 2 w (not the other way: w occurs inside its own projections)
              (fact 'eq-sym (list 'NTH 2 wv) rr)
              (subst (list '= rr (list 'NTH 2 wv)))
              (fact 'eq-sym wv (list 'LIST (list 'NTH 1 wv) (list 'NTH 2 wv)))
              (ass)))))
      ;; the slice itself
      (fact 'finsum-fiber-slice r7l-ag r7l-T3 Ifgu r7l-PHIL tv r7l-F3L AL BE)
      (subst (list '= (list 'FINSUM r7l-ag r7l-F3L (r7l-FIB tv))
                      (list 'FINSUM r7l-ag SL Ifgu)))
      ;; the two summands agree pointwise on I(f,g,u)
      (dk-have! (list 'FORALL 'w_ (list 'IMPLIES (list 'IN 'w_ Ifgu)
                                        (list '= (list SL 'w_) (list DD 'w_))))
        (lambda ()
          (let ((zv (dk-di-var!)))
            (dk-apply! inT3 zv)
            (dk-have! (list 'IN zv r7l-Pfg)
              (lambda () (dk-split-all! (dk-landed (lambda () (sep-me (list 'IN zv Ifgu))))) (ass)))
            (fact 'cartesian-nth zv r7l-Sf r7l-Sg)
            (r7l-split-head! (list 'IN (list 'NTH 1 zv) r7l-Sf))
            (r7l-in-carr-off-supp! (list 'NTH 1 zv) r7l-Sf)
            (r7l-in-carr-off-supp! (list 'NTH 2 zv) r7l-Sg)
            (fact 'fun-apply-type-c 'f_ '(CARR m_) '(CARR a_) (list 'NTH 1 zv))
            (fact 'fun-apply-type-c 'g_ '(CARR m_) '(CARR a_) (list 'NTH 2 zv))
            (fact 'ring-carrier-closed-mul 'a_ (list 'f_ (list 'NTH 1 zv)) (list 'g_ (list 'NTH 2 zv)))
            (fact 'ring-carrier-closed-mul 'a_
                  (list '(MUL a_) (list 'f_ (list 'NTH 1 zv)) (list 'g_ (list 'NTH 2 zv)))
                  (list 'h_ rr))
            (fact 'lambda-compose-value r7l-F3L AL Ifgu zv)
            (subst (list '== (list SL zv) (list r7l-F3L (list AL zv))))
            (r7l-beta!)
            (r7l-nth-reduce!)
            (rfl))))
      (fact 'finsum-congruence-q r7l-ag Ifgu SL DD)
      (subst (list '== (list 'FINSUM r7l-ag SL Ifgu) (list 'FINSUM r7l-ag DD Ifgu)))
      (fact 'finsum-type r7l-ag Ifgu DD)
      (rfl)))))
;; ---- assemble ------------------------------------------------------
(fact 'finsum-congruence-q r7l-ag r7l-IL r7l-TGT r7l-LQL)
(subst (list '== (list 'FINSUM r7l-ag r7l-TGT r7l-IL) (list 'FINSUM r7l-ag r7l-LQL r7l-IL)))
(fact 'finsum-type r7l-ag r7l-IL r7l-LQL)
(rfl)
(r7l-done! 'monalg-mul-assoc-left-core)

;;; =====================================================================
;;; THE MIRROR.  Same triple set T3, grouped the other way:
;;;   PHIR = w |-> [p, q.r]                 into IR = I(supp f, IMAGE(mult), x)
;;;   F3R  = w |-> f(p).(g(q).h(r))
;;; The T3 condition is (p.q).r = x, so PHIR lands in IR only through the
;;; monoid's associativity -- that is the one place M's associativity is used.
;;; =====================================================================
(define r7l-Pgh (list 'CARTESIAN r7l-Sg r7l-Sh))
(define r7l-mulgh (r7l-mulmap r7l-Sg r7l-Sh))
(define r7l-Igh (list 'IMAGE r7l-mulgh r7l-Pgh))
(define r7l-GH (r7l-mul 'g_ 'h_))
(define r7l-IR (r7l-IQ r7l-Sf r7l-Igh 'x_))
(define r7l-LQR (r7l-LQ 'f_ r7l-GH r7l-Sf r7l-Igh 'x_))
(define r7l-F3R (list 'VNB-LAMBDA 'w r7l-T3
   '((MUL a_) (f_ (NTH 1 (NTH 1 w))) ((MUL a_) (g_ (NTH 2 (NTH 1 w))) (h_ (NTH 2 w))))))
(define r7l-PHIR (list 'VNB-LAMBDA 'w r7l-T3
   '(LIST (NTH 1 (NTH 1 w)) ((OPR m_) (NTH 2 (NTH 1 w)) (NTH 2 w)))))
(define (r7l-FIBR t) (list 'SEP 's_ r7l-T3 (list '= (list r7l-PHIR 's_) t)))
(define r7l-TGTR (list 'VNB-LAMBDA 't_ r7l-IR
                       (list 'FINSUM r7l-ag r7l-F3R (r7l-FIBR 't_))))

(define (r7l-right-prep!)
  (fact 'monalg-mul-fun 'a_ 'm_ 'g_ 'h_)
  (r7l-fun! r7l-GH)
  (dk-have! (list 'IN r7l-Pgh 'SET) (lambda () (mac 'cartesian-set-iff) (dk-conj-close!)))
  (fact 'card-cartesian-nn r7l-Sg r7l-Sh)
  (dk-have! (list 'AND (list 'IN r7l-Pgh 'SET) (list 'IN (list 'CARD r7l-Pgh) 'NN)))
  (fact 'image-set r7l-mulgh r7l-Pgh)
  (fact 'card-image-finite r7l-mulgh r7l-Pgh)
  (dk-have! (list 'AND (list 'IN r7l-Igh 'SET) (list 'IN (list 'CARD r7l-Igh) 'NN))))

(define (r7l-F3R-type!)
  (dk-have! (list 'IN r7l-F3R (list 'FUN r7l-T3 '(CARR a_)))
    (lambda ()
      (dk-lam-t!)
      (let* ((wv (dk-di-var!))
             (pp (list 'NTH 1 (list 'NTH 1 wv)))
             (qq (list 'NTH 2 (list 'NTH 1 wv)))
             (rr (list 'NTH 2 wv)))
        (r7l-open-T3! wv)
        (fact 'fun-apply-type-c 'f_ '(CARR m_) '(CARR a_) pp)
        (fact 'fun-apply-type-c 'g_ '(CARR m_) '(CARR a_) qq)
        (fact 'fun-apply-type-c 'h_ '(CARR m_) '(CARR a_) rr)
        (fact 'ring-carrier-closed-mul 'a_ (list 'g_ qq) (list 'h_ rr))
        (fact 'ring-carrier-closed-mul 'a_ (list 'f_ pp) (list '(MUL a_) (list 'g_ qq) (list 'h_ rr)))
        (ass))))
  (dk-have! (list 'IN r7l-F3R (list 'FUN r7l-T3 (list 'CARR r7l-ag)))
            (lambda () (mac 'raag-carr) (ass)))
  (dk-have! (list 'FORALL 'z_ (list 'IMPLIES (list 'IN 'z_ r7l-T3)
                                    (list 'IN (list r7l-F3R 'z_) (list 'CARR r7l-ag))))
    (lambda ()
      (let ((zv (dk-di-var!)))
        (fact 'fun-apply-type-c r7l-F3R r7l-T3 (list 'CARR r7l-ag) zv)
        (ass)))))

(define (r7l-PHIR-type!)
  (dk-have! (list 'IN r7l-PHIR (list 'FUN r7l-T3 r7l-IR))
    (lambda ()
      (dk-lam-t!)
      (let* ((wv (dk-di-var!))
             (pp (list 'NTH 1 (list 'NTH 1 wv)))
             (qq (list 'NTH 2 (list 'NTH 1 wv)))
             (rr (list 'NTH 2 wv))
             (qr (list '(OPR m_) qq rr)))
        (r7l-open-T3! wv)
        (r7l-opr-in-carr! qq rr)
        (dk-have! (list 'IN (list 'LIST qq rr) r7l-Pgh)
          (lambda () (fact 'pair-in-cartesian r7l-Sg r7l-Sh qq rr) (ass)))
        (dk-have! (list 'IN qr r7l-Igh)
          (lambda ()
            (mac 'image-membership-iff)
            (ew (list 'LIST qq rr))
            (dk-conj-close! (lambda () (if (eq? (car (dk-goal)) '=)
                                           (begin (lam-b) (r7l-nth-reduce!) (rfl))
                                           (ass))))))
        (r7l-monoid-assoc! pp qq rr)
        (fact 'eq-sym (list '(OPR m_) (list '(OPR m_) pp qq) rr) (list '(OPR m_) pp qr))
        (for-each
         (lambda (n)
           (dk-focus! n)
           (if (eq? (car (dk-goal)) 'IN)
               (begin (fact 'pair-in-cartesian r7l-Sf r7l-Igh pp qr) (ass))
               (begin (r7l-nth-reduce!)
                      (subst (list '= (list '(OPR m_) pp qr)
                                      (list '(OPR m_) (list '(OPR m_) pp qq) rr)))
                      (ass))))
         (dk-opened (lambda () (sep-mi))))))))

;;; =====================================================================
;;; monalg-mul-assoc-right-core -- the mirror of the left core.
;;; =====================================================================
(sp (make-wff
  (r7l-foralls '(a_ m_ f_ g_ h_ x_)
    (r7l-imps (list '(IS-RING a_) '(IS-MONOID m_)
                    (list 'IN 'f_ r7l-F) (list 'IN 'g_ r7l-F) (list 'IN 'h_ r7l-F)
                    '(IN x_ (CARR m_)))
      (list '= (list 'FINSUM r7l-ag r7l-LQR r7l-IR)
               (list 'FINSUM r7l-ag r7l-F3R r7l-T3))))))
(dk-peel!)
(r7l-base-prep!)
(r7l-right-prep!)
(r7l-IQ-facts! r7l-Sf r7l-Igh 'x_)
(r7l-LQ-type! 'f_ r7l-GH r7l-Sf r7l-Igh 'x_)
(r7l-T3-facts!)
(r7l-F3R-type!)
(r7l-PHIR-type!)
(fact 'finsum-fiber r7l-ag r7l-T3 r7l-IR r7l-PHIR r7l-F3R)
(subst (list '= (list 'FINSUM r7l-ag r7l-F3R r7l-T3) (list 'FINSUM r7l-ag r7l-TGTR r7l-IR)))
(have! (list 'FORALL 't_ (list 'IMPLIES (list 'IN 't_ r7l-IR)
                               (list '= (list r7l-TGTR 't_) (list r7l-LQR 't_))))
 (lambda ()
  (let* ((tv   (dk-di-var!))
         (pp   (list 'NTH 1 tv))
         (vv   (list 'NTH 2 tv))
         (Ighv (r7l-IQ r7l-Sg r7l-Sh vv))
         (Lghv (r7l-LQ 'g_ 'h_ r7l-Sg r7l-Sh vv))
         (AL   (list 'VNB-LAMBDA 'sa Ighv (list 'LIST (list 'LIST pp '(NTH 1 sa)) '(NTH 2 sa))))
         (BE   (list 'VNB-LAMBDA 'wb r7l-T3 '(LIST (NTH 2 (NTH 1 wb)) (NTH 2 wb))))
         (DD   (list 'VNB-LAMBDA 'z Ighv (list '(MUL a_) (list 'f_ pp) (list Lghv 'z))))
         (SL   (list 'VNB-LAMBDA 'z Ighv (list r7l-F3R (list AL 'z)))))
    (dk-have! (list 'IN tv (list 'CARTESIAN r7l-Sf r7l-Igh))
      (lambda () (dk-split-all! (dk-landed (lambda () (sep-me (list 'IN tv r7l-IR))))) (ass)))
    (dk-have! (list '= (list '(OPR m_) pp vv) 'x_)
      (lambda () (dk-split-all! (dk-landed (lambda () (sep-me (list 'IN tv r7l-IR))))) (ass)))
    (fact 'cartesian-nth tv r7l-Sf r7l-Igh)
    (r7l-split-head! (list 'IN pp r7l-Sf))
    (r7l-in-carr-off-supp! pp r7l-Sf)
    (r7l-in-carr-off-supp! vv r7l-Igh)
    (fact 'cartesian-pair-eq tv r7l-Sf r7l-Igh)
    (fact 'fun-apply-type-c 'f_ '(CARR m_) '(CARR a_) pp)
    (fact 'fun-apply-type-c r7l-GH '(CARR m_) '(CARR a_) vv)
    (r7l-IQ-facts! r7l-Sg r7l-Sh vv)
    (r7l-LQ-type! 'g_ 'h_ r7l-Sg r7l-Sh vv)
    (dk-have! (list '= (list r7l-LQR tv) (list '(MUL a_) (list 'f_ pp) (list r7l-GH vv)))
      (lambda ()
        (lam-b)
        (fact 'ring-carrier-closed-mul 'a_ (list 'f_ pp) (list r7l-GH vv))
        (rfl)))
    (fact 'finsum-fiber-value r7l-ag r7l-F3R r7l-PHIR r7l-T3 r7l-IR tv)
    (subst (list '== (list r7l-TGTR tv) (list 'FINSUM r7l-ag r7l-F3R (r7l-FIBR tv))))
    (subst (list '= (list r7l-LQR tv) (list '(MUL a_) (list 'f_ pp) (list r7l-GH vv))))
    (fact 'monalg-mul-apply 'a_ 'm_ 'g_ 'h_ vv)
    (subst (list '== (list r7l-GH vv) (list 'FINSUM r7l-ag Lghv Ighv)))
    (fact 'finsum-ring-distrib-left-gen 'a_ (list 'f_ pp) Ighv Lghv)
    (subst (list '= (list '(MUL a_) (list 'f_ pp) (list 'FINSUM r7l-ag Lghv Ighv))
                    (list 'FINSUM r7l-ag DD Ighv)))
    ;; [[p, q], r] in T3 for [q, r] in I(g,h,v)
    (dk-have! (list 'FORALL 'sc_ (list 'IMPLIES (list 'IN 'sc_ Ighv)
                     (list 'IN (list 'LIST (list 'LIST pp '(NTH 1 sc_)) '(NTH 2 sc_)) r7l-T3)))
      (lambda ()
        (let ((sv (dk-di-var!)))
          (dk-have! (list 'IN sv r7l-Pgh)
            (lambda () (dk-split-all! (dk-landed (lambda () (sep-me (list 'IN sv Ighv))))) (ass)))
          (dk-have! (list '= (list '(OPR m_) (list 'NTH 1 sv) (list 'NTH 2 sv)) vv)
            (lambda () (dk-split-all! (dk-landed (lambda () (sep-me (list 'IN sv Ighv))))) (ass)))
          (fact 'cartesian-nth sv r7l-Sg r7l-Sh)
          (r7l-split-head! (list 'IN (list 'NTH 1 sv) r7l-Sg))
          (r7l-in-carr-off-supp! (list 'NTH 1 sv) r7l-Sg)
          (r7l-in-carr-off-supp! (list 'NTH 2 sv) r7l-Sh)
          (dk-have! (list 'IN (list 'LIST pp (list 'NTH 1 sv)) r7l-Pfg)
            (lambda () (fact 'pair-in-cartesian r7l-Sf r7l-Sg pp (list 'NTH 1 sv)) (ass)))
          (r7l-monoid-assoc! pp (list 'NTH 1 sv) (list 'NTH 2 sv))
          (for-each
           (lambda (n)
             (dk-focus! n)
             (if (eq? (car (dk-goal)) 'IN)
                 (begin (fact 'pair-in-cartesian r7l-Pfg r7l-Sh
                              (list 'LIST pp (list 'NTH 1 sv)) (list 'NTH 2 sv))
                        (ass))
                 (begin (r7l-nth-reduce!)
                        (subst (list '= (list '(OPR m_) (list '(OPR m_) pp (list 'NTH 1 sv)) (list 'NTH 2 sv))
                                        (list '(OPR m_) pp (list '(OPR m_) (list 'NTH 1 sv) (list 'NTH 2 sv)))))
                        (subst (list '= (list '(OPR m_) (list 'NTH 1 sv) (list 'NTH 2 sv)) vv))
                        (ass))))
           (dk-opened (lambda () (sep-mi)))))))
    (let ((inT3 (dk-pick (lambda (h) (and (pair? h) (eq? (car h) 'FORALL) (equal? (cadr h) 'sc_)))
                         "[[p,q],r] in T3")))
      (dk-have! (list 'IN AL (list 'FUN Ighv r7l-T3))
        (lambda () (dk-lam-t!) (let ((sv (dk-di-var!))) (dk-apply! inT3 sv) (ass))))
      (dk-have! (list 'FORALL 'k_ (list 'IMPLIES (list 'IN 'k_ Ighv)
                                        (list '= (list r7l-PHIR (list AL 'k_)) tv)))
        (lambda ()
          (let ((sv (dk-di-var!)))
            (dk-apply! inT3 sv)
            (dk-have! (list '= (list '(OPR m_) (list 'NTH 1 sv) (list 'NTH 2 sv)) vv)
              (lambda () (dk-split-all! (dk-landed (lambda () (sep-me (list 'IN sv Ighv))))) (ass)))
            (r7l-beta!)
            (r7l-nth-reduce!)
            (subst (list '= (list '(OPR m_) (list 'NTH 1 sv) (list 'NTH 2 sv)) vv))
            (fact 'eq-sym tv (list 'LIST pp vv))
            (ass))))
      (dk-have! (list 'FORALL 'w_ (list 'IMPLIES (list 'IN 'w_ r7l-T3)
                       (list 'IMPLIES (list '= (list r7l-PHIR 'w_) tv)
                             (list 'IN (list BE 'w_) Ighv))))
        (lambda ()
          (let ((wv (dk-di-var!)))
            (dk-landed (lambda () (di)))
            (r7l-open-T3! wv)
            (r7l-opr-in-carr! (list 'NTH 2 (list 'NTH 1 wv)) (list 'NTH 2 wv))
            (let ((pe (dk-pick (lambda (h) (and (pair? h) (eq? (car h) '=)
                                                (pair? (cadr h)) (pair? (car (cadr h)))
                                                (eq? (caar (cadr h)) 'VNB-LAMBDA)))
                               "PHIR(w) = t")))
              (lam-b-h pe))
            (let* ((qr (list '(OPR m_) (list 'NTH 2 (list 'NTH 1 wv)) (list 'NTH 2 wv)))
                   (lhs (list 'LIST (list 'NTH 1 (list 'NTH 1 wv)) qr)))
              (fact 'eq-sym lhs tv)
              (dk-have! (list '= qr vv)
                (lambda () (subst (list '= tv lhs)) (r7l-nth-reduce!) (rfl)))
              (dk-have! (list 'IN (list 'LIST (list 'NTH 2 (list 'NTH 1 wv)) (list 'NTH 2 wv)) r7l-Pgh)
                (lambda () (fact 'pair-in-cartesian r7l-Sg r7l-Sh
                                 (list 'NTH 2 (list 'NTH 1 wv)) (list 'NTH 2 wv)) (ass)))
              (r7l-beta!)
              (for-each
               (lambda (n)
                 (dk-focus! n)
                 (if (eq? (car (dk-goal)) 'IN) (ass)
                     (begin (r7l-nth-reduce!) (subst (list '= qr vv)) (rfl))))
               (dk-opened (lambda () (sep-mi))))))))
      (dk-have! (list 'FORALL 'k_ (list 'IMPLIES (list 'IN 'k_ Ighv)
                                        (list '= (list BE (list AL 'k_)) 'k_)))
        (lambda ()
          (let ((sv (dk-di-var!)))
            (dk-apply! inT3 sv)
            (dk-have! (list 'IN sv r7l-Pgh)
              (lambda () (dk-split-all! (dk-landed (lambda () (sep-me (list 'IN sv Ighv))))) (ass)))
            (fact 'cartesian-pair-eq sv r7l-Sg r7l-Sh)
            (r7l-beta!)
            (r7l-nth-reduce!)
            (fact 'eq-sym sv (list 'LIST (list 'NTH 1 sv) (list 'NTH 2 sv)))
            (ass))))
      (dk-have! (list 'FORALL 'w_ (list 'IMPLIES (list 'IN 'w_ r7l-T3)
                       (list 'IMPLIES (list '= (list r7l-PHIR 'w_) tv)
                             (list '= (list AL (list BE 'w_)) 'w_))))
        (lambda ()
          (let ((wv (dk-di-var!)))
            (dk-landed (lambda () (di)))
            (r7l-open-T3! wv)
            (r7l-opr-in-carr! (list 'NTH 2 (list 'NTH 1 wv)) (list 'NTH 2 wv))
            (let ((pe (dk-pick (lambda (h) (and (pair? h) (eq? (car h) '=)
                                                (pair? (cadr h)) (pair? (car (cadr h)))
                                                (eq? (caar (cadr h)) 'VNB-LAMBDA)))
                               "PHIR(w) = t")))
              (lam-b-h pe))
            (let* ((qr (list '(OPR m_) (list 'NTH 2 (list 'NTH 1 wv)) (list 'NTH 2 wv)))
                   (lhs (list 'LIST (list 'NTH 1 (list 'NTH 1 wv)) qr)))
              (fact 'eq-sym lhs tv)
              (dk-have! (list '= qr vv)
                (lambda () (subst (list '= tv lhs)) (r7l-nth-reduce!) (rfl)))
              (dk-have! (list '= (list 'NTH 1 (list 'NTH 1 wv)) pp)
                (lambda () (subst (list '= tv lhs)) (r7l-nth-reduce!) (rfl)))
              (dk-have! (list 'IN (list 'LIST (list 'NTH 2 (list 'NTH 1 wv)) (list 'NTH 2 wv)) r7l-Pgh)
                (lambda () (fact 'pair-in-cartesian r7l-Sg r7l-Sh
                                 (list 'NTH 2 (list 'NTH 1 wv)) (list 'NTH 2 wv)) (ass)))
              (dk-have! (list 'IN (list 'LIST (list 'NTH 2 (list 'NTH 1 wv)) (list 'NTH 2 wv)) Ighv)
                (lambda ()
                  (for-each (lambda (n) (dk-focus! n)
                              (if (eq? (car (dk-goal)) 'IN) (ass)
                                  (begin (r7l-nth-reduce!) (subst (list '= qr vv)) (rfl))))
                            (dk-opened (lambda () (sep-mi))))))
              (fact 'cartesian-pair-eq wv r7l-Pfg r7l-Sh)
              (fact 'cartesian-pair-eq (list 'NTH 1 wv) r7l-Sf r7l-Sg)
              (r7l-beta!)
              (r7l-nth-reduce!)
              (fact 'eq-sym (list 'NTH 1 (list 'NTH 1 wv)) pp)
              (subst (list '= pp (list 'NTH 1 (list 'NTH 1 wv))))
              (fact 'eq-sym (list 'NTH 1 wv)
                    (list 'LIST (list 'NTH 1 (list 'NTH 1 wv)) (list 'NTH 2 (list 'NTH 1 wv))))
              (subst (list '= (list 'LIST (list 'NTH 1 (list 'NTH 1 wv)) (list 'NTH 2 (list 'NTH 1 wv)))
                              (list 'NTH 1 wv)))
              (fact 'eq-sym wv (list 'LIST (list 'NTH 1 wv) (list 'NTH 2 wv)))
              (ass)))))
      (fact 'finsum-fiber-slice r7l-ag r7l-T3 Ighv r7l-PHIR tv r7l-F3R AL BE)
      (subst (list '= (list 'FINSUM r7l-ag r7l-F3R (r7l-FIBR tv))
                      (list 'FINSUM r7l-ag SL Ighv)))
      (dk-have! (list 'FORALL 'w_ (list 'IMPLIES (list 'IN 'w_ Ighv)
                                        (list '= (list SL 'w_) (list DD 'w_))))
        (lambda ()
          (let ((zv (dk-di-var!)))
            (dk-apply! inT3 zv)
            (dk-have! (list 'IN zv r7l-Pgh)
              (lambda () (dk-split-all! (dk-landed (lambda () (sep-me (list 'IN zv Ighv))))) (ass)))
            (fact 'cartesian-nth zv r7l-Sg r7l-Sh)
            (r7l-split-head! (list 'IN (list 'NTH 1 zv) r7l-Sg))
            (r7l-in-carr-off-supp! (list 'NTH 1 zv) r7l-Sg)
            (r7l-in-carr-off-supp! (list 'NTH 2 zv) r7l-Sh)
            (fact 'fun-apply-type-c 'g_ '(CARR m_) '(CARR a_) (list 'NTH 1 zv))
            (fact 'fun-apply-type-c 'h_ '(CARR m_) '(CARR a_) (list 'NTH 2 zv))
            (fact 'ring-carrier-closed-mul 'a_ (list 'g_ (list 'NTH 1 zv)) (list 'h_ (list 'NTH 2 zv)))
            (fact 'ring-carrier-closed-mul 'a_ (list 'f_ pp)
                  (list '(MUL a_) (list 'g_ (list 'NTH 1 zv)) (list 'h_ (list 'NTH 2 zv))))
            (fact 'lambda-compose-value r7l-F3R AL Ighv zv)
            (subst (list '== (list SL zv) (list r7l-F3R (list AL zv))))
            (r7l-beta!)
            (r7l-nth-reduce!)
            (rfl))))
      (fact 'finsum-congruence-q r7l-ag Ighv SL DD)
      (subst (list '== (list 'FINSUM r7l-ag SL Ighv) (list 'FINSUM r7l-ag DD Ighv)))
      (fact 'finsum-type r7l-ag Ighv DD)
      (rfl)))))
(fact 'finsum-congruence-q r7l-ag r7l-IR r7l-TGTR r7l-LQR)
(subst (list '== (list 'FINSUM r7l-ag r7l-TGTR r7l-IR) (list 'FINSUM r7l-ag r7l-LQR r7l-IR)))
(fact 'finsum-type r7l-ag r7l-IR r7l-LQR)
(rfl)
(r7l-done! 'monalg-mul-assoc-right-core)

;;; =====================================================================
;;; THE EMBED (monalg-is-ring.scm's `mir-embed!', copied): a sum over
;;; I(A,B,x) equals the sum over I(A',B',x) when A c A', B c B' and the
;;; summand vanishes at every index of the larger set outside the smaller.
;;; =====================================================================
(define (r7l-ptwise-type! L I)
  (let ((claim (list 'FORALL 'z (list 'IMPLIES (list 'IN 'z I)
                                      (list 'IN (list L 'z) (list 'CARR r7l-ag))))))
    (dk-have! claim
      (lambda ()
        (let ((zv (cadr (dk-landed-1 (lambda () (di))))))
          (fact 'fun-apply-type-c L I (list 'CARR r7l-ag) zv)
          (ass))))
    claim))
(define (r7l-zero-off-supp! fn q)
  (let ((iff (dk-fact! 'supp-membership 'a_ 'm_ fn q))
        (eq  (list '= (list fn q) '(ZERO a_))))
    (have! eq (lambda () (dk-only! iff (list 'NOT (list 'IN q (r7l-supp fn)))
                                   (list 'IN q '(CARR m_)))
                         (prop)))
    eq))
(define (r7l-embed! f g A B A2 B2 x in-big! vanish!)
  (let* ((I  (r7l-IQ A B x))   (L  (r7l-LQ f g A B x))
         (I2 (r7l-IQ A2 B2 x)) (L2 (r7l-LQ f g A2 B2 x))
         (Q2 (list 'CARTESIAN A2 B2))
         (incl (list 'FORALL 'zc_ (list 'IMPLIES (list 'IN 'zc_ I) (list 'IN 'zc_ I2))))
         (eqE (list '= (list 'FINSUM r7l-ag L2 I2) (list 'FINSUM r7l-ag L2 I)))
         (goal (list '= (list 'FINSUM r7l-ag L I) (list 'FINSUM r7l-ag L2 I2))))
    (have! incl
      (lambda ()
        (di)
        (sep-me (list 'IN 'zc_ I))
        (fact 'cartesian-nth 'zc_ A B)
        (r7l-split-head! (list 'IN '(NTH 1 zc_) A))
        (fact 'cartesian-pair-eq 'zc_ A B)
        (have! (list 'IN 'zc_ Q2)
          (lambda () (subst (list '= 'zc_ '(LIST (NTH 1 zc_) (NTH 2 zc_))))
                     (dk-have! (list 'IN '(NTH 1 zc_) A2) (lambda () (in-big! '(NTH 1 zc_) 'left)))
                     (dk-have! (list 'IN '(NTH 2 zc_) B2) (lambda () (in-big! '(NTH 2 zc_) 'right)))
                     (fact 'pair-in-cartesian A2 B2 '(NTH 1 zc_) '(NTH 2 zc_)) (ass)))
        (for-each (lambda (n) (dk-focus! n) (ass)) (dk-opened (lambda () (sep-mi))))))
    (have! (list 'SUBSET I I2) (lambda () (mac 'subset-def) (ass)))
    (have! (list 'FORALL 'zc_ (list 'IMPLIES (list 'AND (list 'IN 'zc_ I2) (list 'NOT (list 'IN 'zc_ I)))
                                   (list '= (list L2 'zc_) (list 'IDEN r7l-ag))))
      (lambda ()
        (dk-split-all! (dk-peel!))
        (lam-b)                       ; BEFORE sep-me, which consumes the membership
        (sep-me (list 'IN 'zc_ I2))
        (fact 'cartesian-nth 'zc_ A2 B2)
        (r7l-split-head! (list 'IN '(NTH 1 zc_) A2))
        (r7l-in-carr-off-supp! '(NTH 1 zc_) A2)
        (r7l-in-carr-off-supp! '(NTH 2 zc_) B2)
        (fact 'fun-apply-type-c f '(CARR m_) '(CARR a_) '(NTH 1 zc_))
        (fact 'fun-apply-type-c g '(CARR m_) '(CARR a_) '(NTH 2 zc_))
        (fact 'cartesian-pair-eq 'zc_ A2 B2)
        (mac 'raag-iden)
        (vanish!)))
    (have! (list 'FORALL 'zc_ (list 'IMPLIES (list 'IN 'zc_ I) (list '= (list L 'zc_) (list L2 'zc_))))
      (lambda ()
        (di)
        (dk-apply! incl 'zc_)
        (fact 'fun-apply-type-c L I (list 'CARR r7l-ag) 'zc_)
        (lam-b-h (list 'IN (list L 'zc_) (list 'CARR r7l-ag)))
        (lam-b)
        (rfl)))
    (r7l-ptwise-type! L I)
    (fact 'finsum-congruence r7l-ag I L L2)
    (fact 'finsum-embed r7l-ag I I2 L2)
    (have! goal (lambda () (subst eqE) (ass)))
    goal))
(define (r7l-vanish-left! fn g A B x)
  (lambda ()
    (let ((I (r7l-IQ A B x)))
      (have! (list 'NOT (list 'IN '(NTH 1 zc_) A))
        (lambda ()
          (di)
          (have! (list 'IN 'zc_ I)
            (lambda ()
              (for-each (lambda (n) (dk-focus! n)
                          (if (eq? (car (dk-goal)) '=) (ass)
                              (begin (subst '(= zc_ (LIST (NTH 1 zc_) (NTH 2 zc_))))
                                     (fact 'pair-in-cartesian A B '(NTH 1 zc_) '(NTH 2 zc_)) (ass))))
                        (dk-opened (lambda () (sep-mi))))))
          (ai (list 'NOT (list 'IN 'zc_ I)))))
      (let ((eq (r7l-zero-off-supp! fn '(NTH 1 zc_))))
        (subst eq)
        (fact 'ring-mul-zero-left 'a_ (list g '(NTH 2 zc_)))
        (ass)))))
(define (r7l-vanish-right! f fn A B x)
  (lambda ()
    (let ((I (r7l-IQ A B x)))
      (have! (list 'NOT (list 'IN '(NTH 2 zc_) B))
        (lambda ()
          (di)
          (have! (list 'IN 'zc_ I)
            (lambda ()
              (for-each (lambda (n) (dk-focus! n)
                          (if (eq? (car (dk-goal)) '=) (ass)
                              (begin (subst '(= zc_ (LIST (NTH 1 zc_) (NTH 2 zc_))))
                                     (fact 'pair-in-cartesian A B '(NTH 1 zc_) '(NTH 2 zc_)) (ass))))
                        (dk-opened (lambda () (sep-mi))))))
          (ai (list 'NOT (list 'IN 'zc_ I)))))
      (let ((eq (r7l-zero-off-supp! fn '(NTH 2 zc_))))
        (subst eq)
        (fact 'ring-mul-zero-right 'a_ (list f '(NTH 1 zc_)))
        (ass)))))

;;; =====================================================================
;;; monalg-mul-assoc-at -- the convolution associativity, pointwise.
;;; =====================================================================
(define r7l-Sfg (r7l-supp r7l-FG))
(define r7l-Sgh (r7l-supp r7l-GH))
(sp (make-wff
  (r7l-foralls '(a_ m_ f_ g_ h_ x_)
    (r7l-imps (list '(IS-RING a_) '(IS-MONOID m_)
                    (list 'IN 'f_ r7l-F) (list 'IN 'g_ r7l-F) (list 'IN 'h_ r7l-F)
                    '(IN x_ (CARR m_)))
      (list '= (list (r7l-mul r7l-FG 'h_) 'x_) (list (r7l-mul 'f_ r7l-GH) 'x_))))))
(dk-peel!)
(r7l-base-prep!)
(r7l-right-prep!)
(r7l-supp-facts! r7l-FG)
(r7l-supp-facts! r7l-GH)
(r7l-IQ-facts! r7l-Sfg r7l-Sh 'x_)
(r7l-LQ-type! r7l-FG 'h_ r7l-Sfg r7l-Sh 'x_)
(r7l-IQ-facts! r7l-Ifg r7l-Sh 'x_)
(r7l-LQ-type! r7l-FG 'h_ r7l-Ifg r7l-Sh 'x_)
(r7l-IQ-facts! r7l-Sf r7l-Sgh 'x_)
(r7l-LQ-type! 'f_ r7l-GH r7l-Sf r7l-Sgh 'x_)
(r7l-IQ-facts! r7l-Sf r7l-Igh 'x_)
(r7l-LQ-type! 'f_ r7l-GH r7l-Sf r7l-Igh 'x_)
(r7l-T3-facts!)
(r7l-F3L-type!)
(r7l-F3R-type!)
(fact 'monalg-mul-apply 'a_ 'm_ r7l-FG 'h_ 'x_)
(subst (list '== (list (r7l-mul r7l-FG 'h_) 'x_)
                 (list 'FINSUM r7l-ag (r7l-LQ r7l-FG 'h_ r7l-Sfg r7l-Sh 'x_)
                       (r7l-IQ r7l-Sfg r7l-Sh 'x_))))
(fact 'monalg-mul-apply 'a_ 'm_ 'f_ r7l-GH 'x_)
(subst (list '== (list (r7l-mul 'f_ r7l-GH) 'x_)
                 (list 'FINSUM r7l-ag (r7l-LQ 'f_ r7l-GH r7l-Sf r7l-Sgh 'x_)
                       (r7l-IQ r7l-Sf r7l-Sgh 'x_))))
(subst (r7l-embed! r7l-FG 'h_ r7l-Sfg r7l-Sh r7l-Ifg r7l-Sh 'x_
                   (lambda (t side)
                     (if (eq? side 'right) (ass)
                         (begin (fact 'monalg-mul-supp-in-image 'a_ 'm_ 'f_ 'g_ t) (ass))))
                   (r7l-vanish-left! r7l-FG 'h_ r7l-Sfg r7l-Sh 'x_)))
(subst (r7l-embed! 'f_ r7l-GH r7l-Sf r7l-Sgh r7l-Sf r7l-Igh 'x_
                   (lambda (t side)
                     (if (eq? side 'left) (ass)
                         (begin (fact 'monalg-mul-supp-in-image 'a_ 'm_ 'g_ 'h_ t) (ass))))
                   (r7l-vanish-right! 'f_ r7l-GH r7l-Sf r7l-Sgh 'x_)))
(fact 'monalg-mul-assoc-left-core 'a_ 'm_ 'f_ 'g_ 'h_ 'x_)
(subst (list '= (list 'FINSUM r7l-ag r7l-LQL r7l-IL) (list 'FINSUM r7l-ag r7l-F3L r7l-T3)))
(fact 'monalg-mul-assoc-right-core 'a_ 'm_ 'f_ 'g_ 'h_ 'x_)
(subst (list '= (list 'FINSUM r7l-ag r7l-LQR r7l-IR) (list 'FINSUM r7l-ag r7l-F3R r7l-T3)))
;; the two triple summands agree pointwise, by the ring's multiplicative associativity
(have! (list 'FORALL 'w_ (list 'IMPLIES (list 'IN 'w_ r7l-T3)
                               (list '= (list r7l-F3L 'w_) (list r7l-F3R 'w_))))
  (lambda ()
    (let* ((wv (dk-di-var!))
           (pp (list 'NTH 1 (list 'NTH 1 wv)))
           (qq (list 'NTH 2 (list 'NTH 1 wv)))
           (rr (list 'NTH 2 wv)))
      (r7l-open-T3! wv)
      (fact 'fun-apply-type-c 'f_ '(CARR m_) '(CARR a_) pp)
      (fact 'fun-apply-type-c 'g_ '(CARR m_) '(CARR a_) qq)
      (fact 'fun-apply-type-c 'h_ '(CARR m_) '(CARR a_) rr)
      (r7l-beta!)
      (fact 'ring-mul-assoc 'a_ (list 'f_ pp) (list 'g_ qq) (list 'h_ rr))
      (ass))))
(fact 'finsum-congruence-q r7l-ag r7l-T3 r7l-F3L r7l-F3R)
(subst (list '== (list 'FINSUM r7l-ag r7l-F3L r7l-T3) (list 'FINSUM r7l-ag r7l-F3R r7l-T3)))
(fact 'finsum-type r7l-ag r7l-T3 r7l-F3R)
(rfl)
(r7l-done! 'monalg-mul-assoc-at)

;;; =====================================================================
;;; monalg-mul-assoc -- THE LEAF.  The statement is built through the same
;;; `forall-guarded' call as structure-library/polynomial.scm:160.
;;; =====================================================================
(sp (make-wff
  (forall-guarded '(A M f g h)
    (list '(IS-RING A) '(IS-MONOID M)
          '(IN f (FINSUPP A M)) '(IN g (FINSUPP A M)) '(IN h (FINSUPP A M)))
    '(= (MONALG-MUL A M (MONALG-MUL A M f g) h)
        (MONALG-MUL A M f (MONALG-MUL A M g h))))))
(dk-peel!)
(fact 'monalg-mul-fun 'a 'm 'f 'g)
(fact 'monalg-mul-fun 'a 'm 'g 'h)
(fact 'monalg-mul-fun 'a 'm '(MONALG-MUL a m f g) 'h)
(fact 'monalg-mul-fun 'a 'm 'f '(MONALG-MUL a m g h))
(have! '(FORALL x_ (IMPLIES (IN x_ (CARR m))
          (= ((MONALG-MUL a m (MONALG-MUL a m f g) h) x_)
             ((MONALG-MUL a m f (MONALG-MUL a m g h)) x_))))
  (lambda ()
    (let ((xv (dk-di-var!)))
      (fact 'monalg-mul-assoc-at 'a 'm 'f 'g 'h xv)
      (ass))))
(fact 'monalg-ext 'a 'm '(MONALG-MUL a m (MONALG-MUL a m f g) h)
                        '(MONALG-MUL a m f (MONALG-MUL a m g h)))
(ass)
(r7l-done! 'monalg-mul-assoc)
(gloss! 'monalg-mul-assoc
  "Convolution in A[M] is associative.  Both ((f*g)*h)(x) and (f*(g*h))(x) are
   the sum over the triples (p,q,r) in supp f x supp g x supp h with (p.q).r = x
   of (f(p).g(q)).h(r): the outer index set is embedded in one built from the
   three supports, finsum-fiber groups the triples by (p.q, r) resp. (p, q.r),
   and each fiber is carried onto the inner convolution's index set by an
   explicitly inverted map (finsum-fiber-slice).  M's associativity enters once,
   in the typing of the second grouping map; the ring's, once, in the final
   pointwise congruence.")

;;; ======================================================================
;;; END spliced block (rake batch 5c-L)
;;; ======================================================================

(sp (make-wff '(FORALL A (FORALL M (IMPLIES (IS-RING A) (IMPLIES (IS-MONOID M) (IS-RING (MONALG A M))))))))
(dk-peel!)
(mac 'IS-RING)
(let lp () (let ((l (any-pred (lambda (n) ((dk-head? 'AND) (dk-goal-of n))) (proof-leaves))))
             (when l (dk-focus! l) (di) (lp))))
;; 1. length
(mir-disch! (mir-is? '= 'LENGTH) (lambda () (mac 'MONALG) (len-r) (rfl)))
;; 2. carrier is a set
(mir-disch! (mir-is? 'IN 'CARR) (lambda () (mac 'monalg-carr) (fact 'finsupp-in-set 'a 'm) (ass)))
;; 3. add is a function on F x F
(mir-disch! (mir-is? 'IN 'ADD)
  (lambda () (mac 'monalg-carr) (mac 'monalg-add-op) (fact 'finsupp-in-set 'a 'm) (mir-lam-t!)
    (dk-peel!)
    (let ((t (mir-lam-arg (dk-goal))))
      (fact 'monalg-add-fun 'a 'm (cadddr t) (car (cddddr t))) (ass))))
;; 4. mul is a function on F x F
(mir-disch! (mir-is? 'IN 'MUL)
  (lambda () (mac 'monalg-carr) (mac 'monalg-mul-op) (fact 'finsupp-in-set 'a 'm) (mir-lam-t!)
    (dk-peel!)
    (let ((t (mir-lam-arg (dk-goal))))
      (fact 'monalg-mul-fun 'a 'm (cadddr t) (car (cddddr t))) (ass))))
;; 5. neg is a function on F
(mir-disch! (mir-is? 'IN 'NEG)
  (lambda () (mac 'monalg-carr) (mac 'monalg-neg-op) (fact 'finsupp-in-set 'a 'm) (mir-lam-t!)
    (dk-peel!)
    (let ((t (mir-lam-arg (dk-goal))))
      (fact 'monalg-neg-fun 'a 'm (cadddr t)) (ass))))
;; 6, 7. zero and one lie in F
(mir-disch! (mir-is? 'IN 'ZERO) (lambda () (mac 'monalg-carr) (mac 'monalg-zero-slot) (fact 'monalg-zero-in 'a 'm) (ass)))
(mir-disch! (mir-is? 'IN 'ONE)  (lambda () (mac 'monalg-carr) (mac 'monalg-one-slot)  (fact 'monalg-one-in 'a 'm)  (ass)))
;; 8. add associative
(mir-disch! (mir-is? 'is-associative 'ADD)
  (lambda () (mac 'is-associative) (mac 'monalg-carr) (mac 'monalg-add-op)
    (let ((vs (mir-peel-binders!)))
      (let ((u (car vs)) (v (cadr vs)) (w (caddr vs)))
        (fact 'monalg-add-fun 'a 'm u v) (fact 'monalg-add-fun 'a 'm v w)
        (lam-b)
        (fact 'monalg-add-assoc 'a 'm u v w) (ass)))))
;; 9. add commutative
(mir-disch! (mir-is? 'is-commutative 'ADD)
  (lambda () (mac 'is-commutative) (mac 'monalg-carr) (mac 'monalg-add-op)
    (let ((vs (mir-peel-binders!)))
      (lam-b)
      (fact 'monalg-add-comm 'a 'm (car vs) (cadr vs)) (ass))))
;; 10. zero is the additive identity
(mir-disch! (mir-is? 'is-identity 'ADD)
  (lambda () (mac 'is-identity) (mac 'monalg-carr) (mac 'monalg-add-op) (mac 'monalg-zero-slot)
    (let ((vs (mir-peel-binders!)))
      (fact 'monalg-zero-in 'a 'm)
      (dk-conj-close! (lambda ()
        (lam-b)
        (fact 'monalg-add-zero-left 'a 'm (car vs)) (fact 'monalg-add-zero-right 'a 'm (car vs)) (ass))))))
;; 11. neg gives additive inverses
(mir-disch! (mir-is? 'has-inverses 'ADD)
  (lambda () (mac 'has-inverses) (mac 'monalg-carr) (mac 'monalg-add-op) (mac 'monalg-neg-op) (mac 'monalg-zero-slot)
    (let ((vs (mir-peel-binders!)))
      (fact 'monalg-zero-in 'a 'm) (fact 'monalg-neg-fun 'a 'm (car vs))
      (dk-conj-close! (lambda ()
        (lam-b)
        (fact 'monalg-add-neg-left 'a 'm (car vs)) (fact 'monalg-add-neg-right 'a 'm (car vs)) (ass))))))
;; 12. mul associative -- CHAINED to the seed monalg-mul-assoc (structure-library/polynomial.scm)
(mir-disch! (mir-is? 'is-associative 'MUL)
  (lambda () (mac 'is-associative) (mac 'monalg-carr) (mac 'monalg-mul-op)
    (let ((vs (mir-peel-binders!)))
      (let ((u (car vs)) (v (cadr vs)) (w (caddr vs)))
        (fact 'monalg-mul-fun 'a 'm u v) (fact 'monalg-mul-fun 'a 'm v w)
        (lam-b)
        (fact 'monalg-mul-assoc 'a 'm u v w) (ass)))))
;; 13. one is the multiplicative identity
(mir-disch! (mir-is? 'is-identity 'MUL)
  (lambda () (mac 'is-identity) (mac 'monalg-carr) (mac 'monalg-mul-op) (mac 'monalg-one-slot)
    (let ((vs (mir-peel-binders!)))
      (fact 'monalg-one-in 'a 'm)
      (dk-conj-close! (lambda ()
        (lam-b)
        (fact 'monalg-one-left-fn 'a 'm (car vs)) (fact 'monalg-one-right-fn 'a 'm (car vs)) (ass))))))
;; 14. distributivity
(mir-disch! (mir-is? 'is-distributive 'ADD)
  (lambda () (mac 'is-distributive) (mac 'monalg-carr) (mac 'monalg-add-op) (mac 'monalg-mul-op)
    (let ((vs (mir-peel-binders!)))
      (let ((u (car vs)) (v (cadr vs)) (w (caddr vs)))
        (fact 'monalg-add-fun 'a 'm u v) (fact 'monalg-add-fun 'a 'm v w)
        (fact 'monalg-mul-fun 'a 'm u v) (fact 'monalg-mul-fun 'a 'm u w) (fact 'monalg-mul-fun 'a 'm v w)
        (dk-conj-close! (lambda ()
          (lam-b)
          (fact 'monalg-distrib-left 'a 'm u v w) (fact 'monalg-distrib-right 'a 'm u v w) (ass)))))))
(qed 'monalg-is-ring)
(topic! 'monalg-is-ring 'algebra)
