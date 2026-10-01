;;; rake-prod-of-sums.scm -- the product-of-sums expansion, proven.
;;;
;;;     prod_{k in X} (a(k) + b(k))
;;;         = sum_{S in POWER(X)} (prod_{k in S} a(k)) * (prod_{k in X\S} b(k))
;;;
;;; This file proves `prod-of-sums-expansion' (asserted at
;;; theorem-library/prod-of-sums.scm:137, warranted `well-known'), with the
;;; statement copied LITERALLY -- the load prints "already installed;
;;; re-installing the same statement", which is the signal that the support at
;;; that site is to be RETIRED -- plus the bricks it wants:
;;;
;;;   difference-empty-left       {} \ S = {}
;;;   insert-remove               k not in S  =>  (S u {k}) \ {k} = S
;;;   prod-ring-type-ptwise       PROD-RING stays in the carrier, factor typed POINTWISE
;;;   prod-ring-insert-ptwise     the insertion recurrence, factor typed POINTWISE
;;;   prod-ring-congruence-q      two factor families agreeing on X have == products
;;;   cra-carr / cra-op           the two read-offs of COMMUTATIVE-RING-ADDITIVE-AG
;;;   difference-in-power         W \ S is a subset of W
;;;   prod-ring-type-subset       the product over any SUBSET of a finite index set
;;;   prod-of-sums-summand-type   each term of the expansion is in the carrier
;;;   power-insert-injective      S |-> S u {k} injects POWER(X) into POWER(X u {k})
;;;   lambda-eta-value            ((z_ in D |-> ff(z_)) pt) == ff(pt)
;;;   prod-of-sums-ptwise         the expansion with a and b typed POINTWISE
;;;
;;; USES bc* (class-extensionality): this file loads FROM SOURCE and must never
;;; be compile-file'd.  Load floor: after theorem-library/monalg-is-ring
;;; (lambda-compose-value); no ceiling.
;;;
;;; WHY THE POINTWISE FORMS.  The induction is `finite-set-induction' on the
;;; index set, so the index set VARIES while a and b stay fixed; a FUN typing
;;; `a in FUN(X, CARR R)' does not restrict to a subset (the tree cannot form
;;; the restriction of a set function), while a POINTWISE typing does, in one
;;; union-membership step.  CLAUDE.md, "Finite sums and sets".  The capstone
;;; then derives the FUN-typed statement from the pointwise one by
;;; `fun-apply-type-c'.
;;;
;;; THE ROUTE (written out at theorem-library/rake-finsum-cm-union.scm:628-655,
;;; followed here without change).  Induction on u, class
;;;
;;;   C = { u | for all pointwise-typed a, b:  LHS(u) = RHS(u) }
;;;
;;; with R fixed by the outer peel.  Base u = {}: prod-ring-empty gives ONE(R),
;;; POWER({}) = {{}} (power-of-empty) and the one term is ONE * ONE.
;;; Step u |-> u u {k0}:
;;;
;;;   (1) prod-ring-insert-ptwise peels the factor (a k0 + b k0) off the left,
;;;       after prod-ring-congruence-q has moved the factor family's own lambda
;;;       DOMAIN from u u {k0} back to u -- the two products are over
;;;       syntactically different families and only a congruence relates them;
;;;   (2) the induction hypothesis rewrites the smaller product as the sum over
;;;       POWER(u), and ring-left-dist splits P * (a k0 + b k0);
;;;   (3) finsum-ring-distrib-right pushes each constant factor inside that sum;
;;;   (4) power-insert-cover / power-insert-disjoint cut POWER(u u {k0}) into
;;;       POWER(u) and the image of S |-> S u {k0}, and finsum-union-disjoint
;;;       splits the goal's sum along the cut;
;;;   (5) on the POWER(u) half, insert-difference-outside turns the summand into
;;;       the `b' half of (3) (the subsets AVOIDING k0);
;;;   (6) on the image half, finsum-reindex-ag -- along the bijection
;;;       power-insert-injective + injection-image-is-bijection provide -- pulls
;;;       the sum back to POWER(u), and insert-difference-cancel turns the
;;;       summand into the `a' half of (3) (the subsets CONTAINING k0).
;;;
;;; The outer sum is a sum in the ring's ADDITIVE abelian group, so the
;;; abelian-group finsum laws are the right ones there; the products are sums in
;;; the multiplicative COMM-MONOID view, so the comm-monoid laws are the right
;;; ones under PROD-RING.  The additive view is kept as
;;; COMMUTATIVE-RING-ADDITIVE-AG throughout (that is what the statement and
;;; finsum-ring-distrib-right say); `cra-carr' and `cra-op' read its carrier and
;;; operation off, through `cra-is-rag' and ras-carr / ras-op.
;;;
;;; ONE FINDING, recorded where it bit (see (11)).  The reindexed summand
;;; finsum-reindex-ag builds is (z in T |-> f(phi(z))) with BOTH f and phi
;;; lambdas, so contracting its redexes at a point is a CHAIN: the application
;;; f(...) only becomes a redex after phi(z) has been contracted.  `lam-b'
;;; contracts the whole chain in one inference and the independent rule CHECKER
;;; REFUSES it ("the hypothesis' goal is not the goal with redexes contracted").
;;; The cure is to do the first two contractions by CITATION -- the value lemmas
;;; `lambda-compose-value' (monalg-is-ring.scm) and `lambda-eta-value' (new
;;; here), both stated with VARIABLE heads, so each is a single contraction --
;;; and leave only the last one to `lam-b'.
;;;
;;; ---------------------------------------------------------------------
;;; Helpers (local to this file: driver-kit.scm or the file, no third place)
;;; ---------------------------------------------------------------------

(define (r12e-check! name)
  (if (not (proof-done? *ps*))
      (begin
        (display ";; r12e: OPEN LEAVES before qed ") (display name) (newline)
        (for-each (lambda (l)
                    (display ";;   ") (display (expression->string (dk-goal-of l))) (newline))
                  (proof-leaves))
        (error "r12e: proof not complete" name))))

(define (r12e-done! name)
  (r12e-check! name)
  (qed name)
  (topic! name 'algebra))

(define (r12e-sing v) (list 'PAIR v v))

(define (r12e-tf v type body) (list 'FORALL v (list 'IMPLIES type body)))
(define (r12e-tfin S body)
  (list 'FORALL S (list 'IMPLIES (list 'IN S 'SET)
    (list 'IMPLIES (list 'IN (list 'CARD S) 'NN) body))))

;; `fact' of a membership IFF lands BOTH the instance and the universal; name
;; the instance by its left-hand side.
;; (iff-for retired 2026-09-25: the kit's `iff-for')

(define (r12e-mem-iff! lhs . args)
  (apply fact args)
  (iff-for lhs))

;; `fact', then detach EVERY remaining antecedent from the context (dk-fact!
;; stops at the first antecedent `fact' did not recognise; detach! errors loudly
;; when the antecedent is not there, which is what we want).
(define (r12e-fact! . args)
  (let loop ((r (apply dk-fact! args)))
    (if (and (pair? r) (eq? (car r) 'IMPLIES))
        (loop (dk-landed-1 (lambda () (detach! r))))
        r)))

;; pairing-membership's guard sits BETWEEN its binders, so `fact' stops at the
;; detached (FORALL x ...) and the element has to come from `inst*!'.
(define (r12e-pairmem! kk v)
  (let ((g (list 'AND (list 'IN kk 'SET) (list 'IN kk 'SET))))
    (if (not (any-pred (lambda (f) (alpha-equiv? f g)) (dk-asms))) (have! g)))
  (fact 'pairing-membership kk kk)
  (inst*! (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                    (pair? (caddr f)) (eq? (car (caddr f)) 'IFF)
                                    (equal? (caddr (cadr (caddr f))) (r12e-sing kk))))
                   "the pairing universal")
          v)
  (iff-for (list 'IN v (r12e-sing kk))))

(define (r12e-ensure! form thunk)
  (if (any-pred (lambda (f) (alpha-equiv? f form)) (dk-asms))
      form
      (begin (have! form thunk) form)))

;; (IN z (UNION A B)) in context, from (IN z A) (WHICH = 'left) or (IN z B).
(define (r12e-in-union! av bv zv which)
  (let* ((un (list 'UNION av bv))
         (um (r12e-mem-iff! (list 'IN zv un) 'union-membership av bv zv))
         (hv (list 'IN zv (if (eq? which 'left) av bv))))
    (r12e-ensure! (list 'IN zv un) (lambda () (dk-only! um hv) (prop)))))

;; the pointwise typing over DOM: forall z_ in DOM. (F z_) in CARR(R).
(define (r12e-ptw rv fsym dom)
  (list 'FORALL 'z_ (list 'IMPLIES (list 'IN 'z_ dom)
                          (list 'IN (list fsym 'z_) (list 'CARR rv)))))

;; a guarded universal over DOM whose consequent's head is HEAD.
(define (r12e-guarded-over dom head what)
  (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                            (pair? (caddr f)) (eq? (car (caddr f)) 'IMPLIES)
                            (pair? (cadr (caddr f)))
                            (eq? (car (cadr (caddr f))) 'IN)
                            (equal? (caddr (cadr (caddr f))) dom)
                            (pair? (caddr (caddr f)))
                            (eq? (car (caddr (caddr f))) head)))
           what))

;; a guarded universal over DOM, proved by bridging each z into SRC's domain
;; with BRIDGE! and applying SRC there.
(define (r12e-restrict-univ! form src bridge!)
  (r12e-ensure! form
    (lambda ()
      (let ((zv (dk-di-var!)))
        (bridge! zv)
        (dk-apply! src zv)
        (ass)))))

;;; =====================================================================
;;; (1) difference-empty-left -- {} \ S = {}.
;;; =====================================================================
(sp (make-wff '(FORALL s_ (= (DIFFERENCE EMPTY-SET s_) EMPTY-SET))))
(di)
(let ((sv (caddr (cadr (dk-goal)))))
  (bc* 'class-extensionality)
  (let* ((yv (dk-di-var! (lambda (gg) (cadr (cadr gg)))))
         (dl (r12e-mem-iff! (list 'IN yv (list 'DIFFERENCE 'EMPTY-SET sv))
                            'difference-membership 'EMPTY-SET sv yv))
         (ne (dk-fact! 'empty-set-has-no-members yv)))
    (dk-only! dl ne)
    (prop)))
(r12e-done! 'difference-empty-left)
(gloss! 'difference-empty-left
  "The empty set minus anything is the empty set.")

;;; =====================================================================
;;; (2) insert-remove -- (S u {k}) \ {k} = S, for k outside S.
;;;     The inverse of the insert map S |-> S u {k}, and what makes it
;;;     injective.
;;; =====================================================================
(define r12e-ir-stmt
  '(FORALL s_ (FORALL k_ (IMPLIES (IN k_ SET)
     (IMPLIES (NOT (IN k_ s_))
       (= (DIFFERENCE (UNION s_ (PAIR k_ k_)) (PAIR k_ k_)) s_))))))

(sp (make-wff r12e-ir-stmt))
(dk-peel!)
(let* ((g   (dk-goal))
       (lhs (cadr g))
       (sv  (caddr g))
       (uk  (cadr lhs))                      ; (UNION s_ {k})
       (pr  (caddr lhs))                     ; {k}
       (kv  (cadr pr)))
  (bc* 'class-extensionality)
  (let* ((yv  (dk-di-var! (lambda (gg) (cadr (cadr gg)))))
         (dl  (r12e-mem-iff! (list 'IN yv lhs) 'difference-membership uk pr yv))
         (ul  (r12e-mem-iff! (list 'IN yv uk)  'union-membership sv pr yv))
         (pm  (r12e-pairmem! kv yv))
         (kay (list 'IMPLIES (list '= yv kv) (list 'NOT (list 'IN yv sv)))))
    (have! kay (lambda () (di) (subst (list '= yv kv)) (ass)))
    (dk-only! dl ul pm kay)
    (prop)))
(r12e-done! 'insert-remove)
(gloss! 'insert-remove
  "Inserting a point and removing it again returns the set: for k not in S,
   (S u {k}) \\ {k} = S.")

;;; =====================================================================
;;; (3) prod-ring-type-ptwise -- PROD-RING stays in the carrier, with the
;;;     factor typed POINTWISE.  `prod-ring-type' (rake-finsum-typing.scm)
;;;     asks for a FUN typing over the index set, which an induction that
;;;     varies the index set never has.
;;; =====================================================================
(define r12e-view '(COMMUTATIVE-RING-MULTIPLICATIVE-CM R))
(define r12e-vcarr (list 'CARR r12e-view))

(define r12e-prt-stmt
  (r12e-tf 'R '(IS-COMMUTATIVE-RING R)
    (r12e-tfin 'X
      '(FORALL f (IMPLIES (FORALL z_ (IMPLIES (IN z_ X) (IN (f z_) (CARR R))))
         (IN (PROD-RING R f X) (CARR R)))))))

(sp (make-wff r12e-prt-stmt))
(dk-peel!)
(let ((ptw (r12e-guarded-over 'X 'IN "the pointwise typing over X")))
  (dk-fact! 'crmcm-carr 'R)
  (dk-fact! 'commutative-ring-multiplicative-cm-is-comm-monoid 'R)
  (have! (r12e-ptw r12e-view 'f 'X)
         (lambda ()
           (let ((zv (dk-di-var!)))
             (dk-apply! ptw zv)
             (subst (list '= r12e-vcarr '(CARR R)))
             (ass))))
  (r12e-fact! 'finsum-comm-monoid-type-ptwise r12e-view 'X 'f)
  (mac 'PROD-RING)
  (mac 'FINPROD)
  (dk-fact! 'equality-symmetry r12e-vcarr '(CARR R))
  (subst (list '= '(CARR R) r12e-vcarr))
  (ass))
(r12e-done! 'prod-ring-type-ptwise)
(gloss! 'prod-ring-type-ptwise
  "The finite product of a pointwise-typed family over a finite index set lies
   in the ring's carrier.")

;;; =====================================================================
;;; (4) prod-ring-insert-ptwise -- the insertion recurrence, factor typed
;;;     POINTWISE.  This is `finsum-cm-insert-ptwise' at the multiplicative
;;;     view, exactly as `prod-ring-insert' is `finsum-insert' there.
;;; =====================================================================
(define r12e-pri-stmt
  (r12e-tf 'R '(IS-COMMUTATIVE-RING R)
    (r12e-tfin 'X
      '(FORALL k_ (IMPLIES (IN k_ SET) (IMPLIES (NOT (IN k_ X))
         (FORALL f (IMPLIES (FORALL z_ (IMPLIES (IN z_ (UNION X (PAIR k_ k_)))
                                                (IN (f z_) (CARR R))))
           (= (PROD-RING R f (UNION X (PAIR k_ k_)))
              ((MUL R) (PROD-RING R f X) (f k_)))))))))))

(sp (make-wff r12e-pri-stmt))
(dk-peel!)
(let* ((g   (dk-goal))
       (uu  (cadddr (cadr g)))                 ; (UNION X {k_})
       (kv  (cadr (caddr uu)))
       (ptw (r12e-guarded-over uu 'IN "the pointwise typing over X u {k}")))
  (dk-fact! 'crmcm-carr 'R)
  (dk-fact! 'crmcm-op 'R)
  (dk-fact! 'commutative-ring-multiplicative-cm-is-comm-monoid 'R)
  (have! (r12e-ptw r12e-view 'f uu)
         (lambda ()
           (let ((zv (dk-di-var!)))
             (dk-apply! ptw zv)
             (subst (list '= r12e-vcarr '(CARR R)))
             (ass))))
  (r12e-fact! 'finsum-cm-insert-ptwise r12e-view 'X kv 'f)
  (mac 'PROD-RING)
  (mac 'FINPROD)
  (dk-fact! 'eq-sym (list 'OPR r12e-view) '(MUL R))
  (subst (list '= '(MUL R) (list 'OPR r12e-view)))
  (ass))
(r12e-done! 'prod-ring-insert-ptwise)
(gloss! 'prod-ring-insert-ptwise
  "Adding one fresh index k to a finite index set multiplies one more factor
   f(k) into the product; the factor family is typed pointwise.")

;;; =====================================================================
;;; (5) prod-ring-congruence-q -- two factor families that agree on the index
;;;     set have quasi-equal products.  No typing at all: the conclusion is
;;;     `=='.  This is what moves a product's summand lambda from one DOMAIN
;;;     to another at the induction step.
;;; =====================================================================
(define r12e-prc-stmt
  (r12e-tf 'R '(IS-COMMUTATIVE-RING R)
    (r12e-tfin 'X
      '(FORALL f (FORALL g (IMPLIES (FORALL z_ (IMPLIES (IN z_ X) (= (f z_) (g z_))))
         (== (PROD-RING R f X) (PROD-RING R g X))))))))

(sp (make-wff r12e-prc-stmt))
(dk-peel!)
(dk-fact! 'commutative-ring-multiplicative-cm-is-comm-monoid 'R)
(r12e-fact! 'finsum-cm-congruence-q r12e-view 'X 'f 'g)
(mac 'PROD-RING)
(mac 'FINPROD)
(ass)
(r12e-done! 'prod-ring-congruence-q)
(gloss! 'prod-ring-congruence-q
  "Products of two families that agree pointwise on the index set are
   quasi-equal.")

;;; =====================================================================
;;; (6) cra-carr / cra-op -- the two read-offs of the ADDITIVE view the
;;;     capstone's outer sum lives in.  COMMUTATIVE-RING-ADDITIVE-AG and
;;;     RING-ADDITIVE-AG are the same def-functor (`cra-is-rag'), so these
;;;     are ras-carr / ras-op one substitution away.
;;; =====================================================================
(define r12e-cra '(COMMUTATIVE-RING-ADDITIVE-AG R))
(define r12e-rag '(RING-ADDITIVE-AG R))

(sp (make-wff (r12e-tf 'R '(IS-COMMUTATIVE-RING R)
                (list '= (list 'CARR r12e-cra) '(CARR R)))))
(dk-peel!)
(dk-fact! 'commutative-ring-is-ring 'R)
(dk-fact! 'ras-carr 'R)
(dk-fact! 'cra-is-rag 'R)
(subst (list '== r12e-cra r12e-rag))
(ass)
(r12e-done! 'cra-carr)
(gloss! 'cra-carr "The carrier of a commutative ring's additive group is the ring's carrier.")

(sp (make-wff (r12e-tf 'R '(IS-COMMUTATIVE-RING R)
                (list '= (list 'OPR r12e-cra) '(ADD R)))))
(dk-peel!)
(dk-fact! 'commutative-ring-is-ring 'R)
(dk-fact! 'ras-op 'R)
(dk-fact! 'cra-is-rag 'R)
(subst (list '== r12e-cra r12e-rag))
(ass)
(r12e-done! 'cra-op)
(gloss! 'cra-op "The operation of a commutative ring's additive group is the ring's addition.")

;;; =====================================================================
;;; (7) difference-in-power -- W \ S is a subset of W.
;;; =====================================================================
(sp (make-wff '(FORALL w_ (IMPLIES (IN w_ SET)
                 (FORALL s_ (IN (DIFFERENCE w_ s_) (POWER w_)))))))
(dk-peel!)
(let* ((g  (dk-goal))
       (dw (cadr g))
       (wv (cadr dw))
       (sv (caddr dw)))
  (dk-fact! 'difference-set wv sv)
  (have! (list 'FORALL 'z_ (list 'IMPLIES (list 'IN 'z_ dw) (list 'IN 'z_ wv)))
         (lambda ()
           (let* ((zv (dk-di-var!))
                  (dm (r12e-mem-iff! (list 'IN zv dw) 'difference-membership wv sv zv)))
             (dk-only! dm (list 'IN zv dw))
             (prop))))
  (let ((pm (r12e-mem-iff! (list 'IN dw (list 'POWER wv)) 'power-set-membership wv dw)))
    (dk-only! pm (list 'IN dw 'SET)
              (list 'FORALL 'z_ (list 'IMPLIES (list 'IN 'z_ dw) (list 'IN 'z_ wv))))
    (prop)))
(r12e-done! 'difference-in-power)
(gloss! 'difference-in-power "The difference W \\ S is a subset of W.")

;; From (IN SV (POWER WV)) in context: land its sethood and its subset
;; universal, and return the two as a list.
(define (r12e-subset-univ wv sv)
  (list 'FORALL 'z (list 'IMPLIES (list 'IN 'z sv) (list 'IN 'z wv))))

(define (r12e-in-context? f)
  (any-pred (lambda (g) (alpha-equiv? g f)) (dk-asms)))

(define (r12e-power-open! wv sv)
  (let* ((pw   (list 'POWER wv))
         (sub  (r12e-subset-univ wv sv))
         (st   (list 'IN sv 'SET)))
    (if (not (and (r12e-in-context? st) (r12e-in-context? sub)))
        (let* ((pm   (r12e-mem-iff! (list 'IN sv pw) 'power-set-membership wv sv))
               (conj (list 'AND st sub)))
          (have! conj (lambda () (dk-only! pm (list 'IN sv pw)) (prop)))
          (dk-split! conj)))
    (list st sub)))

;; a conjunction both of whose conjuncts are in context, landed once
(define (r12e-and! a b)
  (let ((f (list 'AND a b)))
    (if (not (r12e-in-context? f)) (have! f))
    f))

;; The converse: (IN SV SET) and the subset universal in context, land
;; (IN SV (POWER WV)).
(define (r12e-power-close! wv sv)
  (let* ((pw  (list 'POWER wv))
         (mem (list 'IN sv pw))
         (sub (r12e-subset-univ wv sv))
         (pm  (r12e-mem-iff! mem 'power-set-membership wv sv)))
    ;; `have!' of the FOCUS GOAL is a silent self-loop, so when the membership
    ;; IS the goal, close it in place instead of opening a lane for it.
    (if (equal? (dk-goal) mem)
        (begin (dk-only! pm (list 'IN sv 'SET) sub) (prop))
        (r12e-ensure! mem (lambda () (dk-only! pm (list 'IN sv 'SET) sub) (prop))))
    mem))

;;; =====================================================================
;;; (8) prod-ring-type-subset -- the product over ANY subset of a finite
;;;     index set stays in the carrier.  This is the form every summand of
;;;     the expansion wants: the index of the inner products ranges over
;;;     POWER(W), never over W itself.
;;; =====================================================================
(define r12e-prts-stmt
  (r12e-tf 'R '(IS-COMMUTATIVE-RING R)
    (r12e-tfin 'W
      '(FORALL f (IMPLIES (FORALL z_ (IMPLIES (IN z_ W) (IN (f z_) (CARR R))))
         (FORALL s_ (IMPLIES (IN s_ (POWER W))
           (IN (PROD-RING R f s_) (CARR R)))))))))

(sp (make-wff r12e-prts-stmt))
(dk-peel!)
(let* ((g   (dk-goal))
       (pr  (cadr g))                         ; (PROD-RING R f s_)
       (rv  (cadr pr)) (fv (caddr pr)) (sv (cadddr pr))
       (inp (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'IN) (equal? (cadr f) sv)
                                      (pair? (caddr f)) (eq? (car (caddr f)) 'POWER)))
                     "s in POWER(W)"))
       (wv  (cadr (caddr inp)))
       (ptw (r12e-guarded-over wv 'IN "the pointwise typing over W"))
       (ignore (r12e-power-open! wv sv))
       (sub (r12e-subset-univ wv sv)))
  (r12e-and! (list 'IN wv 'SET) (list 'IN (list 'CARD wv) 'NN))
  (r12e-and! (list 'IN sv 'SET) sub)
  (r12e-fact! 'card-subset-nn wv sv)
  (r12e-restrict-univ! (r12e-ptw rv fv sv) ptw (lambda (zv) (dk-apply! sub zv)))
  (r12e-fact! 'prod-ring-type-ptwise rv sv fv)
  (ass))
(r12e-done! 'prod-ring-type-subset)
(gloss! 'prod-ring-type-subset
  "The product of a pointwise-typed family over any subset of a finite index
   set lies in the ring's carrier.")

;;; =====================================================================
;;; (9) prod-of-sums-summand-type -- the summand of the expansion's right
;;;     side is in the carrier, at every S in POWER(W).
;;; =====================================================================
(define r12e-pst-stmt
  (r12e-tf 'R '(IS-COMMUTATIVE-RING R)
    (r12e-tfin 'W
      '(FORALL a_ (IMPLIES (FORALL z_ (IMPLIES (IN z_ W) (IN (a_ z_) (CARR R))))
         (FORALL b_ (IMPLIES (FORALL z_ (IMPLIES (IN z_ W) (IN (b_ z_) (CARR R))))
           (FORALL s_ (IMPLIES (IN s_ (POWER W))
             (IN ((MUL R) (PROD-RING R a_ s_) (PROD-RING R b_ (DIFFERENCE W s_)))
                 (CARR R)))))))))))

(sp (make-wff r12e-pst-stmt))
(dk-peel!)
(let* ((g   (dk-goal))
       (mul (cadr g))
       (p1  (cadr mul)) (p2 (caddr mul))
       (rv  (cadr p1)) (av (caddr p1)) (sv (cadddr p1))
       (bv  (caddr p2)) (dw (cadddr p2))
       (wv  (cadr dw)))
  (r12e-fact! 'prod-ring-type-subset rv wv av sv)
  (r12e-fact! 'difference-in-power wv sv)
  (r12e-fact! 'prod-ring-type-subset rv wv bv dw)
  (dk-fact! 'commutative-ring-is-ring rv)
  (r12e-fact! 'ring-carrier-closed-mul rv p1 p2)
  (ass))
(r12e-done! 'prod-of-sums-summand-type)
(gloss! 'prod-of-sums-summand-type
  "Each term of the product-of-sums expansion lies in the ring's carrier.")

;; (NOT (IN KV SV)) from `SV subset XV' and (NOT (IN KV XV)).
(define (r12e-not-in! kv sv xv)
  (let ((form (list 'NOT (list 'IN kv sv))))
    (r12e-ensure! form
                  (lambda ()
                    (di)                           ; assume it; goal FALSITY
                    (dk-apply! (r12e-subset-univ xv sv) kv)
                    (ai (list 'NOT (list 'IN kv xv)))))
    form))

;;; =====================================================================
;;; (10) power-insert-injective -- S |-> S u {k} is an injection of POWER(X)
;;;      into POWER(X u {k}).  With `injection-image-is-bijection' this is the
;;;      bijection POWER(X) -> IMAGE(S |-> S u {k}, POWER(X)) that
;;;      finsum-reindex-ag reindexes the "contains k" half of the expansion
;;;      along.  Injectivity is `insert-remove': the map has a left inverse.
;;; =====================================================================
(define r12e-pii-stmt
  '(FORALL X (IMPLIES (IN X SET)
     (FORALL k_ (IMPLIES (IN k_ SET) (IMPLIES (NOT (IN k_ X))
       (IN (VNB-LAMBDA S (POWER X) (UNION S (PAIR k_ k_)))
           (INJECTION (POWER X) (POWER (UNION X (PAIR k_ k_)))))))))))

(sp (make-wff r12e-pii-stmt))
(dk-peel!)
(let* ((g   (dk-goal))
       (inj (caddr g))
       (pw  (cadr inj))                        ; (POWER X)
       (pwu (caddr inj))                       ; (POWER (X u {k}))
       (xv  (cadr pw))
       (u1  (cadr pwu))
       (pr  (caddr u1))
       (kv  (cadr pr)))
  (r12e-and! (list 'IN kv 'SET) (list 'IN kv 'SET))
  (dk-fact! 'pairing kv kv)
  (r12e-and! (list 'IN xv 'SET) (list 'IN pr 'SET))
  (dk-fact! 'union-set-closure xv pr)
  (dk-fact! 'power-set xv)
  (mac 'injection-membership-iff)
  (dk-conj-close!
   (lambda ()
     (if (eq? (car (dk-goal)) 'IN)
         ;; ---- the FUN typing of the insert map
         (for-each
          (lambda (leaf)
            (dk-focus! leaf)
            (if (eq? (car (dk-goal)) 'FORALL)
                (let* ((sv (dk-di-var!))
                       (su (list 'UNION sv pr)))
                  (r12e-power-open! xv sv)
                  (r12e-and! (list 'IN sv 'SET) (list 'IN pr 'SET))
                  (dk-fact! 'union-set-closure sv pr)
                  (have! (r12e-subset-univ u1 su)
                         (lambda ()
                           (let* ((zv  (dk-di-var!))
                                  (um  (r12e-mem-iff! (list 'IN zv su)
                                                      'union-membership sv pr zv))
                                  (sz  (inst*! (r12e-subset-univ xv sv) zv))
                                  (umU (r12e-mem-iff! (list 'IN zv u1)
                                                      'union-membership xv pr zv)))
                             (dk-only! um sz umU (list 'IN zv su))
                             (prop))))
                  (r12e-power-close! u1 su))
                (ass)))                        ; the sethood leaf (IN (POWER X) SET)
          (dk-opened (lambda () (lam-t))))
         ;; ---- injectivity
         (let* ((landed (dk-peel!))
                (gg  (dk-goal))                ; (= a b)
                (av  (cadr gg))
                (bv  (caddr gg))
                (eqn (dk-pick (lambda (f) (and (pair? f) (eq? (car f) '=)
                                               (pair? (cadr f)) (pair? (car (cadr f)))
                                               (eq? (car (car (cadr f))) 'VNB-LAMBDA)))
                              "the insert-map equation")))
           (r12e-power-open! xv av)
           (r12e-power-open! xv bv)
           (r12e-not-in! kv av xv)
           (r12e-not-in! kv bv xv)
           (lam-b-h eqn)
           (let ((beta (dk-pick (lambda (f) (and (pair? f) (eq? (car f) '=)
                                                 (pair? (cadr f))
                                                 (eq? (car (cadr f)) 'UNION)))
                                "the beta-reduced equation")))
             (r12e-fact! 'insert-remove av kv)
             (r12e-fact! 'insert-remove bv kv)
             (dk-fact! 'eq-sym (list 'DIFFERENCE (list 'UNION av pr) pr) av)
             (subst (list '= av (list 'DIFFERENCE (list 'UNION av pr) pr)))
             (subst beta)
             (ass)))))))
(r12e-done! 'power-insert-injective)
(gloss! 'power-insert-injective
  "For k outside X, S |-> S u {k} injects POWER(X) into POWER(X u {k}).")

;;; =====================================================================
;;; (11) lambda-eta-value -- ((z_ in D |-> ff(z_)) pt) == ff(pt), the eta
;;;      companion of `lambda-compose-value'.  The head is a VARIABLE, so the
;;;      reduction is a SINGLE contraction and the rule checker accepts it;
;;;      instantiating the head at a lambda afterwards is substitution, not
;;;      beta.  This is what reduces the eta-expanded bijection
;;;      `injection-image-is-bijection' produces.
;;; =====================================================================
(sp (make-wff
 '(FORALL ff_ (FORALL dm_ (FORALL pt_ (IMPLIES (IN pt_ dm_)
    (== ((VNB-LAMBDA z_ dm_ (ff_ z_)) pt_) (ff_ pt_))))))))
(dk-peel!)
(lam-b)
(qrfl)
(r12e-done! 'lambda-eta-value)
(gloss! 'lambda-eta-value
  "The eta-expansion of a map applied to a point of its domain is the map's
   value there.")

;;; =====================================================================
;;; (12) prod-of-sums-ptwise -- the expansion, a and b typed POINTWISE.
;;;      finite-set-induction on the index set; the class carries a and b as
;;;      BOUND variables, so the step may re-use the hypothesis at the same
;;;      two families (a pointwise typing restricts to the smaller index set,
;;;      a FUN typing would not).
;;; =====================================================================

;; the pointwise typing over DOM with a chosen binder and a chosen carrier
(define (r12e-ptw-b bnd cv fterm dom)
  (list 'FORALL bnd (list 'IMPLIES (list 'IN bnd dom)
                          (list 'IN (list fterm bnd) cv))))

(define (r12e-sum-lam rv uu)
  (list 'VNB-LAMBDA 'kv_ uu (list (list 'ADD rv) '(a_ kv_) '(b_ kv_))))

(define (r12e-term-lam rv uu)
  (list 'VNB-LAMBDA 'sv_ (list 'POWER uu)
        (list (list 'MUL rv) (list 'PROD-RING rv 'a_ 'sv_)
              (list 'PROD-RING rv 'b_ (list 'DIFFERENCE uu 'sv_)))))

(define (r12e-pos-body rv uu)
  (list 'FORALL 'a_
    (list 'IMPLIES (r12e-ptw rv 'a_ uu)
      (list 'FORALL 'b_
        (list 'IMPLIES (r12e-ptw rv 'b_ uu)
          (list '= (list 'PROD-RING rv (r12e-sum-lam rv uu) uu)
                   (list 'FINSUM (list 'COMMUTATIVE-RING-ADDITIVE-AG rv)
                         (r12e-term-lam rv uu) (list 'POWER uu))))))))

(define (r12e-cls rv) (list 'COMP 'pu_ (r12e-pos-body rv 'pu_)))

(define (r12e-step-formula rv)
  (let ((cls (r12e-cls rv)))
    (list 'FORALL 'u_
      (list 'IMPLIES (list 'AND (list 'IN 'u_ 'SET)
                           (list 'AND (list 'IN (list 'CARD 'u_) 'NN) (list 'IN 'u_ cls)))
        (list 'FORALL 'x_
          (list 'IMPLIES (list 'AND (list 'IN 'x_ 'SET) (list 'NOT (list 'IN 'x_ 'u_)))
                (list 'IN (list 'UNION 'u_ (list 'PAIR 'x_ 'x_)) cls)))))))

;;; --- the base: the index set is empty -------------------------------------
(define (r12e-base-body! rv)
  (dk-peel!)
  (let* ((ag  (list 'COMMUTATIVE-RING-ADDITIVE-AG rv))
         (one (list 'ONE rv))
         (mt  'EMPTY-SET)
         (g0  (dk-goal))
         (lhs (cadr g0))
         (lam (caddr lhs))                      ; the summand lambda over {}
         (gl  (caddr (caddr g0)))               ; the term lambda over POWER({})
         (bdy (cadddr gl))
         (av  (caddr (cadr bdy)))
         (bv  (caddr (caddr bdy))))
    (dk-fact! 'commutative-ring-is-ring rv)
    (dk-fact! 'ring-one-in rv)
    (r12e-fact! 'cra-carr rv)
    (r12e-fact! 'commutative-ring-additive-ag-is-abelian-group rv)
    (fact 'empty-set-is-set)
    (r12e-fact! 'prod-ring-empty rv lam)
    (r12e-fact! 'prod-ring-empty rv av)
    (r12e-fact! 'prod-ring-empty rv bv)
    (dk-fact! 'difference-empty-left mt)
    (dk-fact! 'power-of-empty)
    (subst (list '= (list 'POWER mt) (list 'PAIR mt mt)))
    (let* ((g1  (dk-goal))
           (rh1 (caddr g1))
           (gl1 (caddr rh1))                    ; the term lambda, domain {{}}
           (pp  (cadddr rh1)))
      (let ((pm (r12e-pairmem! mt mt)))
        (r12e-ensure! (list '= mt mt) (lambda () (rfl)))
        (r12e-ensure! (list 'IN mt pp)
                      (lambda () (dk-only! pm (list '= mt mt)) (prop))))
      (have! (list 'IN (list gl1 mt) (list 'CARR ag))
             (lambda ()
               (subst (list '= (list 'CARR ag) (list 'CARR rv)))
               (lam-b)
               (subst (list '= (list 'DIFFERENCE mt mt) mt))
               (subst (list '= (list 'PROD-RING rv av mt) one))
               (subst (list '= (list 'PROD-RING rv bv mt) one))
               (r12e-fact! 'ring-carrier-closed-mul rv one one)
               (ass)))
      (r12e-fact! 'finsum-singleton-ptwise ag mt gl1)
      (subst (list '= (list 'FINSUM ag gl1 pp) (list gl1 mt)))
      (subst (list '= lhs one))
      (lam-b)
      (subst (list '= (list 'DIFFERENCE mt mt) mt))
      (subst (list '= (list 'PROD-RING rv av mt) one))
      (subst (list '= (list 'PROD-RING rv bv mt) one))
      (r12e-fact! 'ring-mul-left-id rv one)
      (subst (list '= (list (list 'MUL rv) one one) one))
      (rfl))))

(define (r12e-base! rv)
  (for-each
   (lambda (leaf)
     (dk-focus! leaf)
     (if (eq? (car (dk-goal)) 'IN)
         (begin (fact 'empty-set-is-set) (ass))
         (r12e-base-body! rv)))
   (dk-opened (lambda () (comp-mi)))))

;;; --- the step: one fresh point k added to the index set -------------------

;; ZV is a subset of WV, WV is finite, KV lies outside WV, and FV is typed
;; pointwise over (UNION WV {KV}).  Land the insertion equation
;;   PROD-RING(R, FV, ZV u {KV}) = (MUL R)(PROD-RING(R, FV, ZV), FV(KV))
;; together with everything it needs on the way.
(define (r12e-insert-at! rv wv zv kv fv)
  (let* ((pr (list 'PAIR kv kv))
         (u1 (list 'UNION wv pr))
         (zk (list 'UNION zv pr))
         (sub (r12e-subset-univ wv zv)))
    (r12e-power-open! wv zv)
    (r12e-and! (list 'IN wv 'SET) (list 'IN (list 'CARD wv) 'NN))
    (r12e-and! (list 'IN zv 'SET) sub)
    (r12e-fact! 'card-subset-nn wv zv)
    (r12e-not-in! kv zv wv)
    (r12e-restrict-univ! (r12e-ptw rv fv zk) (r12e-ptw rv fv u1)
      (lambda (zz)
        (let* ((um  (r12e-mem-iff! (list 'IN zz zk) 'union-membership zv pr zz))
               (sz  (inst*! sub zz))
               (umU (r12e-mem-iff! (list 'IN zz u1) 'union-membership wv pr zz)))
          (r12e-ensure! (list 'IN zz u1)
                        (lambda () (dk-only! um sz umU (list 'IN zz zk)) (prop))))))
    (r12e-fact! 'prod-ring-insert-ptwise rv zv kv fv)))

;; the agreement lane for the half of POWER(u u {k}) that AVOIDS k
(define (r12e-half-b! rv uv kv av bv im zv)
  (let* ((pr  (list 'PAIR kv kv))
         (u1  (list 'UNION uv pr))
         (p0  (list 'POWER uv))
         (dd  (list 'DIFFERENCE uv zv))
         (mu  (lambda (x y) (list (list 'MUL rv) x y)))
         (aa  (list 'PROD-RING rv av zv))
         (bb  (list 'PROD-RING rv bv dd))
         (bk  (list bv kv)))
    (r12e-in-union! p0 im zv 'left)
    (r12e-power-open! uv zv)
    (r12e-not-in! kv zv uv)
    (dk-lam-b!)
    (r12e-fact! 'insert-difference-outside uv zv kv)
    (subst (list '= (list 'DIFFERENCE u1 zv) (list 'UNION dd pr)))
    (r12e-fact! 'difference-in-power uv zv)
    (r12e-insert-at! rv uv dd kv bv)
    (subst (list '= (list 'PROD-RING rv bv (list 'UNION dd pr)) (mu bb bk)))
    (r12e-fact! 'prod-ring-type-subset rv uv av zv)
    (r12e-fact! 'prod-ring-type-subset rv uv bv dd)
    (r12e-fact! 'ring-carrier-closed-mul rv bb bk)
    (r12e-fact! 'ring-mul-assoc rv aa bb bk)
    (subst (list '= (mu (mu aa bb) bk) (mu aa (mu bb bk))))
    (rfl)))

;; the agreement lane for the half that CONTAINS k, after the reindexing
(define (r12e-half-a! rv uv kv av bv lmap im gim phi rphi zv)
  (let* ((pr  (list 'PAIR kv kv))
         (u1  (list 'UNION uv pr))
         (p0  (list 'POWER uv))
         (zk  (list 'UNION zv pr))
         (dd  (list 'DIFFERENCE uv zv))
         (mu  (lambda (x y) (list (list 'MUL rv) x y)))
         (aa  (list 'PROD-RING rv av zv))
         (bb  (list 'PROD-RING rv bv dd))
         (ak  (list av kv)))
    (r12e-power-open! uv zv)
    (r12e-ensure! (list '= (list lmap zv) zk) (lambda () (lam-b) (rfl)))
    (r12e-ensure! (list 'IN zk im)
      (lambda ()
        (let* ((imi (r12e-mem-iff! (list 'IN zk im) 'image-membership-iff lmap p0 zk))
               (ex  (caddr (caddr imi))))             ; the existential conjunct of the iff's right side (2026-09-30)
          (have! ex (lambda () (ew zv) (prop)))
          (dk-have! (list 'IN zk 'SET) (lambda () (dk-sethood! zk)))
          (dk-only! imi ex (list 'IN zk 'SET))
          (prop))))
    ;; The reindexed summand is a lambda whose body applies a lambda to a
    ;; lambda's value: contracting all three redexes AT ONCE is refused by the
    ;; lambda-beta rule CHECKER (the inner application only becomes a redex
    ;; after the outer one is contracted), so the first two are done by
    ;; CITATION -- `lambda-compose-value' and `lambda-eta-value', both stated
    ;; with variable heads -- and only the last is a beta.
    (r12e-fact! 'lambda-compose-value gim phi p0 zv)
    (subst (list '== (list rphi zv) (list gim (list phi zv))))
    (r12e-fact! 'lambda-eta-value lmap p0 zv)
    (subst (list '== (list phi zv) (list lmap zv)))
    (subst (list '= (list lmap zv) zk))
    (dk-lam-b!)
    (r12e-fact! 'insert-difference-cancel uv zv kv)
    (subst (list '= (list 'DIFFERENCE u1 zk) dd))
    (r12e-insert-at! rv uv zv kv av)
    (subst (list '= (list 'PROD-RING rv av zk) (mu aa ak)))
    (r12e-fact! 'prod-ring-type-subset rv uv av zv)
    (r12e-fact! 'difference-in-power uv zv)
    (r12e-fact! 'prod-ring-type-subset rv uv bv dd)
    (r12e-fact! 'ring-mul-assoc rv aa ak bb)
    (subst (list '= (mu (mu aa ak) bb) (mu aa (mu ak bb))))
    (r12e-fact! 'commutative-ring-mul-comm rv ak bb)
    (subst (list '= (mu ak bb) (mu bb ak)))
    (r12e-fact! 'ring-mul-assoc rv aa bb ak)
    (subst (list '= (mu (mu aa bb) ak) (mu aa (mu bb ak))))
    (rfl)))

(define (r12e-step-body! rv uv kv ih)
  (dk-peel!)
  (let* ((ag    (list 'COMMUTATIVE-RING-ADDITIVE-AG rv))
         (pr    (list 'PAIR kv kv))
         (u1    (list 'UNION uv pr))
         (p0    (list 'POWER uv))
         (p1    (list 'POWER u1))
         (carrR (list 'CARR rv))
         (carrA (list 'CARR ag))
         (mu    (lambda (x y) (list (list 'MUL rv) x y)))
         (g     (dk-goal))
         (lam1  (caddr (cadr g)))                 ; the summand lambda over U1
         (gg1   (caddr (caddr g)))                ; the term lambda over POWER(U1)
         (bdy   (cadddr gg1))
         (av    (caddr (cadr bdy)))
         (bv    (caddr (caddr bdy)))
         (ptwA  (r12e-ptw rv av u1))
         (ptwB  (r12e-ptw rv bv u1)))
    (display ";; r12e step: ") (display (list uv kv av bv)) (newline)
    (dk-fact! 'commutative-ring-is-ring rv)
    (r12e-fact! 'cra-carr rv)
    (r12e-fact! 'cra-op rv)
    (r12e-fact! 'commutative-ring-additive-ag-is-abelian-group rv)
    ;; U1 is finite
    (r12e-and! (list 'IN kv 'SET) (list 'NOT (list 'IN kv uv)))
    (r12e-fact! 'card-insert uv kv)
    (dk-fact! 'ord-succ-nn (list 'CARD uv))
    (dk-fact! 'nn-succ-closed (list 'CARD uv))
    (r12e-ensure! (list 'IN (list 'CARD u1) 'NN)
      (lambda ()
        (subst (list '= (list 'CARD u1) (list 'succ_ORD (list 'CARD uv))))
        (subst (list '= (list 'succ_ORD (list 'CARD uv)) (list 'succ (list 'CARD uv))))
        (ass)))
    ;; k lies in U1
    (let ((pm (r12e-pairmem! kv kv)))
      (r12e-ensure! (list '= kv kv) (lambda () (rfl)))
      (r12e-ensure! (list 'IN kv pr) (lambda () (dk-only! pm (list '= kv kv)) (prop))))
    (r12e-in-union! uv pr kv 'right)
    (dk-apply! ptwA kv)
    (dk-apply! ptwB kv)
    ;; the typings restricted to u
    (r12e-restrict-univ! (r12e-ptw rv av uv) ptwA
                         (lambda (zz) (r12e-in-union! uv pr zz 'left)))
    (r12e-restrict-univ! (r12e-ptw rv bv uv) ptwB
                         (lambda (zz) (r12e-in-union! uv pr zz 'left)))
    ;; the two powersets are finite sets
    (dk-fact! 'power-set uv)
    (dk-fact! 'power-set u1)
    (r12e-and! (list 'IN uv 'SET) (list 'IN (list 'CARD uv) 'NN))
    (r12e-fact! 'card-power-nn uv)
    (r12e-and! (list 'IN u1 'SET) (list 'IN (list 'CARD u1) 'NN))
    (r12e-fact! 'card-power-nn u1)
    ;; ---- the left-hand side
    (let* ((ihEq (dk-apply! ih av bv))
           (lam0 (caddr (cadr ihEq)))
           (g0   (caddr (caddr ihEq)))
           (psum (caddr ihEq))
           (ak   (list av kv))
           (bk   (list bv kv)))
      (have! (r12e-ptw rv lam1 u1)
             (lambda ()
               (let ((zz (dk-di-var!)))
                 (lam-b)
                 (dk-apply! ptwA zz)
                 (dk-apply! ptwB zz)
                 (r12e-fact! 'ring-add-closed rv (list av zz) (list bv zz))
                 (ass))))
      (r12e-fact! 'prod-ring-insert-ptwise rv uv kv lam1)
      (r12e-ensure! (list '= (list lam1 kv) (list (list 'ADD rv) ak bk))
                    (lambda () (lam-b) (rfl)))
      (have! (list 'FORALL 'z_ (list 'IMPLIES (list 'IN 'z_ uv)
                                     (list '= (list lam1 'z_) (list lam0 'z_))))
             (lambda ()
               (let ((zz (dk-di-var!)))
                 (r12e-in-union! uv pr zz 'left)
                 (dk-apply! ptwA zz)
                 (dk-apply! ptwB zz)
                 (lam-b)
                 (rfl))))
      (r12e-fact! 'prod-ring-congruence-q rv uv lam1 lam0)
      ;; ---- the induction hypothesis's sum is in the carrier
      (have! (r12e-ptw-b 'zc_ carrA g0 p0)
             (lambda ()
               (let ((zz (dk-di-var!)))
                 (lam-b)
                 (subst (list '= carrA carrR))
                 (r12e-fact! 'prod-of-sums-summand-type rv uv av bv zz)
                 (ass))))
      (r12e-fact! 'finsum-type-ptwise ag p0 g0)
      (r12e-ensure! (list 'IN psum carrR)
                    (lambda () (subst (list '= carrR carrA)) (ass)))
      (r12e-fact! 'ring-left-dist rv psum ak bk)
      ;; ---- push the two constants inside the induction hypothesis's sum
      (have! (list 'IN g0 (list 'FUN p0 carrR))
             (lambda ()
               (for-each (lambda (leaf)
                           (dk-focus! leaf)
                           (if (eq? (car (dk-goal)) 'FORALL)
                               (let ((zz (dk-di-var!)))
                                 (r12e-fact! 'prod-of-sums-summand-type rv uv av bv zz)
                                 (ass))
                               (ass)))
                         (dk-opened (lambda () (lam-t))))))
      (let* ((eqDa (r12e-fact! 'finsum-ring-distrib-right rv ak p0 g0))
             (eqDb (r12e-fact! 'finsum-ring-distrib-right rv bk p0 g0))
             (ha   (caddr (caddr eqDa)))
             (hb   (caddr (caddr eqDb)))
             ;; ---- cut POWER(U1) in two
             (eqCov (r12e-fact! 'power-insert-cover uv kv))
             (un    (caddr eqCov))
             (im    (caddr un))
             (lmap  (cadr im)))
        (dk-fact! 'image-set lmap p0)
        (r12e-fact! 'card-image-finite lmap p0)
        (let ((eqDis (r12e-fact! 'power-insert-disjoint uv kv)))
          (have! (list 'FORALL 'z_ (list 'IMPLIES (list 'IN 'z_ im)
                                         (list 'NOT (list 'IN 'z_ p0))))
                 (lambda ()
                   (let* ((zz  (dk-di-var!))
                          (imi (r12e-mem-iff! (list 'IN zz (list 'INTERSECTION p0 im))
                                              'intersection-membership p0 im zz))
                          (ne  (dk-fact! 'empty-set-has-no-members zz))
                          (nin (list 'NOT (list 'IN zz (list 'INTERSECTION p0 im)))))
                     (have! nin (lambda () (subst eqDis) (ass)))
                     (dk-only! imi ne nin (list 'IN zz im))
                     (prop)))))
        ;; the goal's index set, rewritten as the union of the two halves
        (subst eqCov)
        (let* ((g2   (dk-goal))
               (gg1u (caddr (caddr g2)))          ; the term lambda, domain the union
               (gim  (list 'VNB-LAMBDA 'tv_ im
                           (list (list 'MUL rv) (list 'PROD-RING rv av 'tv_)
                                 (list 'PROD-RING rv bv (list 'DIFFERENCE u1 'tv_))))))
          (have! (r12e-ptw-b 'z_ carrA gg1u un)
                 (lambda ()
                   (let ((zz (dk-di-var!)))
                     (lam-b)
                     (subst (list '= carrA carrR))
                     (r12e-ensure! (list 'IN zz p1) (lambda () (subst eqCov) (ass)))
                     (r12e-fact! 'prod-of-sums-summand-type rv u1 av bv zz)
                     (ass))))
          (subst (r12e-fact! 'finsum-union-disjoint ag p0 im gg1u))
          ;; ---- the half that avoids k
          (have! (list 'FORALL 'zc_ (list 'IMPLIES (list 'IN 'zc_ p0)
                                        (list '= (list gg1u 'zc_) (list hb 'zc_))))
                 (lambda ()
                   (let ((zz (dk-di-var!)))
                     (r12e-half-b! rv uv kv av bv im zz))))
          (r12e-fact! 'finsum-congruence-q ag p0 gg1u hb)
          (subst (list '== (list 'FINSUM ag gg1u p0) (list 'FINSUM ag hb p0)))
          ;; ---- the half that contains k: same summand, domain the image
          (have! (list 'FORALL 'zc_ (list 'IMPLIES (list 'IN 'zc_ im)
                                        (list '= (list gg1u 'zc_) (list gim 'zc_))))
                 (lambda ()
                   (let ((zz (dk-di-var!)))
                     (r12e-in-union! p0 im zz 'right)
                     (dk-lam-b!)
                     (r12e-ensure! (list 'IN zz p1) (lambda () (subst eqCov) (ass)))
                     (r12e-fact! 'prod-of-sums-summand-type rv u1 av bv zz)
                     (r12e-fact! 'prod-ring-type-subset rv u1 av zz)
                     (r12e-fact! 'difference-in-power u1 zz)
                     (r12e-fact! 'prod-ring-type-subset rv u1 bv (list 'DIFFERENCE u1 zz))
                     (rfl))))
          (r12e-fact! 'finsum-congruence-q ag im gg1u gim)
          (subst (list '== (list 'FINSUM ag gg1u im) (list 'FINSUM ag gim im)))
          ;; ---- reindex the image half back to POWER(u)
          (r12e-fact! 'power-insert-injective uv kv)
          (let ((eqBij (r12e-fact! 'injection-image-is-bijection p0 p1 lmap)))
            (let ((phi (cadr eqBij)))
              (have! (list 'IN gim (list 'FUN im carrA))
                     (lambda ()
                       (for-each (lambda (leaf)
                                   (dk-focus! leaf)
                                   (if (eq? (car (dk-goal)) 'FORALL)
                                       (let ((zz (dk-di-var!)))
                                         (subst (list '= carrA carrR))
                                         (r12e-ensure! (list 'IN zz p1)
                                           (lambda ()
                                             (subst eqCov)
                                             (let ((um (r12e-mem-iff! (list 'IN zz un)
                                                                      'union-membership p0 im zz)))
                                               (dk-only! um (list 'IN zz im))
                                               (prop))))
                                         (r12e-fact! 'prod-of-sums-summand-type rv u1 av bv zz)
                                         (ass))
                                       (ass)))
                                 (dk-opened (lambda () (lam-t))))))
              (r12e-and! (list 'IN p0 'SET) (list 'IN (list 'CARD p0) 'NN))
              (let* ((eqRe (r12e-fact! 'finsum-reindex-ag ag im p0 phi gim))
                     (rphi (caddr (caddr eqRe))))
                (subst eqRe)
                (have! (list 'FORALL 'zc_ (list 'IMPLIES (list 'IN 'zc_ p0)
                                              (list '= (list rphi 'zc_) (list ha 'zc_))))
                       (lambda ()
                         (let ((zz (dk-di-var!)))
                           (r12e-half-a! rv uv kv av bv lmap im gim phi rphi zz))))
                (r12e-fact! 'finsum-congruence-q ag p0 rphi ha)
                (subst (list '== (list 'FINSUM ag rphi p0) (list 'FINSUM ag ha p0)))
                ;; ---- put the constants back outside, and finish
                (subst (list '= (list 'FINSUM ag ha p0) (mu psum ak)))
                (subst (list '= (list 'FINSUM ag hb p0) (mu psum bk)))
                (subst (list '= (list 'OPR ag) (list 'ADD rv)))
                ;; the split puts the k-AVOIDING half (the b factor) first, so
                ;; the two summands come in the opposite order to ring-left-dist's
                (r12e-fact! 'ring-carrier-closed-mul rv psum ak)
                (r12e-fact! 'ring-carrier-closed-mul rv psum bk)
                (r12e-fact! 'ring-add-comm rv (mu psum bk) (mu psum ak))
                (subst (list '= (list (list 'ADD rv) (mu psum bk) (mu psum ak))
                             (list (list 'ADD rv) (mu psum ak) (mu psum bk))))
                (subst (list '= (list (list 'ADD rv) (mu psum ak) (mu psum bk))
                             (mu psum (list (list 'ADD rv) ak bk))))
                (subst (list '= (list 'PROD-RING rv lam1 u1)
                             (mu (list 'PROD-RING rv lam1 uv) (list lam1 kv))))
                (subst (list '== (list 'PROD-RING rv lam1 uv) (list 'PROD-RING rv lam0 uv)))
                (subst ihEq)
                (subst (list '= (list lam1 kv) (list (list 'ADD rv) ak bk)))
                (rfl)))))))))

(define (r12e-step! rv)
  (let ((cls (r12e-cls rv)))
    (dk-split-all! (dk-peel!))
    (let* ((g  (dk-goal))
           (u1 (cadr g))
           (uv (cadr u1))
           (pr (caddr u1))
           (kv (cadr pr))
           (ih (dk-landed-find (lambda () (comp-me (list 'IN uv cls)))
                               (dk-head? 'FORALL))))
      (r12e-and! (list 'IN kv 'SET) (list 'IN kv 'SET))
      (dk-fact! 'pairing kv kv)
      (r12e-and! (list 'IN uv 'SET) (list 'IN pr 'SET))
      (dk-fact! 'union-set-closure uv pr)
      (for-each
       (lambda (leaf)
         (dk-focus! leaf)
         (if (eq? (car (dk-goal)) 'IN)
             (ass)
             (r12e-step-body! rv uv kv ih)))
       (dk-opened (lambda () (comp-mi)))))))

(sp (make-wff (r12e-tf 'R '(IS-COMMUTATIVE-RING R) (r12e-tfin 'W (r12e-pos-body 'R 'W)))))
(di)                                    ; the binder
(di)                                    ; the guard -- not a typing
(let* ((rv  (cadr (dk-pick (dk-head? 'IS-COMMUTATIVE-RING) "the ring")))
       (cls (r12e-cls rv))
       (stp (r12e-step-formula rv)))
  (have! (list 'IN 'EMPTY-SET cls) (lambda () (r12e-base! rv)))
  (have! stp (lambda () (r12e-step! rv)))
  (r12e-and! (list 'IN 'EMPTY-SET cls) stp)
  (let ((ind (dk-fact! 'finite-set-induction cls)))
    (dk-peel!)
    (let* ((g   (dk-goal))
           (wv  (cadddr (cadr g)))
           (bdy (cadddr (caddr (caddr g))))
           (av  (caddr (cadr bdy)))
           (bv  (caddr (caddr bdy))))
      (r12e-and! (list 'IN wv 'SET) (list 'IN (list 'CARD wv) 'NN))
      (let* ((inW  (dk-apply! ind wv))
             (body (dk-landed-find (lambda () (comp-me inW)) (dk-head? 'FORALL))))
        (dk-apply! body av bv)
        (ass)))))
(r12e-done! 'prod-of-sums-ptwise)
(gloss! 'prod-of-sums-ptwise
  "The product-of-sums expansion with the two families typed POINTWISE on the
   index set -- the form an induction on the index set can use.")

;;; =====================================================================
;;; (13) prod-of-sums-expansion -- the capstone, the statement copied
;;;      LITERALLY from theorem-library/prod-of-sums.scm:137.  A FUN typing
;;;      gives the pointwise one by `fun-apply-type-c', and (12) is the proof.
;;; =====================================================================
(sp (make-wff
 '(FORALL R (IMPLIES (IS-COMMUTATIVE-RING R)
     (FORALL X (IMPLIES (AND (IN X SET) (IN (CARD X) NN))
     (FORALL a (IMPLIES (IN a (FUN X (CARR R)))
     (FORALL b (IMPLIES (IN b (FUN X (CARR R)))
       (= (PROD-RING R (VNB-LAMBDA k X ((ADD R) (a k) (b k))) X)
          (FINSUM (COMMUTATIVE-RING-ADDITIVE-AG R)
                  (VNB-LAMBDA S (POWER X) ((MUL R) (PROD-RING R a S)
                                         (PROD-RING R b (DIFFERENCE X S))))
                  (POWER X)))))))))))))
(dk-peel!)
(dk-split-all!)
(let* ((g   (dk-goal))
       (lhs (cadr g))
       (rv  (cadr lhs))
       (xv  (cadddr lhs))
       (bdy (cadddr (caddr (caddr g))))
       (av  (caddr (cadr bdy)))
       (bv  (caddr (caddr bdy)))
       (ca  (list 'CARR rv)))
  (have! (r12e-ptw rv av xv)
         (lambda () (let ((zz (dk-di-var!)))
                      (r12e-fact! 'fun-apply-type-c av xv ca zz)
                      (ass))))
  (have! (r12e-ptw rv bv xv)
         (lambda () (let ((zz (dk-di-var!)))
                      (r12e-fact! 'fun-apply-type-c bv xv ca zz)
                      (ass))))
  (r12e-fact! 'prod-of-sums-ptwise rv xv av bv)
  (ass))
(r12e-done! 'prod-of-sums-expansion)
(gloss! 'prod-of-sums-expansion
  "The product over a finite index set X of the pointwise sums a(k) + b(k) is
   the sum, over all subsets S of X, of (prod_S a) * (prod_{X\\S} b).")
