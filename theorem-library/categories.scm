;;; categories.scm -- FOUR CATEGORIES BESIDE THE DEFAULTS: Lipschitz, uniformly
;;; continuous and continuous maps of metric spaces, bounded linear maps of
;;; normed vector spaces; their laws, their Hom functors, and the inclusions.
;;;
;;; Batch 39 (2026-09-28).  The user's notes-43: "there is a DEFAULT category
;;; corresponding to a structure (in most cases very restrictive) but it would
;;; allow us to define alternatives to the default, like the Lipschitz category or
;;; the continuous category."  docs/categories-per-structure-2026-09-28.md is the
;;; design; structures.scm's `declare-category!' is the mechanism.  The default
;;; of METRIC-SPACE (IS-HOM-METRIC-SPACE, the isometries) and of
;;; NORMED-VECTOR-SPACE (linear and norm-preserving) are untouched.
;;;
;;; For each category CAT on structure X, declare-category! installs (definitional)
;;; the arrow predicate IS-CAT-ARROW(a, b, f) := IS-X(a) and IS-X(b) and
;;; f in FUN(C a, C b) and BODY, and the hom-set HOM-CAT(a, b), and records the
;;; OBLIGATIONS hom-CAT-id, hom-CAT-compose, hom-CAT-in-set, which this file
;;; PROVES (category-obligations-audit lists the ones that are not).  Also here:
;;;
;;;   hom-CAT-member-iff            the SEP's membership (generic)
;;;   hom-CAT-post-type / -pre-type the Hom functors Hom(a, -), Hom(-, b) on the
;;;                                 hom-sets (hom-functors.scm's driver, copied)
;;;   the INCLUSIONS, arrow-wise and as hom-sets:
;;;     isometry => Lipschitz (K = 1) => uniformly continuous (delta = eps/(K+1))
;;;       => continuous (uniformly-continuous-is-continuous);
;;;     linear isometry => bounded linear (K = 1).
;;;   The identity laws are read off the inclusions: the identity is an isometry
;;;   (hom-metric-space-id), hence Lipschitz, hence ...; a linear isometry
;;;   (hom-normed-vector-space-id), hence bounded linear.
;;;
;;; Nothing is asserted; every qed is expected modulo 0.  Prefix `cat-'.

;;; =======================================================================
;;; The four categories.
;;; =======================================================================

;;; LIPSCHITZ: forsome K in RR, 0 <= K and d_b(f x, f y) <= K d_a(x, y).
(declare-category! 'LIPSCHITZ 'METRIC-SPACE '(a b f)
  '(FORSOME lpk_ (AND (IN lpk_ RR) (AND (<= 0 lpk_)
     (FORALL lpx_ (IMPLIES (IN lpx_ (PTS a))
       (FORALL lpy_ (IMPLIES (IN lpy_ (PTS a))
         (<= ((DIST b) (f lpx_) (f lpy_)) (* lpk_ ((DIST a) lpx_ lpy_)))))))))))

;;; UNIFORMLY-CONTINUOUS and CONTINUOUS: the tree's own predicates
;;; (metric-continuity.scm), not restated.
(declare-category! 'UNIFORMLY-CONTINUOUS 'METRIC-SPACE '(a b f)
  '(IS-UNIFORMLY-CONTINUOUS a b f))
(declare-category! 'CONTINUOUS 'METRIC-SPACE '(a b f)
  '(IS-CONTINUOUS a b f))

;;; BOUNDED-LINEAR: over the same scalars (the default hom's convention), additive,
;;; homogeneous -- the clauses spelled exactly as the generated
;;; IS-HOM-NORMED-VECTOR-SPACE spells them, binders x1_ x2_ included -- and bounded.
(declare-category! 'BOUNDED-LINEAR 'NORMED-VECTOR-SPACE '(a b f)
  '(AND (= (SCAL a) (SCAL b))
    (AND (FORALL x1_ (IMPLIES (IN x1_ (VEC a)) (FORALL x2_ (IMPLIES (IN x2_ (VEC a))
           (= (f ((VADD a) x1_ x2_)) ((VADD b) (f x1_) (f x2_)))))))
    (AND (FORALL x1_ (IMPLIES (IN x1_ (CARR (SCAL a))) (FORALL x2_ (IMPLIES (IN x2_ (VEC a))
           (= (f ((ACT a) x1_ x2_)) ((ACT b) x1_ (f x2_)))))))
         (FORSOME blk_ (AND (IN blk_ RR) (AND (<= 0 blk_)
           (FORALL x1_ (IMPLIES (IN x1_ (VEC a))
             (<= ((VNRM b) (f x1_)) (* blk_ ((VNRM a) x1_))))))))))))

(notation! 'IS-LIPSCHITZ-ARROW 'kind 'predicate 'arity 3
           'english "$3 is a Lipschitz map from $1 to $2")
(notation! 'HOM-LIPSCHITZ 'kind 'functoid 'arity 2
           'english "the Lipschitz maps from $1 to $2")

;;; =======================================================================
;;; Helpers.
;;; =======================================================================

(define (cat-ctx f who)
  (or (dk-ctx-form f) (error "categories: not in context --" who (expression->string f))))
(define (cat-done! name)
  (if (proof-done? *ps*) (qed name) (error "categories: failed to prove" name)))
(define (cat-inst thm . terms)
  (let loop ((f (lookup-theorem thm)) (ts terms))
    (if (null? ts) f
        (loop (subst-free (quantifier-var f) (car ts) (quantifier-body f)) (cdr ts)))))
(define (cat-conjuncts f)
  (if (dk-head-is? f 'AND)
      (append (cat-conjuncts (cadr f)) (cat-conjuncts (caddr f)))
      (list f)))
(define (cat-and fs)
  (if (null? (cdr fs)) (car fs) (list 'AND (car fs) (cat-and (cdr fs)))))
(define (cat-contains? e sub) (dk-contains? e sub))
(define (cat-find what pred) (dk-pick pred what))

(define (cat-arrow cat) (category-arrow-name cat))
(define (cat-arrow-def cat) (category-arrow-def-name cat))
(define (cat-hs cat) (category-hom-set-name cat))
(define (cat-thm cat suffix) (symbol-append 'hom- cat suffix))
(define (cat-x cat) (category-structure cat))
(define (cat-isx cat) (symbol-append 'IS- (cat-x cat)))
(define (cat-carrier cat) (car (category--carriers (cat-x cat))))

;;; The points of an inner estimate, read off the GOAL (never off the order in
;;; which `dk-peel!' reports its landings):
;;;   (<= LHS (* K ((D v) x y)))  -> (x y)        cat-rhs-points
;;;   (<= ((D v) (F x) (F y)) R)  -> (x y)        cat-lhs-points
(define (cat-rhs-points g) (let ((d (caddr (caddr g)))) (cdr d)))
(define (cat-lhs-points g) (let ((d (cadr g))) (list (cadr (cadr d)) (cadr (caddr d)))))

;;; the slot typings of IS-X(v), X a shape structure, landed on a lane
(define (cat-land-typings! x v)
  (let* ((isx  (symbol-append 'IS- x))
         (accs (map car (structure-def-slots (lookup-structure x))))
         (ts   (filter (lambda (c) (and (dk-head-is? c 'IN) (pair? (cadr c)) (= (length (cadr c)) 2)
                                        (memq (car (cadr c)) accs) (equal? (cadr (cadr c)) v)
                                        (not (dk-asm? c))))
                       (cat-conjuncts (caddr (cat-inst isx v))))))
    (if (pair? ts)
        (let ((conj (cat-and ts)))
          (dk-have! conj
            (lambda ()
              (mac-h isx (cat-ctx (list isx v) "IS-X"))
              (dk-split-all!)
              (dk-conj-close!)))
          (if (pair? (cdr ts)) (dk-split-all! (list (cat-ctx conj "typings"))))))))

;;; detach every antecedent of the chain CH, proving each (conjunctive or not)
;;; from the context
(define (cat-detach-all! ch)
  (let loop ((r ch))
    (if (and (pair? r) (eq? (car r) 'IMPLIES))
        (loop (if (dk-asm? (cadr r))
                  (dk-landed-1 (lambda () (detach! r)))
                  (detach-with! r (lambda () (dk-conj-close!)))))
        r)))
(define (cat-cite! thm . args) (cat-detach-all! (apply dk-cite! thm args)))

;;; the FUN typing of the operation OPV in context, or #f
(define (cat-op-typing opv)
  (find-first (lambda (f) (and (dk-head-is? f 'IN) (equal? (cadr f) opv)
                               (dk-head-is? (caddr f) 'FUN) (= (length (caddr f)) 3)))
              (dk-asms)))

;;; type the applied operation T = ((OP v) x ...) in its range, the arguments
;;; typed in context (hom-laws.scm's hml-op-type!)
(define (cat-op-type! t)
  (let* ((opv  (car t)) (args (cdr t))
         (ty   (or (cat-op-typing opv) (error "cat-op-type!: no FUN typing for" (expression->string opv))))
         (dom  (cadr (caddr ty))) (rng (caddr (caddr ty)))
         (goal (list 'IN t rng)))
    (cond ((dk-asm? goal) (dk-ctx-form goal))
          ((= (length args) 1) (dk-cite! 'fun-apply-type-c opv dom rng (car args)))
          ((= (length args) 2)
           (let ((lst (list 'LIST (car args) (cadr args))))
             (dk-have! goal
               (lambda ()
                 (fact 'apply-tupling-2 opv (car args) (cadr args))
                 (subst (list '== t (list opv lst)))
                 (fact 'pair-in-cartesian (cadr dom) (caddr dom) (car args) (cadr args))
                 (fact 'fun-apply-type-c opv dom rng lst)
                 (ass)))
             (cat-ctx goal "op typing")))
          (#t (error "cat-op-type!: arity" (expression->string t))))))

;;; open the arrow hypothesis ARROW(x, y, f) in context: its conjuncts land
(define (cat-open-arrow! cat hyp)
  (mac-h (cat-arrow-def cat) hyp)
  (dk-split-all!))

;;; the chain  LHS <= K2 * MID,  MID <= K1 * BASE,  0 <= K2  (all in context)
;;; ==>  LHS <= (K2 * K1) * BASE, the terms typed in RR first
(define (cat-scale-chain! lhs mid base k2 k1)
  (let* ((k1b  (list '* k1 base))
         (k2m  (list '* k2 mid))
         (k2kb (list '* k2 k1b))
         (kk   (list '* k2 k1))
         (rhs  (list '* kk base)))
    (for-each dk-real! (list lhs mid base k1 k2 k1b k2m k2kb kk rhs))
    (cat-cite! 'rr-le-scale-nonneg k2 mid k1b)                 ; k2 mid <= k2 (k1 base)
    (dk-have! (list '= k2kb rhs) (lambda () (crs)))           ; = (k2 k1) base
    (dk-le-chain! lhs k2m k2kb rhs)))

;;; =======================================================================
;;; Membership and sethood: generic (they see only the predicate).
;;; =======================================================================

(define (cat-prove-member-iff! cat)
  (sp (make-wff (category-member-iff cat)))
  (dk-peel!)
  (mac (cat-hs cat))
  (for-each
    (lambda (lf)
      (dk-focus! lf)
      (if (dk-head-is? (dk-goal) 'AND)
          (begin
            (sep-me (dk-pick (lambda (x) (and (dk-head-is? x 'IN) (dk-head-is? (caddr x) 'SEP)))
                             "the SEP membership"))
            (dk-conj-close!))
          (begin
            (dk-split-all!)
            (in-sep! (lambda () (ass)) (lambda () (ass))))))
    (dk-opened (lambda () (di))))
  (cat-done! (cat-thm cat '-member-iff)))

(define (cat-prove-in-set! cat)
  (sp (category-obligation (cat-thm cat '-in-set)))
  (dk-peel!)
  (let* ((hs (cadr (dk-goal))) (va (cadr hs)) (vb (caddr hs)))
    (cat-land-typings! (cat-x cat) va)
    (cat-land-typings! (cat-x cat) vb)
    (mac (cat-hs cat))
    (sep-set)
    (mac 'fun-set-iff)
    (dk-conj-close!)
    (cat-done! (cat-thm cat '-in-set))))

(for-each (lambda (cat) (cat-prove-member-iff! cat) (cat-prove-in-set! cat))
          '(LIPSCHITZ UNIFORMLY-CONTINUOUS CONTINUOUS BOUNDED-LINEAR))

;;; =======================================================================
;;; The inclusions, arrow by arrow.
;;; =======================================================================

;;; --- an isometry is 1-Lipschitz --------------------------------------------
(sp (make-wff '(FORALL a (FORALL b (FORALL f
       (IMPLIES (IS-HOM-METRIC-SPACE a b f) (IS-LIPSCHITZ-ARROW a b f)))))))
(dk-peel!)
(let* ((gl (dk-goal)) (va (cadr gl)) (vb (caddr gl)) (vf (cadddr gl))
       (hconj (cat-conjuncts (caddr (cat-inst 'IS-HOM-METRIC-SPACE-def va vb vf))))
       (iso (list-ref hconj (- (length hconj) 1))))
  (mac-h 'IS-HOM-METRIC-SPACE-def (cat-ctx (list 'IS-HOM-METRIC-SPACE va vb vf) "the isometry"))
  (dk-split-all!)
  (mac 'is-lipschitz-arrow-def)
  (dk-conj-close!
    (lambda ()
      (let ((g (dk-goal)))
        (cond ((dk-asm? g) (ass))
              ((dk-head-is? g 'FORSOME)
               (ew 1)
               (dk-conj-close!
                 (lambda ()
                   (let ((g2 (dk-goal)))
                     (cond ((dk-head-is? g2 'FORALL)
                            (let* ((landed (dk-peel!))
                                   (pts (cat-rhs-points (dk-goal)))
                                   (x (car pts)) (y (cadr pts))
                                   (e (dk-apply! (cat-ctx iso "iso clause") x y))
                                   (da (cadr e)) (db (caddr e)))
                              (dk-cite! 'metric-dist-real va x y)
                              (subst (list '= db da))
                              (dk-ineq! (list 'IN da 'RR))))
                           ((dk-head-is? g2 '<=) (dk-ineq!))
                           (#t (from-context!)))))))
              (#t (error "isometry => Lipschitz: unexpected conjunct" (expression->string g))))))))
(cat-done! 'hom-metric-space-is-lipschitz-arrow)

;;; --- a K-Lipschitz map is uniformly continuous: delta = eps / (K + 1) ---------
(sp (make-wff '(FORALL a (FORALL b (FORALL f
       (IMPLIES (IS-LIPSCHITZ-ARROW a b f) (IS-UNIFORMLY-CONTINUOUS-ARROW a b f)))))))
(dk-peel!)
(let* ((gl (dk-goal)) (va (cadr gl)) (vb (caddr gl)) (vf (cadddr gl))
       (pa (list 'PTS va)) (pb (list 'PTS vb)))
  (cat-open-arrow! 'LIPSCHITZ (cat-ctx (list 'IS-LIPSCHITZ-ARROW va vb vf) "the Lipschitz arrow"))
  (let* ((ex (cat-find "the Lipschitz constant" (lambda (x) (dk-head-is? x 'FORSOME))))
         (k  (dk-skolem! ex))
         (lip (cat-find "the Lipschitz estimate"
                (lambda (x) (and (dk-head-is? x 'FORALL) (cat-contains? x k))))))
    (mac 'is-uniformly-continuous-arrow-def)
    (dk-conj-close!
      (lambda ()
        (let ((g (dk-goal)))
          (cond
            ((dk-asm? g) (ass))
            ((dk-head-is? g 'IS-UNIFORMLY-CONTINUOUS)
             (mac 'is-uniformly-continuous)
             (dk-conj-close!
               (lambda ()
                 (if (dk-asm? (dk-goal))
                     (ass)
                     (let* ((landed (dk-peel!))                ; POS-RR(eps)
                            (eps (cadr (car landed)))
                            (m   (list '+ k 1))
                            (r   (list 'recip m))
                            (d   (list '* eps r)))
                       (dk-cite! 'rr-pos-rr-in-rr eps)
                       (dk-cite! 'rr-lt-of-pos-rr eps)
                       (dk-real! m)
                       (dk-have! (list '< 0 m) (lambda () (dk-ineq! (list '<= 0 k) (list 'IN k 'RR))))
                       (dk-have! (list '<= k m) (lambda () (dk-ineq! (list 'IN k 'RR))))
                       (cat-cite! 'rr-pos-ne-zero m)
                       (cat-cite! 'rr-recip-closed m)
                       (cat-cite! 'rr-recip-pos m)
                       (cat-cite! 'rr-recip-inverse m)       ; m * r = 1
                       (cat-cite! 'rr-mul-pos eps r)          ; 0 < eps * r
                       (dk-real! d)
                       (cat-cite! 'rr-pos-rr-of-lt d)
                       ;; m * (eps * r) = eps
                       (dk-have! (list '= (list '* m d) eps)
                         (lambda ()
                           (dk-have! (list '= (list '* m d) (list '* eps (list '* m r)))
                                     (lambda () (dk-crs-opaque!)))
                           (subst (list '= (list '* m d) (list '* eps (list '* m r))))
                           (subst (list '= (list '* m r) 1))
                           (crs)))
                       (ew d)
                       (dk-conj-close!
                         (lambda ()
                           (if (dk-asm? (dk-goal))
                               (ass)
                               (let* ((ls (dk-peel!))
                                      (pts (cat-lhs-points (dk-goal)))
                                      (x (car pts)) (y (cadr pts))
                                      (da (list (list 'DIST va) x y))
                                      (fx (list vf x)) (fy (list vf y))
                                      (db (list (list 'DIST vb) fx fy)))
                                 (dk-cite! 'metric-dist-real va x y)
                                 (dk-cite! 'metric-pos va x y)
                                 (dk-cite! 'fun-apply-type-c vf pa pb x)
                                 (dk-cite! 'fun-apply-type-c vf pa pb y)
                                 (dk-cite! 'metric-dist-real vb fx fy)
                                 (dk-apply! (cat-ctx lip "Lipschitz estimate") x y)   ; db <= k da
                                 (cat-cite! 'rr-prod-le-prod k m da d)                  ; k da <= m d
                                 (dk-le-chain! db (list '* k da) (list '* m d) eps))))))))))
            (#t (error "Lipschitz => UC: unexpected conjunct" (expression->string g))))))))
  (cat-done! 'lipschitz-arrow-is-uniformly-continuous-arrow))

;;; --- a uniformly continuous map is continuous ---------------------------------
(sp (make-wff '(FORALL a (FORALL b (FORALL f
       (IMPLIES (IS-UNIFORMLY-CONTINUOUS-ARROW a b f) (IS-CONTINUOUS-ARROW a b f)))))))
(dk-peel!)
(let* ((gl (dk-goal)) (va (cadr gl)) (vb (caddr gl)) (vf (cadddr gl)))
  (cat-open-arrow! 'UNIFORMLY-CONTINUOUS
    (cat-ctx (list 'IS-UNIFORMLY-CONTINUOUS-ARROW va vb vf) "the UC arrow"))
  (dk-cite! 'uniformly-continuous-is-continuous va vb vf)
  (mac 'is-continuous-arrow-def)
  (dk-conj-close! (lambda () (ass))))
(cat-done! 'uniformly-continuous-arrow-is-continuous-arrow)

;;; --- a linear isometry is bounded linear (K = 1) --------------------------------
(sp (make-wff '(FORALL a (FORALL b (FORALL f
       (IMPLIES (IS-HOM-NORMED-VECTOR-SPACE a b f) (IS-BOUNDED-LINEAR-ARROW a b f)))))))
(dk-peel!)
(let* ((gl (dk-goal)) (va (cadr gl)) (vb (caddr gl)) (vf (cadddr gl))
       (hconj (cat-conjuncts (caddr (cat-inst 'IS-HOM-NORMED-VECTOR-SPACE-def va vb vf))))
       (nrm (list-ref hconj (- (length hconj) 1))))
  (mac-h 'IS-HOM-NORMED-VECTOR-SPACE-def
         (cat-ctx (list 'IS-HOM-NORMED-VECTOR-SPACE va vb vf) "the linear isometry"))
  (dk-split-all!)
  (cat-land-typings! 'NORMED-VECTOR-SPACE va)
  (mac 'is-bounded-linear-arrow-def)
  (dk-conj-close!
    (lambda ()
      (let ((g (dk-goal)))
        (cond ((dk-asm? g) (ass))
              ((dk-head-is? g 'FORSOME)
               (ew 1)
               (dk-conj-close!
                 (lambda ()
                   (let ((g2 (dk-goal)))
                     (cond ((dk-head-is? g2 'FORALL)
                            (let* ((landed (dk-peel!))
                                   (x (car (cat-rhs-points (dk-goal))))
                                   (e (dk-apply! (cat-ctx nrm "norm clause") x))
                                   (na (cadr e)) (nb (caddr e)))
                              (cat-op-type! na)
                              (subst (list '= nb na))
                              (dk-ineq! (list 'IN na 'RR))))
                           ((dk-head-is? g2 '<=) (dk-ineq!))
                           (#t (from-context!)))))))
              (#t (error "linear isometry => bounded linear: unexpected conjunct"
                         (expression->string g))))))))
(cat-done! 'hom-normed-vector-space-is-bounded-linear-arrow)

;;; =======================================================================
;;; The identities: read off the inclusions.
;;; =======================================================================

(define (cat-prove-id-by-inclusion! cat prev-id incl)
  (sp (category-obligation (cat-thm cat '-id)))
  (dk-peel!)
  (let* ((gl (dk-goal)) (v (cadr gl)) (idf (cadddr gl)))
    (dk-cite! prev-id v)
    (dk-cite! incl v v idf)
    (ass))
  (cat-done! (cat-thm cat '-id)))

(cat-prove-id-by-inclusion! 'LIPSCHITZ 'hom-metric-space-id 'hom-metric-space-is-lipschitz-arrow)
(cat-prove-id-by-inclusion! 'UNIFORMLY-CONTINUOUS 'hom-lipschitz-id
                            'lipschitz-arrow-is-uniformly-continuous-arrow)
(cat-prove-id-by-inclusion! 'CONTINUOUS 'hom-uniformly-continuous-id
                            'uniformly-continuous-arrow-is-continuous-arrow)
(cat-prove-id-by-inclusion! 'BOUNDED-LINEAR 'hom-normed-vector-space-id
                            'hom-normed-vector-space-is-bounded-linear-arrow)

;;; =======================================================================
;;; Composition.
;;; =======================================================================

;;; the common head: peel, read the objects and maps off the goal, open both
;;; arrows, type the composite and land its beta law.  Returns
;;; (va vb vc vf vg cu) with CU = compose-apply's universal for this composite.
(define (cat-compose-head! cat . pre)
  (sp (category-obligation (cat-thm cat '-compose)))
  (dk-peel!)
  (let* ((arrow (cat-arrow cat))
         (gl (dk-goal)) (va (cadr gl)) (vc (caddr gl)) (gf (cadddr gl))
         (vg (cadr gf)) (vf (caddr gf))
         (hf (dk-pick (lambda (x) (and (dk-head-is? x arrow) (equal? (cadddr x) vf))) "the f arrow"))
         (vb (caddr hf))
         (hg (cat-ctx (list arrow vb vc vg) "the g arrow"))
         (c  (cat-carrier cat))
         (ca (list c va)) (cb (list c vb)) (cc (list c vc)))
    (cat-open-arrow! cat hf)
    (cat-open-arrow! cat hg)
    (cat-land-typings! (cat-x cat) va)
    (cat-land-typings! (cat-x cat) vb)
    (cat-land-typings! (cat-x cat) vc)
    (dk-have! (list 'AND (list 'IN vf (list 'FUN ca cb)) (list 'IN vg (list 'FUN cb cc))))
    (dk-cite! 'compose-type ca cb cc vg vf)
    (let ((cu (dk-cite! 'compose-apply ca cb cc vg vf)))
      ;; PRE, if given, runs on the hypotheses BEFORE the goal is unfolded (the
      ;; bounded-linear skolems: see there)
      (let ((extra (if (pair? pre) ((car pre) va vb vc vf vg) '())))
        (mac (cat-arrow-def cat))
        (append (list va vb vc vf vg cu) extra)))))

;;; --- Lipschitz: the constants multiply ------------------------------------------
(let* ((h (cat-compose-head! 'LIPSCHITZ))
       (va (list-ref h 0)) (vb (list-ref h 1)) (vc (list-ref h 2))
       (vf (list-ref h 3)) (vg (list-ref h 4)) (cu (list-ref h 5))
       (pa (list 'PTS va)) (pb (list 'PTS vb)) (pc (list 'PTS vc))
       (exf (cat-find "f's constant" (lambda (x) (and (dk-head-is? x 'FORSOME) (cat-contains? x vf)))))
       (exg (cat-find "g's constant" (lambda (x) (and (dk-head-is? x 'FORSOME) (cat-contains? x vg)))))
       (k1 (dk-skolem! exf))
       (k2 (dk-skolem! exg))
       (lf (cat-find "f's estimate" (lambda (x) (and (dk-head-is? x 'FORALL) (cat-contains? x k1)))))
       (lg (cat-find "g's estimate" (lambda (x) (and (dk-head-is? x 'FORALL) (cat-contains? x k2)))))
       (kk (list '* k2 k1)))
  (dk-conj-close!
    (lambda ()
      (let ((g (dk-goal)))
        (cond
          ((dk-asm? g) (ass))
          ((dk-head-is? g 'FORSOME)
           (ew kk)
           (dk-conj-close!
             (lambda ()
               (let ((g2 (dk-goal)))
                 (cond
                   ((dk-head-is? g2 'IN) (dk-real! kk))
                   ((dk-head-is? g2 '<=) (cat-cite! 'rr-leq-mul-nonneg k2 k1) (ass))
                   (#t
                    (let* ((ls (dk-peel!))
                           (pts (cat-rhs-points (dk-goal)))
                           (x (car pts)) (y (cadr pts))
                           (fx (list vf x)) (fy (list vf y))
                           (da (list (list 'DIST va) x y))
                           (db (list (list 'DIST vb) fx fy))
                           (dc (list (list 'DIST vc) (list vg fx) (list vg fy))))
                      (subst (dk-apply! cu x))
                      (subst (dk-apply! cu y))
                      (dk-cite! 'fun-apply-type-c vf pa pb x)
                      (dk-cite! 'fun-apply-type-c vf pa pb y)
                      (dk-cite! 'fun-apply-type-c vg pb pc fx)
                      (dk-cite! 'fun-apply-type-c vg pb pc fy)
                      (dk-cite! 'metric-dist-real va x y)
                      (dk-cite! 'metric-dist-real vb fx fy)
                      (dk-cite! 'metric-dist-real vc (list vg fx) (list vg fy))
                      (dk-apply! (cat-ctx lf "f's estimate") x y)
                      (dk-apply! (cat-ctx lg "g's estimate") fx fy)
                      (cat-scale-chain! dc db da k2 k1))))))))
          (#t (error "Lipschitz compose: unexpected conjunct" (expression->string g))))))))
(cat-done! 'hom-lipschitz-compose)

;;; --- uniform continuity: the eps-delta chase ----------------------------------
;;; Given eps, g's delta d1 for eps, then f's delta d2 for d1: points within d2
;;; go to points within d1, which go to points within eps.  (continuity-compose.scm
;;; is the pointwise twin.)  The two eps-universals are told apart by the map
;;; they mention; the two delta-universals by their delta.
(let* ((h (cat-compose-head! 'UNIFORMLY-CONTINUOUS))
       (va (list-ref h 0)) (vb (list-ref h 1)) (vc (list-ref h 2))
       (vf (list-ref h 3)) (vg (list-ref h 4)) (cu (list-ref h 5))
       (pa (list 'PTS va)) (pb (list 'PTS vb)))
  (mac-h 'is-uniformly-continuous (cat-ctx (list 'IS-UNIFORMLY-CONTINUOUS va vb vf) "f UC"))
  (dk-split-all!)
  (mac-h 'is-uniformly-continuous (cat-ctx (list 'IS-UNIFORMLY-CONTINUOUS vb vc vg) "g UC"))
  (dk-split-all!)
  (let ((uf (cat-find "f's eps-universal"
              (lambda (x) (and (dk-head-is? x 'FORALL) (cat-contains? x 'POS-RR)
                               (cat-contains? x vf) (not (cat-contains? x vg))))))
        (ug (cat-find "g's eps-universal"
              (lambda (x) (and (dk-head-is? x 'FORALL) (cat-contains? x 'POS-RR)
                               (cat-contains? x vg))))))
    (dk-conj-close!
      (lambda ()
        (let ((g (dk-goal)))
          (cond
            ((dk-asm? g) (ass))
            ((dk-head-is? g 'IS-UNIFORMLY-CONTINUOUS)
             (mac 'is-uniformly-continuous)
             (dk-conj-close!
               (lambda ()
                 (if (dk-asm? (dk-goal))
                     (ass)
                     (let* ((landed (dk-peel!))
                            (eps (cadr (car landed)))
                            (d1  (dk-skolem! (dk-apply! ug eps)))
                            (dl1 (cat-find "g's delta-universal"
                                   (lambda (x) (and (dk-head-is? x 'FORALL) (cat-contains? x d1)
                                                    (not (cat-contains? x 'POS-RR))))))
                            (d2  (dk-skolem! (dk-apply! uf d1)))
                            (dl2 (cat-find "f's delta-universal"
                                   (lambda (x) (and (dk-head-is? x 'FORALL) (cat-contains? x d2)
                                                    (not (cat-contains? x 'POS-RR)))))))
                       (ew d2)
                       (dk-conj-close!
                         (lambda ()
                           (if (dk-asm? (dk-goal))
                               (ass)
                               (let* ((ls (dk-peel!))
                                      (pts (cat-lhs-points (dk-goal)))
                                      (x (car pts)) (y (cadr pts)))
                                 (dk-apply! dl2 x y)
                                 (dk-cite! 'fun-apply-type-c vf pa pb x)
                                 (dk-cite! 'fun-apply-type-c vf pa pb y)
                                 (dk-apply! dl1 (list vf x) (list vf y))
                                 (subst (dk-apply! cu x))
                                 (subst (dk-apply! cu y))
                                 (ass))))))))))
            (#t (error "UC compose: unexpected conjunct" (expression->string g)))))))))
(cat-done! 'hom-uniformly-continuous-compose)

;;; --- continuity: pointwise, by ms-compose-continuous-at ---------------------------
;;; ms-compose-continuous-at speaks of the lambda  z |-> g(f(z))  on PTS(a); the
;;; composite COMPOSE(g, f) is that lambda (function extensionality, once).
(let* ((h (cat-compose-head! 'CONTINUOUS))
       (va (list-ref h 0)) (vb (list-ref h 1)) (vc (list-ref h 2))
       (vf (list-ref h 3)) (vg (list-ref h 4)) (cu (list-ref h 5))
       (pa (list 'PTS va)) (pb (list 'PTS vb)) (pc (list 'PTS vc))
       (gf (list 'COMPOSE vg vf))
       (lam (list 'VNB-LAMBDA 'msz_ pa (list vg (list vf 'msz_)))))
  (mac-h 'is-continuous (cat-ctx (list 'IS-CONTINUOUS va vb vf) "f continuous"))
  (dk-split-all!)
  (mac-h 'is-continuous (cat-ctx (list 'IS-CONTINUOUS vb vc vg) "g continuous"))
  (dk-split-all!)
  (let ((cf (cat-find "f's pointwise continuity"
              (lambda (x) (and (dk-head-is? x 'FORALL) (cat-contains? x 'IS-CONTINUOUS-AT)
                               (cat-contains? x vf)))))
        (cg (cat-find "g's pointwise continuity"
              (lambda (x) (and (dk-head-is? x 'FORALL) (cat-contains? x 'IS-CONTINUOUS-AT)
                               (cat-contains? x vg)))))
        (e  (dk-fun-ext! gf lam pa pc #f
              (lambda () (dk-lam-type! (lambda ()
                                          (let* ((ls (dk-peel!)) (z (cadr (car ls))))
                                            (dk-cite! 'fun-apply-type-c vf pa pb z)
                                            (dk-cite! 'fun-apply-type-c vg pb pc (list vf z))
                                            (ass)))
                                        (lambda () (ass))))
              (lambda (v)
                (dk-cite! 'fun-apply-type-c vf pa pb v)
                (dk-cite! 'fun-apply-type-c vg pb pc (list vf v))
                (subst (dk-apply! cu v))
                (if (not (dk-lam-b!)) (rfl))))))
    (dk-conj-close!
      (lambda ()
        (let ((g (dk-goal)))
          (cond
            ((dk-asm? g) (ass))
            ((dk-head-is? g 'IS-CONTINUOUS)
             (mac 'is-continuous)
             (dk-conj-close!
               (lambda ()
                 (if (dk-asm? (dk-goal))
                     (ass)
                     (let* ((ls (dk-peel!)) (x (cadr (car ls))))
                       (dk-apply! cf x)
                       (dk-cite! 'fun-apply-type-c vf pa pb x)
                       (dk-apply! cg (list vf x))
                       (dk-cite! 'ms-compose-continuous-at va vb vc vf vg x)
                       (subst (list '= gf lam))
                       (ass))))))
            (#t (error "continuous compose: unexpected conjunct" (expression->string g)))))))))
(cat-done! 'hom-continuous-compose)

;;; --- bounded linear: the linear clauses by preservation, the constants multiply ---

;;; The clauses are found in the context BY CONTENT (the map and the operation
;;; they mention), never by instantiating the definition with `cat-inst': at
;;; (b, c, g) that instantiation renames the definition's own bound b, the
;;; renaming MINTS a fresh name, the mint is charged to the next recorded step,
;;; and the page's `name-witness!' then cites a variable the replayed step does
;;; not mint (found by the page audit of this proof; recorded in the report).
(let* ((h (cat-compose-head! 'BOUNDED-LINEAR))
       (va (list-ref h 0)) (vb (list-ref h 1)) (vc (list-ref h 2))
       (vf (list-ref h 3)) (vg (list-ref h 4)) (cu (list-ref h 5))
       (clause (lambda (head map op who)
                 (cat-find who (lambda (x) (and (dk-head-is? x head) (cat-contains? x map)
                                                (cat-contains? x op))))))
       (fadd (clause 'FORALL vf (list 'VADD va) "f additive"))
       (gadd (clause 'FORALL vg (list 'VADD vb) "g additive"))
       (fhom (clause 'FORALL vf (list 'ACT va) "f homogeneous"))
       (gact (clause 'FORALL vg (list 'ACT vb) "g homogeneous"))
       (k1 (dk-skolem! (clause 'FORSOME vf (list 'VNRM vb) "f bound")))
       (k2 (dk-skolem! (clause 'FORSOME vg (list 'VNRM vc) "g bound")))
       (ea (list 'VEC va)) (eb (list 'VEC vb)) (ec (list 'VEC vc))
       (sab (cat-ctx (list '= (list 'SCAL va) (list 'SCAL vb)) "SCAL(a) = SCAL(b)"))
       (bf (cat-find "f's estimate" (lambda (x) (and (dk-head-is? x 'FORALL) (cat-contains? x k1)))))
       (bg (cat-find "g's estimate" (lambda (x) (and (dk-head-is? x 'FORALL) (cat-contains? x k2)))))
       (kk (list '* k2 k1))
       (typ (lambda (v w) (dk-cite! 'fun-apply-type-c vf ea eb v)
                          (if w (dk-cite! 'fun-apply-type-c vg eb ec (list vf v))))))
  (dk-conj-close!
    (lambda ()
      (let ((g (dk-goal)))
        (cond
          ((dk-asm? g) (ass))
          ;; SCAL(a) = SCAL(c)
          ((dk-head-is? g '=) (subst sab) (ass))
          ((dk-head-is? g 'FORSOME)
           (ew kk)
           (dk-conj-close!
             (lambda ()
               (let ((g2 (dk-goal)))
                 (cond
                   ((dk-head-is? g2 'IN) (dk-real! kk))
                   ((dk-head-is? g2 '<=) (cat-cite! 'rr-leq-mul-nonneg k2 k1) (ass))
                   (#t
                    (let* ((ls (dk-peel!))
                           (x (car (cat-rhs-points (dk-goal))))
                           (fx (list vf x))
                           (na (list (list 'VNRM va) x))
                           (nb (list (list 'VNRM vb) fx))
                           (nc (list (list 'VNRM vc) (list vg fx))))
                      (subst (dk-apply! cu x))
                      (typ x #t)
                      (cat-op-type! na) (cat-op-type! nb) (cat-op-type! nc)
                      (dk-apply! bf x)
                      (dk-apply! bg fx)
                      (cat-scale-chain! nc nb na k2 k1))))))))
          ;; the additive and the homogeneous clause
          ((dk-head-is? g 'FORALL)
           (let* ((ls (dk-peel!))
                  (arg (cadr (cadr (dk-goal))))      ; ((VADD a) u x) or ((ACT a) u x)
                  (u (cadr arg)) (x (caddr arg))
                  (add? (equal? (car arg) (list 'VADD va))))
             (if add?
                 (let* ((s (list (list 'VADD va) u x)))
                   (cat-op-type! s)
                   (subst (dk-apply! cu s))
                   (subst (dk-apply! cu u))
                   (subst (dk-apply! cu x))
                   (typ u #f) (typ x #f)
                   (subst (dk-apply! fadd u x))
                   (dk-apply! gadd (list vf u) (list vf x))
                   (ass))
                 (let* ((s (list (list 'ACT va) u x)))
                   (cat-op-type! s)
                   (subst (dk-apply! cu s))
                   (subst (dk-apply! cu x))
                   (typ x #f)
                   (subst (dk-apply! fhom u x))
                   (dk-have! (list 'IN u (list 'CARR (list 'SCAL vb)))
                     (lambda () (subst (list '= (list 'SCAL vb) (list 'SCAL va))) (ass)))
                   (dk-apply! gact u (list vf x))
                   (ass)))))
          (#t (error "bounded linear compose: unexpected conjunct" (expression->string g))))))))
(cat-done! 'hom-bounded-linear-compose)

;;; =======================================================================
;;; The Hom functors: post- and pre-composition map hom-sets to hom-sets.
;;; hom-functors.scm's driver (hmf-prove-post-type! / -pre-type!), which names
;;; the default's predicate and theorems; copied here with the category's.  (A
;;; kit candidate: one driver parameterised by (IS-X, carrier, arrow, arrow
;;; definition, hom-set, theorem prefix) would serve both files.)
;;; =======================================================================

(define (cat-post h s) (list 'VNB-LAMBDA 'hmpf_ s (list 'COMPOSE h 'hmpf_)))
(define (cat-pre k s)  (list 'VNB-LAMBDA 'hmpf_ s (list 'COMPOSE 'hmpf_ k)))

(define (cat-open-member! cat f x y)
  (mac-h (cat-thm cat '-member-iff) (cat-ctx (list 'IN f (list (cat-hs cat) x y)) "membership"))
  (dk-split-all!))

(define (cat-object! cat v arrow-hyp)
  (if (not (dk-asm? (list (cat-isx cat) v)))
      (dk-have! (list (cat-isx cat) v)
        (lambda ()
          (mac-h (cat-arrow-def cat) (cat-ctx arrow-hyp "the arrow"))
          (dk-split-all!)
          (ass)))))

(define (cat-carrier-set! cat v)
  (let ((goal (list 'IN (list (cat-carrier cat) v) 'SET)))
    (if (not (dk-asm? goal))
        (dk-have! goal
          (lambda ()
            (mac-h (cat-isx cat) (cat-ctx (list (cat-isx cat) v) "IS-X"))
            (dk-split-all!)
            (ass))))))

(define (cat-close-composite! cat x y z outer inner)
  (let* ((c (cat-carrier cat))
         (cx (list c x)) (cy (list c y)) (cz (list c z)))
    (dk-cite! (cat-thm cat '-compose) x y z inner outer)
    (dk-have! (list 'AND (list 'IN inner (list 'FUN cx cy)) (list 'IN outer (list 'FUN cy cz))))
    (dk-cite! 'compose-type cx cy cz outer inner)
    (mac (cat-thm cat '-member-iff))
    (dk-conj-close!)))

(define (cat-prove-post-type! cat)
  (let ((hs (cat-hs cat)) (arrow (cat-arrow cat)))
    (sp (make-wff `(FORALL a (FORALL b (FORALL c (FORALL h
           (IMPLIES (,(cat-isx cat) a) (IMPLIES (IN h (,hs b c))
             (IN ,(cat-post 'h (list hs 'a 'b)) (FUN (,hs a b) (,hs a c)))))))))))
    (dk-peel!)
    (let* ((gl (dk-goal)) (lam (cadr gl)) (dom (caddr lam)) (va (cadr dom)) (vb (caddr dom))
           (vh (cadr (cadddr lam))) (vc (caddr (caddr (caddr gl)))))
      (cat-open-member! cat vh vb vc)
      (cat-object! cat vb (list arrow vb vc vh))
      (cat-carrier-set! cat va)
      (dk-cite! (cat-thm cat '-in-set) va vb)
      (dk-lam-type!
        (lambda ()
          (let* ((landed (dk-peel!)) (vf (cadr (car landed))))
            (cat-open-member! cat vf va vb)
            (cat-close-composite! cat va vb vc vh vf)))
        (lambda () (ass)))
      (cat-done! (cat-thm cat '-post-type)))))

(define (cat-prove-pre-type! cat)
  (let ((hs (cat-hs cat)) (arrow (cat-arrow cat)))
    (sp (make-wff `(FORALL a (FORALL b (FORALL c (FORALL k
           (IMPLIES (,(cat-isx cat) b) (IMPLIES (IN k (,hs c a))
             (IN ,(cat-pre 'k (list hs 'a 'b)) (FUN (,hs a b) (,hs c b)))))))))))
    (dk-peel!)
    (let* ((gl (dk-goal)) (lam (cadr gl)) (dom (caddr lam)) (va (cadr dom)) (vb (caddr dom))
           (vk (caddr (cadddr lam))) (vc (cadr (caddr (caddr gl)))))
      (cat-open-member! cat vk vc va)
      (cat-object! cat va (list arrow vc va vk))
      (cat-object! cat vc (list arrow vc va vk))
      (cat-carrier-set! cat vc)
      (dk-cite! (cat-thm cat '-in-set) va vb)
      (dk-lam-type!
        (lambda ()
          (let* ((landed (dk-peel!)) (vf (cadr (car landed))))
            (cat-open-member! cat vf va vb)
            (cat-close-composite! cat vc va vb vf vk)))
        (lambda () (ass)))
      (cat-done! (cat-thm cat '-pre-type)))))

(for-each (lambda (cat) (cat-prove-post-type! cat) (cat-prove-pre-type! cat))
          '(LIPSCHITZ UNIFORMLY-CONTINUOUS CONTINUOUS BOUNDED-LINEAR))

;;; =======================================================================
;;; The inclusions as hom-sets: the identity-on-objects functors
;;;   HOM-METRIC-SPACE(a, b) subset HOM-LIPSCHITZ(a, b) subset
;;;   HOM-UNIFORMLY-CONTINUOUS(a, b) subset HOM-CONTINUOUS(a, b),
;;;   HOM-NORMED-VECTOR-SPACE(a, b) subset HOM-BOUNDED-LINEAR(a, b).
;;; =======================================================================

(define (cat-prove-subset! name hs1 member1 hs2 member2 incl)
  (sp (make-wff `(FORALL a (FORALL b (SUBSET (,hs1 a b) (,hs2 a b))))))
  (dk-peel!)
  (let* ((gl (dk-goal)) (va (cadr (cadr gl))) (vb (caddr (cadr gl))))
    (mac 'subset-def)
    (let* ((ls (dk-peel!)) (f (cadr (car ls))))
      (mac-h member1 (cat-ctx (list 'IN f (list hs1 va vb)) "membership"))
      (dk-split-all!)
      (dk-cite! incl va vb f)
      (mac member2)
      (dk-conj-close!)))
  (cat-done! name))

(cat-prove-subset! 'hom-metric-space-subset-hom-lipschitz
  'HOM-METRIC-SPACE 'hom-metric-space-member-iff 'HOM-LIPSCHITZ 'hom-lipschitz-member-iff
  'hom-metric-space-is-lipschitz-arrow)
(cat-prove-subset! 'hom-lipschitz-subset-hom-uniformly-continuous
  'HOM-LIPSCHITZ 'hom-lipschitz-member-iff
  'HOM-UNIFORMLY-CONTINUOUS 'hom-uniformly-continuous-member-iff
  'lipschitz-arrow-is-uniformly-continuous-arrow)
(cat-prove-subset! 'hom-uniformly-continuous-subset-hom-continuous
  'HOM-UNIFORMLY-CONTINUOUS 'hom-uniformly-continuous-member-iff
  'HOM-CONTINUOUS 'hom-continuous-member-iff
  'uniformly-continuous-arrow-is-continuous-arrow)
(cat-prove-subset! 'hom-normed-vector-space-subset-hom-bounded-linear
  'HOM-NORMED-VECTOR-SPACE 'hom-normed-vector-space-member-iff
  'HOM-BOUNDED-LINEAR 'hom-bounded-linear-member-iff
  'hom-normed-vector-space-is-bounded-linear-arrow)
