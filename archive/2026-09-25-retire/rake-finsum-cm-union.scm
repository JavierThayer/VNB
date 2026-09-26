;;; theorem-library/rake-finsum-cm-union.scm -- the COMMUTATIVE-MONOID mirror of
;;; the FINSUM congruence / insertion / disjoint-union block, plus the two set
;;; identities that a peeling induction over POWER(X) needs.
;;; Rake batch 5c, assignment 5c-T.  Helper prefix `r7t-'; every helper is
;;; file-local.
;;;
;;;   finsum-cm-congruence-q      m a comm monoid, S finite, f = g pointwise on S
;;;                                 =>  FINSUM(m,f,S) == FINSUM(m,g,S)   (NO typing)
;;;   finsum-cm-insert-ptwise     FINSUM over X u {k} peels f(k), with the summand
;;;                                 typed POINTWISE instead of by a FUN membership
;;;   finsum-cm-union-disjoint    S, T finite and disjoint, f typed pointwise on
;;;                                 S u T  =>  FINSUM(S u T) = FINSUM(S) . FINSUM(T)
;;;   insert-difference-outside   (X u {k0}) \ S = (X \ S) u {k0}   for k0 not in S
;;;   insert-difference-cancel    (X u {k0}) \ (S u {k0}) = X \ S   for k0 not in X
;;;
;;; WHY THE MIRROR IS NEEDED AT ALL.  FINSUM is one functoid -- it reads only
;;; OPR and IDEN off its structure argument -- so FINSUM at a commutative monoid
;;; is the same term as FINSUM at an abelian group, and PROD-RING / FINPROD are
;;; thin aliases of it at COMMUTATIVE-RING-MULTIPLICATIVE-CM (finprod.scm).  But
;;; every law in rake-finsum-laws.scm and rake-finsum-union.scm is GUARDED on
;;; IS-ABELIAN-GROUP, and a commutative monoid is a 3-slot tuple where an abelian
;;; group is a 4-slot one, so none of them instantiates at a monoid.  The
;;; multiplicative side of a ring, and RR-POS-STAR under `eplus', are commutative
;;; monoids with no inverses at all.  rake-finsum-union.scm's closing block names
;;; this file as step (1) of the route to prod-of-sums-expansion, and batch 5b-H's
;;; report names the comm-monoid pointwise typing as the brick under its X10/X11.
;;;
;;; WHAT CHANGES FROM THE ABELIAN-GROUP PROOFS, and it is only this:
;;;   * IS-ABELIAN-GROUP  ->  IS-COMM-MONOID throughout;
;;;   * abelian-group-is-group + group-identity-in  ->  comm-monoid-identity-in-carr;
;;;     group-assoc -> comm-monoid-assoc;  group-left-id -> comm-monoid-left-id;
;;;     abelian-group-opr-comm -> comm-monoid-opr-comm   (all four PROVEN modulo 0
;;;     in theorem-library/rake-finsum-core.scm; the MONOID axioms monoid-assoc /
;;;     -left-id / -right-id are UNWARRANTED `theory-add-axiom!'s and are NOT cited
;;;     here -- citing one would make every result `trust: none');
;;;   * finsum-insert-ag -> finsum-insert (finsum-insert.scm's comm-monoid form);
;;;   * finsum-type-ptwise -> finsum-comm-monoid-type-ptwise (assignment 5c-K,
;;;     theorem-library/rake-finsum-cm-ptwise.scm), which EXISTED when this file
;;;     was written and is cited rather than re-proved;
;;;   * sum-ag-segment-congruence, fin-enum-is-bijection, ord-segment-nn-subset
;;;     and fun-apply-type-c carry NO structure hypothesis, so they are cited
;;;     unchanged.
;;; Note the ONE shape difference that costs a line: `finsum-insert' states its
;;; set and element guards as AND-antecedents where `finsum-insert-ag' curries
;;; them, so each must be `have!'d as a conjunction before the `dk-fact!' (a
;;; `fact' does not split a conjunctive antecedent).
;;;
;;; THE TWO SET IDENTITIES are the ones rake-finsum-union.scm's closing block
;;; lists as step (2).  Both are class-extensionality plus the membership iffs
;;; and `prop'; neither needs a sethood hypothesis, because class-extensionality
;;; is unguarded.  They are stated with the MINIMAL hypothesis in each case
;;; (k0 not in S for the first, k0 not in X for the second): neither needs
;;; S subset X, and the first is true for any S whatever that misses k0.
;;;
;;; LOAD WINDOW [265, end), assuming theorem-library/rake-finsum-cm-ptwise is
;;; wired below 265 (its own window is [252, end)).
;;;   lo = 265: the latest citations are `union-assoc' and `union-empty-right'
;;;       (theorem-library/fin-subsets, 264).  Next latest: card-inequalities
;;;       (259, card-union-nn), rake-finsum-cm-ptwise (5c-K, not yet wired, its
;;;       own window [252, end); finsum-comm-monoid-type-ptwise),
;;;       rake-finsum-core (251, comm-monoid-assoc, comm-monoid-left-id,
;;;       comm-monoid-opr-comm), finsum-insert (233, finsum-insert, finsum-empty),
;;;       rake-finsum-welldef (232, sum-ag-segment-congruence),
;;;       rake-finsum-typing (231, comm-monoid-identity-in-carr),
;;;       rake-inverse-bij (192, fin-enum-is-bijection), difference-laws (189,
;;;       difference-membership), fun-apply-type-proof (160, fun-apply-type-c),
;;;       ord-segment-nn-subset-proof (152, ord-segment-nn-subset),
;;;       equality-basics (146, eq-sym), structure-library/bijection (81,
;;;       bijection-membership-iff).  Everything else is primitive: theory.scm
;;;       (class-extensionality, pairing, pairing-membership, union-membership,
;;;       union-set-closure, empty-set-is-set), cardinality.scm (card-insert,
;;;       finite-set-induction), ordinals.scm (ord-succ-nn), number-systems
;;;       (nn-succ-closed).
;;;   hi: unconstrained.  All five names are NEW -- this file proves no support
;;;       and retires nothing.  Natural slot: immediately after
;;;       theorem-library/rake-finsum-union (assignment 5c-M, window [265, 314)).

;;; ---------------------------------------------------------------------
;;; Helpers
;;; ---------------------------------------------------------------------

(define (r7t-check! name)
  (if (not (proof-done? *ps*))
      (begin
        (display ";; r7t: OPEN LEAVES before qed ") (display name) (newline)
        (for-each (lambda (l)
                    (display ";;   ") (display (expression->string (dk-goal-of l))) (newline))
                  (proof-leaves))
        (error "r7t: proof not complete" name))))

(define (r7t-sing v) (list 'PAIR v v))

(define (r7t-tf v type body) (list 'FORALL v (list 'IMPLIES type body)))
(define (r7t-tfin S body)
  (list 'FORALL S (list 'IMPLIES (list 'IN S 'SET)
    (list 'IMPLIES (list 'IN (list 'CARD S) 'NN) body))))

;; (FORALL v (IMPLIES (IN v DOM) BODY)), DOM a term or a predicate on terms
(define (r7t-guarded-forall? f dom)
  (and (pair? f) (eq? (car f) 'FORALL) (= (length f) 3)
       (let ((b (caddr f)))
         (and (pair? b) (eq? (car b) 'IMPLIES) (= (length b) 3)
              (let ((a (cadr b)))
                (and (pair? a) (eq? (car a) 'IN) (= (length a) 3)
                     (if (procedure? dom) (dom (caddr a)) (equal? (caddr a) dom))))))))

;; ... whose INNER formula satisfies PRED
(define (r7t-guarded-forall-inner? f dom pred)
  (and (r7t-guarded-forall? f dom)
       (pred (caddr (caddr f)))))

;; the eigenvariable of the ORD-SEGMENT typing among LANDED
(define (r7t-seg-var landed)
  (let ((f (any-pred (lambda (g) (and (pair? g) (eq? (car g) 'IN) (symbol? (cadr g))
                                      (pair? (caddr g)) (eq? (car (caddr g)) 'ORD-SEGMENT)))
                     landed)))
    (if f (cadr f)
        (error "r7t-seg-var: no ORD-SEGMENT typing landed"
               (map expression->string landed)))))

;; `fact' of a membership IFF lands BOTH the instance and the universal, and
;; dk-deepest cannot separate them; name the instance by its left-hand side.
(define (r7t-iff-for lhs)
  (let ((hits (filter (lambda (f) (and (pair? f) (eq? (car f) 'IFF) (equal? (cadr f) lhs)))
                      (dk-asms))))
    (if (null? hits)
        (begin (display ";; r7t-iff-for MISS: ") (display (expression->string lhs)) (newline)
               (for-each (lambda (f) (if (and (pair? f) (eq? (car f) 'IFF))
                                         (begin (display ";;   IFF: ")
                                                (display (expression->string f)) (newline))))
                         (dk-asms))
               (error "r7t-iff-for: no instance" lhs))
        (car hits))))

(define (r7t-mem-iff! lhs . args)
  (apply fact args)
  (r7t-iff-for lhs))

;; pairing-membership's guard sits BETWEEN its binders, so `fact' stops at the
;; detached (FORALL x ...) and the element has to come from `inst*!'.
(define (r7t-pairmem! kk v)
  (let ((g (list 'AND (list 'IN kk 'SET) (list 'IN kk 'SET))))
    (if (not (any-pred (lambda (f) (alpha-equiv? f g)) (dk-asms))) (have! g)))
  (fact 'pairing-membership kk kk)
  (inst*! (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                    (pair? (caddr f)) (eq? (car (caddr f)) 'IFF)
                                    (equal? (caddr (cadr (caddr f))) (r7t-sing kk))))
                   "the pairing universal")
          v)
  (r7t-iff-for (list 'IN v (r7t-sing kk))))

(define (r7t-ensure! form thunk)
  (if (any-pred (lambda (f) (alpha-equiv? f form)) (dk-asms))
      form
      (begin (have! form thunk) form)))

;; (IN z (UNION A B)) in context, from (IN z A) (WHICH = 'left) or (IN z B).
(define (r7t-in-union! av bv zv which)
  (let* ((un (list 'UNION av bv))
         (um (r7t-mem-iff! (list 'IN zv un) 'union-membership av bv zv))
         (have (list 'IN zv (if (eq? which 'left) av bv))))
    (r7t-ensure! (list 'IN zv un) (lambda () (dk-only! um have) (prop)))))

;; a pointwise typing / a disjointness universal over DOM, named by its DOMAIN
;; and by the HEAD of its consequent (both have the same FORALL/IMPLIES shape).
(define (r7t-guarded-over dom head what)
  (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                            (pair? (caddr f)) (eq? (car (caddr f)) 'IMPLIES)
                            (equal? (caddr (cadr (caddr f))) dom)
                            (pair? (caddr (caddr f)))
                            (eq? (car (caddr (caddr f))) head)))
           what))
(define (r7t-ptw-over dom) (r7t-guarded-over dom 'IN "the pointwise typing"))
(define (r7t-disj-over dom) (r7t-guarded-over dom 'NOT "the disjointness hypothesis"))

(define (r7t-ptw mv fsym dom)
  (list 'FORALL 'z_ (list 'IMPLIES (list 'IN 'z_ dom)
                          (list 'IN (list fsym 'z_) (list 'CARR mv)))))
(define (r7t-disj sv dom)
  (list 'FORALL 'z_ (list 'IMPLIES (list 'IN 'z_ dom) (list 'NOT (list 'IN 'z_ sv)))))

;; a guarded universal over DOM, proved by bridging each z into SRC's domain
;; with BRIDGE! and applying SRC there.
(define (r7t-restrict-univ! form src bridge!)
  (r7t-ensure! form
    (lambda ()
      (let ((zv (dk-di-var!)))
        (bridge! zv)
        (dk-apply! src zv)
        (ass)))))

;;; ===================================================================
;;; (1) finsum-cm-congruence-q -- the comm-monoid twin of
;;;     `finsum-congruence-q' (rake-finsum-laws.scm).  The conclusion is `=='
;;;     (quasi-equality), so NO typing of either summand is needed: this is the
;;;     mathematical content, and it is what the two proofs below cite.
;;;
;;; The whole content is that the two ENUM-FAMs agree on ORD-SEGMENT(|S|),
;;; which `enum-fam-value' reads off; `sum-ag-segment-congruence' carries no
;;; structure hypothesis at all, so this proof is the abelian-group one with
;;; IS-COMM-MONOID in the guard and nothing else changed.
;;; ===================================================================
(define r7t-cong-q-stmt
  (r7t-tf 'm '(IS-COMM-MONOID m)
    (r7t-tfin 'S
      (list 'FORALL 'f (list 'FORALL 'g
        (list 'IMPLIES '(FORALL z (IMPLIES (IN z S) (= (f z) (g z))))
                       '(== (FINSUM m f S) (FINSUM m g S))))))))

(sp (make-wff r7t-cong-q-stmt))
(dk-peel!)
(let* ((gl  (dk-goal))
       (mv  (cadr (cadr gl)))
       (fv  (caddr (cadr gl)))
       (sv  (cadddr (cadr gl)))
       (gv  (caddr (caddr gl)))
       (agree (dk-pick (lambda (a) (r7t-guarded-forall? a sv)) "forall z in S. f z = g z"))
       (phi  (list 'FIN-ENUM sv))
       (seg  (list 'ORD-SEGMENT (list 'CARD sv)))
       (famf (list 'ENUM-FAM mv fv phi (list 'CARD sv)))
       (famg (list 'ENUM-FAM mv gv phi (list 'CARD sv))))
  (display ";; r7t cong vars: ") (display (list mv sv fv gv)) (newline)
  (mac 'FINSUM)
  (let ((bij (dk-fact! 'fin-enum-is-bijection sv)))
    (mac-h 'bijection-membership-iff bij)
    (dk-split-all!))
  (have! (list 'FORALL 'i_ (list 'IMPLIES (list 'IN 'i_ seg)
                                 (list '== (list famf 'i_) (list famg 'i_))))
         (lambda ()
           (let* ((landed (dk-peel!))
                  (iv (r7t-seg-var landed)))
             (dk-fact! 'ord-segment-nn-subset (list 'CARD sv) iv)
             (dk-fact! 'fun-apply-type-c phi seg sv iv)
             (dk-apply! agree (list phi iv))
             (mac 'ENUM-FAM)
             (lam-b)
             (subst (list '= (list fv (list phi iv)) (list gv (list phi iv))))
             (qrfl))))
  (dk-fact! 'sum-ag-segment-congruence (list 'CARD sv) mv famf famg)
  (ass))
(r7t-check! 'finsum-cm-congruence-q)
(qed 'finsum-cm-congruence-q)
(topic! 'finsum-cm-congruence-q 'algebra)

;;; ===================================================================
;;; (2) finsum-cm-insert-ptwise -- the insertion recurrence with the summand
;;;     typed POINTWISE instead of by a FUN membership.
;;;
;;;     m a comm monoid, X finite, k a set not in X,
;;;     f z in CARR(m) for every z in X u {k}
;;;        =>  FINSUM(m,f,X u {k}) = (OPR m)(FINSUM(m,f,X), f k)
;;;
;;; WHY IT IS THE BRICK (rake-finsum-union.scm says it for the abelian-group
;;; twin, and the argument is the same one).  `finsum-insert' asks for
;;; f in FUN(X u {k}, CARR m), and an induction that peels indices off an index
;;; set never has that: the hypothesis types f on the WHOLE set and the IH is
;;; about a proper subset, so each step would need a RESTRICTION of a set
;;; function, which this tree cannot form.  The restriction IS the lambda
;;; (VNB-LAMBDA w_ U (f w_)), typed by `lam-t' from the pointwise hypothesis,
;;; and `finsum-cm-congruence-q' -- which carries NO typing at all -- transports
;;; the three sums back to f.
;;; ===================================================================
(define r7t-fip-stmt
  '(FORALL m (IMPLIES (IS-COMM-MONOID m)
     (FORALL s_ (IMPLIES (IN s_ SET) (IMPLIES (IN (CARD s_) NN)
     (FORALL k_ (IMPLIES (IN k_ SET) (IMPLIES (NOT (IN k_ s_))
     (FORALL f_ (IMPLIES (FORALL z_ (IMPLIES (IN z_ (UNION s_ (PAIR k_ k_)))
                                             (IN (f_ z_) (CARR m))))
       (= (FINSUM m f_ (UNION s_ (PAIR k_ k_)))
          ((OPR m) (FINSUM m f_ s_) (f_ k_))))))))))))))

;; From the pointwise typing PTW over U in context: the restriction lambda and
;; its FUN typing.
(define (r7t-restrict! mv uu fv ptw)
  (let* ((ca (list 'CARR mv))
         (gl (list 'VNB-LAMBDA 'w_ uu (list fv 'w_))))
    (have! (list 'IN gl (list 'FUN uu ca))
           (lambda () (dk-lam-t!) (ass)))
    gl))

;; Close the focus goal (= (f z) (g z)) for one z already known to be in the
;; lambda's domain: the pointwise typing PTW at z certifies (f z) DEFINED, which
;; is what `rfl' asks for after the beta.
(define (r7t-agree-at! ptw zv)
  (dk-apply! ptw zv)
  (lam-b)
  (rfl))

(sp (make-wff r7t-fip-stmt))
(dk-peel!)
(let* ((g   (dk-goal))
       (lhs (cadr g))                        ; (FINSUM m f U)
       (mv  (cadr lhs)) (fv (caddr lhs)) (uu (cadddr lhs))
       (xv  (cadr uu))
       (kv  (cadr (caddr uu)))
       (pr  (r7t-sing kv))
       (so  (lambda (t) (list 'succ_ORD t)))
       (ptw (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                      (pair? (caddr f)) (eq? (car (caddr f)) 'IMPLIES)
                                      (equal? (caddr (cadr (caddr f))) uu)))
                     "the pointwise typing over U")))
  (display ";; r7t fip vars: ") (display (list mv xv kv fv)) (newline)
  ;; U is a set, and it is finite
  (have! (list 'AND (list 'IN kv 'SET) (list 'IN kv 'SET)))
  (fact 'pairing kv kv)
  (have! (list 'AND (list 'IN xv 'SET) (list 'IN pr 'SET)))
  (fact 'union-set-closure xv pr)                      ; (IN U SET)
  (have! (list 'AND (list 'IN kv 'SET) (list 'NOT (list 'IN kv xv))))
  (fact 'card-insert xv kv)                            ; (= (CARD U) (succ_ORD (CARD X)))
  (fact 'ord-succ-nn (list 'CARD xv))
  (fact 'nn-succ-closed (list 'CARD xv))
  (have! (list 'IN (list 'CARD uu) 'NN)
         (lambda () (subst (list '= (list 'CARD uu) (so (list 'CARD xv))))
                    (subst (list '= (so (list 'CARD xv)) (list 'succ (list 'CARD xv))))
                    (ass)))
  ;; k is in U
  (let ((pmk (r7t-pairmem! kv kv)))
    (have! (list '= kv kv) (lambda () (rfl)))
    (have! (list 'IN kv pr) (lambda () (dk-only! pmk (list '= kv kv)) (prop))))
  (let ((umk (r7t-mem-iff! (list 'IN kv uu) 'union-membership xv pr kv)))
    (have! (list 'IN kv uu) (lambda () (dk-only! umk (list 'IN kv pr)) (prop))))
  ;; the restriction, and the three transports
  (let ((gl (r7t-restrict! mv uu fv ptw)))
    (have! (list 'FORALL 'z_ (list 'IMPLIES (list 'IN 'z_ uu)
                                   (list '= (list fv 'z_) (list gl 'z_))))
           (lambda ()
             (let ((zv (dk-di-var!)))
               (r7t-agree-at! ptw zv))))
    (have! (list 'FORALL 'z_ (list 'IMPLIES (list 'IN 'z_ xv)
                                   (list '= (list fv 'z_) (list gl 'z_))))
           (lambda ()
             (let* ((zv (dk-di-var!))
                    (umz (r7t-mem-iff! (list 'IN zv uu) 'union-membership xv pr zv)))
               (have! (list 'IN zv uu)
                      (lambda () (dk-only! umz (list 'IN zv xv)) (prop)))
               (r7t-agree-at! ptw zv))))
    (dk-fact! 'finsum-cm-congruence-q mv uu fv gl)      ; (== (FINSUM m f U) (FINSUM m g U))
    (dk-fact! 'finsum-cm-congruence-q mv xv fv gl)      ; (== (FINSUM m f X) (FINSUM m g X))
    (have! (list '== (list fv kv) (list gl kv))
           (lambda () (lam-b) (qrfl)))
    ;; `finsum-insert' states its two guards as AND-antecedents where the
    ;; abelian-group form curries them, and `fact' will not split a conjunctive
    ;; antecedent -- so each is `have!'d whole before the citation.
    (have! (list 'AND (list 'IN xv 'SET) (list 'IN (list 'CARD xv) 'NN)))
    (dk-fact! 'finsum-insert mv xv kv gl)
    (subst (list '== (list 'FINSUM mv fv uu) (list 'FINSUM mv gl uu)))
    (subst (list '== (list 'FINSUM mv fv xv) (list 'FINSUM mv gl xv)))
    (subst (list '== (list fv kv) (list gl kv)))
    (ass)))
(r7t-check! 'finsum-cm-insert-ptwise)
(qed 'finsum-cm-insert-ptwise)
(topic! 'finsum-cm-insert-ptwise 'algebra)

;;; ===================================================================
;;; (3) finsum-cm-union-disjoint -- a finite sum over a disjoint union splits,
;;;     in a COMMUTATIVE MONOID.
;;;
;;;     m a comm monoid, S and T finite and DISJOINT, f typed pointwise on S u T
;;;        =>  FINSUM(m,f,S u T) = (OPR m)(FINSUM(m,f,S), FINSUM(m,f,T))
;;;
;;; THE ARGUMENT is `finite-set-induction' (primitive, class form) on T, with
;;;     C = { u | S and u disjoint => for every pointwise-typed f,
;;;                the sum over S u u splits }
;;; -- m and S are fixed eigenvariables, so C is an honest class term.  The base
;;; is union-empty-right plus finsum-empty and the unit law (here reached as
;;; comm-monoid-opr-comm then comm-monoid-left-id, since the MONOID right-identity
;;; axiom is unwarranted); the step is union-assoc (S u (T u {x}) = (S u T) u {x})
;;; plus finsum-cm-insert-ptwise twice -- once to peel x off the big sum, once to
;;; peel it off the T sum -- and comm-monoid-assoc to re-bracket.  Every summand
;;; typing the step needs is the hypothesis restricted to a subset, which is one
;;; union-membership step, BECAUSE the typing is pointwise.
;;; ===================================================================

;; the class body at TV, with the summand variable named `f_'
(define (r7t-body mv sv tv)
  (list 'IMPLIES
    (list 'FORALL 'z_ (list 'IMPLIES (list 'IN 'z_ tv) (list 'NOT (list 'IN 'z_ sv))))
    (list 'FORALL 'f_
      (list 'IMPLIES
        (list 'FORALL 'z_ (list 'IMPLIES (list 'IN 'z_ (list 'UNION sv tv))
                                (list 'IN (list 'f_ 'z_) (list 'CARR mv))))
        (list '= (list 'FINSUM mv 'f_ (list 'UNION sv tv))
                 (list (list 'OPR mv) (list 'FINSUM mv 'f_ sv)
                                      (list 'FINSUM mv 'f_ tv)))))))

(define r7t-fud-stmt
  (list 'FORALL 'm (list 'IMPLIES '(IS-COMM-MONOID m)
    (list 'FORALL 's_ (list 'IMPLIES '(IN s_ SET) (list 'IMPLIES '(IN (CARD s_) NN)
      (list 'FORALL 't_ (list 'IMPLIES '(IN t_ SET) (list 'IMPLIES '(IN (CARD t_) NN)
        (r7t-body 'm 's_ 't_))))))))))

;;; --- the base: T = EMPTY-SET ----------------------------------------------
(define (r7t-base! mv sv)
  (for-each
   (lambda (leaf)
     (dk-focus! leaf)
     (if (equal? (dk-goal) '(in empty-set set))
         (begin (fact 'empty-set-is-set) (ass))
         (begin
           (dk-peel!)
           (let* ((g   (dk-goal))
                  (lhs (cadr g))
                  (fv  (caddr lhs))
                  (vv  (cadddr lhs))          ; (UNION s_ EMPTY-SET)
                  (ptw (r7t-ptw-over vv))
                  (aa  (list 'FINSUM mv fv sv))
                  (ee  (list 'IDEN mv))
                  (op  (lambda (x y) (list (list 'OPR mv) x y))))
             (fact 'union-empty-right sv)     ; (= (UNION s_ EMPTY-SET) s_)
             (r7t-restrict-univ! (r7t-ptw mv fv sv) ptw
                                 (lambda (zv) (r7t-in-union! sv 'EMPTY-SET zv 'left)))
             (fact 'finsum-comm-monoid-type-ptwise mv sv fv)
             (fact 'finsum-empty mv fv)
             (fact 'comm-monoid-identity-in-carr mv)
             (subst (list '= vv sv))
             (subst (list '== (list 'FINSUM mv fv 'EMPTY-SET) ee))
             (fact 'comm-monoid-opr-comm mv aa ee)
             (subst (list '= (op aa ee) (op ee aa)))
             (fact 'comm-monoid-left-id mv aa)
             (subst (list '= (op ee aa) aa))
             (rfl)))))
   (dk-opened (lambda () (comp-mi)))))

;;; --- the step: T |-> T u {x} ---------------------------------------------
(define (r7t-step-body! mv sv tv1 xv cls ih)
  (dk-peel!)
  (let* ((pr    (r7t-sing xv))
         (t1    (list 'UNION tv1 pr))
         (w     (list 'UNION sv tv1))
         (g     (dk-goal))
         (lhs   (cadr g))
         (fv    (caddr lhs))
         (vv    (cadddr lhs))                 ; (UNION s_ (UNION t_ {x}))
         (wpr   (list 'UNION w pr))
         (ptwV  (r7t-ptw-over vv))
         (djT1  (r7t-disj-over t1))
         (op    (lambda (x y) (list (list 'OPR mv) x y)))
         (aa    (list 'FINSUM mv fv sv))
         (bb    (list 'FINSUM mv fv tv1))
         (cc    (list fv xv)))
    (display ";; r7t step body: ") (display (list fv xv)) (newline)
    ;; V = W u {x}
    (fact 'union-assoc sv tv1 pr)             ; (= (UNION W {x}) V)
    (fact 'eq-sym wpr vv)                     ; (= V (UNION W {x}))
    ;; x is in T1, hence in V, and not in W
    (let ((pmx (r7t-pairmem! xv xv)))
      (r7t-ensure! (list '= xv xv) (lambda () (rfl)))
      (r7t-ensure! (list 'IN xv pr) (lambda () (dk-only! pmx (list '= xv xv)) (prop))))
    (r7t-in-union! tv1 pr xv 'right)          ; (IN x T1)
    (r7t-in-union! sv t1 xv 'right)           ; (IN x V)
    (dk-apply! djT1 xv)                       ; (NOT (IN x s_))
    (let ((umw (r7t-mem-iff! (list 'IN xv w) 'union-membership sv tv1 xv)))
      (r7t-ensure! (list 'NOT (list 'IN xv w))
        (lambda () (dk-only! umw (list 'NOT (list 'IN xv sv))
                                 (list 'NOT (list 'IN xv tv1)))
                   (prop))))
    ;; the pointwise typings the three citations want
    (r7t-restrict-univ! (r7t-ptw mv fv wpr) ptwV
      (lambda (zv) (r7t-ensure! (list 'IN zv vv)
                     (lambda () (subst (list '= vv wpr)) (ass)))))
    (r7t-restrict-univ! (r7t-ptw mv fv t1) ptwV
      (lambda (zv) (r7t-in-union! sv t1 zv 'right)))
    (r7t-restrict-univ! (r7t-ptw mv fv w) (r7t-ptw-over wpr)
      (lambda (zv) (r7t-in-union! w pr zv 'left)))
    (r7t-restrict-univ! (r7t-ptw mv fv sv) (r7t-ptw-over w)
      (lambda (zv) (r7t-in-union! sv tv1 zv 'left)))
    (r7t-restrict-univ! (r7t-ptw mv fv tv1) (r7t-ptw-over w)
      (lambda (zv) (r7t-in-union! sv tv1 zv 'right)))
    ;; T is disjoint from S because T u {x} is
    (r7t-restrict-univ! (r7t-disj sv tv1) djT1
      (lambda (zv) (r7t-in-union! tv1 pr zv 'left)))
    ;; the two peels and the induction hypothesis
    (dk-fact! 'finsum-cm-insert-ptwise mv w xv fv)
    (dk-fact! 'finsum-cm-insert-ptwise mv tv1 xv fv)
    (let* ((inner (dk-landed-1 (lambda () (detach! ih))))
           (ihq   (dk-apply! inner fv)))
      (fact 'finsum-comm-monoid-type-ptwise mv sv fv)
      (fact 'finsum-comm-monoid-type-ptwise mv tv1 fv)
      (dk-apply! ptwV xv)                      ; (IN (f x) (CARR m))
      (subst (list '= vv wpr))
      (subst (list '= (list 'FINSUM mv fv wpr) (op (list 'FINSUM mv fv w) cc)))
      (subst ihq)
      (subst (list '= (list 'FINSUM mv fv t1) (op bb cc)))
      (fact 'comm-monoid-assoc mv aa bb cc)
      (ass))))

(define (r7t-step! mv sv cls)
  (dk-split-all! (dk-peel!))
  (let* ((g   (dk-goal))                       ; (IN (UNION t_ {x}) cls)
         (t1  (cadr g))
         (tv1 (cadr t1))
         (xv  (cadr (caddr t1)))
         (pr  (r7t-sing xv))
         (ih  (dk-landed-find (lambda () (comp-me (dk-pick (lambda (f)
                                  (and (pair? f) (eq? (car f) 'IN) (equal? (caddr f) cls)))
                                  "T in the class")))
                              (dk-head? 'IMPLIES))))
    (have! (list 'AND (list 'IN xv 'SET) (list 'IN xv 'SET)))
    (fact 'pairing xv xv)
    (have! (list 'AND (list 'IN tv1 'SET) (list 'IN pr 'SET)))
    (fact 'union-set-closure tv1 pr)
    (have! (list 'AND (list 'IN sv 'SET) (list 'IN tv1 'SET)))
    (fact 'union-set-closure sv tv1)
    (fact 'card-union-nn sv tv1)
    (for-each
     (lambda (leaf)
       (dk-focus! leaf)
       (if (equal? (dk-goal) (list 'in t1 'set))
           (ass)
           (r7t-step-body! mv sv tv1 xv cls ih)))
     (dk-opened (lambda () (comp-mi))))))

(sp (make-wff r7t-fud-stmt))
(dk-peel!)
(let* ((g   (dk-goal))
       (lhs (cadr g))
       (mv  (cadr lhs)) (fv (caddr lhs)) (st (cadddr lhs))
       (sv  (cadr st)) (tv (caddr st))
       (cls (list 'COMP 'u_ (r7t-body mv sv 'u_)))
       (stp (list 'FORALL 'u_
              (list 'IMPLIES (list 'AND (list 'IN 'u_ 'SET)
                                   (list 'AND (list 'IN (list 'CARD 'u_) 'NN)
                                         (list 'IN 'u_ cls)))
                (list 'FORALL 'x_
                  (list 'IMPLIES (list 'AND (list 'IN 'x_ 'SET)
                                       (list 'NOT (list 'IN 'x_ 'u_)))
                        (list 'IN (list 'UNION 'u_ (list 'PAIR 'x_ 'x_)) cls)))))))
  (display ";; r7t fud vars: ") (display (list mv sv tv fv)) (newline)
  (have! (list 'IN 'EMPTY-SET cls) (lambda () (r7t-base! mv sv)))
  (have! stp (lambda () (r7t-step! mv sv cls)))
  (have! (list 'AND (list 'IN 'EMPTY-SET cls) stp))
  (let ((ind (dk-fact! 'finite-set-induction cls)))
    (have! (list 'AND (list 'IN tv 'SET) (list 'IN (list 'CARD tv) 'NN)))
    (let* ((int  (dk-apply! ind tv))
           (body (dk-landed-find (lambda () (comp-me int)) (dk-head? 'IMPLIES)))
           (inner (dk-landed-1 (lambda () (detach! body)))))
      (dk-apply! inner fv)
      (ass))))
(r7t-check! 'finsum-cm-union-disjoint)
(qed 'finsum-cm-union-disjoint)
(topic! 'finsum-cm-union-disjoint 'algebra)

;;; ===================================================================
;;; (4) insert-difference-outside -- inserting a point OUTSIDE S commutes with
;;;     removing S:
;;;
;;;         k not in S   =>   (X u {k}) \ S  =  (X \ S) u {k}
;;;
;;; Step (2) of the route in rake-finsum-union.scm's closing block, and the
;;; identity that carries the POWER(X u {k0}) split of prod-of-sums-expansion.
;;; Stated with the MINIMAL hypothesis: `S subset X' is not needed, and the
;;; identity holds for any S at all that misses k.  class-extensionality is
;;; unguarded, so neither side needs a sethood premise; k's does, because
;;; pairing-membership is guarded on it.
;;; ===================================================================
(define r7t-ido-stmt
  '(FORALL x_ (FORALL s_ (FORALL k_ (IMPLIES (IN k_ SET)
     (IMPLIES (NOT (IN k_ s_))
       (= (DIFFERENCE (UNION x_ (PAIR k_ k_)) s_)
          (UNION (DIFFERENCE x_ s_) (PAIR k_ k_)))))))))

(sp (make-wff r7t-ido-stmt))
(dk-peel!)
(let* ((g   (dk-goal))
       (lhs (cadr g)) (rhs (caddr g))
       (uk  (cadr lhs))                      ; (UNION x_ {k})
       (sv  (caddr lhs))
       (xv  (cadr uk))
       (pr  (caddr uk))
       (kv  (cadr pr))
       (dxs (cadr rhs)))                     ; (DIFFERENCE x_ s_)
  (display ";; r7t ido vars: ") (display (list xv sv kv)) (newline)
  (bc* 'class-extensionality)
  (let* ((yv  (dk-di-var! (lambda (gg) (cadr (cadr gg)))))
         (dl  (r7t-mem-iff! (list 'IN yv lhs) 'difference-membership uk sv yv))
         (ul  (r7t-mem-iff! (list 'IN yv uk)  'union-membership xv pr yv))
         (ur  (r7t-mem-iff! (list 'IN yv rhs) 'union-membership dxs pr yv))
         (dr  (r7t-mem-iff! (list 'IN yv dxs) 'difference-membership xv sv yv))
         (pm  (r7t-pairmem! kv yv))
         (kay (list 'IMPLIES (list '= yv kv) (list 'NOT (list 'IN yv sv)))))
    (have! kay (lambda () (di) (subst (list '= yv kv)) (ass)))
    (dk-only! dl ul ur dr pm kay)
    (prop)))
(r7t-check! 'insert-difference-outside)
(qed 'insert-difference-outside)
(topic! 'insert-difference-outside 'plumbing)

;;; ===================================================================
;;; (5) insert-difference-cancel -- inserting a point into BOTH sides cancels:
;;;
;;;         k not in X   =>   (X u {k}) \ (S u {k})  =  X \ S
;;;
;;; The companion of (4), and the other half of step (2).  Again the minimal
;;; hypothesis: k not in X is what forces a member of the left side to come
;;; from X rather than from {k}, and nothing is assumed about S.
;;; ===================================================================
(define r7t-idc-stmt
  '(FORALL x_ (FORALL s_ (FORALL k_ (IMPLIES (IN k_ SET)
     (IMPLIES (NOT (IN k_ x_))
       (= (DIFFERENCE (UNION x_ (PAIR k_ k_)) (UNION s_ (PAIR k_ k_)))
          (DIFFERENCE x_ s_))))))))

(sp (make-wff r7t-idc-stmt))
(dk-peel!)
(let* ((g   (dk-goal))
       (lhs (cadr g)) (rhs (caddr g))
       (uk  (cadr lhs))                      ; (UNION x_ {k})
       (sk  (caddr lhs))                     ; (UNION s_ {k})
       (xv  (cadr uk))
       (pr  (caddr uk))
       (kv  (cadr pr))
       (sv  (cadr sk)))
  (display ";; r7t idc vars: ") (display (list xv sv kv)) (newline)
  (bc* 'class-extensionality)
  (let* ((yv  (dk-di-var! (lambda (gg) (cadr (cadr gg)))))
         (dl  (r7t-mem-iff! (list 'IN yv lhs) 'difference-membership uk sk yv))
         (ul  (r7t-mem-iff! (list 'IN yv uk)  'union-membership xv pr yv))
         (uls (r7t-mem-iff! (list 'IN yv sk)  'union-membership sv pr yv))
         (dr  (r7t-mem-iff! (list 'IN yv rhs) 'difference-membership xv sv yv))
         (pm  (r7t-pairmem! kv yv))
         (kay (list 'IMPLIES (list '= yv kv) (list 'NOT (list 'IN yv xv)))))
    (have! kay (lambda () (di) (subst (list '= yv kv)) (ass)))
    (dk-only! dl ul uls dr pm kay)
    (prop)))
(r7t-check! 'insert-difference-cancel)
(qed 'insert-difference-cancel)
(topic! 'insert-difference-cancel 'plumbing)

;;; =====================================================================
;;; NOT PROVEN HERE, and what is left.  (Nothing below is code; it is the
;;; report kept beside the file.)
;;;
;;; prod-of-sums-expansion (theorem-library/prod-of-sums.scm:137) was explicitly
;;; NOT part of this assignment, and the reason to keep the note is that its
;;; remaining obstacles are now small and nameable.  rake-finsum-union.scm's
;;; closing block sets out the route in three steps; (1) the comm-monoid mirror
;;; and (2) the two set identities are what this file is, so what is left is (3),
;;; the expansion itself:
;;;
;;;   finite-set-induction on X; prod-ring-insert to factor out (a k0 + b k0);
;;;   ring-left-dist to split it; power-insert-cover / power-insert-disjoint
;;;   (rake-combinatorics.scm, both proven) to cut POWER(X u {k0}) into POWER(X)
;;;   and the image of S |-> S u {k0}; finsum-union-disjoint (rake-finsum-union.scm,
;;;   the ABELIAN-GROUP form -- the outer sum of the expansion is a sum in the
;;;   ring's additive group, so the abelian-group law is the right one there) to
;;;   split the sum along that cut; finsum-reindex-ag with `bijection-from-inverse'
;;;   (rake-monalg-comm.scm) to pull the image half back to POWER(X);
;;;   insert-difference-outside and insert-difference-cancel (HERE) to rewrite the
;;;   two index-set expressions the reindexed summand produces; and
;;;   finsum-cm-congruence-q (HERE) for the PRODUCT side, whose lambda's own
;;;   DOMAIN changes from X to X u {k0} at the step, so the two products are over
;;;   syntactically different summands and only a congruence relates them.
;;;
;;; TWO comm-monoid laws are deliberately NOT mirrored, because nothing asked for
;;; them and each is a five-line copy of its abelian-group twin when it is:
;;;   finsum-cm-all-id-ptwise      (finsum-all-id-ptwise, rake-finsum-union.scm)
;;;                                -- wants a comm-monoid `finsum-all-id' first;
;;;                                the abelian-group one is finsum-type-proof.scm's
;;;   finsum-cm-union-disjoint-fun (the `S n T = {}' + FUN-typing packaging)
;;;
;;; A NOTE FOR THE INTEGRATOR ABOUT THE MONOID AXIOMS.  monoid-assoc,
;;; monoid-left-id and monoid-right-id (structure-library/monoid.scm:18-40) are
;;; unwarranted `theory-add-axiom!'s; assignment 5c-P proves all three
;;; (theorem-library/rake-monoid-laws.scm) and asks for them to be retired.  This
;;; file cites NONE of them -- it goes through comm-monoid-assoc /
;;; comm-monoid-left-id / comm-monoid-opr-comm (rake-finsum-core.scm, proven) --
;;; so it is independent of that retirement in either direction.  In particular
;;; the unit law is reached as "commute, then left-identity", one line longer than
;;; a right-identity citation would be and with no debt.
;;; =====================================================================
