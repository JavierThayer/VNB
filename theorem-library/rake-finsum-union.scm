;;; theorem-library/rake-finsum-union.scm -- the two set/card bricks that three
;;; rake batches built inline, the POINTWISE finsum recurrences they make
;;; possible, the DISJOINT-UNION law for FINSUM, and `finsum-embed'.
;;; Rake batch 5c, assignment 5c-M.  Helper prefix `r7m-'; every helper is
;;; file-local.  Seven theorems, all `proven modulo 0'.
;;;
;;;   card-insert-converse       x not in a, CARD(a u {x}) = succ k, k in NN
;;;                                => CARD a = k
;;;   remove-restore             (a \ {x}) u {x} = a   for x in a
;;;   finsum-insert-ptwise       finsum-insert-ag with the summand typed
;;;                                POINTWISE instead of by a FUN membership
;;;   finsum-union-disjoint      NEW.  S, T finite and disjoint, f typed
;;;                                pointwise on S u T =>
;;;                                FINSUM(S u T) = FINSUM(S) . FINSUM(T)
;;;   finsum-union-disjoint-fun  the same with `S n T = {}' and a FUN typing
;;;   finsum-all-id-ptwise       finsum-all-id with the summand typed pointwise
;;;   finsum-embed               the SUPPORT (theorem-library/finsum-additive.scm
;;;                                :220-234), statement copied literally
;;;
;;; WHAT MADE finsum-union-disjoint REACHABLE.  Its two obstacles were named,
;;; correctly, in rake-finsum-laws.scm's header and again in rake-monalg-comm.scm's
;;; closing block: (i) the induction step's IH needs f typed on a SUBSET of the
;;; index set, i.e. a RESTRICTION of a set function, which this tree cannot form;
;;; (ii) the surgery T = (T \ {x}) u {x} with CARD(T \ {x}) in NN, i.e. a converse
;;; of card-insert.  Both dissolve, and neither the way the notes expected:
;;;
;;;   * (i) is not an obstacle at all once the law is stated with the summand
;;;     typed POINTWISE.  Restricting a pointwise typing to a subset is one
;;;     union-membership step.  The FUN typing is then needed only INSIDE
;;;     finsum-insert-ptwise, at the one set where it is available, and there the
;;;     restriction IS the lambda (VNB-LAMBDA w_ U (f w_)) -- typed by `lam-t',
;;;     transported by `finsum-congruence-q', which carries no typing hypothesis
;;;     at all.  That is the batch-G lesson ("state a classifying map POINTWISE
;;;     and the missing RESTRICT stops mattering") applied to the summand.
;;;   * (ii) never arises: the induction is `finite-set-induction' (primitive,
;;;     class form) on T, whose step ADDS a point (T |-> T u {x}) rather than
;;;     removing one, so no set is ever cut down.  card-insert-converse and
;;;     remove-restore are proved here anyway -- they are what the assignment
;;;     asked for, three batches built them inline, and the NEXT peeling
;;;     induction will want them -- but this file's own proofs use neither.
;;;
;;; finsum-embed is then a corollary, not an induction: S2 IS the disjoint union
;;; S u (S2 \ S), the sum splits, and the second half is a sum of identities
;;; (finsum-all-id-ptwise).  The support's warrant proposed "induction on
;;; |S2 \ S| via finsum-insert-ag"; that induction is done once, here, in general.
;;;
;;; LOAD WINDOW [265, 314).
;;;   lo = 265: the latest citations are `union-assoc' and `union-empty-right'
;;;       (theorem-library/fin-subsets, 264).  Next latest: card-inequalities
;;;       (259, card-union-nn), rake-finsum-laws (249, finsum-congruence-q,
;;;       finsum-type-ptwise), card-subset-nn (246), finsum-insert (233,
;;;       finsum-insert-ag, finsum-empty), finsum-type-proof (201,
;;;       finsum-all-id), subtype-laws (199, abelian-group-is-group,
;;;       abelian-group-opr-comm, group-assoc, group-left-id, group-identity-in),
;;;       difference-laws (189, difference-membership, difference-set),
;;;       fun-apply-type-proof (160, fun-apply-type-c), equality-basics (146,
;;;       eq-sym, eq-trans).  Everything else is primitive: theory.scm
;;;       (extensionality, class-extensionality, subset-def, pairing,
;;;       pairing-membership, union-membership, union-set-closure,
;;;       intersection-membership, membership-implies-sethood, empty-set-is-set,
;;;       empty-set-has-no-members), cardinality.scm (card-insert, card-in-ord,
;;;       finite-set-induction), ordinals.scm (ord-succ-nn, ord-succ-injective,
;;;       nn-subset-ord), number-systems (nn-succ-closed).
;;;   hi = 314: theorem-library/finsum-fiber (314) cites `finsum-embed', whose
;;;       support is retired in favour of the proof here; the other citer is
;;;       monalg-is-ring (319).  The five NEW names are cited by nothing yet.

;;; ---------------------------------------------------------------------
;;; Helpers
;;; ---------------------------------------------------------------------

(define (r7m-check! name)
  (if (not (proof-done? *ps*))
      (begin
        (display ";; r7m: OPEN LEAVES before qed ") (display name) (newline)
        (for-each (lambda (l)
                    (display ";;   ") (display (expression->string (dk-goal-of l))) (newline))
                  (proof-leaves))
        (error "r7m: proof not complete" name))))

(define (r7m-sing v) (list 'PAIR v v))

;; `fact' of a membership IFF lands BOTH the instance and the universal, and
;; dk-deepest cannot separate them; name the instance by its left-hand side.
;; (iff-for retired 2026-09-25: the kit's `iff-for')

(define (r7m-mem-iff! lhs . args)
  (apply fact args)
  (iff-for lhs))

;; pairing-membership's guard sits BETWEEN its binders, so `fact' stops at the
;; detached (FORALL x ...) and the element has to come from `inst*!'.
(define (r7m-pairmem! kk v)
  (let ((g (list 'AND (list 'IN kk 'SET) (list 'IN kk 'SET))))
    (if (not (any-pred (lambda (f) (alpha-equiv? f g)) (dk-asms))) (have! g)))
  (fact 'pairing-membership kk kk)
  (inst*! (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                    (pair? (caddr f)) (eq? (car (caddr f)) 'IFF)
                                    (equal? (caddr (cadr (caddr f))) (r7m-sing kk))))
                   "the pairing universal")
          v)
  (iff-for (list 'IN v (r7m-sing kk))))

;;; ===================================================================
;;; (1) card-insert-converse -- card-insert run BACKWARDS.
;;;
;;;     x not in a, CARD(a u {x}) = succ k, k in NN  =>  CARD a = k.
;;;
;;; card-insert gives CARD(a u {x}) = succ_ORD(CARD a); the hypothesis makes
;;; that succ k = succ_ORD k (ord-succ-nn), and succ_ORD is injective on the
;;; ordinals.  Built inline as lemma 7 of theorem-library/rake-choose-succ.scm
;;; (choose-set-remove-in) and wanted by every finite-set induction that peels
;;; an element off the index set.
;;; ===================================================================
(define r7m-cic-stmt
  '(FORALL a_ (IMPLIES (IN a_ SET)
     (FORALL x_ (IMPLIES (AND (IN x_ SET) (NOT (IN x_ a_)))
       (FORALL k_ (IMPLIES (IN k_ NN)
         (IMPLIES (= (CARD (UNION a_ (PAIR x_ x_))) (succ k_))
                  (= (CARD a_) k_)))))))))

(sp (make-wff r7m-cic-stmt))
(dk-split-all! (dk-peel!))
(let* ((g   (dk-goal))                       ; (= (CARD a_) k_)
       (av  (cadr (cadr g)))
       (kv  (caddr g))
       (hyp (dk-pick (lambda (f) (and (pair? f) (eq? (car f) '=)
                                      (pair? (cadr f)) (eq? (car (cadr f)) 'CARD)
                                      (pair? (cadr (cadr f)))
                                      (eq? (car (cadr (cadr f))) 'UNION)))
                     "CARD(a u {x}) = succ k"))
       (uu  (cadr hyp))                      ; (CARD (UNION a_ (PAIR x_ x_)))
       (un  (cadr uu))                       ; (UNION a_ (PAIR x_ x_))
       (xv  (cadr (caddr un)))
       (so  (lambda (t) (list 'succ_ORD t))))
  (display ";; r7m cic vars: ") (display (list av xv kv)) (newline)
  (have! (list 'AND (list 'IN xv 'SET) (list 'NOT (list 'IN xv av))))
  ;; card-insert carries a FINITENESS guard since 2026-09-18
  ;; (structure-library/cardinality.scm: unguarded it is false of an infinite A).
  ;; Here the guard is NOT a hypothesis and cannot be one -- the cardinal of the
  ;; smaller set is what this lemma computes -- so it comes off the BIGGER set:
  ;; CARD(a u {x}) is succ k, hence in NN, and a is a subset of a u {x}, so
  ;; card-subset-nn types CARD(a).  That is the only new citation.
  (have! (list 'AND (list 'IN xv 'SET) (list 'IN xv 'SET)))
  (fact 'pairing xv xv)                      ; (IN {x} SET)
  (have! (list 'AND (list 'IN av 'SET) (list 'IN (r7m-sing xv) 'SET)))
  (fact 'union-set-closure av (r7m-sing xv)) ; (IN U SET)
  (fact 'nn-succ-closed kv)                  ; (IN (succ k_) NN)
  (have! (list 'IN uu 'NN)                   ; (IN (CARD U) NN)
         (lambda () (subst hyp) (ass)))
  (have! (list 'AND (list 'IN un 'SET) (list 'IN uu 'NN)))
  (let ((incl (list 'FORALL 'z_ (list 'IMPLIES (list 'IN 'z_ av) (list 'IN 'z_ un)))))
    (have! incl
           (lambda ()
             (let* ((zv  (dk-di-var!))
                    (umz (r7m-mem-iff! (list 'IN zv un) 'union-membership
                                       av (r7m-sing xv) zv)))
               (dk-only! umz (list 'IN zv av))
               (prop))))
    (have! (list 'AND (list 'IN av 'SET) incl)))
  (fact 'card-subset-nn un av)               ; (IN (CARD a_) NN)
  (fact 'card-insert av xv)                  ; (= (CARD U) (succ_ORD (CARD a_)))
  (fact 'eq-sym uu (so (list 'CARD av)))
  (fact 'eq-trans (so (list 'CARD av)) uu (list 'succ kv))
  (fact 'ord-succ-nn kv)                     ; (= (succ_ORD k_) (succ k_))
  (fact 'eq-sym (so kv) (list 'succ kv))
  (fact 'eq-trans (so (list 'CARD av)) (list 'succ kv) (so kv))
  (fact 'card-in-ord av)
  (fact 'nn-subset-ord kv)
  (have! (list 'AND (list 'IN (list 'CARD av) 'ORD)
               (list 'AND (list 'IN kv 'ORD)
                     (list '= (so (list 'CARD av)) (so kv)))))
  (fact 'ord-succ-injective (list 'CARD av) kv)
  (ass))
(r7m-check! 'card-insert-converse)
(qed 'card-insert-converse)
(topic! 'card-insert-converse 'combinatorial)

;;; ===================================================================
;;; (2) remove-restore -- (a \ {x}) u {x} = a  for x in a.
;;;
;;; The other half of the surgery: card-insert-converse counts the smaller set,
;;; this one puts the point back.  Built inline as lemma 6 of
;;; theorem-library/rake-choose-succ.scm (`choose-set-remove-restores', whose
;;; statement is this one with the sethood of x as a separate premise) and again
;;; inside rake-combinatorics.scm's power-insert-cover.  Here x's sethood comes
;;; off its membership (membership-implies-sethood), so the citer supplies
;;; nothing but `x in a'.
;;; ===================================================================
(define r7m-rr-stmt
  '(FORALL a_ (IMPLIES (IN a_ SET)
     (FORALL x_ (IMPLIES (IN x_ a_)
       (= (UNION (DIFFERENCE a_ (PAIR x_ x_)) (PAIR x_ x_)) a_))))))

(sp (make-wff r7m-rr-stmt))
(dk-peel!)
(let* ((g  (dk-goal))                        ; (= (UNION (DIFFERENCE a {x}) {x}) a)
       (U  (cadr g))
       (av (caddr g))
       (D  (cadr U))
       (xv (cadr (caddr U)))
       (pr (r7m-sing xv)))
  (display ";; r7m rr vars: ") (display (list av xv)) (newline)
  (fact 'membership-implies-sethood xv av)
  (have! (list 'AND (list 'IN xv 'SET) (list 'IN xv 'SET)))
  (fact 'pairing xv xv)
  (fact 'difference-set av pr)
  (have! (list 'AND (list 'IN D 'SET) (list 'IN pr 'SET)))
  (fact 'union-set-closure D pr)
  (have! (list 'AND (list 'IN U 'SET) (list 'IN av 'SET)))
  (let ((ext (iff-for (begin (fact 'extensionality U av) (list '= U av)))))
    (have! (list 'FORALL 'y_ (list 'IFF (list 'IN 'y_ U) (list 'IN 'y_ av)))
      (lambda ()
        (let* ((yv  (dk-di-var! (lambda (gg) (cadr (cadr gg)))))
               (umy (r7m-mem-iff! (list 'IN yv U) 'union-membership D pr yv))
               (dmy (r7m-mem-iff! (list 'IN yv D) 'difference-membership av pr yv))
               (pmy (r7m-pairmem! xv yv))
               (kay (list 'IMPLIES (list '= yv xv) (list 'IN yv av))))
          (have! kay (lambda () (di) (subst (list '= yv xv)) (ass)))
          (dk-only! umy dmy pmy kay)
          (prop))))
    (dk-only! ext (list 'FORALL 'y_ (list 'IFF (list 'IN 'y_ U) (list 'IN 'y_ av))))
    (prop)))
(r7m-check! 'remove-restore)
(qed 'remove-restore)
(topic! 'remove-restore 'plumbing)

;;; ===================================================================
;;; (3) finsum-insert-ptwise -- finsum-insert-ag with the summand typed
;;;     POINTWISE instead of by a FUN membership.
;;;
;;;     ag an abelian group, X finite, k a set not in X,
;;;     f z in CARR(ag) for every z in X u {k}
;;;        =>  FINSUM(ag,f,X u {k}) = (OPR ag)(FINSUM(ag,f,X), f k)
;;;
;;; WHY IT IS THE BRICK.  finsum-insert-ag asks for f in FUN(X u {k}, CARR ag),
;;; and an induction that peels indices off an index set never has that: the
;;; hypothesis types f on the WHOLE set and the IH is about a proper subset, so
;;; each step would need a RESTRICTION of a set function, which this tree cannot
;;; form (CLAUDE.md, "Two things the tree does NOT have").  The restriction IS
;;; the lambda (VNB-LAMBDA w_ U (f w_)), typed by `lam-t' from the pointwise
;;; hypothesis, and `finsum-congruence-q' -- which carries NO typing at all --
;;; transports the three sums back to f.  So the FUN typing is needed only
;;; INSIDE this proof, at the one set where it is available.
;;; ===================================================================
(define r7m-fip-stmt
  '(FORALL ag (IMPLIES (IS-ABELIAN-GROUP ag)
     (FORALL s_ (IMPLIES (IN s_ SET) (IMPLIES (IN (CARD s_) NN)
     (FORALL k_ (IMPLIES (IN k_ SET) (IMPLIES (NOT (IN k_ s_))
     (FORALL f_ (IMPLIES (FORALL z_ (IMPLIES (IN z_ (UNION s_ (PAIR k_ k_)))
                                             (IN (f_ z_) (CARR ag))))
       (= (FINSUM ag f_ (UNION s_ (PAIR k_ k_)))
          ((OPR ag) (FINSUM ag f_ s_) (f_ k_))))))))))))))

;; From the pointwise typing PTW over U in context: the restriction lambda, its
;; FUN typing, and the two quasi-equations that take a sum of f to a sum of it.
(define (r7m-restrict! agv uu fv ptw)
  (let* ((ca (list 'CARR agv))
         (gl (list 'VNB-LAMBDA 'w_ uu (list fv 'w_))))
    (have! (list 'IN gl (list 'FUN uu ca))
           (lambda () (dk-lam-t!) (ass)))
    gl))

;; Close the focus goal (= (f z) (g z)) for one z already known to be in the
;; lambda's domain: the pointwise typing PTW at z certifies (f z) DEFINED, which
;; is what `rfl' asks for after the beta.
(define (r7m-agree-at! ptw zv)
  (dk-apply! ptw zv)
  (lam-b)
  (rfl))

(sp (make-wff r7m-fip-stmt))
(dk-peel!)
(let* ((g   (dk-goal))
       (lhs (cadr g))                        ; (FINSUM ag f U)
       (agv (cadr lhs)) (fv (caddr lhs)) (uu (cadddr lhs))
       (xv  (cadr uu))
       (kv  (cadr (caddr uu)))
       (pr  (r7m-sing kv))
       (ca  (list 'CARR agv))
       (so  (lambda (t) (list 'succ_ORD t)))
       (ptw (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                      (pair? (caddr f)) (eq? (car (caddr f)) 'IMPLIES)
                                      (equal? (caddr (cadr (caddr f))) uu)))
                     "the pointwise typing over U")))
  (display ";; r7m fip vars: ") (display (list agv xv kv fv)) (newline)
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
  ;; k is in U, and so is every member of X
  (let ((pmk (r7m-pairmem! kv kv)))
    (have! (list '= kv kv) (lambda () (rfl)))
    (have! (list 'IN kv pr) (lambda () (dk-only! pmk (list '= kv kv)) (prop))))
  (let ((umk (r7m-mem-iff! (list 'IN kv uu) 'union-membership xv pr kv)))
    (have! (list 'IN kv uu) (lambda () (dk-only! umk (list 'IN kv pr)) (prop))))
  ;; the restriction, and the three transports
  (let ((gl (r7m-restrict! agv uu fv ptw)))
    (have! (list 'FORALL 'z_ (list 'IMPLIES (list 'IN 'z_ uu)
                                   (list '= (list fv 'z_) (list gl 'z_))))
           (lambda ()
             (let ((zv (dk-di-var!)))
               (r7m-agree-at! ptw zv))))
    (have! (list 'FORALL 'z_ (list 'IMPLIES (list 'IN 'z_ xv)
                                   (list '= (list fv 'z_) (list gl 'z_))))
           (lambda ()
             (let* ((zv (dk-di-var!))
                    (umz (r7m-mem-iff! (list 'IN zv uu) 'union-membership xv pr zv)))
               (have! (list 'IN zv uu)
                      (lambda () (dk-only! umz (list 'IN zv xv)) (prop)))
               (r7m-agree-at! ptw zv))))
    (dk-fact! 'finsum-congruence-q agv uu fv gl)        ; (== (FINSUM ag f U) (FINSUM ag g U))
    (dk-fact! 'finsum-congruence-q agv xv fv gl)        ; (== (FINSUM ag f X) (FINSUM ag g X))
    (have! (list '== (list fv kv) (list gl kv))
           (lambda () (lam-b) (qrfl)))
    (dk-fact! 'finsum-insert-ag agv xv kv gl)
    (subst (list '== (list 'FINSUM agv fv uu) (list 'FINSUM agv gl uu)))
    (subst (list '== (list 'FINSUM agv fv xv) (list 'FINSUM agv gl xv)))
    (subst (list '== (list fv kv) (list gl kv)))
    (ass)))
(r7m-check! 'finsum-insert-ptwise)
(qed 'finsum-insert-ptwise)
(topic! 'finsum-insert-ptwise 'algebra)

;;; ===================================================================
;;; (4) finsum-union-disjoint -- a finite sum over a disjoint union splits.
;;;
;;;     ag an abelian group, S and T finite and DISJOINT, f typed pointwise
;;;     on S u T
;;;        =>  FINSUM(ag,f,S u T) = (OPR ag)(FINSUM(ag,f,S), FINSUM(ag,f,T))
;;;
;;; NEW: the tree has had no statement of this shape.  Batches 5b-A and 5b-I
;;; both stopped on it (prod-of-sums-expansion; the SUM-SET disjoint-union
;;; axiom), and `finsum-embed' is its corollary.
;;;
;;; THE ARGUMENT is `finite-set-induction' (primitive, class form) on T, with
;;; the class
;;;     C = { u | S and u disjoint => for every pointwise-typed f,
;;;                the sum over S u u splits }
;;; -- ag and S are fixed eigenvariables, so C is an honest class term.  The
;;; base is union-empty-right plus finsum-empty and the unit law; the step is
;;; union-assoc (S u (T u {x}) = (S u T) u {x}) plus finsum-insert-ptwise twice
;;; -- once to peel x off the big sum, once to peel it off the T sum -- and
;;; group-assoc to re-bracket.  Every summand typing the step needs is the
;;; hypothesis restricted to a subset, which is one union-membership step,
;;; BECAUSE the typing is pointwise: with a FUN typing each of those would be a
;;; restriction the tree cannot form.
;;; ===================================================================

;; the class body at TV, with the summand variable named `f_'
(define (r7m-body agv sv tv)
  (list 'IMPLIES
    (list 'FORALL 'z_ (list 'IMPLIES (list 'IN 'z_ tv) (list 'NOT (list 'IN 'z_ sv))))
    (list 'FORALL 'f_
      (list 'IMPLIES
        (list 'FORALL 'z_ (list 'IMPLIES (list 'IN 'z_ (list 'UNION sv tv))
                                (list 'IN (list 'f_ 'z_) (list 'CARR agv))))
        (list '= (list 'FINSUM agv 'f_ (list 'UNION sv tv))
                 (list (list 'OPR agv) (list 'FINSUM agv 'f_ sv)
                                       (list 'FINSUM agv 'f_ tv)))))))

(define r7m-fud-stmt
  (list 'FORALL 'ag (list 'IMPLIES '(IS-ABELIAN-GROUP ag)
    (list 'FORALL 's_ (list 'IMPLIES '(IN s_ SET) (list 'IMPLIES '(IN (CARD s_) NN)
      (list 'FORALL 't_ (list 'IMPLIES '(IN t_ SET) (list 'IMPLIES '(IN (CARD t_) NN)
        (r7m-body 'ag 's_ 't_))))))))))

;; a pointwise typing / a disjointness universal over DOM, named by its DOMAIN
;; and by the HEAD of its consequent (both have the same FORALL/IMPLIES shape).
(define (r7m-guarded-over dom head what)
  (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                            (pair? (caddr f)) (eq? (car (caddr f)) 'IMPLIES)
                            (equal? (caddr (cadr (caddr f))) dom)
                            (pair? (caddr (caddr f)))
                            (eq? (car (caddr (caddr f))) head)))
           what))
(define (r7m-ptw-over dom) (r7m-guarded-over dom 'IN "the pointwise typing"))
(define (r7m-disj-over dom) (r7m-guarded-over dom 'NOT "the disjointness hypothesis"))

(define (r7m-ptw agv fsym dom)
  (list 'FORALL 'z_ (list 'IMPLIES (list 'IN 'z_ dom)
                          (list 'IN (list fsym 'z_) (list 'CARR agv)))))
(define (r7m-disj sv dom)
  (list 'FORALL 'z_ (list 'IMPLIES (list 'IN 'z_ dom) (list 'NOT (list 'IN 'z_ sv)))))

(define (r7m-ensure! form thunk)
  (if (any-pred (lambda (f) (alpha-equiv? f form)) (dk-asms))
      form
      (begin (have! form thunk) form)))

;; (IN z (UNION A B)) in context, from (IN z A) (WHICH = 'left) or (IN z B).
(define (r7m-in-union! av bv zv which)
  (let* ((un (list 'UNION av bv))
         (um (r7m-mem-iff! (list 'IN zv un) 'union-membership av bv zv))
         (have (list 'IN zv (if (eq? which 'left) av bv))))
    (r7m-ensure! (list 'IN zv un) (lambda () (dk-only! um have) (prop)))))

;; a guarded universal over DOM, proved by bridging each z into SRC's domain
;; with BRIDGE! and applying SRC there.
(define (r7m-restrict-univ! form src bridge!)
  (r7m-ensure! form
    (lambda ()
      (let ((zv (dk-di-var!)))
        (bridge! zv)
        (dk-apply! src zv)
        (ass)))))

;;; --- the base: T = EMPTY-SET ----------------------------------------------
(define (r7m-base! agv sv)
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
                  (ptw (r7m-ptw-over vv))
                  (aa  (list 'FINSUM agv fv sv))
                  (ee  (list 'IDEN agv))
                  (op  (lambda (x y) (list (list 'OPR agv) x y))))
             (fact 'union-empty-right sv)     ; (= (UNION s_ EMPTY-SET) s_)
             (r7m-restrict-univ! (r7m-ptw agv fv sv) ptw
                                 (lambda (zv) (r7m-in-union! sv 'EMPTY-SET zv 'left)))
             (fact 'finsum-type-ptwise agv sv fv)
             (fact 'finsum-empty agv fv)
             (fact 'abelian-group-is-group agv)
             (fact 'group-identity-in agv)
             (subst (list '= vv sv))
             (subst (list '== (list 'FINSUM agv fv 'EMPTY-SET) ee))
             (fact 'abelian-group-opr-comm agv aa ee)
             (subst (list '= (op aa ee) (op ee aa)))
             (fact 'group-left-id agv aa)
             (subst (list '= (op ee aa) aa))
             (rfl)))))
   (dk-opened (lambda () (comp-mi)))))

;;; --- the step: T |-> T u {x} ---------------------------------------------
(define (r7m-step-body! agv sv tv1 xv cls ih)
  (dk-peel!)
  (let* ((pr    (r7m-sing xv))
         (t1    (list 'UNION tv1 pr))
         (w     (list 'UNION sv tv1))
         (g     (dk-goal))
         (lhs   (cadr g))
         (fv    (caddr lhs))
         (vv    (cadddr lhs))                 ; (UNION s_ (UNION t_ {x}))
         (wpr   (list 'UNION w pr))
         (ptwV  (r7m-ptw-over vv))
         (djT1  (r7m-disj-over t1))
         (op    (lambda (x y) (list (list 'OPR agv) x y)))
         (aa    (list 'FINSUM agv fv sv))
         (bb    (list 'FINSUM agv fv tv1))
         (cc    (list fv xv)))
    (display ";; r7m step body: ") (display (list fv xv)) (newline)
    ;; V = W u {x}
    (fact 'union-assoc sv tv1 pr)             ; (= (UNION W {x}) V)
    (fact 'eq-sym wpr vv)                     ; (= V (UNION W {x}))
    ;; x is in T1, hence in V, and not in W
    (let ((pmx (r7m-pairmem! xv xv)))
      (r7m-ensure! (list '= xv xv) (lambda () (rfl)))
      (r7m-ensure! (list 'IN xv pr) (lambda () (dk-only! pmx (list '= xv xv)) (prop))))
    (r7m-in-union! tv1 pr xv 'right)          ; (IN x T1)
    (r7m-in-union! sv t1 xv 'right)           ; (IN x V)
    (dk-apply! djT1 xv)                       ; (NOT (IN x s_))
    (let ((umw (r7m-mem-iff! (list 'IN xv w) 'union-membership sv tv1 xv)))
      (r7m-ensure! (list 'NOT (list 'IN xv w))
        (lambda () (dk-only! umw (list 'NOT (list 'IN xv sv))
                                 (list 'NOT (list 'IN xv tv1)))
                   (prop))))
    ;; the pointwise typings the three citations want
    (r7m-restrict-univ! (r7m-ptw agv fv wpr) ptwV
      (lambda (zv) (r7m-ensure! (list 'IN zv vv)
                     (lambda () (subst (list '= vv wpr)) (ass)))))
    (r7m-restrict-univ! (r7m-ptw agv fv t1) ptwV
      (lambda (zv) (r7m-in-union! sv t1 zv 'right)))
    (r7m-restrict-univ! (r7m-ptw agv fv w) (r7m-ptw-over wpr)
      (lambda (zv) (r7m-in-union! w pr zv 'left)))
    (r7m-restrict-univ! (r7m-ptw agv fv sv) (r7m-ptw-over w)
      (lambda (zv) (r7m-in-union! sv tv1 zv 'left)))
    (r7m-restrict-univ! (r7m-ptw agv fv tv1) (r7m-ptw-over w)
      (lambda (zv) (r7m-in-union! sv tv1 zv 'right)))
    ;; T is disjoint from S because T u {x} is
    (r7m-restrict-univ! (r7m-disj sv tv1) djT1
      (lambda (zv) (r7m-in-union! tv1 pr zv 'left)))
    ;; the two peels and the induction hypothesis
    (dk-fact! 'finsum-insert-ptwise agv w xv fv)
    (dk-fact! 'finsum-insert-ptwise agv tv1 xv fv)
    (let* ((inner (dk-landed-1 (lambda () (detach! ih))))
           (ihq   (dk-apply! inner fv)))
      (fact 'finsum-type-ptwise agv sv fv)
      (fact 'finsum-type-ptwise agv tv1 fv)
      (dk-apply! ptwV xv)                      ; (IN (f x) (CARR ag))
      (fact 'abelian-group-is-group agv)
      (subst (list '= vv wpr))
      (subst (list '= (list 'FINSUM agv fv wpr) (op (list 'FINSUM agv fv w) cc)))
      (subst ihq)
      (subst (list '= (list 'FINSUM agv fv t1) (op bb cc)))
      (fact 'group-assoc agv aa bb cc)
      (ass))))

(define (r7m-step! agv sv cls)
  (dk-split-all! (dk-peel!))
  (let* ((g   (dk-goal))                       ; (IN (UNION t_ {x}) cls)
         (t1  (cadr g))
         (tv1 (cadr t1))
         (xv  (cadr (caddr t1)))
         (pr  (r7m-sing xv))
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
           (r7m-step-body! agv sv tv1 xv cls ih)))
     (dk-opened (lambda () (comp-mi))))))

(sp (make-wff r7m-fud-stmt))
(dk-peel!)
(let* ((g   (dk-goal))
       (lhs (cadr g))
       (agv (cadr lhs)) (fv (caddr lhs)) (st (cadddr lhs))
       (sv  (cadr st)) (tv (caddr st))
       (cls (list 'COMP 'u_ (r7m-body agv sv 'u_)))
       (stp (list 'FORALL 'u_
              (list 'IMPLIES (list 'AND (list 'IN 'u_ 'SET)
                                   (list 'AND (list 'IN (list 'CARD 'u_) 'NN)
                                         (list 'IN 'u_ cls)))
                (list 'FORALL 'x_
                  (list 'IMPLIES (list 'AND (list 'IN 'x_ 'SET)
                                       (list 'NOT (list 'IN 'x_ 'u_)))
                        (list 'IN (list 'UNION 'u_ (list 'PAIR 'x_ 'x_)) cls)))))))
  (display ";; r7m fud vars: ") (display (list agv sv tv fv)) (newline)
  (have! (list 'IN 'EMPTY-SET cls) (lambda () (r7m-base! agv sv)))
  (have! stp (lambda () (r7m-step! agv sv cls)))
  (have! (list 'AND (list 'IN 'EMPTY-SET cls) stp))
  (let ((ind (dk-fact! 'finite-set-induction cls)))
    (have! (list 'AND (list 'IN tv 'SET) (list 'IN (list 'CARD tv) 'NN)))
    (let* ((int  (dk-apply! ind tv))
           (body (dk-landed-find (lambda () (comp-me int)) (dk-head? 'IMPLIES)))
           (inner (dk-landed-1 (lambda () (detach! body)))))
      (dk-apply! inner fv)
      (ass))))
(r7m-check! 'finsum-union-disjoint)
(qed 'finsum-union-disjoint)
(topic! 'finsum-union-disjoint 'algebra)

;;; ===================================================================
;;; (4b) finsum-union-disjoint-fun -- the same law in the vocabulary the rest
;;;      of the library speaks: disjointness as `S n T = {}' (the form
;;;      card-union-disjoint and the SUM-SET axioms use) and the summand typed
;;;      by a FUN membership over the union.  Both hypotheses are one step
;;;      stronger than (4)'s, so the proof is two derivations and a citation.
;;; ===================================================================
(define r7m-fudf-stmt
  (list 'FORALL 'ag (list 'IMPLIES '(IS-ABELIAN-GROUP ag)
    (list 'FORALL 's_ (list 'IMPLIES '(IN s_ SET) (list 'IMPLIES '(IN (CARD s_) NN)
      (list 'FORALL 't_ (list 'IMPLIES '(IN t_ SET) (list 'IMPLIES '(IN (CARD t_) NN)
        (list 'IMPLIES '(= (INTERSECTION s_ t_) EMPTY-SET)
          (list 'FORALL 'f_ (list 'IMPLIES
            '(IN f_ (FUN (UNION s_ t_) (CARR ag)))
            '(= (FINSUM ag f_ (UNION s_ t_))
                ((OPR ag) (FINSUM ag f_ s_) (FINSUM ag f_ t_)))))))))))))))

(sp (make-wff r7m-fudf-stmt))
(dk-peel!)
(let* ((g   (dk-goal))
       (lhs (cadr g))
       (agv (cadr lhs)) (fv (caddr lhs)) (st (cadddr lhs))
       (sv  (cadr st)) (tv (caddr st))
       (ca  (list 'CARR agv)))
  (display ";; r7m fudf vars: ") (display (list agv sv tv fv)) (newline)
  (have! (r7m-ptw agv fv st)
    (lambda () (let ((zv (dk-di-var!)))
                 (fact 'fun-apply-type-c fv st ca zv)
                 (ass))))
  (have! (r7m-disj sv tv)
    (lambda ()
      (let* ((zv (dk-di-var!))
             (im (r7m-mem-iff! (list 'IN zv (list 'INTERSECTION sv tv))
                               'intersection-membership sv tv zv)))
        (di)                                   ; assume (IN z s_)
        (have! (list 'IN zv (list 'INTERSECTION sv tv))
               (lambda () (dk-only! im (list 'IN zv sv) (list 'IN zv tv)) (prop)))
        (fact 'eq-sym (list 'INTERSECTION sv tv) 'EMPTY-SET)
        (have! (list 'IN zv 'EMPTY-SET)
               (lambda () (subst (list '= 'EMPTY-SET (list 'INTERSECTION sv tv))) (ass)))
        (ai (dk-fact! 'empty-set-has-no-members zv)))))
  (dk-fact! 'finsum-union-disjoint agv sv tv fv)
  (ass))
(r7m-check! 'finsum-union-disjoint-fun)
(qed 'finsum-union-disjoint-fun)
(topic! 'finsum-union-disjoint-fun 'algebra)

;;; ===================================================================
;;; (5) finsum-all-id-ptwise -- finsum-all-id with the summand typed
;;;     POINTWISE.  Same move as (3), and for the same reason: the sum whose
;;;     summand vanishes is a sum over a SUBSET of where the summand is typed.
;;;     No typing hypothesis is needed at all -- `f z = IDEN(ag)' on the index
;;;     set types f there by itself.
;;; ===================================================================
(define r7m-faip-stmt
  '(FORALL ag (IMPLIES (IS-ABELIAN-GROUP ag)
     (FORALL s_ (IMPLIES (IN s_ SET) (IMPLIES (IN (CARD s_) NN)
     (FORALL f_ (IMPLIES (FORALL z_ (IMPLIES (IN z_ s_) (= (f_ z_) (IDEN ag))))
       (= (FINSUM ag f_ s_) (IDEN ag))))))))))

(sp (make-wff r7m-faip-stmt))
(dk-peel!)
(let* ((g   (dk-goal))
       (lhs (cadr g))
       (agv (cadr lhs)) (fv (caddr lhs)) (sv (cadddr lhs))
       (ca  (list 'CARR agv))
       (ee  (list 'IDEN agv))
       (ptw (r7m-guarded-over sv '= "f is IDEN on S"))
       (gl  (list 'VNB-LAMBDA 'w_ sv (list fv 'w_))))
  (display ";; r7m faip vars: ") (display (list agv sv fv)) (newline)
  (fact 'abelian-group-is-group agv)
  (fact 'group-identity-in agv)
  (have! (list 'IN gl (list 'FUN sv ca))
         (lambda () (dk-lam-t!)
                    (let ((wv (dk-di-var!)))
                      (dk-apply! ptw wv)
                      (subst (list '= (list fv wv) ee))
                      (ass))))
  (have! (list 'FORALL 'z_ (list 'IMPLIES (list 'IN 'z_ sv)
                                 (list '= (list gl 'z_) ee)))
         (lambda () (let ((zv (dk-di-var!)))
                      (dk-apply! ptw zv)
                      (lam-b)
                      (ass))))
  (have! (list 'FORALL 'z_ (list 'IMPLIES (list 'IN 'z_ sv)
                                 (list '= (list fv 'z_) (list gl 'z_))))
         (lambda () (let ((zv (dk-di-var!)))
                      (dk-apply! ptw zv)
                      (lam-b)
                      (rfl))))
  (dk-fact! 'finsum-all-id agv sv gl)
  (dk-fact! 'finsum-congruence-q agv sv fv gl)
  (subst (list '== (list 'FINSUM agv fv sv) (list 'FINSUM agv gl sv)))
  (ass))
(r7m-check! 'finsum-all-id-ptwise)
(qed 'finsum-all-id-ptwise)
(topic! 'finsum-all-id-ptwise 'algebra)

;;; ===================================================================
;;; (6) finsum-embed -- extension by the identity.  The support's statement,
;;;     copied LITERALLY from theorem-library/finsum-additive.scm (its `tf' /
;;;     `tfin' builders reproduced here, so the installed formula is
;;;     byte-identical).
;;;
;;; The warrant proposed "induction on |S2 \ S| via finsum-insert-ag"; with
;;; finsum-union-disjoint the induction is already done.  S2 IS the disjoint
;;; union S u (S2 \ S) -- that is the surgery rake-finsum-laws.scm's header
;;; named as the blocker -- the sum splits, and the second half is a sum of
;;; identities.
;;; ===================================================================
(define (r7m-tf v type body) (list 'FORALL v (list 'IMPLIES type body)))
(define (r7m-tfin S body)
  (list 'FORALL S (list 'IMPLIES (list 'IN S 'SET)
    (list 'IMPLIES (list 'IN (list 'CARD S) 'NN) body))))

(define r7m-embed-stmt
  (r7m-tf 'ag '(IS-ABELIAN-GROUP ag)
   (r7m-tfin 'S
    (r7m-tfin 'S2
     (r7m-tf 'f '(IN f (FUN S2 (CARR ag)))
      (list 'IMPLIES '(SUBSET S S2)
       (list 'IMPLIES
             '(FORALL z (IMPLIES (AND (IN z S2) (NOT (IN z S))) (= (f z) (IDEN ag))))
        (list '=
          '(FINSUM ag f S2)
          '(FINSUM ag f S)))))))))

(sp (make-wff r7m-embed-stmt))
(dk-peel!)
(let* ((g   (dk-goal))
       (l   (cadr g)) (r (caddr g))
       (agv (cadr l)) (fv (caddr l)) (s2 (cadddr l))
       (sv  (cadddr r))
       (dd  (list 'DIFFERENCE s2 sv))
       (un  (list 'UNION sv dd))
       (ca  (list 'CARR agv))
       (ee  (list 'IDEN agv))
       (aa  (list 'FINSUM agv fv sv))
       (op  (lambda (x y) (list (list 'OPR agv) x y)))
       (offid (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                        (pair? (caddr f)) (eq? (car (caddr f)) 'IMPLIES)
                                        (pair? (cadr (caddr f)))
                                        (eq? (car (cadr (caddr f))) 'AND)))
                       "f is IDEN off S")))
  (display ";; r7m embed vars: ") (display (list agv sv s2 fv)) (newline)
  ;; SUBSET S S2, pointwise
  (let* ((sdi (r7m-mem-iff! (list 'SUBSET sv s2) 'subset-def sv s2))
         (sub (caddr sdi)))
    (have! sub (lambda () (dk-only! sdi (list 'SUBSET sv s2)) (prop)))
    ;; D = S2 \ S is a finite set
    (fact 'difference-set s2 sv)
    (let ((dsub (list 'FORALL 'z (list 'IMPLIES (list 'IN 'z dd) (list 'IN 'z s2)))))
      (have! dsub
        (lambda () (let* ((zv  (dk-di-var!))
                          (dmz (r7m-mem-iff! (list 'IN zv dd) 'difference-membership s2 sv zv)))
                     (dk-only! dmz (list 'IN zv dd))
                     (prop))))
      (have! (list 'AND (list 'IN s2 'SET) (list 'IN (list 'CARD s2) 'NN)))
      (let ((csn (dk-fact! 'card-subset-nn s2)))
        (have! (list 'AND (list 'IN dd 'SET) dsub))
        (dk-apply! csn dd)))                    ; (IN (CARD D) NN)
    ;; S2 = S u D
    (have! (list '= un s2)
      (lambda ()
        (bc* 'class-extensionality)
        (let* ((xv  (dk-di-var! (lambda (gg) (cadr (cadr gg)))))
               (umx (r7m-mem-iff! (list 'IN xv un) 'union-membership sv dd xv))
               (dmx (r7m-mem-iff! (list 'IN xv dd) 'difference-membership s2 sv xv))
               (sx  (inst*! sub xv)))
          (dk-only! umx dmx sx)
          (prop))))
    (fact 'eq-sym un s2)                        ; (= S2 (UNION S D))
    ;; disjointness, the pointwise typings, and f = IDEN on D
    (have! (r7m-disj sv dd)
      (lambda () (let* ((zv  (dk-di-var!))
                        (dmz (r7m-mem-iff! (list 'IN zv dd) 'difference-membership s2 sv zv)))
                   (dk-only! dmz (list 'IN zv dd))
                   (prop))))
    (have! (r7m-ptw agv fv un)
      (lambda () (let ((zv (dk-di-var!)))
                   (have! (list 'IN zv s2) (lambda () (subst (list '= s2 un)) (ass)))
                   (fact 'fun-apply-type-c fv s2 ca zv)
                   (ass))))
    (have! (r7m-ptw agv fv sv)
      (lambda () (let ((zv (dk-di-var!)))
                   (dk-apply! sub zv)
                   (fact 'fun-apply-type-c fv s2 ca zv)
                   (ass))))
    (have! (list 'FORALL 'z_ (list 'IMPLIES (list 'IN 'z_ dd)
                                   (list '= (list fv 'z_) ee)))
      (lambda () (let* ((zv  (dk-di-var!))
                        (dmz (r7m-mem-iff! (list 'IN zv dd) 'difference-membership s2 sv zv)))
                   (have! (list 'AND (list 'IN zv s2) (list 'NOT (list 'IN zv sv)))
                          (lambda () (dk-only! dmz (list 'IN zv dd)) (prop)))
                   (dk-apply! offid zv)
                   (ass))))
    ;; the split, the vanishing half, and the unit law
    (dk-fact! 'finsum-union-disjoint agv sv dd fv)
    (dk-fact! 'finsum-all-id-ptwise agv dd fv)
    (fact 'finsum-type-ptwise agv sv fv)
    (fact 'abelian-group-is-group agv)
    (fact 'group-identity-in agv)
    (subst (list '= s2 un))
    (subst (list '= (list 'FINSUM agv fv un) (op aa (list 'FINSUM agv fv dd))))
    (subst (list '= (list 'FINSUM agv fv dd) ee))
    (fact 'abelian-group-opr-comm agv aa ee)
    (subst (list '= (op aa ee) (op ee aa)))
    (fact 'group-left-id agv aa)
    (subst (list '= (op ee aa) aa))
    (rfl)))
(r7m-check! 'finsum-embed)
(qed 'finsum-embed)
(topic! 'finsum-embed 'algebra)

;;; =====================================================================
;;; NOT PROVEN, and what it is waiting for.  (Nothing below is code; it is the
;;; report kept beside the file.)
;;;
;;; prod-of-sums-expansion (theorem-library/prod-of-sums.scm:137) was the third
;;; item of this assignment, "if reachable".  It is NOT, and the reason is worth
;;; more than the capstone: the brick rake-monalg-comm.scm's closing block named
;;; -- finsum-union-disjoint -- is now proven, and it serves the RIGHT-hand side
;;; of the expansion only.  The LEFT-hand side is a PRODUCT, and the product
;;; layer has none of the machinery this file uses.
;;;
;;;   PROD-RING(R,f,S) = FINPROD(R^x, f, S) = FINSUM(R^x, f, S) with
;;;   R^x = COMMUTATIVE-RING-MULTIPLICATIVE-CM(R)  (structure-library/finprod.scm)
;;;
;;; -- a thin alias, as that file says, so "every finsum-comm-monoid theorem
;;; applies verbatim through it".  The catch is the inventory.  EVERY law proved
;;; here and in rake-finsum-laws.scm is guarded on IS-ABELIAN-GROUP, and a
;;; commutative monoid is a 3-slot tuple where an abelian group is a 4-slot one,
;;; so none of them instantiates at R^x.  What exists on the comm-monoid side is
;;; exactly four theorems -- finsum-comm-monoid-type, -well-defined,
;;; -permutation-invariance, and finsum-insert (comm-monoid form).  There is no
;;; comm-monoid congruence, no comm-monoid all-identity law, and no comm-monoid
;;; pointwise typing (5b-H's report already names the last of these as the brick
;;; blocking its X10/X11).
;;;
;;; The induction step of the expansion needs a comm-monoid CONGRUENCE before
;;; anything else: the left side is PROD-RING of (VNB-LAMBDA k X ((ADD R)(a k)(b k)))
;;; over X, and at the step the lambda's own DOMAIN changes from X to X u {k0},
;;; so the two products are over syntactically different summands and only a
;;; congruence relates them.  So the honest order of work is:
;;;
;;;   1. the comm-monoid mirror of this file and of rake-finsum-laws.scm's
;;;      congruence block -- finprod-congruence-q, finprod-type-ptwise,
;;;      finprod-insert-ptwise, finprod-union-disjoint.  Each is the abelian-group
;;;      proof with IS-ABELIAN-GROUP replaced by IS-COMM-MONOID and the two group
;;;      citations (abelian-group-is-group + group-identity-in, group-left-id)
;;;      replaced by comm-monoid-identity-in-carr / comm-monoid-carrier-closed-opr
;;;      (rake-finsum-typing.scm) and the comm-monoid unit law; the fold lemmas
;;;      they bottom out in (sum-ag-comm-monoid-type-ind,
;;;      sum-ag-comm-monoid-type-ptwise, sum-ag-segment-congruence) are already
;;;      proven.  One file, and it unblocks 5b-H's X10/X11 as well.
;;;   2. the two set identities, still missing as named lemmas and both easy now
;;;      that difference-membership and remove-restore are theorems:
;;;      (X u {k0}) \ S = (X \ S) u {k0}   for S subset X, k0 not in X, and
;;;      (X u {k0}) \ (S u {k0}) = X \ S.
;;;   3. the expansion itself: finite-set-induction on X; prod-ring-insert to
;;;      factor out (a k0 + b k0); ring-left-dist to split it; power-insert-cover
;;;      / power-insert-disjoint (rake-combinatorics.scm, both proven) to cut
;;;      POWER(X u {k0}) into POWER(X) and the image of S |-> S u {k0};
;;;      finsum-union-disjoint (HERE) to split the sum along that cut;
;;;      finsum-reindex-ag with `bijection-from-inverse' (rake-monalg-comm.scm)
;;;      to pull the image half back to POWER(X); finsum-congruence to match the
;;;      two summands pointwise.  A 300-500 line driver, and every piece of it
;;;      exists once (1) and (2) are done.
;;;
;;; A DUPLICATE the integrator should know about.  `choose-set-remove-restores'
;;; (theorem-library/rake-choose-succ.scm, position 262) is `remove-restore' with
;;; the sethood of x as a separate premise instead of read off its membership --
;;; the same fact, proved twice, by the same driver.  It cannot simply be retired
;;; in its favour: this file cites union-assoc (fin-subsets, 264) and so must load
;;; after rake-choose-succ.  Either move the two set bricks of this file into a
;;; slot below 262 (they cite nothing later than difference-laws, 189, so [190,
;;; 262) is open to them), or leave the duplicate and note it.
;;; =====================================================================
