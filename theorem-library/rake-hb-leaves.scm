;;; theorem-library/rake-hb-leaves.scm -- nine asserted leaves of the
;;; Hahn-Banach cluster, PROVEN.
;;;
;;; The nine proven theorems good-step, hahn-banach, hahn-banach-extend-one,
;;; hb-good-has-maximal, norm-as-sup, norm-attained-by-functional,
;;; norm-bounded-by-functionals, nvs-taylor-remainder-bound and
;;; vector-taylor-remainder-bound bill about 25 distinct asserted leaves between
;;; them.  This file retires the ones that are READ-OFFS -- a definition
;;; unfolded and a conjunct taken, or a typing chased through FUN -- plus two
;;; scalar facts.  Statements are copied LITERALLY from their add-to-pss sites;
;;; each qed prints "re-installing the same statement".
;;;
;;;   extends-on-trans          linear-functional.scm's EXTENDS-ON, unfolded twice
;;;   vnrm-nonneg               a conjunct of IS-NORMED-VECTOR-SPACE
;;;   linfun-on-vec-is-linfun   the two predicates unfold to the same AND
;;;   blf-app-real              f in FUN(VEC m, RR), applied
;;;   bdd-linfun-abs-real         "   + rr-abs-closed
;;;   linfun-app-abs-real       the subspace version of the same
;;;   abs-nonneg-le             rr-abs-of-nonneg, flipped, substituted
;;;   rr-mul-le-right           (b-a)c >= 0 by rr-leq-mul-nonneg, then crs + ineq
;;;   proper-subset-witness     class-extensionality, contrapositive, by pbc
;;;
;;; NOT HERE, and why:
;;;   good-sub-submodule / good-sub-in-power  -- GOOD-SUB and NPE are defined
;;;      INSIDE noetherian-maximal-proof.scm and cited inside it, so the window
;;;      is empty: those two proofs SPLICE (rake-hb-leaves-2.scm holds them).
;;;   line-has-v -- same, for LINE inside norm-as-sup-proof.scm.
;;;   span-add-one-superset / span-add-one-has-v -- FALSE AS STATED; see the
;;;      note at the end of this file.
;;;
;;; LOAD WINDOW  [193, 504) over load.scm's prover-load entries:
;;;   lo = 193, just after theorem-library/subset-lemmas (subset-mem-fwd, the
;;;        latest citation here; then rake-analysis2 is NOT needed, nor
;;;        discrete-space -- those two belong to the spliced file).  The other
;;;        floors: theorem-library/rr-abs-basics (178), rr-order-bundle (185),
;;;        binary-minus-laws (160), fun-apply-type-proof (161),
;;;        equality-basics (147), the tactic `prop' (142), `ineq' (32),
;;;        `crs' (30), structure-library/linear-functional (65).
;;;   hi = 504, theorem-library/hahn-banach-full-proof -- the earliest citer of
;;;        extends-on-trans / vnrm-nonneg / linfun-app-abs-real /
;;;        proper-subset-witness.  (norm-as-sup-proof at 505 cites
;;;        linfun-on-vec-is-linfun, bdd-linfun-abs-real and abs-nonneg-le;
;;;        vector-taylor-proof at 506 cites blf-app-real and rr-mul-le-right.)
;;;   RECOMMENDED SLOT: immediately before "theorem-library/hahn-banach-proof".
;;;   No LATE tactic is used (no `contra', no `prep', no `ineq-supply').

;;; --------------------------------------------------------------------
;;; File-local helpers (`rhb-' prefix; none is named like a tactic).

;;; `ineq' takes 1-BASED indices into the context list, which no driver can
;;; count by hand after a few `fact's.  Name the premises by FORMULA instead --
;;; the formulas the context actually holds, not reconstructions.
(define (rhb-ineq! . rhb-forms)
  (let ((rhb-asms (dk-asms)))
    (apply ineq
           (map (lambda (f)
                  (let loop ((l rhb-asms) (i 1))
                    (cond ((null? l) (error "rhb-ineq!: not in context" f))
                          ((equal? (car l) f) i)
                          (#t (loop (cdr l) (+ i 1))))))
                rhb-forms))))

;;; Cite THM at TERMS; if what lands is still an implication, prove its
;;; antecedent with THUNK and detach.  `bc' declines these: the antecedent sits
;;; under the theorem's own universals, so backchain finds "no matching
;;; implication" (seen here on class-extensionality and power-mem-intro).
(define (rhb-cite! rhb-thm rhb-terms rhb-thunk)
  (let ((r (apply dk-fact! rhb-thm rhb-terms)))
    (if (and (pair? r) (eq? (car r) 'IMPLIES))
        (begin (have! (cadr r) rhb-thunk)
               (dk-landed-1 (lambda () (detach! r))))
        r)))

;;; The context's FUN typing whose DOMAIN is DOM -- named on its shape, never
;;; rebuilt (the eigenvariable `dk-skolem!' minted is not guessable).
(define (rhb-fun-typing-of rhb-dom)
  (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'IN)
                             (pair? (caddr fm)) (eq? (car (caddr fm)) 'FUN)
                             (equal? (cadr (caddr fm)) rhb-dom)))
           "the FUN typing with that domain"))

;;; "g maps into RR, so g(w) -- and |g(w)| -- is a real."  The three typing
;;; leaves below differ only in which predicate hides the FUN typing and
;;; whether the goal wears an `abs'; UNFOLDS is the list of predicate names to
;;; strip, outermost first.
(define (rhb-app-real! rhb-unfolds)
  (for-each (lambda (nm)
              (let ((h (dk-pick (dk-head? nm) "the functional hypothesis")))
                (mac-h nm h)
                (dk-split-all!)))
            rhb-unfolds)
  (let* ((g   (dk-goal))
         (arg (cadr g))
         (app (if (and (pair? arg) (eq? (car arg) 'abs)) (cadr arg) arg))
         (fun (rhb-fun-typing-of
               (let ((h (dk-pick (lambda (fm)
                                   (and (pair? fm) (eq? (car fm) 'IN)
                                        (equal? (cadr fm) (car app))
                                        (pair? (caddr fm))
                                        (eq? (car (caddr fm)) 'FUN)))
                                 "the functional's own FUN typing")))
                 (cadr (caddr h))))))
    (dk-fact! 'fun-apply-type-c (car app) (cadr (caddr fun)) (caddr (caddr fun)) (cadr app))
    (if (not (equal? app arg)) (dk-fact! 'rr-abs-closed app))
    (ass)))

;;; ====================================================================
;;; extends-on-trans -- hahn-banach-full-proof.scm:108
;;; ====================================================================
(sp (make-wff
     '(FORALL s (FORALL t (FORALL g2 (FORALL g1 (FORALL f
        (IMPLIES (SUBSET s t) (IMPLIES (EXTENDS-ON t g2 g1) (IMPLIES (EXTENDS-ON s g1 f)
           (EXTENDS-ON s g2 f)))))))))))
(dk-peel!)
(let* ((rhb-g   (dk-goal))
       (rhb-s   (cadr rhb-g))
       (rhb-sub (dk-pick (dk-head? 'SUBSET) "SUBSET s t"))
       (rhb-t   (caddr rhb-sub))
       (rhb-e1  (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'EXTENDS-ON)
                                           (equal? (cadr fm) rhb-t)))
                         "EXTENDS-ON t g2 g1"))
       (rhb-gg1 (cadddr rhb-e1))
       (rhb-e2  (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'EXTENDS-ON)
                                           (equal? (cadr fm) rhb-s)
                                           (equal? (caddr fm) rhb-gg1)))
                         "EXTENDS-ON s g1 f")))
  (mac 'extends-on)
  (let ((rhb-x (dk-di-var!)))
    (dk-fact! 'subset-mem-fwd rhb-s rhb-t rhb-x)
    (let* ((rhb-a1 (dk-landed-1 (lambda () (mac-h 'extends-on rhb-e1))))
           (rhb-a2 (dk-landed-1 (lambda () (mac-h 'extends-on rhb-e2))))
           (rhb-q1 (dk-apply! rhb-a1 rhb-x)))
      (dk-apply! rhb-a2 rhb-x)
      (subst rhb-q1)
      (ass))))
(qed 'extends-on-trans)

;;; ====================================================================
;;; vnrm-nonneg -- hahn-banach-full-proof.scm:116
;;; A conjunct of IS-NORMED-VECTOR-SPACE, taken by unfolding the predicate --
;;; NOT by citing normed-ag-nrm-nonneg (which is itself asserted: routing
;;; through the normed-ag view only moves the debt, and the qed says so).
;;; ====================================================================
(sp (make-wff
     '(FORALL m (FORALL w_
        (IMPLIES (IS-NORMED-VECTOR-SPACE m) (IMPLIES (IN w_ (VEC m))
           (<= 0 ((VNRM m) w_))))))))
(dk-peel!)
(let* ((rhb-g (dk-goal))
       (rhb-m (cadr (car (caddr rhb-g))))
       (rhb-w (cadr (caddr rhb-g)))
       (rhb-h (dk-pick (dk-head? 'IS-NORMED-VECTOR-SPACE) "IS-NVS")))
  (mac-h 'is-normed-vector-space rhb-h)
  (dk-split-all!)
  (let ((rhb-law (dk-pick (lambda (fm)
                            (and (pair? fm) (eq? (car fm) 'FORALL)
                                 (dk-contains? fm (list '<= 0 (list (list 'VNRM rhb-m) (cadr fm))))))
                          "the norm-nonnegativity law")))
    (dk-apply! rhb-law rhb-w)
    (ass)))
(qed 'vnrm-nonneg)

;;; ====================================================================
;;; linfun-on-vec-is-linfun -- norm-as-sup-proof.scm:96
;;; ====================================================================
(sp (make-wff
     '(FORALL m (FORALL f
        (IMPLIES (IS-LINEAR-FUNCTIONAL-ON m (VEC m) f) (IS-LINEAR-FUNCTIONAL m f))))))
(dk-peel!)
(mac-h 'is-linear-functional-on (dk-pick (dk-head? 'IS-LINEAR-FUNCTIONAL-ON) "the ON hypothesis"))
(mac 'is-linear-functional)
(ass)
(qed 'linfun-on-vec-is-linfun)

;;; ====================================================================
;;; blf-app-real -- vector-taylor-proof.scm:680
;;; ====================================================================
(sp (make-wff
     '(FORALL m (FORALL g (FORALL v
        (IMPLIES (IS-BOUNDED-LINEAR-FUNCTIONAL m g) (IMPLIES (IN v (VEC m))
           (IN (g v) RR))))))))
(dk-peel!)
(rhb-app-real! '(IS-BOUNDED-LINEAR-FUNCTIONAL IS-LINEAR-FUNCTIONAL))
(qed 'blf-app-real)

;;; ====================================================================
;;; bdd-linfun-abs-real -- norm-as-sup-proof.scm:86
;;; ====================================================================
(sp (make-wff
     '(FORALL m (FORALL f (FORALL x
        (IMPLIES (IS-BOUNDED-LINEAR-FUNCTIONAL m f) (IMPLIES (IN x (VEC m))
           (IN (abs (f x)) RR))))))))
(dk-peel!)
(rhb-app-real! '(IS-BOUNDED-LINEAR-FUNCTIONAL IS-LINEAR-FUNCTIONAL))
(qed 'bdd-linfun-abs-real)

;;; ====================================================================
;;; linfun-app-abs-real -- hahn-banach-full-proof.scm:130
;;; ====================================================================
(sp (make-wff
     '(FORALL m (FORALL t (FORALL g (FORALL w_
        (IMPLIES (IS-LINEAR-FUNCTIONAL-ON m t g) (IMPLIES (IN w_ t)
           (IN (abs (g w_)) RR)))))))))
(dk-peel!)
(rhb-app-real! '(IS-LINEAR-FUNCTIONAL-ON))
(qed 'linfun-app-abs-real)

;;; ====================================================================
;;; abs-nonneg-le -- norm-as-sup-proof.scm:234
;;; `subst' rewrites LEFT TO RIGHT and only in the GOAL, so the equation is
;;; used flipped: a -> abs(a) turns the goal into the hypothesis.
;;; ====================================================================
(sp (make-wff
     '(FORALL a (FORALL c (IMPLIES (IN a RR) (IMPLIES (<= 0 a)
        (IMPLIES (<= (abs a) c) (<= a c))))))))
(dk-peel!)
(let ((rhb-a (cadr (dk-goal))))
  (dk-fact! 'rr-abs-of-nonneg rhb-a)
  (subst (dk-fact! 'eq-sym (list 'abs rhb-a) rhb-a))
  (ass))
(qed 'abs-nonneg-le)

;;; ====================================================================
;;; rr-mul-le-right -- vector-taylor-proof.scm:689
;;; rr-leq-mul-nonneg is an arithmetic-base axiom with a CONJUNCTIVE
;;; antecedent, so each AND is `have!'d whole before the citation.
;;; ====================================================================
(sp (make-wff
     '(FORALL a (IMPLIES (IN a RR) (FORALL b (IMPLIES (IN b RR) (FORALL c (IMPLIES (IN c RR)
        (IMPLIES (<= a b) (IMPLIES (<= 0 c) (<= (* a c) (* b c))))))))))))
(dk-peel!)
(let* ((rhb-g (dk-goal))
       (rhb-a (cadr  (cadr rhb-g)))
       (rhb-c (caddr (cadr rhb-g)))
       (rhb-b (cadr  (caddr rhb-g)))
       (rhb-d (list '- rhb-b rhb-a)))
  (dk-fact! 'rr-sub-in-rr rhb-b rhb-a)
  (dk-fact! 'rr-mul-in-rr rhb-d rhb-c)
  (dk-fact! 'rr-mul-in-rr rhb-a rhb-c)
  (dk-fact! 'rr-mul-in-rr rhb-b rhb-c)
  (have! (list 'AND (list 'IN rhb-d 'RR) (list 'IN rhb-c 'RR)))
  (have! (list 'AND (list '<= 0 rhb-d) (list '<= 0 rhb-c))
         (lambda ()
           (dk-conj-close!
            (lambda ()
              (if (equal? (dk-goal) (list '<= 0 rhb-c))
                  (ass)
                  (rhb-ineq! (list '<= rhb-a rhb-b)
                             (list 'IN rhb-a 'RR) (list 'IN rhb-b 'RR)))))))
  (dk-fact! 'rr-leq-mul-nonneg rhb-d rhb-c)
  (have! (list '= (list '* rhb-d rhb-c)
                  (list '- (list '* rhb-b rhb-c) (list '* rhb-a rhb-c)))
         (lambda () (crs)))
  (rhb-ineq! (list '<= 0 (list '* rhb-d rhb-c))
             (list '= (list '* rhb-d rhb-c)
                      (list '- (list '* rhb-b rhb-c) (list '* rhb-a rhb-c)))))
(qed 'rr-mul-le-right)

;;; ====================================================================
;;; proper-subset-witness -- hahn-banach-full-proof.scm:100
;;; The contrapositive of class-extensionality.  `pbc' opens it; the inner
;;; `pbc' turns "x in b but the witness set is empty" into the very existential
;;; the outer negation denies.  `prop' sees the two as ONE atom only because
;;; the existential is READ OFF the negation (prop is not alpha-aware).
;;; ====================================================================
(sp (make-wff
     '(FORALL a (FORALL b
        (IMPLIES (SUBSET a b) (IMPLIES (NOT (= a b))
           (FORSOME x_ (AND (IN x_ b) (NOT (IN x_ a))))))))))
(dk-peel!)
(let* ((rhb-sub (dk-pick (dk-head? 'SUBSET) "SUBSET a b"))
       (rhb-aa  (cadr rhb-sub))
       (rhb-bb  (caddr rhb-sub)))
  (pbc)
  (let* ((rhb-neg (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'NOT)
                                             (pair? (cadr fm))
                                             (eq? (car (cadr fm)) 'FORSOME)))
                           "the negated existential"))
         (rhb-ex  (cadr rhb-neg)))
    (rhb-cite! 'class-extensionality (list rhb-aa rhb-bb)
      (lambda ()
        (let ((rhb-x (dk-di-var! (lambda (gg) (cadr (cadr gg))))))
          (for-each
           (lambda (rhb-leaf)
             (dk-focus! rhb-leaf)
             ;; `di' on the IFF already peels each direction's antecedent, so a
             ;; second `di' here would be an inert step (it warns "cannot
             ;; decompose"); peel only if one is still standing.
             (if (eq? (car (dk-goal)) 'IMPLIES) (di))
             (if (equal? (dk-goal) (list 'IN rhb-x rhb-bb))
                 (begin (dk-fact! 'subset-mem-fwd rhb-aa rhb-bb rhb-x) (ass))
                 (begin
                   (pbc)
                   (have! rhb-ex (lambda () (ew rhb-x) (dk-conj-close! (lambda () (ass)))))
                   (prop))))
           (dk-opened (lambda () (di)))))))
    (prop)))
(qed 'proper-subset-witness)

;;; ====================================================================
;;; FINDING -- span-add-one-superset and span-add-one-has-v are FALSE as
;;; stated (hahn-banach-full-proof.scm:63 and :71).  Both are guarded only by
;;;
;;;     (IS-SUBMODULE m t)  and  (IN v (VEC m))
;;;
;;; and IS-SUBMODULE says nothing about the module LAWS of m -- no identity, no
;;; unital action.  Their proofs need y = y (+) 0.v and v = 0 (+) 1.v, neither
;;; of which follows.  COUNTEREXAMPLE, one model for both:
;;;
;;;     VEC(m)   = {0,1}                  VZERO(m) = 0
;;;     VADD(m)  = the constant 0 on CARTESIAN(VEC,VEC)
;;;     ACT(m)   = the constant 0 on CARTESIAN(CARR(SCAL m), VEC)
;;;     VNEG(m)  = the identity on VEC     t = {0,1}     v = 1
;;;
;;; IS-SUBMODULE(m,t) holds (t subset VEC, VZERO in t, and all three closures
;;; land on 0, which is in t), and v is in VEC(m).  But
;;;     SPAN-ADD-ONE(m,t,v) = { y in VEC(m) : some x in t, r in RR,
;;;                             y = VADD(x, ACT(r,v)) } = {0},
;;; so t = {0,1} is NOT a subset of it (span-add-one-superset fails) and
;;; v = 1 is NOT in it (span-add-one-has-v fails).
;;;
;;; The GUARDED forms -- both with (IS-NORMED-VECTOR-SPACE m) added, exactly as
;;; span-add-one-submodule already carries it -- are true and provable from
;;; span-add-one-membership (theorem-library/rake-algebra.scm), nvs-act-zero
;;; and nvs-act-unital + nvs-scal-one.  Changing the statement is the USER's
;;; call, so nothing is proven here: the two citers (hahn-banach-full-proof.scm
;;; and, through it, norm-as-sup-proof.scm) both carry IS-NORMED-VECTOR-SPACE
;;; in context at the citation, so adding the guard costs them nothing.
;;; ====================================================================

;;; Topics, carried over from the retired support sites (integrator, 2026-09-19).
(topic! 'proper-subset-witness 'analysis)
(topic! 'extends-on-trans 'analysis)
(topic! 'vnrm-nonneg 'analysis)
(topic! 'linfun-app-abs-real 'analysis)
(topic! 'bdd-linfun-abs-real 'analysis)
(topic! 'linfun-on-vec-is-linfun 'analysis)
(topic! 'abs-nonneg-le 'analysis)
(topic! 'blf-app-real 'analysis)
(topic! 'rr-mul-le-right 'analysis)
