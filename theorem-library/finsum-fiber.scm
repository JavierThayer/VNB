;;; finsum-fiber.scm -- FIBERED FUBINI: group the terms of a finite sum by the
;;; fibers of an arbitrary map, and the CARTESIAN projection brick it needs.
;;;
;;;   ag abelian group;  S, T finite sets;  phi : S -> T;  f : S -> CARR(ag)
;;;
;;;      SUM_{x in S} f(x)  =  SUM_{t in T} SUM_{x in S, phi(x) = t} f(x)
;;;
;;; WHY IT EXISTS.  `finsum-fubini' interchanges two sums over a CARTESIAN
;;; PRODUCT: the inner index set is the SAME for every outer index.  Every
;;; convolution-style product needs the other shape, where the inner index set
;;; DEPENDS on the outer one -- the fiber phi^-1(t).  Concretely, the
;;; convolution of the monoid algebra A[M] (structure-library/polynomial.scm)
;;;
;;;      (f*g)(x) = SUM_{(p,q) in supp f x supp g,  p.q = x}  f(p) g(q)
;;;
;;; is a sum over a fiber of the multiplication map, and the associativity of
;;; convolution (monalg-mul-assoc, the one asserted law behind monalg-is-ring)
;;; is exactly the statement that the triple sum over
;;; { (p,q,r) : p.q.r = x } can be grouped by (p.q, r) or by (p, q.r) and
;;; the two agree.  `finsum-fubini' cannot say that; this can.  It is also the
;;; general "sum over a partition" principle: any equivalence relation with
;;; finitely many classes is the fiber decomposition of the quotient map.
;;;
;;; THE PROOF, and it needs no new axiom.  Let G : S x T -> CARR(ag) be the
;;; INDICATOR-WEIGHTED summand
;;;
;;;      G(x,t) = f(x)  if phi(x) = t,   IDEN(ag) otherwise.
;;;
;;;   (1) For fixed x, SUM_{t in T} G(x,t) = f(x): every term but t = phi(x)
;;;       is the identity, so `finsum-single-support' collapses the sum.
;;;       Hence (finsum-congruence) SUM_x SUM_t G = SUM_x f.
;;;   (2) `finsum-fubini' interchanges the two sums.
;;;   (3) For fixed t, the summand x |-> G(x,t) is IDEN(ag) at every x OUTSIDE
;;;       the fiber, so `finsum-embed' restricts the sum over S to the sum over
;;;       the fiber, where (finsum-congruence again) it IS f.
;;;
;;; So the fibered form is a THEOREM of the rectangular one, not a strengthening
;;; of the trust base: it costs only what finsum-fubini, -single-support,
;;; -embed, -congruence and card-subset-nn already cost.
;;;
;;; THE BRICK: cartesian-nth.  Typing G at all needs "z in X x Y implies
;;; NTH(1,z) in X and NTH(2,z) in Y", which the tree did not have -- which is
;;; why `matmul-assoc-summand-type' (structure-library/matrix.scm:637), the one
;;; earlier lambda-on-a-product typing, is an ASSERTED support rather than a
;;; proof.  It is proved here from `cartesian-decompose', the procedural macete
;;; that IS the membership schema of the product (library.scm:721).
;;;
;;; WARRANT ON A KERNEL MACETE.  `cartesian-decompose' is installed by
;;; `install-macete!', not by `add-axiom!', so it carries no provenance
;;; and no warrant: every proof that uses it bills `trust: none' for a schema
;;; library.scm's own comment calls an axiom.  It is warranted `well-known' below
;;; so this file's bills read honestly.  The BETTER answer is almost certainly
;;;
;;;     (register-provenance! 'cartesian-decompose 'definitional)
;;;
;;; -- the schema says what the cartesian product IS, exactly as the ordinal
;;; axioms say what the ordinals are -- but the primitive shelf grows only by an
;;; explicit foundational decision (CLAUDE.md), so that line is NOT taken here.
;;;
;;; Dependencies: finsum-fubini (finsum-fubini-c), finsum-additive
;;; (finsum-congruence, finsum-embed), matrix (finsum-single-support),
;;; prod-of-sums (card-subset-nn), subtype-laws (group-identity-in,
;;; abelian-group-is-group), fun-apply-type-proof (fun-apply-type-c).

;;; (the `warrant!' for cartesian-decompose MOVED 2026-09-14 to theorem-library/founder-warrants.scm:
;;; matof-in-mat.scm, which loads before this file, bills it, and a warrant registered
;;; after the citing qed reads as `trust: none' at load time.)

;;; -----------------------------------------------------------------------
;;; local driver helpers (ffb- prefix)
;;; -----------------------------------------------------------------------

(define (ffb-tf v type body) (list 'FORALL v (list 'IMPLIES type body)))
(define (ffb-tfin S body)                 ; finiteness premises CURRIED, so a
  (list 'FORALL S (list 'IMPLIES (list 'IN S 'SET)   ; forward `fact' detaches
    (list 'IMPLIES (list 'IN (list 'CARD S) 'NN) body))))  ; each guard

(define (ffb-peel!)                       ; peel the FORALL/IMPLIES prefix --
  (let lp ((k 0))                         ; never a fixed count of `di's
    (if (> k 25) (error "ffb-peel!: runaway"))
    (if (memq (car (dk-goal)) '(forall implies)) (begin (di) (lp (+ k 1))))))

(define (ffb-has? e h)                    ; does expression e mention head h?
  (let walk ((e e))
    (and (pair? e)
         (or (eq? (car e) h)
             (let lp ((l e)) (and (pair? l) (or (walk (car l)) (lp (cdr l)))))))))

(define (ffb-nth*!)                       ; reduce NTH(k,[...]) to exhaustion
  (let lp ((k 0)) (if (and (< k 8) (ffb-has? (dk-goal) 'NTH)) (begin (nth-r) (lp (+ k 1))))))

(define (ffb-each-opened! thunk)          ; run thunk; close every leaf it opened
  (for-each (lambda (n) (dk-focus! n) (ass)) (dk-opened thunk)))

(define (ffb-raw form) (wff-formula (make-wff form)))

;; two-leaf AND-goal driver: b1 on the leaf whose goal is G1, b2 on the other.
;; Discriminated on the GOAL, never on the order dk-opened happens to return.
(define (ffb-and! g1 b1 b2)
  (let ((ls (dk-opened (lambda () (di)))))
    (dk-focus! (any-pred (lambda (n) (equal? (dk-goal-of n) g1)) ls)) (b1)
    (dk-focus! (any-pred (lambda (n) (not (equal? (dk-goal-of n) g1))) ls)) (b2)))

;; `if-true' / `if-false' do NOT rewrite the goal: each opens TWO leaves -- the
;; condition (resp. its negation) and the original goal with the VALUE EQUATION
;; added to the context (primitive-inferences.scm:523).  So: close the condition
;; leaf with CLOSER, then substitute the value equation into the other.
(define (ffb-if! ifterm which closer)
  (let* ((cnd   (cadr ifterm))
         (val   (if (eq? which 'true) (caddr ifterm) (cadddr ifterm)))
         (cgoal (if (eq? which 'true) cnd (list 'NOT cnd)))
         (ls    (dk-opened (lambda ()
                  (if (eq? which 'true) (if-true ifterm) (if-false ifterm))))))
    (dk-focus! (any-pred (lambda (n) (equal? (dk-goal-of n) cgoal)) ls))
    (closer)
    (dk-focus! (any-pred (lambda (n) (not (equal? (dk-goal-of n) cgoal))) ls))
    (subst (list '= ifterm val))))

;; an UNGUARDED universal with an AND antecedent peels the quantifier and lands
;; NOTHING; the antecedent comes on the next `di'.  Loop on the LANDING.
(define (ffb-di-land!)
  (let lp ((k 0))
    (if (> k 3) (error "ffb-di-land!: nothing landed"))
    (let ((l (dk-landed* (lambda () (di))))) (if (null? l) (lp (+ k 1)) l))))

;;; =====================================================================
;;; brick: the projections of a member of a cartesian product
;;; =====================================================================

(sp (make-wff '(FORALL x_ (FORALL aa (FORALL bb
   (IMPLIES (IN x_ (CARTESIAN aa bb))
     (AND (IN (NTH 1 x_) aa) (IN (NTH 2 x_) bb))))))))
;; `mac' BEFORE any `di': cartesian-decompose descends through the connectives
;; and rewrites the ANTECEDENT in place; there is no `mac-h' route, a procedural
;; macete not being a theorem the hypothesis rewriter can rebuild.
(mac 'cartesian-decompose)
(di) (di)
(let lp ((k 0))                            ; skolemize the two existentials
  (let ((ex (any-pred (dk-head? 'FORSOME) (dk-asms))))
    (if (and ex (< k 5)) (begin (dk-split! ex) (lp (+ k 1))))))
(subst (any-pred (lambda (a) (and (pair? a) (eq? (car a) '=) (eq? (cadr a) 'x_))) (dk-asms)))
(nth-r)
(ffb-each-opened! (lambda () (di)))
(qed 'cartesian-nth)
(gloss! 'cartesian-nth
  "A member of a cartesian product is the pair of its projections: z in X x Y
   implies NTH(1,z) in X and NTH(2,z) in Y.  What every typing of a lambda whose
   domain is a product needs, and what matmul-assoc-summand-type asserts.")
(topic! 'cartesian-nth 'plumbing)

;;; =====================================================================
;;; finsum-fiber
;;; =====================================================================

;; the indicator-weighted summand on S x T
(define ffb-G '(VNB-LAMBDA w_ (CARTESIAN S T)
                 (IF (= (phi (NTH 1 w_)) (NTH 2 w_)) (f (NTH 1 w_)) (IDEN ag))))
(define ffb-Gty (list 'IN ffb-G '(FUN (CARTESIAN S T) (CARR ag))))
;; the two iterated sums finsum-fubini-c relates.  The lambda binders are `i'
;; and `j' because that is what finsum-fubini's own statement uses: the landed
;; instance must match these terms SYMBOL FOR SYMBOL for `subst' to fire.
(define ffb-outerS (list 'VNB-LAMBDA 'i 'S
   (list 'FINSUM 'ag (list 'VNB-LAMBDA 'j 'T (list ffb-G '(LIST i j))) 'T)))
(define ffb-outerT (list 'VNB-LAMBDA 'j 'T
   (list 'FINSUM 'ag (list 'VNB-LAMBDA 'i 'S (list ffb-G '(LIST i j))) 'S)))
(define ffb-fiber '(SEP s_ S (= (phi s_) t_)))
(define ffb-target (list 'VNB-LAMBDA 't_ 'T (list 'FINSUM 'ag 'f ffb-fiber)))
(define ffb-eqF (list '= (list 'FINSUM 'ag ffb-outerS 'S) (list 'FINSUM 'ag ffb-outerT 'T)))
;; the summand of the inner sum, at a fixed source point / a fixed fiber index
(define (ffb-lamj zv) (list 'VNB-LAMBDA 'j 'T
   (list 'IF (list '= (list 'phi zv) 'j) (list 'f zv) '(IDEN ag))))
(define (ffb-lami tv) (list 'VNB-LAMBDA 'i 'S
   (list 'IF (list '= '(phi i) tv) '(f i) '(IDEN ag))))
(define (ffb-fib tv)  (list 'SEP 's_ 'S (list '= '(phi s_) tv)))

;; (ffb-lami tv) is a function S -> CARR(ag): it is f inside the fiber over tv
;; and IDEN(ag) outside it.  Wanted TWICE -- once inside the restriction lane
;; (3), and once by the pointwise typing the restated `finsum-congruence' asks
;; of its first summand at the assembly.  Returns the lambda.  Needs in context:
;; (IN S SET), f in FUN(S, CARR ag), IDEN(ag) in CARR(ag), (IN tv T).
(define (ffb-lami-type! tv)
  (let ((li (ffb-lami tv)))
    (have! (list 'IN li '(FUN S (CARR ag)))
      (lambda ()
        (for-each
          (lambda (l) (dk-focus! l)
            (if (equal? (dk-goal-of l) '(in s set)) (ass)
                (let* ((iv (cadr (dk-landed-1 (lambda () (di)))))
                       (it (list 'IF (list '= (list 'phi iv) tv) (list 'f iv) '(IDEN ag))))
                  (fact 'fun-apply-type-c 'f 'S '(CARR ag) iv)
                  (use-em (cadr it)
                    (lambda () (ffb-if! it 'true  (lambda () (ass))) (ass))
                    (lambda () (ffb-if! it 'false (lambda () (ass))) (ass))))))
          (dk-opened (lambda () (lam-t))))))
    li))

(sp (make-wff
  (ffb-tf 'ag '(IS-ABELIAN-GROUP ag)
   (ffb-tfin 'S (ffb-tfin 'T
    (ffb-tf 'phi '(IN phi (FUN S T))
     (ffb-tf 'f '(IN f (FUN S (CARR ag)))
       (list '= '(FINSUM ag f S) (list 'FINSUM 'ag ffb-target 'T)))))))))
(ffb-peel!)
(fact 'abelian-group-is-group 'ag)
(fact 'group-identity-in 'ag)             ; IDEN(ag) in CARR(ag)

;;; ---- G is a function on S x T ---------------------------------------
(have! ffb-Gty
 (lambda ()
   (for-each
     (lambda (l)
       (dk-focus! l)
       (if (equal? (dk-goal-of l) '(in (cartesian s t) set))
           (begin (mac 'cartesian-set-iff) (ffb-each-opened! (lambda () (di))))
           ;; lam-t's pointwise leaf binds a FRESH variable -- read it off the
           ;; landed typing, never off the lambda's printed binder name.
           (let ((wv (cadr (dk-landed-1 (lambda () (di))))))
             (fact 'cartesian-nth wv 'S 'T)
             (dk-split! (list 'AND (list 'IN (list 'NTH 1 wv) 'S)
                                   (list 'IN (list 'NTH 2 wv) 'T)))
             (fact 'fun-apply-type-c 'f 'S '(CARR ag) (list 'NTH 1 wv))
             (let ((it (list 'IF (list '= (list 'phi (list 'NTH 1 wv)) (list 'NTH 2 wv))
                             (list 'f (list 'NTH 1 wv)) '(IDEN ag))))
               (use-em (cadr it)
                 (lambda () (ffb-if! it 'true  (lambda () (ass))) (ass))
                 (lambda () (ffb-if! it 'false (lambda () (ass))) (ass)))))))
     (dk-opened (lambda () (lam-t))))))

;;; ---- the interchange -------------------------------------------------
(fact 'finsum-fubini-c 'ag 'S 'T ffb-G)

;;; ---- (1) the inner sum over T collapses to f -------------------------
(have! (list 'FORALL 'z (list 'IMPLIES '(IN z S) (list '= '(f z) (list ffb-outerS 'z))))
 (lambda ()
   (let* ((zv (cadr (dk-landed-1 (lambda () (di)))))
          (lj (ffb-lamj zv)))
     (lam-b) (ffb-nth*!)
     (fact 'fun-apply-type-c 'phi 'S 'T zv)
     (fact 'fun-apply-type-c 'f 'S '(CARR ag) zv)
     (have! (list 'IN lj '(FUN T (CARR ag)))
       (lambda ()
         (for-each
           (lambda (l) (dk-focus! l)
             (if (equal? (dk-goal-of l) '(in t set)) (ass)
                 (let* ((jv (cadr (dk-landed-1 (lambda () (di)))))
                        (it (list 'IF (list '= (list 'phi zv) jv) (list 'f zv) '(IDEN ag))))
                   (use-em (cadr it)
                     (lambda () (ffb-if! it 'true  (lambda () (ass))) (ass))
                     (lambda () (ffb-if! it 'false (lambda () (ass))) (ass))))))
           (dk-opened (lambda () (lam-t))))))
     ;; every index but phi(zv) contributes the identity
     (have! (list 'FORALL 'j (list 'IMPLIES '(IN j T)
              (list 'IMPLIES (list 'NOT (list '= 'j (list 'phi zv)))
                    (list '= (list lj 'j) '(IDEN ag)))))
       (lambda ()
         (let ((jv (cadr (dk-landed-1 (lambda () (di))))))
           (di)
           (lam-b)
           (let ((it (list 'IF (list '= (list 'phi zv) jv) (list 'f zv) '(IDEN ag))))
             (ffb-if! it 'false
               (lambda ()                       ; goal NOT(phi(zv) = jv); context
                 (di)                           ; has NOT(jv = phi(zv)) -- `=' has
                 (have! (list '= jv (list 'phi zv))   ; no symmetry theorem, so
                        (lambda () (subst (list '= (list 'phi zv) jv)) (rfl)))
                 (ai (list 'NOT (list '= jv (list 'phi zv))))))
             (rfl)))))
     (fact 'finsum-single-support 'ag 'T lj (list 'phi zv))
     (subst (list '= (list 'FINSUM 'ag lj 'T) (list lj (list 'phi zv))))
     (lam-b)
     (ffb-if! (list 'IF (list '= (list 'phi zv) (list 'phi zv)) (list 'f zv) '(IDEN ag))
              'true (lambda () (rfl)))
     (rfl))))

;;; ---- (3) the inner sum over S restricts to the fiber -----------------
(have! (list 'FORALL 'zt (list 'IMPLIES '(IN zt T)
         (list '= (list ffb-outerT 'zt) (list ffb-target 'zt))))
 (lambda ()
   (let ((tv (cadr (dk-landed-1 (lambda () (di))))))
     (lam-b) (ffb-nth*!)
     (let ((fb (ffb-fib tv)) (li (ffb-lami tv)))
       ;; the fiber is a finite subset of S
       (have! (list 'IN fb 'SET) (lambda () (sep-set) (ass)))
       (have! (list 'FORALL 'z (list 'IMPLIES (list 'IN 'z fb) (list 'IN 'z 'S)))
         (lambda () (let ((zv (cadr (dk-landed-1 (lambda () (di))))))
                      (sep-me (list 'IN zv fb)) (ass))))
       ;; card-subset-nn takes AND antecedents, which `fact' will not split
       (have! (list 'AND '(IN S SET) '(IN (CARD S) NN))
              (lambda () (ffb-and! '(in s set) (lambda () (ass)) (lambda () (ass)))))
       (have! (list 'AND (list 'IN fb 'SET)
                (list 'FORALL 'z (list 'IMPLIES (list 'IN 'z fb) (list 'IN 'z 'S))))
              (lambda () (ffb-and! (ffb-raw (list 'IN fb 'SET))
                                   (lambda () (ass)) (lambda () (ass)))))
       (fact 'card-subset-nn 'S fb)
       (have! (list 'SUBSET fb 'S)
         (lambda () (mac 'subset-def)
                    (let ((zv (cadr (dk-landed-1 (lambda () (di))))))
                      (sep-me (list 'IN zv fb)) (ass))))
       ;; the summand is a function S -> CARR(ag)
       (ffb-lami-type! tv)
       ;; ... which is the identity at every index OUTSIDE the fiber
       (have! (list 'FORALL 'z (list 'IMPLIES (list 'AND '(IN z S) (list 'NOT (list 'IN 'z fb)))
                                     (list '= (list li 'z) '(IDEN ag))))
         (lambda ()
           (let* ((land (ffb-di-land!))
                  (conj (any-pred (dk-head? 'AND) land))
                  (zv   (cadr (cadr conj))))
             (dk-split! conj)
             (let ((it (list 'IF (list '= (list 'phi zv) tv) (list 'f zv) '(IDEN ag))))
               (use-em (cadr it)
                 (lambda ()                        ; phi(zv) = tv puts zv IN the
                   (have! (list 'IN zv fb)         ; fiber, contradicting the
                     (lambda () (ffb-each-opened! (lambda () (sep-mi)))))  ; premise
                   (ai (list 'NOT (list 'IN zv fb))))
                 (lambda ()
                   (lam-b)
                   (ffb-if! it 'false (lambda () (ass)))
                   (rfl)))))))
       ;; ... and IS f on the fiber
       (have! (list 'FORALL 'z (list 'IMPLIES (list 'IN 'z fb) (list '= (list li 'z) '(f z))))
         (lambda ()
           (let ((zv (cadr (dk-landed-1 (lambda () (di))))))
             (sep-me (list 'IN zv fb))
             (lam-b)
             (ffb-if! (list 'IF (list '= (list 'phi zv) tv) (list 'f zv) '(IDEN ag))
                      'true (lambda () (ass)))
             (rfl))))
       (fact 'finsum-embed 'ag fb 'S li)
       ;; the restated finsum-congruence (2026-09-17) wants its FIRST summand
       ;; typed POINTWISE on the index set: li is a function on S and the fiber
       ;; is a subset of S, so it is one fun-apply-type-c per member.
       (have! (list 'FORALL 'z (list 'IMPLIES (list 'IN 'z fb)
                                     (list 'IN (list li 'z) '(CARR ag))))
         (lambda ()
           (let ((zv (cadr (dk-landed-1 (lambda () (di))))))
             (sep-me (list 'IN zv fb))
             (fact 'fun-apply-type-c li 'S '(CARR ag) zv)
             (ass))))
       (fact 'finsum-congruence 'ag fb li 'f)
       (subst (list '= (list 'FINSUM 'ag li 'S) (list 'FINSUM 'ag li fb)))
       (ass)))))

;;; ---- assembly --------------------------------------------------------
;; the pointwise typings the restated finsum-congruence asks of its FIRST
;; summand.  For f it is the premise f in FUN(S, CARR ag), read off one point at
;; a time; for the inner-sum-over-S family it is finsum-type applied to the
;; lambda ffb-lami-type! types -- which is what that family beta-reduces to.
(have! '(FORALL z (IMPLIES (IN z S) (IN (f z) (CARR ag))))
  (lambda ()
    (let ((zv (cadr (dk-landed-1 (lambda () (di))))))
      (fact 'fun-apply-type-c 'f 'S '(CARR ag) zv)
      (ass))))
(have! (list 'FORALL 'z (list 'IMPLIES '(IN z T)
                              (list 'IN (list ffb-outerT 'z) '(CARR ag))))
  (lambda ()
    (let ((tv (cadr (dk-landed-1 (lambda () (di))))))
      (lam-b) (ffb-nth*!)
      (let ((li (ffb-lami-type! tv)))
        (fact 'finsum-type 'ag 'S li)
        (ass)))))
(fact 'finsum-congruence 'ag 'S 'f ffb-outerS)
(fact 'finsum-congruence 'ag 'T ffb-outerT ffb-target)
(subst (list '= (list 'FINSUM 'ag 'f 'S) (list 'FINSUM 'ag ffb-outerS 'S)))
(subst ffb-eqF)
(ass)
(qed 'finsum-fiber)
(gloss! 'finsum-fiber
  "Fibered Fubini: a finite sum may be grouped by the fibers of any map out of
   its index set.  For phi : S -> T with S and T finite and f valued in an
   abelian group, SUM_{x in S} f(x) = SUM_{t in T} SUM_{phi(x)=t} f(x).  The
   dependent-index Fubini that convolution products need, of which
   finsum-fubini (constant fiber, S = X x Y, phi the projection) is the special
   case.")
(topic! 'finsum-fiber 'algebra)
