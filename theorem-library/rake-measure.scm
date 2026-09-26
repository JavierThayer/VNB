;;; rake-measure.scm -- rake batch 5, batch W: the light end of measure theory.
;;;
;;; TWO of the seven assigned supports are PROVEN here, `modulo 0':
;;;
;;;   sigma-generated-is-sigma-algebra   structure-library/measure.scm:231
;;;   measurable-map-compose             structure-library/measure.scm:451
;;;
;;; The other five stop against the SAME WALL and it is not a measure-theoretic
;;; one: THE EXTENDED REALS HAVE NO ARITHMETIC AND NO ORDER.  The inventory is
;;; in the block "WHAT THE OTHER FIVE NEED" at the foot of this file, and it is
;;; the batch's main output.  Nothing below cites an asserted fact.
;;;
;;; WHAT THIS FILE ALSO INSTALLS, and why.  sigma-algebra.scm asserts NOTHING
;;; (its own header lists the consequences as "NEXT, not stated"), so every
;;; proof about a sigma-algebra has to unfold IS-SIGMA-ALGEBRA by hand -- and
;;; `mac-h' is destructive, so the hypothesis is gone by the second use.  The
;;; twelve lemmas below are the `stl--project!' treatment (subtype-laws.scm)
;;; applied to IS-SIGMA-ALGEBRA, SIGMA-GENERATED and IS-MEASURABLE-MAP: four
;;; projections, one intro and the three SIGMA-GENERATED read-offs.  They are
;;; what makes the two target proofs short, and the next measure-theory proof
;;; will want them too.
;;;
;;;   sigma-algebra-ambient-set         IS-SIGMA-ALGEBRA(omega,cA) => omega in SET
;;;   sigma-algebra-whole-in            ... => omega in cA
;;;   sigma-algebra-complement-closed   ... a in cA => omega \ a in cA
;;;   sigma-algebra-union-closed        ... f in FUN(NN,cA) => union_n f(n) in cA
;;;   sigma-generated-in-power          a in SIGMA-GENERATED(omega,cE) => a in POWER(omega)
;;;   sigma-generated-in-every          ... => a lies in every sigma-algebra over cE
;;;   sigma-generated-intro             the converse of the two together
;;;   measurable-map-source-algebra     the four IS-MEASURABLE-MAP conjuncts,
;;;   measurable-map-target-algebra       projected one at a time, plus
;;;   measurable-map-in-fun               the intro rule that rebuilds the
;;;   measurable-map-preimage             predicate from them
;;;   measurable-map-intro
;;;
;;; CITATIONS and their load positions (0-based over the quoted file names in
;;; load.scm).  Everything mathematical is at 198 or below:
;;;
;;;   base theory (library.scm, `primitive'):  subset-def, class-extensionality,
;;;       fun-codomain-iff, complement-in-membership, complement-in-set-closure,
;;;       power-set-membership
;;;   equality-symmetry            theorem-library/axioms.scm            15
;;;   nn-is-set                    number-systems.scm                    34
;;;   IS-SIGMA-ALGEBRA (def iff)   structure-library/sigma-algebra.scm   50
;;;   sigma-generated-membership   structure-library/measure.scm        123
;;;   IS-MEASURABLE-MAP (def iff)  structure-library/measure.scm        123
;;;   prop                         prop.scm                             143
;;;   fun-apply-type-c             theorem-library/fun-apply-type-proof  162
;;;   compose-apply, compose-type  theorem-library/compose-apply-proof   163
;;;   power-whole-in, power-mem-in,
;;;   power-mem-intro, power-mem-sethood
;;;                                theorem-library/discrete-space.scm   198
;;;
;;; LOAD WINDOW [199, end).  lo = 199: discrete-space (198) is the latest thing
;;; cited.  There is no hi -- neither target support is on any bill and nothing
;;; in the library cites either (they are in DEBT-BUNDLE.md section 3, the
;;; off-bill two thirds).
;;;
;;; RETIRE, after this file is wired in:
;;;   structure-library/measure.scm:231-246   sigma-generated-is-sigma-algebra
;;;                                           (support + warrant! + topic! + gloss!)
;;;   structure-library/measure.scm:451-465   measurable-map-compose
;;;                                           (support + warrant! + topic! + gloss!)
;;;
;;; Helper prefix: r5w-.

;;; -----------------------------------------------------------------------
;;; file-local kit
;;; -----------------------------------------------------------------------

;;; Split every top-level AND among the OPEN leaves, to exhaustion.  A
;;; def-predicate body is a right-nested AND tower, so one `di' per level.
(define (r5w-split-ands!)
  (let lp ()
    (let ((m (filter (lambda (l) (let ((g (dk-goal-of l)))
                                   (and (pair? g) (eq? (car g) 'AND))))
                     (proof-leaves))))
      (if (pair? m) (begin (dk-focus! (car m)) (di) (lp))))))

;;; Focus the first open leaf whose GOAL satisfies PRED; ERROR if there is none
;;; (a focus helper that returns #f and leaves focus put hides every later bug).
(define (r5w-focus! pred what)
  (let ((ls (filter (lambda (l) (pred (dk-goal-of l))) (proof-leaves))))
    (if (null? ls)
        (error "r5w-focus!: no open leaf matching" what)
        (begin (dk-focus! (car ls)) (car ls)))))

;;; "the formula mentions the symbol H anywhere".  The two closure conjuncts of
;;; IS-SIGMA-ALGEBRA are both FORALL/IMPLIES with an IN consequent, so the head
;;; does not discriminate them; COMPLEMENT-IN vs BIG-UNION does.
(define (r5w-mentions? h)
  (lambda (f) (let walk ((x f))
                (cond ((eq? x h) #t)
                      ((pair? x) (or (walk (car x)) (walk (cdr x))))
                      (#t #f)))))

;;; -----------------------------------------------------------------------
;;; 1.  The IS-SIGMA-ALGEBRA projections.
;;;
;;; Each is `mac-h' the defining iff, split the tower, cite the conjunct.  The
;;; unfold is destructive, which is exactly why these exist: a caller that
;;; needs two conjuncts cannot get them by unfolding twice.
;;; -----------------------------------------------------------------------

(sp (make-wff (forall-guarded '(omega cA) '((IS-SIGMA-ALGEBRA omega cA))
                '(IN omega SET))))
(dk-peel!)
(dk-split! (dk-landed-1
            (lambda () (mac-h 'IS-SIGMA-ALGEBRA '(IS-SIGMA-ALGEBRA omega cA)))))
(ass)
(qed 'sigma-algebra-ambient-set)
(topic! 'sigma-algebra-ambient-set 'set-quotient)

(sp (make-wff (forall-guarded '(omega cA) '((IS-SIGMA-ALGEBRA omega cA))
                '(IN omega cA))))
(dk-peel!)
(dk-split! (dk-landed-1
            (lambda () (mac-h 'IS-SIGMA-ALGEBRA '(IS-SIGMA-ALGEBRA omega cA)))))
(ass)
(qed 'sigma-algebra-whole-in)
(topic! 'sigma-algebra-whole-in 'set-quotient)

(sp (make-wff (forall-guarded '(omega cA a_)
                '((IS-SIGMA-ALGEBRA omega cA) (IN a_ cA))
                '(IN (COMPLEMENT-IN omega a_) cA))))
(dk-peel!)
(dk-split! (dk-landed-1
            (lambda () (mac-h 'IS-SIGMA-ALGEBRA '(IS-SIGMA-ALGEBRA omega cA)))))
(dk-apply! (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                     ((r5w-mentions? 'complement-in) f)))
                    "the complement universal")
           'a_)
(ass)
(qed 'sigma-algebra-complement-closed)
(topic! 'sigma-algebra-complement-closed 'set-quotient)

(sp (make-wff (forall-guarded '(omega cA f_)
                '((IS-SIGMA-ALGEBRA omega cA) (IN f_ (FUN NN cA)))
                '(IN (BIG-UNION n_ NN (f_ n_)) cA))))
(dk-peel!)
(dk-split! (dk-landed-1
            (lambda () (mac-h 'IS-SIGMA-ALGEBRA '(IS-SIGMA-ALGEBRA omega cA)))))
(dk-apply! (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                     ((r5w-mentions? 'big-union) f)))
                    "the countable-union universal")
           'f_)
(ass)
(qed 'sigma-algebra-union-closed)
(topic! 'sigma-algebra-union-closed 'set-quotient)

;;; -----------------------------------------------------------------------
;;; 2.  The SIGMA-GENERATED read-offs.
;;;
;;; SIGMA-GENERATED is a def-functoid, so `mac-h' cannot unfold it in an
;;; ASSUMPTION by its own name; measure.scm states the membership iff beside it
;;; (`sigma-generated-membership', stamped definitional) for exactly that
;;; reason, and `mac-h' DOES rebuild a rule from that theorem.  These three
;;; turn the iff into the elim/elim/intro triple a driver wants.
;;; -----------------------------------------------------------------------

(sp (make-wff '(FORALL omega (FORALL cE (FORALL a_
     (IMPLIES (IN a_ (SIGMA-GENERATED omega cE)) (IN a_ (POWER omega))))))))
(dk-peel!)
(dk-split! (dk-landed-1
            (lambda () (mac-h 'sigma-generated-membership
                              '(IN a_ (SIGMA-GENERATED omega cE))))))
(ass)
(qed 'sigma-generated-in-power)
(topic! 'sigma-generated-in-power 'set-quotient)

;;; The antecedents are CURRIED, not conjoined, so `fact' detaches them one at
;;; a time against the live context (the ideal.scm:73 convention).  The
;;; theorem's own quantified body has the AND form, hence the `have!'.
(sp (make-wff '(FORALL omega (FORALL cE (FORALL a_ (FORALL cB_
     (IMPLIES (IN a_ (SIGMA-GENERATED omega cE))
       (IMPLIES (IS-SIGMA-ALGEBRA omega cB_)
         (IMPLIES (SUBSET cE cB_) (IN a_ cB_))))))))))
(dk-peel!)
(dk-split! (dk-landed-1
            (lambda () (mac-h 'sigma-generated-membership
                              '(IN a_ (SIGMA-GENERATED omega cE))))))
(have! '(AND (IS-SIGMA-ALGEBRA omega cB_) (SUBSET cE cB_)))
(dk-apply! (dk-pick (dk-head? 'FORALL) "the sigma-algebra universal") 'cB_)
(ass)
(qed 'sigma-generated-in-every)
(topic! 'sigma-generated-in-every 'set-quotient)

(sp (make-wff '(FORALL omega (FORALL cE (FORALL a_
     (IMPLIES (IN a_ (POWER omega))
       (IMPLIES (FORALL cB_
                  (IMPLIES (AND (IS-SIGMA-ALGEBRA omega cB_) (SUBSET cE cB_))
                           (IN a_ cB_)))
                (IN a_ (SIGMA-GENERATED omega cE)))))))))
(dk-peel!)
(mac 'sigma-generated-membership)
(dk-conj-close! (lambda () (ass)))
(qed 'sigma-generated-intro)
(topic! 'sigma-generated-intro 'set-quotient)

;;; -----------------------------------------------------------------------
;;; 3.  sigma-generated-is-sigma-algebra.
;;;
;;; The intersection of all sigma-algebras over cE is one.  Five conjuncts, and
;;; every one of them is "check it in POWER(omega), then check it in each cB":
;;; that is what the two read-offs above say, so each conjunct is two `have!'
;;; lanes and one sigma-generated-intro.
;;;
;;; Note what is NOT needed: `IS-SIGMA-ALGEBRA(omega, POWER omega)'.  The first
;;; component of the membership iff is a POWER membership one proves directly
;;; (complement-in-set-closure and the BIG-UNION kernel rules do it), so the
;;; family never has to be shown non-empty.
;;; -----------------------------------------------------------------------

(sp (make-wff (forall-guarded '(omega cE)
                '((IN omega SET) (SUBSET cE (POWER omega)))
    '(IS-SIGMA-ALGEBRA omega (SIGMA-GENERATED omega cE)))))
(dk-peel!)
(mac 'IS-SIGMA-ALGEBRA)
(r5w-split-ands!)

;;; (1) omega is a set -- the hypothesis.
(r5w-focus! (lambda (g) (equal? g '(IN omega SET))) "omega in SET")
(ass)

;;; (2) the generated algebra is a family of subsets of omega.
(r5w-focus! (dk-head? 'SUBSET) "the inclusion conjunct")
(mac 'subset-def)
(let ((z (cadr (car (dk-peel!)))))
  (fact 'sigma-generated-in-power 'omega 'cE z)
  (ass))

;;; (3) omega itself is in it.
(r5w-focus! (lambda (g) (equal? g '(IN omega (SIGMA-GENERATED omega cE))))
            "omega in the generated algebra")
(have! '(IN omega (POWER omega))
       (lambda () (fact 'power-whole-in 'omega) (ass)))
(have! '(FORALL cB_ (IMPLIES (AND (IS-SIGMA-ALGEBRA omega cB_) (SUBSET cE cB_))
                             (IN omega cB_)))
       (lambda ()
         ;; The binder cB_ is unguarded with an AND antecedent, so `di' peels
         ;; the quantifier and lands NOTHING; dk-peel! loops to the landing.
         ;; Read the eigenvariable off the landed conjunction, never off the
         ;; binder spelling.
         (let* ((landed (dk-peel!))
                (bb (caddr (cadr (car landed)))))
           (dk-split! (car landed))
           (fact 'sigma-algebra-whole-in 'omega bb)
           (ass))))
(fact 'sigma-generated-intro 'omega 'cE 'omega)
(ass)

;;; (4) closed under complements.
(r5w-focus! (r5w-mentions? 'complement-in) "the complement conjunct")
(let* ((r5w-c4 (dk-peel!))
       (aa (cadr (car r5w-c4)))
       (ca (list 'COMPLEMENT-IN 'omega aa))
       (sub (list 'FORALL 'z_ (list 'IMPLIES (list 'IN 'z_ ca) '(IN z_ omega))))
       (uni (list 'FORALL 'cB_
                  (list 'IMPLIES '(AND (IS-SIGMA-ALGEBRA omega cB_) (SUBSET cE cB_))
                        (list 'IN ca 'cB_)))))
  ;; omega \ a is a set and is included in omega, so it is in POWER(omega).
  (have! (list 'IN ca 'SET)
         (lambda () (fact 'complement-in-set-closure 'omega aa) (ass)))
  (have! sub
         (lambda ()
           (let ((zz (cadr (car (dk-peel!)))))
             (fact 'complement-in-membership 'omega aa zz)
             (prop))))
  (fact 'power-mem-intro 'omega ca)
  ;; and every sigma-algebra over cE holds it, being closed under complements.
  (have! uni
         (lambda ()
           (let* ((l2 (dk-peel!))
                  (bb (caddr (cadr (car l2)))))
             (dk-split! (car l2))
             (fact 'sigma-generated-in-every 'omega 'cE aa bb)
             (fact 'sigma-algebra-complement-closed 'omega bb aa)
             (ass))))
  ;; The POWER typing is landed BEFORE this citation on purpose: instantiation
  ;; owes definedness for the instantiating term, and an `IN' hypothesis
  ;; mentioning it outside a binder is the certificate.
  (fact 'sigma-generated-intro 'omega 'cE ca)
  (ass))

;;; (5) closed under countable unions.  The only conjunct with real work: the
;;; union's sethood and its inclusion in omega both go through the BIG-UNION
;;; kernel rules (`bu-set', `bu-me'), and the per-cB half needs the family
;;; RETYPED into FUN(NN, cB) -- there is no codomain-widening lemma in the
;;; tree, so it is rebuilt through fun-codomain-iff, goal side.
(r5w-focus! (r5w-mentions? 'big-union) "the countable-union conjunct")
(let* ((r5w-c5 (dk-peel!))
       (ff (cadr (car r5w-c5)))
       (gg '(SIGMA-GENERATED omega cE))
       (bu (list 'BIG-UNION 'n_ 'NN (list ff 'n_)))
       (ptw (list 'FORALL 'n_ (list 'IMPLIES '(IN n_ NN)
                                    (list 'IN (list ff 'n_) '(POWER omega)))))
       (sub (list 'FORALL 'z_ (list 'IMPLIES (list 'IN 'z_ bu) '(IN z_ omega))))
       (uni (list 'FORALL 'cB_
                  (list 'IMPLIES '(AND (IS-SIGMA-ALGEBRA omega cB_) (SUBSET cE cB_))
                        (list 'IN bu 'cB_)))))
  ;; every term of the family is a subset of omega
  (have! ptw
         (lambda ()
           (let ((nv (cadr (car (dk-peel!)))))
             (fact 'fun-apply-type-c ff 'NN gg nv)
             (fact 'sigma-generated-in-power 'omega 'cE (list ff nv))
             (ass))))
  ;; the union is a set: bu-set opens (IN NN SET) and the pointwise sethood
  (have! (list 'IN bu 'SET)
         (lambda ()
           (for-each
            (lambda (l)
              (dk-focus! l)
              (if (equal? (dk-goal) '(IN NN SET))
                  (begin (fact 'nn-is-set) (ass))
                  (let ((nv (cadr (car (dk-peel!)))))
                    (dk-apply! ptw nv)
                    (fact 'power-mem-sethood 'omega (list ff nv))
                    (ass))))
            (dk-opened (lambda () (bu-set))))))
  ;; ... and is included in omega: a member comes from some f(e)
  (have! sub
         (lambda ()
           (let* ((zz (cadr (car (dk-peel!))))
                  (new (dk-landed (lambda () (bu-me (list 'IN zz bu)))))
                  (ein (car (filter (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                                     (eq? (caddr f) 'NN)))
                                    new)))
                  (ee (cadr ein)))
             (dk-apply! ptw ee)
             (fact 'power-mem-in 'omega (list ff ee) zz)
             (ass))))
  (fact 'power-mem-intro 'omega bu)
  ;; every sigma-algebra over cE holds it, being closed under countable unions
  (have! uni
         (lambda ()
           (let* ((l2 (dk-peel!))
                  (bb (caddr (cadr (car l2)))))
             (dk-split! (car l2))
             (have! (list 'IN ff (list 'FUN 'NN bb))
                    (lambda ()
                      (mac 'fun-codomain-iff)
                      (dk-conj-close!
                       (lambda ()
                         (if (eq? (car (dk-goal)) 'FORALL)
                             (let ((nv (cadr (car (dk-peel!)))))
                               (fact 'fun-apply-type-c ff 'NN gg nv)
                               (fact 'sigma-generated-in-every 'omega 'cE (list ff nv) bb)
                               (ass))
                             (begin
                               (dk-split!
                                (dk-landed-1
                                 (lambda () (mac-h 'fun-codomain-iff
                                                   (list 'IN ff (list 'FUN 'NN gg))))))
                               (ass)))))))
             (fact 'sigma-algebra-union-closed 'omega bb ff)
             (ass))))
  (fact 'sigma-generated-intro 'omega 'cE bu)
  (ass))

(qed 'sigma-generated-is-sigma-algebra)
(topic! 'sigma-generated-is-sigma-algebra 'set-quotient)

;;; -----------------------------------------------------------------------
;;; 4.  The IS-MEASURABLE-MAP projections and its intro rule.
;;; -----------------------------------------------------------------------

(define (r5w-mm-project! concl)
  (sp (make-wff (forall-guarded '(omega cA omega2 cB f)
                  '((IS-MEASURABLE-MAP omega cA omega2 cB f))
                  concl)))
  (dk-peel!)
  (dk-split! (dk-landed-1
              (lambda () (mac-h 'IS-MEASURABLE-MAP
                                '(IS-MEASURABLE-MAP omega cA omega2 cB f)))))
  (ass))

(r5w-mm-project! '(IS-SIGMA-ALGEBRA omega cA))
(qed 'measurable-map-source-algebra)
(topic! 'measurable-map-source-algebra 'plumbing)

(r5w-mm-project! '(IS-SIGMA-ALGEBRA omega2 cB))
(qed 'measurable-map-target-algebra)
(topic! 'measurable-map-target-algebra 'plumbing)

(r5w-mm-project! '(IN f (FUN omega omega2)))
(qed 'measurable-map-in-fun)
(topic! 'measurable-map-in-fun 'plumbing)

;;; The preimage conjunct, with its own binder peeled: the preimage of a
;;; measurable b is the SEP { x in omega : f(x) in b }, as measure.scm writes it
;;; (a PREIMAGE head would read a metric structure for its point set).
(sp (make-wff (forall-guarded '(omega cA omega2 cB f b_)
                '((IS-MEASURABLE-MAP omega cA omega2 cB f) (IN b_ cB))
                '(IN (SEP x_ omega (IN (f x_) b_)) cA))))
(dk-peel!)
(dk-split! (dk-landed-1
            (lambda () (mac-h 'IS-MEASURABLE-MAP
                              '(IS-MEASURABLE-MAP omega cA omega2 cB f)))))
(dk-apply! (dk-pick (dk-head? 'FORALL) "the preimage universal") 'b_)
(ass)
(qed 'measurable-map-preimage)
(topic! 'measurable-map-preimage 'plumbing)

(sp (make-wff (forall-guarded '(omega cA omega2 cB f)
                (list '(IS-SIGMA-ALGEBRA omega cA)
                      '(IS-SIGMA-ALGEBRA omega2 cB)
                      '(IN f (FUN omega omega2))
                      '(FORALL b_ (IMPLIES (IN b_ cB)
                                    (IN (SEP x_ omega (IN (f x_) b_)) cA))))
                '(IS-MEASURABLE-MAP omega cA omega2 cB f))))
(dk-peel!)
(mac 'IS-MEASURABLE-MAP)
(dk-conj-close! (lambda () (ass)))
(qed 'measurable-map-intro)
(topic! 'measurable-map-intro 'plumbing)

;;; -----------------------------------------------------------------------
;;; 5.  measurable-map-compose.
;;;
;;; The content is one SET EQUALITY, and the tree has no SEP extensionality
;;; rule, so it goes through `class-extensionality' (library.scm, primitive):
;;;
;;;    { x in omega : (g o f)(x) in b }  =  { x in omega : f(x) in B' },
;;;           where  B' = { y in omega2 : g(y) in b }.
;;;
;;; Both memberships are opened with sep-me / sep-mi and bridged by
;;; `compose-apply', whose equation is used LEFT-to-RIGHT in one direction and
;;; through `equality-symmetry' in the other -- `subst' rewrites the GOAL, so
;;; the orientation is decided by which side the goal carries.
;;;
;;; The inner SEP is written with the binder y_ rather than x_ on purpose: the
;;; outer SEP binds x_ too, and a shadowed binder inside a term that later gets
;;; substituted is a hazard with no upside.  `ass' is alpha-aware, so the
;;; x_-spelled instance that measurable-map-preimage delivers still closes it.
;;; -----------------------------------------------------------------------

(sp (make-wff (forall-guarded '(omega cA omega2 cB omega3 cg f g)
                '((IS-MEASURABLE-MAP omega cA omega2 cB f)
                  (IS-MEASURABLE-MAP omega2 cB omega3 cg g))
    '(IS-MEASURABLE-MAP omega cA omega3 cg (COMPOSE g f)))))
(dk-peel!)
(fact 'measurable-map-source-algebra 'omega 'cA 'omega2 'cB 'f)
(fact 'measurable-map-target-algebra 'omega2 'cB 'omega3 'cg 'g)
(fact 'measurable-map-in-fun 'omega 'cA 'omega2 'cB 'f)
(fact 'measurable-map-in-fun 'omega2 'cB 'omega3 'cg 'g)
(fact 'sigma-algebra-ambient-set 'omega 'cA)
;; compose-type and compose-apply both take their two typings CONJOINED, and
;; `fact' will not split a conjunctive antecedent: assemble it first.
(have! '(AND (IN f (FUN omega omega2)) (IN g (FUN omega2 omega3))))
(fact 'compose-type 'omega 'omega2 'omega3 'g 'f)

(have! '(FORALL b_ (IMPLIES (IN b_ cg)
          (IN (SEP x_ omega (IN ((COMPOSE g f) x_) b_)) cA)))
  (lambda ()
    (let* ((bb  (cadr (car (dk-peel!))))
           (bp  (list 'SEP 'y_ 'omega2 (list 'IN (list 'g 'y_) bb)))
           (lhs (list 'SEP 'x_ 'omega
                      (list 'IN (list (list 'COMPOSE 'g 'f) 'x_) bb)))
           (rhs (list 'SEP 'x_ 'omega (list 'IN (list 'f 'x_) bp))))
      (have! (list 'IN bp 'cB)
             (lambda () (fact 'measurable-map-preimage 'omega2 'cB 'omega3 'cg 'g bb)
                        (ass)))
      (have! (list 'IN rhs 'cA)
             (lambda () (fact 'measurable-map-preimage 'omega 'cA 'omega2 'cB 'f bp)
                        (ass)))
      (have! (list 'FORALL 'w_ (list 'IFF (list 'IN 'w_ lhs) (list 'IN 'w_ rhs)))
        (lambda ()
          (dk-peel!)
          (let ((w (cadr (cadr (dk-goal)))))
            (for-each
             (lambda (l)
               (dk-focus! l)
               (if ((r5w-mentions? 'compose) (dk-goal))
                   ;; w in rhs  |-  w in lhs
                   (begin
                     (sep-me (list 'IN w rhs))
                     (sep-me (list 'IN (list 'f w) bp))
                     (fact 'compose-apply 'omega 'omega2 'omega3 'g 'f w)
                     (for-each (lambda (k)
                                 (dk-focus! k)
                                 (if ((r5w-mentions? 'compose) (dk-goal))
                                     (begin (subst (list '= (list (list 'COMPOSE 'g 'f) w)
                                                         (list 'g (list 'f w))))
                                            (ass))
                                     (ass)))
                               (dk-opened (lambda () (sep-mi)))))
                   ;; w in lhs  |-  w in rhs
                   (begin
                     (sep-me (list 'IN w lhs))
                     (fact 'compose-apply 'omega 'omega2 'omega3 'g 'f w)
                     (fact 'equality-symmetry
                           (list (list 'COMPOSE 'g 'f) w) (list 'g (list 'f w)))
                     (for-each
                      (lambda (k)
                        (dk-focus! k)
                        (if (equal? (dk-goal) (list 'IN w 'omega))
                            (ass)
                            (for-each
                             (lambda (m)
                               (dk-focus! m)
                               (cond ((equal? (dk-goal) (list 'IN (list 'f w) 'omega2))
                                      (fact 'fun-apply-type-c 'f 'omega 'omega2 w)
                                      (ass))
                                     (#t
                                      (subst (list '= (list 'g (list 'f w))
                                                   (list (list 'COMPOSE 'g 'f) w)))
                                      (ass))))
                             (dk-opened (lambda () (sep-mi))))))
                      (dk-opened (lambda () (sep-mi)))))))
             (dk-opened (lambda () (di)))))))
      (fact 'class-extensionality lhs rhs)
      (subst (list '= lhs rhs))
      (ass))))
(fact 'measurable-map-intro 'omega 'cA 'omega3 'cg '(COMPOSE g f))
(ass)
(qed 'measurable-map-compose)
(topic! 'measurable-map-compose 'plumbing)

;;; =======================================================================
;;; WHAT THE OTHER FIVE NEED -- the missing extended-real bricks.
;;;
;;; measure-monotone (measure.scm:346), measure-finitely-additive (:361),
;;; outer-measure-binary-subadditive (:323), caratheodory-null-measurable
;;; (:285) and measurable-fn-indicator (integral.scm:157) were surveyed before
;;; being attempted, as the brief asked.  NOT ONE of the first four can be
;;; driven, and they all stop in the same place.
;;;
;;; THE FINDING, in one sentence: [0,+inf] has an addition with four defining
;;; equations, a supremum with three characterising axioms, and NO ORDER
;;; THEORY AT ALL -- the only two facts about `<=' on RR-STAR are
;;; `pos-inf-upper-bound' and `neg-inf-lower-bound' (extended-reals.scm), and
;;; every other order axiom in the tree (rr-leq-reflexive, -antisymmetric,
;;; -transitive, -total, number-systems.scm:407-423) is guarded on `IN _ RR'.
;;; Measured: no theorem or axiom in the tree mentions `eplus' and `<=' in the
;;; same formula except the asserted supports themselves, and there is no
;;; proven theorem about ESUM, ESUP, EINF or eplus anywhere.
;;;
;;; (A) ORDER ON RR-POS-STAR -- none of these exists.
;;;   X1  rr-pos-star-le-refl      x in RR-POS-STAR => x <= x
;;;   X2  rr-pos-star-le-trans     x,y,z in RR-POS-STAR, x<=y, y<=z => x<=z
;;;   X3  rr-pos-star-le-antisymm  x,y in RR-POS-STAR, x<=y, y<=x => x = y
;;;   X4  pos-inf-not-le-real      x in RR => NOT (<= POS-INF x)
;;;
;;;   X1-X3 are case splits on rr-pos-star-membership over the RR axioms PLUS
;;;   X4, and X4 IS INDEPENDENT of the present axioms: interpret POS-INF as a
;;;   point with x <= POS-INF and POS-INF <= x for every x and every axiom of
;;;   extended-reals.scm / extended-reals-pos.scm still holds (they are all
;;;   either guarded on RR or one of the two bounds).  So X4 has to be a
;;;   DECISION -- an axiom about what POS-INF is -- not a proof.
;;;
;;;   Consequence worth stating on its own: extended-reals-pos.scm's header
;;;   says "Uniqueness of the lub is not asserted separately -- it follows
;;;   from antisymmetry of <=".  That antisymmetry is X3, which the tree does
;;;   not have on RR-POS-STAR, so ESUP -- and with it ESUM, EINF, ELIMINF,
;;;   ELIMSUP and INTEGRAL -- is NOT pinned down by its axioms as they stand.
;;;   The same hole makes the (<=) half of `esum-finite-iff-bounded'
;;;   (theorem-library/extended-sum.scm:79) unprovable: its warrant argues
;;;   "ESUM(f) <= M < POS-INF forces ESUM(f) =/= POS-INF", which is exactly X4.
;;;
;;; (B) ARITHMETIC OF eplus -- none of these exists either.  `eplus' has
;;;   FOUR axioms (eplus-real, eplus-pos-inf-left, eplus-pos-inf-right,
;;;   eplus-in-fun) and its monoid laws are packed inside the single assertion
;;;   `rr-pos-star-is-comm-monoid', with no slot read-off to get them out.
;;;   X5  eplus-zero-left / -right    eplus(0,x) = x = eplus(x,0)
;;;   X6  eplus-comm, eplus-assoc     (the read-offs from RR-POS-STAR-ADD-MONOID;
;;;                                    the `def-functor' view read-off pattern
;;;                                    of ag-view-read-offs.scm, one per slot)
;;;   X7  eplus-le-left               x,y in RR-POS-STAR => x <= eplus(x,y)
;;;   X8  eplus-mono                  x<=x', y<=y' => eplus(x,y) <= eplus(x',y')
;;;   X5 and X6 are three-case splits and cost nothing; X7 and X8 need X1-X4.
;;;
;;; (C) ESUM -- three bricks, all missing, and the first is the keystone.
;;;   X9  esum-finite-support-2   f in FUN(NN,RR-POS-STAR), f(n) = 0 for n >= 2
;;;                               =>  ESUM f = eplus(f 0, f 1)
;;;   X10 finsum-cm-monotone      S subset T finite  =>
;;;                               FINSUM(RR-POS-STAR-ADD-MONOID,f,S) <= FINSUM(...,T)
;;;                               (the <= half of X9, via esum-least)
;;;   X11 esum-le-termwise        f <= g pointwise  =>  ESUM f <= ESUM g
;;;   X9 is what "countable additivity gives finite additivity" IS: the whole
;;;   padded-sequence argument both sources use silently.  Its >= half is one
;;;   `esum-upper' at S = {0,1} plus finsum-insert/finsum-singleton; its <=
;;;   half is `esum-least' plus X10 plus X5.
;;;
;;; (D) SET-LEVEL bricks the same arguments need, also missing.  sigma-algebra.scm
;;;   asserts nothing and its header lists these as "NEXT (not stated)":
;;;   S1  sigma-algebra-empty-in        EMPTY-SET in cA (omega \ omega; ~15 lines,
;;;                                     provable here, not needed by either target)
;;;   S2  sigma-algebra-union-closed-2  binary union -- needs the countable
;;;                                     closure at the 2-valued family, hence S4
;;;   S3  sigma-algebra-inter-closed-2 / -difference-closed   (De Morgan off S2)
;;;   S4  big-union-of-padded-family    BIG-UNION n in NN of
;;;                                     (IF n=0 then a else IF n=1 then b else {})
;;;                                     = UNION a b.  Nothing of this shape exists,
;;;                                     and every padding argument needs it.
;;;
;;; PER LEAF:
;;;   measure-monotone                 S2,S3,S4 + X9 + X5 + X7   (b = a u (b\a))
;;;   measure-finitely-additive        S4 + X9 + X5
;;;   outer-measure-binary-subadditive S4 + X9 + X10             (pad a,b,{},{},...)
;;;   caratheodory-null-measurable     X3,X4 (to get mu(A n E) = 0 from
;;;                                    0 <= mu(A n E) <= mu(E) = 0) + X5, and it
;;;                                    also CHAINS to the asserted
;;;                                    outer-measure-binary-subadditive (or to
;;;                                    Def. 4.1(3) at a padded family, i.e. S4+X9)
;;;                                    for the other inequality.  Blocked twice.
;;;   measurable-fn-indicator          the ONLY one of the five free of (A)-(C):
;;;                                    it needs `(IN 1 RR-POS-STAR)' (one line off
;;;                                    rr-pos-star-membership), S1, `rr-leq-total'
;;;                                    on alpha against 0 and 1, and THREE
;;;                                    class-extensionality arguments -- the tail
;;;                                    { x : alpha < 1_a(x) } is omega when
;;;                                    alpha < 0, a when 0 <= alpha < 1, and
;;;                                    EMPTY-SET when 1 <= alpha.  Left undone
;;;                                    because the brief says to stop at the first
;;;                                    leaf that wants a missing extended-real
;;;                                    fact, and measure-monotone is the third in
;;;                                    the order; it is a ~200-line assignment and
;;;                                    it is unblocked.
;;;
;;; RECOMMENDED ORDER FOR THE NEXT BATCH: X4 is a user decision (the POS-INF
;;; strictness axiom, on the `pos-inf-not-in-rr' precedent); X1-X3 and X5-X8
;;; then fall in one file of about 150 lines; S4 and X9 are the next file; the
;;; four measure leaves follow immediately after, each in twenty lines.
;;; =======================================================================
