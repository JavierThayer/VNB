;;; theorem-library/rake-eplus-defined.scm -- extended addition on [0,+inf]
;;; DEFINED, and its laws proven.  Rake batch 5c-V.
;;;
;;; NOTHING HERE CITES eplus-real, eplus-pos-inf-left, eplus-pos-inf-right or
;;; eplus-in-fun.  Those four are the axioms this file replaces.  It reads the
;;; ONE defining equation the integrator installs in place of them,
;;;
;;;    eplus-def   eplus == VNB-LAMBDA [x_,y_] in RR-POS-STAR x RR-POS-STAR.
;;;                          IF (x_ = POS-INF or y_ = POS-INF)
;;;                             THEN POS-INF ELSE binplus(x_, y_)
;;;
;;; (scratchpad/r7v/r7v-def.scm holds the exact form, with the reason it is a
;;; provenance-wrapped add-axiom! and not a def-constant).
;;;
;;; WHY DEFINE RATHER THAN STAMP.  The four axioms are not merely unwarranted:
;;; taken together they are INCONSISTENT, and the derivation is fifteen lines
;;; (scratchpad/r7v/r7v-p3.scm, `;; qed r7v-extended-reals-pos-is-inconsistent:
;;; proven modulo {eplus-real, eplus-in-fun, rr-pos-star-nonneg}').  `eplus-real'
;;; quantifies over ALL reals and concludes a STRICT equation, so it asserts that
;;; eplus(x, 0) DENOTES for every real x; `eplus-in-fun' puts eplus in
;;; FUN(RR-POS-STAR x RR-POS-STAR, RR-POS-STAR), and `fun-domain-apply-def' says
;;; a member of FUN(A) is defined EXACTLY on A.  Hence every real lies in
;;; [0,+inf], hence (rr-pos-star-nonneg) every real is >= 0, hence 1 < 1.
;;; Stamping the three case equations `definitional' would have made a FALSE
;;; axiom contribute {} to every bill in the measure arc.
;;;
;;; WHAT THE DEFINITION COSTS.  Exactly one of the four statements weakens.
;;; `eplus-pos-inf-left', `eplus-pos-inf-right' and `eplus-in-fun' are proven
;;; here UNCHANGED, character for character.  `eplus-real' is replaced by
;;; `eplus-real-defined', which adds `0 <= x' and `0 <= y' -- the half of the
;;; original that was false.  Its only citation site in the tree is
;;; theorem-library/rake-extended-order.scm:127 (the helper r6h-eplus-real!,
;;; twelve call sites); see the closing block for the four sites that then need
;;; one extra line each.
;;;
;;; CONTENTS
;;;   apply-congruence-2      f == g  =>  f(u,v) == g(u,v)          modulo 0
;;;   rr-pos-star-is-set      [0,+inf] is a SET                     modulo 0
;;;   eplus-in-fun            the typing, UNCHANGED    modulo {pos-inf-not-in-rr}
;;;   eplus-pos-inf-left      UNCHANGED                             modulo 0
;;;   eplus-pos-inf-right     UNCHANGED                             modulo 0
;;;   eplus-real-defined      the GUARDED finite case  modulo {pos-inf-not-in-rr}
;;;
;;; `pos-inf-not-in-rr' (structure-library/extended-reals.scm:62) is a bare
;;; unwarranted axiom, so the two bills naming it read `trust: none'.  It is
;;; irreducible here: "POS-INF is not a real" is precisely what makes the finite
;;; and the infinite cases of the definition disjoint.  It is the same species as
;;; the three axioms 5c-K flagged (pos-inf-upper-bound, pos-inf-neq-neg-inf,
;;; neg-inf-not-in-rr) and wants the same user decision on provenance.
;;;
;;; LOAD WINDOW [191, 234).  lo = 191 is forced by `subclass-of-set-is-set'
;;; (theorem-library/subset-lemmas, 190) and by theorem-library/rake-rr-pos-star
;;; (batch 5c-K, itself [142,234)), whose `pos-inf-in-rr-pos-star' this file
;;; cites -- so wire this file AFTER both.  Everything else is earlier: the base
;;; theory (11), number-systems (34), numeric-instances (68),
;;; extended-reals (75), extended-reals-pos (76, the definition),
;;; definitional-reclass (104, which stamps rr-star-membership), and the tactics
;;; interactive (134), driver-kit (138), prop (141), calc (185, `ineq').
;;; hi = 234 is theorem-library/rake-extended-order, which must be able to cite
;;; `eplus-real-defined'.
;;;
;;; Helper prefix: r7v-.

(define r7v-lam
  '(VNB-LAMBDA (LIST x_ y_) (CARTESIAN RR-POS-STAR RR-POS-STAR)
     (IF (OR (= x_ POS-INF) (= y_ POS-INF))
         POS-INF
         (binplus x_ y_))))

(define r7v-cart '(CARTESIAN RR-POS-STAR RR-POS-STAR))
(define r7v-pair '(PAIR POS-INF POS-INF))
(define r7v-sup  (list 'UNION 'RR r7v-pair))

(define (r7v-real-case tm) (list 'AND (list 'IN tm 'RR) (list '<= 0 tm)))
(define (r7v-inf-case  tm) (list '= tm 'POS-INF))

;;; The case split off `rr-pos-star-membership' (definitional), 5c-K's lane.
(define (r7v-star-cases! tm real-body inf-body)
  (have! (list 'OR (r7v-real-case tm) (r7v-inf-case tm))
         (lambda ()
           (let ((inst (dk-fact! 'rr-pos-star-membership tm)))
             (dk-only! inst (list 'IN tm 'RR-POS-STAR))
             (prop))))
  (use-cases (list (r7v-real-case tm) (r7v-inf-case tm)) real-body inf-body))

;;; (= POS-INF POS-INF): an atomic constant needs no definedness certificate.
(define (r7v-pos-inf-refl!)
  (have! '(= POS-INF POS-INF) (lambda () (rfl))))

;;; A bare (ineq) passes ZERO premises to the oracle; every call here names them.
(define (r7v-indices n)
  (let loop ((k n) (acc '())) (if (= k 0) acc (loop (- k 1) (cons k acc)))))

(define (r7v-ineq! claim . keepers)
  (have! claim
         (lambda ()
           (apply dk-only! keepers)
           (apply ineq (r7v-indices (length (dk-asms)))))))

;;; From (IN TM RR) in context, land (NOT (= TM POS-INF)): POS-INF is not a
;;; real (pos-inf-not-in-rr).
(define (r7v-not-pos-inf! tm)
  (have! (list 'NOT (list '= tm 'POS-INF))
         (lambda ()
           (di)                              ; assume the equation; goal FALSITY
           (have! '(IN POS-INF RR)
                  (lambda () (subst (list '= 'POS-INF tm)) (ass)))
           (fact 'pos-inf-not-in-rr)
           (ai '(NOT (IN POS-INF RR))))))

;;; (IN TM RR-POS-STAR) from (IN TM RR) and (<= 0 TM) in context.  The -close!
;;; form is for a leaf whose goal IS that membership (a `have!' of the focus
;;; goal is an alpha self-loop); the other is the lane.
(define (r7v-close-in-star! tm)
  (let ((i (dk-fact! 'rr-pos-star-membership tm)))
    (dk-only! i (list 'IN tm 'RR) (list '<= 0 tm))
    (prop)))

(define (r7v-in-star! tm)
  (have! (list 'IN tm 'RR-POS-STAR)
         (lambda () (r7v-close-in-star! tm))))

;;; Rewrite (eplus A B) in the GOAL to the lambda redex and beta-reduce it.
;;; The licence for the beta is (IN A RR-POS-STAR) and (IN B RR-POS-STAR); both
;;; must already be in context or the step owes a leaf nothing can close.
(define (r7v-unfold! a b)
  (let ((eq (dk-fact! 'apply-congruence-2 'eplus r7v-lam a b)))
    (subst eq))
  (lam-b))

;;; if-true / if-false open TWO leaves: the condition and the main branch.
;;; Close the condition with CLOSE-COND!, then rewrite the IF away in the main
;;; branch and run THUNK there.  (rkm-if-branch!, rake-mat-typing.scm.)
(define (r7v-if-branch! true? ifterm close-cond! thunk)
  (let* ((c      (cadr ifterm))
         (val    (if true? (caddr ifterm) (cadddr ifterm)))
         (want   (if true? c (list 'NOT c)))
         (opened (dk-opened (lambda () (if true? (if-true ifterm) (if-false ifterm)))))
         (conds  (filter (lambda (l) (alpha-equiv? (dk-goal-of l) want)) opened))
         (mains  (filter (lambda (l) (not (memq l conds))) opened)))
    (if (not (and (= 1 (length conds)) (= 1 (length mains))))
        (error "r7v-if-branch!: expected one condition leaf and one main leaf, got"
               (map (lambda (l) (expression->string (dk-goal-of l))) opened)))
    (dk-focus! (car conds)) (close-cond!)
    (dk-focus! (car mains))
    (subst (list '= ifterm val))
    (thunk)))

;;; ===================================================================
;;; (1) apply-congruence-2 -- quasi-equal function terms have quasi-equal
;;; values at every pair of arguments.
;;;
;;; WHY THIS BRICK EXISTS.  A defining equation for a CONSTANT that denotes a
;;; function, (== eplus LAM), cannot be unfolded in APPLIED position by any
;;; rewriter in the tree: `subst' goes through replace-term -> subst-free, whose
;;; general-compound branch substitutes a symbol head only when it is NOT a
;;; registered constant (expressions.scm), and the macete engine's own branch
;;; says "symbol heads pass through unchanged" (macetes.scm).  eplus IS
;;; registered -- EPLUS sits in *wff-term-form-heads* (wff.scm) -- so both
;;; decline.  Leibniz at the level of the APPLICATION is the way in, and it is
;;; three lines: with f and g VARIABLES the same subst-free branch does
;;; substitute the head, and `==' is reflexive unconditionally (qrfl).
;;;
;;; Its macete form is automatically INERT (S-10: the schema variable g occurs
;;; in the condition and the replacement but not in the source pattern), which
;;; is what one wants -- the source pattern (f u v) matches every binary
;;; application in the library.

(sp (make-wff '(FORALL f (FORALL g (IMPLIES (== f g)
                 (FORALL u (FORALL v (== (f u v) (g u v)))))))))
(dk-peel!)
(subst '(== f g))
(qrfl)
(qed 'apply-congruence-2)
(topic! 'apply-congruence-2 'plumbing)
(gloss! 'apply-congruence-2
  "Quasi-equal function terms have quasi-equal values: f == g implies
   f(u,v) == g(u,v).  The bridge a defining equation for a function-valued
   CONSTANT needs, since no rewriter in the tree rewrites a registered constant
   head in applied position.")

;;; ===================================================================
;;; (2) rr-pos-star-is-set -- [0,+inf] is a SET.
;;;
;;; `lam-t' owes (IN A SET) for the domain of a lambda, so the typing of eplus
;;; cannot be proved without it, and nothing in the tree had it.  RR-POS-STAR is
;;; included in RR u {POS-INF}, which is a set, so subclass-of-set-is-set
;;; delivers it.  POS-INF's own sethood comes off `rr-star-membership'
;;; (definitional) rather than off the unwarranted `pos-inf-in-rr-star'.

(sp (make-wff '(IN RR-POS-STAR SET)))
(r7v-pos-inf-refl!)
(have! '(IN POS-INF RR-STAR)
       (lambda ()
         (let ((inst (dk-fact! 'rr-star-membership 'POS-INF)))
           (dk-only! inst '(= POS-INF POS-INF))
           (prop))))
(fact 'membership-implies-sethood 'POS-INF 'RR-STAR)   ; (IN POS-INF SET)
(have! '(AND (IN POS-INF SET) (IN POS-INF SET)))
(fact 'pairing 'POS-INF 'POS-INF)                      ; (IN (PAIR POS-INF POS-INF) SET)
(fact 'rr-is-set)
(have! (list 'AND '(IN RR SET) (list 'IN r7v-pair 'SET)))
(fact 'union-set-closure 'RR r7v-pair)
(have! (list 'IN 'POS-INF r7v-pair)
       (lambda ()
         (let* ((u (dk-fact! 'pairing-membership 'POS-INF 'POS-INF))
                (i (inst*! u 'POS-INF)))
           (dk-only! i '(= POS-INF POS-INF))
           (prop))))
(have! (list 'SUBSET 'RR-POS-STAR r7v-sup)
       (lambda ()
         (mac 'subset-def)
         (dk-peel!)
         (r7v-star-cases! 'x
           (lambda ()
             (dk-split! (r7v-real-case 'x))
             (let ((i (dk-fact! 'union-membership 'RR r7v-pair 'x)))
               (dk-only! i '(IN x RR))
               (prop)))
           (lambda ()
             (subst '(= x POS-INF))
             (let ((i (dk-fact! 'union-membership 'RR r7v-pair 'POS-INF)))
               (dk-only! i (list 'IN 'POS-INF r7v-pair))
               (prop))))))
(fact 'subclass-of-set-is-set 'RR-POS-STAR r7v-sup)
(ass)
(qed 'rr-pos-star-is-set)
(topic! 'rr-pos-star-is-set 'analysis)
(gloss! 'rr-pos-star-is-set
  "[0,+inf] is a set: it is included in RR u {+inf}, and a subclass of a set is
   a set.  What lam-t owes for any function whose domain is RR-POS-STAR.")

;;; ===================================================================
;;; (3) eplus-in-fun -- statement copied literally from
;;; structure-library/extended-reals-pos.scm:146.  An AXIOM there; a THEOREM
;;; here, because the definition exhibits the graph.

(sp (make-wff '(IN eplus (FUN (CARTESIAN RR-POS-STAR RR-POS-STAR) RR-POS-STAR))))
(fact 'eplus-def)
(subst (list '== 'eplus r7v-lam))
(fact 'rr-pos-star-is-set)
(have! '(AND (IN RR-POS-STAR SET) (IN RR-POS-STAR SET)))
(have! (list 'IN r7v-cart 'SET)
       (lambda ()
         (fact 'cartesian-set-iff 'RR-POS-STAR 'RR-POS-STAR)
         (prop)))
(let* ((opened (dk-opened (lambda () (lam-t))))
       (sets   (filter (lambda (l) (let ((g (dk-goal-of l)))
                                     (and (pair? g) (eq? (car g) 'IN)
                                          (eq? (caddr g) 'SET))))
                       opened))
       (typ    (filter (lambda (l) (not (memq l sets))) opened)))
  (for-each (lambda (l) (dk-focus! l) (ass)) sets)
  (dk-focus! (car typ))
  (dk-peel!)
  ;; the eigenvariables are read off the GOAL, never off the landing order
  (let* ((ift (cadr (dk-goal)))                 ; (IF (OR ..) POS-INF (binplus ..))
         (cnd (cadr ift))
         (xv  (cadr (cadr cnd)))
         (yv  (cadr (caddr cnd)))
         (inf! (lambda (eqn)
                 (r7v-if-branch! #t ift
                   (lambda () (dk-only! eqn) (prop))
                   (lambda () (fact 'pos-inf-in-rr-pos-star) (ass))))))
    (r7v-star-cases! xv
      (lambda ()                                ; xv is a nonnegative real
        (dk-split! (r7v-real-case xv))
        (r7v-not-pos-inf! xv)
        (r7v-star-cases! yv
          (lambda ()                            ; both real: the value is xv + yv
            (dk-split! (r7v-real-case yv))
            (r7v-not-pos-inf! yv)
            (r7v-if-branch! #f ift
              (lambda ()
                (dk-only! (list 'NOT (list '= xv 'POS-INF))
                          (list 'NOT (list '= yv 'POS-INF)))
                (prop))
              (lambda ()
                (fact 'binplus-apply xv yv)
                (subst (list '== (list 'binplus xv yv) (list '+ xv yv)))
                (have! (list 'AND (list 'IN xv 'RR) (list 'IN yv 'RR)))
                (fact 'rr-add-closed xv yv)
                (r7v-ineq! (list '<= 0 (list '+ xv yv))
                           (list 'IN xv 'RR) (list 'IN yv 'RR)
                           (list '<= 0 xv) (list '<= 0 yv))
                (r7v-close-in-star! (list '+ xv yv)))))
          (lambda () (inf! (list '= yv 'POS-INF)))))
      (lambda () (inf! (list '= xv 'POS-INF))))))
(qed 'eplus-in-fun)
(topic! 'eplus-in-fun 'analysis)

;;; ===================================================================
;;; (4) eplus-pos-inf-left -- statement copied literally from
;;; structure-library/extended-reals-pos.scm:135.  TRUE of the definition
;;; exactly as it stands: POS-INF is in the domain, so the application denotes
;;; and the IF takes its left branch.

(sp (make-wff '(FORALL y (IMPLIES (IN y RR-POS-STAR)
                 (= (eplus POS-INF y) POS-INF)))))
(dk-peel!)
(fact 'eplus-def)
(fact 'pos-inf-in-rr-pos-star)
(r7v-unfold! 'POS-INF 'y)
(r7v-pos-inf-refl!)
(r7v-if-branch! #t (cadr (dk-goal))
  (lambda () (dk-only! '(= POS-INF POS-INF)) (prop))
  (lambda () (rfl)))
(qed 'eplus-pos-inf-left)
(topic! 'eplus-pos-inf-left 'analysis)

;;; ===================================================================
;;; (5) eplus-pos-inf-right -- statement copied literally from
;;; structure-library/extended-reals-pos.scm:140.

(sp (make-wff '(FORALL x (IMPLIES (IN x RR-POS-STAR)
                 (= (eplus x POS-INF) POS-INF)))))
(dk-peel!)
(fact 'eplus-def)
(fact 'pos-inf-in-rr-pos-star)
(r7v-unfold! 'x 'POS-INF)
(r7v-pos-inf-refl!)
(r7v-if-branch! #t (cadr (dk-goal))
  (lambda () (dk-only! '(= POS-INF POS-INF)) (prop))
  (lambda () (rfl)))
(qed 'eplus-pos-inf-right)
(topic! 'eplus-pos-inf-right 'analysis)

;;; ===================================================================
;;; (6) eplus-real-defined -- the GUARDED finite case.
;;;
;;; The axiom it replaces, `eplus-real' (extended-reals-pos.scm:128), quantifies
;;; over ALL reals:
;;;     forall x, y. x in RR and y in RR  =>  eplus(x,y) = binplus(x,y).
;;; That is FALSE of any definition whose domain is [0,+inf] x [0,+inf], and it
;;; is INCONSISTENT with the file's own `eplus-in-fun' -- see the closing block.
;;; The strongest true form adds nonnegativity.  Stated with the four
;;; antecedents CURRIED rather than conjoined, so a citer's `fact' auto-detaches
;;; whichever are already in context (in the callers the real case of a
;;; RR-POS-STAR split has landed all four as separate atoms).

(sp (make-wff
     '(FORALL x (FORALL y
        (IMPLIES (IN x RR)
          (IMPLIES (<= 0 x)
            (IMPLIES (IN y RR)
              (IMPLIES (<= 0 y)
                (= (eplus x y) (binplus x y))))))))))
(dk-peel!)
(r7v-in-star! 'x)
(r7v-in-star! 'y)
(fact 'eplus-def)
(r7v-unfold! 'x 'y)
(r7v-not-pos-inf! 'x)
(r7v-not-pos-inf! 'y)
(r7v-if-branch! #f (cadr (dk-goal))
  (lambda ()
    (dk-only! '(NOT (= x POS-INF)) '(NOT (= y POS-INF)))
    (prop))
  (lambda ()
    (fact 'binplus-apply 'x 'y)
    (subst '(== (binplus x y) (+ x y)))
    (rfl)))
(qed 'eplus-real-defined)
(topic! 'eplus-real-defined 'analysis)
(gloss! 'eplus-real-defined
  "Extended addition agrees with ordinary addition on the NONNEGATIVE reals.
   The guard 0 <= x, 0 <= y is not decoration: eplus is a function on
   [0,+inf] x [0,+inf], so eplus(x,y) does not denote when either argument is a
   negative real, and the unguarded form is false.")

;;; ===================================================================
;;; WHAT THE INTEGRATOR MUST CHANGE
;;; ===================================================================
;;;
;;; A. structure-library/extended-reals-pos.scm
;;;    RETIRE the four add-axiom! forms eplus-real (:127-131),
;;;    eplus-pos-inf-left (:134-136), eplus-pos-inf-right (:139-141) and
;;;    eplus-in-fun (:144-145), together with the second `for-each ... warrant!'
;;;    block at the foot of the file (the one over
;;;    '(eplus-real eplus-pos-inf-left eplus-pos-inf-right
;;;      rr-pos-star-add-monoid-def)) -- keep `rr-pos-star-add-monoid-def' in
;;;    that list only if it is not turned into a def-constant (see C).
;;;    INSTALL in their place the two forms of scratchpad/r7v/r7v-def.scm.
;;;    The file header's paragraph "Defined like the polymorphic operators of
;;;    numeric-instances.scm: a constant operation symbol pinned by apply
;;;    axioms + a typing (closure) axiom, rather than a VNB-LAMBDA" becomes
;;;    false and should be rewritten; so does the parallel paragraph in
;;;    structure-library/extended-arith.scm's PROVENANCE block, which cites
;;;    eplus-in-fun as the precedent for etimes-in-fun.
;;;
;;; B. theorem-library/rake-extended-order.scm -- the ONLY citer.
;;;    :127  (fact 'eplus-real a b)  ->  (fact 'eplus-real-defined a b)
;;;    The statement is curried on (IN a RR), (<= 0 a), (IN b RR), (<= 0 b), so
;;;    `fact' auto-detaches whichever are in context.  Eight of the twelve call
;;;    sites already hold all four (they sit in the REAL case of a
;;;    rr-pos-star-membership split, where dk-split! has landed both conjuncts).
;;;    The four that do not, and the one line each needs FIRST:
;;;      :290 (r6h-eplus-real! 0 'x)          (fact 'rr-leq-reflexive 0)
;;;      :309 (r6h-eplus-real! 'x 0)          (fact 'rr-leq-reflexive 0)
;;;      :381 (r6h-eplus-real! '(+ x y) 'z)   rr-add-closed + r6h-ineq! for
;;;                                           (<= 0 (+ x y))
;;;      :382 (r6h-eplus-real! 'x '(+ y z))   the same for (+ y z)
;;;      :471 (r6h-eplus-real! 'x 'y)  in eplus-mono: x and y are typed in
;;;           RR-POS-STAR and shown real by rr-pos-star-le-real-in-rr, but their
;;;           nonnegativity is not in context -- two (fact 'rr-pos-star-nonneg _).
;;;    Nothing else in rake-extended-order.scm moves: eplus-pos-inf-left and
;;;    eplus-pos-inf-right keep their exact statements, so its nine other
;;;    citations of them are untouched.
;;;
;;; C. STILL ASSERTED, and NOT provable in this window.
;;;    * rr-pos-star-add-monoid-def, (= RR-POS-STAR-ADD-MONOID
;;;      (LIST RR-POS-STAR eplus 0)), is the defining equation of a DIFFERENT
;;;      constant and is not a consequence of anything here.  It should become
;;;      (def-constant 'RR-POS-STAR-ADD-MONOID
;;;         (list 'rr-pos-star-add-monoid-def
;;;               '(= RR-POS-STAR-ADD-MONOID (LIST RR-POS-STAR eplus 0))))
;;;      -- RR-POS-STAR-ADD-MONOID occurs only in ARGUMENT position, so
;;;      def-constant's register-constant! costs nothing here (contrast eplus,
;;;      whose registration is what forces apply-congruence-2 above).  Better
;;;      still, `declare-instance!' it as a COMM-MONOID: nothing else makes
;;;      `surface-goal!' work on it, and that is what the next item needs.
;;;    * rr-pos-star-is-comm-monoid, (IS-COMM-MONOID RR-POS-STAR-ADD-MONOID),
;;;      is now within reach but must sit ABOVE rake-extended-order (234),
;;;      because its associativity, commutativity and identity conjuncts are
;;;      eplus-assoc / eplus-comm / eplus-zero-left / eplus-zero-right, which
;;;      that file proves.  With those, plus eplus-closed (also there),
;;;      eplus-in-fun and rr-pos-star-is-set (here) and zero-in-rr-pos-star
;;;      (5c-K), every conjunct of the IS-COMM-MONOID unfold is one citation.
;;;      The driver is theorem-library/nn-add-monoid.scm's, and it is SHORTER
;;;      here because the OPR slot holds the bare constant `eplus' rather than a
;;;      tupled VNB-LAMBDA -- but `surface-goal!' (transport.scm:143) errors on
;;;      RR-POS-STAR-ADD-MONOID ("not a declared instance"), so either do the
;;;      slot read-offs by hand ((slot 'CARR), subst the monoid-def, (nth-r);
;;;      ag-view-read-offs.scm's `ras-*' is the pattern) or declare the instance
;;;      first.  A file of its own, wired after rake-extended-order.
