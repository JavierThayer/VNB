;;; theorem-library/rake-etimes-defined.scm -- extended MULTIPLICATION on
;;; [0,+inf] DEFINED, and its laws proven.  Rake batch 5c-Y.
;;;
;;; NOTHING HERE CITES etimes-real, etimes-zero-pos-inf, etimes-pos-inf-zero,
;;; etimes-pos-inf-left, etimes-pos-inf-right or etimes-in-fun.  Those six are
;;; the axioms this file replaces.  It reads the ONE defining equation the
;;; integrator installs in place of them,
;;;
;;;   etimes-def  etimes == VNB-LAMBDA [x_,y_] in RR-POS-STAR x RR-POS-STAR.
;;;                          IF (x_ = POS-INF or y_ = POS-INF)
;;;                             THEN IF (x_ = 0 or y_ = 0) THEN 0 ELSE POS-INF
;;;                             ELSE bintimes(x_, y_)
;;;
;;; (scratchpad/r7y/r7y-def.scm holds the exact form, with the reason it is a
;;; provenance-wrapped theory-add-axiom! and not a def-constant, and the reason
;;; the infinite test is the OUTER one.)
;;;
;;; WHY DEFINE RATHER THAN STAMP -- AND THIS TIME THE STAMP IS ALREADY ON.
;;; The five case equations of structure-library/extended-arith.scm are wrapped
;;; `definitional', so they contribute {} to every bill.  Together with
;;; `etimes-in-fun' they are INCONSISTENT, and the derivation is the one 5c-V
;;; found for eplus, transposed symbol for symbol
;;; (scratchpad/r7y/r7y-p1.scm, `;; qed r7y-extended-arith-is-inconsistent:
;;; proven modulo {etimes-in-fun, rr-pos-star-nonneg}'):
;;;
;;;   `etimes-real' quantifies over ALL reals -- negatives included -- and
;;;   concludes a STRICT equation, so it asserts that etimes(x, 0) DENOTES for
;;;   every real x; `etimes-in-fun' puts etimes in
;;;   FUN(RR-POS-STAR x RR-POS-STAR, RR-POS-STAR), and `fun-domain-apply-def'
;;;   says a member of FUN(A,B) is defined EXACTLY on A.  Hence every real lies
;;;   in [0,+inf]; hence (rr-pos-star-nonneg) every real is >= 0; hence 1 < 1.
;;;
;;; Note the bill of that derivation: `etimes-real' does NOT appear in it.  The
;;; definitional stamp hides the false axiom from every ledger, which is why
;;; this case is worse than the eplus one rather than merely the same.
;;;
;;; WHAT THE DEFINITION COSTS.  Exactly one of the six statements weakens.
;;; `etimes-zero-pos-inf', `etimes-pos-inf-zero', `etimes-pos-inf-left',
;;; `etimes-pos-inf-right' and `etimes-in-fun' are proven here UNCHANGED,
;;; character for character (the two guarded ones are copied through
;;; `forall-guarded' exactly as extended-arith.scm writes them, never
;;; transcribed from the printed reading).  `etimes-real'
;;; is replaced by `etimes-real-defined', which adds `0 <= x' and `0 <= y' --
;;; the half of the original that was false.  It has NO citation site in the
;;; tree (see the closing block), so that cost is zero today.
;;;
;;; CONTENTS
;;;   etimes-in-fun           the typing, UNCHANGED   modulo {pos-inf-not-in-rr}
;;;   etimes-zero-pos-inf     UNCHANGED
;;;   etimes-pos-inf-zero     UNCHANGED
;;;   etimes-pos-inf-left     UNCHANGED
;;;   etimes-pos-inf-right    UNCHANGED
;;;   etimes-real-defined     the GUARDED finite case
;;;
;;; `pos-inf-not-in-rr' (structure-library/extended-reals.scm:59) is a bare
;;; unwarranted axiom, so bills naming it read `trust: none'.  It is irreducible
;;; here for the same reason 5c-V gives: "POS-INF is not a real" is precisely
;;; what makes the finite and infinite branches of the tower disjoint.  Same
;;; species as the three axioms 5c-K flagged (pos-inf-upper-bound,
;;; pos-inf-neq-neg-inf, neg-inf-not-in-rr); same user decision wanted.
;;;
;;; LOAD WINDOW.  Wire this file AFTER theorem-library/rake-eplus-defined
;;; (batch 5c-V), whose `apply-congruence-2' and `rr-pos-star-is-set' it cites,
;;; and hence after theorem-library/rake-rr-pos-star (5c-K) and
;;; theorem-library/subset-lemmas, which that file needs.  NOTHING forces a
;;; ceiling: no proven theorem in the tree cites any etimes axiom, and the only
;;; file that mentions `etimes' at all is structure-library/integral.scm, which
;;; uses the CONSTANT (in the def-functoids PTWISE-ETIMES and PTWISE-SCALE, and
;;; in the asserted supports measurable-fn-etimes and integral-homogeneous) and
;;; never an etimes axiom by name.  So the window is [rake-eplus-defined+1, end).
;;;
;;; Helper prefix: r7y-.

(define r7y-lam
  '(VNB-LAMBDA (LIST x_ y_) (CARTESIAN RR-POS-STAR RR-POS-STAR)
     (IF (OR (= x_ POS-INF) (= y_ POS-INF))
         (IF (OR (= x_ 0) (= y_ 0))
             0
             POS-INF)
         (bintimes x_ y_))))

(define r7y-cart '(CARTESIAN RR-POS-STAR RR-POS-STAR))

(define (r7y-real-case tm) (list 'AND (list 'IN tm 'RR) (list '<= 0 tm)))
(define (r7y-inf-case  tm) (list '= tm 'POS-INF))

;;; The case split off `rr-pos-star-membership' (definitional), 5c-K's lane.
(define (r7y-star-cases! tm real-body inf-body)
  (have! (list 'OR (r7y-real-case tm) (r7y-inf-case tm))
         (lambda ()
           (let ((inst (dk-fact! 'rr-pos-star-membership tm)))
             (dk-only! inst (list 'IN tm 'RR-POS-STAR))
             (prop))))
  (use-cases (list (r7y-real-case tm) (r7y-inf-case tm)) real-body inf-body))

;;; (= t t) for an atomic constant: no definedness certificate is owed.
(define (r7y-refl! tm)
  (have! (list '= tm tm) (lambda () (rfl))))

;;; From (IN TM RR) in context, land (NOT (= TM POS-INF)) resp.
;;; (NOT (= POS-INF TM)): POS-INF is not a real.  Both orientations occur --
;;; the outer condition of the tower tests (= x_ POS-INF), the inner one
;;; (= x_ 0), and after x_ := POS-INF that reads (= POS-INF 0).
(define (r7y-not-pos-inf! tm)
  (have! (list 'NOT (list '= tm 'POS-INF))
         (lambda ()
           (di)                              ; assume the equation; goal FALSITY
           (have! '(IN POS-INF RR)
                  (lambda () (subst (list '= 'POS-INF tm)) (ass)))
           (fact 'pos-inf-not-in-rr)
           (ai '(NOT (IN POS-INF RR))))))

(define (r7y-pos-inf-not! tm)
  (have! (list 'NOT (list '= 'POS-INF tm))
         (lambda ()
           (di)                              ; assume (= POS-INF tm); goal FALSITY
           (have! '(IN POS-INF RR)
                  (lambda () (subst (list '= 'POS-INF tm)) (ass)))
           (fact 'pos-inf-not-in-rr)
           (ai '(NOT (IN POS-INF RR))))))

;;; (IN TM RR-POS-STAR) from (IN TM RR) and (<= 0 TM) in context.
(define (r7y-close-in-star! tm)
  (let ((i (dk-fact! 'rr-pos-star-membership tm)))
    (dk-only! i (list 'IN tm 'RR) (list '<= 0 tm))
    (prop)))

(define (r7y-in-star! tm)
  (have! (list 'IN tm 'RR-POS-STAR)
         (lambda () (r7y-close-in-star! tm))))

;;; Rewrite (etimes A B) in the GOAL to the lambda redex and beta-reduce it.
;;; The licence for the beta is (IN A RR-POS-STAR) and (IN B RR-POS-STAR); both
;;; must already be in context or the step owes a leaf nothing can close.
;;; `etimes-def' must be in context too (apply-congruence-2's antecedent).
(define (r7y-unfold! a b)
  (let ((eq (dk-fact! 'apply-congruence-2 'etimes r7y-lam a b)))
    (subst eq))
  (lam-b))

;;; if-true / if-false open TWO leaves: the condition and the main branch.
;;; Close the condition with CLOSE-COND!, then rewrite the IF away in the main
;;; branch and run THUNK there.  (r7v-if-branch!, rake-eplus-defined.scm;
;;; rkm-if-branch!, rake-mat-typing.scm.)
(define (r7y-if-branch! true? ifterm close-cond! thunk)
  (let* ((c      (cadr ifterm))
         (val    (if true? (caddr ifterm) (cadddr ifterm)))
         (want   (if true? c (list 'NOT c)))
         (opened (dk-opened (lambda () (if true? (if-true ifterm) (if-false ifterm)))))
         (conds  (filter (lambda (l) (alpha-equiv? (dk-goal-of l) want)) opened))
         (mains  (filter (lambda (l) (not (memq l conds))) opened)))
    (if (not (and (= 1 (length conds)) (= 1 (length mains))))
        (error "r7y-if-branch!: expected one condition leaf and one main leaf, got"
               (map (lambda (l) (expression->string (dk-goal-of l))) opened)))
    (dk-focus! (car conds)) (close-cond!)
    (dk-focus! (car mains))
    (subst (list '= ifterm val))
    (thunk)))

;;; The INFINITE branch of the tower, as it appears in a TYPING goal: the outer
;;; condition holds (EQN is the disjunct that makes it so), and the inner IF is
;;; resolved by a case split on its own condition -- 0 in two branches, POS-INF
;;; in the third, all three in RR-POS-STAR.
;;;
;;; The split is on the two ATOMS `x_ = 0' and `y_ = 0', one after the other,
;;; and NOT on the inner condition `x_ = 0 or y_ = 0' itself.  `use-em' on a
;;; DISJUNCTIVE proposition does not produce two branches: it calls `use-cases'
;;; on (OR P (NOT P)), and `use-cases--split' FLATTENS a nested OR, so P = (OR a
;;; b) yields the THREE cases a, b, (NOT P).  `use-cases' checks the body count
;;; against the case count; `use-em--on' checks only that it was handed two
;;; bodies, and `for-each' over the unequal lists then pairs the first two cases
;;; and drops the third SILENTLY.  The dropped leaf is the one that matters
;;; here -- the ELSE branch, the only one whose value is POS-INF -- and it
;;; surfaces only at `qed'.
(define (r7y-inf-typing! ift eqn)
  (r7y-if-branch! #t ift
    (lambda () (dk-only! eqn) (prop))
    (lambda ()
      (let* ((ift2  (cadr (dk-goal)))
             (c2    (cadr ift2))
             (dx    (cadr c2))                  ; (= x_ 0)
             (dy    (caddr c2))                 ; (= y_ 0)
             ;; The condition leaf is closed by OR-introduction on the side the
             ;; case assumed, never by (dk-only! .. ) (prop).  `wk' posts a new
             ;; node, `dg-post!' hash-conses by alpha of the assertion plus
             ;; equality of the context, and on the SECOND call of this helper
             ;; the weakened sequent coincides with one the first call already
             ;; grounded -- so the leaf closed under the driver's feet and the
             ;; focus moved to the sibling, where the following `prop' declined
             ;; on a goal nobody had asked it about.  Harmless here only because
             ;; the leaf really was closed; loud, and one graph away from a bug.
             (zero! (lambda (left?)             ; the value is 0
                      (r7y-if-branch! #t ift2
                        (lambda () (if left? (oi-l) (oi-r)) (ass))
                        (lambda () (fact 'zero-in-rr-pos-star) (ass))))))
        (use-em dx
          (lambda () (zero! #t))
          (lambda ()
            (use-em dy
              (lambda () (zero! #f))
              (lambda ()                        ; neither is 0: the value is POS-INF
                (r7y-if-branch! #f ift2
                  (lambda () (prop))
                  (lambda () (fact 'pos-inf-in-rr-pos-star) (ass)))))))))))

;;; ===================================================================
;;; (1) etimes-in-fun -- statement copied literally from
;;; structure-library/extended-arith.scm:80.  An AXIOM there; a THEOREM here,
;;; because the definition exhibits the graph.

(sp (make-wff '(IN etimes (FUN (CARTESIAN RR-POS-STAR RR-POS-STAR) RR-POS-STAR))))
(fact 'etimes-def)
(subst (list '== 'etimes r7y-lam))
(fact 'rr-pos-star-is-set)
(have! '(AND (IN RR-POS-STAR SET) (IN RR-POS-STAR SET)))
(have! (list 'IN r7y-cart 'SET)
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
  (let* ((ift (cadr (dk-goal)))              ; the outer IF of the tower
         (cnd (cadr ift))
         (xv  (cadr (cadr cnd)))
         (yv  (cadr (caddr cnd))))
    (r7y-star-cases! xv
      (lambda ()                             ; xv is a nonnegative real
        (dk-split! (r7y-real-case xv))
        (r7y-not-pos-inf! xv)
        (r7y-star-cases! yv
          (lambda ()                         ; both real: the value is xv * yv
            (dk-split! (r7y-real-case yv))
            (r7y-not-pos-inf! yv)
            (r7y-if-branch! #f ift
              (lambda ()
                (dk-only! (list 'NOT (list '= xv 'POS-INF))
                          (list 'NOT (list '= yv 'POS-INF)))
                (prop))
              (lambda ()
                (fact 'bintimes-apply xv yv)
                (subst (list '== (list 'bintimes xv yv) (list '* xv yv)))
                (have! (list 'AND (list 'IN xv 'RR) (list 'IN yv 'RR)))
                (fact 'rr-mul-closed xv yv)
                (have! (list 'AND (list '<= 0 xv) (list '<= 0 yv)))
                (fact 'rr-leq-mul-nonneg xv yv)
                (r7y-close-in-star! (list '* xv yv)))))
          (lambda () (r7y-inf-typing! ift (list '= yv 'POS-INF)))))
      (lambda () (r7y-inf-typing! ift (list '= xv 'POS-INF))))))
(qed 'etimes-in-fun)
(topic! 'etimes-in-fun 'analysis)

;;; ===================================================================
;;; (2) etimes-zero-pos-inf -- statement copied literally from
;;; structure-library/extended-arith.scm:61.  The measure-theory convention
;;; 0 * oo = 0, now a consequence of the tower rather than an assumption.

(sp (make-wff '(= (etimes 0 POS-INF) 0)))
(fact 'etimes-def)
(fact 'zero-in-rr-pos-star)
(fact 'pos-inf-in-rr-pos-star)
(r7y-unfold! 0 'POS-INF)
(r7y-refl! 'POS-INF)
(r7y-refl! 0)
(r7y-if-branch! #t (cadr (dk-goal))
  (lambda () (dk-only! '(= POS-INF POS-INF)) (prop))
  (lambda ()
    (r7y-if-branch! #t (cadr (dk-goal))
      (lambda () (dk-only! '(= 0 0)) (prop))
      (lambda () (rfl)))))
(qed 'etimes-zero-pos-inf)
(topic! 'etimes-zero-pos-inf 'analysis)

;;; ===================================================================
;;; (3) etimes-pos-inf-zero -- statement copied literally from
;;; structure-library/extended-arith.scm:64.

(sp (make-wff '(= (etimes POS-INF 0) 0)))
(fact 'etimes-def)
(fact 'zero-in-rr-pos-star)
(fact 'pos-inf-in-rr-pos-star)
(r7y-unfold! 'POS-INF 0)
(r7y-refl! 'POS-INF)
(r7y-refl! 0)
(r7y-if-branch! #t (cadr (dk-goal))
  (lambda () (dk-only! '(= POS-INF POS-INF)) (prop))
  (lambda ()
    (r7y-if-branch! #t (cadr (dk-goal))
      (lambda () (dk-only! '(= 0 0)) (prop))
      (lambda () (rfl)))))
(qed 'etimes-pos-inf-zero)
(topic! 'etimes-pos-inf-zero 'analysis)

;;; ===================================================================
;;; (4) etimes-pos-inf-left -- statement copied through `forall-guarded'
;;; exactly as structure-library/extended-arith.scm:68 writes it.

(sp (make-wff (forall-guarded '(y) '((IN y RR-POS-STAR) (NOT (= y 0)))
                '(= (etimes POS-INF y) POS-INF))))
(dk-peel!)
(fact 'etimes-def)
(fact 'pos-inf-in-rr-pos-star)
(r7y-unfold! 'POS-INF 'y)
(r7y-refl! 'POS-INF)
(fact 'rr-zero-in)
(r7y-pos-inf-not! 0)
(r7y-if-branch! #t (cadr (dk-goal))
  (lambda () (dk-only! '(= POS-INF POS-INF)) (prop))
  (lambda ()
    (r7y-if-branch! #f (cadr (dk-goal))
      (lambda ()
        (dk-only! '(NOT (= POS-INF 0)) '(NOT (= y 0)))
        (prop))
      (lambda () (rfl)))))
(qed 'etimes-pos-inf-left)
(topic! 'etimes-pos-inf-left 'analysis)

;;; ===================================================================
;;; (5) etimes-pos-inf-right -- statement copied through `forall-guarded'
;;; exactly as structure-library/extended-arith.scm:73 writes it.

(sp (make-wff (forall-guarded '(x) '((IN x RR-POS-STAR) (NOT (= x 0)))
                '(= (etimes x POS-INF) POS-INF))))
(dk-peel!)
(fact 'etimes-def)
(fact 'pos-inf-in-rr-pos-star)
(r7y-unfold! 'x 'POS-INF)
(r7y-refl! 'POS-INF)
(fact 'rr-zero-in)
(r7y-pos-inf-not! 0)
(r7y-if-branch! #t (cadr (dk-goal))
  (lambda () (dk-only! '(= POS-INF POS-INF)) (prop))
  (lambda ()
    (r7y-if-branch! #f (cadr (dk-goal))
      (lambda ()
        (dk-only! '(NOT (= x 0)) '(NOT (= POS-INF 0)))
        (prop))
      (lambda () (rfl)))))
(qed 'etimes-pos-inf-right)
(topic! 'etimes-pos-inf-right 'analysis)

;;; ===================================================================
;;; (6) etimes-real-defined -- the GUARDED finite case.
;;;
;;; The axiom it replaces, `etimes-real' (extended-arith.scm:56), quantifies
;;; over ALL reals:
;;;     forall x, y. x in RR and y in RR  =>  etimes(x,y) = bintimes(x,y).
;;; That is FALSE of any definition whose domain is [0,+inf] x [0,+inf], and
;;; with etimes-in-fun beside it, it is INCONSISTENT -- see the header.  The
;;; strongest true form adds nonnegativity.  Stated with the four antecedents
;;; CURRIED rather than conjoined, so a citer's `fact' auto-detaches whichever
;;; are already in context (as 5c-V did for eplus-real-defined).

(sp (make-wff
     '(FORALL x (FORALL y
        (IMPLIES (IN x RR)
          (IMPLIES (<= 0 x)
            (IMPLIES (IN y RR)
              (IMPLIES (<= 0 y)
                (= (etimes x y) (bintimes x y))))))))))
(dk-peel!)
(r7y-in-star! 'x)
(r7y-in-star! 'y)
(fact 'etimes-def)
(r7y-unfold! 'x 'y)
(r7y-not-pos-inf! 'x)
(r7y-not-pos-inf! 'y)
(r7y-if-branch! #f (cadr (dk-goal))
  (lambda ()
    (dk-only! '(NOT (= x POS-INF)) '(NOT (= y POS-INF)))
    (prop))
  (lambda ()
    (fact 'bintimes-apply 'x 'y)
    (subst '(== (bintimes x y) (* x y)))
    (rfl)))
(qed 'etimes-real-defined)
(topic! 'etimes-real-defined 'analysis)
(gloss! 'etimes-real-defined
  "Extended multiplication agrees with ordinary multiplication on the
   NONNEGATIVE reals.  The guard 0 <= x, 0 <= y is not decoration: etimes is a
   function on [0,+inf] x [0,+inf], so etimes(x,y) does not denote when either
   argument is a negative real, and the unguarded form is false -- and,
   together with etimes-in-fun, inconsistent.")

;;; ===================================================================
;;; WHAT THE INTEGRATOR MUST CHANGE
;;; ===================================================================
;;;
;;; A. structure-library/extended-arith.scm
;;;    RETIRE the whole `(fluid-let ((*current-provenance* 'definitional)) ...)'
;;;    block at :51-75 -- the five case equations etimes-real (:56),
;;;    etimes-zero-pos-inf (:61), etimes-pos-inf-zero (:64), etimes-pos-inf-left
;;;    (:68), etimes-pos-inf-right (:73) -- together with the typing axiom
;;;    etimes-in-fun (:80-81) and its `warrant!' (:83-90).  Keep the `gloss!'
;;;    (:92), the `register-operator!' (:103) and the `notation!' (:104): they
;;;    are about the SYMBOL, not about the axioms.
;;;    INSTALL in their place the two forms of scratchpad/r7y/r7y-def.scm
;;;    (a `declare-named-only!' and the provenance-wrapped `etimes-def').
;;;    The file's PROVENANCE block (:23-32) becomes false as it stands and must
;;;    be rewritten: "Everything below except `etimes-in-fun' is FREE ... the
;;;    five etimes equations are a definition by cases of a fresh symbol ...
;;;    so they are wrapped `definitional'" is exactly the reading that hid the
;;;    inconsistency, and its last clause ("the same status eplus-in-fun has in
;;;    extended-reals-pos.scm") points at the axiom 5c-V retired.  The
;;;    inconsistency and its probe path belong in the replacement paragraph.
;;;
;;; B. CITERS: there are NONE to repair.  Measured by grep over
;;;    structure-library/, theorem-library/ and calculus/: no file cites
;;;    etimes-real, etimes-zero-pos-inf, etimes-pos-inf-zero,
;;;    etimes-pos-inf-left, etimes-pos-inf-right or etimes-in-fun by name, and
;;;    no proven theorem's bill names any of them.  The only file that mentions
;;;    `etimes' at all is structure-library/integral.scm, and it mentions the
;;;    CONSTANT: the def-functoids PTWISE-ETIMES (:82) and PTWISE-SCALE (:86),
;;;    and the asserted supports measurable-fn-etimes (:177) and
;;;    integral-homogeneous (:326).  None of them is affected -- and
;;;    integral-homogeneous, the only one that applies etimes to a bare real,
;;;    is already guarded `(IN c RR)' AND `(<= 0 c)', i.e. inside the domain the
;;;    definition gives.
;;;    So `etimes-real' -> `etimes-real-defined' costs nothing today.  It will
;;;    cost one `(<= 0 c)' per site the first time the integral arc computes
;;;    with etimes on a real.
;;;
;;; C. STILL ASSERTED AND NOT TOUCHED HERE.  `pos-inf-not-in-rr'
;;;    (extended-reals.scm:59) is the sole leaf of four of the six bills above.
;;;    It is a bare unwarranted axiom, so those four read `trust: none'.  Same
;;;    user decision as the three axioms 5c-K flagged and the one 5c-V flagged;
;;;    the five of them (pos-inf-not-in-rr, neg-inf-not-in-rr,
;;;    pos-inf-neq-neg-inf, pos-inf-upper-bound, neg-inf-lower-bound) are the
;;;    residue of extended-reals.scm, and `pos-inf-above-reals' beside them is
;;;    already stamped `primitive'.
;;;
;;; ===================================================================
;;; REPORT ONLY -- the rest of the extended-real vocabulary, surveyed for the
;;; same species of defect (a strict `=' or an IN-FUN typing that over-asserts
;;; definedness).
;;; ===================================================================
;;;
;;; The pattern that broke eplus and etimes needs TWO axioms: an UNGUARDED (or
;;; under-guarded) STRICT equation that makes an application denote off the
;;; intended domain, and a `(IN <constant> (FUN A B))' that -- through
;;; `fun-domain-apply-def' -- says it denotes ONLY on A.  Grepped over
;;; structure-library/ and theorem-library/: the ONLY two axioms of the form
;;; `(IN <bare constant> (FUN ...))' in the whole tree were `eplus-in-fun' and
;;; `etimes-in-fun'.  Every other `IN f (FUN ..)' is a hypothesis about a bound
;;; variable.  So the pair-of-axioms defect has no third instance.
;;;
;;; Item by item:
;;;
;;; * ELOWER-BOUNDS, EINF, ETAIL, ELIMINF, ELIMSUP (extended-arith.scm
;;;   :117, :120, :135, :155, :158) are `def-functoid's.  A def-functoid
;;;   installs one rewrite macete `HEAD(args) == body' and no theorem, and `=='
;;;   is quasi-equality: it asserts NOTHING about denotation.  None of the five
;;;   can over-assert definedness, and none has a companion typing axiom.  Clean.
;;;   (What they DO owe is unrelated and already known: ELOWER-BOUNDS is a SEP
;;;   over RR-POS-STAR, so EINF inherits ESUP's obligations, and nothing in the
;;;   tree yet proves `SUBSET (ELOWER-BOUNDS S) RR-POS-STAR' -- the guard every
;;;   esup-* axiom carries.)
;;; * ECONVERGES-TO (:176) is a `def-predicate': an IFF, no denotation claim.
;;;   Clean.
;;; * ESUP (extended-reals-pos.scm :88, :93, :100, :108).  esup-in, esup-upper
;;;   and esup-least are guarded on `(SUBSET S RR-POS-STAR)' and conclude `IN'
;;;   or `<=', never an equation.  `esup-empty', `(= (ESUP EMPTY-SET) 0)', IS a
;;;   strict equation and so does assert that `ESUP(EMPTY-SET)' denotes -- but
;;;   EMPTY-SET satisfies the other three axioms' guard, there is no
;;;   `esup-in-fun' to contradict it, and `esup-in' asserts the same denotation
;;;   anyway.  Consistent; NOT the same species.
;;; * ESUM (theorem-library/extended-sum.scm :38, :51, :64).  All three are
;;;   guarded on `(IN f (FUN (DOM f) RR-POS-STAR))' and conclude `IN' or `<='.
;;;   No equation, no FUN typing of ESUM itself.  Clean of THIS defect.
;;;   A different and real debt sits there, worth stating because it is the
;;;   mirror image: ESUM has no defining equation at all, only three
;;;   characterising laws warranted `informal', so nothing in the tree shows the
;;;   characterisation is SATISFIABLE.  The eplus/etimes lesson applies in the
;;;   other direction -- there the axioms were jointly unsatisfiable and a
;;;   definition settled it; here a definition (the ESUP of the set of finite
;;;   partial sums, which the file's own header writes out) would settle it too.
;;; * rr-pos-star-add-monoid-def (extended-reals-pos.scm :156) is a strict
;;;   equation, `(= RR-POS-STAR-ADD-MONOID (LIST RR-POS-STAR eplus 0))', but its
;;;   right-hand side is a LIST of three denoting terms, so the denotation it
;;;   asserts is free.  5c-V's report already asks for it to become a
;;;   `def-constant'.  Clean.
