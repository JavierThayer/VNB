;;; rake-measure2.scm -- rake batch 5b-F: the indicator function, and the four
;;; SET-LEVEL bricks sigma-algebra.scm's header lists as "NEXT (not stated)".
;;;
;;; FIVE theorems, all `modulo 0':
;;;
;;;   sigma-algebra-empty-in          EMPTY-SET is in every sigma-algebra
;;;   sigma-algebra-union-closed-2    binary union closure
;;;   sigma-algebra-inter-closed-2    binary intersection closure
;;;   sigma-algebra-difference-closed a \ b closure (COMPLEMENT-IN is the
;;;                                   relative difference, theory.scm:677)
;;;   measurable-fn-indicator         structure-library/integral.scm:157,
;;;                                   the assigned leaf -- RETIRE that support
;;;
;;; WHY THE BRICKS COME FIRST.  They are S1-S3 of rake-measure.scm's closing
;;; block, and the indicator needs S1: the tail { x in omega : alpha < 1_a(x) }
;;; is EMPTY-SET when 1 <= alpha, so without "the empty set is measurable" the
;;; third case of the indicator proof cannot close.
;;;
;;; THE INDICATOR, in three conjuncts (IS-MEASURABLE-FN, integral.scm:130).
;;;   (1) IS-SIGMA-ALGEBRA(omega, cA)               -- the hypothesis.
;;;   (2) INDICATOR(omega,a) in FUN(omega, RR-POS-STAR).  `mac INDICATOR' opens
;;;       the VNB-LAMBDA, `lam-t' splits it into the pointwise typing and the
;;;       sethood of omega (which is sigma-algebra-ambient-set), and the
;;;       pointwise value is 1 or 0 -- both in RR-POS-STAR off the DEFINITIONAL
;;;       rr-pos-star-membership.
;;;   (3) for every real alpha, the tail { x in omega : alpha < 1_a(x) } is in
;;;       cA.  VNB's measurability is the TAIL criterion (integral.scm's header
;;;       says so), so this is a case analysis on alpha, not a rewriting:
;;;           alpha < 0        the tail is omega        (sigma-algebra-whole-in)
;;;           0 <= alpha < 1   the tail is a            (the hypothesis)
;;;           1 <= alpha       the tail is EMPTY-SET    (S1, proven above)
;;;       Each case is one class-extensionality argument; the only arithmetic
;;;       is "alpha < 0 implies alpha < 1", which `ineq' does off (IN alpha RR).
;;;
;;; The binary union is the COUNTABLE union at the two-valued family
;;; (VNB-LAMBDA k_ NN (IF (= k_ 0) a_ b_)) -- no padding with EMPTY-SET is
;;; needed, so rake-measure.scm's brick S4 ("big-union-of-padded-family") is
;;; NOT required: every index beyond 0 simply repeats b, and
;;; BIG-UNION n_ NN of that family IS a u b.  Intersection and difference are
;;; then De Morgan off it, each one `prop' over three atoms.
;;;
;;; CITATIONS and their load positions (0-based over the quoted file names in
;;; load.scm):
;;;   base theory (theory.scm, `primitive'): class-extensionality, subset-def,
;;;       empty-set-is-set, empty-set-has-no-members, complement-in-membership,
;;;       union-membership, intersection-membership
;;;   equality-symmetry                theorem-library/axioms.scm          15
;;;   nn-zero-in, rr-zero-in, rr-one-in, nn-is-set   number-systems.scm    34
;;;   IS-SIGMA-ALGEBRA (def iff)       structure-library/sigma-algebra.scm 50
;;;   rr-pos-star-membership           structure-library/extended-reals-pos 76
;;;       (stamped `definitional' at structure-library/definitional-reclass.scm,
;;;        position 106 -- so it contributes {} to the bill)
;;;   IS-MEASURABLE-FN (def iff), INDICATOR   structure-library/integral.scm 125
;;;   nn-one-in                        theorem-library/nn-order-ord.scm   166
;;;   power-mem-in                     theorem-library/discrete-space.scm 198
;;;   sigma-algebra-ambient-set, -whole-in, -complement-closed, -union-closed
;;;                                    theorem-library/rake-measure.scm   199
;;;
;;; LOAD WINDOW [200, end).  lo = 200: rake-measure (199) is the latest thing
;;; cited.  There is no hi -- measurable-fn-indicator is on no bill and nothing
;;; in the library cites it (DEBT-BUNDLE.md section 3), and the four bricks are
;;; new names.
;;;
;;; RETIRE, after this file is wired in:
;;;   structure-library/integral.scm:157-171   measurable-fn-indicator
;;;                                            (support + warrant! + topic! + gloss!)
;;;
;;; Helper prefix: r6f-.

;;; -----------------------------------------------------------------------
;;; file-local kit
;;; -----------------------------------------------------------------------

;;; "the formula mentions the symbol H anywhere" -- for discriminating the
;;; three FORALL conjuncts an IS-SIGMA-ALGEBRA unfold lands.
(define (r6f-mentions? h)
  (lambda (f) (let walk ((x f))
                (cond ((eq? x h) #t)
                      ((pair? x) (or (walk (car x)) (walk (cdr x))))
                      (#t #f)))))

;;; Resolve an IF by its condition WITHOUT rewriting the goal: `if-true' /
;;; `if-false' open TWO leaves -- the CONDITION and the main goal, which gains
;;; the equation IF(c,a,b) = val as an ASSUMPTION (the goal itself is NOT
;;; rewritten; CLAUDE.md).  CLOSER discharges the condition leaf, `ass' by
;;; default (the enclosing case split put it in context).  Returns the equation.
(define (r6f-if-eq! true? ifterm . opt)
  (let* ((closer (if (pair? opt) (car opt) (lambda () (ass))))
         (c      (cadr ifterm))
         (val    (if true? (caddr ifterm) (cadddr ifterm)))
         (want   (if true? c (list 'NOT c)))
         (opened (dk-opened (lambda () (if true? (if-true ifterm) (if-false ifterm)))))
         (conds  (filter (lambda (l) (alpha-equiv? (dk-goal-of l) want)) opened))
         (mains  (filter (lambda (l) (not (memq l conds))) opened)))
    (if (not (and (= 1 (length conds)) (= 1 (length mains))))
        (error "r6f-if-eq!: expected one condition leaf and one main leaf, got"
               (map (lambda (l) (expression->string (dk-goal-of l))) opened)))
    (dk-focus! (car conds)) (closer)
    (dk-focus! (car mains))
    (list '= ifterm val)))

;;; ... and, when the IF IS in the goal, rewrite it away and run THUNK.
(define (r6f-if-branch! true? ifterm thunk . opt)
  (let ((eqn (apply r6f-if-eq! true? ifterm opt)))
    (subst eqn)
    (thunk)))

;;; Split on the IF's condition and hand the surviving VALUE to K.
(define (r6f-case-if! ifterm k)
  (use-em (cadr ifterm)
    (lambda () (r6f-if-branch! #t ifterm (lambda () (k (caddr  ifterm)))))
    (lambda () (r6f-if-branch! #f ifterm (lambda () (k (cadddr ifterm)))))))

;;; From (= IFTERM val) and (REL lhs IFTERM) in context, land (REL lhs val).
;;; `subst' rewrites the GOAL only, so the transfer is a `have!' lane whose
;;; goal is rewritten by the REVERSED equation and then closed by `ass'.
(define (r6f-transfer! eqn rel lhs)
  (let ((val (caddr eqn)) (ifterm (cadr eqn)))
    (fact 'equality-symmetry ifterm val)
    (have! (list rel lhs val)
           (lambda () (subst (list '= val ifterm)) (ass)))))

;;; the first (IN <HEAD-term> _) assumption
(define (r6f-pick-head head what)
  (dk-pick (lambda (g) (and (pair? g) (eq? (car g) 'IN)
                            (pair? (cadr g)) (eq? (car (cadr g)) head)))
           what))

;;; (IN x (POWER omega)) from (IN x cA): the SUBSET conjunct of the defining
;;; iff, read off in a `have!' lane because `mac-h' is destructive and the
;;; IS-SIGMA-ALGEBRA hypothesis is needed again afterwards.
(define (r6f-in-power! x)
  (have! (list 'IN x '(POWER omega))
    (lambda ()
      (dk-split! (dk-landed-1
                  (lambda () (mac-h 'IS-SIGMA-ALGEBRA '(IS-SIGMA-ALGEBRA omega cA)))))
      (mac-h 'subset-def '(SUBSET cA (POWER omega)))
      ;; three FORALLs land from that unfold; discriminate on POWER, never on
      ;; the head.
      (dk-apply! (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                           ((r6f-mentions? 'POWER) f)))
                          "the subset universal")
                 x)
      (ass))))

;;; (IMPLIES (IN w x) (IN w omega)), x already known to be in POWER(omega).
(define (r6f-sub-impl! x w)
  (have! (list 'IMPLIES (list 'IN w x) (list 'IN w 'omega))
         (lambda () (di) (fact 'power-mem-in 'omega x w) (ass))))

;;; the 1-based index of a context formula, for `ineq' (whose premise indices
;;; are 1-BASED, ineq-oracle:206).
(define (r6f-prem f)
  (let loop ((as (dk-asms)) (i 1))
    (cond ((null? as) (error "r6f-prem: not in context" (expression->string f)))
          ((equal? (car as) f) i)
          (#t (loop (cdr as) (+ i 1))))))

;;; (IN c RR-POS-STAR) for c = 0 or 1.
(define (r6f-in-rr-pos-star! c)
  (mac 'rr-pos-star-membership)
  (oi-l)
  (dk-conj-close!
   (lambda ()
     (if (eq? (car (dk-goal)) 'IN)
         (begin (fact (if (equal? c 1) 'rr-one-in 'rr-zero-in)) (ass))
         (arith)))))

;;; Prove (= A B) by class-extensionality and rewrite A into B in the goal.
;;; FWD is run on the leaf that assumes (IN w A) and must reach (IN w B); BWD
;;; on its mirror.  (The IFF goal goes to TWO leaves under one `di', each with
;;; its antecedent already in context.)
(define (r6f-class-eq! a b fwd bwd)
  (have! (list 'FORALL 'w_ (list 'IFF (list 'IN 'w_ a) (list 'IN 'w_ b)))
    (lambda ()
      (let ((w (dk-di-var! (lambda (g) (cadr (cadr g))))))
        (for-each (lambda (l)
                    (dk-focus! l)
                    (if (equal? (dk-goal) (list 'IN w b)) (fwd w) (bwd w)))
                  (dk-opened (lambda () (di)))))))
  (fact 'class-extensionality a b)
  (subst (list '= a b)))

;;; =====================================================================
;;; S1 -- EMPTY-SET is in every sigma-algebra.
;;;
;;; omega is a member and the family is closed under complements, so
;;; omega \ omega is a member; and omega \ omega = EMPTY-SET by
;;; class-extensionality, both sides having no elements.
;;; =====================================================================

(sp (make-wff (forall-guarded '(omega cA) '((IS-SIGMA-ALGEBRA omega cA))
                '(IN EMPTY-SET cA))))
(dk-peel!)
(fact 'empty-set-is-set)
(fact 'sigma-algebra-whole-in 'omega 'cA)
(fact 'sigma-algebra-complement-closed 'omega 'cA 'omega)
(have! '(FORALL x_ (IFF (IN x_ EMPTY-SET) (IN x_ (COMPLEMENT-IN omega omega))))
       (lambda ()
         (let ((v (dk-di-var! (lambda (g) (cadr (cadr g))))))
           (mac 'complement-in-membership)
           (fact 'empty-set-has-no-members v)
           ;; `prop' declines this one: its discharge wants NOT-elim against a
           ;; positive that is still inside the unsplit conjunction, so both
           ;; directions are taken by hand.
           (for-each
            (lambda (l)
              (dk-focus! l)
              (if (eq? (car (dk-goal)) 'AND)
                  (ai (list 'NOT (list 'IN v 'EMPTY-SET)))
                  (begin (dk-split-all!)
                         (ai (list 'NOT (list 'IN v 'omega))))))
            (dk-opened (lambda () (di)))))))
(fact 'class-extensionality 'EMPTY-SET '(COMPLEMENT-IN omega omega))
(subst '(= EMPTY-SET (COMPLEMENT-IN omega omega)))
(ass)
(qed 'sigma-algebra-empty-in)
(topic! 'sigma-algebra-empty-in 'set-quotient)

;;; =====================================================================
;;; S2 -- binary union.
;;;
;;; The countable closure at the two-valued family k |-> IF(k = 0, a, b).
;;; =====================================================================

(sp (make-wff (forall-guarded '(omega cA a_ b_)
                '((IS-SIGMA-ALGEBRA omega cA) (IN a_ cA) (IN b_ cA))
    '(IN (UNION a_ b_) cA))))
(dk-peel!)

(define r6f-fam '(VNB-LAMBDA k_ NN (IF (= k_ 0) a_ b_)))

(have! (list 'IN r6f-fam '(FUN NN cA))
       (lambda ()
         (dk-lam-t!)                     ; closes the (IN NN SET) leaf itself
         (dk-peel!)
         (r6f-case-if! (cadr (dk-goal)) (lambda (v) (ass)))))
(fact 'sigma-algebra-union-closed 'omega 'cA r6f-fam)

(let ((bu (cadr (r6f-pick-head 'BIG-UNION "the countable-union membership"))))
  ;; the equation is oriented UNION = BIG-UNION, because it is the UNION that
  ;; the goal carries and `subst' rewrites the goal.
  (r6f-class-eq! '(UNION a_ b_) bu
    ;; w in a u b |- w in the big union: the witness is 0 on the a side and 1
    ;; on the b side.  `lam-b' needs its argument TYPED first (CLAUDE.md), so
    ;; the (IN 0 NN) / (IN 1 NN) fact is landed ABOVE the beta.
    (lambda (w)
      (let ((orf (dk-landed-1
                  (lambda () (mac-h 'union-membership (list 'IN w '(UNION a_ b_)))))))
        (for-each
         (lambda (m)
           (dk-focus! m)
           (let* ((a-side (member (list 'IN w 'a_) (dk-asms)))
                  (k      (if a-side 0 1))
                  (typing (list 'IN k 'NN)))
             (fact (if a-side 'nn-zero-in 'nn-one-in))
             (for-each (lambda (n)
                         (dk-focus! n)
                         (if (equal? (dk-goal) typing)
                             (ass)
                             (begin (lam-b)
                                    (r6f-if-branch! a-side (caddr (dk-goal))
                                                    (lambda () (ass))
                                                    (lambda () (arith))))))
                       (dk-opened (lambda () (bu-mi k))))))
         (dk-opened (lambda () (ai orf))))))
    ;; w in the big union |- w in a u b: the eigenvariable e indexes the term
    ;; that holds w; beta-reduce the HYPOTHESIS (lam-b-h) and split on e = 0.
    (lambda (w)
      (let* ((landed (dk-landed (lambda () (bu-me (list 'IN w bu)))))
             (ein    (car (filter (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                                   (eq? (caddr f) 'NN)))
                                  landed)))
             (e      (cadr ein))
             (app    (car (filter (lambda (f) (not (eq? f ein))) landed))))
        (lam-b-h app)
        (let ((ifterm (list 'IF (list '= e 0) 'a_ 'b_)))
          (mac 'union-membership)
          (use-em (list '= e 0)
            (lambda ()
              (r6f-transfer! (r6f-if-eq! #t ifterm) 'IN w)
              (oi-l) (ass))
            (lambda ()
              (r6f-transfer! (r6f-if-eq! #f ifterm) 'IN w)
              (oi-r) (ass)))))))
  (ass))
(qed 'sigma-algebra-union-closed-2)
(topic! 'sigma-algebra-union-closed-2 'set-quotient)

;;; =====================================================================
;;; S3a -- binary intersection, De Morgan off S2.
;;;
;;;   a n b  =  omega \ ((omega \ a) u (omega \ b))
;;;
;;; which needs a, b included in omega -- that is the SUBSET conjunct of the
;;; defining iff, hence r6f-in-power! and r6f-sub-impl!.
;;; =====================================================================

(sp (make-wff (forall-guarded '(omega cA a_ b_)
                '((IS-SIGMA-ALGEBRA omega cA) (IN a_ cA) (IN b_ cA))
    '(IN (INTERSECTION a_ b_) cA))))
(dk-peel!)
(fact 'sigma-algebra-ambient-set 'omega 'cA)
(r6f-in-power! 'a_)
(r6f-in-power! 'b_)
(fact 'sigma-algebra-complement-closed 'omega 'cA 'a_)
(fact 'sigma-algebra-complement-closed 'omega 'cA 'b_)
(fact 'sigma-algebra-union-closed-2 'omega 'cA
      '(COMPLEMENT-IN omega a_) '(COMPLEMENT-IN omega b_))
(fact 'sigma-algebra-complement-closed 'omega 'cA
      '(UNION (COMPLEMENT-IN omega a_) (COMPLEMENT-IN omega b_)))
(let ((rhs '(COMPLEMENT-IN omega (UNION (COMPLEMENT-IN omega a_)
                                        (COMPLEMENT-IN omega b_)))))
  ;; Both directions at once: unfold every membership in the IFF goal and hand
  ;; the three remaining atoms to `prop', with the two inclusions as the only
  ;; assumptions left standing (prop has an atom cap).
  (have! (list 'FORALL 'w_ (list 'IFF (list 'IN 'w_ '(INTERSECTION a_ b_))
                                 (list 'IN 'w_ rhs)))
    (lambda ()
      (let ((w (dk-di-var! (lambda (g) (cadr (cadr g))))))
        (r6f-sub-impl! 'a_ w)
        (r6f-sub-impl! 'b_ w)
        (mac 'intersection-membership)
        (mac 'complement-in-membership)
        (mac 'union-membership)
        (mac 'complement-in-membership)   ; the inner two, exposed by the last
        (dk-only! (list 'IMPLIES (list 'IN w 'a_) (list 'IN w 'omega))
                  (list 'IMPLIES (list 'IN w 'b_) (list 'IN w 'omega)))
        (prop))))
  (fact 'class-extensionality '(INTERSECTION a_ b_) rhs)
  (subst (list '= '(INTERSECTION a_ b_) rhs))
  (ass))
(qed 'sigma-algebra-inter-closed-2)
(topic! 'sigma-algebra-inter-closed-2 'set-quotient)

;;; =====================================================================
;;; S3b -- the relative difference a \ b = a n (omega \ b).
;;; =====================================================================

(sp (make-wff (forall-guarded '(omega cA a_ b_)
                '((IS-SIGMA-ALGEBRA omega cA) (IN a_ cA) (IN b_ cA))
    '(IN (COMPLEMENT-IN a_ b_) cA))))
(dk-peel!)
(fact 'sigma-algebra-ambient-set 'omega 'cA)
(r6f-in-power! 'a_)
(fact 'sigma-algebra-complement-closed 'omega 'cA 'b_)
(fact 'sigma-algebra-inter-closed-2 'omega 'cA 'a_ '(COMPLEMENT-IN omega b_))
(let ((rhs '(INTERSECTION a_ (COMPLEMENT-IN omega b_))))
  (have! (list 'FORALL 'w_ (list 'IFF (list 'IN 'w_ '(COMPLEMENT-IN a_ b_))
                                 (list 'IN 'w_ rhs)))
    (lambda ()
      (let ((w (dk-di-var! (lambda (g) (cadr (cadr g))))))
        (r6f-sub-impl! 'a_ w)
        (mac 'intersection-membership)
        (mac 'complement-in-membership)
        (dk-only! (list 'IMPLIES (list 'IN w 'a_) (list 'IN w 'omega)))
        (prop))))
  (fact 'class-extensionality '(COMPLEMENT-IN a_ b_) rhs)
  (subst (list '= '(COMPLEMENT-IN a_ b_) rhs))
  (ass))
(qed 'sigma-algebra-difference-closed)
(topic! 'sigma-algebra-difference-closed 'set-quotient)

;;; =====================================================================
;;; measurable-fn-indicator -- structure-library/integral.scm:157.
;;; =====================================================================

;;; conjunct (2): the FUN typing.
(define (r6f-indicator-typing!)
  (mac 'INDICATOR)
  (dk-lam-t!)
  (dk-peel!)
  (r6f-case-if! (cadr (dk-goal)) (lambda (v) (r6f-in-rr-pos-star! v))))

;;; conjunct (3): the tails.  ALPHA is the peeled real; SEP the tail set.
(define (r6f-indicator-tails!)
  (dk-peel!)
  (mac 'INDICATOR)
  (lam-b)                                ; licensed by the SEP binder's typing
  (let* ((sep   (cadr (dk-goal)))
         (alpha (cadr (cadddr sep))))
    (use-em (list '< alpha 0)
      ;; ---- alpha < 0: every value of the indicator beats alpha ----------
      (lambda ()
        (r6f-class-eq! sep 'omega
          (lambda (w) (sep-me (list 'IN w sep)) (ass))
          (lambda (w)
            (for-each
             (lambda (l)
               (dk-focus! l)
               (if (equal? (dk-goal) (list 'IN w 'omega))
                   (ass)
                   (let ((ifterm (caddr (dk-goal))))
                     (use-em (cadr ifterm)
                       (lambda () (r6f-if-branch! #t ifterm
                                    ;; alpha < 0 < 1
                                    (lambda () (ineq (r6f-prem (list '< alpha 0))))))
                       (lambda () (r6f-if-branch! #f ifterm (lambda () (ass))))))))
             (dk-opened (lambda () (sep-mi)))))
          )
        (fact 'sigma-algebra-whole-in 'omega 'cA)
        (ass))
      (lambda ()
        (use-em (list '< alpha 1)
          ;; ---- 0 <= alpha < 1: the tail is a itself ---------------------
          (lambda ()
            (r6f-class-eq! sep 'a_
              (lambda (w)
                (sep-me (list 'IN w sep))
                (use-em (list 'IN w 'a_)
                  (lambda () (ass))
                  (lambda ()
                    ;; the value is 0 there, so alpha < 0 -- excluded
                    (r6f-transfer! (r6f-if-eq! #f (list 'IF (list 'IN w 'a_) 1 0))
                                   '< alpha)
                    (ai (list 'NOT (list '< alpha 0))))))
              (lambda (w)
                (for-each
                 (lambda (l)
                   (dk-focus! l)
                   (if (equal? (dk-goal) (list 'IN w 'omega))
                       (begin (fact 'power-mem-in 'omega 'a_ w) (ass))
                       (r6f-if-branch! #t (caddr (dk-goal)) (lambda () (ass)))))
                 (dk-opened (lambda () (sep-mi))))))
            (ass))
          ;; ---- 1 <= alpha: the tail is empty ----------------------------
          (lambda ()
            (r6f-class-eq! sep 'EMPTY-SET
              (lambda (w)
                (sep-me (list 'IN w sep))
                (use-em (list 'IN w 'a_)
                  (lambda ()
                    (r6f-transfer! (r6f-if-eq! #t (list 'IF (list 'IN w 'a_) 1 0))
                                   '< alpha)
                    (ai (list 'NOT (list '< alpha 1))))
                  (lambda ()
                    (r6f-transfer! (r6f-if-eq! #f (list 'IF (list 'IN w 'a_) 1 0))
                                   '< alpha)
                    (have! (list '< alpha 1)
                           (lambda () (ineq (r6f-prem (list '< alpha 0)))))
                    (ai (list 'NOT (list '< alpha 1))))))
              (lambda (w)
                (fact 'empty-set-has-no-members w)
                (ai (list 'NOT (list 'IN w 'EMPTY-SET)))))
            (fact 'sigma-algebra-empty-in 'omega 'cA)
            (ass)))))))

(sp (make-wff (forall-guarded '(omega cA a_)
                '((IS-SIGMA-ALGEBRA omega cA) (IN a_ cA))
    '(IS-MEASURABLE-FN omega cA (INDICATOR omega a_)))))
(dk-peel!)
(fact 'sigma-algebra-ambient-set 'omega 'cA)
(r6f-in-power! 'a_)
(mac 'IS-MEASURABLE-FN)
(dk-conj-close!
 (lambda ()
   (let ((g (dk-goal)))
     (cond ((eq? (car g) 'FORALL) (r6f-indicator-tails!))
           ((and (eq? (car g) 'IN) (pair? (caddr g)) (eq? (car (caddr g)) 'FUN))
            (r6f-indicator-typing!))
           (#t (ass))))))
(qed 'measurable-fn-indicator)
(topic! 'measurable-fn-indicator 'plumbing)
