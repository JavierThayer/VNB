;;; c-int-oriented.scm -- THE ORIENTED DEFINITE INTEGRAL, the sub-interval
;;; restriction of Def 4.6 (docs/calculus.pdf REMARK 4.9), and ADDITIVITY IN THE
;;; BOUNDS.
;;;
;;; WHAT WAS IN THE WAY.  `IS-ANTIDERIVATIVE(f,phi,a,b)' (antiderivative.scm)
;;; carries `a < b' as a conjunct, deliberately: deriv-zero-implies-constant,
;;; mvt-upper-bound and mvt-lower-bound each want it, and a definition that
;;; omitted it would push the conjunct onto every citation site.  So
;;; `C-INT(phi,a,b)' -- an IOTA over the antiderivatives ON [a,b] -- cannot be
;;; written at a = b or at b < a, and three statements the logarithm needs
;;; cannot be STATED:
;;;
;;;     int_a^a = 0,      int_b^a = -int_a^b,      int_a^c = int_a^b + int_b^c.
;;;
;;; WHY A WRAPPER AND NOT A RELAXED PREDICATE.  The other candidate was to relax
;;; the conjunct to `a <= b'.  Measured and rejected: IS-ANTIDERIVATIVE occurs in
;;; thirteen theorem-library files, `antiderivative-endpoints' -- the projection
;;; that HANDS OUT the `a < b' -- is cited at five sites, and everything downstream
;;; of Prop 4.10 (antiderivative-differ-by-constant, hence Cor 4.11, hence
;;; c-int-value and every c-int-* result) goes through
;;; deriv-zero-implies-constant, which is stated for a NONDEGENERATE interval.
;;; Relaxing re-grades all of that and hands each of those proofs a degenerate
;;; case to dispose of, in exchange for a definition that is still silent about
;;; b < a.  The wrapper is ADDITIVE: not one existing formula changes, and the
;;; bridge `c-int-or-anti' carries every existing c-int-* result into the new
;;; vocabulary by one `subst'.
;;;
;;; THE SHAPE, AND WHY THE CONDITION IS ANTIDERIVABILITY AND NOT `a < b'.  The
;;; obvious wrapper branches on the ORDER,
;;;
;;;     IF a < b THEN C-INT(phi,a,b) ELSE IF b < a THEN -C-INT(phi,b,a) ELSE 0,
;;;
;;; and it is worse in two measurable ways.  What is used instead is the
;;; totalising conditional of SEQ-LIMIT (seq-limit.scm), branching on the
;;; predicate that says the inner term is DEFINED:
;;;
;;;   C-INT-OR(phi,a,b) = IF IS-ANTIDERIVABLE(phi,a,b) THEN  C-INT(phi,a,b)
;;;                       ELSE IF IS-ANTIDERIVABLE(phi,b,a) THEN -C-INT(phi,b,a)
;;;                       ELSE 0.
;;;
;;; The two conditions cannot both hold (`antiderivable-not-reverse'), and
;;; IS-ANTIDERIVABLE(phi,a,b) already entails a < b (`antiderivable-endpoints'),
;;; so this refines the order version rather than replacing it: on the three
;;; order cases it takes the three values the order version takes, WHEN those
;;; values exist.  What it buys:
;;;
;;;  1. C-INT-OR IS TOTAL -- `c-int-or-in-rr' is UNCONDITIONAL.  That is the
;;;     reason the logarithm needs this file: LOG is to be
;;;     `VNB-LAMBDA x RR . C-INT-OR(recip,1,x)', and every continuity and
;;;     derivative theorem in this tree is stated for a member of FUN(RR,RR).
;;;     recip is not antiderivable across 0, so with the order-branching wrapper
;;;     that lambda's body is UNDEFINED at every x <= 0 and the lambda is not in
;;;     FUN(RR,RR) at all.  seq-limit.scm records the same finding one rung down
;;;     ("without it SEQ-LIMIT cannot appear in the body of a VNB-LAMBDA whose
;;;     domain is larger than the set where the family converges").
;;;  2. `=' IS PARTIAL, and with the order version `c-int-or-reverse' is NOT
;;;     PROVABLE as stated.  Two of its three branches close by `qrfl', but the
;;;     third ends at  C-INT(phi,b,a) == -(-C-INT(phi,b,a)), and double negation
;;;     is not syntactic -- it is `crs', which wants the term in RR, which is
;;;     exactly what the order version declines to say.  (Measured, not guessed:
;;;     the order version was built first and got that far.)  With the totalised
;;;     version every term in sight is a real and `c-int-or-reverse' is an
;;;     unconditional `=' -- as is `int_a^a = 0', which needs no typing
;;;     hypothesis either, IS-ANTIDERIVABLE(phi,a,a) being refutable outright.
;;;
;;; The price is the price SEQ-LIMIT pays: where phi is antiderivable in neither
;;; orientation the integral READS 0 rather than being undefined.  That is what
;;; totalising means, and the four branch equations below are stated so that no
;;; proof can use the value 0 without having refuted both conditions.
;;;
;;; THE INTERFACE -- SEQ-LIMIT'S PACKAGING DISCIPLINE.  The three-way IF must
;;; not leak.  It is opened in exactly three places, all in section 3, and every
;;; later proof in this file and every citer outside it works from the READ-OFFS:
;;;
;;;   c-int-or-anti        IS-ANTIDERIVABLE(phi,a,b) => C-INT-OR(phi,a,b)
;;;                                                       = C-INT(phi,a,b)
;;;                        -- THE BRIDGE.  This is the `a < b' bridge the brief
;;;                        asks for, with the hypothesis that makes it TRUE:
;;;                        `a < b' ALONE cannot bridge, because the right-hand
;;;                        side then need not exist, and IS-ANTIDERIVABLE gives
;;;                        `a < b' anyway (antiderivable-endpoints).  Every
;;;                        existing c-int-* theorem is hypothesised on exactly
;;;                        this, so each transfers by one `subst'.
;;;   c-int-or-flip        the same hypothesis, bounds swapped: -C-INT(phi,a,b).
;;;   c-int-or-none        both refuted => 0.  Stated with BOTH refutations as
;;;                        hypotheses, so no proof can reach the value 0 without
;;;                        having established them.
;;;   c-int-or-degenerate  int_a^a = 0.                     UNCONDITIONAL.
;;;   c-int-or-reverse     int_b^a = -int_a^b.              UNCONDITIONAL.
;;;   c-int-or-in-rr       the integral is a real.          UNCONDITIONAL.
;;;   c-int-or-value       (64), oriented -- the master equation, below.
;;;   c-int-or-additive    additivity in the bounds, no ordering hypothesis.
;;;
;;; REMARK 4.9, AND WHY IT IS FREE HERE.  `antiderivative-subinterval' says an
;;; antiderivative on [a,b] is one on any [lo,hi] inside it, WITH THE SAME f.
;;; The notes say "f RESTRICTED to a subinterval [c,d] is an antiderivative of
;;; phi|[c,d]"; there is no restriction operator in this tree and none is
;;; wanted, because antiderivative.scm's convention is already the pointwise
;;; one -- f and phi are members of FUN(RR,RR) and the clauses are tested AT
;;; THE POINTS of the interval, not on a subspace.  So the restriction is
;;; literally the same f and the same phi, at the new bounds.
;;; Def 4.6 asks continuity on the CLOSED interval and differentiability on the
;;; OPEN one, so a restriction lemma needs BOTH containments -- the lesson
;;; antiderivable-affine-subst.scm records, where they had to be HANDED IN
;;; because an affine map of negative slope reverses the interval.  Here the
;;; bounds are literal reals and the hypotheses `a <= lo', `lo < hi', `hi <= b'
;;; give both: closed by rr-leq-transitive, open by rr-le-lt-trans /
;;; rr-lt-le-trans.  Nothing has to be assumed.
;;;
;;; THE MASTER EQUATION.  `c-int-or-value' is (64) for the oriented integral and
;;; it is where the case analysis stops:
;;;
;;;    IS-ANTIDERIVATIVE(f,phi,p,q),  a,b in [p,q]  ==>  C-INT-OR(phi,a,b)
;;;                                                        = f(b) - f(a).
;;;
;;; ONE antiderivative on the ambient interval serves every sub-interval and
;;; every orientation.  Everything after it is arithmetic: additivity in the
;;; bounds is  f(c) - f(a) = (f(b) - f(a)) + (f(c) - f(b)),  one `crs', for
;;; ARBITRARY a, b, c in [p,q] -- no ordering hypothesis at all, which is the
;;; point of having built the orientation first.
;;;
;;; Needs c-int (C-INT, c-int-value, c-int-in-rr), antiderivative
;;; (IS-ANTIDERIVATIVE, IS-ANTIDERIVABLE, antiderivative-endpoints,
;;; antiderivative-map-in-fun), ccint-basics (ccint-membership), rr-order-basics
;;; (rr-lt-trans, rr-lt-trichotomy, rr-lt-le-trans, rr-le-lt-trans),
;;; number-systems (rr-leq-transitive, rr-leq-reflexive, rr-zero-in),
;;; fun-apply-type-proof (fun-apply-type-c) and driver-kit.
;;; =====================================================================

;;; ---- file-local driver helpers (the `co-' prefix) --------------------

;;; Every driver here is `quietly'-wrapped, and `quietly' silences `vnb-guard'
;;; as well as `show': a tactic that ERRORS inside one becomes a silent no-op.
;;; So every proof is followed by this check, which is what surfaces a step that
;;; landed an implication instead of the formula it was supposed to land.
;;; (afs-check, antiderivable-affine-subst.scm, is the same guard.)
(define (co-check name)
  (if (not (proof-done? *ps*))
      (error "c-int-oriented: proof did not close" name)))

;;; peel a leading FORALL/IMPLIES prefix.  `di' is greedy, so this loops on the
;;; goal's HEAD rather than counting calls.
(define (co-peel!)
  (let loop ((n 0))
    (let ((g (dk-goal)))
      (if (and (pair? g) (memq (car g) '(FORALL IMPLIES)) (< n 24))
          (begin (di) (loop (+ n 1)))
          #t))))

;;; `di' until something LANDS.  A guarded universal lands its guard in one
;;; call; a universal whose antecedent is a conjunction peels the quantifier and
;;; lands nothing, the antecedent arriving on the next call.  Loop on the
;;; landing, never on a `di' count.
(define (co-di-landed!)
  (let loop ((fuel 6))
    (let ((l (dk-landed* (lambda () (di)))))
      (cond ((pair? l) l)
            ((> fuel 0) (loop (- fuel 1)))
            (else (error "co-di-landed!: nothing ever landed"))))))

;;; `ai' every conjunction in the context, to exhaustion.
(define (co-split-asms!)
  (let loop ((l (dk-asms)) (n 0))
    (cond ((or (null? l) (> n 20)) #t)
          ((and (pair? (car l)) (eq? (caar l) 'AND))
           (ai (car l)) (loop (dk-asms) (+ n 1)))
          (else (loop (cdr l) n)))))

;;; the context hypothesis that is a FORALL whose CONSEQUENT has head `h'.
;;; Discriminating on the consequent, not on a symbol the formula contains, is
;;; the rule of CLAUDE.md: both universals of Def 4.6 mention f, and the
;;; instantiated copies of each land beside the originals.
(define (co-forall-with h)
  (let loop ((l (dk-asms)))
    (cond ((null? l) (error "co-forall-with: no universal with that consequent" h))
          ((let ((z (car l)))
             (and (pair? z) (eq? (car z) 'FORALL)
                  (pair? (caddr z)) (eq? (car (caddr z)) 'IMPLIES)
                  (pair? (caddr (caddr z)))
                  (eq? (car (caddr (caddr z))) h)))
           (car l))
          (else (loop (cdr l))))))

;;; skolemize an IS-ANTIDERIVABLE hypothesis and return the eigenvariable.
(define (co-skolem! of lo hi)
  (mac-h 'IS-ANTIDERIVABLE (list 'IS-ANTIDERIVABLE of lo hi))
  (cadr (car (dk-landed* (lambda () (dk-ai-head! 'FORSOME))))))

;;; the IF terms C-INT-OR(phi,lo,hi) unfolds to -- outer and inner.
(define (co-if lo hi)
  (list 'IF (list 'IS-ANTIDERIVABLE 'phi lo hi) (list 'C-INT 'phi lo hi)
        (co-if2 lo hi)))
(define (co-if2 lo hi)
  (list 'IF (list 'IS-ANTIDERIVABLE 'phi hi lo) (list '- (list 'C-INT 'phi hi lo)) 0))

;;; =====================================================================
;;; 0.  TWO ORDER FACTS THE TREE DID NOT HAVE.
;;;
;;; `<' is DEFINED (order-predicates.scm) as `<= and not =', so irreflexivity is
;;; the reflexivity of `=' read through the unfold, and asymmetry is one
;;; instance of rr-lt-trans against it.  Neither was in rr-order-basics.scm:
;;; nothing had needed to rule a branch of a conditional OUT before.
;;; =====================================================================

(quietly (lambda ()
(sp (make-wff '(FORALL a (IMPLIES (IN a RR) (NOT (< a a))))))
(co-peel!) (di)                       ; the NOT: assume a < a, goal FALSITY
(mac-h '< '(< a a))
(have! '(= a a) (lambda () (rfl)))
(prop)))
(co-check 'rr-lt-irrefl)
(qed 'rr-lt-irrefl)
(topic! 'rr-lt-irrefl 'inequalities)
(alias! 'rr-lt-irrefl "no real is less than itself")

(quietly (lambda ()
(sp (make-wff '(FORALL a (IMPLIES (IN a RR) (FORALL b (IMPLIES (IN b RR)
     (IMPLIES (< a b) (NOT (< b a)))))))))
(co-peel!) (di)
(fact 'rr-lt-irrefl 'a)
(fact 'rr-lt-trans 'a 'b 'a)
(prop)))
(co-check 'rr-lt-asymm)
(qed 'rr-lt-asymm)
(topic! 'rr-lt-asymm 'inequalities)
(alias! 'rr-lt-asymm "the strict order on RR is asymmetric")

;;; =====================================================================
;;; 1.  TWO PROJECTIONS OF IS-ANTIDERIVABLE.
;;;
;;; `antiderivative-endpoints' projects the bounds out of an ANTIDERIVATIVE;
;;; these do it for the existential, and the second is what makes the two
;;; branches of C-INT-OR mutually exclusive.
;;; =====================================================================

(quietly (lambda ()
(sp (make-wff '(FORALL phi (FORALL a (FORALL b
   (IMPLIES (IS-ANTIDERIVABLE phi a b)
            (AND (IN a RR) (AND (IN b RR) (< a b))))))))) 
(co-peel!)
(let ((fv (co-skolem! 'phi 'a 'b)))
  (fact 'antiderivative-endpoints fv 'phi 'a 'b)
  (ass))))
(co-check 'antiderivable-endpoints)
(qed 'antiderivable-endpoints)
(topic! 'antiderivable-endpoints 'analysis)
(alias! 'antiderivable-endpoints
        "an antiderivable function is antiderivable on a nondegenerate [a,b]")

(quietly (lambda ()
(sp (make-wff '(FORALL phi (FORALL a (FORALL b
   (IMPLIES (IS-ANTIDERIVABLE phi a b) (NOT (IS-ANTIDERIVABLE phi b a))))))))
(co-peel!) (di)
(fact 'antiderivable-endpoints 'phi 'a 'b)
(fact 'antiderivable-endpoints 'phi 'b 'a)
(co-split-asms!)
(fact 'rr-lt-asymm 'a 'b)
(prop)))
(co-check 'antiderivable-not-reverse)
(qed 'antiderivable-not-reverse)
(topic! 'antiderivable-not-reverse 'analysis)
(alias! 'antiderivable-not-reverse
        "a function antiderivable on [a,b] is not antiderivable on [b,a]")

;;; the degenerate interval is not an interval of antiderivability at all.
(quietly (lambda ()
(sp (make-wff '(FORALL phi (FORALL a (NOT (IS-ANTIDERIVABLE phi a a))))))
(co-peel!) (di)
(fact 'antiderivable-endpoints 'phi 'a 'a)
(co-split-asms!)
(fact 'rr-lt-irrefl 'a)
(prop)))
(co-check 'antiderivable-not-degenerate)
(qed 'antiderivable-not-degenerate)
(topic! 'antiderivable-not-degenerate 'analysis)
(alias! 'antiderivable-not-degenerate
        "nothing is antiderivable on a degenerate interval")

;;; =====================================================================
;;; 2.  THE DEFINITION.
;;; =====================================================================

(def-functoid 'C-INT-OR '(phi a b)
  '(IF (IS-ANTIDERIVABLE phi a b) (C-INT phi a b)
       (IF (IS-ANTIDERIVABLE phi b a) (- (C-INT phi b a)) 0)))
(notation! 'C-INT-OR 'kind 'functoid 'arity 3
           'english "the oriented integral of $1 from $2 to $3"
           'tex "\\int_{$2}^{$3} $1")

;;; =====================================================================
;;; 3.  THE THREE BRANCH EQUATIONS.  Every proof below reasons with these; the
;;; IF is never opened again.
;;; =====================================================================

;;; THE BRIDGE.  Every existing c-int-* theorem is hypothesised on
;;; IS-ANTIDERIVABLE (or on IS-ANTIDERIVATIVE, which gives it by one `ew'), so
;;; this equation fires at every one of them: `subst' it and the old statement
;;; is the new one.
(quietly (lambda ()
(sp (make-wff '(FORALL phi (FORALL a (FORALL b
   (IMPLIES (IS-ANTIDERIVABLE phi a b)
            (= (C-INT-OR phi a b) (C-INT phi a b))))))))
(co-peel!)
(mac 'c-int-or)
(for-each (lambda (l) (dk-focus! l) (ass))
          (dk-opened (lambda () (if-true (co-if 'a 'b)))))))
(co-check 'c-int-or-anti)
(qed 'c-int-or-anti)
(topic! 'c-int-or-anti 'analysis)
(alias! 'c-int-or-anti
        "on an interval of antiderivability the oriented integral is C-INT")

;;; the same hypothesis, the bounds the other way round: the sign flips.
(quietly (lambda ()
(sp (make-wff '(FORALL phi (FORALL a (FORALL b
   (IMPLIES (IS-ANTIDERIVABLE phi a b)
            (= (C-INT-OR phi b a) (- (C-INT phi a b)))))))))
(co-peel!)
(fact 'antiderivable-not-reverse 'phi 'a 'b)
(mac 'c-int-or)
(for-each
 (lambda (l)
   (dk-focus! l)
   (if (eq? (car (dk-goal)) 'NOT)
       (ass)
       (for-each (lambda (m)
                   (dk-focus! m)
                   (if (eq? (car (dk-goal)) 'IS-ANTIDERIVABLE)
                       (ass)
                       (begin (subst (list '= (co-if 'b 'a) (co-if2 'b 'a))) (ass))))
                 (dk-opened (lambda () (if-true (co-if2 'b 'a)))))))
 (dk-opened (lambda () (if-false (co-if 'b 'a)))))))
(co-check 'c-int-or-flip)
(qed 'c-int-or-flip)
(topic! 'c-int-or-flip 'analysis)
(alias! 'c-int-or-flip "reversing the bounds negates the oriented integral")

;;; the value where NEITHER orientation is an interval of antiderivability.
;;; Stated with both refutations as hypotheses, so no proof can reach the value
;;; 0 without having established them.
(quietly (lambda ()
(sp (make-wff '(FORALL phi (FORALL a (FORALL b
   (IMPLIES (NOT (IS-ANTIDERIVABLE phi a b))
   (IMPLIES (NOT (IS-ANTIDERIVABLE phi b a))
            (= (C-INT-OR phi a b) 0))))))))
(co-peel!)
(mac 'c-int-or)
(for-each
 (lambda (l)
   (dk-focus! l)
   (if (eq? (car (dk-goal)) 'NOT)
       (ass)
       (for-each (lambda (m)
                   (dk-focus! m)
                   (if (eq? (car (dk-goal)) 'NOT)
                       (ass)
                       (begin (subst (list '= (co-if 'a 'b) (co-if2 'a 'b))) (ass))))
                 (dk-opened (lambda () (if-false (co-if2 'a 'b)))))))
 (dk-opened (lambda () (if-false (co-if 'a 'b)))))))
(co-check 'c-int-or-none)
(qed 'c-int-or-none)
(topic! 'c-int-or-none 'analysis)
(alias! 'c-int-or-none
        "where the function is antiderivable in neither orientation the oriented integral reads zero")

;;; =====================================================================
;;; 4.  WHAT THE ORIENTATION WAS BUILT FOR.  All three unconditional -- no
;;; antiderivability hypothesis, and (int_a^a) not even a typing hypothesis.
;;; =====================================================================

;;;   int_a^a = 0.
(quietly (lambda ()
(sp (make-wff '(FORALL phi (FORALL a (= (C-INT-OR phi a a) 0)))))
(co-peel!)
(fact 'antiderivable-not-degenerate 'phi 'a)
(fact 'c-int-or-none 'phi 'a 'a)
(ass)))
(co-check 'c-int-or-degenerate)
(qed 'c-int-or-degenerate)
(topic! 'c-int-or-degenerate 'analysis)
(alias! 'c-int-or-degenerate
        "the integral over a degenerate interval is zero"
        "int_a^a = 0")

;;;   THE ORIENTED INTEGRAL IS TOTAL.  This is what lets C-INT-OR stand in the
;;;   body of a VNB-LAMBDA over all of RR, which is what LOG needs.
(quietly (lambda ()
(sp (make-wff '(FORALL phi (FORALL a (FORALL b (IN (C-INT-OR phi a b) RR))))))
(co-peel!)
(use-em '(IS-ANTIDERIVABLE phi a b)
  (lambda ()
    (fact 'c-int-or-anti 'phi 'a 'b)
    (fact 'c-int-in-rr 'phi 'a 'b)
    (subst (list '= '(C-INT-OR phi a b) '(C-INT phi a b)))
    (ass))
  (lambda ()
    (use-em '(IS-ANTIDERIVABLE phi b a)
      (lambda ()
        (fact 'c-int-or-flip 'phi 'b 'a)
        (fact 'c-int-in-rr 'phi 'b 'a)
        (fact 'rr-neg-closed '(C-INT phi b a))
        (subst (list '= '(C-INT-OR phi a b) '(- (C-INT phi b a))))
        (ass))
      (lambda ()
        (fact 'c-int-or-none 'phi 'a 'b)
        (subst (list '= '(C-INT-OR phi a b) 0))
        (fact 'rr-zero-in)
        (ass))))))) 
(co-check 'c-int-or-in-rr)
(qed 'c-int-or-in-rr)
(topic! 'c-int-or-in-rr 'analysis)
(alias! 'c-int-or-in-rr "the oriented integral is always a real number")

;;;   int_b^a = -int_a^b, for every phi and every pair of bounds.  The three
;;;   cases are the three branches; the last one needs -0 = 0 and the middle one
;;;   double negation, both `crs' against c-int-in-rr.
(quietly (lambda ()
(sp (make-wff '(FORALL phi (FORALL a (FORALL b
   (= (C-INT-OR phi b a) (- (C-INT-OR phi a b))))))))
(co-peel!)
(use-em '(IS-ANTIDERIVABLE phi a b)
  (lambda ()
    (fact 'c-int-or-anti 'phi 'a 'b)
    (fact 'c-int-or-flip 'phi 'a 'b)
    (subst (list '= '(C-INT-OR phi a b) '(C-INT phi a b)))
    (ass))
  (lambda ()
    (use-em '(IS-ANTIDERIVABLE phi b a)
      (lambda ()
        (fact 'c-int-or-anti 'phi 'b 'a)
        (fact 'c-int-or-flip 'phi 'b 'a)
        (fact 'c-int-in-rr 'phi 'b 'a)
        (subst (list '= '(C-INT-OR phi a b) '(- (C-INT phi b a))))
        (have! '(= (- (- (C-INT phi b a))) (C-INT phi b a)) (lambda () (crs)))
        (subst '(= (- (- (C-INT phi b a))) (C-INT phi b a)))
        (ass))
      (lambda ()
        (fact 'c-int-or-none 'phi 'a 'b)
        (fact 'c-int-or-none 'phi 'b 'a)
        (subst (list '= '(C-INT-OR phi a b) 0))
        (subst (list '= '(C-INT-OR phi b a) 0))
        (have! '(= (- 0) 0) (lambda () (crs)))
        (subst '(= (- 0) 0))
        (rfl)))))))
(co-check 'c-int-or-reverse)
(qed 'c-int-or-reverse)
(topic! 'c-int-or-reverse 'analysis)
(alias! 'c-int-or-reverse
        "reversing the bounds negates the integral"
        "int_b^a = -int_a^b")

;;; =====================================================================
;;; 5.  REMARK 4.9 -- SUB-INTERVAL RESTRICTION.
;;;
;;; The same f serves the sub-interval.  Def 4.6 asks continuity on the CLOSED
;;; interval and differentiability on the OPEN one, so both containments are
;;; needed; from `a <= lo', `lo < hi', `hi <= b' both follow, the closed one by
;;; rr-leq-transitive and the open one by rr-le-lt-trans / rr-lt-le-trans.
;;; Nothing is assumed.
;;; =====================================================================

;;; run THUNK at every atomic conjunct of an AND goal, splitting with `di' and
;;; following `dk-opened' -- LOCAL, unlike a sweep over (proof-leaves), so it is
;;; safe inside a `have!' lane.
(define (co-each-conjunct! thunk)
  (if (eq? (car (dk-goal)) 'AND)
      (for-each (lambda (n) (dk-focus! n) (co-each-conjunct! thunk))
                (dk-opened (lambda () (di))))
      (thunk)))

;;; the three transitivity citations.  Each has a CONJUNCTIVE antecedent, which
;;; `fact' will not detach, so the AND is put in context first.
(define (co-le-trans! x y z)
  (have! (list 'AND (list 'IN x 'RR) (list 'AND (list 'IN y 'RR) (list 'IN z 'RR))))
  (have! (list 'AND (list '<= x y) (list '<= y z)))
  (fact 'rr-leq-transitive x y z) (ass))
(define (co-le-lt! x y z)
  (have! (list 'AND (list '<= x y) (list '< y z)))
  (fact 'rr-le-lt-trans x y z) (ass))
(define (co-lt-le! x y z)
  (have! (list 'AND (list '< x y) (list '<= y z)))
  (fact 'rr-lt-le-trans x y z) (ass))

;;; (IN v RR) off a CCINT membership, WITHOUT destroying the membership: `mac-h'
;;; REPLACES the hypothesis it unfolds and c-int-or-value wants the CCINT form
;;; itself.  Same lane trick as `ad-rr-of!' (antiderivative.scm).
(define (co-in-rr! v lo hi)
  (have! (list 'IN v 'RR)
    (lambda ()
      (mac-h 'ccint-membership (list 'IN v (list 'CCINT lo hi)))
      (prop))))

(quietly (lambda ()
(sp (make-wff
     (forall-guarded '(f phi a b lo hi)
       (list '(IS-ANTIDERIVATIVE f phi a b) '(IN lo RR) '(IN hi RR)
             '(<= a lo) '(< lo hi) '(<= hi b))
       '(IS-ANTIDERIVATIVE f phi lo hi))))
(co-peel!)
(mac-h 'IS-ANTIDERIVATIVE '(IS-ANTIDERIVATIVE f phi a b))
(co-split-asms!)
(mac 'IS-ANTIDERIVATIVE)
(co-each-conjunct!
 (lambda ()
   (let ((g (dk-goal)))
     (cond
      ;; the five atomic conjuncts: four typings and the nondegeneracy
      ((memq (car g) '(IN <)) (ass))
      ;; CONTINUITY on the closed [lo,hi]: every point of it is a point of [a,b]
      ((eq? (car (caddr (caddr g))) 'IS-CONTINUOUS-AT)
       (let* ((mem (car (co-di-landed!)))
              (xv  (cadr mem)))
         (mac-h 'ccint-membership mem)
         (co-split-asms!)
         (have! (list 'IN xv '(CCINT a b))
           (lambda ()
             (mac 'ccint-membership)
             (co-each-conjunct!
              (lambda ()
                (let ((h (dk-goal)))
                  ;; (IN xv RR) / (<= a xv) / (<= xv b) -- discriminated on
                  ;; WHICH SIDE the eigenvariable sits, not on a bound's name.
                  (cond ((eq? (car h) 'IN)      (ass))
                        ((eq? (cadr h) xv)      (co-le-trans! xv 'hi 'b))
                        (else                   (co-le-trans! 'a 'lo xv))))))))
         (inst+ (co-forall-with 'IS-CONTINUOUS-AT) xv)
         (ass)))
      ;; DIFFERENTIABILITY on the open (lo,hi): a < th < b there.  The antecedent
      ;; is a conjunction, so the quantifier and the antecedent come on separate
      ;; `di's -- loop on the LANDING.  And instantiate BEFORE splitting: `fact'
      ;; and `detach!' want the AND back.
      (else
       (let* ((h  (car (co-di-landed!)))
              (th (cadr (cadr h))))
         (co-split-asms!)
         (co-le-lt! 'a 'lo th)
         (co-lt-le! th 'hi 'b)
         (let* ((ld (dk-landed* (lambda () (inst+ (co-forall-with 'IS-DIFF-AT) th))))
                (im (car (filter (lambda (z) (and (pair? z) (eq? (car z) 'IMPLIES))) ld))))
           (have! (list 'AND (list 'IN th 'RR)
                        (list 'AND (list '< 'a th) (list '< th 'b))))
           (detach! im)
           (ass)))))))) ))
(co-check 'antiderivative-subinterval)
(qed 'antiderivative-subinterval)
(topic! 'antiderivative-subinterval 'analysis)
(alias! 'antiderivative-subinterval
        "Remark 4.9"
        "an antiderivative on [a,b] is an antiderivative on every subinterval")

(quietly (lambda ()
(sp (make-wff
     (forall-guarded '(phi a b lo hi)
       (list '(IS-ANTIDERIVABLE phi a b) '(IN lo RR) '(IN hi RR)
             '(<= a lo) '(< lo hi) '(<= hi b))
       '(IS-ANTIDERIVABLE phi lo hi))))
(co-peel!)
(let ((fv (co-skolem! 'phi 'a 'b)))
  (fact 'antiderivative-subinterval fv 'phi 'a 'b 'lo 'hi)
  (mac 'IS-ANTIDERIVABLE)
  (ew fv)
  (ass))))
(co-check 'antiderivable-subinterval)
(qed 'antiderivable-subinterval)
(topic! 'antiderivable-subinterval 'analysis)
(alias! 'antiderivable-subinterval
        "Remark 4.9 (existential form)"
        "antiderivability on [a,b] restricts to every subinterval")

;;; =====================================================================
;;; 6.  THE MASTER EQUATION -- (64) for the oriented integral.
;;;
;;; ONE antiderivative on the ambient [p,q] serves every sub-interval and every
;;; orientation, and this is the only theorem in the file that opens the three
;;; order cases.  Everything after it is arithmetic.
;;; =====================================================================

(quietly (lambda ()
(sp (make-wff
     (forall-guarded '(f phi p q a b)
       (list '(IS-ANTIDERIVATIVE f phi p q)
             '(IN a (CCINT p q)) '(IN b (CCINT p q)))
       '(= (C-INT-OR phi a b) (- (f b) (f a))))))
(co-peel!)
(fact 'antiderivative-endpoints 'f 'phi 'p 'q)
(mac-h 'ccint-membership '(IN a (CCINT p q)))
(mac-h 'ccint-membership '(IN b (CCINT p q)))
(co-split-asms!)
(fact 'antiderivative-map-in-fun 'f 'phi 'p 'q)
(fact 'fun-apply-type-c 'f 'RR 'RR 'a)
(fact 'fun-apply-type-c 'f 'RR 'RR 'b)
(fact 'rr-lt-trichotomy 'a 'b)
(use-cases '((< a b) (= a b) (< b a))
  ;; a < b: Remark 4.9 puts an antiderivative on [a,b], and (64) reads it off.
  (lambda ()
    (fact 'antiderivative-subinterval 'f 'phi 'p 'q 'a 'b)
    (have! '(IS-ANTIDERIVABLE phi a b)
           (lambda () (mac 'IS-ANTIDERIVABLE) (ew 'f) (ass)))
    (fact 'c-int-or-anti 'phi 'a 'b)
    (fact 'c-int-value 'f 'phi 'a 'b)
    (subst '(= (C-INT-OR phi a b) (C-INT phi a b)))
    (ass))
  ;; a = b: the degenerate branch, and f(b) - f(b) = 0 is one `crs'.
  (lambda ()
    (subst '(= a b))
    (fact 'c-int-or-degenerate 'phi 'b)
    (subst '(= (C-INT-OR phi b b) 0))
    (crs))
  ;; b < a: Remark 4.9 on [b,a], the flip equation, and one `crs' for the sign.
  (lambda ()
    (fact 'antiderivative-subinterval 'f 'phi 'p 'q 'b 'a)
    (have! '(IS-ANTIDERIVABLE phi b a)
           (lambda () (mac 'IS-ANTIDERIVABLE) (ew 'f) (ass)))
    (fact 'c-int-or-flip 'phi 'b 'a)
    (fact 'c-int-value 'f 'phi 'b 'a)
    (subst '(= (C-INT-OR phi a b) (- (C-INT phi b a))))
    (subst '(= (C-INT phi b a) (- (f a) (f b))))
    (crs)))))
(co-check 'c-int-or-value)
(qed 'c-int-or-value)
(topic! 'c-int-or-value 'analysis)
(alias! 'c-int-or-value
        "equation (64), oriented"
        "the oriented integral between any two points of [p,q] is f(b) - f(a)")

;;; =====================================================================
;;; 7.  ADDITIVITY IN THE BOUNDS.
;;; =====================================================================

;;; THE GENERAL FORM -- no ordering hypothesis at all, which is the whole reason
;;; the orientation was built.  a, b, c are any three points of an interval of
;;; antiderivability, in any order.  One antiderivative, three read-offs, and
;;;    f(c) - f(a)  =  (f(b) - f(a)) + (f(c) - f(b)),
;;; which is one `crs'.
(quietly (lambda ()
(sp (make-wff
     (forall-guarded '(phi p q a b c)
       (list '(IS-ANTIDERIVABLE phi p q)
             '(IN a (CCINT p q)) '(IN b (CCINT p q)) '(IN c (CCINT p q)))
       '(= (C-INT-OR phi a c) (+ (C-INT-OR phi a b) (C-INT-OR phi b c))))))
(co-peel!)
(let ((fv (co-skolem! 'phi 'p 'q)))
  (co-in-rr! 'a 'p 'q)
  (co-in-rr! 'b 'p 'q)
  (co-in-rr! 'c 'p 'q)
  (fact 'antiderivative-map-in-fun fv 'phi 'p 'q)
  (fact 'fun-apply-type-c fv 'RR 'RR 'a)
  (fact 'fun-apply-type-c fv 'RR 'RR 'b)
  (fact 'fun-apply-type-c fv 'RR 'RR 'c)
  (fact 'c-int-or-value fv 'phi 'p 'q 'a 'c)
  (fact 'c-int-or-value fv 'phi 'p 'q 'a 'b)
  (fact 'c-int-or-value fv 'phi 'p 'q 'b 'c)
  (subst (list '= '(C-INT-OR phi a c) (list '- (list fv 'c) (list fv 'a))))
  (subst (list '= '(C-INT-OR phi a b) (list '- (list fv 'b) (list fv 'a))))
  (subst (list '= '(C-INT-OR phi b c) (list '- (list fv 'c) (list fv 'b))))
  (crs))))
(co-check 'c-int-or-additive)
(qed 'c-int-or-additive)
(topic! 'c-int-or-additive 'analysis)
(alias! 'c-int-or-additive
        "additivity in the bounds"
        "int_a^c = int_a^b + int_b^c, for any three points of an interval of antiderivability")

;;; THE SAME FACT IN C-INT VOCABULARY, for a caller who has a < b < c and does
;;; not want to hear about the orientation.  Both sub-intervals are Remark 4.9
;;; instances of the ambient one, so one antiderivative serves all three (64)s.
(quietly (lambda ()
(sp (make-wff
     (forall-guarded '(phi a b c)
       (list '(IS-ANTIDERIVABLE phi a c) '(IN b RR) '(< a b) '(< b c))
       '(= (C-INT phi a c) (+ (C-INT phi a b) (C-INT phi b c))))))
(co-peel!)
(let ((fv (co-skolem! 'phi 'a 'c)))
  (fact 'antiderivative-endpoints fv 'phi 'a 'c)
  (co-split-asms!)
  (fact 'antiderivative-map-in-fun fv 'phi 'a 'c)
  (fact 'fun-apply-type-c fv 'RR 'RR 'a)
  (fact 'fun-apply-type-c fv 'RR 'RR 'b)
  (fact 'fun-apply-type-c fv 'RR 'RR 'c)
  (fact 'rr-leq-reflexive 'a)
  (fact 'rr-leq-reflexive 'c)
  (fact 'rr-lt-implies-le 'a 'b)
  (fact 'rr-lt-implies-le 'b 'c)
  (fact 'antiderivative-subinterval fv 'phi 'a 'c 'a 'b)
  (fact 'antiderivative-subinterval fv 'phi 'a 'c 'b 'c)
  (fact 'c-int-value fv 'phi 'a 'c)
  (fact 'c-int-value fv 'phi 'a 'b)
  (fact 'c-int-value fv 'phi 'b 'c)
  (subst (list '= '(C-INT phi a c) (list '- (list fv 'c) (list fv 'a))))
  (subst (list '= '(C-INT phi a b) (list '- (list fv 'b) (list fv 'a))))
  (subst (list '= '(C-INT phi b c) (list '- (list fv 'c) (list fv 'b))))
  (crs))))
(co-check 'c-int-add-bounds)
(qed 'c-int-add-bounds)
(topic! 'c-int-add-bounds 'analysis)
(alias! 'c-int-add-bounds
        "additivity in the bounds, ordered"
        "for a < b < c the integral over [a,c] splits at b")
