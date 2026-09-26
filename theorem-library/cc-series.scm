;;; cc-series.scm -- THE COMPLEX SERIES LAYER: ordered partial sums in CC, and
;;; their convergence in CC-MS.
;;;
;;;     CC-SERIES-PARTIAL-SUM(f, k)   = Sum_{n<k} f(n)          in CC
;;;     CC-SERIES-CONVERGES-TO(f, L)  = those partial sums -> L in CC-MS
;;;     CC-SERIES-CONVERGES(f)        = ... -> some complex limit
;;;
;;; WHAT WAS MISSING, and it is worth stating plainly: NO COMPLEX SUM WAS EVER
;;; FORMED ANYWHERE IN THE TREE.  `SUM-AG' (structure-library/sequences.scm) is
;;; generic over an abelian group and was used over RR's additive group only;
;;; ELL-ONE (theorem-library/dominated-convergence.scm) is defined through
;;; SERIES-CONVERGES of the REAL sequence of magnitudes, so even "the absolutely
;;; summable complex sequences" never adds two complex numbers.  This file is
;;; the missing brick: it is theorem-library/power-series.scm's real layer with
;;; RR-NORMED-FIELD -> CC-NORMED-FIELD and RR-MS -> CC-MS, and
;;; theorem-library/comparison-test-proof.scm's read-offs done again for CC.
;;;
;;; WHY THE ORDERED ROUTE AND NOT THE SUMMABILITY NET.  summability.scm has the
;;; abstract engine -- `absolute-summable-implies-summable' -- but it is stated
;;; over IS-COMPLETE(NAG-METRIC-SPACE grp), and nothing in the tree identifies
;;; NAG-METRIC-SPACE of CC's additive group with CC-MS.  That identification is
;;; a structure-equality obligation of the same species as the metric-subspace
;;; gate in the Ascoli work, and it is not needed: convergence stated directly
;;; in CC-MS meets `cc-complete' (PROVEN modulo 0) with nothing in between.
;;;
;;; WHAT IT COSTS: nothing.  All seven results are `modulo 0'.  In particular
;;; NEITHER `cc-is-normed-field' NOR `sum-ag-type' is cited, and both would have
;;; been the obvious route.  `sum-ag-type' is an unwarranted axiom AND needs
;;; IS-ABELIAN-GROUP of the view, which costs `cc-is-normed-field' -- itself a
;;; bare axiom with no warrant at all, i.e. `trust: none'.  The induction below
;;; goes around both: the group's operation and identity are read off the
;;; INSTANCE (the slot contents of CC-NORMED-FIELD, which are definitional), so
;;; the closure comes from `cc-add-closed' and `cc-zero-in' -- the arithmetic
;;; axioms -- and not from the complexes being a normed field.  This is
;;; comparison-test-proof.scm's own reasoning at R2, transposed.
;;;
;;; THE SLOT HOLDS A LAMBDA, and that is why the read-offs are needed at all.
;;; CC-NORMED-FIELD's ADD slot is the tupled VNB-LAMBDA on CARTESIAN(CC,CC), not
;;; a shared constant: one function per instance, since one object asserted into
;;; five function classes at once proved ZZ = QQ = RR = CC and thence FALSITY
;;; (the 2026-08-29 repair).  So `(OPR (NORMED-FIELD-ADDITIVE-AG
;;; CC-NORMED-FIELD))' has to be unfolded to that lambda before SUM-AG's
;;; recursion says anything about `+'.
;;;
;;; Loads after complex (CC-MS), numeric-instances (CC-NORMED-FIELD), views
;;; (NORMED-FIELD-ADDITIVE-AG), sequences (SUM-AG and its recursion equations),
;;; metric-completeness (CONVERGES-TO / CONVERGES) and driver-kit.

(define ccs-ag '(NORMED-FIELD-ADDITIVE-AG CC-NORMED-FIELD))
(define ccs-add-lam '(VNB-LAMBDA (LIST x_ y_) (CARTESIAN CC CC) (+ x_ y_)))

;;; `di' until an assumption lands -- never a count (CLAUDE.md).
(define (ccs-di-landed!)
  (let loop ((n 0))
    (let ((new (dk-landed* (lambda () (di)))))
      (cond ((pair? new) new)
            ((> n 4) (error "ccs-di-landed!: di landed no assumption"))
            (else (loop (+ n 1)))))))

(define (ccs-di-landed-1!)
  (let ((new (ccs-di-landed!)))
    (if (null? (cdr new)) (car new)
        (error "ccs-di-landed-1!: expected 1 landing" (map expression->string new)))))

;;; =======================================================================
;;; R0.  THE READ-OFFS.  What are the operation and the identity of the
;;; additive abelian group of CC?  NORMED-FIELD-ADDITIVE-AG is a def-functor,
;;; hence a functoid whose body is the LIST of the four source slots: unfold the
;;; functoid, project the accessor, compute the list index, fire the instance's
;;; own slot macete.
;;; =======================================================================

(sp (make-wff (list '== (list 'OPR ccs-ag) ccs-add-lam)))
(mac 'normed-field-additive-ag) (slot 'OPR) (nth-r) (slot 'ADD) (qrfl)
(qed 'cc-additive-ag-opr)
(topic! 'cc-additive-ag-opr 'analysis)
(alias! 'cc-additive-ag-opr "the operation of CC's additive group")

(sp (make-wff (list '== (list 'IDEN ccs-ag) 0)))
(mac 'normed-field-additive-ag) (slot 'IDEN) (nth-r) (slot 'ZERO) (qrfl)
(qed 'cc-additive-ag-iden)
(topic! 'cc-additive-ag-iden 'analysis)
(alias! 'cc-additive-ag-iden "the identity of CC's additive group is 0")

;;; =======================================================================
;;; THE DEFINITIONS.
;;;
;;; The partial sum is SUM-AG over the additive group of CC, i.e. by
;;; construction f(0) + f(1) + ... + f(k-1) in that order.  Convergence is the
;;; ORDERED limit of those partial sums in the complete metric space CC-MS --
;;; the classical meaning of "Sum f(n) = L".  Unconditional (net) summability is
;;; a different predicate, IS-SUMMABLE of summability.scm; the bridge between
;;; them inside a radius of convergence is a later brick, not this one.
;;; =======================================================================

(def-functoid 'CC-SERIES-PARTIAL-SUM '(f k)
  (list 'SUM-AG ccs-ag 'f 'k))

(def-predicate 'CC-SERIES-CONVERGES-TO '(f L)
  '(CONVERGES-TO CC-MS (VNB-LAMBDA k NN (CC-SERIES-PARTIAL-SUM f k)) L))

(def-predicate 'CC-SERIES-CONVERGES '(f)
  '(CONVERGES CC-MS (VNB-LAMBDA k NN (CC-SERIES-PARTIAL-SUM f k))))

(notation! 'CC-SERIES-PARTIAL-SUM 'kind 'functoid 'arity 2
           'english "the $2-th partial sum of the complex series $1")
(notation! 'CC-SERIES-CONVERGES-TO 'kind 'predicate 'arity 2
           'english "the complex series $1 converges to $2")
(notation! 'CC-SERIES-CONVERGES 'kind 'predicate 'arity 1
           'english "the complex series $1 converges")

;;; =======================================================================
;;; R1.  THE EMPTY PARTIAL SUM IS 0.
;;;
;;; Stated with `==' (quasi-equality) because that is what SUM-AG's recursion
;;; installs and because f is UNGUARDED here: off-domain both sides are
;;; undefined, and a strict `=' would assert undefined = undefined.
;;; =======================================================================

(sp (make-wff '(FORALL f (== (CC-SERIES-PARTIAL-SUM f 0) 0))))
(di) (mac 'cc-series-partial-sum) (mac 'sum-ag-zero) (mac 'cc-additive-ag-iden) (qrfl)
(qed 'cc-series-partial-sum-zero)
(topic! 'cc-series-partial-sum-zero 'analysis)
(alias! 'cc-series-partial-sum-zero "the empty complex partial sum is 0")

;;; =======================================================================
;;; R2.  A COMPLEX PARTIAL SUM IS COMPLEX.
;;;
;;; The induction runs at the GROUP level, stated about SUM-AG rather than about
;;; CC-SERIES-PARTIAL-SUM, so that the induction hypothesis is in the same
;;; language as `sum-ag-succ'.  It also HAS to: the surface recurrence below is
;;; guarded on its arguments being complex, and typing those arguments is
;;; exactly this result -- citing it here would be circular.
;;;
;;; k is stated OUTERMOST.  `ni' tests the goal's SHAPE, so a single `di' over
;;; forall([f in fun(nn,cc), k in nn], ...) would take the run whole and the
;;; induction would be gone, with no undo.
;;; =======================================================================

(sp (make-wff (list 'FORALL 'k (list 'IMPLIES '(IN k NN)
   (list 'FORALL 'f (list 'IMPLIES '(IN f (FUN NN CC))
     (list 'IN (list 'SUM-AG ccs-ag 'f 'k) 'CC)))))))

(define ccs0-br (use-induction))

(dk-focus! (cdr (assq 'base ccs0-br)))
(di)
(mac 'sum-ag-zero) (mac 'cc-additive-ag-iden)
(fact 'cc-zero-in)
(ass)

(dk-focus! (cdr (assq 'step ccs0-br)))
(define ccs0-n  (cdr (assq 'var ccs0-br)))
(define ccs0-ih (cdr (assq 'ih  ccs0-br)))
(define ccs0-f  (cadr (ccs-di-landed-1!)))
(inst+ ccs0-ih ccs0-f)                           ; SUM-AG(ag, f, n) in CC
(fact 'fun-apply-type-c ccs0-f 'NN 'CC ccs0-n)   ; f(n) in CC
(mac 'sum-ag-succ) (mac 'cc-additive-ag-opr)
(dk-saturate-slot-ops! 'CC '((+ . cc-add-closed)))
(ass)

(qed 'sum-ag-cc-in-cc)
(topic! 'sum-ag-cc-in-cc 'analysis)

;;; ... and the CC-SERIES-PARTIAL-SUM form, one unfold away.
(sp (make-wff '(FORALL k (IMPLIES (IN k NN)
   (FORALL f (IMPLIES (IN f (FUN NN CC)) (IN (CC-SERIES-PARTIAL-SUM f k) CC)))))))
(di)
(mac 'cc-series-partial-sum)
(fact 'sum-ag-cc-in-cc 'k 'f)
(ass)
(qed 'cc-series-partial-sum-in-cc)
(topic! 'cc-series-partial-sum-in-cc 'analysis)
(alias! 'cc-series-partial-sum-in-cc "a complex partial sum is complex")

;;; =======================================================================
;;; R3.  THE FUNCTOID'S UNFOLD EQUATION, AS A THEOREM.
;;;
;;; `def-functoid' installs only a rewrite macete, so `mac-h' cannot unfold
;;; CC-SERIES-PARTIAL-SUM in a HYPOTHESIS by the functoid's own name -- it warns
;;; `unknown theorem/macete' and the driver sails on with the hypothesis
;;; untouched.  The equation is provable in one line and the resulting THEOREM
;;; is what mac-h rebuilds its rule from.
;;; =======================================================================

(sp (make-wff (list 'FORALL 'f (list 'FORALL 'k
      (list '== '(CC-SERIES-PARTIAL-SUM f k) (list 'SUM-AG ccs-ag 'f 'k))))))
(di) (mac 'cc-series-partial-sum) (qrfl)
(qed 'cc-series-partial-sum-unfold)
(topic! 'cc-series-partial-sum-unfold 'analysis)

;;; =======================================================================
;;; R4.  THE RECURRENCE, IN THE SURFACE LANGUAGE.  After this, every partial-sum
;;; argument is ordinary complex arithmetic.
;;;
;;; GUARDED ON THE ARGUMENTS, which is the weakest hypothesis that works: the
;;; operation slot holds a set function on CARTESIAN(CC,CC), so off the complexes
;;; the left side is an application outside its domain (undefined) while the
;;; right side is not, and `==' would make the unguarded statement false.
;;; Guarding on `IN f (FUN NN CC)' instead would be too strong -- a pointwise-
;;; complex sequence could no longer cite it.
;;; =======================================================================

(sp (make-wff (list 'FORALL 'f (list 'FORALL 'k (list 'IMPLIES '(IN k NN)
   (list 'IMPLIES '(IN (CC-SERIES-PARTIAL-SUM f k) CC)
     (list 'IMPLIES '(IN (f k) CC)
       '(== (CC-SERIES-PARTIAL-SUM f (succ k))
            (+ (CC-SERIES-PARTIAL-SUM f k) (f k))))))))))
(di) (di) (di)
;; put the partial-sum typing into SUM-AG language, since unfolding the goal
;; does the same to it: normalise BOTH sides or `ass' silently fails to match.
(mac-h 'cc-series-partial-sum-unfold '(IN (CC-SERIES-PARTIAL-SUM f k) CC))
(mac 'cc-series-partial-sum) (mac 'sum-ag-succ) (mac 'cc-additive-ag-opr)
(dk-saturate-slot-ops! 'CC '((+ . cc-add-closed)))
(qrfl)
(qed 'cc-series-partial-sum-succ)
(topic! 'cc-series-partial-sum-succ 'analysis)
(alias! 'cc-series-partial-sum-succ "the complex partial-sum recurrence")

;;; =======================================================================
;;; R5.  THE FINITE-SUM TRIANGLE INEQUALITY IN CC.
;;;
;;;     |Sum_{j<k} f(j)|  <=  Sum_{j<k} |f(j)|
;;;
;;; This is the estimate that turns absolute convergence into convergence: with
;;; it, a complex series whose magnitudes sum has Cauchy partial sums, and
;;; `cc-complete' (PROVEN modulo 0) supplies the limit.  The tree had the
;;; two-term inequality (`cc-magnitude-triangle') and the real finite-sum one
;;; (an induction inside comparison-test-proof.scm); this is that induction
;;; again with the complex modulus, and it is the only genuinely new analysis
;;; the complex exponential needs.
;;;
;;; STATED IN TRANSFER FORM: `g' is any sequence agreeing POINTWISE with the
;;; magnitudes of `f', rather than the literal lambda j |-> |f(j)|.  A
;;; conclusion about a literal VNB-LAMBDA can only ever be applied to that
;;; lambda, and every use then owes a beta-reduction under a binder -- the
;;; design note dominated-convergence.scm and continuity-transfer.scm both make.
;;; A caller holding the lambda supplies the agreement by `lam-b'; a caller
;;; holding some other sequence supplies it directly.
;;;
;;; `cc-magnitude-zero' comes first because the base case needs it and nothing
;;; in the tree stated it: `cc-magnitude-zero-iff' gives |z| = 0 iff z = 0, so
;;; the value at 0 is one instance plus `0 = 0'.  It is kept here rather than in
;;; cc-magnitude.scm because this is its only customer; move it up if a second
;;; one appears.
;;; =======================================================================

(sp (make-wff '(= (magnitude 0) 0)))
(fact 'cc-zero-in)
(fact 'cc-magnitude-zero-iff 0)
(have! '(= 0 0) (lambda () (rfl)))
(prop)
(qed 'cc-magnitude-zero)
(topic! 'cc-magnitude-zero 'analysis)
(alias! 'cc-magnitude-zero "the magnitude of 0 is 0")

(define (ccs-idx form)
  (let loop ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "ccs-idx: not in context" form))
          ((equal? (car l) form) i)
          (else (loop (cdr l) (+ i 1))))))

(define (ccs-ineq . fs) (apply ineq (map ccs-idx fs)))

;;; peel until the goal's head is HEAD; guard on progress, error on a miss.
(define (ccs-peel-to! head)
  (let loop ((n 0))
    (let ((g (dk-goal)))
      (cond ((and (pair? g) (eq? (car g) head)) g)
            ((> n 8) (error "ccs-peel-to!: never reached" head))
            (else (di) (loop (+ n 1)))))))

;;; k is stated OUTERMOST: `ni' tests the goal's SHAPE, and one `di' over a
;;; binder run with k inside would take the whole prefix, after which the
;;; induction is gone and there is no undo.
(sp (make-wff
     '(FORALL k (IMPLIES (IN k NN)
        (FORALL f (IMPLIES (IN f (FUN NN CC))
          (FORALL g (IMPLIES (IN g (FUN NN RR))
            (IMPLIES (FORALL j (IMPLIES (IN j NN) (= (g j) (magnitude (f j)))))
              (<= (magnitude (CC-SERIES-PARTIAL-SUM f k))
                  (SERIES-PARTIAL-SUM g k)))))))))))

(define ccs5-br (use-induction))

;;; BASE: both sides are the empty sum, and |0| = 0.
(dk-focus! (cdr (assq 'base ccs5-br)))
(ccs-peel-to! '<=)
(mac 'cc-series-partial-sum-zero)
(mac 'series-partial-sum-zero)
(mac 'cc-magnitude-zero)
(arith)

;;; STEP: one term of each recurrence, then the two-term triangle inequality.
(dk-focus! (cdr (assq 'step ccs5-br)))
(define ccs5-ih (cdr (assq 'ih ccs5-br)))
(ccs-peel-to! '<=)
(define ccs5-S  '(CC-SERIES-PARTIAL-SUM f k))
(define ccs5-fk '(f k))
(define ccs5-ag
  (let loop ((l (dk-asms)))
    (cond ((null? l) (error "cc-series R5: no agreement hypothesis"))
          ((and (pair? (car l)) (eq? (caar l) 'FORALL) (dk-contains? (car l) 'magnitude))
           (car l))
          (else (loop (cdr l))))))

;; both recurrences are GUARDED on their arguments, so type them BEFORE the macs
(fact 'cc-series-partial-sum-in-cc 'k 'f)
(fact 'fun-apply-type-c 'f 'NN 'CC 'k)
(fact 'series-partial-sum-in-rr 'k 'g)
(fact 'fun-apply-type-c 'g 'NN 'RR 'k)
(mac 'cc-series-partial-sum-succ)
(mac 'series-partial-sum-succ)

;; `fact' will not split a conjunctive antecedent -- land the AND first, or the
;; citation lands the IMPLICATION and every later step reads the wrong formula.
(have! (list 'AND (list 'IN ccs5-S 'CC) (list 'IN ccs5-fk 'CC)))
(fact 'cc-magnitude-triangle ccs5-S ccs5-fk)
(fact 'cc-add-closed ccs5-S ccs5-fk)
(dk-deepest (lambda () (inst+ (dk-deepest (lambda () (inst+ ccs5-ih 'f))) 'g)))
(inst+ ccs5-ag 'k)
(fact 'cc-magnitude-closed ccs5-S)
(fact 'cc-magnitude-closed ccs5-fk)
(fact 'cc-magnitude-closed (list '+ ccs5-S ccs5-fk))
(ccs-ineq (list '<= (list 'magnitude (list '+ ccs5-S ccs5-fk))
                (list '+ (list 'magnitude ccs5-S) (list 'magnitude ccs5-fk)))
          (list '<= (list 'magnitude ccs5-S) '(SERIES-PARTIAL-SUM g k))
          (list '= (list 'g 'k) (list 'magnitude ccs5-fk)))

(qed 'cc-series-partial-sum-magnitude-le)
(topic! 'cc-series-partial-sum-magnitude-le 'analysis)
(alias! 'cc-series-partial-sum-magnitude-le
        "the magnitude of a complex partial sum is at most the partial sum of the magnitudes")
