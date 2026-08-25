;;; ell-two-act-closed-drive.scm -- THE LEAF LEFT FOR THE USER (2026-08-24).
;;;
;;; theorem-library/ell-two.scm builds the l^2(NN; CC) carrier and closes it
;;; under the pointwise SUM.  Three of the four closure facts a vector-space
;;; declaration needs are cheap (VZERO, VNEG, and the sum, which is the one
;;; with content).  The FOURTH -- closure under the scalar action
;;;
;;;     a in CC,  x in ELL-TWO   =>   (k |-> a x(k)) in ELL-TWO
;;;
;;; is blocked on a real-series lemma the tree does not have, and that lemma is
;;; this drive.
;;;
;;; WHY IT IS BLOCKED, in one line.  |a x(k)|^2 = |a|^2 |x(k)|^2 by
;;; `cc-magnitude-mul' (PROVEN, cc-magnitude.scm), so the squared-magnitude
;;; series of a.x is the CONSTANT MULTIPLE c.F of the squared-magnitude series
;;; F of x, with c = |a|^2 >= 0.  Nothing in the tree says a convergent
;;; nonnegative real series stays convergent under a nonnegative constant
;;; scale.  Every OTHER combination is there: `series-converges-sum'
;;; (dominated-convergence.scm) for f + g, `comparison-test' for domination.
;;; Scaling is the gap.
;;;
;;; ------------------------------------------------------------------
;;; THE TWO RUNGS
;;;
;;;   L1  series-partial-sum-scale
;;;         c in RR, f, g in FUN(NN,RR),  (forall n. g(n) = c * f(n))
;;;           =>  forall k in NN.  SERIES-PARTIAL-SUM(g,k) = c * SERIES-PARTIAL-SUM(f,k)
;;;
;;;       An induction on k.  Base and step are both one rewrite:
;;;         series-partial-sum-zero  S(g,0) = 0 = c * 0 = c * S(f,0)
;;;         series-partial-sum-succ  S(g, succ k) = S(g,k) + g(k)
;;;                                              = c*S(f,k) + c*f(k)
;;;                                              = c*(S(f,k) + f(k))
;;;                                              = c * S(f, succ k)      (crs)
;;;
;;;   L2  series-converges-scale
;;;         c in RR, 0 <= c, f, g in FUN(NN,RR), (forall n. 0 <= f(n)),
;;;         (forall n. g(n) = c * f(n)), SERIES-CONVERGES(f)
;;;           =>  SERIES-CONVERGES(g)
;;;
;;;       `series-partial-sum-bounded' (dominated-convergence.scm:1099) gives a
;;;       real bnd with S(f,k) <= bnd for every k; L1 turns that into
;;;       S(g,k) = c*S(f,k) <= c*bnd (one `rr-le-scale-nonneg' -- the step
;;;       `ineq' cannot take, c and S(f,k) both being variables).  The
;;;       partial sums of g are nondecreasing because g is nonnegative
;;;       (`series-partial-sum-monotone-nonneg'), so `monotone-convergence-rr'
;;;       closes it, exactly as `series-converges-sum' does one file up.
;;;
;;;   Then ell-two-act-closed is four lines: cc-magnitude-mul at (a, x(k)),
;;;   L2 at c = magnitude(a)*magnitude(a), and `mac 'ell-two-membership'.
;;;
;;; ------------------------------------------------------------------
;;; WHAT TO WATCH, and it is a copilot question rather than a mathematical one.
;;;
;;; L1's statement quantifies c_, f, g and the pointwise equation BEFORE the
;;; induction variable k_.  Peel them and the goal IS ni-shaped -- literally
;;; (FORALL k_ (IMPLIES (IN k_ NN) ...)) -- so `ni' fires and this is an
;;; ordinary induction.  Peel ONE `di' further and it is not: `di' takes the
;;; k_ universal with its typing, the goal becomes the bare equation at a
;;; fixed k_, and there is no undo.  That is the case `what-now's induction
;;; lane (suggest.scm, 2026-08-15) exists for -- it prints the (cut "...")
;;; that restates the goal with the NN variable outermost, built from the goal
;;; and the CONTEXT's typings.
;;;
;;; So there are two things to look at, and the second is the interesting one:
;;;
;;;   1. On the leaf this script leaves (ni-shaped), does the panel offer
;;;      (ni)?  The live-fire lane should, and the induction lane should stay
;;;      silent.
;;;   2. Type one more (di) FIRST, then (what-now).  Does the induction lane
;;;      fire, and is the cut it prints the one you would have written?  The
;;;      lane quantifies only eigenvariables that carry a typing assumption;
;;;      c_, f and g all do, but the POINTWISE EQUATION is an untyped
;;;      hypothesis that has to come along in the cut or the induction step
;;;      cannot use it.  If the emitted cut drops it, that is the lane defect
;;;      worth fixing, and it is worth more than the lemma.
;;;
;;; Run:   ./prover -b -i prove-scripts/drives/ell-two-act-closed-drive.scm
;;;        then (what-now) on the open leaf.

(define e2d-stmt
  "forall([c_ in rr, f in fun(nn,rr), g in fun(nn,rr)],
     forall([n_ in nn], g(n_) = c_ * f(n_)) implies
     forall([k_ in nn],
       series-partial-sum(g, k_) = c_ * series-partial-sum(f, k_)))")

(sp (make-wff e2d-stmt))

;;; Peel up to -- and NOT past -- the induction variable.  Measured: the first
;;; `di' takes the three guarded typings and stops at the pointwise
;;; implication; the second takes that implication and leaves the k_ universal
;;; standing.  A third would take k_ too, and there is no undo.
(di)
(di)

(newline)
(display ";;; --- THE LEAF ---") (newline)
(display ";;; goal: ") (display (expr->str (dk-goal) 0)) (newline)
(display ";;; ni-shaped (i.e. would (ni) fire)? ")
(display (let ((g (dk-goal)))
           (and (pair? g) (eq? (car g) 'FORALL)
                (pair? (caddr g)) (eq? (car (caddr g)) 'IMPLIES)
                (equal? (cadr (caddr g)) (list 'IN (cadr g) 'NN)))))
(newline)
(display ";;; context, one per line:") (newline)
(for-each (lambda (a) (display ";;;   ") (display (expr->str a 0)) (newline))
          (dk-asms))
(newline)
(display ";;; available, all PROVEN modulo 0:") (newline)
(display ";;;   series-partial-sum-zero, series-partial-sum-succ  (comparison-test-proof)") (newline)
(display ";;;   series-partial-sum-in-rr, series-partial-sum-seq-apply,") (newline)
(display ";;;   series-partial-sum-seq-in-fun, series-partial-sum-monotone-nonneg") (newline)
(display ";;;   series-partial-sum-bounded, monotone-convergence-rr, comparison-test") (newline)
(display ";;;   rr-le-scale-nonneg, rr-prod-le-prod, rr-sq-nonneg  (rr-order-basics)") (newline)
(display ";;;   cc-magnitude-mul, cc-magnitude-neg                 (cc-magnitude)") (newline)
(display ";;; and in theorem-library/ell-two.scm, new on 2026-08-24:") (newline)
(display ";;;   rr-sq-add-le, cc-magnitude-sq-add-le, ell-two-membership,") (newline)
(display ";;;   ell-two-add-closed, ell-two-neg-closed, ell-two-zero-in,") (newline)
(display ";;;   series-partial-sum-zero-seq, zero-series-converges") (newline)
(newline)
(display ";;; (ni) fires on this leaf.  Base and step are then one rewrite each:") (newline)
(display ";;;   base  (mac 'series-partial-sum-zero)  then the c_*0 = 0 arithmetic") (newline)
(display ";;;   step  (mac 'series-partial-sum-succ), the pointwise equation at k_,") (newline)
(display ";;;         the induction hypothesis, and (crs) for c_*S + c_*f = c_*(S+f)") (newline)
(display ";;; theorem-library/ell-two.scm's `series-partial-sum-zero-seq' is the") (newline)
(display ";;; same induction at c_ = 0 and is the worked example.") (newline)
(newline)
(display ";;; Then type one more (di) and (what-now): that is the induction lane's case.") (newline)
