;;; interval-extremum.scm -- LOCAL MAXIMUM AND LOCAL MINIMUM OF A FUNCTION ON
;;; A SET.  DEFINITIONS ONLY; Proposition 2.10 is proven in
;;; theorem-library/interval-extremum.scm.
;;;
;;; THE SOURCE is the user's notes (Supplements to Calculus), section 2.4,
;;; Definition 2.9:
;;;
;;;     Suppose f is real valued function defined on [a, b].  f has a LOCAL
;;;     MAXIMUM at theta in [a, b] if and only if there is an alpha > 0 such
;;;     that f(x) >= f(theta) for all |x - theta| <= alpha.  f has a LOCAL
;;;     MINIMUM at theta in [a, b] if and only if there is an alpha > 0 such
;;;     that f(x) <= f(theta) for all |x - theta| <= alpha.
;;;
;;; ONE POINT WHERE THIS FILE DOES NOT COPY THE NOTES, AND WHY.  As printed,
;;; Definition 2.9 has the two inequalities EXCHANGED: it calls `f(x) >=
;;; f(theta) near theta' a local maximum.  The notes' own next paragraph uses
;;; the other reading -- the proof of Proposition 2.10 opens "By definition of
;;; local maximum, there is an alpha > 0 such that f(x + h) <= f(x) for
;;; 0 <= h <= alpha" -- and the first conclusion of 2.10, [D+ f](x) <= 0, is
;;; FALSE under the printed reading (take f(x) = x on [-1, 1] at theta = -1:
;;; f(x) >= f(-1) for every x, so -1 is a `local maximum' as printed, while
;;; D+ f = 1 > 0).  The definitions below therefore read
;;;
;;;     LOCAL MAXIMUM:  f(x) <= f(theta)    near theta
;;;     LOCAL MINIMUM:  f(theta) <= f(x)    near theta
;;;
;;; which is what 2.10 is proved from, and what 2.12's proof (`hence theta is a
;;; local maximum of a function which is differentiable at theta') uses.  This
;;; is reported to the user as a typographical defect of the notes, not as a
;;; decision taken here.
;;;
;;; THE DOMAIN IS A PARAMETER, not an interval.  The notes state the definition
;;; for f on [a, b]; nothing in it is about intervals, and the predicate is
;;; wanted at D = CCINT(a, b) (2.10, 2.12) and, later, at an arbitrary subset
;;; of the line.  The quantifier "for all |x - theta| <= alpha" is read, as the
;;; notes must read it, over the points of D where f is defined: outside D the
;;; term f(x) does not denote, a member of FUN(D, RR) being defined EXACTLY on
;;; D.  Hence the two guards on the inner universal, `x in D' first.
;;;
;;; WHY THE FUN TYPING IS A CONJUNCT.  Without `f in FUN(D, RR)' the inequality
;;; f(x) <= f(theta) is an assertion about terms that need not denote, which is
;;; the species of under-guarded statement CLAUDE.md lists.  With it, every
;;; term in the body is a real.  IS-CONTINUOUS-ON (interval-calculus.scm)
;;; carries its typing conjunct for the same reason.
;;;
;;; NO alpha-DEPENDENCE ON THE INTERVAL.  alpha is not asked to keep
;;; [theta - alpha, theta + alpha] inside D: the notes do not ask it either,
;;; and at an endpoint of [a, b] no such alpha exists.  The points of the
;;; window that are outside D are simply not quantified over.
;;;
;;; BINDER NAMES.  `lmt_', `lma_', `lmx_' -- none folds onto a registered
;;; constant, a class name or an accessor, and none is a name a driver or a
;;; predicate body instantiates at.
;;;
;;; Dependencies: order-predicates.scm (POS-RR), rr-abs (ABS), fun.scm (FUN).
;;; Nothing is proven here.

;;; -----------------------------------------------------------------------
;;; Definition 2.9, the maximum.

(def-predicate 'IS-LOCAL-MAX-AT '(f D lmt_)
  '(AND (IN f (FUN D RR))
        (AND (IN lmt_ D)
             (FORSOME lma_
               (AND (POS-RR lma_)
                    (FORALL lmx_
                      (IMPLIES (IN lmx_ D)
                        (IMPLIES (<= (ABS (- lmx_ lmt_)) lma_)
                                 (<= (f lmx_) (f lmt_))))))))))

(notation! 'IS-LOCAL-MAX-AT 'kind 'predicate 'arity 3
           'english "$1 has a local maximum on $2 at $3")

;;; -----------------------------------------------------------------------
;;; Definition 2.9, the minimum.

(def-predicate 'IS-LOCAL-MIN-AT '(f D lmt_)
  '(AND (IN f (FUN D RR))
        (AND (IN lmt_ D)
             (FORSOME lma_
               (AND (POS-RR lma_)
                    (FORALL lmx_
                      (IMPLIES (IN lmx_ D)
                        (IMPLIES (<= (ABS (- lmx_ lmt_)) lma_)
                                 (<= (f lmt_) (f lmx_))))))))))

(notation! 'IS-LOCAL-MIN-AT 'kind 'predicate 'arity 3
           'english "$1 has a local minimum on $2 at $3")
