;;; interval-taylor.scm -- THE VOCABULARY OF TAYLOR'S FORMULA ON AN INTERVAL.
;;; DEFINITIONS ONLY; every theorem is in theorem-library/interval-taylor.scm.
;;;
;;; THE SOURCE is the user's notes (Supplements to Calculus), section 2.6,
;;; Theorem 2.18:
;;;
;;;     Suppose f is a function on [a, b] and n >= 1 an integer such that
;;;     f^(n-1)(x) is defined and continuous for x in [a, b] and differentiable
;;;     for x in (a, b).  Let R_n be such that
;;;
;;;  (19)    f(b) = sum_{k=0}^{n-1} f^(k)(a)/k! (b - a)^k + R_n(a, b).
;;;
;;;     If G is a real-valued function which is continuous on [a, b] and
;;;     differentiable on (a, b), then there is a xi in (a, b) such that
;;;
;;;  (20)    G'(xi) . R_n(a, b) = f^(n)(xi)/(n-1)! (b - xi)^(n-1) . {G(b) - G(a)}.
;;;
;;; and the proof's auxiliary function
;;;
;;;  (21)    F(x) = sum_{k=0}^{n-1} f^(k)(x)/k! (b - x)^k.
;;;
;;; ---------------------------------------------------------------------
;;; WHY THE DERIVATIVES ARE A FAMILY AND NOT AN OPERATOR.
;;;
;;; The library has NTH-DERIV (higher-derivatives.scm), and taylor-proof.scm
;;; proves the theorem with it -- for f in FUN(RR, RR), that is, for a function
;;; differentiable n times on the WHOLE LINE.  The notes ask for f on [a, b]
;;; only, and there is no n-th derivative operator for a function on [a, b]:
;;; NTH-DERIV(f, k + 1) is the derivative of NTH-DERIV(f, k) AT EVERY POINT OF
;;; RR, and the notes' f^(n-1) is not differentiable at a or at b (it is only
;;; asked to be CONTINUOUS there).  The derivatives are therefore GIVEN, as a
;;; family d with d(0) = f, d(k) = f^(k); this is what
;;; docs/real-calculus-statements.tex proposes and what the user approved.
;;;
;;; d IS NOT A MEMBER OF ANY `FUN(NN, ...)'.  d(k) for k < n is a function on
;;; the CLOSED interval and d(n) is a function on the OPEN one, so a single
;;; codomain would have to be a class containing both -- and the only honest
;;; one is the class of all sets.  d is left as a bare family, applied; every
;;; theorem that instantiates at d(k) first lands the typing that the predicate
;;; supplies, which is what the definedness certificate asks for (CLAUDE.md,
;;; "Definedness": an untyped application is never certified).
;;;
;;; WHY d(n) LIVES ON THE OPEN INTERVAL.  The notes never evaluate f^(n)
;;; anywhere but at the interior point xi, and asking for f^(n) on [a, b] would
;;; be a strictly stronger hypothesis than the notes make.  OOINT(a, b) is the
;;; exact domain.
;;;
;;; THE INDEX HYGIENE, checked before anything was proven:
;;;
;;;   * every index is TYPED: the family universal is guarded `tk_ in NN', and
;;;     `succ' is applied only to tk_, which is in NN there (`succ' off NN is
;;;     uninterpreted -- CLAUDE.md's first species of false statement);
;;;   * `power(b - tv_, tk_)' has its exponent in NN, which is what
;;;     `power-succ' / `power-zero' / `power-closed-at' are guarded on;
;;;   * the division by k! is `* recip(FACTORIAL tk_)', never `/': the reader
;;;     desugars `/' to exactly that, and FACTORIAL(k) is a positive real for
;;;     every k in NN (`factorial-real-pos'), so the reciprocal is defined;
;;;   * n >= 1 is a conjunct of the predicate, not a convention: at n = 0 the
;;;     sum (21) is empty and (20) speaks of f^(-1);
;;;   * a < b is a conjunct, so OOINT(a, b) is inhabited and CCINT(a, b) is
;;;     the interval the notes mean.
;;;
;;; THE DEFINED OBJECTS.  TAYLOR-SUM is a TERM in the base point, not a
;;; function; TAYLOR-AUX is the function (21) on [a, b], the only object of
;;; this file that is a member of a FUN class.  TAYLOR-REM is R_n(a, b), which
;;; (19) DEFINES -- the notes' "let R_n be such that (19)" is a definition by
;;; the equation, and the equation determines it, so it is written out.
;;;
;;; BINDER NAMES.  `tk_' (the summation index), `tv_' (the base point of the
;;; sum, a parameter), `tu_' (the argument of TAYLOR-AUX), `tx_' (the interior
;;; point of the family universal).  None folds onto a registered constant, a
;;; class name or an accessor; none is a name a driver mints or a predicate
;;; body binds elsewhere in the calculus arc (CLAUDE.md, "Case folding").
;;;
;;; Dependencies: power-series.scm (SERIES-PARTIAL-SUM), injection.scm
;;; (FACTORIAL), extreme-value.scm (CCINT), interval-calculus.scm (OOINT,
;;; IS-CONTINUOUS-ON, HAS-DERIV-AT), number-systems.scm (power).
;;; Nothing is proven here.

;;; -----------------------------------------------------------------------
;;; The summand of (21) as a family on NN:  k |-> d(k)(tv_) (b - tv_)^k / k!

(def-functoid 'TAYLOR-TERM '(d b tv_)
  '(VNB-LAMBDA tk_ NN
     (* (* ((d tk_) tv_) (power (- b tv_) tk_)) (recip (FACTORIAL tk_)))))

(notation! 'TAYLOR-TERM 'kind 'functoid 'arity 3
           'english "the Taylor summand of the family $1 towards $2 at $3")

;;; -----------------------------------------------------------------------
;;; The sum of (21) at the base point tv_, over k < n.  SERIES-PARTIAL-SUM(g,n)
;;; is sum_{k<n} g(k), so the notes' sum_{k=0}^{n-1} is this at n.

(def-functoid 'TAYLOR-SUM '(d n b tv_)
  '(SERIES-PARTIAL-SUM (TAYLOR-TERM d b tv_) n))

(notation! 'TAYLOR-SUM 'kind 'functoid 'arity 4
           'english "the Taylor sum of $1 of order $2 towards $3 at $4")

;;; -----------------------------------------------------------------------
;;; (21) itself: the auxiliary function F on [a, b].

(def-functoid 'TAYLOR-AUX '(d n a b)
  '(VNB-LAMBDA tu_ (CCINT a b) (TAYLOR-SUM d n b tu_)))

(notation! 'TAYLOR-AUX 'kind 'functoid 'arity 4
           'english "the Taylor auxiliary function of $1 of order $2 on $3 to $4")

;;; -----------------------------------------------------------------------
;;; (19): R_n(a, b) = f(b) - sum_{k<n} f^(k)(a) (b - a)^k / k!.

(def-functoid 'TAYLOR-REM '(d n a b)
  '(- ((d 0) b) (TAYLOR-SUM d n b a)))

(notation! 'TAYLOR-REM 'kind 'functoid 'arity 4
           'english "the Taylor remainder of $1 of order $2 from $3 to $4")

;;; -----------------------------------------------------------------------
;;; The hypothesis of 2.18 on the family.

(def-predicate 'IS-TAYLOR-FAMILY '(d n a b)
  (conjuncts->and
    (list '(IN n NN)
          '(<= 1 n)
          '(IN a RR)
          '(IN b RR)
          '(< a b)
          '(IN (d n) (FUN (OOINT a b) RR))
          '(FORALL tk_
             (IMPLIES (IN tk_ NN)
               (IMPLIES (< tk_ n)
                 (AND (IN (d tk_) (FUN (CCINT a b) RR))
                      (AND (IS-CONTINUOUS-ON (d tk_) (CCINT a b))
                           (FORALL tx_
                             (IMPLIES (IN tx_ (OOINT a b))
                               (HAS-DERIV-AT (d tk_) tx_ ((d (succ tk_)) tx_))))))))))))

(notation! 'IS-TAYLOR-FAMILY 'kind 'predicate 'arity 4
           'english "$1 is a Taylor family of order $2 on $3 to $4")
