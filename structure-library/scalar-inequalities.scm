;;; scalar-inequalities.scm -- a library of important elementary inequalities
;;; over RR, asserted as warranted PSS supports (library phase, no machine
;;; proof).  These are the "mindless tricks" of real analysis: every one is
;;; either a sum-of-squares fact (discharged in one step by the (sos) oracle,
;;; see [[project-next-session-agenda]]) or a one-line calculus estimate.  They
;;; are stated here once, with names, so proofs can cite them by name instead
;;; of re-deriving them.
;;;
;;; Two groups:
;;;   (1) polynomial inequalities -- Young, QM-AM, AM-GM(2), Cauchy-Schwarz(2),
;;;       Bernoulli.  All sum-of-squares / elementary.
;;;   (2) the BOUNDED-FUNCTION family  f(t) = t/(1+t)  on  t >= 0.  This is the
;;;       through-line for the bounded metric (bounded-metric.scm) and the
;;;       countable product metric (product-metric.scm): f is increasing,
;;;       bounded by 1, dominated by its argument, and SUBADDITIVE, which is
;;;       exactly what turns a metric d into the equivalent bounded metric
;;;       d/(1+d) (subadditivity gives the triangle inequality).
;;;
;;; Loads right after order-lemmas.scm (the RR order calculus it leans on).

;;; =======================================================================
;;; (1) Polynomial inequalities.

;;; Young's inequality, p=q=2:  a*b <= (a^2 + b^2)/2.   (a-b)^2 >= 0.
(support 'rr-young-2
  '(FORALL a (IMPLIES (IN a RR) (FORALL b (IMPLIES (IN b RR)
     (<= (* a b) (/ (+ (* a a) (* b b)) 2)))))))
(warrant! 'rr-young-2 'well-known
  "Young's inequality at p=q=2:  a*b <= (a^2+b^2)/2  for all real a,b.
   Equivalent to (a-b)^2 >= 0; closed in one step by (sos \"a - b\").")

;;; AM-GM for two terms, square form (no roots):  4*a*b <= (a+b)^2.
(support 'rr-amgm-2
  '(FORALL a (IMPLIES (IN a RR) (FORALL b (IMPLIES (IN b RR)
     (<= (* 4 (* a b)) (* (+ a b) (+ a b))))))))
(warrant! 'rr-amgm-2 'well-known
  "AM-GM for two terms in square form:  4ab <= (a+b)^2  for all real a,b
   (equality iff a=b).  The root form 2*sqrt(ab) <= a+b for a,b>=0 follows once
   square roots are available.  (a-b)^2 >= 0; closed by (sos \"a - b\").")

;;; Quadratic-mean / arithmetic-mean, square form:  (a+b)^2 <= 2*(a^2+b^2).
(support 'rr-qm-am-2
  '(FORALL a (IMPLIES (IN a RR) (FORALL b (IMPLIES (IN b RR)
     (<= (* (+ a b) (+ a b)) (* 2 (+ (* a a) (* b b)))))))))
(warrant! 'rr-qm-am-2 'well-known
  "Power-mean (QM >= AM) in square form:  (a+b)^2 <= 2(a^2+b^2).  Equivalent to
   (a-b)^2 >= 0; closed by (sos \"a - b\").  The n=2 case of Cauchy-Schwarz with
   the all-ones vector.")

;;; Cauchy-Schwarz for two terms, square form:
;;;   (a1 b1 + a2 b2)^2 <= (a1^2 + a2^2)(b1^2 + b2^2).
(support 'rr-cauchy-schwarz-2
  '(FORALL a1 (IMPLIES (IN a1 RR) (FORALL a2 (IMPLIES (IN a2 RR)
     (FORALL b1 (IMPLIES (IN b1 RR) (FORALL b2 (IMPLIES (IN b2 RR)
       (<= (* (+ (* a1 b1) (* a2 b2)) (+ (* a1 b1) (* a2 b2)))
           (* (+ (* a1 a1) (* a2 a2)) (+ (* b1 b1) (* b2 b2)))))))))))))
(warrant! 'rr-cauchy-schwarz-2 'well-known
  "Cauchy-Schwarz for two terms:  (a1 b1 + a2 b2)^2 <= (a1^2+a2^2)(b1^2+b2^2).
   The difference is the Lagrange identity (a1 b2 - a2 b1)^2 >= 0; closed by
   (sos \"a1*b2 - a2*b1\").  The finite-sum generalisation is
   cauchy-schwarz-finite (analysis-inequalities.scm).")

;;; Bernoulli's inequality:  for x >= -1 and n in NN,  1 + n*x <= (1+x)^n.
(support 'rr-bernoulli
  '(FORALL x (IMPLIES (IN x RR) (FORALL n (IMPLIES (IN n NN)
     (IMPLIES (<= -1 x) (<= (+ 1 (* n x)) (power (+ 1 x) n))))))))
(warrant! 'rr-bernoulli 'well-known
  "Bernoulli's inequality:  (1+x)^n >= 1 + n*x  for real x >= -1 and n in NN.
   Standard induction on n (the step multiplies by 1+x >= 0).")

;;; =======================================================================
;;; (2) The bounded-function family  f(t) = t/(1+t)  on  t >= 0.
;;;
;;; f is the order isomorphism [0,oo) -> [0,1) that turns any metric d into the
;;; topologically equivalent bounded metric  d/(1+d)  (bounded-metric.scm) and
;;; feeds the countable product metric (product-metric.scm).  All five facts
;;; are elementary calculus; together they give nonnegativity, boundedness,
;;; monotonicity, domination, and -- the key one -- subadditivity.

;;; Nonnegativity:  t >= 0  =>  t/(1+t) >= 0.
(support 'bdd-fn-nonneg
  '(FORALL t (IMPLIES (IN t RR) (IMPLIES (<= 0 t) (<= 0 (/ t (+ 1 t)))))))
(warrant! 'bdd-fn-nonneg 'well-known
  "t/(1+t) >= 0 for t >= 0: numerator and denominator are both nonnegative
   (and 1+t >= 1 > 0).")

;;; Boundedness:  t >= 0  =>  t/(1+t) < 1.
(support 'bdd-fn-lt-one
  '(FORALL t (IMPLIES (IN t RR) (IMPLIES (<= 0 t) (< (/ t (+ 1 t)) 1)))))
(warrant! 'bdd-fn-lt-one 'well-known
  "t/(1+t) < 1 for t >= 0: equivalent to t < 1+t, i.e. 0 < 1.  This is what
   makes the derived metric d/(1+d) bounded (every distance < 1).")

;;; Domination:  t >= 0  =>  t/(1+t) <= t.
(support 'bdd-fn-le-arg
  '(FORALL t (IMPLIES (IN t RR) (IMPLIES (<= 0 t) (<= (/ t (+ 1 t)) t)))))
(warrant! 'bdd-fn-le-arg 'well-known
  "t/(1+t) <= t for t >= 0: equivalent to t <= t*(1+t) = t + t^2, i.e.
   0 <= t^2.  Gives one half of the topological equivalence d/(1+d) ~ d (the
   identity from (X,d) to (X, d/(1+d)) is 1-Lipschitz, hence continuous).")

;;; Monotonicity:  0 <= s <= t  =>  s/(1+s) <= t/(1+t).
(support 'bdd-fn-mono
  '(FORALL s (IMPLIES (IN s RR) (FORALL t (IMPLIES (IN t RR)
     (IMPLIES (AND (<= 0 s) (<= s t))
              (<= (/ s (+ 1 s)) (/ t (+ 1 t)))))))))
(warrant! 'bdd-fn-mono 'well-known
  "t/(1+t) = 1 - 1/(1+t) is increasing on [0,oo): s <= t gives 1/(1+t) <=
   1/(1+s).  Lets the triangle inequality for d be pushed through f.")

;;; Subadditivity:  a,b >= 0  =>  (a+b)/(1+a+b) <= a/(1+a) + b/(1+b).
;;; THE key fact: with monotonicity it yields the triangle inequality for the
;;; bounded metric  rho(x,z) = f(d(x,z)) <= f(d(x,y)+d(y,z)) <= f(d(x,y)) +
;;; f(d(y,z)) = rho(x,y) + rho(y,z).
(support 'bdd-fn-subadd
  '(FORALL a (IMPLIES (IN a RR) (FORALL b (IMPLIES (IN b RR)
     (IMPLIES (AND (<= 0 a) (<= 0 b))
       (<= (/ (+ a b) (+ 1 (+ a b)))
           (+ (/ a (+ 1 a)) (/ b (+ 1 b))))))))))
(warrant! 'bdd-fn-subadd 'well-known
  "Subadditivity of f(t)=t/(1+t) on [0,oo):  f(a+b) <= f(a)+f(b).  Since
   1+a+b >= 1+a and 1+a+b >= 1+b,  (a+b)/(1+a+b) = a/(1+a+b) + b/(1+a+b) <=
   a/(1+a) + b/(1+b).  This is the fact that makes d/(1+d) satisfy the triangle
   inequality, hence be a metric.  See [[bounded-metric]].")
