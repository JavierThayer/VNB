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
;;; rr-young-2 RETIRED 2026-09-18 (rake batch 5): proven modulo 0 in theorem-library/rake-inequalities.scm

;;; AM-GM for two terms, square form (no roots):  4*a*b <= (a+b)^2.
;;; rr-amgm-2 RETIRED 2026-09-18 (rake batch 5): proven modulo 0 in theorem-library/rake-inequalities.scm

;;; Quadratic-mean / arithmetic-mean, square form:  (a+b)^2 <= 2*(a^2+b^2).
;;; rr-qm-am-2 RETIRED 2026-09-18 (rake batch 5): proven modulo 0 in theorem-library/rake-inequalities.scm

;;; Cauchy-Schwarz for two terms, square form:
;;;   (a1 b1 + a2 b2)^2 <= (a1^2 + a2^2)(b1^2 + b2^2).
;;; rr-cauchy-schwarz-2 RETIRED 2026-09-18 (rake batch 5): proven modulo 0 in theorem-library/rake-inequalities.scm

;;; Bernoulli's inequality:  for x >= -1 and n in NN,  1 + n*x <= (1+x)^n.
;;; rr-bernoulli RETIRED 2026-09-18 (rake batch 5): proven modulo 0 in theorem-library/rake-inequalities.scm

;;; =======================================================================
;;; (2) The bounded-function family  f(t) = t/(1+t)  on  t >= 0.
;;;
;;; f is the order isomorphism [0,oo) -> [0,1) that turns any metric d into the
;;; topologically equivalent bounded metric  d/(1+d)  (bounded-metric.scm) and
;;; feeds the countable product metric (product-metric.scm).  All five facts
;;; are elementary calculus; together they give nonnegativity, boundedness,
;;; monotonicity, domination, and -- the key one -- subadditivity.

;;; Nonnegativity:  t >= 0  =>  t/(1+t) >= 0.
;;; bdd-fn-nonneg MOVED 2026-09-15 (wave 6) to theorem-library/bdd-metric-basics.scm, where it is PROVEN modulo 0.

;;; Boundedness:  t >= 0  =>  t/(1+t) < 1.
;;; bdd-fn-lt-one MOVED 2026-09-15 (wave 6) to theorem-library/bdd-metric-basics.scm, where it is PROVEN modulo 0.

;;; Domination:  t >= 0  =>  t/(1+t) <= t.
;;; bdd-fn-le-arg MOVED 2026-09-15 (wave 6) to theorem-library/bdd-metric-basics.scm, where it is PROVEN modulo 0.

;;; Monotonicity:  0 <= s <= t  =>  s/(1+s) <= t/(1+t).
;;; bdd-fn-mono MOVED 2026-09-15 (wave 6) to theorem-library/bdd-metric-basics.scm, where it is PROVEN modulo 0.

;;; Subadditivity:  a,b >= 0  =>  (a+b)/(1+a+b) <= a/(1+a) + b/(1+b).
;;; THE key fact: with monotonicity it yields the triangle inequality for the
;;; bounded metric  rho(x,z) = f(d(x,z)) <= f(d(x,y)+d(y,z)) <= f(d(x,y)) +
;;; f(d(y,z)) = rho(x,y) + rho(y,z).
;;; bdd-fn-subadd MOVED 2026-09-15 (wave 6) to theorem-library/bdd-metric-basics.scm, where it is PROVEN modulo 0.
