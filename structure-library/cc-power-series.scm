;;; cc-power-series.scm -- THE VOCABULARY OF COMPLEX POWER SERIES (the notes 2.2).
;;; DEFINITIONS ONLY; the laws are PROVEN in theorem-library/cc-power-series-laws.scm
;;; (and the root / ratio tests they rest on in theorem-library/limsup-tests.scm).
;;; Batch 25-A, 2026-09-24.  Every definition below is a DECISION FOR THE USER.
;;;
;;; THE SOURCE.  ~/docs/complex-analysis.pdf, section 2.2 (pp. 24-28).
;;;
;;; A power series sum_k a_k z^k is its coefficient sequence cf in FUN(NN, CC);
;;; the series at a point z is the CC series of the terms k |-> cf(k) z^k
;;; (CC-SERIES-PARTIAL-SUM / CC-SERIES-CONVERGES, theorem-library/cc-series.scm),
;;; so no separate "power series" object is introduced.  Binders are cps..._
;;; (no other body binds them).
;;;
;;; ---------------------------------------------------------------------
;;; CPS-RADIUS(cf).  The notes, p. 25: "The radius of convergence of a power
;;; series sum_{k>=0} a_k x^k in C[[x]] is the supremum of real numbers r such
;;; that sum_{k>=0} |a_k| r^k < infinity.  The radius of convergence is +infinity
;;; if and only if sum |a_k| r^k < infinity for all positive real numbers r."
;;;
;;; Written as the supremum IN [0, +inf] (ESUP, extended-reals-pos.scm) of the set
;;; of NON-NEGATIVE reals r for which the real series sum_k |cf(k)| r^k converges.
;;; The restriction r >= 0 is implicit in the notes (|a_k| r^k is a non-negative
;;; term only for r >= 0, and "< infinity" is said of a series of non-negative
;;; terms); ESUP needs a subset of [0, +inf].  The value is POS-INF exactly when
;;; the set is unbounded, which is the notes' second sentence (a theorem here, not
;;; part of the definition).  The set always contains 0 (sum |a_k| 0^k = |a_0|).
;;; REJECTED ALTERNATIVE: defining the radius by the formula of Prop 2.7,
;;; 1 / lim sup |a_k|^(1/k).  The notes make that formula a PROPOSITION (2.7),
;;; proven from this definition by the root test; defining it would make 2.7 a
;;; tautology and would need an extended reciprocal (1/0 = +inf, 1/+inf = 0) the
;;; tree does not have.
(def-functoid 'CPS-RADIUS '(cf)
  '(ESUP (SEP cpsr_ RR
           (AND (<= 0 cpsr_)
                (SERIES-CONVERGES (VNB-LAMBDA cpsk_ NN (* (magnitude (cf cpsk_)) (power cpsr_ cpsk_))))))))

(notation! 'CPS-RADIUS 'kind 'functoid 'arity 1
           'english "the radius of convergence of the power series with coefficients $1")

;;; ---------------------------------------------------------------------
;;; CC-SUP-NORM(u, X).  The notes, (29): "For u a complex-valued function on a
;;; set X, define ||u||_sup = sup{|u(x)| : x in X}.  Note that ||u||_sup may
;;; assume the value +infinity."  Written as the supremum IN [0, +inf] (ESUP) of
;;; the image of X under x |-> |u(x)|; for u(x) in CC every |u(x)| is a
;;; non-negative real, so the image lies in [0, +inf], and the value is POS-INF
;;; exactly when |u| is unbounded on X, as the notes say.  (The sup of the empty
;;; image is ESUP of the empty set, 0.)
;;; REJECTED ALTERNATIVE: the real SUP (rr-sup-*) under a boundedness hypothesis;
;;; the notes allow the value +infinity and state normal convergence with it.
(def-functoid 'CC-SUP-NORM '(u cpsxs_)
  '(ESUP (IMAGE (VNB-LAMBDA cpsx_ cpsxs_ (magnitude (u cpsx_))) cpsxs_)))

(notation! 'CC-SUP-NORM 'kind 'functoid 'arity 2
           'english "the supremum norm of $1 on $2")

;;; ---------------------------------------------------------------------
;;; IS-NORMALLY-CONVERGENT(u, X).  The notes, p. 26: "Suppose {u_i}_{i>=0} is a
;;; sequence of complex-valued functions defined on a set X.  The infinite series
;;; of functions sum_{i=0}^inf u_i is normally convergent on X if and only if
;;; sum_i ||u_i||_sup < infinity."  A series of extended reals is finite exactly
;;; when every term is finite and the real series converges, which is how it is
;;; written: every ||u_i||_sup is a real number and SERIES-CONVERGES of
;;; i |-> ||u_i||_sup.  u is the FAMILY i |-> u_i (u(i) a function on X).
;;; REJECTED ALTERNATIVE: an extended sum (ESUM) of the norms in [0, +inf] being
;;; finite: equivalent, but every consumer (the M-test, 2.8, 2.10) needs the
;;; ordered real series.
(def-predicate 'IS-NORMALLY-CONVERGENT '(u cpsxs_)
  '(AND (FORALL cpsi_ (IMPLIES (IN cpsi_ NN) (IN (CC-SUP-NORM (u cpsi_) cpsxs_) RR)))
        (SERIES-CONVERGES (VNB-LAMBDA cpsi_ NN (CC-SUP-NORM (u cpsi_) cpsxs_)))))

(notation! 'IS-NORMALLY-CONVERGENT 'kind 'predicate 'arity 2
           'english "the series of the functions $1 is normally convergent on $2")

;;; ---------------------------------------------------------------------
;;; CC-SERIES-LIMIT(f).  The sum of a convergent complex series -- the notes' "the
;;; value of the series" (p. 26: "Let f(x) be the value of the series
;;; sum_{k=0}^inf u_k(x)"; p. 27, Prop 2.10: "the function f(z) = sum_k a_k z^k").
;;; The CC mirror of SERIES-LIMIT (theorem-library/dominated-convergence.scm):
;;; the unique limit of the partial sums, as a description.  It denotes only for a
;;; convergent series (cc-series-limit-converges-to proves that it then is the
;;; limit).  The sum of a power series at z is CC-SERIES-LIMIT of k |-> cf(k) z^k.
;;; REJECTED ALTERNATIVE: a CPS-SUM(cf, z) functoid for power series only; the
;;; general sum is what the notes' normal-convergence paragraph uses, and the
;;; power series sum is one instance of it.
(def-functoid 'CC-SERIES-LIMIT '(f)
  '(IOTA cpsl_ (CC-SERIES-CONVERGES-TO f cpsl_)))

(notation! 'CC-SERIES-LIMIT 'kind 'functoid 'arity 1
           'english "the sum of the complex series $1"
           'noun "sum of the complex series $1")
