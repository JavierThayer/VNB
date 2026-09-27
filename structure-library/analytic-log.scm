;;; analytic-log.scm -- ANALYTICITY AT A POINT (the notes' Def 2.11) AND THE
;;; PRINCIPAL LOGARITHM (the notes 2.3.3.1, after Prop 2.19).
;;; DEFINITIONS ONLY; the laws are PROVEN in theorem-library/analytic-log-laws.scm.
;;; Batch 38, 2026-09-27 (the user's decision of the same day: IS-ANALYTIC-AT
;;; with the translation to a centre, and the principal logarithm, one batch).
;;;
;;; (1) IS-ANALYTIC-AT(f, U, a) -- Def 2.11: "f is analytic at a iff there is a
;;;     formal power series sum a_k x^k with positive radius of convergence
;;;     such that f(z) = sum a_k (z - a)^k for z near a".  Stated ON an open set
;;;     U (a function lives on its set):
;;;       U open in CC-MS, f in FUN(U, CC), a in U, and there are a coefficient
;;;       function cf in FUN(NN, CC) and a real r with 0 < r < CPS-RADIUS(cf)
;;;       (the radius may be POS-INF; `<' on the extended reals), the ball
;;;       B(a, r) inside U, and f(z) = CC-SERIES-LIMIT(k |-> cf(k) (z - a)^k)
;;;       for every z of B(a, r).
;;;     "Positive radius" is carried by the real r: 0 < r < R.  "Near a" is the
;;;     ball of radius r; any r below the radius will do (the tree's power-series
;;;     layer takes every real 0 < r < R, the 26-A convention).
;;;
;;; (2) CC-LOG(w) -- the principal branch: THE z in CC with -pi < Im z < pi and
;;;     exp z = w.  A def-functoid, IOTA-bodied (the model: R-EXP in
;;;     theorem-library/r-exp.scm, PI in structure-library/cc-pi.scm).  The
;;;     description is satisfiable and unique exactly on the slit plane
;;;     C \ (-inf, 0] = {u in CC : not(Im u = 0 and Re u <= 0)}, by Prop 2.19
;;;     (cc-exp-open-strip-onto, cc-exp-injective-strip); off it the IOTA is
;;;     undefined.  Existence and uniqueness are theorems (cc-log-exists,
;;;     cc-log-unique), the characterisation cc-log-spec follows by iota-d.
;;;     No name is given to the slit plane: every statement carries its
;;;     defining condition as a guard, spelled as cc-exp-bijection-open-strip
;;;     spells its SEP.
;;;
;;; BINDERS.  anl..._ and clg..._ are bound by nothing else in the tree.
;;; Dependencies: structure-library/cc-power-series (CPS-RADIUS,
;;; CC-SERIES-LIMIT), cc-elementary (CC-EXP), cc-pi (PI), metric balls.
;;; LOAD SLOT: after structure-library/cc-pi.

(def-predicate 'IS-ANALYTIC-AT '(anlf_ anlu_ anla_)
  '(AND (IS-OPEN CC-MS anlu_)
   (AND (IN anlf_ (FUN anlu_ CC))
   (AND (IN anla_ anlu_)
        (FORSOME anlcf_
          (AND (IN anlcf_ (FUN NN CC))
               (FORSOME anlr_
                 (AND (IN anlr_ RR)
                 (AND (< 0 anlr_)
                 (AND (< anlr_ (CPS-RADIUS anlcf_))
                 (AND (SUBSET (BALL CC-MS anla_ anlr_) anlu_)
                      (FORALL anlz_
                        (IMPLIES (IN anlz_ (BALL CC-MS anla_ anlr_))
                          (= (anlf_ anlz_)
                             (CC-SERIES-LIMIT
                               (VNB-LAMBDA anlk_ NN
                                 (* (anlcf_ anlk_) (power (- anlz_ anla_) anlk_))))))))))))))))))

(notation! 'IS-ANALYTIC-AT 'kind 'predicate 'arity 3
           'english "$1 is analytic at $3 on $2"
           'tex "$1 \\text{ is analytic at } $3")

(def-functoid 'CC-LOG '(clgw_)
  '(IOTA clgz_ (AND (IN clgz_ CC)
                (AND (< (- PI) (imag-part clgz_))
                (AND (< (imag-part clgz_) PI)
                     (= (CC-EXP clgz_) clgw_))))))

(notation! 'CC-LOG 'kind 'functoid 'arity 1
           'english "the principal logarithm of $1"
           'noun "principal logarithm of $1"
           'tex "\\log\\left($1\\right)")
