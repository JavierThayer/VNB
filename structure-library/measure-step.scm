;;; measure-step.scm -- WAVE 2 (2026-10-27..30), wired 2026-10-30 from scratchpad/md/md-vocab.scm.
;;; Library: measure.

;;; md-vocab.scm -- vocabulary for construction-of-measures.pdf ch. 2 (M-D), definitions only.
;;; Agent M-D, 2026-10-28 (NEW DEFINITIONS, the user's to confirm).  DESTINATION: structure-library/measure-step.scm.
;;; Library: measure.  Load window: after real-integral.scm (IS-REAL-MEASURABLE-FN).
;;;
;;;   IS-MEASURABLE-STEP-FN(omega, ca, s)   Def 2.4 with Y = R: a measurable real function taking finitely many values.
;;;                                         (The tree's IS-STEP-FN is the regulated-function notion on an interval.)
(def-predicate 'IS-MEASURABLE-STEP-FN '(omega ca s)
  '(AND (IS-REAL-MEASURABLE-FN omega ca s) (IN (CARD (IMAGE s omega)) NN)))
(notation! 'IS-MEASURABLE-STEP-FN 'kind 'predicate 'arity 3
           'english "$3 is a measurable real step function on $1 with $2")

;;;   LINF-NORM(omega, ca, mu, f)   (32): ||f||_inf = inf{ M in [0, +inf] : |f(x)| <= M for almost all x }, i.e. the
;;;                                 M with mu{ x : M < |f(x)| } = 0.
;;;   IS-MEASURE-ISOMORPHISM(omega, ca, mu, omega2, cb, nu, tt)   tt : X -> Y is measurable with a measurable inverse
;;;                                 and carries mu to nu: nu(B) = mu(tt^-1 B) for B in cb.  (The notes use the term
;;;                                 in Cor 2.35 without a definition; this is the standard one.)
(def-functoid 'LINF-NORM '(omega ca mu f)
  '(EINF (SEP lim_ RR-POS-STAR (= (mu (SEP lix_ omega (< lim_ (abs (f lix_))))) 0))))
(def-predicate 'IS-MEASURE-ISOMORPHISM '(omega ca mu omega2 cb nu tt)
  '(AND (IS-MEASURABLE-MAP omega ca omega2 cb tt)
   (AND (FORALL mib_ (IMPLIES (IN mib_ cb) (= (nu mib_) (mu (SEP mix_ omega (IN (tt mix_) mib_))))))
        (FORSOME mis_ (AND (IS-MEASURABLE-MAP omega2 cb omega ca mis_)
                      (AND (FORALL mix_ (IMPLIES (IN mix_ omega) (= (mis_ (tt mix_)) mix_)))
                           (FORALL miy_ (IMPLIES (IN miy_ omega2) (= (tt (mis_ miy_)) miy_)))))))))
(notation! 'LINF-NORM 'kind 'functoid 'arity 4
           'english "the essential supremum norm of $4 over $1 with respect to $3")
(notation! 'IS-MEASURE-ISOMORPHISM 'kind 'predicate 'arity 7
           'english "$7 is a measure isomorphism from ($1, $3) to ($4, $6)")

;;;   IS-ABSOLUTELY-CONTINUOUS(omega, ca, mu, nu)   Def 3.9: mu << nu, i.e. nu(E) = 0 implies mu(E) = 0 on ca.
(def-predicate 'IS-ABSOLUTELY-CONTINUOUS '(omega ca mu nu)
  '(FORALL ace_ (IMPLIES (IN ace_ ca) (IMPLIES (= (nu ace_) 0) (= (mu ace_) 0)))))
(notation! 'IS-ABSOLUTELY-CONTINUOUS 'kind 'predicate 'arity 4
           'english "$3 is absolutely continuous with respect to $4 on $2")
