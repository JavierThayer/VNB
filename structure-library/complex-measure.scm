;;; complex-measure.scm -- WAVE 2 (2026-10-27..30), wired 2026-10-30 from scratchpad/mf/mf-cvocab.scm.
;;; Library: measure.

;;; mf-cvocab.scm -- complex measures (construction-of-measures.pdf ch. 3, sec. 5): DEFINITIONS ONLY.
;;; Agent M-F, 2026-10-29 (NEW DEFINITIONS, the user's to confirm).
;;; DESTINATION: structure-library/complex-measure.scm.  Library: measure.
;;; Load window: after structure-library/measure.scm, real-integral.scm (RINTEGRAL, IS-INTEGRABLE,
;;; IS-REAL-MEASURABLE-FN), the CC vocabulary (REAL-PART, IMAG-PART, +i, magnitude).
;;;
;;; IS-FINITE-MEASURE(omega, ca, mu)      a measure with mu(X) finite.
;;; IS-COMPLEX-MEASURE(omega, ca, nu)     the user's definition (spectral plan, notes-67; th-main.pdf 4.4.1): nu : ca -> CC
;;;   is a combination nu = nu1 - nu2 + i(nu3 - nu4) of four FINITE countably additive measures.  The notes' Def 3.16
;;;   (real and imaginary parts finite signed measures) is equivalent by Prop 3.12 (Jordan) and (63).
;;; IS-COMPLEX-MEASURABLE-FN(omega, ca, u)   u : X -> CC with measurable real and imaginary parts.
;;; COMPLEX-INTEGRAL(omega, ca, mu, u)    int u dmu = int Re u dmu + i int Im u dmu, for a positive measure mu.
;;; IS-COMPLEX-NULL-SET(omega, ca, nu, a) a is nu-null: a measurable, and nu vanishes on every measurable subset of a
;;;   (the notes' "null sets of nu" in Prop 3.17 (1)).

(def-predicate 'IS-FINITE-MEASURE '(omega ca mu)
  '(AND (IS-MEASURE omega ca mu) (IN (mu omega) RR)))
(notation! 'IS-FINITE-MEASURE 'kind 'predicate 'arity 3
           'english "$3 is a finite countably additive measure on the sigma-algebra $2 of subsets of $1")

(def-predicate 'IS-COMPLEX-MEASURE '(omega ca nu)
  '(AND (IS-SIGMA-ALGEBRA omega ca)
     (AND (IN nu (FUN ca CC))
       (FORSOME cm1_ (FORSOME cm2_ (FORSOME cm3_ (FORSOME cm4_
         (AND (IS-FINITE-MEASURE omega ca cm1_)
           (AND (IS-FINITE-MEASURE omega ca cm2_)
             (AND (IS-FINITE-MEASURE omega ca cm3_)
               (AND (IS-FINITE-MEASURE omega ca cm4_)
                 (FORALL cma_ (IMPLIES (IN cma_ ca)
                   (= (nu cma_) (+ (- (cm1_ cma_) (cm2_ cma_)) (* +i (- (cm3_ cma_) (cm4_ cma_))))))))))))))))))
(notation! 'IS-COMPLEX-MEASURE 'kind 'predicate 'arity 3
           'english "$3 is a complex measure on the sigma-algebra $2 of subsets of $1")

(def-predicate 'IS-COMPLEX-MEASURABLE-FN '(omega ca u)
  '(AND (IN u (FUN omega CC))
     (AND (IS-REAL-MEASURABLE-FN omega ca (VNB-LAMBDA crx_ omega (REAL-PART (u crx_))))
          (IS-REAL-MEASURABLE-FN omega ca (VNB-LAMBDA crx_ omega (IMAG-PART (u crx_)))))))
(notation! 'IS-COMPLEX-MEASURABLE-FN 'kind 'predicate 'arity 3
           'english "$3 is a measurable complex-valued function on $1 with $2")

(def-functoid 'COMPLEX-INTEGRAL '(omega ca mu u)
  '(+ (RINTEGRAL omega ca mu (VNB-LAMBDA cix_ omega (REAL-PART (u cix_))))
      (* +i (RINTEGRAL omega ca mu (VNB-LAMBDA cix_ omega (IMAG-PART (u cix_)))))))
(notation! 'COMPLEX-INTEGRAL 'kind 'functoid 'arity 4
           'english "the integral of the complex function $4 with respect to $3")

(def-predicate 'IS-COMPLEX-NULL-SET '(omega ca nu a)
  '(AND (IN a ca) (FORALL cnb_ (IMPLIES (IN cnb_ ca) (IMPLIES (SUBSET cnb_ a) (= (nu cnb_) 0))))))
(notation! 'IS-COMPLEX-NULL-SET 'kind 'predicate 'arity 4
           'english "$4 is a null set of the complex measure $3")
