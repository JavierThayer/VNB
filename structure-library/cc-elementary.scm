;;; cc-elementary.scm -- THE ELEMENTARY FUNCTIONS exp, cos, sin ON CC, DEFINED BY
;;; THEIR POWER SERIES (the notes 2.3.1, 2.3.2).
;;; DEFINITIONS ONLY; the laws are PROVEN in theorem-library/cc-exp.scm.
;;; Batch 31-A, 2026-09-25.  The user's decision of 2026-09-25: CC-EXP, CC-COS and
;;; CC-SIN are DEFINED BY THEIR POWER SERIES (pi is not defined here: 31-B).
;;;
;;; THE SOURCE.  ~/docs/complex-analysis.pdf, section 2.3 (pp. 30-33):
;;;   2.3.1: "The exponential map is exp z = sum_{k=0}^inf z^k / k!."
;;;   2.3.2, (34): "cos z = sum_{k=0}^inf (-1)^k z^(2k) / (2k)!,
;;;                 sin z = sum_{k=0}^inf (-1)^k z^(2k+1) / (2k+1)!."
;;;
;;; THE SHAPE.  Each is CC-SERIES-LIMIT (structure-library/cc-power-series.scm,
;;; the sum of a convergent complex series) of the series of its terms, written
;;; coefficient first, `c_k * z^m', the shape of the power series of 2.7-2.10
;;; (cf(k) * z^k), so that the theorems of cc-power-series-laws.scm,
;;; cc-power-series-deriv.scm and cps-taylor-coefficients.scm apply to exp with
;;; ONE instantiation, cf(k) = recip(factorial(k)).  cos and sin are the notes'
;;; series (34) literally, indexed by k: the term of cos is
;;; (-1)^k recip((2k)!) z^(2k), that of sin (-1)^k recip((2k+1)!) z^(2k+1).  They
;;; are power series in w = z^2 (coefficients (-1)^k / (2k)! and (-1)^k /
;;; (2k+1)!, the latter times z); the notes' identity (34) exp(iz) = cos z +
;;; i sin z is the split of the exponential series into its even- and
;;; odd-indexed terms.  2k is (* 2 k) and 2k+1 is succ(2k), the library's NN
;;; spelling of k+1 (factorial-succ, the derived series of 2.10); -1 is the
;;; numeral of cc-i-squared (i * i = -1).
;;;
;;; The value is the sum only where the series converges (CC-SERIES-LIMIT is a
;;; description); it converges at every complex z (cc-exp.scm: the radius of
;;; each series is infinite, the notes' Lemma 2.16), so the three are total on CC.
;;;
;;; REJECTED ALTERNATIVES.  (a) cos and sin through exp, cos z = (exp(iz) +
;;; exp(-iz))/2: the notes DEFINE them by (34) and derive (35); the user decided
;;; the power series.  (b) cos and sin as power series in z with lacunary
;;; coefficients (0 at odd, resp. even, k): not the notes' (34), and every
;;; coefficient would be an IF on the parity of k.  (c) A coefficient constant
;;; EXP-COEF for 1/k!: a fourth definition; the coefficient is the term
;;; VNB-LAMBDA(k, NN, recip(factorial(k))), or a cf given by its values.
;;;
;;; Binders: cek_ (no other body binds it).  The parameter is z.
;;; Dependencies: cc-power-series.scm (CC-SERIES-LIMIT), injection.scm (FACTORIAL),
;;; number-systems.scm (power, recip on CC).

(def-functoid 'CC-EXP '(z)
  '(CC-SERIES-LIMIT (VNB-LAMBDA cek_ NN (* (recip (FACTORIAL cek_)) (power z cek_)))))

(notation! 'CC-EXP 'kind 'functoid 'arity 1
           'english "exp $1"
           'noun "exponential of $1"
           'tex "\\exp $1")

(def-functoid 'CC-COS '(z)
  '(CC-SERIES-LIMIT
     (VNB-LAMBDA cek_ NN (* (* (power -1 cek_) (recip (FACTORIAL (* 2 cek_))))
                            (power z (* 2 cek_))))))

(notation! 'CC-COS 'kind 'functoid 'arity 1
           'english "cos $1"
           'noun "cosine of $1"
           'tex "\\cos $1")

(def-functoid 'CC-SIN '(z)
  '(CC-SERIES-LIMIT
     (VNB-LAMBDA cek_ NN (* (* (power -1 cek_) (recip (FACTORIAL (succ (* 2 cek_)))))
                            (power z (succ (* 2 cek_)))))))

(notation! 'CC-SIN 'kind 'functoid 'arity 1
           'english "sin $1"
           'noun "sine of $1"
           'tex "\\sin $1")
