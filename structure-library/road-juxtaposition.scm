;;; road-juxtaposition.scm -- THE JUXTAPOSITION OF ROADS, THE TRIANGULAR ROAD AND THE LENGTH
;;; OF A ROAD.  DEFINITIONS ONLY; every law is PROVEN in
;;; theorem-library/road-juxtaposition-laws.scm.  Batch 37, 2026-09-26.
;;;
;;; THE SOURCES.  Dieudonne, Foundations of Modern Analysis, 9.6: "if gamma_1 is a path
;;; defined in [a, b] and gamma_2 a path defined in [b, c] such that gamma_1(b) = gamma_2(b),
;;; the map gamma equal to gamma_1 in [a, b] and to gamma_2 in [b, c] is a path, the
;;; juxtaposition of gamma_1 and gamma_2."  complex-analysis.pdf 3.1, Proposition 3.1 (the
;;; concatenation gamma || rho, "defined when the endpoint of gamma is the initial point of
;;; rho") and the estimate (53), which bounds an integral along a path by the LENGTH of the
;;; path times a bound of |f| on its trace.
;;;
;;;     JUXTA(p, q, a, b, c)      the function on [a, c] equal to p on [a, b] and to q on
;;;                               (b, c]: Dieudonne's juxtaposition, the parameter intervals
;;;                               ADJACENT, no reparametrisation
;;;     ROAD-LENGTH(dgam, a, b)   the integral over [a, b] of t |-> |dgam(t)|
;;;     TRI-ROAD(a, b, c)         the triangular road on [0, 3]: the segment <a, b> on
;;;     TRI-ROAD-DERIV(a, b, c)   [0, 1], <b, c> shifted to [1, 2], <c, a> shifted to [2, 3]
;;;
;;; STATEMENT CHECKS.
;;; (1) JUXTA is an IF term under a VNB-LAMBDA over [a, c]: at t <= b it is p(t), otherwise
;;;     q(t).  At t = b it therefore takes p's value.  For a PATH this is harmless when the
;;;     endpoint condition p(b) = q(b) holds, and every law that needs the right-hand
;;;     values on the CLOSED interval [b, c] carries that condition.  For a DERIVATIVE the
;;;     two values at b may differ, and nothing reads them: IS-PRIMITIVE reads its integrand
;;;     on the open interval only (`primitive-integrand-interior-congruence'), and
;;;     IS-REGULATED-ON reads a right limit at b from t > b and a left limit from t < b.
;;;     The juxtaposed derivative is written with the SAME constructor.
;;; (2) The inactive branch of the IF need not denote: q(t) for t < a is outside q's domain.
;;;     The IF is resolved by `if-true' / `if-false' on a proven condition, so the inactive
;;;     branch is never evaluated.  No law is stated about JUXTA off [a, c].
;;; (3) ROAD-LENGTH takes the DERIVATIVE only: the length of the road (pgam, dgam) depends
;;;     on dgam alone, and every law carries is-road(pgam, dgam, a, b) as a hypothesis,
;;;     which is where pgam enters.  A four-argument form would carry an argument its value
;;;     does not read.  ROAD-LENGTH is a PW-INT, an IOTA term, and is defined where
;;;     t |-> |dgam(t)| has a primitive; for a road it does (`road-length-primitive': the
;;;     magnitude is regulated, `regulated-on-magnitude', and a regulated function has a
;;;     primitive, `regulated-on-has-primitive').
;;; (4) TRI-ROAD's shifted sides are the COMPOSITES t |-> SEG-PATH(b, c)(t - 1) and
;;;     t |-> SEG-PATH(c, a)(t - 2): the affine maps t |-> t - 1, t - 2 of the brief composed
;;;     with the segment.  The juxtaposition is left-nested: JUXTA(JUXTA(<a,b>, <b,c>', 0, 1,
;;;     2), <c,a>'', 0, 2, 3).
;;; (5) BINDERS: jxt_ (JUXTA), rlt_ (ROAD-LENGTH), trs_ (the two shifted sides, sibling
;;;     lambdas, so one name serves both and the shift lemmas match either literally).
;;;     Parameters jxp_ jxq_ jxa_ jxb_ jxc_, rld_ rla_ rlb_, tra_ trb_ trc_.  None folds onto
;;;     a class name, an accessor or a registered constant, and no predicate body or driver
;;;     in the cone binds one.
;;;
;;; Dependencies: path-integral.scm (PW-INT), segments-triangles.scm (SEG-PATH, SEG-DERIV),
;;; extreme-value.scm (CCINT), number systems (magnitude).  Load slot: after
;;; structure-library/segments-triangles.

(def-functoid 'JUXTA '(jxp_ jxq_ jxa_ jxb_ jxc_)
  '(VNB-LAMBDA jxt_ (CCINT jxa_ jxc_) (IF (<= jxt_ jxb_) (jxp_ jxt_) (jxq_ jxt_))))

(notation! 'JUXTA 'kind 'functoid 'arity 5
           'english "the juxtaposition of $1 on [$3, $4] and $2 on [$4, $5]")

(def-functoid 'ROAD-LENGTH '(rld_ rla_ rlb_)
  '(PW-INT (VNB-LAMBDA rlt_ (CCINT rla_ rlb_) (magnitude (rld_ rlt_))) rla_ rlb_))

(notation! 'ROAD-LENGTH 'kind 'functoid 'arity 3
           'english "the length of the road with derivative $1 on [$2, $3]")

(def-functoid 'TRI-ROAD '(tra_ trb_ trc_)
  '(JUXTA (JUXTA (SEG-PATH tra_ trb_)
                 (VNB-LAMBDA trs_ (CCINT 1 2) ((SEG-PATH trb_ trc_) (- trs_ 1)))
                 0 1 2)
          (VNB-LAMBDA trs_ (CCINT 2 3) ((SEG-PATH trc_ tra_) (- trs_ 2)))
          0 2 3))

(notation! 'TRI-ROAD 'kind 'functoid 'arity 3
           'english "the triangular road through $1, $2, $3")

(def-functoid 'TRI-ROAD-DERIV '(tra_ trb_ trc_)
  '(JUXTA (JUXTA (SEG-DERIV tra_ trb_)
                 (VNB-LAMBDA trs_ (CCINT 1 2) ((SEG-DERIV trb_ trc_) (- trs_ 1)))
                 0 1 2)
          (VNB-LAMBDA trs_ (CCINT 2 3) ((SEG-DERIV trc_ tra_) (- trs_ 2)))
          0 2 3))

(notation! 'TRI-ROAD-DERIV 'kind 'functoid 'arity 3
           'english "the derivative of the triangular road through $1, $2, $3")
