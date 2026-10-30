;;; tb6-vocab.scm -- THE WEAK* TOPOLOGY AND POLARS (definitions only), for topological-vector-space.pdf
;;; Cor 3.27 (Banach-Alaoglu) and Prop 3.29.  Agent TB-6 (worker-08), 2026-10-26 (NEW DEFINITIONS, the user's to
;;; confirm).  DESTINATION: structure-library/weak-star.scm.  Library: analysis.
;;; Load window: after tb-vocab (IS-TVS, SEMINORM-TOP), linear-functional, top-product (TPRODUCT-TOP).
;;;
;;;   TOP-DUAL(m, t)          E*, the continuous linear functionals of the real TVS (m, t): f : VEC m -> RR linear and
;;;                           continuous into the real line with the topology of |.| (the SEMINORM-TOP of RR-NVS used
;;;                           by tvs-kernel-closed and tvs-geometric-hb).
;;;   POLAR(m, t, a)          Def 3.10 for the dual system <E, E*>: { f in E* : f(x) <= 1 for every x in a }.
;;;   WEAK-STAR-TOP(m, t)     the w<E*, E> topology of Def 3.3 on E*: by Remark 3.16 the topology induced on E* from the
;;;                           product R^E (pointwise convergence), i.e. the subspace topology of TPRODUCT-TOP over the
;;;                           index set VEC m with every factor the metric line.
;;; Binders: tdf_, plf_, plx_, and b6n_ (shared on purpose with tb6.scm, whose product of lines uses the same binder,
;;; so that the unfolded topology is literally the product that file proves things about).

(def-functoid 'TOP-DUAL '(m t)
  '(SEP tdf_ (FUN (VEC m) RR)
     (AND (IS-LINEAR-FUNCTIONAL m tdf_)
          (IS-HOM-TOP-SPACE t (SEMINORM-TOP (NORMED-VECTOR-SPACE-AS-MODULE RR-NVS) (PAIR 0 0)
                                            (VNB-LAMBDA nvk_ (PAIR 0 0) (VNRM RR-NVS)))
                            tdf_))))
(def-functoid 'POLAR '(m t a)
  '(SEP plf_ (TOP-DUAL m t) (FORALL plx_ (IMPLIES (IN plx_ a) (<= (plf_ plx_) 1)))))
(def-functoid 'WEAK-STAR-TOP '(m t)
  '(SUBSPACE-TOP (TPRODUCT-TOP (VEC m) (VNB-LAMBDA b6n_ (VEC m) (METRIC-TOP RR-MS))) (TOP-DUAL m t)))

(notation! 'TOP-DUAL 'kind 'functoid 'arity 2
           'english "the topological dual of the topological vector space $1 with topology $2")
(notation! 'POLAR 'kind 'functoid 'arity 3
           'english "the polar of $3 in the topological dual of $1 with topology $2")
(notation! 'WEAK-STAR-TOP 'kind 'functoid 'arity 2
           'english "the weak* topology on the topological dual of $1 with topology $2")

;;;   DUAL-WEAK-STAR-TOP(m)   for a normed space m: the w<E*, E> topology on E* = DUAL-VEC(m) (the bounded linear
;;;                           functionals), induced from the product R^E as above.
;;;   DUAL-UNIT-BALL(m)       the unit ball { f in E* : ||f|| <= 1 } of the dual, ||f|| = DUAL-NORM(m, f).
(def-functoid 'DUAL-WEAK-STAR-TOP '(m)
  '(SUBSPACE-TOP (TPRODUCT-TOP (VEC m) (VNB-LAMBDA b6n_ (VEC m) (METRIC-TOP RR-MS))) (DUAL-VEC m)))
(def-functoid 'DUAL-UNIT-BALL '(m)
  '(SEP dbf_ (DUAL-VEC m) (<= (DUAL-NORM m dbf_) 1)))
(notation! 'DUAL-WEAK-STAR-TOP 'kind 'functoid 'arity 1
           'english "the weak* topology on the dual of the normed space $1")
(notation! 'DUAL-UNIT-BALL 'kind 'functoid 'arity 1
           'english "the closed unit ball of the dual of the normed space $1")
