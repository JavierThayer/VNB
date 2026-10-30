;;; mh-vocab.scm -- vocabulary for construction-of-measures.pdf ch. 4, sections 2.4 and 4:
;;; method II and Hausdorff measures.  DEFINITIONS ONLY (destination: structure-library/).
;;; Agent RA-BASICS (M-H), 2026-10-26.  NEW DEFINITIONS, the user's to confirm.
;;;
;;;   DIAM(m, A)                   the diameter sup{ d(x, y) : x, y in A } in [0, +inf]
;;;                                (ESUP; DIAM(m, empty) = 0)
;;;   METHOD-II-DELTA(m, C, p, d)  mu*_delta: method I (METHOD-I-OUTER) on C_delta =
;;;                                { A in C : DIAM(m, A) <= delta } with p restricted to C_delta
;;;   METHOD-II(m, C, p)           mu*_0 = lim_(delta -> 0) mu*_delta, written as the ESUP over
;;;                                delta > 0 (the family is nonincreasing in delta, notes (87))
;;;   HAUSDORFF-PM(m, lam)         A |-> DIAM(A)^lam  (EPOW)
;;;   HAUSDORFF(m, lam)            H^lam = METHOD-II(m, POWER(PTS m), HAUSDORFF-PM(m, lam))
;;;   PHI-PM(m, phi)               A |-> phi(DIAM(A)), +inf when DIAM(A) = +inf
;;;   HAUSDORFF-PHI(m, phi)        H^phi = METHOD-II(m, POWER(PTS m), PHI-PM(m, phi))
;;;   NNREAL                       [0, +inf) as a set of reals
;;;   IS-DOUBLING(phi)             phi : [0, oo) -> [0, oo) nondecreasing, phi(0) = 0, and
;;;                                phi(2r) <= alpha phi(r) for some alpha > 0 and all r > 0
;;;   IS-HAUSDORFF-DIM(m, E, lam)  lam >= 0, H^rho(E) = 0 for rho > lam, H^rho(E) = +inf for
;;;                                0 < rho < lam  (rho = 0, the counting measure, is not included)
;;;
;;; BINDERS: mhw_ mhx_ mhy_ mha_ mhe_ mhv_ mhd_ mhh_ mhr_ mhq_ mhp_ mhz_; none folds onto a class
;;; name, an accessor or a registered constant.  Library: measure.

(def-functoid 'DIAM '(mhm_ mhs_)
  '(ESUP (SEP mhw_ RR-POS-STAR (FORSOME mhx_ (AND (IN mhx_ mhs_) (FORSOME mhy_ (AND (IN mhy_ mhs_)
          (= mhw_ ((DIST mhm_) mhx_ mhy_)))))))))
(notation! 'DIAM 'kind 'functoid 'arity 2 'english "the diameter of $2 in $1")

(def-functoid 'METHOD-II-DELTA '(mhm_ mhc_ mhp_ mhd_)
  '(METHOD-I-OUTER (PTS mhm_) (SEP mha_ mhc_ (<= (DIAM mhm_ mha_) mhd_))
                   (RESTRICT mhp_ (SEP mha_ mhc_ (<= (DIAM mhm_ mha_) mhd_)))))
(notation! 'METHOD-II-DELTA 'kind 'functoid 'arity 4
           'english "the method-II outer measure at scale $4 of the pre-measure $3 on $2 (in $1)")

;;; NBGSEP (2026-10-28): the scale mhd_ is bounded explicitly by mhd_ in RR, so the
;;; separation is predicative (NBG).  POS-RR(mhd_) already gives it: the meaning is unchanged.
(def-functoid 'METHOD-II '(mhm_ mhc_ mhp_)
  '(VNB-LAMBDA mhe_ (POWER (PTS mhm_))
     (ESUP (SEP mhv_ RR-POS-STAR (FORSOME mhd_ (AND (IN mhd_ RR) (AND (POS-RR mhd_)
             (= mhv_ ((METHOD-II-DELTA mhm_ mhc_ mhp_ mhd_) mhe_)))))))))
(notation! 'METHOD-II 'kind 'functoid 'arity 3
           'english "the method-II outer measure of the pre-measure $3 on $2 (in $1)")

(def-functoid 'HAUSDORFF-PM '(mhm_ mhl_)
  '(VNB-LAMBDA mhh_ (POWER (PTS mhm_)) (EPOW (DIAM mhm_ mhh_) mhl_)))
(notation! 'HAUSDORFF-PM 'kind 'functoid 'arity 2 'english "A |-> diam(A)^$2 (in $1)")

(def-functoid 'HAUSDORFF '(mhm_ mhl_)
  '(METHOD-II mhm_ (POWER (PTS mhm_)) (HAUSDORFF-PM mhm_ mhl_)))
(notation! 'HAUSDORFF 'kind 'functoid 'arity 2 'english "the Hausdorff outer measure of dimension $2 on $1")

(def-functoid 'PHI-PM '(mhm_ mhf_)
  '(VNB-LAMBDA mhh_ (POWER (PTS mhm_))
     (IF (= (DIAM mhm_ mhh_) POS-INF) POS-INF (mhf_ (DIAM mhm_ mhh_)))))
(notation! 'PHI-PM 'kind 'functoid 'arity 2 'english "A |-> $2(diam(A)) (in $1)")

(def-functoid 'HAUSDORFF-PHI '(mhm_ mhf_)
  '(METHOD-II mhm_ (POWER (PTS mhm_)) (PHI-PM mhm_ mhf_)))
(notation! 'HAUSDORFF-PHI 'kind 'functoid 'arity 2 'english "the generalized Hausdorff outer measure H^$2 on $1")

(def-constant 'NNREAL (list 'nnreal-def '(== NNREAL (SEP mhr_ RR (<= 0 mhr_)))))
(notation! 'NNREAL 'kind 'constant 'arity 0 'english "[0, +oo)")

(def-predicate 'IS-DOUBLING '(mhf_)
  '(AND (IN mhf_ (FUN NNREAL NNREAL))
   (AND (= (mhf_ 0) 0)
   (AND (FORALL mhr_ (IMPLIES (IN mhr_ NNREAL) (FORALL mhq_ (IMPLIES (IN mhq_ NNREAL)
          (IMPLIES (<= mhr_ mhq_) (<= (mhf_ mhr_) (mhf_ mhq_)))))))
        (FORSOME mhp_ (AND (POS-RR mhp_)
          (FORALL mhr_ (IMPLIES (IN mhr_ RR) (IMPLIES (< 0 mhr_)
            (<= (mhf_ (* 2 mhr_)) (* mhp_ (mhf_ mhr_))))))))))))
(notation! 'IS-DOUBLING 'kind 'predicate 'arity 1 'english "$1 is a doubling function")

(def-predicate 'IS-HAUSDORFF-DIM '(mhm_ mhs_ mhl_)
  '(AND (IN mhl_ RR) (AND (<= 0 mhl_)
   (AND (FORALL mhr_ (IMPLIES (IN mhr_ RR) (IMPLIES (< mhl_ mhr_) (= ((HAUSDORFF mhm_ mhr_) mhs_) 0))))
        (FORALL mhr_ (IMPLIES (IN mhr_ RR) (IMPLIES (< 0 mhr_) (IMPLIES (< mhr_ mhl_)
          (= ((HAUSDORFF mhm_ mhr_) mhs_) POS-INF)))))))))
(notation! 'IS-HAUSDORFF-DIM 'kind 'predicate 'arity 3 'english "$2 has Hausdorff dimension $3 in $1")
