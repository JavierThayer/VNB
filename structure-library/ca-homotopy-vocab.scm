;;; ch3c-vocab.scm -- vocabulary for the general Cauchy theorem (complex-analysis.pdf 3.3).
;;; Destination: structure-library/ca-homotopy-vocab.scm.  Library: complex-analysis.
;;; Binders: hm*_ (hma_ hmb_ hmd_ hmf_ hmk_ hmn_ hms_ hmt_ hmw_ hmx_ hmz_), used by nothing else.
;;;
;;;   GOOD-APPROX(u, pgam, prho, a, b)   Def 3.10: prho is a good approximation to pgam in u
;;;   HOMOTOPIC(u, pgam, prho, a, b)     Def 3.14: homotopic in u with endpoints fixed
;;;   NULL-HOMOTOPIC(u, pgam, a, b)      Def 3.19
;;;   SIMPLY-CONNECTED(u)                Def 3.19
;;;
;;; Def 3.10 indexes B_0..B_n but uses B_0..B_{n-1}: the latter is what is stated.  The curves of
;;; Defs 3.10 / 3.14 are continuous curves (IS-PATH) INTO u (trace in u).  The homotopy domain
;;; [0, 1] x [a, b] is PRODUCT2-MS(SUBSPACE-MS(RR-MS, [0, 1]), SUBSPACE-MS(RR-MS, [a, b])) (the max
;;; metric), whose points are CARTESIAN(CCINT(0, 1), CCINT(a, b)).

(def-predicate 'GOOD-APPROX '(hmu_ hmg_ hmr_ hma_ hmb_)
  '(AND (IS-PATH hmg_ hma_ hmb_)
   (AND (IS-PATH hmr_ hma_ hmb_)
   (AND (SUBSET (TRACE hmg_ hma_ hmb_) hmu_)
   (AND (SUBSET (TRACE hmr_ hma_ hmb_) hmu_)
   (AND (= (hmr_ hma_) (hmg_ hma_))
   (AND (= (hmr_ hmb_) (hmg_ hmb_))
        (FORSOME hmn_ (AND (IN hmn_ NN) (AND (<= 1 hmn_)
          (FORSOME hmt_ (AND (IN hmt_ (FUN NN RR)) (AND (= (hmt_ 0) hma_) (AND (= (hmt_ hmn_) hmb_)
            (FORSOME hmd_ (AND (IN hmd_ (FUN NN (POWER CC)))
              (FORALL hmk_ (IMPLIES (IN hmk_ NN) (IMPLIES (< hmk_ hmn_)
                (AND (< (hmt_ hmk_) (hmt_ (succ hmk_)))
                (AND (IS-OPEN (NF-METRIC-SPACE CC-NORMED-FIELD) (hmd_ hmk_))
                (AND (IS-CONVEX-CC (hmd_ hmk_))
                (AND (SUBSET (hmd_ hmk_) hmu_)
                     (FORALL hmw_ (IMPLIES (IN hmw_ (CCINT (hmt_ hmk_) (hmt_ (succ hmk_))))
                       (AND (IN (hmg_ hmw_) (hmd_ hmk_)) (IN (hmr_ hmw_) (hmd_ hmk_))))))))))))))))))))))))))))
(notation! 'GOOD-APPROX 'kind 'predicate 'arity 5 'english "$3 is a good approximation to $2 in $1")

(def-predicate 'HOMOTOPIC '(hmu_ hmg_ hmr_ hma_ hmb_)
  '(AND (IS-PATH hmg_ hma_ hmb_)
   (AND (IS-PATH hmr_ hma_ hmb_)
   (AND (= (hmr_ hma_) (hmg_ hma_))
   (AND (= (hmr_ hmb_) (hmg_ hmb_))
        (FORSOME hmf_ (AND (IN hmf_ (FUN (CARTESIAN (CCINT 0 1) (CCINT hma_ hmb_)) hmu_))
          (AND (FORALL hmz_ (IMPLIES (IN hmz_ (CARTESIAN (CCINT 0 1) (CCINT hma_ hmb_)))
                 (IS-CONTINUOUS-AT (PRODUCT2-MS (SUBSPACE-MS RR-MS (CCINT 0 1)) (SUBSPACE-MS RR-MS (CCINT hma_ hmb_)))
                                   CC-MS hmf_ hmz_)))
          (AND (FORALL hmt_ (IMPLIES (IN hmt_ (CCINT hma_ hmb_))
                 (AND (= (hmf_ (LIST 0 hmt_)) (hmg_ hmt_)) (= (hmf_ (LIST 1 hmt_)) (hmr_ hmt_)))))
               (FORALL hms_ (IMPLIES (IN hms_ (CCINT 0 1))
                 (AND (= (hmf_ (LIST hms_ hma_)) (hmg_ hma_)) (= (hmf_ (LIST hms_ hmb_)) (hmg_ hmb_))))))))))))))
(notation! 'HOMOTOPIC 'kind 'predicate 'arity 5 'english "$2 and $3 are homotopic in $1 with endpoints fixed")

(def-predicate 'NULL-HOMOTOPIC '(hmu_ hmg_ hma_ hmb_)
  '(AND (= (hmg_ hmb_) (hmg_ hma_))
        (HOMOTOPIC hmu_ hmg_ (VNB-LAMBDA hmx_ (CCINT hma_ hmb_) (hmg_ hma_)) hma_ hmb_)))
(notation! 'NULL-HOMOTOPIC 'kind 'predicate 'arity 4 'english "the closed curve $2 is null homotopic in $1")

(def-predicate 'SIMPLY-CONNECTED '(hmu_)
  '(AND (IS-OPEN (NF-METRIC-SPACE CC-NORMED-FIELD) hmu_)
   (AND (IS-CONNECTED CC-MS hmu_)
        (FORALL hma_ (FORALL hmb_ (FORALL hmg_
          (IMPLIES (IS-PATH hmg_ hma_ hmb_) (IMPLIES (SUBSET (TRACE hmg_ hma_ hmb_) hmu_)
            (IMPLIES (= (hmg_ hmb_) (hmg_ hma_)) (NULL-HOMOTOPIC hmu_ hmg_ hma_ hmb_))))))))))
(notation! 'SIMPLY-CONNECTED 'kind 'predicate 'arity 1 'english "$1 is simply connected")

;;; ---------------------------------------------------------------------------
;;; POLYGONAL ROADS on a given partition (Example 3.11, Prop 3.17).  The polygon lives on the curve's
;;; own interval with its corners at the partition points, since Def 3.10 compares at the same
;;; parameter.  AFF-SEG(p, q, c, d) is the affine segment from p to q on [c, d]; POLY-ROAD(t, x, m) is
;;; the polygon through x(0), ..., x(m+1) at t(0) < ... < t(m+1) (m + 1 pieces), built by JUXTA.
(def-functoid 'AFF-SEG '(hmp_ hmq_ hmc_ hmd_)
  '(VNB-LAMBDA hmz_ (CCINT hmc_ hmd_) (+ hmp_ (* (* (- hmz_ hmc_) (recip (- hmd_ hmc_))) (- hmq_ hmp_)))))
(notation! 'AFF-SEG 'kind 'functoid 'arity 4 'english "the affine segment from $1 to $2 on [$3, $4]")
(def-functoid 'AFF-DER '(hmp_ hmq_ hmc_ hmd_)
  '(VNB-LAMBDA hmz_ (CCINT hmc_ hmd_) (* (recip (- hmd_ hmc_)) (- hmq_ hmp_))))
(notation! 'AFF-DER 'kind 'functoid 'arity 4 'english "the derivative of the affine segment from $1 to $2 on [$3, $4]")
(def-by-nn-recursion 'POLY-ROAD '(hmt_ hmx_)
  '(AFF-SEG (hmx_ 0) (hmx_ (succ 0)) (hmt_ 0) (hmt_ (succ 0)))
  '(hmm_ hmv_)
  '(JUXTA hmv_ (AFF-SEG (hmx_ (succ hmm_)) (hmx_ (succ (succ hmm_))) (hmt_ (succ hmm_)) (hmt_ (succ (succ hmm_))))
          (hmt_ 0) (hmt_ (succ hmm_)) (hmt_ (succ (succ hmm_)))))
(notation! 'POLY-ROAD 'kind 'functoid 'arity 3 'english "the polygon through the points $2 at the nodes $1, with $3 + 1 pieces")
(def-by-nn-recursion 'POLY-DER '(hmt_ hmx_)
  '(AFF-DER (hmx_ 0) (hmx_ (succ 0)) (hmt_ 0) (hmt_ (succ 0)))
  '(hmm_ hmv_)
  '(JUXTA hmv_ (AFF-DER (hmx_ (succ hmm_)) (hmx_ (succ (succ hmm_))) (hmt_ (succ hmm_)) (hmt_ (succ (succ hmm_))))
          (hmt_ 0) (hmt_ (succ hmm_)) (hmt_ (succ (succ hmm_)))))
(notation! 'POLY-DER 'kind 'functoid 'arity 3 'english "the derivative of the polygon through $2 at the nodes $1")
