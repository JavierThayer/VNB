;;; ccr4x-vocab.scm -- wave of 2026-11-09/10 (agent CCR-1109-C), wired 2026-11-10 from scratchpad/ccr1109c/ccr4x-vocab.scm.
;;; Library: analysis.

;;; ccr4x-vocab.scm -- CCR.pdf chapter 4 (extension of valuations): integer powers of a nonzero element of a normed
;;; field.  DEFINITIONS ONLY; the laws are in theorem-library/ccr4x-zpow.scm.  Agent CCR-1109-C, 2026-11-09.
;;; Destination: structure-library/ccr4x-vocab.scm.  Library: analysis (beside ccr2-vocab).  Load window: after
;;; structure-library/normed-field (the ring view NORMED-FIELD-AS-COMMUTATIVE-RING) and ring-power.
;;;
;;;   NV-ZPOW(K, w, k)   w^k for k in ZZ: the y in K with y w^b = w^a, a = max(k, 0), b = max(-k, 0).
;;;                      Unique when w /= 0 (w^b /= 0, cancellation); w^k is the ring power when k >= 0 and the
;;;                      inverse of w^(-k) when k < 0 (nv-zpow-nat, nv-zpow-neg).  The same cancellation definition
;;;                      as QP-PPOW (qp-vocab), for an arbitrary normed field.
;;; Binders zp*_.
(def-functoid 'NV-ZPOW '(zpk_ zpw_ zpn_)
  '(IOTA zpy_ (AND (IN zpy_ (CARR zpk_))
                   (= ((MUL zpk_) zpy_ (RING-POWER (NORMED-FIELD-AS-COMMUTATIVE-RING zpk_) zpw_ (MAX (- zpn_) 0)))
                      (RING-POWER (NORMED-FIELD-AS-COMMUTATIVE-RING zpk_) zpw_ (MAX zpn_ 0))))))
(notation! 'NV-ZPOW 'kind 'functoid 'arity 3 'english "the power $2^$3 in $1 ($3 an integer)")

;;;   IS-NV-REP-SET(K, A, R)  (CCR.pdf section 4.4) R is a representative set for A / M(A): R lies in A, contains
;;;                      0 and 1, every x in A is within distance < 1 of some element of R, and two elements of R at
;;;                      distance < 1 are equal (the alpha_j of the notes are representatives of distinct classes).
;;;                      That the nonzero elements are units of absolute value 1 is a consequence (nv-rep-set-norm-one).
;;; Binders rp*_.
(def-predicate 'IS-NV-REP-SET '(rpk_ rpa_ rpr_)
  '(AND (FORALL rpx_ (IMPLIES (IN rpx_ rpr_) (IN rpx_ rpa_)))
   (AND (IN (ZERO rpk_) rpr_)
   (AND (IN (ONE rpk_) rpr_)
   (AND (FORALL rpx_ (IMPLIES (IN rpx_ rpa_)
          (FORSOME rpy_ (AND (IN rpy_ rpr_) (< ((FNRM rpk_) ((ADD rpk_) rpx_ ((NEG rpk_) rpy_))) 1)))))
        (FORALL rpx_ (IMPLIES (IN rpx_ rpr_) (FORALL rpy_ (IMPLIES (IN rpy_ rpr_)
          (IMPLIES (< ((FNRM rpk_) ((ADD rpk_) rpx_ ((NEG rpk_) rpy_))) 1) (= rpx_ rpy_)))))))))))
(notation! 'IS-NV-REP-SET 'kind 'predicate 'arity 3 'english "$3 is a representative set for $2 modulo its maximal ideal in $1")

;;;   NV-DIGIT(K, R, z)       the element of R within distance < 1 of z (the alpha_j of section 4.4; unique for
;;;                      z in Z(K) when R is a representative set: nv-digit-def).
;;;   NV-TERM(K, w, a, n)     the terms j |-> a(n + j) w^(n + j), j in NN, of the series (36) with digits a : ZZ -> K.
;;;   NV-PSUM(K, w, a, n, m)  the m-th partial sum  sum_{j < m} a(n + j) w^(n + j).
;;;   IS-NV-EXPANSION(K, w, R, a, n, x)  x = sum_{k >= n} a_k w^k (CCR.pdf (36)): the digits a : ZZ -> R vanish
;;;                      below n and the partial sums converge to x in the metric space of K.
;;; Binders dg*_, nt*_, ne*_.
(def-functoid 'NV-DIGIT '(dgk_ dgr_ dgz_)
  '(IOTA dgy_ (AND (IN dgy_ dgr_) (< ((FNRM dgk_) ((ADD dgk_) dgz_ ((NEG dgk_) dgy_))) 1))))
(notation! 'NV-DIGIT 'kind 'functoid 'arity 3 'english "the representative in $2 of $3")
(def-functoid 'NV-TERM '(ntk_ ntw_ nta_ ntn_)
  '(VNB-LAMBDA ntj_ NN ((MUL ntk_) (nta_ (+ ntn_ ntj_)) (NV-ZPOW ntk_ ntw_ (+ ntn_ ntj_)))))
(notation! 'NV-TERM 'kind 'functoid 'arity 4 'english "the terms a($4 + j) $2^($4 + j) of the series with digits $3")
(def-functoid 'NV-PSUM '(ntk_ ntw_ nta_ ntn_ ntm_)
  '(SUM-AG (NORMED-FIELD-ADDITIVE-AG ntk_) (NV-TERM ntk_ ntw_ nta_ ntn_) ntm_))
(notation! 'NV-PSUM 'kind 'functoid 'arity 5 'english "the $5-th partial sum of the series with digits $3 from $4")
(def-predicate 'IS-NV-EXPANSION '(nek_ new_ ner_ nea_ nen_ nex_)
  '(AND (IN nea_ (FUN ZZ ner_))
   (AND (FORALL nei_ (IMPLIES (IN nei_ ZZ) (IMPLIES (< nei_ nen_) (= (nea_ nei_) (ZERO nek_)))))
        (CONVERGES-TO (NF-METRIC-SPACE nek_) (VNB-LAMBDA nem_ NN (NV-PSUM nek_ new_ nea_ nen_ nem_)) nex_))))
(notation! 'IS-NV-EXPANSION 'kind 'predicate 'arity 6 'english "$6 = sum over k >= $5 of $4(k) $2^k with digits in $3")
