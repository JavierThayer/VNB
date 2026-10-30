;;; qp-vocab.scm -- WAVE 2 (2026-10-27..30), wired 2026-10-30 from scratchpad/ccrqp/qp-vocab.scm.
;;; Library: complex-analysis.

;;; qp-vocab.scm -- Q_p, THE COMPLETION OF Q UNDER |.|_p, AS A NON-ARCHIMEDEAN VALUED FIELD (CCR.pdf Definition 1.26).
;;; DEFINITIONS ONLY; the laws are in theorem-library/qp-laws.scm.  Agent CCR-QP, 2026-10-27.  Destination:
;;; structure-library/qp-vocab.scm.  Library: complex-analysis (as padic-vocab: |.|_p is built on cc-exp
;;; neighbours -- see WIRE-PLAN-1027 0.3).  Load window: after padic-vocab, metric-completion, ringoid.
;;;
;;; The metric space of Q is QP-MS(p) = NF-METRIC-SPACE(QQ-PADIC(p)); Q_p is its COMPLETION (Def 1.26), whose
;;; points are classes of Cauchy sequences.  The field operations come from the RING of Cauchy sequences
;;; with pointwise operations and its IDEAL of null sequences: a RINGOID, whose quotient ring the tree
;;; already proves to be a ring (ringoid-quotient-is-ring).  The quotient setoid is the completion's
;;; CAUCHY-SETOID (proved equal), so the field and the completion have the same points.  The absolute value
;;; is the completion distance to 0.
;;;
;;;   QP-MS(p)          Q with the metric of |.|_p
;;;   QP(p)             Q_p as a metric space: COMPLETION(QP-MS(p))                         (Definition 1.26)
;;;   QP-CS(p)          the Cauchy sequences of QP-MS(p)
;;;   QP-SADD/SMUL/SNEG(p)  pointwise operations on Cauchy sequences
;;;   QP-NULL(p)        the null sequences (null distance to the zero sequence)
;;;   QP-CSR(p)         the ringoid [QP-CS, +, *, -, 0, 1, QP-NULL]
;;;   QP-RING(p)        the quotient ring QP-CS / QP-NULL
;;;   QP-ABS(p)         |x| = d(x, 0) in the completion
;;;   QP-FIELD(p)       [QP-RING's six slots, QP-ABS]: the NV field Q_p
;;;   ZP(p)             Z_p = Z(Q_p), the p-adic integers                                   (Definition 1.26)
;;; Binders qs*_.

(def-functoid 'QP-MS '(qsp_) '(NF-METRIC-SPACE (QQ-PADIC qsp_)))
(notation! 'QP-MS 'kind 'functoid 'arity 1 'english "the rationals with the $1-adic metric")

(def-functoid 'QP '(qsp_) '(COMPLETION (NF-METRIC-SPACE (QQ-PADIC qsp_))))
(notation! 'QP 'kind 'functoid 'arity 1 'english "the $1-adic numbers Q_$1, as a metric space")

(def-functoid 'QP-CS '(qsp_) '(CSEQ (NF-METRIC-SPACE (QQ-PADIC qsp_))))
(notation! 'QP-CS 'kind 'functoid 'arity 1 'english "the Cauchy sequences of rationals for the $1-adic metric")

(def-functoid 'QP-SADD '(qsp_)
  '(VNB-LAMBDA (LIST qsu_ qsv_) (CARTESIAN (QP-CS qsp_) (QP-CS qsp_)) (VNB-LAMBDA qsn_ NN (+ (qsu_ qsn_) (qsv_ qsn_)))))
(def-functoid 'QP-SMUL '(qsp_)
  '(VNB-LAMBDA (LIST qsu_ qsv_) (CARTESIAN (QP-CS qsp_) (QP-CS qsp_)) (VNB-LAMBDA qsn_ NN (* (qsu_ qsn_) (qsv_ qsn_)))))
(def-functoid 'QP-SNEG '(qsp_)
  '(VNB-LAMBDA qsu_ (QP-CS qsp_) (VNB-LAMBDA qsn_ NN (- (qsu_ qsn_)))))

(def-functoid 'QP-NULL '(qsp_)
  '(SEP qsu_ (QP-CS qsp_) (CSEQ-EQUIV (NF-METRIC-SPACE (QQ-PADIC qsp_)) qsu_ (VNB-LAMBDA qsn_ NN 0))))
(notation! 'QP-NULL 'kind 'functoid 'arity 1 'english "the null sequences of rationals for the $1-adic metric")

(def-functoid 'QP-CSR '(qsp_)
  '(LIST (QP-CS qsp_) (QP-SADD qsp_) (QP-SMUL qsp_) (QP-SNEG qsp_) (VNB-LAMBDA qsn_ NN 0) (VNB-LAMBDA qsn_ NN 1)
         (QP-NULL qsp_)))
(notation! 'QP-CSR 'kind 'functoid 'arity 1 'english "the ring of $1-adic Cauchy sequences with the ideal of null sequences")

(def-functoid 'QP-RING '(qsp_) '(RINGOID-QUOTIENT-RING (QP-CSR qsp_)))

(def-functoid 'QP-ABS '(qsp_)
  '(VNB-LAMBDA qsx_ (QUOTIENT (CAUCHY-SETOID (NF-METRIC-SPACE (QQ-PADIC qsp_))))
     ((DIST (COMPLETION (NF-METRIC-SPACE (QQ-PADIC qsp_))))
      qsx_ (CLASS (CAUCHY-SETOID (NF-METRIC-SPACE (QQ-PADIC qsp_))) (VNB-LAMBDA qsn_ NN 0)))))
(notation! 'QP-ABS 'kind 'functoid 'arity 1 'english "the $1-adic absolute value on Q_$1")

(def-functoid 'QP-FIELD '(qsp_)
  '(LIST (CARR (QP-RING qsp_)) (ADD (QP-RING qsp_)) (MUL (QP-RING qsp_)) (NEG (QP-RING qsp_))
         (ZERO (QP-RING qsp_)) (ONE (QP-RING qsp_)) (QP-ABS qsp_)))
(notation! 'QP-FIELD 'kind 'functoid 'arity 1 'english "the field Q_$1 of $1-adic numbers")

(def-functoid 'ZP '(qsp_) '(NV-INTEGERS (QP-FIELD qsp_)))
(notation! 'ZP 'kind 'functoid 'arity 1 'english "the ring Z_$1 of $1-adic integers")

;; ord_p on Q_p (CCR.pdf section 1.4, equation (11)): ord_K(x) = log_r |x| = log|x| / log r, with r = 1/2 as
;; fixed in section 1.3.  recip-star is the total reciprocal of RR.
(def-functoid 'QP-ORD '(qsp_)
  '(VNB-LAMBDA qox_ (CARR (QP-FIELD qsp_))
     (* (log ((QP-ABS qsp_) qox_)) (recip-star (log (recip-star 2))))))
(notation! 'QP-ORD 'kind 'functoid 'arity 1 'english "the order function ord_$1 on Q_$1")

;; p^k in Q_p for k in ZZ: the y with y * p^b = p^a, where a = max(k, 0), b = max(-k, 0) (both in NN, a - b = k)
;; and p^a, p^b are the embedded rational powers.  Unique by cancellation (p^b /= 0).
(def-functoid 'QP-PPOW '(qsp_ qsk_)
  '(IOTA qpy_ (AND (IN qpy_ (CARR (QP-FIELD qsp_)))
                   (= ((MUL (QP-FIELD qsp_)) qpy_ ((EMBED (NF-METRIC-SPACE (QQ-PADIC qsp_))) (power qsp_ (MAX (- qsk_) 0))))
                      ((EMBED (NF-METRIC-SPACE (QQ-PADIC qsp_))) (power qsp_ (MAX qsk_ 0)))))))
(notation! 'QP-PPOW 'kind 'functoid 'arity 2 'english "the power $1^$2 in Q_$1 ($2 an integer)")

;; F_p = Z / pZ (CCR.pdf Remark 1.27, Corollary 2.24): the ringoid [ZZ-RING; ideal pZ] and its quotient ring.
(def-functoid 'FP-RINGOID '(qsp_)
  '(LIST ZZ (VNB-LAMBDA (LIST x_ y_) (CARTESIAN ZZ ZZ) (+ x_ y_)) (VNB-LAMBDA (LIST x_ y_) (CARTESIAN ZZ ZZ) (* x_ y_))
         (VNB-LAMBDA x_ ZZ (- x_)) 0 1 (SEP fpn_ ZZ (ZZ-DIVIDES qsp_ fpn_))))
(notation! 'FP-RINGOID 'kind 'functoid 'arity 1 'english "the integers with the ideal $1 Z")
(def-functoid 'FP '(qsp_) '(RINGOID-QUOTIENT-RING (FP-RINGOID qsp_)))
(notation! 'FP 'kind 'functoid 'arity 1 'english "the field F_$1 = Z / $1 Z")

;; Proposition 4.19 (the p-adic expansion).  Digits are a function a : ZZ -> ZZ with 0 <= a(k) < p, vanishing below
;; the starting exponent n; the series is sum_{k >= n} a_k p^k, read as the sequence of its partial sums
;; QP-PSUM(p, a, n, m) = sum_{j < m} a_{n+j} p^{n+j} (SUM-AG over the additive group of Q_p), convergent in Q_p.
;; QP-DIGIT(p, y) is the digit of y in Z_p: the unique d in {0, ..., p-1} with |y - d| < 1.
(def-functoid 'QP-DIGIT '(qsp_ qdy_)
  '(IOTA qdd_ (AND (IN qdd_ ZZ) (AND (<= 0 qdd_) (AND (< qdd_ qsp_)
     (< ((QP-ABS qsp_) ((ADD (QP-FIELD qsp_)) qdy_ ((NEG (QP-FIELD qsp_)) ((EMBED (NF-METRIC-SPACE (QQ-PADIC qsp_))) qdd_)))) 1))))))
(notation! 'QP-DIGIT 'kind 'functoid 'arity 2 'english "the $1-adic digit of $2")

(def-functoid 'QP-TERM '(qsp_ qta_ qtn_)
  '(VNB-LAMBDA qtj_ NN ((MUL (QP-FIELD qsp_)) ((EMBED (NF-METRIC-SPACE (QQ-PADIC qsp_))) (qta_ (+ qtn_ qtj_)))
                                              (QP-PPOW qsp_ (+ qtn_ qtj_)))))
(notation! 'QP-TERM 'kind 'functoid 'arity 3 'english "the terms a_($3 + j) $1^($3 + j) of the $1-adic series with digits $2")

(def-functoid 'QP-PSUM '(qsp_ qta_ qtn_ qtm_)
  '(SUM-AG (NORMED-FIELD-ADDITIVE-AG (QP-FIELD qsp_)) (QP-TERM qsp_ qta_ qtn_) qtm_))
(notation! 'QP-PSUM 'kind 'functoid 'arity 4 'english "the $4-th partial sum of the $1-adic series with digits $2 from $3")

(def-predicate 'IS-QP-DIGITS '(qsp_ qta_ qtn_)
  '(AND (IN qta_ (FUN ZZ ZZ))
        (FORALL qtk_ (IMPLIES (IN qtk_ ZZ)
          (AND (<= 0 (qta_ qtk_)) (AND (< (qta_ qtk_) qsp_) (IMPLIES (< qtk_ qtn_) (= (qta_ qtk_) 0))))))))
(notation! 'IS-QP-DIGITS 'kind 'predicate 'arity 3 'english "$2 is a $1-adic digit sequence starting at $3")

(def-predicate 'IS-QP-EXPANSION '(qsp_ qta_ qtn_ qtx_)
  '(AND (IS-QP-DIGITS qsp_ qta_ qtn_)
        (CONVERGES-TO (QP qsp_) (VNB-LAMBDA qtm_ NN (QP-PSUM qsp_ qta_ qtn_ qtm_)) qtx_)))
(notation! 'IS-QP-EXPANSION 'kind 'predicate 'arity 4 'english "$4 = sum over k >= $3 of $2(k) $1^k in Q_$1")

;; Lemma 5.17 / Definition 5.18 / Proposition 5.20: the character lambda of Q_p.  lambda(x) = PADIC-CHAR(p)(u), the
;; character of Q (exp(2 pi i {u}_p): Q/Z composed into T), for any rational u with |x - u|_p <= 1; by Lemma 5.17
;; such u exist (u = p^k z) and two of them differ by an integer.
(def-functoid 'QP-LAMBDA-AT '(qsp_ qlx_)
  '(IOTA qlw_ (AND (IN qlw_ CC) (FORSOME qlu_ (AND (IN qlu_ QQ) (AND
     (<= ((QP-ABS qsp_) ((ADD (QP-FIELD qsp_)) qlx_ ((NEG (QP-FIELD qsp_)) ((EMBED (NF-METRIC-SPACE (QQ-PADIC qsp_))) qlu_)))) 1)
     (= qlw_ ((PADIC-CHAR qsp_) qlu_))))))))
(notation! 'QP-LAMBDA-AT 'kind 'functoid 'arity 2 'english "the value at $2 of the $1-adic character lambda of Q_$1")
(def-functoid 'QP-LAMBDA '(qsp_) '(VNB-LAMBDA qly_ (CARR (QP-FIELD qsp_)) (QP-LAMBDA-AT qsp_ qly_)))
(notation! 'QP-LAMBDA 'kind 'functoid 'arity 1 'english "the character lambda of the additive group of Q_$1")
