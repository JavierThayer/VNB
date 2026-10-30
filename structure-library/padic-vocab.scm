;;; padic-vocab.scm -- THE p-ADIC ABSOLUTE VALUE ON QQ (CCR.pdf section 1.2).  DEFINITIONS ONLY; the laws are in
;;; theorem-library/padic-laws.scm.  Agent PADIC, wave MAP-1026, 2026-10-26.  Destination:
;;; structure-library/padic-vocab.scm.  Library: analysis.  Load window: after structure-library/zz-divisibility,
;;; normed-field, and ccr2-vocab (IS-NV-FIELD).
;;;
;;;   ZZ-PRIME(p)          p > 1 in ZZ whose only divisors are 1, -1, p, -p
;;;   ZZ-ORD-IS(p, n, k)   p^k divides n and p^(k+1) does not: k = ord_p(n)   (section 1.2; n /= 0 has one such k)
;;;   PADIC-REL(p, x, v)   v = |x|_p: v = 0 for x = 0; for x = a/b /= 0, v 2^ord(a) = 2^ord(b)   (equation (8)
;;;                        and (10) with r = 1/2, the notes' choice in section 1.3)
;;;   PADIC-ABS(p)         x |-> |x|_p, a function QQ -> RR (the description of PADIC-REL)
;;;   QQ-PADIC(p)          QQ with + * - 0 1 and |.|_p, a NORMED-FIELD 7-tuple
;;;   QQ-NV(f)             QQ with + * - 0 1 and the function f as norm: "f is a valuation on Q" is
;;;                        IS-NV-FIELD(QQ-NV(f))                                   (Proposition 1.24)
;;;   IS-NONTRIVIAL-NV(K)  some a in K has |a| not in {0, 1}                       (before Remark 1.23)
;;; Binders cp*_.  Integer powers are the real power (power p k), integer-valued (pz-power-in-zz).

(def-predicate 'ZZ-PRIME '(cpp_)
  '(AND (IN cpp_ ZZ)
   (AND (< 1 cpp_)
        (FORALL cpd_ (IMPLIES (IN cpd_ ZZ) (IMPLIES (ZZ-DIVIDES cpd_ cpp_)
          (OR (= cpd_ 1) (OR (= cpd_ (- 1)) (OR (= cpd_ cpp_) (= cpd_ (- cpp_)))))))))))
(notation! 'ZZ-PRIME 'kind 'predicate 'arity 1 'english "$1 is a prime number")

(def-predicate 'ZZ-ORD-IS '(cpp_ cpn_ cpk_)
  '(AND (ZZ-DIVIDES (power cpp_ cpk_) cpn_) (NOT (ZZ-DIVIDES (power cpp_ (succ cpk_)) cpn_))))
(notation! 'ZZ-ORD-IS 'kind 'predicate 'arity 3 'english "$3 is the order of $2 at $1")

(def-predicate 'PADIC-REL '(cpp_ cpx_ cpv_)
  '(AND (IN cpv_ RR)
        (OR (AND (= cpx_ 0) (= cpv_ 0))
            (AND (NOT (= cpx_ 0))
                 (FORSOME cpa_ (AND (IN cpa_ ZZ) (FORSOME cpb_ (AND (IN cpb_ ZZ) (AND (NOT (= cpb_ 0)) (AND (= (* cpx_ cpb_) cpa_)
                   (FORSOME cpi_ (AND (IN cpi_ NN) (FORSOME cpj_ (AND (IN cpj_ NN)
                     (AND (ZZ-ORD-IS cpp_ cpa_ cpi_) (AND (ZZ-ORD-IS cpp_ cpb_ cpj_)
                       (= (* cpv_ (power 2 cpi_)) (power 2 cpj_))))))))))))))))))
(notation! 'PADIC-REL 'kind 'predicate 'arity 3 'english "$3 is the $1-adic absolute value of $2")

;;; NBGSEP (2026-10-28): the descriptions in PADIC-ABS and PADIC-CHAR carry the membership of
;;; their variable (cpv_ in RR, which PADIC-REL already states; cpw_ in CC and cpr_ in QQ, implied
;;; by the value cc-exp(..) and by PADIC-FRAC-REP), so the lambda bodies are predicative (NBG).
(def-functoid 'PADIC-ABS '(cpp_)
  '(VNB-LAMBDA cpx_ QQ (IOTA cpv_ (AND (IN cpv_ RR) (PADIC-REL cpp_ cpx_ cpv_)))))
(notation! 'PADIC-ABS 'kind 'functoid 'arity 1 'english "the $1-adic absolute value on the rationals")

(def-functoid 'QQ-PADIC '(cpp_)
  '(LIST QQ
         (VNB-LAMBDA (LIST x_ y_) (CARTESIAN QQ QQ) (+ x_ y_))
         (VNB-LAMBDA (LIST x_ y_) (CARTESIAN QQ QQ) (* x_ y_))
         (VNB-LAMBDA x_ QQ (- x_))
         0
         1
         (PADIC-ABS cpp_)))
(notation! 'QQ-PADIC 'kind 'functoid 'arity 1 'english "the rationals with the $1-adic absolute value")

(def-functoid 'QQ-NV '(cpf_)
  '(LIST QQ
         (VNB-LAMBDA (LIST x_ y_) (CARTESIAN QQ QQ) (+ x_ y_))
         (VNB-LAMBDA (LIST x_ y_) (CARTESIAN QQ QQ) (* x_ y_))
         (VNB-LAMBDA x_ QQ (- x_))
         0
         1
         cpf_))
(notation! 'QQ-NV 'kind 'functoid 'arity 1 'english "the rationals with the norm $1")

(def-predicate 'IS-NONTRIVIAL-NV '(cpk_)
  '(FORSOME cpa_ (AND (IN cpa_ (CARR cpk_)) (AND (NOT (= ((FNRM cpk_) cpa_) 0)) (NOT (= ((FNRM cpk_) cpa_) 1))))))
(notation! 'IS-NONTRIVIAL-NV 'kind 'predicate 'arity 1 'english "the valuation of $1 is non-trivial")

;;; Remark 5.21: the p-adic character of Q.  e(r) = exp(2 pi i r).
;;;   PADIC-FRAC-REP(p, x, r)  r = z / p^m (z in ZZ, m in NN) with |x - r|_p <= 1: a p-adic fractional part of x
;;;                            (Lemma 5.17 / Definition 5.18, on Q)
;;;   PADIC-CHAR(p)            x |-> e(r) for any such r: lambda of Definition 5.18 composed with Q/Z -> T
(def-predicate 'PADIC-FRAC-REP '(cpp_ cpx_ cpr_)
  '(AND (IN cpr_ QQ)
   (AND (FORSOME cpz_ (AND (IN cpz_ ZZ) (FORSOME cpm_ (AND (IN cpm_ NN) (= (* cpr_ (power cpp_ cpm_)) cpz_)))))
        (<= ((PADIC-ABS cpp_) (+ cpx_ (- cpr_))) 1))))
(notation! 'PADIC-FRAC-REP 'kind 'predicate 'arity 3 'english "$3 is a $1-adic fractional part of $2")

(def-functoid 'PADIC-CHAR '(cpp_)
  '(VNB-LAMBDA cpx_ QQ (IOTA cpw_ (AND (IN cpw_ CC) (FORSOME cpr_ (AND (IN cpr_ QQ) (AND (PADIC-FRAC-REP cpp_ cpx_ cpr_)
                                     (= cpw_ (cc-exp (* (* (* 2 pi) +i) cpr_))))))))))
(notation! 'PADIC-CHAR 'kind 'functoid 'arity 1 'english "the $1-adic character x |-> exp(2 pi i {x}_p) of the rationals")
