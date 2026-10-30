;;; pruefer-vocab.scm -- WAVE 2 (2026-10-27..30), wired 2026-10-30 from scratchpad/ccrpr/pruefer-vocab.scm.
;;; Library: complex-analysis.

;;; pruefer-vocab.scm -- THE PRUEFER GROUP Z(p^infinity) = Q_p / Z_p (CCR.pdf section 5.3, Definition 5.22), SEPARATING
;;; CHARACTERS (Proposition 5.23) AND THE p-POWER ROOTS OF UNITY (Corollary 5.25).  DEFINITIONS ONLY; the laws are in
;;; theorem-library/pruefer-laws.scm.  Agent CCR-PRUEFER, 2026-10-29.  Destination: structure-library/pruefer-vocab.scm.
;;; Library: complex-analysis (as qp-vocab).  Load window: after qp-vocab, qag-vocab, ccr4-vocab (IS-ADD-CHARACTER).
;;;
;;;   PRUEFER(p)                    Z(p^infinity) = Q_p / Z_p: the quotient group (QUOTIENT-AG, qag-vocab) of the additive
;;;                                 group of Q_p by Z_p                                                   (Definition 5.22)
;;;   IS-SEPARATING-CHARACTER(K, L)  L is a character of the additive group of the NV field K (IS-ADD-CHARACTER, ccr4-vocab)
;;;                                 whose kernel is exactly Z(K): L(x) = 1 iff |x| <= 1.  The notes use the term without a
;;;                                 definition; this is the property Proposition 5.20 proves for lambda and the one
;;;                                 Proposition 5.23 needs (the induced map on K/Z(K) is injective exactly when the
;;;                                 kernel is Z(K)).
;;;   MU-PINF(p)                    the p^k-th roots of unity, k >= 0: {z in CC : z^(p^k) = 1 for some k in NN}  (Cor 5.25)
;;; Binders prp_ sck_ scl_ scx_ mpz_ mpk_.

(def-functoid 'PRUEFER '(prp_) '(QUOTIENT-AG (NORMED-FIELD-ADDITIVE-AG (QP-FIELD prp_)) (ZP prp_)))
(notation! 'PRUEFER 'kind 'functoid 'arity 1 'english "the Pruefer $1-group Q_$1/Z_$1")

(def-predicate 'IS-SEPARATING-CHARACTER '(sck_ scl_)
  '(AND (IS-ADD-CHARACTER sck_ scl_)
        (FORALL scx_ (IMPLIES (IN scx_ (CARR sck_)) (IFF (= (scl_ scx_) 1) (IN scx_ (NV-INTEGERS sck_)))))))
(notation! 'IS-SEPARATING-CHARACTER 'kind 'predicate 'arity 2
           'english "$2 is a separating character of $1 (a character whose kernel is the integral elements)")

(def-functoid 'MU-PINF '(prp_)
  '(SEP mpz_ CC (FORSOME mpk_ (AND (IN mpk_ NN) (= (power mpz_ (power prp_ mpk_)) 1)))))
(notation! 'MU-PINF 'kind 'functoid 'arity 1 'english "the group of the $1-power roots of unity")

;;   PRIMITIVE-ROOTS(n)            the primitive n-th roots of unity: z in CC with z^n = 1 and z^m /= 1 for 1 <= m < n
;;                                 (Remark 5.26)
(def-functoid 'PRIMITIVE-ROOTS '(prn_)
  '(SEP prz_ CC (AND (= (power prz_ prn_) 1)
                     (FORALL prm_ (IMPLIES (IN prm_ NN) (IMPLIES (<= 1 prm_) (IMPLIES (< prm_ prn_) (NOT (= (power prz_ prm_) 1)))))))))
(notation! 'PRIMITIVE-ROOTS 'kind 'functoid 'arity 1 'english "the primitive $1-th roots of unity")
