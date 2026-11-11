;;; ccr1109a5-vocab.scm -- wave of 2026-11-09/10 (agent CCR-1109-A5), wired 2026-11-10 from scratchpad/ccr1109a5/ccr1109a5-vocab.scm.
;;; Library: analysis.

;;; ccr1109a5-vocab.scm -- CCR.pdf section 6.1.1: the trivial absolute value of a finite field F_q and the residue
;;; pairing of F_q((x)).  DEFINITIONS ONLY.  Agent CCR-1109-A5, 2026-11-09.
;;; Destination: structure-library/ccr1109a5-vocab.scm.  Library: analysis (TRIV-NF is a NORMED-FIELD tuple;
;;; LAURENT-PAIRING names LAURENT-SET / LAURENT-MUL of ccr1109a3-laurent-vocab, which is analysis).
;;; Load window: after structure-library/ccr1109a3-laurent-vocab (LAURENT-SET, LAURENT-MUL) and normed-field.
;;;
;;;   TRIV-ABS(K, x)             0 at x = 0, 1 elsewhere: the trivial absolute value of the ring K
;;;   TRIV-NF(K)                 the ring K with its trivial absolute value, as a NORMED-FIELD 7-tuple
;;;                              (QP-FIELD's / LAURENT-NF's shape: the ring's six slots, then the norm).  For a
;;;                              FINITE field this is the only absolute value there is (nf-finite-norm-trivial,
;;;                              theorem-library/ccr1109a5-finite-field), so "a character of F_q" is a
;;;                              character of TRIV-NF(F_q), and every additive homomorphism F_q -> T is one
;;;                              (nf-finite-add-character).
;;;   LAURENT-PAIRING(K, chi)    (g, f) |-> chi(a_0(f g)) on K((x)) x K((x)): the bicharacter (61) of
;;;                              Proposition 6.10.  a_0(f g) = sum_k a_k(f) a_(-k)(g) is the coefficient at 0
;;;                              of the product, a finite sum (the product of Laurent series is the
;;;                              convolution of ccr1109a3-laurent-vocab), so chi of it is the finite product (59).
;;; Binders a5*_.

(def-functoid 'TRIV-ABS '(a5k_ a5x_) '(IF (= a5x_ (ZERO a5k_)) 0 1))
(notation! 'TRIV-ABS 'kind 'functoid 'arity 2 'english "the trivial absolute value of $2 in $1")

(def-functoid 'TRIV-NF '(a5k_)
  '(LIST (CARR a5k_) (ADD a5k_) (MUL a5k_) (NEG a5k_) (ZERO a5k_) (ONE a5k_)
         (VNB-LAMBDA a5x_ (CARR a5k_) (TRIV-ABS a5k_ a5x_))))
(notation! 'TRIV-NF 'kind 'functoid 'arity 1 'english "the field $1 with the trivial absolute value")

(def-functoid 'LAURENT-PAIRING '(a5k_ a5c_)
  '(VNB-LAMBDA (LIST a5g_ a5f_) (CARTESIAN (LAURENT-SET a5k_) (LAURENT-SET a5k_))
     (a5c_ ((LAURENT-MUL a5k_ a5f_ a5g_) 0))))
(notation! 'LAURENT-PAIRING 'kind 'functoid 'arity 2
           'english "the pairing (g, f) |-> $2(a_0(f g)) on the Laurent series over $1")
