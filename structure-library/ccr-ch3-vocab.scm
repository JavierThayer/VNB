;;; ccr-ch3-vocab.scm -- wave of 2026-11-09/10 (agent CCR-1109-B), wired 2026-11-10 from scratchpad/ccr1109b/ccr-ch3-vocab.scm.
;;; Library: analysis.

;;; ccr-ch3-vocab.scm -- OPERATORS ON K^n OVER A NON-ARCHIMEDEAN VALUED FIELD (CCR.pdf chapter 3, s. 3.1:
;;; the max norm of a matrix, Definition 3.2).  DEFINITIONS ONLY; the laws are in
;;; theorem-library/ccr-ch3-ops.scm.  Agent CCR-1109-B, wave 2026-11-09.
;;; Destination: structure-library/ccr-ch3-vocab.scm.  Library: linear-algebra is too low (IS-NV-FIELD is
;;; analysis), so: analysis.
;;;
;;; THE MODEL.  The notes identify a linear operator T on K^n with its n-by-n matrix and define
;;; ||T||_max = ||A||_max = max |a_ij|_K.  The tree's matrices are MAT(m, n, X) (structure-library/matrix.scm)
;;; with the ring operations of the commutative-ring view V = NORMED-FIELD-AS-COMMUTATIVE-RING(K); the ring
;;; of operators is MAT-RING(V, n) and T^k is MPOW in its multiplicative monoid.  The max norm enters every
;;; statement of the chapter only through bounds ||A||_max <= c, so it is given as that predicate:
;;;
;;;   IS-MAT-BOUND(K, m, n, A, c)      A is an m-by-n matrix over K with |a_ij| <= c for every entry,
;;;                                    i.e. ||A||_max <= c
;;;   MAT-POWER(K, n, T, k)            T^k in the ring MAT-RING(V, n)
;;;   IS-POWER-BOUNDED-BY(K, n, T, c)  T is n-by-n, 0 <= c, and ||T^k||_max <= c for every k in NN
;;;   IS-POWER-BOUNDED(K, n, T)        some real c has IS-POWER-BOUNDED-BY(K, n, T, c)   (Definition 3.2:
;;;                                    C_T = sup_k ||T^k||_max < infinity)
;;;
;;; Load window: after structure-library/ccr2-vocab (IS-NV-FIELD), matrix, views, monoid-power.
;;; Binders cbv*_.  No axiom, support or stamp.

(def-predicate 'IS-MAT-BOUND '(K m n A c)
  '(AND (IN A (MAT m n (CARR K)))
        (FORALL cbvi_ (IMPLIES (IN cbvi_ (INTERVAL 1 m))
          (FORALL cbvj_ (IMPLIES (IN cbvj_ (INTERVAL 1 n))
            (<= ((FNRM K) (ENTRY A cbvi_ cbvj_)) c)))))))
(notation! 'IS-MAT-BOUND 'kind 'predicate 'arity 5
           'english "$4 is a $2-by-$3 matrix over $1 with max norm at most $5")

(def-functoid 'MAT-POWER '(K n tm j)
  '(MPOW (RING-MULTIPLICATIVE-MONOID (MAT-RING (NORMED-FIELD-AS-COMMUTATIVE-RING K) n)) tm j))
(notation! 'MAT-POWER 'kind 'functoid 'arity 4 'english "$3^$4")

(def-predicate 'IS-POWER-BOUNDED-BY '(K n tm c)
  '(AND (IN tm (MAT n n (CARR K)))
   (AND (IN c RR)
   (AND (<= 0 c)
        (FORALL cbvk_ (IMPLIES (IN cbvk_ NN) (IS-MAT-BOUND K n n (MAT-POWER K n tm cbvk_) c)))))))
(notation! 'IS-POWER-BOUNDED-BY 'kind 'predicate 'arity 4
           'english "the powers of the $2-by-$2 matrix $3 over $1 have max norm at most $4")

(def-predicate 'IS-POWER-BOUNDED '(K n tm)
  '(FORSOME cbvc_ (IS-POWER-BOUNDED-BY K n tm cbvc_)))
(notation! 'IS-POWER-BOUNDED 'kind 'predicate 'arity 3
           'english "the $2-by-$2 matrix $3 over $1 is power bounded")
