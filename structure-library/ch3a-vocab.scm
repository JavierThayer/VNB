;;; ch3a-vocab.scm -- automorphisms of an open subset of CC (CH3-A, 2026-10-26).
;;; DEFINITIONS ONLY.  Destination: structure-library/ch3a-vocab.scm, library complex-analysis.
;;; Load window: after the HOLOMORPHIC-ON vocabulary (structure-library/holomorphic*) and
;;; INVERSE-BIJ / BIJECTION; before theorem-library/ch3a-schwarz.
;;;
;;; IS-HOLOMORPHIC-AUTOMORPHISM(u, phi): phi is an automorphism of u in the sense of Definition 10.7
;;; of the complex analysis notes -- a bijective holomorphic mapping of u onto itself.  ("Holomorphic"
;;; is in the name to keep it apart from the algebraic automorphisms of the algebra library.)
(def-predicate 'IS-HOLOMORPHIC-AUTOMORPHISM '(hau_ hap_)
  '(AND (IN hap_ (BIJECTION hau_ hau_)) (HOLOMORPHIC-ON hau_ hap_)))

(notation! 'IS-HOLOMORPHIC-AUTOMORPHISM 'kind 'predicate 'arity 2
           'english "$2 is an automorphism of $1")

;;; CC-PARTIAL-PROD(f, n) = f(0) f(1) ... f(n-1), the finite product of complex numbers (the empty
;;; product is 1); the multiplicative twin of CC-SERIES-PARTIAL-SUM.  Installs
;;; cc-partial-prod-zero and cc-partial-prod-succ (def-by-nn-recursion).
(def-by-nn-recursion 'CC-PARTIAL-PROD '(cpf_)
  1
  '(cpn_ cpv_)
  '(* cpv_ (cpf_ cpn_)))

(notation! 'CC-PARTIAL-PROD 'kind 'functoid 'arity 2
           'english "the product of the first $2 values of $1")
