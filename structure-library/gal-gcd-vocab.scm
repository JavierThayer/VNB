;;; gal-gcd-vocab.scm -- a greatest common divisor of a set of ring elements (galois-theory notes,
;;; section 4, "gcd sdet A") (GALOIS, 2026-10-26).  DEFINITIONS ONLY.  Destination:
;;; structure-library/gal-gcd-vocab.scm, library algebra.  Load window: after catools-gal-vocab (DIVIDES).
;;; IS-GCD-SET(s, S, d): d divides every element of S, and every common divisor of S divides d.
(def-predicate 'IS-GCD-SET '(ggs_ ggt_ ggd_)
  '(AND (IN ggd_ (CARR ggs_))
        (AND (FORALL ggx_ (IMPLIES (IN ggx_ ggt_) (DIVIDES ggs_ ggd_ ggx_)))
             (FORALL gge_ (IMPLIES (IN gge_ (CARR ggs_))
               (IMPLIES (FORALL ggx_ (IMPLIES (IN ggx_ ggt_) (DIVIDES ggs_ gge_ ggx_))) (DIVIDES ggs_ gge_ ggd_)))))))
(notation! 'IS-GCD-SET 'kind 'predicate 'arity 3 'english "$3 is a greatest common divisor of $2 in $1")
