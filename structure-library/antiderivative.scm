;;; antiderivative.scm -- Definition 4.6 (calculus.pdf), as VOCABULARY.
;;;
;;;   IS-ANTIDERIVATIVE(f, phi, a, b)   f is continuous on [a,b], and on (a,b)
;;;                                     differentiable with derivative phi
;;;   IS-ANTIDERIVABLE(phi, a, b)       some f antidifferentiates phi on [a,b]
;;;
;;; HOISTED HERE 2026-09-20 (batch 12-A) from theorem-library/antiderivative.scm:116,
;;; where the two definitions sat inside a proof file at load position ~514 of
;;; 546 -- which jammed all twelve files stated with them into the last thirty
;;; slots of the load.  The definitions need only CCINT
;;; (structure-library/extreme-value), IS-DIFF-AT (structure-library/derivative),
;;; IS-CONTINUOUS-AT and RR-MS, all of which load just above.
;;;
;;; Nothing is proven here: the eleven proofs of
;;; theorem-library/antiderivative.scm -- the projections of Def 4.6 and the
;;; Chapter 4 results -- stay where they are, and every citation keeps its name.

(def-predicate 'IS-ANTIDERIVATIVE '(f phi a b)
  (conjuncts->and
    (list '(IN f (FUN RR RR))
          '(IN phi (FUN RR RR))
          '(IN a RR)
          '(IN b RR)
          '(< a b)
          '(FORALL x_ (IMPLIES (IN x_ (CCINT a b))
                       (IS-CONTINUOUS-AT RR-MS RR-MS f x_)))
          '(FORALL th_ (IMPLIES (AND (IN th_ RR) (AND (< a th_) (< th_ b)))
                       (IS-DIFF-AT f th_ (phi th_)))))))
(notation! 'IS-ANTIDERIVATIVE 'kind 'predicate 'arity 4
           'english "$1 is an antiderivative of $2 on the interval [$3, $4]")

(def-predicate 'IS-ANTIDERIVABLE '(phi a b)
  '(FORSOME f_ (IS-ANTIDERIVATIVE f_ phi a b)))
(notation! 'IS-ANTIDERIVABLE 'kind 'predicate 'arity 3
           'english "$1 is antiderivable on the interval [$2, $3]")
