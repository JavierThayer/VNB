;;; derivative.scm -- the Caratheodory derivative, as VOCABULARY.
;;;
;;;   IS-DIFF-AT(f, a, L)   f is differentiable at a with derivative L
;;;   DERIV(f, a)           the unique such L (an IOTA; well defined by
;;;                         `derivative-unique', theorem-library/differentiation.scm)
;;;
;;; HOISTED HERE 2026-09-20 (batch 12-A) from theorem-library/differentiation.scm:37,
;;; where the two definitions sat inside a proof file at load position ~358 of
;;; 546.  Thirty-four other files STATE theorems with IS-DIFF-AT, and every one
;;; of them had to load below that proof file for no reason: the definition
;;; needs nothing but IS-CONTINUOUS-AT (structure-library/metric-continuity),
;;; RR-MS (structure-library/numeric-instances) and the base theory, all of
;;; which load far above here.
;;;
;;; Nothing is proven here.  The four proofs of differentiation.scm -- among
;;; them `derivative-unique', which is what makes the IOTA a definition --
;;; stay where they are, and every citation keeps its name.

;;; IS-DIFF-AT(f, a, L): f is differentiable at a with derivative L.
(def-predicate 'IS-DIFF-AT '(f a L)
  '(AND (IN f (FUN RR RR))
   (AND (IN a RR)
   (AND (IN L RR)
        (FORSOME phi
          (AND (IN phi (FUN RR RR))
          (AND (IS-CONTINUOUS-AT RR-MS RR-MS phi a)
          (AND (= (phi a) L)
               (FORALL x (IMPLIES (IN x RR)
                 (= (- (f x) (f a)) (* (phi x) (- x a)))))))))))))

;;; DERIV(f, a) = the unique L with IS-DIFF-AT(f,a,L) (well-defined by
;;; derivative-unique, theorem-library/differentiation.scm); equals phi(a).
;;; Written f'(a) in the notes.
(def-functoid 'DERIV '(f a)
  '(IOTA L (IS-DIFF-AT f a L)))

;;; The ENGLISH of the predicate, read by wff->english / the proof reader
;;; (operators.scm).  A def-predicate's reading cannot be derived the way a
;;; structure's noun can, so it is written next to what it means.
(notation! 'IS-DIFF-AT 'kind 'predicate 'arity 3
           'english "$1 is differentiable at $2, with derivative $3")
