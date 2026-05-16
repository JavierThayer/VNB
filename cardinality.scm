;;; cardinality.scm -- CARD functoid: cardinality of sets
;;;
;;; CARD maps every set A to its cardinality CARD(A) ∈ ORD.
;;; Under AC, CARD(A) is the least ordinal alpha with a bijection A -> alpha.
;;; We axiomatise the key properties directly.
;;;
;;; Dependencies: ordinals.scm (ORD, ORD-SEGMENT, succ_ORD), number-systems.scm (NN).

;;; -----------------------------------------------------------------------
;;; Basic ordinal value

;;; CARD(A) ∈ ORD for every set A
(theory-add-axiom! *current-theory* 'card-in-ord
  '(FORALL A
      (IMPLIES (IN A SET)
               (IN (CARD A) ORD))))

;;; -----------------------------------------------------------------------
;;; Concrete values

;;; CARD(∅) = 0
(theory-add-axiom! *current-theory* 'card-empty
  '(= (CARD EMPTY-SET) 0))

;;; Inserting a fresh element increments cardinality by one.
;;; PAIR(x,x) = {x} (by pairing-membership with a=b=x); both pairing axioms
;;; require the arguments to be sets, so x ∈ SET is needed here.
;;; (REVIEW.md G-10) The rest of the manual writes singletons as
;;; make-set([x]); using PAIR(x,x) here is equivalent (and pre-dates
;;; the make-set primitive) but cosmetically inconsistent.  Worth
;;; rewriting to (UNION A (MAKE-SET (LIST x))) once it's verified that
;;; the equational rewrite doesn't perturb existing card-insert proofs.
(theory-add-axiom! *current-theory* 'card-insert
  '(FORALL A
      (IMPLIES (IN A SET)
               (FORALL x
                 (IMPLIES (AND (IN x SET) (NOT (IN x A)))
                          (= (CARD (UNION A (PAIR x x)))
                             (succ_ORD (CARD A))))))))

;;; CARD(ORD-SEGMENT(n)) = n for every n ∈ NN.
;;; Bridge between cardinality and the NN-indexed model of finite sets.
(theory-add-axiom! *current-theory* 'card-segment
  '(FORALL n
      (IMPLIES (IN n NN)
               (= (CARD (ORD-SEGMENT n)) n))))

;;; -----------------------------------------------------------------------
;;; Finiteness and enumeration

;;; A finite set (CARD(A) ∈ NN) bijects with ORD-SEGMENT(CARD(A)).
;;; Existence of the bijection follows from AC + Hartogs; axiomatised here.
(theory-add-axiom! *current-theory* 'card-finite-bij
  '(FORALL A
      (IMPLIES (AND (IN A SET) (IN (CARD A) NN))
               (FORSOME phi
                 (AND (IN phi (FUN (ORD-SEGMENT (CARD A)) A))
                      ;; injective
                      (FORALL j
                        (IMPLIES (IN j (ORD-SEGMENT (CARD A)))
                          (FORALL k
                            (IMPLIES (AND (IN k (ORD-SEGMENT (CARD A)))
                                         (= (phi j) (phi k)))
                                     (= j k)))))
                      ;; surjective
                      (FORALL a
                        (IMPLIES (IN a A)
                                 (FORSOME k
                                   (AND (IN k (ORD-SEGMENT (CARD A)))
                                        (= (phi k) a))))))))))

;;; -----------------------------------------------------------------------
;;; Finite additivity

;;; CARD(A ∪ B) = CARD(A) + CARD(B) when A and B are finite and disjoint.
;;; The + on the right is NN addition (both cardinalities are in NN).
(theory-add-axiom! *current-theory* 'card-union-disjoint
  '(FORALL A
      (IMPLIES (AND (IN A SET) (IN (CARD A) NN))
               (FORALL B
                 (IMPLIES (AND (IN B SET) (IN (CARD B) NN)
                               (= (INTERSECTION A B) EMPTY-SET))
                          (= (CARD (UNION A B))
                             (+ (CARD A) (CARD B))))))))
