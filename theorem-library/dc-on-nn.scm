;;; theorem-library/dc-on-nn.scm
;;;
;;; Dependent recursion / dependent choice on NN, as a Proof Support Set
;;; entry.
;;;
;;; Schema:
;;;
;;;   Given a set X, an element a in X, and a set R (intended as a
;;;   subset of NN x X x X) such that
;;;
;;;     forall k in NN. forall x in X. exists y in X. (LIST k x y) in R,
;;;
;;;   there exists f : NN -> X with f(0) = a and, for every k in NN,
;;;
;;;     (LIST k (f k) (f (succ k))) in R.
;;;
;;; Triples are encoded as (LIST k x y) per the n-ary apply-tupling
;;; convention installed in theorem-library/axioms.scm.
;;;
;;; This is the inside-a-proof companion to def-by-nn-recursion: the
;;; latter is a top-level definition macro that installs a named
;;; operator from a closed-form successor expression, while dc-on-nn
;;; produces a sequence inside a proof from a witness relation.
;;;
;;; Derivable in VNB from primitive recursion on NN + Hilbert epsilon:
;;; choose g(k, x) := CHOICE { y in X : (LIST k x y) in R } using
;;; global choice, then recurse f(0) := a, f(succ k) := g(k, f k).
;;; Accepted here without mechanical proof during the library-building
;;; phase.
;;;
;;; Typical use: extracting a sequence of nested infinite subsets of NN
;;; (S_0 supset S_1 supset ...) for the diagonalization argument; more
;;; generally, any "build a sequence by repeated choices" construction.

(support 'dc-on-nn
  '(FORALL X
     (IMPLIES (IN X SET)
       (FORALL a
         (IMPLIES (IN a X)
           (FORALL R
             (IMPLIES (IN R SET)
               (IMPLIES
                 (FORALL k
                   (IMPLIES (IN k NN)
                     (FORALL u
                       (IMPLIES (IN u X)
                         (FORSOME y
                           (AND (IN y X)
                                (IN (LIST k u y) R)))))))
                 (FORSOME f
                   (AND (IN f (FUN NN X))
                        (AND (= (f 0) a)
                             (FORALL k
                               (IMPLIES (IN k NN)
                                 (IN (LIST k (f k) (f (succ k))) R))))))))))))))
