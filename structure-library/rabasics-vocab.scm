;;; rabasics-vocab.scm -- vocabulary for the RA-BASICS wave (calculus.pdf 1.13, 3.7; CA 1.7).
;;; DEFINITIONS ONLY (destination: structure-library/).  Agent RA-BASICS, 2026-10-26
;;; (NEW DEFINITIONS, the user's to confirm; added under the rule "missing vocabulary is not a
;;; stopping point").
;;;
;;;   INF(s)
;;;       the infimum of a set of reals, written through the library's SUP:
;;;       INF(s) = -SUP{ v in RR : v = -x for some x in s }.  The notes (after Axiom 1):
;;;       "Lower bounds and greatest lower bounds are defined similarly ... the infimum of S".
;;;       The tree had SUP (primitive, number-systems.scm) and no INF.  That INF(s) IS the
;;;       greatest lower bound of a non-empty set bounded below is proven (rr-inf-is-glb,
;;;       theorem-library rabasics-monotone).
;;;
;;;   IS-ORDER-ISO(f, a, b)
;;;       f is a bijection of a onto b and strictly increasing: x < y in a gives f(x) < f(y).
;;;       For linearly ordered a and b this is the textbook order isomorphism (x <= y iff
;;;       f(x) <= f(y)).  It is stated with < on purpose.  (Updated 2026-10-27: the remark that the
;;;       <=-iff form is not provable for a map onto RR-STAR is out of date.  Since the RR-STAR
;;;       order primitives of 2026-10-26, <= is a total order on RR-STAR, and the <=-iff form is
;;;       proven for the extended line: ccint-rr-star-order-iso-le, ccint-rr-star-iso-le-iff,
;;;       theorem-library/extorder-iso.scm.)
;;;
;;; STATEMENT CHECKS.  No IOTA, CHOICE or FORSOME witness outside a body.  BINDERS: infs_ infv_
;;; infx_, oisf_ oisa_ oisb_ oisx_ oisy_; none folds onto a class name, an accessor or a
;;; registered constant.  Library: core (SUP, RR, BIJECTION).  Load slot: after
;;; structure-library/bijection and number-systems.

(def-functoid 'INF '(infs_)
  '(- (SUP (SEP infv_ RR (FORSOME infx_ (AND (IN infx_ infs_) (= infv_ (- infx_))))))))
(notation! 'INF 'kind 'functoid 'arity 1
           'english "the infimum of $1")

(def-predicate 'IS-ORDER-ISO '(oisf_ oisa_ oisb_)
  '(AND (IN oisf_ (BIJECTION oisa_ oisb_))
        (FORALL oisx_ (IMPLIES (IN oisx_ oisa_)
          (FORALL oisy_ (IMPLIES (IN oisy_ oisa_)
            (IMPLIES (< oisx_ oisy_) (< (oisf_ oisx_) (oisf_ oisy_)))))))))
(notation! 'IS-ORDER-ISO 'kind 'predicate 'arity 3
           'english "$1 is an order isomorphism of $2 onto $3")
