;;; theorem-library/sum-set-right-scalar.scm
;;;
;;; sum-set-right-scalar:  right scalar pull-out for finite-set sums in a ring.
;;;
;;;   (sum_{z in X} f(z)) * b  =  sum_{z in X} (f(z) * b)
;;;
;;; Provable by finite-set-induction (cardinality.scm) using
;;; sum-set-empty + sum-set-singleton + sum-set-disjoint-union +
;;; ring-right-dist + ring-mul-zero-right at the base.  PSS-promoted
;;; from structure-library/sequences.scm 2026-05-27 (was a kernel axiom).
;;;
;;; Stated separately from [[sum-set-left-scalar]] because the ring need
;;; not be commutative.

(support 'sum-set-right-scalar
  '(FORALL s (IMPLIES (IS-RING s)
     (FORALL b (IMPLIES (IN b (A s))
     (FORALL X (IMPLIES (AND (IN X SET) (IN (CARD X) NN))
     (FORALL f (IMPLIES (IN f (FUN X (A s)))
       (= ((MUL s) (SUM-SET s X f) b)
          (SUM-SET s X (VNB-LAMBDA z ((MUL s) (f z) b)))))))))))))
