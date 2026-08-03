;;; theorem-library/sum-set-left-scalar.scm
;;;
;;; sum-set-left-scalar:  left scalar pull-out for finite-set sums in a ring.
;;;
;;;   a * (sum_{z in X} f(z))  =  sum_{z in X} (a * f(z))
;;;
;;; Provable by finite-set-induction (cardinality.scm) using
;;; sum-set-empty + sum-set-singleton + sum-set-disjoint-union +
;;; ring-left-dist + ring-mul-zero-left at the base.  PSS-promoted
;;; from structure-library/sequences.scm 2026-05-27 (was a kernel axiom).
;;;
;;; The lambda variable is z, not x: VNB case-folds, so an outer X (the
;;; set) and an inner x (the lambda's bound element) would be the same name
;;; and capture.  See [[no-case-variant-binders]].

(support 'sum-set-left-scalar
  '(FORALL s (IMPLIES (IS-RING s)
     (FORALL a (IMPLIES (IN a (CARR s))
     (FORALL X (IMPLIES (AND (IN X SET) (IN (CARD X) NN))
     (FORALL f (IMPLIES (IN f (FUN X (CARR s)))
       (= ((MUL s) a (SUM-SET s X f))
          (SUM-SET s X (VNB-LAMBDA z X ((MUL s) a (f z))))))))))))))

(warrant! 'sum-set-left-scalar 'well-known
  "Left distributivity pulled through a finite-set sum, by finite-set-induction
   (cardinality.scm): sum-set-empty and ring-mul-zero-left at the base,
   sum-set-singleton at a point, and sum-set-disjoint-union with ring-left-dist
   at the step.  Asserted from that route rather than proven; it was a kernel
   axiom in structure-library/sequences.scm until the 2026-05-27 promotion, and
   there is no script for it in archive/proven-theorems-archive.scm.")
