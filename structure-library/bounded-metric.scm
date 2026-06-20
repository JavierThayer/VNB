;;; bounded-metric.scm -- the bounded metric  rho = d/(1+d)  of a metric space,
;;; and the fact that it is topologically equivalent to the original (the
;;; identity map is bicontinuous).  Library phase: the construction is a
;;; def-functoid, the metric/equivalence facts are warranted supports.
;;;
;;; For a metric space s = (X, d), define
;;;
;;;     BDD-METRIC(s) = (X,  rho),   rho(x,y) = d(x,y) / (1 + d(x,y)).
;;;
;;; rho is a metric: nonnegativity, symmetry and the zero law are inherited
;;; from d through the increasing map f(t)=t/(1+t) (bdd-fn-* in
;;; scalar-inequalities.scm), and the triangle inequality is exactly the
;;; subadditivity of f:
;;;     rho(x,z) = f(d(x,z)) <= f(d(x,y)+d(y,z))      [f increasing, d-triangle]
;;;                          <= f(d(x,y)) + f(d(y,z)) [f subadditive]
;;;                          = rho(x,y) + rho(y,z).
;;; Every rho-distance is < 1, so rho is BOUNDED.  Because f and its inverse
;;; t |-> t/(1-t) are continuous and increasing, rho and d induce the SAME
;;; topology -- the identity map is continuous both ways.
;;;
;;; This answers "RR has a bounded metric topologically equivalent to the usual
;;; one" (the RR-BOUNDED-MS instance below) and supplies the per-factor bounded
;;; metric used to build the countable product (product-metric.scm).
;;;
;;; Loads after metric-continuity.scm (IS-CONTINUOUS) and scalar-inequalities.

;;; The construction: same carrier, distance pushed through f(t)=t/(1+t).
(def-functoid 'BDD-METRIC '(s)
  '(LIST (X s)
         (VNB-LAMBDA (LIST x y)
           (/ ((D s) x y) (+ 1 ((D s) x y))))))

;;; Carrier is unchanged.
(support 'bdd-metric-carrier
  '(FORALL s (== (X (BDD-METRIC s)) (X s))))
(warrant! 'bdd-metric-carrier 'well-known
  "BDD-METRIC keeps the point set: X(BDD-METRIC s) = X(s).  Read off the
   functoid (the carrier slot is (X s) verbatim).")

;;; The distance formula.
(support 'bdd-metric-distance
  '(FORALL s (IMPLIES (IS-METRIC-SPACE s)
     (FORALL x (IMPLIES (IN x (X s))
       (FORALL y (IMPLIES (IN y (X s))
         (= ((D (BDD-METRIC s)) x y)
            (/ ((D s) x y) (+ 1 ((D s) x y)))))))))))
(warrant! 'bdd-metric-distance 'well-known
  "Beta-reduction of the BDD-METRIC distance lambda:  rho(x,y) =
   d(x,y)/(1+d(x,y)).")

;;; rho is a metric.
(support 'bdd-metric-is-metric-space
  '(FORALL s (IMPLIES (IS-METRIC-SPACE s)
     (IS-METRIC-SPACE (BDD-METRIC s)))))
(warrant! 'bdd-metric-is-metric-space 'well-known
  "rho = d/(1+d) is a metric.  Nonnegativity, symmetry and the zero law come
   from d via the increasing map f(t)=t/(1+t) (bdd-fn-nonneg, bdd-fn-mono,
   and f(t)=0 iff t=0); the triangle inequality is f's subadditivity
   (bdd-fn-subadd) composed with monotonicity over d's triangle inequality.")

;;; rho is bounded: every distance is < 1.
(support 'bdd-metric-bounded
  '(FORALL s (IMPLIES (IS-METRIC-SPACE s)
     (FORALL x (IMPLIES (IN x (X s))
       (FORALL y (IMPLIES (IN y (X s))
         (< ((D (BDD-METRIC s)) x y) 1))))))))
(warrant! 'bdd-metric-bounded 'well-known
  "rho(x,y) = d/(1+d) < 1 always (bdd-fn-lt-one): the bounded metric has
   diameter at most 1, whatever the diameter of (X,d).")

;;; Topological equivalence: the identity map X(s) -> X(BDD-METRIC s) is
;;; continuous in BOTH directions (a homeomorphism), so rho and d give the
;;; same open sets.  This is the precise sense of "topologically equivalent".
(support 'bdd-metric-id-bicontinuous
  '(FORALL s (IMPLIES (IS-METRIC-SPACE s)
     (AND (IS-CONTINUOUS s (BDD-METRIC s) (VNB-LAMBDA x x))
          (IS-CONTINUOUS (BDD-METRIC s) s (VNB-LAMBDA x x))))))
(warrant! 'bdd-metric-id-bicontinuous 'well-known
  "The identity (X,d) <-> (X, d/(1+d)) is bicontinuous, so the two metrics are
   topologically equivalent.  Forward: rho <= d (bdd-fn-le-arg), so id is
   1-Lipschitz, hence continuous.  Backward: rho(x,y) < eps/(1+eps) forces
   d(x,y) < eps (f is an increasing bijection [0,oo)->[0,1) with continuous
   inverse t/(1-t)), so id is continuous the other way too.")

;;; =======================================================================
;;; The RR instance: RR carries a bounded metric equivalent to the usual one.
;;; RR-MS = (RR, |x-y|) is the standard metric (numeric-instances.scm);
;;; RR-BOUNDED-MS = (RR, |x-y|/(1+|x-y|)) is bounded and equivalent to it.

(def-functoid 'RR-BOUNDED-MS '() '(BDD-METRIC RR-MS))

(support 'rr-bounded-ms-is-metric-space
  '(IS-METRIC-SPACE RR-BOUNDED-MS))
(warrant! 'rr-bounded-ms-is-metric-space 'well-known
  "RR-BOUNDED-MS = BDD-METRIC(RR-MS) is a metric space: the bounded-metric
   construction applied to the standard real line RR-MS (which is a metric
   space, rr-is-metric-space).")

(support 'rr-bounded-ms-bounded
  '(FORALL x (IMPLIES (IN x RR)
     (FORALL y (IMPLIES (IN y RR)
       (< ((D RR-BOUNDED-MS) x y) 1))))))
(warrant! 'rr-bounded-ms-bounded 'well-known
  "Every distance in RR-BOUNDED-MS is < 1: the bounded real metric
   |x-y|/(1+|x-y|) has diameter <= 1 although RR itself is unbounded.")

;;; THE answer to (b): RR has a bounded metric topologically equivalent to the
;;; usual metric -- the identity map RR-MS <-> RR-BOUNDED-MS is bicontinuous.
(support 'rr-bounded-equivalent
  '(AND (IS-CONTINUOUS RR-MS RR-BOUNDED-MS (VNB-LAMBDA x x))
        (IS-CONTINUOUS RR-BOUNDED-MS RR-MS (VNB-LAMBDA x x))))
(warrant! 'rr-bounded-equivalent 'well-known
  "RR has a BOUNDED metric topologically equivalent to the usual one: the
   identity map between RR-MS (distance |x-y|) and RR-BOUNDED-MS (distance
   |x-y|/(1+|x-y|)) is continuous in both directions, so the two metrics
   define the same topology on RR while the latter is bounded.  Instance of
   bdd-metric-id-bicontinuous at s = RR-MS.")
