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
;;; The distance lambda binds the two points as `u, v', NOT `x, y': the point-set
;;; accessor was `X' when this was written -- it folds to x and sits in the
;;; adjacent slot -- so a lambda var `x' would have clashed with it.  The accessor
;;; is `PTS' now; the names are kept.  [[feedback_no_case_variant_binders]]
(def-functoid 'BDD-METRIC '(s)
  '(LIST (PTS s)
         (VNB-LAMBDA (LIST u v) (CARTESIAN (PTS s) (PTS s))
           (/ ((DIST s) u v) (+ 1 ((DIST s) u v))))))

;;; Carrier is unchanged.
(support 'bdd-metric-carrier
  '(FORALL s (== (PTS (BDD-METRIC s)) (PTS s))))
(warrant! 'bdd-metric-carrier 'well-known
  "BDD-METRIC keeps the point set: PTS(BDD-METRIC s) = PTS(s).  Read off the
   functoid (the carrier slot is (PTS s) verbatim).")

;;; The distance formula.
(support 'bdd-metric-distance
  '(FORALL s (IMPLIES (IS-METRIC-SPACE s)
     (FORALL x (IMPLIES (IN x (PTS s))
       (FORALL y (IMPLIES (IN y (PTS s))
         (= ((DIST (BDD-METRIC s)) x y)
            (/ ((DIST s) x y) (+ 1 ((DIST s) x y)))))))))))
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
     (FORALL x (IMPLIES (IN x (PTS s))
       (FORALL y (IMPLIES (IN y (PTS s))
         (< ((DIST (BDD-METRIC s)) x y) 1))))))))
(warrant! 'bdd-metric-bounded 'well-known
  "rho(x,y) = d/(1+d) < 1 always (bdd-fn-lt-one): the bounded metric has
   diameter at most 1, whatever the diameter of (X,d).")

;;; Topological equivalence: the identity map PTS(s) -> PTS(BDD-METRIC s) is
;;; continuous in BOTH directions (a homeomorphism), so rho and d give the
;;; same open sets.  This is the precise sense of "topologically equivalent".
(support 'bdd-metric-id-bicontinuous
  '(FORALL s (IMPLIES (IS-METRIC-SPACE s)
     (AND (IS-CONTINUOUS s (BDD-METRIC s) (VNB-LAMBDA x (PTS s) x))
          (IS-CONTINUOUS (BDD-METRIC s) s (VNB-LAMBDA x (PTS (BDD-METRIC s)) x))))))
(warrant! 'bdd-metric-id-bicontinuous 'well-known
  "The identity (X,d) <-> (X, d/(1+d)) is bicontinuous, so the two metrics are
   topologically equivalent.  Forward: rho <= d (bdd-fn-le-arg), so id is
   1-Lipschitz, hence continuous.  Backward: rho(x,y) < eps/(1+eps) forces
   d(x,y) < eps (f is an increasing bijection [0,oo)->[0,1) with continuous
   inverse t/(1-t)), so id is continuous the other way too.")

;;; -----------------------------------------------------------------------
;;; Two packagings of the engine above, so the metrizability theorem
;;; (metrizable-iff-bounded-metrizable, proven in theorem-library) reads in a few
;;; steps instead of re-deriving the typing and topology plumbing inline.

;;; BDD-METRIC of a metric space is a BOUNDED metric space.
(support 'bdd-metric-is-bounded-metric-space
  '(FORALL s (IMPLIES (IS-METRIC-SPACE s)
     (IS-BOUNDED-METRIC-SPACE (BDD-METRIC s)))))
(warrant! 'bdd-metric-is-bounded-metric-space 'well-known
  "BDD-METRIC(s) is a bounded metric space: a metric space by
   bdd-metric-is-metric-space, and 1 in RR bounds every distance since
   d/(1+d) < 1 <= 1 (bdd-metric-bounded).")

;;; BDD-METRIC preserves the metric topology -- the topological-invariance step.
(support 'bdd-metric-preserves-metric-top
  '(FORALL s (IMPLIES (IS-METRIC-SPACE s)
     (== (METRIC-TOP (BDD-METRIC s)) (METRIC-TOP s)))))
(warrant! 'bdd-metric-preserves-metric-top 'well-known
  "METRIC-TOP(BDD-METRIC s) = METRIC-TOP(s): d and d/(1+d) are topologically
   equivalent.  The identity map is bicontinuous (bdd-metric-id-bicontinuous), so
   applying continuous-implies-open-preimage to the identity (whose preimage of a
   set is that set) in both directions gives IS-OPEN(s,U) <=> IS-OPEN(BDD-METRIC s, U);
   the carriers agree (bdd-metric-carrier), so the two [carrier, opens] tuples are
   equal.")

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
       (< ((DIST RR-BOUNDED-MS) x y) 1))))))
(warrant! 'rr-bounded-ms-bounded 'well-known
  "Every distance in RR-BOUNDED-MS is < 1: the bounded real metric
   |x-y|/(1+|x-y|) has diameter <= 1 although RR itself is unbounded.")

;;; THE answer to (b): RR has a bounded metric topologically equivalent to the
;;; usual metric -- the identity map RR-MS <-> RR-BOUNDED-MS is bicontinuous.
(support 'rr-bounded-equivalent
  '(AND (IS-CONTINUOUS RR-MS RR-BOUNDED-MS (VNB-LAMBDA x RR x))
        (IS-CONTINUOUS RR-BOUNDED-MS RR-MS (VNB-LAMBDA x RR x))))
(warrant! 'rr-bounded-equivalent 'well-known
  "RR has a BOUNDED metric topologically equivalent to the usual one: the
   identity map between RR-MS (distance |x-y|) and RR-BOUNDED-MS (distance
   |x-y|/(1+|x-y|)) is continuous in both directions, so the two metrics
   define the same topology on RR while the latter is bounded.  Instance of
   bdd-metric-id-bicontinuous at s = RR-MS.")

;;; =======================================================================
;;; The PREDICATE `bounded metric space', and the metrizability theorem it
;;; enables.  Everything above is per-instance ("this distance is < 1"); this
;;; packages boundedness as a first-class hypothesis so it can appear in the
;;; statement of T1.
;;;
;;; IS-BOUNDED-METRIC-SPACE(s): a metric space whose diameter is finite -- some
;;; real b bounds every distance.  (Diameter <= b for some b, not necessarily
;;; < 1; BDD-METRIC gives the < 1 witness when one is wanted.)

(def-predicate 'IS-BOUNDED-METRIC-SPACE '(s)
  (conjuncts->and
    (list
      '(IS-METRIC-SPACE s)
      (list 'FORSOME 'b
        (conjuncts->and
          (list '(IN b RR)
                (forall-guarded '(x y)
                  (list '(IN x (PTS s)) '(IN y (PTS s)))
                  '(<= ((DIST s) x y) b))))))))
(notation! 'IS-BOUNDED-METRIC-SPACE 'noun "bounded metric space" 'article "a")

;;; The metrizability theorem T1 (metrizable <=> bounded-metrizable) is PROVEN in
;;; theorem-library/metrizable-bounded-proof.scm, from the three packagings above
;;; plus metric-top-is-metrizable-top-space.
