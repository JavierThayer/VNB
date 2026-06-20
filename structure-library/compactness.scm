;;; compactness.scm -- compactness of a metric space and the four-way
;;; characterization (calculus.pdf Prop 3.12).  Supplies the missing
;;; vocabulary (IS-COMPACT, IS-OPEN-COVER, CLUSTER-POINT, HAS-FIP) and states
;;; the characterization as warranted supports (library phase); the proof
;;; directions are the stress test in calculus/compact-stress.scm.
;;;
;;; Prop 3.12.  For a metric space X the following are equivalent:
;;;   (1) X is compact (every open cover has a finite subcover);
;;;   (2) every family of closed sets with the finite-intersection property has
;;;       nonempty intersection;
;;;   (3) every sequence in X has a cluster point;
;;;   (4) X is totally bounded and complete.
;;;
;;; Loads after metric-open-sets (IS-OPEN/IS-CLOSED), metric-topology
;;; (TOTALLY-BOUNDED/BALL), metric-completeness (IS-COMPLETE).

;;; ----- vocabulary -----

;;; An open cover of s: a collection C of open sets whose union is X(s).
(def-predicate 'IS-OPEN-COVER '(s C)
  '(AND (IS-METRIC-SPACE s)
   (AND (FORALL U (IMPLIES (IN U C) (IS-OPEN s U)))
        (== (BIG-UNION U C U) (X s)))))

;;; s is compact: every open cover has a finite subcover.
(def-predicate 'IS-COMPACT '(s)
  '(AND (IS-METRIC-SPACE s)
        (FORALL C (IMPLIES (IS-OPEN-COVER s C)
          (FORSOME F (AND (SUBSET F C)
                     (AND (IN (CARD F) NN)
                          (IS-OPEN-COVER s F))))))))

;;; x is a cluster point of the sequence f: every ball around x meets f at
;;; arbitrarily large indices (the sequence is frequently near x).
(def-predicate 'CLUSTER-POINT '(s f x)
  '(AND (IS-METRIC-SPACE s)
   (AND (IN f (FUN NN (X s)))
   (AND (IN x (X s))
        (FORALL eps (IMPLIES (POS-RR eps)
          (FORALL N (IMPLIES (IN N NN)
            (FORSOME n (AND (IN n NN)
                       (AND (<= N n)
                            (< ((D s) (f n) x) eps))))))))))))

;;; A family C of closed sets with the FINITE-INTERSECTION PROPERTY: every
;;; finite subfamily has a common point.
(def-predicate 'HAS-FIP '(s C)
  '(AND (IS-METRIC-SPACE s)
   (AND (FORALL A (IMPLIES (IN A C) (IS-CLOSED s A)))
        (FORALL F (IMPLIES (AND (SUBSET F C) (IN (CARD F) NN))
          (FORSOME p (IN p (BIG-INTERSECTION A F A))))))))

;;; ----- Prop 3.12: the four-way characterization (stated as supports) -----

;;; (1) <=> (4):  compact  iff  totally bounded and complete.
(support 'compact-iff-tb-complete
  '(FORALL s (IMPLIES (IS-METRIC-SPACE s)
     (IFF (IS-COMPACT s)
          (AND (TOTALLY-BOUNDED s) (IS-COMPLETE s))))))
(warrant! 'compact-iff-tb-complete 'reference
  "calculus.pdf Prop 3.12 (1)<=>(4): a metric space is compact iff it is totally
   bounded and complete.  (=>) finite subcovers of ball-covers give finite
   eps-nets (total boundedness), and a Cauchy sequence has a cluster point
   (compactness via (3)) which is then its limit (completeness).  (<=) total
   boundedness + completeness gives sequential compactness by the standard
   diagonal/rapidly-Cauchy-subsequence argument, which gives compactness.")

;;; (1) <=> (3):  compact  iff  every sequence has a cluster point.
(support 'compact-iff-cluster-point
  '(FORALL s (IMPLIES (IS-METRIC-SPACE s)
     (IFF (IS-COMPACT s)
          (FORALL f (IMPLIES (IN f (FUN NN (X s)))
            (FORSOME x (CLUSTER-POINT s f x))))))))
(warrant! 'compact-iff-cluster-point 'reference
  "calculus.pdf Prop 3.12 (1)<=>(3): compact iff every sequence has a cluster
   point (equivalently, a convergent subsequence -- sequential compactness in a
   metric space).  The cluster point is the limit of a rapidly-Cauchy
   subsequence (cauchy-rapid-subsequence).")

;;; (1) <=> (2):  compact  iff  every closed family with FIP has common point.
(support 'compact-iff-fip
  '(FORALL s (IMPLIES (IS-METRIC-SPACE s)
     (IFF (IS-COMPACT s)
          (FORALL C (IMPLIES (HAS-FIP s C)
            (FORSOME p (IN p (BIG-INTERSECTION A C A)))))))))
(warrant! 'compact-iff-fip 'reference
  "calculus.pdf Prop 3.12 (1)<=>(2): compact iff every family of closed sets
   with the finite-intersection property has nonempty intersection.  This is
   the open-cover condition dualised by complementation: an open cover with no
   finite subcover is exactly a closed family with the FIP and empty
   intersection.")

;;; ----- the two directions used most often, stated directly -----

(support 'compact-implies-totally-bounded
  '(FORALL s (IMPLIES (IS-COMPACT s) (TOTALLY-BOUNDED s))))
(warrant! 'compact-implies-totally-bounded 'reference
  "Compact => totally bounded (calculus.pdf Prop 3.12).  For eps > 0 the open
   balls {B(x,eps) : x in X} cover X; a finite subcover's centres form a finite
   eps-net.  Half of (1)=>(4).")

(support 'compact-implies-complete
  '(FORALL s (IMPLIES (IS-COMPACT s) (IS-COMPLETE s))))
(warrant! 'compact-implies-complete 'reference
  "Compact => complete (calculus.pdf Prop 3.12).  A Cauchy sequence in a compact
   space has a cluster point (condition (3)); a Cauchy sequence with a cluster
   point converges to it.  Half of (1)=>(4).")
