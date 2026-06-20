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

;;; ----- ball-cover machinery: the two lemmas that close compact => TB -----

;;; The r-ball cover of s: the family of all open r-balls { B(x,r) : x in X(s) },
;;; as the image of X(s) under  x |-> BALL(s,x,r).
(def-functoid 'BALL-COVER '(s r)
  '(IMAGE (VNB-LAMBDA x (BALL s x r)) (X s)))

;;; Lemma A: for r > 0 the r-ball cover is an open cover of s.
;;; (r-condition matches totally-bounded-def verbatim: r in RR, 0 <= r, r /= 0.)
(support 'ball-cover-is-open-cover
  '(FORALL s (IMPLIES (IS-METRIC-SPACE s)
     (FORALL r (IMPLIES (AND (IN r RR) (AND (<= 0 r) (NOT (= 0 r))))
       (IS-OPEN-COVER s (BALL-COVER s r)))))))
(warrant! 'ball-cover-is-open-cover 'well-known
  "The r-ball cover { B(x,r) : x in X(s) } is an open cover for r > 0: each
   ball is open (ball-is-open), and the union is all of X(s) because every
   point x lies in its own ball B(x,r) (d(x,x)=0 < r).")

;;; Lemma B: if some finite subfamily of the r-ball cover still covers s, then
;;; s has a finite r-net (the centres of the chosen balls).  This is the
;;; centre-extraction step: a finite set of balls drawn from the ball cover
;;; carries a finite set of centres, and covering by the balls is exactly the
;;; r-net condition for the centres.
(support 'finite-ball-subcover-r-net
  '(FORALL s (IMPLIES (IS-METRIC-SPACE s)
     (FORALL r (IMPLIES (AND (IN r RR) (AND (<= 0 r) (NOT (= 0 r))))
       (IMPLIES (FORSOME F (AND (SUBSET F (BALL-COVER s r))
                           (AND (IN (CARD F) NN) (IS-OPEN-COVER s F))))
         (FORSOME N (AND (IN (CARD N) NN) (IS-R-NET s N (X s) r)))))))))
(warrant! 'finite-ball-subcover-r-net 'well-known
  "A finite subcover of the r-ball cover yields a finite r-net.  Each ball in
   the finite subfamily F is B(c,r) for some centre c in X(s); the (finite) set
   N of those centres satisfies IS-R-NET(s,N,X(s),r): every point p in X(s) is
   covered by some B(c,r) in F, i.e. d(c,p) < r with c in N.  |N| <= |F| is
   finite.  The centre-extraction step (choosing a centre per ball) is sound
   because the balls come from the cover BALL-COVER(s,r), whose members are by
   construction the balls B(x,r), x in X(s).")

;;; ----- the directions used most often, stated directly -----

(support 'compact-implies-totally-bounded
  '(FORALL s (IMPLIES (IS-COMPACT s) (TOTALLY-BOUNDED s))))
(warrant! 'compact-implies-totally-bounded 'proof
  "Compact => totally bounded (calculus.pdf Prop 3.12).  For eps > 0 the open
   balls {B(x,eps) : x in X} cover X; a finite subcover's centres form a finite
   eps-net.  Half of (1)=>(4).  MACHINE-PROVEN in calculus/compact-tb-proof.scm
   (installed there as `compact-tb', modulo the asserted ball-cover lemmas
   ball-cover-is-open-cover + finite-ball-subcover-r-net); kept here as an
   asserted PSS citation, the proof run offline.")

(support 'compact-implies-complete
  '(FORALL s (IMPLIES (IS-COMPACT s) (IS-COMPLETE s))))
(warrant! 'compact-implies-complete 'reference
  "Compact => complete (calculus.pdf Prop 3.12).  A Cauchy sequence in a compact
   space has a cluster point (condition (3)); a Cauchy sequence with a cluster
   point converges to it.  Half of (1)=>(4).")
