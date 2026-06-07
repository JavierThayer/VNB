;;; metric-open-sets.scm -- the topology of a metric space.
;;;
;;; Promotes the ball vocabulary of metric-topology.scm to open sets and the
;;; topological reading of continuity.  All in the established idiom: POS-RR
;;; for "> 0", SUBSET / BALL / SEP from the set kernel + metric-topology.
;;;
;;;   IS-OPEN(s, U)        U is open in s: every point of U has a ball in U
;;;   PREIMAGE(s, f, V)    { a in X(s) : f(a) in V }
;;;
;;; The topology axioms (empty / carrier / balls open; unions and finite
;;; intersections of opens open) and the open-preimage characterisation of
;;; continuity are asserted as support in the library-build phase
;;; [[feedback-library-axioms-fine]], each with a warrant sketching the proof
;;; [[feedback-warrants]].  All of this is reachable WITHOUT a function-
;;; composition operator -- the COMPOSE gap [[project-metric-continuity]]
;;; blocks only composition-of-continuous and the sequential characterisation,
;;; not the open-preimage equivalence below.
;;;
;;; Bound-variable hygiene (as in metric-continuity.scm): domain points are
;;; `a' / `b', never `x' (X is the carrier accessor -- case-fold capture).
;;; The point ranging over an open set is `y' (matching BALL's own SEP var).
;;;
;;; Dependencies: metric-space.scm (IS-METRIC-SPACE, X, D), metric-topology.scm
;;; (BALL, ball-2r-triangle, ball-subset-carrier), metric-continuity.scm
;;; (IS-CONTINUOUS), order-predicates.scm (POS-RR), set kernel (SEP, SUBSET,
;;; BIG-UNION, INTERSECTION, EMPTY-SET).  Loaded right after metric-continuity.

;;; -----------------------------------------------------------------------
;;; IS-OPEN(s, U): U is a subset of X(s) and every point of U is the centre
;;; of some r-ball (r > 0) contained in U.

(def-predicate 'IS-OPEN '(s U)
  '(AND (IS-METRIC-SPACE s)
   (AND (SUBSET U (X s))
        (FORALL y (IMPLIES (IN y U)
          (FORSOME r (AND (POS-RR r)
                          (SUBSET (BALL s y r) U))))))))

;;; -----------------------------------------------------------------------
;;; PREIMAGE(s, f, V): the f-preimage of V, cut down to the domain X(s).
;;; Written directly as a separation, so its membership law is SEP's.

(def-functoid 'PREIMAGE '(s f V)
  '(SEP a (X s) (IN (f a) V)))

;;; preimage-membership: a in PREIMAGE(s,f,V) iff a in X(s) and f(a) in V.
;;; Direct from SEP membership; recorded so proofs can rewrite by name.
(theory-add-axiom! *current-theory* 'preimage-membership
  '(FORALL s (FORALL f (FORALL V (FORALL a
     (IFF (IN a (PREIMAGE s f V))
          (AND (IN a (X s)) (IN (f a) V))))))))

;;; -----------------------------------------------------------------------
;;; Topology axioms: the open sets of a metric space form a topology.

;;; empty-is-open: the empty set is open (vacuously -- it has no points).
(support 'empty-is-open
  '(FORALL s (IMPLIES (IS-METRIC-SPACE s)
     (IS-OPEN s EMPTY-SET))))
(warrant! 'empty-is-open 'proof
  "EMPTY-SET subset X(s) holds vacuously and the point-quantifier in IS-OPEN ranges over no points; unfold IS-OPEN and discharge both conjuncts.")

;;; carrier-is-open: the whole space X(s) is open.  Any positive r works at
;;; each point since BALL(s,y,r) subset X(s) (ball-subset-carrier).
(support 'carrier-is-open
  '(FORALL s (IMPLIES (IS-METRIC-SPACE s)
     (IS-OPEN s (X s)))))
(warrant! 'carrier-is-open 'proof
  "SUBSET(X(s),X(s)) is reflexivity; at each point pick any r > 0, and BALL(s,y,r) subset X(s) by ball-subset-carrier.")

;;; ball-is-open: every open ball is an open set.  The workhorse: for y in
;;; BALL(s,x,r), the slack t = r - D(s)(x,y) > 0 gives BALL(s,y,t) subset
;;; BALL(s,x,r) by the triangle inequality (cf. ball-2r-triangle).
(support 'ball-is-open
  '(FORALL s (IMPLIES (IS-METRIC-SPACE s)
     (FORALL x (IMPLIES (IN x (X s))
       (FORALL r (IMPLIES (AND (IN r RR) (<= 0 r) (NOT (= 0 r)))
         (IS-OPEN s (BALL s x r)))))))))
(warrant! 'ball-is-open 'proof
  "For y in BALL(s,x,r) the slack t = r - D(s)(x,y) is > 0 (ball-membership); the triangle inequality (metric-triangle) gives BALL(s,y,t) subset BALL(s,x,r), so y is interior. Hence BALL(s,x,r) is open.")

;;; union-of-opens-open: an arbitrary indexed union of open sets is open.
;;; g : A -> open subsets of X(s); the union is the BIG-UNION binder.
(support 'union-of-opens-open
  '(FORALL s (IMPLIES (IS-METRIC-SPACE s)
     (FORALL A (FORALL g
       (IMPLIES (FORALL i (IMPLIES (IN i A) (IS-OPEN s (g i))))
         (IS-OPEN s (BIG-UNION i A (g i)))))))))
(warrant! 'union-of-opens-open 'proof
  "A point y of the union lies in some (g i) with i in A; the ball witnessing openness of (g i) at y is contained in (g i), hence in the union. Subset-of-carrier is inherited termwise.")

;;; inter-of-opens-open: a binary (hence finite) intersection of opens is open.
;;; Take the smaller of the two radii at a common point.
(support 'inter-of-opens-open
  '(FORALL s (IMPLIES (IS-METRIC-SPACE s)
     (FORALL U (FORALL W
       (IMPLIES (AND (IS-OPEN s U) (IS-OPEN s W))
         (IS-OPEN s (INTERSECTION U W))))))))
(warrant! 'inter-of-opens-open 'proof
  "At a point y in U cap W, openness gives balls of radii r_U, r_W inside U, W respectively; the ball of radius min(r_U,r_W) lies in both, hence in the intersection.")

;;; -----------------------------------------------------------------------
;;; Open-preimage characterisation of continuity.  This is the topological
;;; reading of IS-CONTINUOUS, and -- unlike composition / the sequential
;;; characterisation -- needs no function-composition operator.

;;; continuous-implies-open-preimage: a continuous map pulls open sets back to
;;; open sets.
(support 'continuous-implies-open-preimage
  '(FORALL s (FORALL t (FORALL f
     (IMPLIES (IS-CONTINUOUS s t f)
       (FORALL V (IMPLIES (IS-OPEN t V)
         (IS-OPEN s (PREIMAGE s f V)))))))))
(warrant! 'continuous-implies-open-preimage 'proof
  "Let a in PREIMAGE(s,f,V), so f(a) in V open: some eps-ball B(t,f(a),eps) subset V (ball-is-open / openness of V). Continuity at a gives delta > 0 with f(B(s,a,delta)) subset B(t,f(a),eps) subset V, so B(s,a,delta) subset PREIMAGE(s,f,V). Hence the preimage is open.")

;;; open-preimage-implies-continuous: the converse -- if every open set pulls
;;; back to an open set, the map is continuous.
(support 'open-preimage-implies-continuous
  '(FORALL s (FORALL t (FORALL f
     (IMPLIES (AND (IS-METRIC-SPACE s)
              (AND (IS-METRIC-SPACE t)
                   (IN f (FUN (X s) (X t)))))
       (IMPLIES (FORALL V (IMPLIES (IS-OPEN t V)
                  (IS-OPEN s (PREIMAGE s f V))))
         (IS-CONTINUOUS s t f)))))))
(warrant! 'open-preimage-implies-continuous 'proof
  "Fix a in X(s) and eps > 0. The ball V = B(t,f(a),eps) is open (ball-is-open), so PREIMAGE(s,f,V) is open by hypothesis and contains a (f(a) in V via metric-self-zero). Openness yields delta > 0 with B(s,a,delta) subset PREIMAGE(s,f,V), i.e. f maps the delta-ball into the eps-ball. Hence IS-CONTINUOUS-AT at every a, so IS-CONTINUOUS.")
