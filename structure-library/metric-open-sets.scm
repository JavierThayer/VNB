;;; metric-open-sets.scm -- the topology of a metric space.
;;;
;;; Promotes the ball vocabulary of metric-topology.scm to open sets and the
;;; topological reading of continuity.  All in the established idiom: POS-RR
;;; for "> 0", SUBSET / BALL / SEP from the set kernel + metric-topology.
;;;
;;;   IS-OPEN(s, U)        U is open in s: every point of U has a ball in U
;;;   PREIMAGE(s, f, V)    { a in PTS(s) : f(a) in V }
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
;;; `a' / `b', never `x' (PTS is the carrier accessor -- case-fold capture).
;;; The point ranging over an open set is `y' (matching BALL's own SEP var).
;;;
;;; Dependencies: metric-space.scm (IS-METRIC-SPACE, X, D), metric-topology.scm
;;; (BALL, ball-2r-triangle, ball-mem-from-le), metric-continuity.scm
;;; (IS-CONTINUOUS), order-predicates.scm (POS-RR), set kernel (SEP, SUBSET,
;;; BIG-UNION, INTERSECTION, EMPTY-SET).  Loaded right after metric-continuity.

;;; -----------------------------------------------------------------------
;;; IS-OPEN(s, U): U is a subset of PTS(s) and every point of U is the centre
;;; of some r-ball (r > 0) contained in U.

(def-predicate 'IS-OPEN '(s U)
  '(AND (IS-METRIC-SPACE s)
   (AND (SUBSET U (PTS s))
        (FORALL y (IMPLIES (IN y U)
          (FORSOME r (AND (POS-RR r)
                          (SUBSET (BALL s y r) U))))))))

;;; -----------------------------------------------------------------------
;;; PREIMAGE(s, f, V): the f-preimage of V, cut down to the domain PTS(s).
;;; Written directly as a separation, so its membership law is SEP's.

(def-functoid 'PREIMAGE '(s f V)
  '(SEP a (PTS s) (IN (f a) V)))

;;; preimage-membership: a in PREIMAGE(s,f,V) iff a in PTS(s) and f(a) in V.
;;; Direct from SEP membership; recorded so proofs can rewrite by name.
(theory-add-axiom! *current-theory* 'preimage-membership
  '(FORALL s (FORALL f (FORALL V (FORALL a
     (IFF (IN a (PREIMAGE s f V))
          (AND (IN a (PTS s)) (IN (f a) V))))))))

;;; (No `preimage-subset-carrier' axiom: PREIMAGE(s,f,V) subset PTS(s) is a SEP
;;; over PTS(s), so it falls straight out of the kernel separation rule sep-me
;;; -- a per-operator support for it would just reify the generic SEP z A p
;;; subset A.  Proved inline where needed, e.g. calculus/prop-3-15-proof.scm.
;;; [[feedback-no-closure-axiom-proliferation]])

;;; -----------------------------------------------------------------------
;;; Topology axioms: the open sets of a metric space form a topology.

;;; empty-is-open: the empty set is open (vacuously -- it has no points).
(support 'empty-is-open
  '(FORALL s (IMPLIES (IS-METRIC-SPACE s)
     (IS-OPEN s EMPTY-SET))))
(warrant! 'empty-is-open 'proof
  "EMPTY-SET subset PTS(s) holds vacuously and the point-quantifier in IS-OPEN ranges over no points; unfold IS-OPEN and discharge both conjuncts.")

;;; carrier-is-open: the whole space PTS(s) is open.  Any positive r works at
;;; each point since BALL(s,y,r) is a SEP over PTS(s), hence subset PTS(s).
(support 'carrier-is-open
  '(FORALL s (IMPLIES (IS-METRIC-SPACE s)
     (IS-OPEN s (PTS s)))))
(warrant! 'carrier-is-open 'proof
  "SUBSET(PTS(s),PTS(s)) is reflexivity; at each point pick any r > 0, and BALL(s,y,r) subset PTS(s) (a SEP over PTS(s), via the kernel sep rule).")

;;; ball-is-open: every open ball is an open set.  The workhorse: for y in
;;; BALL(s,x,r), the slack t = r - DIST(s)(x,y) > 0 gives BALL(s,y,t) subset
;;; BALL(s,x,r) by the triangle inequality (cf. ball-2r-triangle).
(support 'ball-is-open
  '(FORALL s (IMPLIES (IS-METRIC-SPACE s)
     (FORALL x (IMPLIES (IN x (PTS s))
       (FORALL r (IMPLIES (AND (IN r RR) (<= 0 r) (NOT (= 0 r)))
         (IS-OPEN s (BALL s x r)))))))))
(warrant! 'ball-is-open 'proof
  "For y in BALL(s,x,r) the slack t = r - DIST(s)(x,y) is > 0 (ball-membership); the triangle inequality (metric-triangle) gives BALL(s,y,t) subset BALL(s,x,r), so y is interior. Hence BALL(s,x,r) is open.")

;;; union-of-opens-open: an arbitrary indexed union of open sets is open.
;;; g : A -> open subsets of PTS(s); the union is the BIG-UNION binder.
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
  "MACHINE-PROVEN in calculus/prop-3-15-proof.scm (qed; proven modulo {rr-pos-shrink, ball-mem-from-le, ball-membership, continuous-is-continuous-at}; the PREIMAGE-subset-PTS(s) conjunct goes straight through the kernel SEP rule sep-me).  Sketch: let a in PREIMAGE(s,f,V), so f(a) in V open: some eps-ball B(t,f(a),eps) subset V.  Shrink eps to half<eps (rr-pos-shrink); continuity at a for half gives delta>0 with d(s)(a,z)<=delta => d(t)(f a,f z)<=half<eps, so f(z) in B(t,f(a),eps) subset V (ball-mem-from-le bridges the non-strict bound to strict ball membership).  Hence B(s,a,delta) subset PREIMAGE(s,f,V): the preimage is open.")

;;; open-preimage-implies-continuous: the converse -- if every open set pulls
;;; back to an open set, the map is continuous.
(support 'open-preimage-implies-continuous
  '(FORALL s (FORALL t (FORALL f
     (IMPLIES (AND (IS-METRIC-SPACE s)
              (AND (IS-METRIC-SPACE t)
                   (IN f (FUN (PTS s) (PTS t)))))
       (IMPLIES (FORALL V (IMPLIES (IS-OPEN t V)
                  (IS-OPEN s (PREIMAGE s f V))))
         (IS-CONTINUOUS s t f)))))))
(warrant! 'open-preimage-implies-continuous 'proof
  "Fix a in PTS(s) and eps > 0. The ball V = B(t,f(a),eps) is open (ball-is-open), so PREIMAGE(s,f,V) is open by hypothesis and contains a (f(a) in V via metric-self-zero). Openness yields delta > 0 with B(s,a,delta) subset PREIMAGE(s,f,V), i.e. f maps the delta-ball into the eps-ball. Hence IS-CONTINUOUS-AT at every a, so IS-CONTINUOUS.")

;;; -----------------------------------------------------------------------
;;; Closed sets and the closed-preimage characterisation of continuity
;;; (Prop 3.15, clause (2) of ~/docs/calculus.pdf).
;;;
;;; A set is closed iff its complement (relative to the carrier) is open.
;;; The set-level relative complement COMPLEMENT-IN(A,B) = A \ B and its
;;; membership law (complement-in-membership, theory.scm) already exist;
;;; IS-CLOSED just wires them to the metric topology.

;;; IS-CLOSED(s, A): A is a subset of PTS(s) whose complement PTS(s) \ A is open.
(def-predicate 'IS-CLOSED '(s A)
  '(AND (IS-METRIC-SPACE s)
   (AND (SUBSET A (PTS s))
        (IS-OPEN s (COMPLEMENT-IN (PTS s) A)))))

;;; preimage-complement: f-preimage commutes with relative complement,
;;;   PREIMAGE(s, f, PTS(t) \ U) = PTS(s) \ PREIMAGE(s, f, U),
;;; for f : PTS(s) -> PTS(t).  This is the algebraic identity that turns the
;;; open-preimage fact into the closed-preimage fact.
(support 'preimage-complement
  '(FORALL s (FORALL t (FORALL f (FORALL U
     (IMPLIES (AND (IS-METRIC-SPACE s)
              (AND (IS-METRIC-SPACE t)
                   (IN f (FUN (PTS s) (PTS t)))))
       (= (PREIMAGE s f (COMPLEMENT-IN (PTS t) U))
          (COMPLEMENT-IN (PTS s) (PREIMAGE s f U)))))))))
(warrant! 'preimage-complement 'proof
  "Both sides are subsets of PTS(s), so set-extensionality applies. For a in PTS(s): a in LHS iff f(a) in PTS(t)\\U iff f(a) in PTS(t) and not f(a) in U (complement-in-membership); f(a) in PTS(t) holds by fun-apply-type, so LHS-membership is `not f(a) in U`. a in RHS iff a in PTS(s) and not (a in PTS(s) and f(a) in U) (complement-in / preimage-membership), i.e. `not f(a) in U`. The two coincide.")

;;; continuous-implies-closed-preimage: a continuous map pulls closed sets
;;; back to closed sets -- Prop 3.15, (1) => (2).
(support 'continuous-implies-closed-preimage
  '(FORALL s (FORALL t (FORALL f
     (IMPLIES (IS-CONTINUOUS s t f)
       (FORALL A (IMPLIES (IS-CLOSED t A)
         (IS-CLOSED s (PREIMAGE s f A)))))))))
(warrant! 'continuous-implies-closed-preimage 'proof
  "A closed means PTS(t)\\A open; continuity (continuous-implies-open-preimage) makes PREIMAGE(s,f,PTS(t)\\A) open; preimage-complement rewrites it to PTS(s)\\PREIMAGE(s,f,A). PREIMAGE(s,f,A) subset PTS(s) (its SEP), so its complement being open is exactly IS-CLOSED(s, PREIMAGE(s,f,A)).")

;;; closed-preimage-implies-continuous: the converse -- Prop 3.15, (2) => (1).
(support 'closed-preimage-implies-continuous
  '(FORALL s (FORALL t (FORALL f
     (IMPLIES (AND (IS-METRIC-SPACE s)
              (AND (IS-METRIC-SPACE t)
                   (IN f (FUN (PTS s) (PTS t)))))
       (IMPLIES (FORALL A (IMPLIES (IS-CLOSED t A)
                  (IS-CLOSED s (PREIMAGE s f A))))
         (IS-CONTINUOUS s t f)))))))
(warrant! 'closed-preimage-implies-continuous 'proof
  "Complement flip of open-preimage-implies-continuous: given an open V subset PTS(t), PTS(t)\\V is closed, so by hypothesis PREIMAGE(s,f,PTS(t)\\V) = PTS(s)\\PREIMAGE(s,f,V) (preimage-complement) is closed, i.e. its complement PREIMAGE(s,f,V) is open. Every open set pulls back open, so f is continuous (open-preimage-implies-continuous).")
