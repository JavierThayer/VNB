;;; RETIRED 2026-09-17 (proven): continuous-implies-open-preimage -- theorem-library/rake-cont-preimage.scm
;;; (modulo 0, via dk-halve!; this file now holds no support at all).
;;; RETIRED 2026-09-17 (proven): empty-is-open, carrier-is-open, union-of-opens-open,
;;; inter-of-opens-open, preimage-complement, open-preimage-implies-continuous,
;;; continuous-implies-closed-preimage, closed-preimage-implies-continuous --
;;; theorem-library/rake-open-sets.scm (all modulo 0 except
;;; continuous-implies-closed-preimage, which bills continuous-implies-open-preimage,
;;; the one support left in this file).
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
;;; Dependencies: metric-space.scm (IS-METRIC-SPACE, PTS, DIST), metric-topology.scm
;;; (BALL, ball-2r-triangle, ball-mem-from-le), metric-continuity.scm
;;; (IS-CONTINUOUS), order-predicates.scm (POS-RR), set kernel (SEP, SUBSET,
;;; BIG-UNION, INTERSECTION, EMPTY-SET).  Loaded right after metric-continuity.
;;; RETIRED 2026-09-14 (proven): ball-is-open -- theorem-library/ball-is-open.scm

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
;;; subset A.  Proved inline where needed, e.g. archive/calculus-pre-rename/prop-3-15-proof.scm.
;;; [[feedback-no-closure-axiom-proliferation]])

;;; -----------------------------------------------------------------------
;;; Topology axioms: the open sets of a metric space form a topology.

;;; empty-is-open: the empty set is open (vacuously -- it has no points).

;;; carrier-is-open: the whole space PTS(s) is open.  Any positive r works at
;;; each point since BALL(s,y,r) is a SEP over PTS(s), hence subset PTS(s).

;;; ball-is-open: every open ball is an open set.  The workhorse: for y in
;;; BALL(s,x,r), the slack t = r - DIST(s)(x,y) > 0 gives BALL(s,y,t) subset
;;; BALL(s,x,r) by the triangle inequality (cf. ball-2r-triangle).

;;; union-of-opens-open: an arbitrary indexed union of open sets is open.
;;; g : A -> open subsets of PTS(s); the union is the BIG-UNION binder.

;;; inter-of-opens-open: a binary (hence finite) intersection of opens is open.
;;; Take the smaller of the two radii at a common point.

;;; -----------------------------------------------------------------------
;;; Open-preimage characterisation of continuity.  This is the topological
;;; reading of IS-CONTINUOUS, and -- unlike composition / the sequential
;;; characterisation -- needs no function-composition operator.

;;; continuous-implies-open-preimage: a continuous map pulls open sets back to
;;; open sets.
;; RE-TIERED 2026-09-15 from `proof' to `informal', because the claim of a
;; machine proof was AUDITED and no longer holds.  The proof DID exist; the
;; accessor rename invalidated it and nobody re-ran it.  The named file is still
;; on disk and still byte-identical, and against today's band it DIES at line 124
;; -- `focus-leaf!: no frontier leaf matching "subset x(s"' -- because the metric
;; carrier is `PTS' now and the distance is `DIST'.  Nine sites spell them the old
;; way.  macetes.scm:1511 recorded this on 2026-08-02 and the warrant went on
;; saying MACHINE-PROVEN for six weeks.
;; `informal' is the honest tier: a rigorous mechanized argument was written and
;; is on disk, which outranks a recited derivation, and it is not `proof', which
;; asserts that a machine has checked it.  Two further obstacles to simply
;; reviving the file: it calls `set-proof-state-focus!' directly five times (the
;; grep-gate requires that to be empty outside driver-kit.scm, and its page would
;; not replay), and it top-level-defines S, T, F, V, Y, Z -- six single capitals,
;; the case-fold danger zone.  Note also that the bill quoted below is four
;; supports, all still asserted, so a revived file would not read `modulo 0'.
;;; open-preimage-implies-continuous: the converse -- if every open set pulls
;;; back to an open set, the map is continuous.

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

;;; continuous-implies-closed-preimage: a continuous map pulls closed sets
;;; back to closed sets -- Prop 3.15, (1) => (2).

;;; closed-preimage-implies-continuous: the converse -- Prop 3.15, (2) => (1).

;;; Notation -- read by wff->english / the proof reader (operators.scm).
(notation! 'IS-CLOSED             'kind 'predicate 'arity 2 'english "$2 is closed in $1")
