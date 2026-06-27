;;; compactness.scm -- compactness of a metric space and the four-way
;;; characterization (calculus.pdf Prop 3.12).  Supplies the missing
;;; vocabulary (IS-COMPACT, IS-OPEN-COVER, CLUSTER-POINT, HAS-FIP) and states
;;; the characterization as warranted supports (library phase); the proof
;;; directions are the stress test in stress-tests/compact-tb-stress.scm.
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

;;; ----- Prop 3.12: the four-way characterization (warranted ASSERTIONS) -----
;;; These equivalences are headline results, not PSS plumbing, so each is a
;;; warranted assertion (matchable macete, not a Proof Support).  See
;;; [[pss-central-role]]: PSS = curated reusable minutiae a proof backchains;
;;; a Prop-3.12 equivalence is a destination you prove, not a fast lemma.

;;; (1) <=> (4):  compact  iff  totally bounded and complete.
(theory-add-axiom! *current-theory* 'compact-iff-tb-complete
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
(theory-add-axiom! *current-theory* 'compact-iff-cluster-point
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
(theory-add-axiom! *current-theory* 'compact-iff-fip
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

;;; The r-ball cover of s: the family of all open r-balls { B(c,r) : c in X(s) },
;;; as the image of X(s) under  c |-> BALL(s,c,r).  The lambda variable is `c'
;;; (centre), NOT `x': the carrier accessor X folds to x, and the cover's domain
;;; (X s) sits next to the lambda -- keeping them disjoint avoids the carrier/
;;; point name clash.  [[feedback_no_case_variant_binders]]
(def-functoid 'BALL-COVER '(s r)
  '(IMAGE (VNB-LAMBDA c (BALL s c r)) (X s)))

;;; Lemma A: for r > 0 the r-ball cover is an open cover of s.
;;; (r-condition matches the TOTALLY-BOUNDED def verbatim: r in RR, 0 <= r, r /= 0.)
(support 'ball-cover-is-open-cover
  '(FORALL s (IMPLIES (IS-METRIC-SPACE s)
     (FORALL r (IMPLIES (AND (IN r RR) (AND (<= 0 r) (NOT (= 0 r))))
       (IS-OPEN-COVER s (BALL-COVER s r)))))))
(warrant! 'ball-cover-is-open-cover 'well-known
  "The r-ball cover { B(x,r) : x in X(s) } is an open cover for r > 0: each
   ball is open (ball-is-open), and the union is all of X(s) because every
   point x lies in its own ball B(x,r) (d(x,x)=0 < r).")

;;; ----- centre extraction, made explicit via global choice -----
;;;
;;; The centre-extraction step ("a finite r-ball cover yields a finite r-net")
;;; is exactly where a choice of centre-per-ball is needed: a member of the ball
;;; cover is stored as the SET B(c,r), with the centre c thrown away, and the
;;; map x |-> B(x,r) need not be injective, so "the centre of a ball" is not a
;;; function without choice.  We make the choice EXPLICIT with the global
;;; Hilbert epsilon (CHOICE, theory.scm): for a ball B, CENTRES(s,B,r) is the
;;; (set of) centres of B, and CHOICE(CENTRES s B r) picks one -- defined exactly
;;; when that set is inhabited (the iota/epsilon definedness proviso), which it
;;; is for a ball drawn from the cover.  CENTRE-SET(s,r,F) is then the image of
;;; F under  B |-> CHOICE(CENTRES s B r)  -- a bona fide function (VNB-LAMBDA),
;;; so "choose a centre per ball" is a one-liner, not a hand-wave.

;;; CENTRES(s,B,r): the centres of the ball B at radius r (a SEP-subset of X(s)).
(def-functoid 'CENTRES '(s B r) '(SEP c (X s) (= (BALL s c r) B)))

;;; CENTRE-SET(s,r,F): the chosen centres of the balls in F -- the image of F
;;; under the choice function  B |-> CHOICE(CENTRES s B r).
(def-functoid 'CENTRE-SET '(s r F)
  '(IMAGE (VNB-LAMBDA B (CHOICE (CENTRES s B r))) F))

;;; Directional slices of the CENTRES SEP-membership equivalence (definitional:
;;; c in {c in X(s) : B(c,r)=B} iff c in X(s) and B(c,r)=B).
(support 'centres-mem-build
  '(FORALL s (FORALL B (FORALL r (FORALL c
     (IMPLIES (IN c (X s)) (IMPLIES (= (BALL s c r) B) (IN c (CENTRES s B r)))))))))
(support 'centres-in-carrier
  '(FORALL s (FORALL B (FORALL r (FORALL c
     (IMPLIES (IN c (CENTRES s B r)) (IN c (X s))))))))
(support 'centres-ball-eq
  '(FORALL s (FORALL B (FORALL r (FORALL c
     (IMPLIES (IN c (CENTRES s B r)) (= (BALL s c r) B)))))))
(warrant! 'centres-mem-build 'well-known "SEP-membership of CENTRES (definitional).")
(warrant! 'centres-in-carrier 'well-known "CENTRES(s,B,r) is a SEP-subset of X(s) (definitional).")
(warrant! 'centres-ball-eq 'well-known "Each centre c of B satisfies B(c,r)=B (definitional).")

;;; A member of the ball cover is a ball B(c,r) about some centre c in X(s)
;;; (forward direction of IMAGE-membership for BALL-COVER).
(support 'ball-cover-mem-fwd
  '(FORALL s (FORALL r (FORALL U
     (IMPLIES (IN U (BALL-COVER s r))
              (FORSOME c (AND (IN c (X s)) (= (BALL s c r) U))))))))
(warrant! 'ball-cover-mem-fwd 'well-known
  "BALL-COVER(s,r) = { B(x,r) : x in X(s) }, so each member is a ball about a
   centre in X(s) (image-membership of BALL-COVER; definitional).")

;;; The chosen centre of a ball U in F lies in CENTRE-SET(s,r,F)
;;; (image-membership of CENTRE-SET + lambda-beta; witness B := U).
(support 'centre-set-contains-choice
  '(FORALL s (FORALL r (FORALL F (FORALL U
     (IMPLIES (IN U F) (IN (CHOICE (CENTRES s U r)) (CENTRE-SET s r F))))))))
(warrant! 'centre-set-contains-choice 'well-known
  "CHOICE(CENTRES s U r) = (B |-> CHOICE(CENTRES s B r))(U) is in the image of F
   when U in F (image-membership + beta; definitional).")

;;; CENTRE-SET of a finite family is finite (image of a finite set is finite).
(support 'centre-set-finite
  '(FORALL s (FORALL r (FORALL F
     (IMPLIES (IN (CARD F) NN) (IN (CARD (CENTRE-SET s r F)) NN))))))
(warrant! 'centre-set-finite 'well-known
  "The image of a finite set under a function is finite: |CENTRE-SET(s,r,F)| <=
   |F|, so it is in NN when |F| is.")

;;; The members of an open cover cover X(s): every point lies in some member.
(support 'open-cover-covers-point
  '(FORALL s (FORALL F (IMPLIES (IS-OPEN-COVER s F)
     (FORALL p (IMPLIES (IN p (X s))
       (FORSOME U (AND (IN U F) (IN p U)))))))))
(warrant! 'open-cover-covers-point 'well-known
  "An open cover has union X(s) (IS-OPEN-COVER's third conjunct), so every point
   p in X(s) lies in some member U of the cover (BIG-UNION membership).")

;;; Forward direction of subset-def.
(support 'subset-mem-fwd
  '(FORALL A (FORALL B (FORALL x
     (IMPLIES (SUBSET A B) (IMPLIES (IN x A) (IN x B)))))))
(warrant! 'subset-mem-fwd 'well-known "Forward direction of subset-def (definitional).")

;;; Ball membership in terms of the defining ball: if p in U and U = B(s,c,r)
;;; then d(c,p) < r  (= the two conjuncts <= and /=).  Curried for forward use.
(support 'ball-point-le
  '(FORALL s (FORALL c (FORALL r (FORALL W (FORALL p
     (IMPLIES (IN p W) (IMPLIES (= (BALL s c r) W)
              (<= ((D s) c p) r)))))))))
(support 'ball-point-ne
  '(FORALL s (FORALL c (FORALL r (FORALL W (FORALL p
     (IMPLIES (IN p W) (IMPLIES (= (BALL s c r) W)
              (NOT (= ((D s) c p) r))))))))))
(warrant! 'ball-point-le 'well-known
  "If p in W and W = B(s,c,r) then d(c,p) <= r (ball-membership, modulo the eq).")
(warrant! 'ball-point-ne 'well-known
  "If p in W and W = B(s,c,r) then d(c,p) /= r (ball-membership, modulo the eq).")

;;; The chosen centre of a cover ball is genuinely a centre of it -- the
;;; soundness of the epsilon choice (defined because the centre-set is
;;; inhabited).  MACHINE-PROVEN in calculus/finite-ball-subcover-proof.scm.
(support 'chosen-centre-is-centre
  '(FORALL s (FORALL r (FORALL U
     (IMPLIES (IN U (BALL-COVER s r))
       (AND (IN (CHOICE (CENTRES s U r)) (X s))
            (= (BALL s (CHOICE (CENTRES s U r)) r) U)))))))
(warrant! 'chosen-centre-is-centre 'proof
  "CHOICE(CENTRES s U r) in X(s) and B(CHOICE(CENTRES s U r),r) = U: U in the
   ball cover makes CENTRES(s,U,r) inhabited, so the epsilon choice lands in it
   (choice-axiom) and CENTRES-membership gives both conjuncts.  MACHINE-PROVEN
   in calculus/finite-ball-subcover-proof.scm.")

;;; Lemma B: a finite r-ball subcover yields a finite r-net -- its centres.
;;; MACHINE-PROVEN (the centre extraction above made the choice explicit).
(support 'finite-ball-subcover-r-net
  '(FORALL s (IMPLIES (IS-METRIC-SPACE s)
     (FORALL r (IMPLIES (AND (IN r RR) (AND (<= 0 r) (NOT (= 0 r))))
       (IMPLIES (FORSOME F (AND (SUBSET F (BALL-COVER s r))
                           (AND (IN (CARD F) NN) (IS-OPEN-COVER s F))))
         (FORSOME N (AND (IN (CARD N) NN) (IS-R-NET s N (X s) r)))))))))
(warrant! 'finite-ball-subcover-r-net 'proof
  "A finite subcover F of the r-ball cover yields a finite r-net N = CENTRE-SET
   (s,r,F), the chosen centres of the balls in F: |N| <= |F| is finite, and for
   p in X(s) some U in F contains p (open-cover-covers-point), U = B(c,r) with
   c = CHOICE(CENTRES s U r) a genuine centre (chosen-centre-is-centre), so c in
   N with d(c,p) < r.  MACHINE-PROVEN in calculus/finite-ball-subcover-proof.scm,
   modulo the explicit-construction membership lemmas above; the centre choice
   is the global epsilon, no longer a hand-wave.")

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
(warrant! 'compact-implies-complete 'proof
  "Compact => complete (calculus.pdf Prop 3.12).  A Cauchy sequence in a compact
   space has a cluster point (condition (3)); a Cauchy sequence with a cluster
   point converges to it.  Half of (1)=>(4).  MACHINE-PROVEN in
   calculus/compact-complete-proof.scm (installed there as `compact-complete',
   modulo the three asserted lemmas compact-seq-has-cluster +
   cauchy-cluster-converges + cauchy-seq-is-fun); kept here as an asserted PSS
   citation, the proof run offline.")

;;; ----- the two lemmas that close compact => complete -----

;;; Lemma C (forward slice of Prop 3.12 (1)=>(3)): in a compact space every
;;; sequence f : NN -> X(s) has a cluster point.  Directly backchainable
;;; (relation-/FORSOME-headed conclusion), unlike the IFF compact-iff-cluster-
;;; point which a goal cannot match against.  AND-shaped antecedent so bc*
;;; splits it into the two conjuncts (both land in context during the proof).
(support 'compact-seq-has-cluster
  '(FORALL s (FORALL f
     (IMPLIES (AND (IS-COMPACT s) (IN f (FUN NN (X s))))
              (FORSOME x (CLUSTER-POINT s f x))))))
(warrant! 'compact-seq-has-cluster 'reference
  "calculus.pdf Prop 3.12 (1)=>(3): a compact metric space is sequentially
   compact -- every sequence has a cluster point (a convergent subsequence).
   The forward, directly-backchainable slice of compact-iff-cluster-point.")

;;; Lemma D (the analytic keystone): a Cauchy sequence with a cluster point
;;; CONVERGES (to that cluster point).  AND-shaped antecedent + existential
;;; cluster hypothesis, conclusion the folded CONVERGES so bc* matches the goal.
(support 'cauchy-cluster-converges
  '(FORALL s (FORALL f
     (IMPLIES (AND (IS-CAUCHY-SEQ s f) (FORSOME x (CLUSTER-POINT s f x)))
              (CONVERGES s f)))))
(warrant! 'cauchy-cluster-converges 'well-known
  "A Cauchy sequence with a cluster point x converges to x.  Given eps > 0:
   Cauchyness gives N with d(f m, f n) <= eps/2 for m,n >= N; x is a cluster
   point, so some n >= N has d(f n, x) < eps/2; then for every m >= N,
   d(f m, x) <= d(f m, f n) + d(f n, x) < eps.  Hence f converges to x.  This
   is the standard fact powering compact => complete (calculus.pdf Prop 3.12).")

;;; ----- Plain-English gloss (PSS review 2026-06-26): 3+-line statement -----
(gloss! 'finite-ball-subcover-r-net
  "For a metric space s and radius r>0: if the r-ball cover of s has a finite subcover, then s has a finite r-net (a finite set N of points such that every point of s is within r of some member of N).  Extracting a net from a finite subcover -- its centres.")
