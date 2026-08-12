;;; compact-tb-stress.scm -- STRESS TEST of the compactness characterization
;;; (calculus.pdf Prop 3.12), per the "proof requests are PSS probes" lens:
;;; the deliverable is the surfaced obstacles, not a QED.  Run with
;;;   ./prover -i stress-tests/compact-tb-stress.scm
;;;
;;; KIND: machinery-gap probe (names the missing reusable lemmas).
;;; PSS SUPPORTS LEANED ON (see theorem-library/pss-topics.scm):
;;;   compactness vocab    IS-COMPACT, IS-OPEN-COVER, TOTALLY-BOUNDED, IS-R-NET
;;;                        (topology bucket; def-predicates, metric-topology.scm)
;;;   ball-cover-is-open-cover    the ball family is an open cover  (topology)
;;;   finite-ball-subcover-r-net  finite subcover yields a finite r-net
;;;                               (now PROVEN, modulo chosen-centre-is-centre)
;;;   chosen-centre-is-centre     the epsilon centre pick is a genuine centre
;;; OUTCOME: closed the gap -> compact-tb (proven theorem, compact-tb-proof.scm).
;;;
;;; Target direction: (1) => (4) half,  compact => totally bounded.
;;; The driven prefix below reaches the heart of the argument cleanly; the
;;; remaining step is the genuine machinery gap (recorded at the bottom).

;;; ----- the proof prefix that WORKS -----
(sp (make-wff '(FORALL s (IMPLIES (IS-COMPACT s) (TOTALLY-BOUNDED s)))))
(di) (di)                       ; peel forall s; move IS-COMPACT(s) to a hyp
;; NB: ONE (di) peels only the forall here; the trailing IMPLIES needs a
;;     SECOND (di).  Idiom: di until the goal is atomic.
(mac 'TOTALLY-BOUNDED)          ; unfold the GOAL's TOTALLY-BOUNDED.
;; NB: TOTALLY-BOUNDED and IS-R-NET are now def-predicates (metric-topology.scm),
;;     so they unfold by their OWN name -- uniform with IS-COMPACT / IS-OPEN-COVER
;;     / CLUSTER-POINT / HAS-FIP (compactness.scm), and both now appear in
;;     DEFINITIONS.md / the browser.  [OBSTACLE 1 RESOLVED: was register-constant!'d
;;     with a hand-rolled `totally-bounded-def' IFF axiom, invisible to the index.]
(di) (di)                       ; split the AND; peel r, assume r > 0.
;; Now two subgoals:
;;   [a]  is-compact(s)  =>  is-metric-space(s)
;;        -- trivial: the first conjunct of IS-COMPACT's definition.
;;        (mac-h 'IS-COMPACT <hyp>) then take the conjunct.
;;   [b]  ..., r in rr, 0 < r  =>  forsome F. card(F) in NN and
;;                                  is-r-net(s, F, X(s), r)
;;        -- THE crux (see below).

;;; ----- THE OBSTACLE (the point of the stress test) -----
;;;
;;; Subgoal [b] is the mathematical heart and needs three pieces of machinery
;;; that the library does NOT yet have as reusable lemmas:
;;;
;;;  (i)  COVER CONSTRUCTION.  Form the open cover  C = { B(x,r) : x in X(s) }
;;;       as a SET -- the image  IMAGE(X(s), \x. BALL(s,x,r)).  Prove
;;;       IS-OPEN-COVER(s, C):  every member is open (ball-is-open, EXISTS),
;;;       and the union is X(s) because every point lies in its own ball
;;;       (d(x,x)=0 < r).  Missing: a packaged "ball cover" lemma.
;;;
;;;  (ii) INSTANTIATE compactness at C to get a finite subcover F (a finite
;;;       SET OF BALLS that still covers).  Mechanical once (i) is in hand
;;;       (mac-h 'IS-COMPACT, inst at C).
;;;
;;;  (iii) CENTRE EXTRACTION (the real gap).  IS-R-NET is phrased in terms of
;;;       CENTRES, but a finite subcover is a finite set of BALLS.  Recovering
;;;       a finite set of centres from a finite family of balls needs either a
;;;       choice function (ball |-> its centre) or a centre-remembering
;;;       representation of the cover.  No reusable lemma does this.  This is
;;;       the missing keystone -- call it `finite-ball-cover-gives-r-net'.
;;;
;;; Recommended fix (next build): add, as warranted PSS supports,
;;;   ball-cover-is-open-cover   : IS-OPEN-COVER(s, IMAGE(X(s), \x.BALL(s,x,r)))
;;;   finite-ball-cover-r-net    : a finite subcover of the ball cover yields a
;;;                                finite r-net (centres of the chosen balls).
;;; With those two, compact => totally-bounded is a short backchain.  The
;;; converse half (4)=>(1) needs the diagonal / rapidly-Cauchy-subsequence
;;; argument -- cauchy-rapid-subsequence (metric-completeness.scm) already
;;; exists, so that direction is better supplied.
;;;
;;; STATUS: vocabulary (IS-COMPACT etc.) and the Prop 3.12 equivalences are
;;; installed as warranted supports (compactness.scm); the machine proof waits
;;; on the two ball-cover lemmas above.  Left as a documented probe.
;;;
;;; UPDATE 2026-06-20 (assembly attempt with the two ball-cover lemmas built):
;;;  - BUG FOUND + FIXED: totally-bounded-def's r-condition was the 3-arg
;;;    (AND (IN r RR) (<= 0 r) (NOT (= 0 r))).  AND is strictly BINARY
;;;    (make-wff: connective arity error on 3 args), so theory-add-axiom!
;;;    stored it with the r/=0 conjunct silently DROPPED -- TB wrongly allowed
;;;    r=0.  Rewritten as nested binary (metric-topology.scm).  [Audit lead:
;;;    grep other axioms for 3-arg AND/OR similarly truncated.]
;;;  - The assembly then drives cleanly to the crux subgoal
;;;       r in rr, 0<=r, r/=0, (forall C: open-cover => finite subcover),
;;;       is-metric-space(s)  =>  forsome F. card(F) in NN and is-r-net(s,F,X(s),r)
;;;    via: (di)(di) (mac-h 'IS-COMPACT 1) (ai 1) (mac 'totally-bounded-def)
;;;         (di) (ass) (di)(di).
;;;  - WALL: (bc* 'finite-ball-subcover-r-net) does NOT fire -- its conclusion
;;;    is EXISTENTIAL (forsome N ...), and bc* matches relation-headed
;;;    conclusions, not FORSOME-headed ones.  Finishing needs FORWARD chaining:
;;;    establish forsome-subcover from compactness (inst (forall C) at
;;;    BALL-COVER(s,r); discharge open-cover by ball-cover-is-open-cover), then
;;;    ta/inst/detach! lemma B's three antecedents to land forsome-N in context
;;;    and close by (ass).  ~15-20 forward steps -> a slog, so left asserted
;;;    (compact-implies-totally-bounded) per the not-a-slog guard.
;;;  - To make it a SHORT proof later: either (i) a bc* that matches existential
;;;    conclusions, or (ii) reformulate lemma B to conclude IS-R-NET about a
;;;    NAMED centre-set functoid R-NET-OF(s,r) (non-existential), then close the
;;;    goal with (ew '(R-NET-OF s r)) + bc*.  Both are clean follow-ups.
;;;
;;; DONE 2026-06-20 via route (i): match-expr is now ALPHA-AWARE on binders
;;; (macetes.scm) -- bc* matches a FORSOME-/FORALL-headed conclusion against a
;;; goal with a differently-named bound variable.  So bc* backchains the
;;; EXISTENTIAL lemma finite-ball-subcover-r-net directly, no Skolem functoid
;;; needed.  The completed QED is calculus/compact-tb-proof.scm (installed as
;;; `compact-tb', proven modulo the two warranted ball-cover lemmas).  The
;;; alpha-aware fix is a reusable, general capability (helps mac + bc* on every
;;; quantified conclusion), not specific to this proof.

;;; -----------------------------------------------------------------------
;;; COMPANION (2026-06-22): the OTHER half of (1)=>(4), compact => COMPLETE,
;;; is now machine-proven in calculus/compact-complete-proof.scm (installed as
;;; `compact-complete'), modulo three warranted backchain-ready lemmas:
;;;   compact-seq-has-cluster  (=> slice of Prop 3.12 (1)=>(3))
;;;   cauchy-cluster-converges (the analytic keystone: Cauchy + cluster => conv)
;;;   cauchy-seq-is-fun        (typing projection of IS-CAUCHY-SEQ)
;;; STRESS-TEST FINDING: the wall was NOT a missing tactic but forward `fact':
;;; it will not detach a CONJUNCTIVE antecedent whose conjuncts are only
;;; separately in context, and it spawns sibling goals.  Pure backward bc*
;;; (stating the lemmas with relation-/FORSOME-headed conclusions) is the clean
;;; route -- 11 tactics, same style as compact-tb-proof.scm.

;;; -----------------------------------------------------------------------
;;; CENTRE EXTRACTION CLOSED (2026-06-22).  Obstacle (iii) above -- "recovering
;;; a finite set of centres from a finite family of balls needs a choice
;;; function; no reusable lemma does this" -- is now resolved by making the
;;; choice EXPLICIT with the global Hilbert epsilon:
;;;   CENTRES(s,B,r)   = { c in X(s) : B(c,r) = B }        (def-functoid)
;;;   CENTRE-SET(s,r,F)= IMAGE(B |-> CHOICE(CENTRES s B r), F)
;;; (compactness.scm).  finite-ball-subcover-r-net is then MACHINE-PROVEN in
;;; calculus/finite-ball-subcover-proof.scm (with chosen-centre-is-centre: the
;;; epsilon pick is a genuine centre, defined because the cover ball's centre
;;; set is inhabited -- the iota/epsilon definedness proviso).  So compact-tb is
;;; now proven modulo the explicit-construction membership lemmas, not the
;;; opaque centre-extraction hand-wave.  bc* GOTCHAS hit en route: it chokes on
;;; a CONJUNCTION conclusion and on a nested-application conclusion ((D s) c p);
;;; split into atomic-conclusion lemmas and/or discharge forward with `fact'.
