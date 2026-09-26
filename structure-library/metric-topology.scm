;;; metric-topology.scm -- balls, r-nets, total-boundedness.
;;;
;;; Builds on metric-space.scm.  Adds basic point-set vocabulary for
;;; arguments about covers and approximation:
;;;
;;;   BALL(s, x, r)        open ball: { y in PTS(s) : DIST(s)(x,y) < r }
;;;   IS-R-NET(s, F, A, r) F approximates A to within r in s
;;;   TOTALLY-BOUNDED(s)   for every positive r, PTS(s) has a finite r-net
;;;
;;; "r > 0" is spelled (AND (IN r RR) (<= 0 r) (NOT (= 0 r))), matching
;;; the eps > 0 idiom already in cc-complete (complex.scm).  Strict <
;;; is similarly spelled (AND (<= a b) (NOT (= a b))) since VNB has
;;; <= as primitive but no strict <.  Both idioms are candidates for
;;; a future POS / < cleanup pass; they appear throughout the analytic
;;; vocabulary and the inconsistency would be jarring if introduced here
;;; piecemeal.
;;;
;;; Centers-only formulation: F is a set of points (centers) in PTS(s),
;;; not a set of balls.  The set-of-balls view is one functoid away
;;; ({ BALL(s,c,r) : c in F }), but pigeonhole-on-centers is what the
;;; standard metric-space arguments actually use.

;;; -----------------------------------------------------------------------
;;; CONVENTION: functoids over a structure `s' are deliberately UNGUARDED.
;;;
;;; BALL(s,c,r), BALL-COVER(s,r) (compactness.scm), BDD-METRIC(s)
;;; (bounded-metric.scm), CAUCHY-SETOID(M) (metric-completion.scm) and the
;;; like are defined for ANY `s', with no IS-METRIC-SPACE(s) precondition in
;;; the definition body.  `s' could be a bongo for which PTS(s)/DIST(s) happen to
;;; denote something.  This is intentional and harmless:
;;;
;;;   1. The logic is untyped and partial, so the term is always well-formed.
;;;      The body uses whatever DIST(s) denotes; no metric law (symmetry,
;;;      triangle, ...) is INVOKED in the definition, so none is NEEDED.  If
;;;      DIST(s) is undefined, undefinedness propagates (t=t is definedness) and
;;;      you get the empty set / an undefined term -- never a false theorem.
;;;
;;;   2. A definition is a conservative abbreviation, not an assertion:
;;;      BALL(s,c,r) := {...} is just (FORALL s c r. BALL(s,c,r) = {...}),
;;;      true by fiat.  It introduces no new theorem in the old vocabulary,
;;;      so it cannot make IS-METRIC-SPACE(bongo) -- or anything false --
;;;      provable.  Garbage in, garbage out; "garbage out" is never a lie.
;;;
;;;   3. The mathematical content lives in the GUARDED theorems.  Every
;;;      substantive support (BALL-COVER is an open cover, BDD-METRIC(s) is a
;;;      metric space, CAUCHY-SETOID(M) is a setoid) carries IS-METRIC-SPACE
;;;      as a hypothesis; the IS-OPEN-COVER / IS-COMPACT predicates fold it in
;;;      as a conjunct.  That is where the bongo is excluded.  Leaving the
;;;      definitions naked avoids an IF-IS-METRIC-SPACE-THEN-ELSE wart in
;;;      every body and the duplicated guard in every downstream proof.
;;;
;;;   So the only purely-definitional supports below (ball-membership,
;;;   bdd-metric-carrier, centres-*, ball-point-*, subset-mem-fwd) are
;;;   CORRECTLY unguarded -- they are SEP/slot read-offs that hold for any s.
;;;   The one discipline that actually bites: a substantive theorem must not
;;;   FORGET its IS-METRIC-SPACE hypothesis -- but that is a theorem-statement
;;;   bug caught by the proof failing, not something a definition can launder.
;;;
;;; -----------------------------------------------------------------------
;;; BALL(s, c, r) -- the open r-ball around centre c in metric space s.
;;;
;;; The centre parameter is `c', NOT `x': the carrier accessor is X, and the
;;; MIT reader case-folds, so X and x are the SAME symbol.  A param named `x'
;;; would therefore be a PATTERN VARIABLE that captures the carrier (x s) in the
;;; body -- unfolding BALL(s, t, r) at any centre t would rewrite (PTS s) to
;;; (t s).  It only ever worked because every call site applied BALL at the
;;; literal variable `x' (the substitution was the identity).  Naming the centre
;;; `c' (as `centres' below already does) keeps it disjoint from the carrier.
;;; [[feedback-no-case-variant-binders]]

(def-functoid 'BALL '(s c r)
  '(SEP y (PTS s)
        (AND (<= ((DIST s) c y) r)
             (NOT (= ((DIST s) c y) r)))))

;;; CLOSED-BALL(s, c, r) -- the closed r-ball around the centre c in s.
;;;
;;; Deliberately UNGUARDED in s, c and r, exactly as BALL is, and for the reason
;;; metric-topology.scm's own CONVENTION note gives: a definition is a conservative
;;; abbreviation, the substantive facts below carry IS-METRIC-SPACE.  The centre
;;; parameter is `c', never `x' (the case-fold trap the BALL comment records); the
;;; SEP variable is `y', as BALL's is.
;;;
;;; The body is BALL's with the strict conjunct dropped: BALL(s,c,r) asks
;;; d(c,y) <= r AND d(c,y) /= r, CLOSED-BALL asks only d(c,y) <= r.  At r < 0 the
;;; set is empty and every law still holds (theorem-library/metric-closure-laws.scm) (closed-ball-is-closed is guarded
;;; on r in RR, not on POS-RR r); on the empty space it is EMPTY-SET.

(def-functoid 'CLOSED-BALL '(s c r)
  '(SEP y (PTS s) (<= ((DIST s) c y) r)))

;;; ball-membership: y in BALL(s,x,r) iff y in PTS(s) and DIST(s)(x,y) < r.
;;; Direct from SEP membership; recorded so proofs can rewrite by name.

;;; (No `ball-subset-carrier' axiom: BALL(s,x,r) subset PTS(s) is a SEP over
;;; PTS(s), so it falls straight out of the kernel separation rule sep-me --
;;; a per-operator support for it would just reify the generic SEP z A p
;;; subset A.  Prove inline when needed: (mac 'BALL) unfolds the functoid to
;;; SEP in the goal, (mac 'subset-def)(di), then sep-me supplies IN z (PTS s).
;;; [[feedback-no-closure-axiom-proliferation]])

;;; ball-mem-from-le: a point at distance <= d from the centre, with d < r,
;;; lies in the open r-ball.  This packages the one piece of order friction
;;; that the open-preimage argument keeps hitting: V's openness supplies a
;;; STRICT eps-ball, but continuity only delivers a NON-strict bound
;;; d(t)(f y, f z) <= d.  Halving eps (rr-pos-halvable) gives a d < eps, and
;;; this lemma turns the non-strict bound at radius d into strict membership
;;; at radius r = eps.  Stated with d, r in RR so the order chain is typed.
;;; RETIRED 2026-09-17 (guarded, then proven): ball-mem-from-le --
;;; theorem-library/rake-balls.scm.  The statement gained `x in PTS(s)' after
;;; `FORALL x': without it nothing certifies DIST(s)(x,y) as a real
;;; (metric-dist-real wants BOTH points in PTS(s)), so the two transitivity
;;; steps of its warrant could not run.  Nothing cited it.

;;; RETIRED 2026-09-17 (proven): ball-membership, ball-is-set, ball-center-in,
;;; ball-2r-triangle -- theorem-library/rake-balls.scm, all modulo 0 (the SEP
;;; membership by the functoid-unfold recipe, `ball-sep-unfold'; sethood from SEP
;;; sethood and the carrier typing; the two metric facts from metric-laws).

;;; ball-2r-triangle: two points in the same r-ball are within 2r of each
;;; other.  The workhorse for arguments that pigeonhole sequence terms
;;; through a finite cover of r-balls -- once two terms land in the same
;;; ball, the 2r bound supplies the Cauchy estimate.
;;;
;;; Derivable from metric-triangle + metric-sym; left as an axiom during
;;; the library-build phase per [[feedback-library-axioms-fine]].

;;; -----------------------------------------------------------------------
;;; IS-R-NET(s, F, A, r) -- F is an r-net for A in metric space s.
;;;
;;; F is a subclass of A, and every point of A is within distance < r of some
;;; point of F.  The centres are required to lie in A itself; for the one use
;;; the library makes of the predicate, TOTALLY-BOUNDED below, A is PTS(s), so
;;; the centres are points of the space.
;;;
;;; THE SUBSET CONJUNCT (added 2026-09-19, the user's decision).  Until that
;;; date the definition consisted of the quantified clause alone, the centres
;;; were unconstrained, and the comment printed here claimed that "F lives
;;; inside PTS(s) by the typing of DIST(s)".  That claim was FALSE, and the
;;; defect it hid is recorded here because the two theorems it invalidated
;;; stood for seven weeks.
;;;
;;;   * What the typing of DIST(s) gives is weaker than the claim.  DIST(s)
;;;     is a member of FUN(CARTESIAN(PTS s, PTS s), RR), so a member c of F
;;;     for which the term ((DIST s) c p) is asserted to be a real number is
;;;     thereby a point of s -- that implication is the theorem
;;;     `dist-le-implies-in-carrier' (theorem-library/rake-tb-leaves.scm).
;;;     It constrains only those members of F that are actually USED as
;;;     centres by the quantified clause.  It says nothing whatever about the
;;;     remaining members, and in particular it does not make F a SET: the
;;;     universal class satisfies the old definition in any model in which
;;;     some point of A is at distance 0 from itself.
;;;
;;;   * The consequence sat one level up, in TOTALLY-BOUNDED.  That predicate
;;;     bounds the net by `(IN (CARD F) NN)', and every axiom about CARD
;;;     (structure-library/cardinality.scm: card-in-ord, card-insert,
;;;     card-finite-bij, card-union-disjoint) is guarded on `(IN A SET)'.  For
;;;     a proper class F the term CARD(F) is therefore unconstrained, and
;;;     `(IN (CARD F) NN)' is satisfiable without F being finite in any sense.
;;;
;;;   * The counter-model.  Let s be an uncountable discrete metric space
;;;     (d(x,y) = 1 for x /= y) in a model in which CARD of the universal
;;;     class is 3, and let F be the universal class.  Under the old
;;;     definition IS-R-NET(s, F, PTS(s), r) holds for every r > 0, since each
;;;     p is at distance 0 < r from itself and p belongs to F; and
;;;     (IN (CARD F) NN) holds by the choice of model.  So TOTALLY-BOUNDED(s)
;;;     held of an uncountable discrete space, at which the supports
;;;     `tb-rad-ball-cover' (theorem-library/cauchy-subsequence.scm) and
;;;     `tb-scale-dense-seq' (structure-library/separable.scm) are both FALSE:
;;;     at radius 1/2 every ball is a singleton, so no finite set of balls
;;;     covers PTS(s) and no sequence comes within 1/2 of every point.  The
;;;     defect was found on 2026-09-19 by the agent that attempted those two
;;;     supports (scratchpad/triage/RAKE-BATCH6-REPORTS.md, entry 6-P).
;;;
;;;   * The decision (the user's, 2026-09-19) puts the repair on IS-R-NET
;;;     rather than on TOTALLY-BOUNDED, and states it as `SUBSET F A' rather
;;;     than as sethood of F.  Two consequences.  (i) F subseteq A is the
;;;     ordinary textbook definition of an r-net, and the generality the old
;;;     header reserved -- centres drawn from outside A, as from the closure of
;;;     A -- is used nowhere in the tree.  (ii) Sethood of the net is now a
;;;     consequence and not a separate hypothesis: at A = PTS(s),
;;;     IS-METRIC-SPACE(s) carries `(IN (PTS s) SET)' as a typing conjunct
;;;     (surfaced as `rkt-pts-in-set!',
;;;     theorem-library/rake-analysis-typing.scm), and `subclass-of-set-is-set'
;;;     (theorem-library/subset-lemmas.scm) turns the subset clause into
;;;     `(IN F SET)', which is what makes `(IN (CARD F) NN)' in TOTALLY-BOUNDED
;;;     say what it was always meant to say.  The clause is also the property
;;;     every construction in the tree already delivers: the one prover of an
;;;     r-net, `finite-ball-subcover-r-net'
;;;     (calculus/finite-ball-subcover-proof.scm), builds its net as
;;;     CENTRE-SET(s, r, F), an IMAGE of chosen centres each of which
;;;     `chosen-centre-is-centre' places in PTS(s).
;;;
;;; The clause strengthens the predicate.  Every support that holds IS-R-NET or
;;; TOTALLY-BOUNDED as a HYPOTHESIS is therefore weakened, hence still true;
;;; every statement that asserts one as a CONCLUSION owes the new conjunct.

;; def-predicate (not a raw theory-add-axiom!) so IS-R-NET registers in
;; `theory-definitions' -> DEFINITIONS.md -> the browser Definitions page, and
;; is stamped `definitional' at source (the macete name is the predicate name,
;; IS-R-NET; cf. IS-COMPACT in compactness.scm).
(def-predicate 'IS-R-NET '(s F A r)
  '(AND (SUBSET F A)
        (FORALL p
          (IMPLIES (IN p A)
            (FORSOME c
              (AND (IN c F)
                   (AND (<= ((DIST s) c p) r)
                        (NOT (= ((DIST s) c p) r)))))))))

;;; -----------------------------------------------------------------------
;;; TOTALLY-BOUNDED(s) -- every positive r admits a finite r-net for PTS(s).
;;;
;;; Includes IS-METRIC-SPACE(s) in the unfolding; total-boundedness is
;;; only meaningful on a metric space.

;; def-predicate so TOTALLY-BOUNDED is indexed in DEFINITIONS.md / the browser
;; and stamped `definitional' at source (macete name = predicate name).
(def-predicate 'TOTALLY-BOUNDED '(s)
  '(AND (IS-METRIC-SPACE s)
        (FORALL r
          ;; NB: AND is strictly binary -- the old 3-arg
          ;; (AND (IN r RR) (<= 0 r) (NOT (= 0 r))) silently dropped the
          ;; r/=0 conjunct (make-wff arity), so TB wrongly allowed r=0.
          ;; Nested binary form keeps all three: r in RR, 0<=r, r/=0.
          (IMPLIES (AND (IN r RR) (AND (<= 0 r) (NOT (= 0 r))))
            (FORSOME F
              (AND (IN (CARD F) NN)
                   (IS-R-NET s F (PTS s) r)))))))

;;; -----------------------------------------------------------------------
;;; Notation -- the ENGLISH of these predicates, declared beside their
;;; definitions and read by wff->english / the proof reader (operators.scm).
;;; A def-predicate's reading cannot be derived the way a structure's noun can
;;; (noun vs adjective: IS-COMPLETE wants "s is complete", not "s is a complete"),
;;; so it is written here, once, next to what it means.
(notation! 'TOTALLY-BOUNDED 'kind 'predicate 'arity 1
           'english "$1 is totally bounded")
(notation! 'IS-R-NET 'kind 'predicate 'arity 4
           'english "$2 is an $4-net for $3 in $1")
