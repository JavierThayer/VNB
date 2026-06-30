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

;;; ball-membership: y in BALL(s,x,r) iff y in PTS(s) and DIST(s)(x,y) < r.
;;; Direct from SEP membership; recorded so proofs can rewrite by name.
(support 'ball-membership
  '(FORALL s
     (FORALL x
       (FORALL r
         (FORALL y
           (IFF (IN y (BALL s x r))
                (AND (IN y (PTS s))
                     (AND (<= ((DIST s) x y) r)
                          (NOT (= ((DIST s) x y) r))))))))))
(warrant! 'ball-membership 'proof
  "BALL(s,x,r) is the def-functoid SEP(y in PTS(s) | d(x,y)<=r and d(x,y)!=r); the iff is just SEP-membership after unfolding BALL.  Definitional.")

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
(support 'ball-mem-from-le
  '(FORALL s
     (IMPLIES (IS-METRIC-SPACE s)
       (FORALL x
         (FORALL y
           (FORALL d
             (FORALL r
               (IMPLIES (AND (IN y (PTS s))
                        (AND (IN d RR)
                        (AND (IN r RR)
                        (AND (<= ((DIST s) x y) d)
                             (< d r)))))
                 (IN y (BALL s x r))))))))))
(warrant! 'ball-mem-from-le 'proof
  "d(x,y) <= d and d <= r (from d < r) give d(x,y) <= r by rr-leq-transitive. And d(x,y) = r would give r <= d (substituting into d(x,y) <= d), contradicting d < r by rr-leq-antisymmetric; so d(x,y) != r. With y in PTS(s), ball-membership yields y in BALL(s,x,r).")

;;; ball-is-set: BALL(s,x,r) in SET whenever s is a metric space.
;;; Derivable from SEP sethood + PTS(s) in SET (carrier typing of
;;; IS-METRIC-SPACE).  Kept as a named macete so BALL-using proofs don't
;;; re-derive sethood at every use; not a per-operator closure proliferation.
(support 'ball-is-set
  '(FORALL s
     (IMPLIES (IS-METRIC-SPACE s)
       (FORALL x
         (FORALL r
           (IN (BALL s x r) SET))))))
(warrant! 'ball-is-set 'proof
  "BALL(s,x,r) is a SEP over PTS(s) (def-functoid); PTS(s) is a set (carrier typing of IS-METRIC-SPACE); a SEP over a set is a set (kernel sep-sethood).")

;;; ball-center-in: x is in its own r-ball when r > 0.
;;; Uses metric-self-zero: DIST(s)(x,x) = 0 < r.
(support 'ball-center-in
  '(FORALL s
     (IMPLIES (IS-METRIC-SPACE s)
       (FORALL x
         (IMPLIES (IN x (PTS s))
           (FORALL r
             (IMPLIES (AND (IN r RR) (<= 0 r) (NOT (= 0 r)))
               (IN x (BALL s x r)))))))))
(warrant! 'ball-center-in 'proof
  "metric-self-zero gives d(s)(x,x)=0, so 0<=r and 0!=r (r>0) put x into the SEP; ball-membership then gives x in BALL(s,x,r).")

;;; ball-2r-triangle: two points in the same r-ball are within 2r of each
;;; other.  The workhorse for arguments that pigeonhole sequence terms
;;; through a finite cover of r-balls -- once two terms land in the same
;;; ball, the 2r bound supplies the Cauchy estimate.
;;;
;;; Derivable from metric-triangle + metric-sym; left as an axiom during
;;; the library-build phase per [[feedback-library-axioms-fine]].
(support 'ball-2r-triangle
  '(FORALL s
     (IMPLIES (IS-METRIC-SPACE s)
       (FORALL x
         (IMPLIES (IN x (PTS s))
           (FORALL r
             (IMPLIES (AND (IN r RR) (<= 0 r) (NOT (= 0 r)))
               (FORALL y
                 (IMPLIES (IN y (BALL s x r))
                   (FORALL z
                     (IMPLIES (IN z (BALL s x r))
                       (AND (<= ((DIST s) y z) (+ r r))
                            (NOT (= ((DIST s) y z) (+ r r)))))))))))))))
(warrant! 'ball-2r-triangle 'proof
  "metric-triangle: d(y,z) <= d(y,x)+d(x,z).  Each of d(y,x)=d(x,y) (metric-sym) and d(x,z) is < r by ball-membership, so d(y,z) < r+r.")

;;; -----------------------------------------------------------------------
;;; IS-R-NET(s, F, A, r) -- F is an r-net for A in metric space s.
;;;
;;; Every point of A is within distance < r of some point of F.  The
;;; centers F need not lie inside A; in classical analysis r-nets for a
;;; subset A often have centers outside A (e.g. centers in the closure).
;;; For our use A = PTS(s) and F lives inside PTS(s) by the typing of DIST(s).

;; def-predicate (not a raw theory-add-axiom!) so IS-R-NET registers in
;; `theory-definitions' -> DEFINITIONS.md -> the browser Definitions page, and
;; is stamped `definitional' at source (the macete name is the predicate name,
;; IS-R-NET; cf. IS-COMPACT in compactness.scm).
(def-predicate 'IS-R-NET '(s F A r)
  '(FORALL p
     (IMPLIES (IN p A)
       (FORSOME c
         (AND (IN c F)
              (AND (<= ((DIST s) c p) r)
                   (NOT (= ((DIST s) c p) r))))))))

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
