;;; compact-stress.scm -- STRESS TEST of the compactness characterization
;;; (calculus.pdf Prop 3.12), per the "proof requests are PSS probes" lens:
;;; the deliverable is the surfaced obstacles, not a QED.  Run with
;;;   ./prover -i calculus/compact-stress.scm
;;;
;;; Target direction: (1) => (4) half,  compact => totally bounded.
;;; The driven prefix below reaches the heart of the argument cleanly; the
;;; remaining step is the genuine machinery gap (recorded at the bottom).

;;; ----- the proof prefix that WORKS -----
(sp (make-wff '(FORALL s (IMPLIES (IS-COMPACT s) (TOTALLY-BOUNDED s)))))
(di) (di)                       ; peel forall s; move IS-COMPACT(s) to a hyp
;; NB: ONE (di) peels only the forall here; the trailing IMPLIES needs a
;;     SECOND (di).  Idiom: di until the goal is atomic.
(mac 'totally-bounded-def)      ; unfold the GOAL's TOTALLY-BOUNDED.
;; NB: TOTALLY-BOUNDED is register-constant!'d (an opaque predicate symbol),
;;     NOT a def-predicate, so it has no macete of its own name -- you unfold
;;     it with its characterizing IFF axiom `totally-bounded-def' (likewise
;;     `is-r-net-def' for IS-R-NET).  Contrast IS-COMPACT / IS-OPEN-COVER /
;;     CLUSTER-POINT / HAS-FIP (compactness.scm), which ARE def-predicates and
;;     unfold by their own name.  [OBSTACLE 1: a vocabulary inconsistency.]
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
