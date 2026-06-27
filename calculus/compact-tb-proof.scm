;;; compact-tb-proof.scm -- machine proof of  compact => totally bounded
;;; (calculus.pdf Prop 3.12, the (1)=>(4) half), assembled from the two
;;; warranted ball-cover lemmas (compactness.scm).  Run:
;;;   ./prover calculus/compact-tb-proof.scm
;;;
;;; This is the QED the stress test (stress-tests/compact-tb-stress.scm) was blocked
;;; on.  The block was that bc* could not match a lemma whose conclusion is
;;; FORSOME-headed; that is now fixed (match-expr is alpha-aware on binders,
;;; macetes.scm), so bc* backchains the EXISTENTIAL lemma
;;; finite-ball-subcover-r-net directly.
;;;
;;; Structure:
;;;   - unfold compactness in the hypothesis and TOTALLY-BOUNDED in the goal;
;;;   - the metric-space subgoal is immediate;
;;;   - fix r > 0; instantiate compactness at the r-ball cover BALL-COVER(s,r);
;;;   - bc* finite-ball-subcover-r-net (centres of a finite subcover form a
;;;     finite r-net), discharging its three antecedents: metric-space,
;;;     r-condition, and "a finite subcover exists" -- the last by backchaining
;;;     the instantiated compactness implication and ball-cover-is-open-cover.
;;;
;;; Proves modulo the two asserted ball-cover lemmas (cover construction +
;;; centre extraction); everything else is machine-checked.

(sp (make-wff '(FORALL s (IMPLIES (IS-COMPACT s) (TOTALLY-BOUNDED s)))))

(di) (di)                       ; peel forall s; move IS-COMPACT(s) to a hyp
(mac-h 'IS-COMPACT 1)           ; unfold compactness: metric-space + subcover law
(ai 1)                          ; split that conjunction into two assumptions
(mac 'TOTALLY-BOUNDED)          ; unfold the goal's TOTALLY-BOUNDED (IFF axiom)
(di)                            ; split the goal AND

(ass)                           ; subgoal 1: is-metric-space(s)  -- in context

(di) (di)                       ; subgoal 2: fix r, assume r>0; goal = exists r-net
(inst 2 '(BALL-COVER s r))      ; compactness at C = BALL-COVER(s,r): adds the
                                ; implication  open-cover(BC) => exists subcover

(bc* 'finite-ball-subcover-r-net ()
  (ass)                         ; antecedent 1: is-metric-space(s)
  (ass)                         ; antecedent 2: r in RR, 0<=r, r/=0
  (begin                        ; antecedent 3: a finite subcover exists
    (bc '(IMPLIES (IS-OPEN-COVER s (BALL-COVER s r))
                  (FORSOME f (AND (SUBSET f (BALL-COVER s r))
                             (AND (IN (CARD f) NN) (IS-OPEN-COVER s f))))))
    (bc* 'ball-cover-is-open-cover () (ass) (ass))))

(qed 'compact-tb)
