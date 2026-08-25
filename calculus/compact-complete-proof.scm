;;; compact-complete-proof.scm -- machine proof of  compact => complete
;;; (calculus.pdf Prop 3.12, the other half of (1)=>(4); the totally-bounded
;;; half is calculus/compact-tb-proof.scm).  Run:
;;;   ./prover calculus/compact-complete-proof.scm
;;;
;;; Mathematical content: a Cauchy sequence f in a compact space has a cluster
;;; point (sequential compactness, Prop 3.12 (1)=>(3)); a Cauchy sequence with
;;; a cluster point converges to it.  So every Cauchy sequence converges, i.e.
;;; the space is complete.
;;;
;;; Three warranted lemmas carry the analysis (compactness.scm /
;;; metric-completeness.scm), all stated backchain-ready (relation- or
;;; FORSOME-headed conclusion, so a goal matches them; bc* is alpha-aware on
;;; binders since the compact-tb work):
;;;   compact-seq-has-cluster  : compact + f:NN->X  =>  exists cluster point
;;;   cauchy-cluster-converges : Cauchy + a cluster point  =>  converges  (keystone)
;;;   cauchy-seq-is-fun        : Cauchy  =>  f : NN -> X   (typing projection)
;;;
;;; Structure (pure backward chaining -- the clean route the stress test
;;; settled on; forward `fact' was rejected because it will not detach a
;;; CONJUNCTIVE antecedent whose conjuncts are only separately in context, and
;;; it litters the tree with sibling goals):
;;;   - unfold IS-COMPLETE in the goal, split the conjunction;
;;;   - metric-space subgoal: the first conjunct of IS-COMPACT, immediate;
;;;   - for the Cauchy sequence f, backchain the keystone cauchy-cluster-
;;;     converges (leaves Cauchy [in ctx] and exists-cluster);
;;;   - exists-cluster: backchain compact-seq-has-cluster (leaves IS-COMPACT
;;;     [in ctx] and f:NN->X);
;;;   - f:NN->X: backchain cauchy-seq-is-fun (leaves IS-CAUCHY-SEQ [in ctx]).
;;;
;;; Proves modulo the three asserted lemmas above; everything else is
;;; machine-checked.

(sp (make-wff '(FORALL s (IMPLIES (IS-COMPACT s) (IS-COMPLETE s)))))
(di) (di)                       ; peel forall s; move IS-COMPACT(s) to a hyp
(mac 'IS-COMPLETE)              ; unfold the goal
(di)                            ; split: [a] is-metric-space  [b] forall f ...

;; ----- [a] is-metric-space(s): the first conjunct of IS-COMPACT(s) -----
(mac-h 'IS-COMPACT 1)           ; unfold IS-COMPACT in the assumption
(ai 1)                          ; decompose the conjunction; is-metric-space(s) lands
(ass)

;; ----- [b] every Cauchy sequence converges -----
(di) (di)                       ; peel f; assume IS-CAUCHY-SEQ(s,f); goal CONVERGES(s,f)
(bc* 'cauchy-cluster-converges) ; goal -> IS-CAUCHY-SEQ(s,f) and exists-cluster
(di)                            ; split the AND goal
(ass)                           ;   IS-CAUCHY-SEQ(s,f) is in context
(bc* 'compact-seq-has-cluster)  ; exists-cluster -> IS-COMPACT(s) and f:NN->X
(di)                            ; split the AND goal
(ass)                           ;   IS-COMPACT(s) is in context
(bc* 'cauchy-seq-is-fun)        ; f:NN->X -> IS-CAUCHY-SEQ(s,f)
(ass)                           ;   in context

(qed 'compact-implies-complete)
