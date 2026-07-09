;;; calculus/block-family-rederive.scm
;;; ====================================================================
;;; STRESS TEST -- re-derive `block-family' (the nested-pigeonhole recursion,
;;; currently a MONOLITHIC warranted assertion in theorem-library/
;;; cauchy-subsequence.scm) from two SMALLER, more-trustworthy pieces:
;;;
;;;   tb-block-step  -- the relativized single pigeonhole fibre (NEW primitive;
;;;                     one finite net + one pigeonhole, no recursion); and
;;;   dc-on-nn       -- dependent choice / recursion on NN (existing PSS).
;;;
;;; If this goes through, block-family stops being an axiom that bundles
;;; pigeonhole + recursion + nesting in one breath, and becomes a THEOREM resting
;;; on (i) a single-step assertion and (ii) the already-accepted recursion
;;; principle -- a genuine trust reduction.
;;;
;;; NOT part of load.scm; a probe/teaching script.  Run (fast):
;;;   cd ~/prover
;;;   mit-scheme --quiet --load load.scm \
;;;       --load calculus/block-family-rederive.scm --eval '(exit)' \
;;;       > /tmp/bfr.out 2>&1
;;;   grep -E '^;;; ' /tmp/bfr.out
;;;
;;; ====================================================================
;;; THE DERIVATION (on paper)
;;;
;;; Goal (after grind introduces s, TB s, f:NN->X(s), rad:NULL-RR-SEQ):
;;;   exists blk:NN->INF-SUBSETS(NN).  (nesting) blk(succ k) subset blk(k)  and
;;;                                    (small)   blk(k) lies in a rad(k)-ball.
;;;
;;;   1. The STEP RELATION.  Let
;;;        R = { (k, J, J_) :  J_ in INF-SUBSETS(NN),  J_ subset J,  and
;;;                            exists c in X(s). forall i in J_. f(i) in BALL(s,c,rad k) }.
;;;      dc-on-nn wants R as a SET of triples (LIST k J J_).
;;;   2. R-TOTALITY is exactly tb-block-step at r = rad(k) (POS-RR(rad k) holds,
;;;      NULL-RR-SEQ is pointwise positive): for every k in NN and every infinite
;;;      block J, tb-block-step hands back a J_ with (k,J,J_) in R.
;;;   3. dc-on-nn[X := INF-SUBSETS(NN), a := NN, R] then yields
;;;        aux : NN -> INF-SUBSETS(NN),  aux(0) = NN,
;;;        forall k. (k, aux k, aux(succ k)) in R,
;;;      i.e. aux(succ k) subset aux(k) AND aux(succ k) sits in a rad(k)-ball.
;;;   4. INDEX SHIFT.  Put blk := lambda k. aux(succ k).  Then
;;;        blk(succ k) = aux(succ(succ k)) subset aux(succ k) = blk(k)   [nesting]
;;;        blk(k)      = aux(succ k) lies in a rad(k)-ball                [small]
;;;      -- block-family verbatim.  (The shift is what lets blk(0) already be a
;;;      rad(0)-fibre; dc-on-nn pins aux(0)=NN, which is in no ball.)
;;;
;;; So: PIGEONHOLE is tb-block-step (free), RECURSION is dc-on-nn (free).  What
;;; remains is pure set-theoretic plumbing -- and that is where the friction is.
;;; ====================================================================

(define (gf) (and *ps* (wff-formula (sequent-node-assertion (proof-state-focus *ps*)))))
(define (ga) (and *ps* (map wff-formula (sequent-node-assumptions (proof-state-focus *ps*)))))
(define (--- title) (newline)(display ";;; ===== ")(display title)(display " =====")(newline))

(--- "Pose block-family and grind")
(sp (make-wff
  '(FORALL s (IMPLIES (TOTALLY-BOUNDED s)
     (FORALL f (IMPLIES (IN f (FUN NN (X s)))
       (FORALL rad (IMPLIES (NULL-RR-SEQ rad)
         (FORSOME blk
           (AND (IN blk (FUN NN (INF-SUBSETS NN)))
           (AND (FORALL k (IMPLIES (IN k NN) (SUBSET (blk (succ k)) (blk k))))
                (FORALL k (IMPLIES (IN k NN)
                  (FORSOME c (AND (IN c (X s))
                    (FORALL i (IMPLIES (IN i (blk k))
                      (IN (f i) (BALL s c (rad k))))))))))))))))))))
(grind)
(display ";;; GOAL after grind: ")(write (gf))(newline)
(display ";;; ASMS after grind: ")(write (ga))(newline)

(--- "What the single-move copilot offers here")
(what-now)

;;; ====================================================================
;;; OBSTACLE MAP (what the kernel actually needs, in priority order)
;;;
;;; O1  THE STEP RELATION AS A SET.  dc-on-nn's R is a SET; we must build
;;;     R = COMP(t, P(t)) where t ranges over triples (LIST k J J_) and P
;;;     decodes t (via NTH 1/2/3) and asserts the fibre predicate.  Proving
;;;     R in SET and the membership bridge (LIST k J J_) in R  <=>  P(k,J,J_)
;;;     is the bulk of the work, and it is GENERIC plumbing, unrelated to the
;;;     mathematics.  *** This is the dominant obstacle. ***
;;;
;;; O2  TOTALITY <-> tb-block-step.  Once R exists, dc-on-nn's totality
;;;     hypothesis  forall k forall u in X. exists y in X. (k,u,y) in R
;;;     is tb-block-step at r = rad(k), modulo the O1 membership bridge and
;;;     POS-RR(rad k) (from NULL-RR-SEQ's positivity conjunct).
;;;
;;; O3  dc-on-nn TYPING HYPS.  INF-SUBSETS(NN) in SET (it is a subclass of
;;;     POWER(NN), a set) and NN in INF-SUBSETS(NN) (NN subset NN, NN infinite).
;;;     Two small lemmas; candidates for warranted supports.
;;;
;;; O4  STEP EXTRACTION + INDEX SHIFT.  From (k, aux k, aux(succ k)) in R,
;;;     recover the two conjuncts (same O1 bridge backwards), then define
;;;     blk = VNB-LAMBDA(k, aux(succ k)) and discharge nesting/small with
;;;     succ arithmetic.  Mechanical once O1 is in hand.
;;;
;;; VERDICT: the MATHEMATICS of block-family is fully covered -- pigeonhole by
;;; tb-block-step, recursion by dc-on-nn.  The ONLY residual is O1, and it is
;;; not about this theorem at all: it is the cost of dc-on-nn taking its step as
;;; a relation-SET rather than a PREDICATE.
;;;
;;; RECOMMENDED MACHINERY (kills O1/O2/O4 wholesale):
;;;   dc-on-nn-pred -- a variant of dc-on-nn whose step is a two-place
;;;   PREDICATE  step(k, u, y)  (k in NN, u y in X), with conclusion
;;;     exists f:NN->X.  f(0)=a  and  forall k in NN. step(k, f k, f(succ k)),
;;;   the COMP/sethood encoding done ONCE inside, hidden from every caller.
;;;   With it, block-family's re-derivation is: instantiate dc-on-nn-pred with
;;;   step := the tb-block-step fibre predicate, discharge totality by
;;;   tb-block-step, index-shift.  No relation-set plumbing in the proof.
;;; ====================================================================
(--- "End of stress probe")
