;;; theorem-library/block-family-combinatorial.scm
;;; ====================================================================
;;; The COMBINATORIAL block family -- block-family with the metric
;;; abstracted away.
;;;
;;; block-family (theorem-library/cauchy-subsequence.scm) says: for a
;;; totally bounded s, a sequence f:NN->PTS(s) and a positive null radius
;;; sequence rad, the index set NN splits into a nested descending family
;;; of INFINITE blocks blk(k), each pinning f into a single rad(k)-ball.
;;;
;;; Stripped of its metric clothing, NONE of that is about distance.  The
;;; only thing total boundedness ever supplies is, at each level k, a
;;; FINITE cover of the point set (the finite rad(k)-net's balls).  The
;;; engine is infinite pigeonhole (pigeonhole-infinite) + dependent choice
;;; on NN (dc-on-nn); the radii, their positivity, and their decay to 0
;;; play no part in the construction.  (Decay re-enters only downstream, in
;;; the Cauchy estimate -- two points in one rad(k)-ball are < 2 rad(k)
;;; apart -- not here.)
;;;
;;; So the honest statement replaces "metric + radius sequence" by a bare
;;; SEQUENCE OF FINITE COVERS  cov : NN -> finite-covers-of-V:
;;;
;;;   V a set, f : NN -> V, cov(k) a finite cover of V for each k
;;;     ==>  exists blk : NN -> INF-SUBSETS(NN) with
;;;            (nesting)  blk(succ k) subset blk(k)               for all k
;;;            (capture)  some U in cov(k) has f(i) in U for all i in blk(k).
;;;
;;; The metric block-family is the instance V := PTS(s),
;;; cov(k) := { BALL(s,c,rad k) : c in (a finite rad(k)-net) }; and
;;; tb-block-step is the per-level cover-block-step at that same cover.
;;;
;;; Rests on: inf-subsets, pigeonhole, dc-on-nn (all already loaded).
;;; No metric vocabulary is used or needed.
;;; ====================================================================

;;; -----------------------------------------------------------------------
;;; Vocabulary: a finite cover of a set.
;;; -----------------------------------------------------------------------

;;; IS-FINITE-COVER(C, A): C is a finite family of sets whose union covers
;;; A.  CARD(C) in NN is finiteness; A subset BIG-UNION(C) is coverage --
;;; enough that every a in A lies in some member of C, which is all the
;;; pigeonhole classifier needs.  (Members need not be subsets of A.)
(def-predicate 'IS-FINITE-COVER '(C A)
  '(AND (IN C SET)
   (AND (IN (CARD C) NN)
        (SUBSET A (BIG-UNION U C U)))))

;;; -----------------------------------------------------------------------
;;; The combinatorial per-level pigeonhole -- the engine, metric-free.
;;; -----------------------------------------------------------------------

;;; cover-block-step: within ANY infinite index block J, a finite cover C
;;; of V pins an infinite SUB-block J_ subset J into a single member of C.
;;; This is tb-block-step with the finite rad-net replaced by an arbitrary
;;; finite cover -- and the proof shows exactly how little the metric did:
;;;   classifier:  CHOICE gives pi : J -> C with pi(i) = some member of C
;;;                containing f(i)  (exists since C covers V and f(i) in V);
;;;   pigeonhole:  J infinite, C finite, pi : J -> C, so pigeonhole-infinite
;;;                gives U in C with an INFINITE fibre
;;;                J_ = { i in J : pi(i) = U } subset J, every f(i) (i in J_)
;;;                in U.
;;; Not one metric axiom is touched; "finite cover" is the whole hypothesis.
(support 'cover-block-step
  '(FORALL V
     (IMPLIES (IN V SET)
       (FORALL f
         (IMPLIES (IN f (FUN NN V))
           (FORALL C
             (IMPLIES (IS-FINITE-COVER C V)
               (FORALL J
                 (IMPLIES (IN J (INF-SUBSETS NN))
                   (FORSOME J_
                     (AND (IN J_ (INF-SUBSETS NN))
                     (AND (SUBSET J_ J)
                          (FORSOME U
                            (AND (IN U C)
                                 (FORALL i
                                   (IMPLIES (IN i J_)
                                     (IN (f i) U)))))))))))))))))
(warrant! 'cover-block-step 'well-known
  "Infinite pigeonhole behind a finite cover.  C finite covers V, so CHOICE
   gives a classifier pi:J->C with f(i) in pi(i) for i in J; pigeonhole-
   infinite on the infinite J then yields a member U in C with an infinite
   fibre J_ = SEP(i in J | pi(i)=U) subset J, and f(i) in U for every i in
   J_.  Metric-free generalization of tb-block-step (which is this at C = a
   finite rad-net's ball cover).")

;;; -----------------------------------------------------------------------
;;; The combinatorial nested block family -- pigeonhole recursion.
;;; -----------------------------------------------------------------------

;;; block-family-combinatorial: recurse cover-block-step down a SEQUENCE of
;;; finite covers.  No metric, no radius, no positivity, no decay -- the
;;; bare combinatorial content of block-family.
;;;
;;; Derivation (identical in shape to calculus/block-family-rederive.scm,
;;; one abstraction layer down):
;;;   step relation  R(k, J, J_) = "J_ in INF-SUBSETS(NN), J_ subset J, and
;;;     some U in cov(k) has f(i) in U for all i in J_";
;;;   R-totality is cover-block-step at C = cov(k) (a finite cover by hyp);
;;;   dc-on-nn[X := INF-SUBSETS(NN), a := NN, R] yields aux:NN->INF-SUBSETS
;;;   (NN), aux(0)=NN, (k, aux k, aux(succ k)) in R;  index-shift
;;;   blk := lambda k. aux(succ k) gives nesting + capture verbatim.
;;; block-family-combinatorial itself -- cover-block-step recursed down the
;;; sequence of covers -- is now MACHINE-PROVEN to QED in the proof-script
;;; region: theorem-library/block-family-combinatorial-proof.scm (dc-on-nn-pred
;;; with step set nxt(k,J) = { J_ in INF-SUBSETS(NN) : J_ subset J and captured
;;; by cov(k) }; totality is cover-block-step; blk(k) := aux(succ k)).  It loads
;;; after interactive (needs sp/di) but before cauchy-subseq-proof, which cites
;;; it.  The statement lives there, at the (sp ...).

;;; ----- Plain-English gloss (PSS review 2026-06-26) -----
(gloss! 'cover-block-step
  "For any set V, a sequence f of elements of V, a finite cover C of V, and an infinite index block J: there is a smaller infinite block J' contained in J and a single cover member U such that all f(i) for i in J' lie in U.  The metric-free single pigeonhole step that block-family-combinatorial iterates.")
