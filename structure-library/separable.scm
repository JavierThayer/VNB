;;; separable.scm -- separability of a metric space (a dense sequence) and the
;;; bridge  compact => separable.  Vocabulary + STATEMENT; proof deferred (see
;;; the effort note).  Added 2026-07-22 for the Ascoli-Arzelà arc.
;;;
;;; A metric space is SEPARABLE iff it has a countable dense subset; for a metric
;;; space this is equivalent to having a DENSE SEQUENCE dseq : NN -> PTS(s)
;;; (every ball meets its range).  We take the dense-sequence form: it is exactly
;;; what Ascoli's diagonal argument consumes, and it sidesteps a standalone
;;; IS-COUNTABLE (which the base does not have).
;;;
;;; EFFORT NOTE (why WARRANTED, not proved).  compact => totally bounded
;;; (compact-iff-tb-complete) => for each n a finite (1/(n+1))-net F_n; the union
;;; U_n F_n is a countable dense set.  A machine proof needs (a) a choice
;;; function n |-> F_n selecting a net per scale and (b) an ENUMERATION of the
;;; countable union of finite sets as one NN-sequence.
;;;
;;; REVISED 2026-07-29.  Obstacle (a) is NOT an obstacle: CHOICE is a term-former
;;; backed by global choice (theory.scm, `choice-axiom'), and the tree already
;;; selects exactly this way twice -- compactness.scm builds
;;; (IMAGE (VNB-LAMBDA B (CHOICE (CENTRES s B r))) F), and finsum.scm defines
;;; FIN-ENUM(S) = (CHOICE (BIJECTION (ORD-SEGMENT (CARD S)) S)).  So "a net per
;;; scale" is a def-functoid, and FIN-ENUM already enumerates each finite net,
;;; which is half of (b).
;;;
;;; What actually remains is ONE missing mechanism: a surjection NN -> NN x NN.
;;; Nothing in the tree has one.  `def-by-nn-recursion' (ordinals.scm) can build
;;; it with no arithmetic at all, by the staircase walk
;;;     W(0) = (0,0);  W(succ n) = if fst(W n) > 0 then (fst-1, snd+1)
;;;                                                else (snd+1, 0)
;;; -- no division, no unique factorization -- whose surjectivity is two
;;; inductions (the diagonal starts (t,0) by induction on t, then j steps along
;;; the diagonal).  It is worth building rather than asserting more topology:
;;; the same surjection gives the general flattening of a sequence of sequences,
;;; which is what `coordinatewise-diagonal-subseq' (asserted, in the Ascoli
;;; statement) and the countable unions of sigma-algebra.scm both want.
;;;
;;; RESOLVED 2026-07-31 -- the paragraph above is now history, and it guessed the
;;; route wrong.  theorem-library/nn-pairing.scm built the re-indexing mechanism,
;;; but by CANTOR pairing (NNPAIR(i,j) = TRINUM(i+j) + j, antidiagonal position)
;;; rather than the staircase recursion sketched above; the projections NNFST /
;;; NNSND are IOTA descriptions inverting it, and the consumable fact is
;;; `nn-flatten' -- for h : NN -> (NN -> A) there is e : NN -> A whose range
;;; contains every h(i)(j), witness e = \n. h(NNFST n)(NNSND n).  No appeal to
;;; CHOICE anywhere in that file: onto plus injective was enough.
;;;
;;; SECOND OBSTACLE, found and settled 2026-08-01.  The density step needs, for a
;;; given eps > 0, a scale n with 1/(n+1) < eps -- and the archimedean property
;;; was not in the tree at all.  The three eps-shrinking facts in
;;; order-predicates.scm are RR-only and never mention NN, and RR is axiomatised
;;; (number-systems.scm:220-337) as an ordered field with no completeness axiom,
;;; so it was not derivable either.  order-predicates.scm now carries
;;; `nn-unbounded-in-rr' (well-known) with the two corollaries a net argument
;;; consumes, `nn-recip-succ-pos' and `nn-recip-succ-small' (both informal).
;;;
;;; So every ingredient is now present -- compact-iff-tb-complete, CHOICE per
;;; scale, FIN-ENUM per net, nn-flatten to re-index, and the archimedean supports
;;; for density.  What remains is the DRIVER, not a missing fact.  The bill will
;;; not be `modulo 0': it will name the archimedean supports and whatever
;;; compact-iff-tb-complete carries.
;;;
;;; Loads after compactness (IS-COMPACT, compact-iff-tb-complete) and metric-
;;; topology (TOTALLY-BOUNDED / IS-R-NET), before the Ascoli statement that
;;; rests on it.  Binder dseq (NOT e -- avoids the numeric constant %e / e).
;;; ====================================================================

;;; IS-SEPARABLE(s): s is a metric space carrying a dense sequence
;;; dseq : NN -> PTS(s) -- every point is approximated to arbitrary precision by
;;; some dseq(n).
(def-predicate 'IS-SEPARABLE '(s)
  (conjuncts->and
    (list
      '(IS-METRIC-SPACE s)
      (forsome-guarded 'dseq '(IN dseq (FUN NN (PTS s)))
        (forall-guarded 'x '(IN x (PTS s))
          (forall-guarded 'eps '(POS-RR eps)
            (forsome-guarded 'n '(IN n NN)
              '(< ((DIST s) x (dseq n)) eps))))))))
(notation! 'IS-SEPARABLE 'kind 'predicate 'arity 1
           'english "$1 is separable")

;;; compact-metric-is-separable: a compact metric space is separable.  (IS-COMPACT
;;; already carries IS-METRIC-SPACE.)  The bridge Ascoli-Arzelà needs.
;;;
;;; INHABITEDNESS GUARD (added 2026-07-29).  The unguarded form was FALSE.  The
;;; empty metric space -- METRIC-SPACE carries no inhabitedness clause, so
;;; PTS(s) = EMPTY-SET with the empty distance function is a legitimate instance
;;; -- is vacuously IS-COMPACT, but IS-SEPARABLE demands a dseq in
;;; FUN(NN, PTS(s)), and FUN is TOTAL, so FUN(NN, EMPTY-SET) is empty and no
;;; dseq exists.  The defect is in the ENCODING, not in the mathematics: the
;;; empty space IS separable in the ordinary sense (its own empty subset is
;;; countable and dense); it is only "has a dense SEQUENCE" that fails on it.
;;; So the guard belongs here, on the one theorem whose CONCLUSION asserts a
;;; sequence, and NOT on IS-METRIC-SPACE -- requiring carriers to be inhabited
;;; would make every metric-space instance owe an inhabitedness proof and would
;;; expel the empty subspace, which every closed-subset / intersection /
;;; restriction construction produces.
;;;
;;; The two antecedents are kept SEPARATE (forall-guarded, nested IMPLIES) and
;;; not folded into an AND, so `fact` can peel both -- it will not cross a
;;; conjunctive antecedent.
(support 'compact-metric-is-separable
  (forall-guarded '(s)
    (list '(IS-COMPACT s)
          '(FORSOME x (IN x (PTS s))))
    '(IS-SEPARABLE s)))
(warrant! 'compact-metric-is-separable 'reference
  '(thayer-calc "compact metric => separable (union of finite 1/n-nets)"))
(gloss! 'compact-metric-is-separable
  "A compact metric space with at least one point is separable: it has a dense
   sequence.  The inhabitedness hypothesis is not decoration -- the empty metric
   space is compact and has no dense SEQUENCE at all, since FUN(NN, EMPTY-SET) is
   empty; it is separable only in the countable-dense-SUBSET sense, which is not
   the sense IS-SEPARABLE encodes.  Proof route: compact => totally bounded
   (compact-iff-tb-complete), so for each n in NN there is a FINITE (1/(n+1))-net
   F_n (TOTALLY-BOUNDED at r = 1/(n+1)); the union D = U_n F_n is countable, and it
   is dense because for any point x and tolerance eps, choosing n with 1/(n+1) < eps
   puts some center of F_n within eps of x.  Selecting the nets and enumerating each
   one are both available (CHOICE, FIN-ENUM); re-indexing the doubly indexed family
   by a single natural is `nn-flatten' (nn-pairing.scm, proven 2026-07-31), and the
   choice of scale below eps is `nn-recip-succ-small' (order-predicates.scm, added
   2026-08-01).  Every ingredient is therefore present and this is asserted only
   because the driver has not been written yet -- see the file header.")
(category! 'compact-metric-is-separable 'topology)

;; The proven/asserted engine this rests on: compact => totally bounded.  (The
;; countable-union enumeration is the content that is NOT yet a separate support.)
(rests-on 'compact-metric-is-separable '(compact-iff-tb-complete))
