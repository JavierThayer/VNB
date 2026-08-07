;;; separable.scm -- separability of a metric space (a dense sequence), the
;;; vocabulary and the one support the bridge compact => separable still needs.
;;; Added 2026-07-22 for the Ascoli-Arzela arc.
;;;
;;; A metric space is SEPARABLE iff it has a countable dense subset; for a metric
;;; space this is equivalent to having a DENSE SEQUENCE dseq : NN -> PTS(s)
;;; (every ball meets its range).  We take the dense-sequence form: it is exactly
;;; what Ascoli's diagonal argument consumes, and it sidesteps a standalone
;;; IS-COUNTABLE (which the base does not have).
;;;
;;; WHAT IS HERE, AND WHAT IS NOT (2026-08-07).  `compact-metric-is-separable'
;;; stood in this file as a `reference' assertion for two weeks; it is now PROVEN
;;; in theorem-library/compact-separable-proof.scm and the assertion is retired.
;;; What stays here is the vocabulary (IS-SEPARABLE) and ONE support,
;;; `tb-scale-dense-seq', whose own comment says why it is asserted.
;;;
;;; The history is worth keeping in one paragraph, because the file spent longer
;;; being wrong about the obstacle than being right about it.  The route was
;;; always: compact => totally bounded => a finite 1/(n+1)-net for each n => the
;;; union of the nets is countable and dense.  The first effort note called the
;;; choice of a net per scale an obstacle; it never was (CHOICE is a term-former
;;; backed by `choice-axiom', and dc-on-nn-pred packages the countable case).
;;; The real missing mechanism was a surjection NN -> NN x NN, and the note that
;;; identified it also guessed its construction wrong -- it sketched a staircase
;;; recursion, and what theorem-library/nn-pairing.scm actually built (2026-07-31)
;;; was CANTOR pairing, NNPAIR(i,j) = TRINUM(i+j) + j, with NNFST / NNSND as IOTA
;;; descriptions inverting it and `nn-flatten' as the consumable fact.  A second
;;; obstacle surfaced on 2026-08-01: the density step needs a scale with
;;; 1/(n+1) < eps, and the archimedean property was not in the tree at all --
;;; order-predicates.scm now carries `nn-unbounded-in-rr' and the two corollaries
;;; a net argument consumes, `nn-recip-succ-pos' and `nn-recip-succ-small'.
;;;
;;; Loads after compactness (IS-COMPACT, compact-iff-tb-complete) and metric-
;;; topology (TOTALLY-BOUNDED / IS-R-NET), before the Ascoli statement that
;;; rests on it and before the proof file, which cites tb-scale-dense-seq.
;;; Binder dseq (NOT e -- avoids the numeric constant %e / e).
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

;;; -----------------------------------------------------------------------
;;; tb-scale-dense-seq -- at every scale, a SEQUENCE that comes r-close to
;;; everything.  The one asserted step of compact-metric-is-separable.
;;;
;;; The theorem's proof needs a doubly indexed family of points, and what
;;; TOTALLY-BOUNDED offers at each scale is a finite SET.  Two conversions sit
;;; between them, and both are plumbing rather than mathematics:
;;;
;;;   (a) the net can be taken INSIDE the carrier.  Neither TOTALLY-BOUNDED nor
;;;       finite-ball-subcover-r-net says its net is a subset of PTS(s) -- only
;;;       that every point of PTS(s) is within r of one of its members.  A
;;;       member that serves any point at all lies in PTS(s), since DIST(s) is a
;;;       function on PTS(s) x PTS(s), so the part of F inside PTS(s) is again a finite r-net;
;;;       and the standard construction (CENTRE-SET, compactness.scm) produces
;;;       centres in the carrier outright, by centres-in-carrier.
;;;
;;;   (b) a FINITE net becomes a TOTAL sequence.  FIN-ENUM(F) enumerates F, but
;;;       only over ORD-SEGMENT(CARD F) (fin-enum-is-bijection); FUN is total, so
;;;       the sequence must be defined on all of NN.  Pad with x0:
;;;           g(j) = FIN-ENUM(F)(j)  for j in ORD-SEGMENT(CARD F),  else x0.
;;;       This is the one place the inhabitedness hypothesis of
;;;       compact-metric-is-separable is spent (the other is the base point of
;;;       the dependent-choice recursion).
;;;
;;; Stated with `<' rather than IS-R-NET's (d <= r AND d /= r) so the consumer
;;; can hand it straight to IS-SEPARABLE, and with the distance written
;;; d(p, g(j)) -- point first -- for the same reason: it saves a metric-sym step
;;; at every call site.
(support 'tb-scale-dense-seq
  (forall-guarded '(s) (list '(TOTALLY-BOUNDED s))
    (forall-guarded '(x0) (list '(IN x0 (PTS s)))
      (forall-guarded '(r) (list '(POS-RR r))
        (forsome-guarded 'g '(IN g (FUN NN (PTS s)))
          (forall-guarded '(p) (list '(IN p (PTS s)))
            (forsome-guarded 'j '(IN j NN)
              '(< ((DIST s) p (g j)) r))))))))
(warrant! 'tb-scale-dense-seq 'well-known
  "Total boundedness at radius r gives a finite F with every point of PTS(s)
   within r of a member of F.  Restrict F to PTS(s) -- a member serving any
   point is in PTS(s), the domain of DIST(s) -- so the part of F inside PTS(s) is a finite r-net
   inside the carrier; the CENTRE-SET construction (compactness.scm) delivers
   one directly, its members being chosen centres (centres-in-carrier).
   Enumerate it by FIN-ENUM (fin-enum-is-bijection: a bijection from
   ORD-SEGMENT(CARD F)) and pad with x0 outside that segment, which makes the
   enumeration TOTAL on NN without changing its range's r-density.  Asserted
   rather than mechanised: both steps are set-theoretic bookkeeping with no
   library payoff, and the topology they serve is machine-proven in
   theorem-library/compact-separable-proof.scm.")
(gloss! 'tb-scale-dense-seq
  "In a totally bounded metric space with at least one point, for every
   tolerance r there is a SEQUENCE whose terms come within r of every point of
   the space.  The sequence form of `there is a finite r-net': a finite net
   enumerated and padded out to all of NN.")
(category! 'tb-scale-dense-seq 'topology)

;;; -----------------------------------------------------------------------
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
;;; PROVEN 2026-08-07 and MOVED to theorem-library/compact-separable-proof.scm,
;;; where the statement now lives at its (sp ...).  The assertion that stood
;;; here -- `reference', on the user's calculus notes -- is retired: the driver
;;; the file header kept saying was "what remains" is written, and the only
;;; asserted step left is tb-scale-dense-seq above.  Its gloss and category
;;; moved with it; the `rests-on' now names tb-scale-dense-seq, dc-on-nn-pred
;;; and nn-flatten rather than compact-iff-tb-complete, which the proof does not
;;; use (it cites the direction compact-implies-totally-bounded instead).
