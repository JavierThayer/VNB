;;; MOVED 2026-09-20 (batch 12-A) from theorem-library/: this file is VOCABULARY --
;;; definitions, notation and warranted supports, not one proof -- and every theorem
;;; stated with it had to load below it.  Its load.scm slot is unchanged.
;;; structure-library/seq-compact-product.scm
;;; ====================================================================
;;; Countable Tychonoff for compact metric spaces:
;;;     a countable product of compact metric spaces is compact.
;;;
;;; The metric (sequential) route, NOT open covers / ultrafilters -- staying
;;; countably-based [[feedback_countably_based]].  Compactness of a metric space
;;; is sequential compactness (Prop 3.12 (1)<=>(3)); the product of sequentially
;;; compact spaces is sequentially compact by the DIAGONALIZATION argument, and
;;; coordinatewise convergence in the product metric IS convergence
;;; (product-convergence-coordinatewise, product-metric.scm).
;;;
;;; The genuinely new content is the keystone coordinatewise-diagonal-subseq:
;;; the iterated subsequence extraction + diagonal.  It is the convergence-level
;;; analogue of theorem-library/diagonalization (which diagonalizes nested INDEX
;;; BLOCKS); here we diagonalize nested REINDEXINGS, one per coordinate, built by
;;; dependent choice on NN (dc-on-nn).  Library-build phase: stated as warranted
;;; supports [[feedback_library_axioms_fine]] [[feedback_pss_over_proof_slog]];
;;; each warrant names the standard construction.
;;;
;;; Dependencies: compactness.scm (IS-COMPACT, compact-iff-cluster-point),
;;; product-metric.scm (PRODUCT-METRIC/-CARRIER, IS-MS-SEQUENCE,
;;; product-convergence-coordinatewise, product-is-metric-space,
;;; product-metric-default-summable), cauchy-subsequence.scm (STRICTLY-MONO-NN,
;;; SUBSEQ), metric-completeness.scm (CONVERGES-TO), dc-on-nn.scm (cited in the
;;; keystone warrant).  Loads after product-metric.
;;; ====================================================================

;;; =======================================================================
;;; 1.  Sequential compactness
;;; =======================================================================

;;; SEQ-COMPACT(s): every sequence in PTS(s) has a subsequence converging to a
;;; point of PTS(s).  The metric face of compactness.  Bound vars: phi the
;;; reindexing, L the limit -- never `x' (the point-set accessor was `X' when
;;; this was written -- it is `PTS' now -- and folds to x, sitting next to the
;;; point set) [[feedback_no_case_variant_binders]].
(def-predicate 'SEQ-COMPACT '(s)
  '(AND (IS-METRIC-SPACE s)
        (FORALL f
          (IMPLIES (IN f (FUN NN (PTS s)))
            (FORSOME phi
              (AND (STRICTLY-MONO-NN phi)
                   (FORSOME L
                     (AND (IN L (PTS s))
                          (CONVERGES-TO s (SUBSEQ f phi) L)))))))))

;;; compact <=> sequentially compact, for a metric space (Prop 3.12 (1)<=>(3)).
;; A Prop-3.12 equivalence, BUT kept in PSS: the proven Tychonoff theorem
;; compact-countable-product backchains through it, so it is a genuine fast
;; lemma (used-as-fast-lemma test passes), not just a headline destination.
;;; compact-iff-seq-compact PROVEN modulo 0 in theorem-library/rake-lebesgue-number.scm (2026-09-19)

;;; =======================================================================
;;; 1.5  Convergence along an index block, and the refinement tower.
;;; =======================================================================

;;; CONVERGES-ALONG(s, g, B, p): the PTS(s)-sequence g converges to p when
;;; restricted to indices in the (infinite) block B -- for every eps>0 there is
;;; a threshold N past which every index i in B keeps g(i) within eps of p.
;;; This is CONVERGES-TO with the tail quantifier relativised to B; it is what a
;;; per-coordinate convergent subsequence delivers (B = the indices of that
;;; subsequence), and it is preserved under reindexing into B (coord-block-
;;; estimate).
(def-predicate 'CONVERGES-ALONG '(s g B p)
  '(AND (IS-METRIC-SPACE s)
   (AND (IN g (FUN NN (PTS s)))
   (AND (IN p (PTS s))
        (FORALL eps (IMPLIES (POS-RR eps)
          (FORSOME N (AND (IN N NN)
            (FORALL i (IMPLIES (IN i NN)
              (IMPLIES (IN i B) (IMPLIES (<= N i)
                (<= ((DIST s) (g i) p) eps)))))))))))))

;;; convergence-block-tower: the refinement-tower core of the diagonal argument
;;; (the analogue of block-family, asserted).  Iterating SEQ-COMPACT one
;;; coordinate at a time -- pass to a convergent-in-coordinate-n sub-block,
;;; built by dependent choice on n (dc-on-nn) -- yields a NESTED tower of
;;; infinite index blocks S(n) and a product point L with coordinate n of seq
;;; convergent ALONG S(n) to L(n).  The hard combinatorial content; the diagonal
;;; (theorem-library/diagonalization) and the per-coordinate transfer (coord-
;;; block-estimate) are proven on top.
;;; convergence-block-tower PROVEN modulo 0 in theorem-library/rake-block-tower.scm (2026-09-19)

;;; coord-block-estimate: convergence ALONG a block transfers to any reindexing
;;; whose tail lands in the block.  If g converges to p along B, delta is
;;; strictly monotone, and delta(j) in B for all j >= m0, then SUBSEQ(g,delta)
;;; converges to p.  This is the per-coordinate transfer that turns the tower's
;;; block-convergence into honest convergence of the diagonal subsequence.
;;;
;;; PROVEN to QED -- theorem-library/coord-block-estimate-proof.scm (interactive
;;; phase).  No longer asserted here.  Modulo {subseq-is-fun, nn-pair-upper-bound,
;;; strictly-mono-ge-id, fun-apply-type-c, nn-in-rr, rr-le-trans-c}.  The proof's
;;; tail-threshold bound var is m0, not n0, to dodge a fresh-var collision with
;;; the cainner skolem's n_* namespace (see that file's FRESH-VAR NOTE).

;;; =======================================================================
;;; 2.  The keystone: the DIAGONALIZATION argument across coordinates.
;;; =======================================================================

;;; coordinatewise-diagonal-subseq.  If every factor (ms n) is sequentially
;;; compact, then any sequence `seq' of points of the product has a single
;;; subsequence SUBSEQ(seq,delta) that converges in EVERY coordinate (to L(n)
;;; in factor n), with L a point of the product carrier.  This is the diagonal
;;; argument; product-convergence-coordinatewise then upgrades it to convergence
;;; in the product metric (next section).
;;;
;;; The coordinate-n sequence of a product sequence g is k |-> (g k)(n); written
;;; (VNB-LAMBDA k (((SUBSEQ seq delta) k) n)) so it matches the LHS shape that
;;; product-convergence-coordinatewise consumes verbatim.
;;; coordinatewise-diagonal-subseq PROVEN in theorem-library/rake-diagonal-subseq.scm (2026-09-19), modulo convergence-block-tower

;;; =======================================================================
;;; 3.  The product is sequentially compact.
;;; =======================================================================

;;; seq-compact-countable-product: a countable product of sequentially compact
;;; metric spaces is sequentially compact.
;; Sequential Tychonoff (countable product).  Kept in PSS: the proven
;; compact-countable-product backchains through it -- a genuine fast lemma.
;;; seq-compact-countable-product PROVEN in theorem-library/rake-diagonal-subseq.scm (2026-09-19), modulo convergence-block-tower

;;; =======================================================================
;;; 4.  Countable Tychonoff (headline).
;;; =======================================================================

;;; compact-countable-product: a countable product of COMPACT metric spaces is
;;; compact.  calculus.pdf countable Tychonoff via sequential compactness.
;;; PROVEN (not asserted) -- theorem-library/tychonoff-proof.scm drives it to
;;; QED: each factor compact => seq-compact (compact-iff-seq-compact); product
;;; seq-compact (seq-compact-countable-product); product is a metric space
;;; (product-is-metric-space @ default weight); seq-compact => compact.  The
;;; cross-coordinate diagonalisation is isolated in the keystone coordinatewise-
;;; diagonal-subseq (cited through seq-compact-countable-product).  The statement
;;; is reproduced there in its (sp ...).

;;; ----- Plain-English glosses (PSS review 2026-06-26): 3+-line statements -----
(gloss! 'convergence-block-tower
  "For a sequence ms of sequentially compact metric spaces and any sequence seq of points of their product: there is a nested tower of infinite index blocks S(0) >= S(1) >= ... and a product point L such that, in each coordinate n, the n-th coordinates of seq converge to L(n) ALONG the block S(n) (i.e. once restricted to indices in S(n)).  The coordinatewise refinement underlying the diagonal argument.")
(gloss! 'coordinatewise-diagonal-subseq
  "For a sequence ms of sequentially compact metric spaces and any sequence seq of points of their product: there is a single strictly increasing reindexing delta and a product point L such that the subsequence seq o delta converges to L in EVERY coordinate at once.  The diagonal argument extracting one subsequence convergent in all coordinates.")

;;; -----------------------------------------------------------------------
;;; Notation -- the ENGLISH of these predicates, declared beside their
;;; definitions and read by wff->english / the proof reader (operators.scm).
;;; A def-predicate's reading cannot be derived the way a structure's noun can
;;; (noun vs adjective: IS-COMPLETE wants "s is complete", not "s is a complete"),
;;; so it is written here, once, next to what it means.
(notation! 'SEQ-COMPACT 'kind 'predicate 'arity 1
           'english "$1 is sequentially compact")
(notation! 'CONVERGES-ALONG 'kind 'predicate 'arity 4
           'english "$2 converges to $4 along $3 in $1")
