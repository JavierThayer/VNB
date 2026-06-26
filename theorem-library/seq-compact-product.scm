;;; theorem-library/seq-compact-product.scm
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

;;; SEQ-COMPACT(s): every sequence in X(s) has a subsequence converging to a
;;; point of X(s).  The metric face of compactness.  Bound vars: phi the
;;; reindexing, L the limit -- never `x' (the carrier accessor X folds to x and
;;; sits next to the point set) [[feedback_no_case_variant_binders]].
(def-predicate 'SEQ-COMPACT '(s)
  '(AND (IS-METRIC-SPACE s)
        (FORALL f
          (IMPLIES (IN f (FUN NN (X s)))
            (FORSOME phi
              (AND (STRICTLY-MONO-NN phi)
                   (FORSOME L
                     (AND (IN L (X s))
                          (CONVERGES-TO s (SUBSEQ f phi) L)))))))))

;;; compact <=> sequentially compact, for a metric space (Prop 3.12 (1)<=>(3)).
(support 'compact-iff-seq-compact
  '(FORALL s (IMPLIES (IS-METRIC-SPACE s)
     (IFF (IS-COMPACT s) (SEQ-COMPACT s)))))
(warrant! 'compact-iff-seq-compact 'reference
  "calculus.pdf Prop 3.12 (1)<=>(3): a metric space is compact iff it is
   sequentially compact.  A cluster point of a sequence is exactly the limit of
   a convergent subsequence (CLUSTER-POINT s f x iff some strictly-mono phi has
   SUBSEQ(f,phi) -> x), so this is compact-iff-cluster-point restated with
   convergent subsequences in place of cluster points.")

;;; =======================================================================
;;; 1.5  Convergence along an index block, and the refinement tower.
;;; =======================================================================

;;; CONVERGES-ALONG(s, g, B, p): the X(s)-sequence g converges to p when
;;; restricted to indices in the (infinite) block B -- for every eps>0 there is
;;; a threshold N past which every index i in B keeps g(i) within eps of p.
;;; This is CONVERGES-TO with the tail quantifier relativised to B; it is what a
;;; per-coordinate convergent subsequence delivers (B = the indices of that
;;; subsequence), and it is preserved under reindexing into B (coord-block-
;;; estimate).
(def-predicate 'CONVERGES-ALONG '(s g B p)
  '(AND (IS-METRIC-SPACE s)
   (AND (IN g (FUN NN (X s)))
   (AND (IN p (X s))
        (FORALL eps (IMPLIES (POS-RR eps)
          (FORSOME N (AND (IN N NN)
            (FORALL i (IMPLIES (IN i NN)
              (IMPLIES (IN i B) (IMPLIES (<= N i)
                (<= ((D s) (g i) p) eps)))))))))))))

;;; convergence-block-tower: the refinement-tower core of the diagonal argument
;;; (the analogue of block-family, asserted).  Iterating SEQ-COMPACT one
;;; coordinate at a time -- pass to a convergent-in-coordinate-n sub-block,
;;; built by dependent choice on n (dc-on-nn) -- yields a NESTED tower of
;;; infinite index blocks S(n) and a product point L with coordinate n of seq
;;; convergent ALONG S(n) to L(n).  The hard combinatorial content; the diagonal
;;; (theorem-library/diagonalization) and the per-coordinate transfer (coord-
;;; block-estimate) are proven on top.
(support 'convergence-block-tower
  '(FORALL ms (IMPLIES (IS-MS-SEQUENCE ms)
     (IMPLIES (FORALL n (IMPLIES (IN n NN) (SEQ-COMPACT (ms n))))
       (FORALL seq (IMPLIES (IN seq (FUN NN (PRODUCT-CARRIER ms)))
         (FORSOME S
           (AND (IN S (FUN NN (INF-SUBSETS NN)))
           (AND (FORALL k (IMPLIES (IN k NN) (SUBSET (S (succ k)) (S k))))
                (FORSOME L
                  (AND (IN L (PRODUCT-CARRIER ms))
                       (FORALL n (IMPLIES (IN n NN)
                         (CONVERGES-ALONG (ms n)
                           (VNB-LAMBDA i ((seq i) n))
                           (S n)
                           (L n)))))))))))))))
(warrant! 'convergence-block-tower 'informal
  "Coordinatewise refinement by dependent choice (calculus.pdf Remark 3.30).
   S(0): SEQ-COMPACT(ms 0) on i|->(seq i)(0) gives a convergent subsequence; its
   index set is an infinite block with coordinate 0 convergent along it.  Given
   S(n), restrict to it and apply SEQ-COMPACT(ms (n+1)) to the (n+1)-coordinate
   sequence to get S(n+1) subset S(n), still convergent in coordinates <= n+1.
   dc-on-nn laces the choices into S:NN->INF-SUBSETS(NN); L(n) is the
   coordinate-n limit, L in PRODUCT-CARRIER.  The block-family analogue for
   convergence; asserted in the library-build phase, the diagonal extraction on
   top is machine-proven.")

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
(support 'coordinatewise-diagonal-subseq
  '(FORALL ms (IMPLIES (IS-MS-SEQUENCE ms)
     (IMPLIES (FORALL n (IMPLIES (IN n NN) (SEQ-COMPACT (ms n))))
       (FORALL seq (IMPLIES (IN seq (FUN NN (PRODUCT-CARRIER ms)))
         (FORSOME delta
           (AND (STRICTLY-MONO-NN delta)
                (FORSOME L
                  (AND (IN L (PRODUCT-CARRIER ms))
                       (FORALL n (IMPLIES (IN n NN)
                         (CONVERGES-TO (ms n)
                           (VNB-LAMBDA k (((SUBSEQ seq delta) k) n))
                           (L n))))))))))))))
(warrant! 'coordinatewise-diagonal-subseq 'informal
  "The diagonal argument (calculus.pdf Remark 3.30 applied across coordinates).
   Build reindexings by dependent choice on the coordinate index (dc-on-nn over
   X = strictly-mono maps NN->NN): phi_0 strictly monotone with coordinate 0 of
   seq o phi_0 convergent -- SEQ-COMPACT(ms 0) on k|->(seq k)(0); given the
   cumulative psi_n = phi_0 o ... o phi_n, choose phi_{n+1} so coordinate n+1 of
   seq o psi_n o phi_{n+1} converges -- SEQ-COMPACT(ms (n+1)); a subsequence of a
   convergent sequence still converges, so coordinates <= n stay convergent.  The
   DIAGONAL delta(k) := psi_k(k) is strictly monotone and, for each n, its tail
   { delta(k) : k >= n } is a subsequence of psi_n, hence seq o delta converges
   in coordinate n.  L(n) := that coordinate-n limit; L lies in PRODUCT-CARRIER
   (each L(n) in X(ms n)).  The per-coordinate convergent subsequence is exactly
   SEQ-COMPACT of each factor; the lacing-together is dc-on-nn + the diagonal.")

;;; =======================================================================
;;; 3.  The product is sequentially compact.
;;; =======================================================================

;;; seq-compact-countable-product: a countable product of sequentially compact
;;; metric spaces is sequentially compact.
(support 'seq-compact-countable-product
  '(FORALL ms (IMPLIES (IS-MS-SEQUENCE ms)
     (IMPLIES (FORALL n (IMPLIES (IN n NN) (SEQ-COMPACT (ms n))))
       (SEQ-COMPACT (PRODUCT-METRIC ms))))))
(warrant! 'seq-compact-countable-product 'reference
  "Given a sequence seq in the product carrier (= X(PRODUCT-METRIC ms), by
   product-metric-carrier), coordinatewise-diagonal-subseq yields a strictly
   monotone delta and L in PRODUCT-CARRIER(ms) with SUBSEQ(seq,delta) converging
   in every coordinate to L(n).  product-convergence-coordinatewise -- at the
   default summable weights (product-metric-default-summable) -- turns
   coordinatewise convergence into CONVERGES-TO(PRODUCT-METRIC ms,
   SUBSEQ(seq,delta), L).  So every product sequence has a convergent
   subsequence: PRODUCT-METRIC(ms) is sequentially compact.")

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
