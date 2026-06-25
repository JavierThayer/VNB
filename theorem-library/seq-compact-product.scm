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
(support 'compact-countable-product
  '(FORALL ms (IMPLIES (IS-MS-SEQUENCE ms)
     (IMPLIES (FORALL n (IMPLIES (IN n NN) (IS-COMPACT (ms n))))
       (IS-COMPACT (PRODUCT-METRIC ms))))))
(warrant! 'compact-countable-product 'reference
  "Countable Tychonoff for compact metric spaces.  Each factor compact =>
   sequentially compact (compact-iff-seq-compact, forward); then
   seq-compact-countable-product makes PRODUCT-METRIC(ms) sequentially compact;
   the product is a metric space (product-is-metric-space at the default
   summable weights, product-metric-default-summable); compact-iff-seq-compact
   backward turns sequential compactness back into compactness.  No open covers
   or ultrafilters -- the metric/sequential route, countably-based.  The whole
   theorem rests on the diagonalization keystone coordinatewise-diagonal-subseq.")
