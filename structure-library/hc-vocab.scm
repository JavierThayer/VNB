;;; hc-vocab.scm -- wave of 2026-11-09/10 (agent HAAR-C), wired 2026-11-10 from scratchpad/haarc-1109/hc-vocab.scm.
;;; Library: analysis.

;;; hc-vocab.scm -- vocabulary for Theorem 1.11 of the compact-groups notes (a group of affine isometries of a
;;; norm compact convex set has a common fixed point) and for the Haar integral of a compact group (Theorem 1.9 in
;;; the form of an invariant mean).  DEFINITIONS ONLY.  Agent HAAR-C, 2026-11-09 (new definitions, the user's to
;;; confirm).  DESTINATION: structure-library/hc-vocab.scm.  Library: analysis.
;;;
;;;   IS-AFFINE-ISOMETRY-GROUP(m, A, gs)
;;;       gs is a group of affine isometric maps of the subset A of the real normed vector space m: every member of
;;;       gs maps A into A, preserves convex combinations (1 - t) u + t v of points of A (0 <= t <= 1) and the
;;;       distance of m, and has an inverse in gs (some h in gs with g(h(x)) = x on A).  The notes say "a group G of
;;;       linear isometric mappings on A"; a map defined on A alone can only be affine, and only the inverses are
;;;       used of the group structure.
;;;   IS-INVARIANT-CCS(m, A, gs, B)
;;;       B is a nonempty convex subset of A, closed in the subspace A of the metric space of m, and invariant under
;;;       every member of gs.  Auxiliary: the sets the proof of Theorem 1.11 orders by inclusion.
;;; (IS-HAAR-INTEGRAL: see the end of the file.)
;;; BINDERS: aim_ aia_ aig_ aif_ aiu_ aiv_ ait_ aih_ aix_ icm_ ica_ icg_ icb_ icz_ icf_ icx_.

(def-predicate 'IS-AFFINE-ISOMETRY-GROUP '(aim_ aia_ aig_)
  (conjuncts->and
    (list
      '(SUBSET aig_ (FUN aia_ aia_))
      '(FORALL aif_ (IMPLIES (IN aif_ aig_) (FORALL aiu_ (IMPLIES (IN aiu_ aia_) (FORALL aiv_ (IMPLIES (IN aiv_ aia_)
         (FORALL ait_ (IMPLIES (IN ait_ RR) (IMPLIES (<= 0 ait_) (IMPLIES (<= ait_ 1)
           (= (aif_ ((VADD aim_) ((ACT aim_) (- 1 ait_) aiu_) ((ACT aim_) ait_ aiv_)))
              ((VADD aim_) ((ACT aim_) (- 1 ait_) (aif_ aiu_)) ((ACT aim_) ait_ (aif_ aiv_))))))))))))))
      '(FORALL aif_ (IMPLIES (IN aif_ aig_) (FORALL aiu_ (IMPLIES (IN aiu_ aia_) (FORALL aiv_ (IMPLIES (IN aiv_ aia_)
         (= ((DIST (NVS-METRIC-SPACE aim_)) (aif_ aiu_) (aif_ aiv_)) ((DIST (NVS-METRIC-SPACE aim_)) aiu_ aiv_))))))))
      '(FORALL aif_ (IMPLIES (IN aif_ aig_) (FORSOME aih_ (AND (IN aih_ aig_)
         (FORALL aix_ (IMPLIES (IN aix_ aia_) (= (aif_ (aih_ aix_)) aix_))))))))))
(notation! 'IS-AFFINE-ISOMETRY-GROUP 'kind 'predicate 'arity 3
           'english "$3 is a group of affine isometries of $2 in the normed space $1")

(def-predicate 'IS-INVARIANT-CCS '(icm_ ica_ icg_ icb_)
  (conjuncts->and
    (list
      '(SUBSET icb_ ica_)
      '(FORSOME icz_ (IN icz_ icb_))
      '(IS-CONVEX-SUBSET icm_ icb_)
      '(IS-CLOSED (SUBSPACE-MS (NVS-METRIC-SPACE icm_) ica_) icb_)
      '(FORALL icf_ (IMPLIES (IN icf_ icg_) (FORALL icx_ (IMPLIES (IN icx_ icb_) (IN (icf_ icx_) icb_))))))))
(notation! 'IS-INVARIANT-CCS 'kind 'predicate 'arity 4
           'english "$4 is a nonempty closed convex subset of $2 in $1 invariant under $3")

;;;   IS-HAAR-INTEGRAL(G, mu)   (target 2 of the brief; STATEMENT VOCABULARY ONLY, nothing proven about it yet)
;;;       G is a compact metric group (the structure METRIC-GROUP of isom2-vocab) and mu is a left-invariant
;;;       positive linear functional on the continuous real functions of G with mu(1) = 1: the Haar integral
;;;       of Theorem 1.9 read as a functional, as in Corollary 3.82 of th-main.  Left invariance is written
;;;       mu(x |-> f(a x)) = mu(f) for every a in G.  HAAR-INTEGRAL(G) by IOTA waits for the uniqueness theorem.
;;; BINDERS: hig_ hiu_ hix_ hia_ hif_.
(def-predicate 'IS-HAAR-INTEGRAL '(hig_ hiu_)
  (conjuncts->and
    (list
      '(IS-METRIC-GROUP hig_)
      '(IS-COMPACT (METRIC-GROUP-MS hig_))
      '(IS-POSITIVE-FUNCTIONAL (METRIC-GROUP-MS hig_) hiu_)
      '(= (hiu_ (VNB-LAMBDA hix_ (PTS (METRIC-GROUP-MS hig_)) 1)) 1)
      '(FORALL hia_ (IMPLIES (IN hia_ (PTS (METRIC-GROUP-MS hig_)))
         (FORALL hif_ (IMPLIES (IN hif_ (CONT-FNS (METRIC-GROUP-MS hig_)))
           (= (hiu_ (VNB-LAMBDA hix_ (PTS (METRIC-GROUP-MS hig_)) (hif_ ((OPR hig_) hia_ hix_)))) (hiu_ hif_)))))))))
(notation! 'IS-HAAR-INTEGRAL 'kind 'predicate 'arity 2
           'english "$2 is a Haar integral of the compact metric group $1")
