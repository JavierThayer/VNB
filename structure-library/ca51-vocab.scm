;;; ca51-vocab.scm -- local compactness and exhaustions by compact sets (CA-51, 2026-10-26).
;;; DEFINITIONS ONLY.  Destination: structure-library/ca51-vocab.scm, library analysis.
;;; Dependencies: metric-topology (CLOSED-BALL, BALL), compactness (IS-COMPACT),
;;; metric-subspace (SUBSPACE-MS).  Load window: after structure-library/separable and
;;; structure-library/metric-subspace; before theorem-library/ca51-compact-laws.
;;;
;;; Compactness of a SUBSET A of a metric space s is the tree's existing notion,
;;; IS-COMPACT(SUBSPACE-MS(s, A)).  Separability is the tree's IS-SEPARABLE (a dense
;;; sequence, structure-library/separable.scm); it is not redefined.
;;;
;;; IS-LOCALLY-COMPACT(s): s is a metric space and every point has a compact closed
;;; ball of positive radius about it (the user's form, 2026-10-26).
(def-predicate 'IS-LOCALLY-COMPACT '(lcs_)
  '(AND (IS-METRIC-SPACE lcs_)
        (FORALL lca_ (IMPLIES (IN lca_ (PTS lcs_))
          (FORSOME lcr_ (AND (POS-RR lcr_)
                             (IS-COMPACT (SUBSPACE-MS lcs_ (CLOSED-BALL lcs_ lca_ lcr_)))))))))

(notation! 'IS-LOCALLY-COMPACT 'kind 'predicate 'arity 1
           'english "$1 is locally compact")

;;; IS-COMPACT-EXHAUSTION(s, K): K = (K_n) is an exhaustive sequence of compact subsets
;;; of the metric space s (Lemma 5.1 of the complex analysis notes):
;;;   (1) K is a sequence of subsets of PTS(s);
;;;   (2) every K_n is compact;
;;;   (3) K_n lies in the interior of K_{n+1}, in the UNIFORM form: there is r > 0 such
;;;       that the open ball of radius r about every point of K_n lies in K_{n+1}
;;;       (for a compact K_n this is equivalent to K_n subset interior(K_{n+1}); the
;;;       INTERIOR functoid is deliberately not used);
;;;   (4) the K_n cover PTS(s);
;;;   (5) every compact subset of s lies in some K_n (the notes' "exhaustive").
(def-predicate 'IS-COMPACT-EXHAUSTION '(ces_ cek_)
  '(AND (IS-METRIC-SPACE ces_)
   (AND (IN cek_ (FUN NN (POWER (PTS ces_))))
   (AND (FORALL cen_ (IMPLIES (IN cen_ NN) (IS-COMPACT (SUBSPACE-MS ces_ (cek_ cen_)))))
   (AND (FORALL cen_ (IMPLIES (IN cen_ NN)
          (FORSOME cer_ (AND (POS-RR cer_)
            (FORALL cey_ (IMPLIES (IN cey_ (cek_ cen_))
              (SUBSET (BALL ces_ cey_ cer_) (cek_ (+ cen_ 1)))))))))
   (AND (FORALL cex_ (IMPLIES (IN cex_ (PTS ces_))
          (FORSOME cen_ (AND (IN cen_ NN) (IN cex_ (cek_ cen_))))))
        (FORALL cea_ (IMPLIES (SUBSET cea_ (PTS ces_))
          (IMPLIES (IS-COMPACT (SUBSPACE-MS ces_ cea_))
            (FORSOME cen_ (AND (IN cen_ NN) (SUBSET cea_ (cek_ cen_)))))))))))))

(notation! 'IS-COMPACT-EXHAUSTION 'kind 'predicate 'arity 2
           'english "$2 is an exhaustive sequence of compact subsets of $1")
