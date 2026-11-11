;;; ccr1109a2-vocab.scm -- wave of 2026-11-09/10 (agent CCR-1109-A2), wired 2026-11-10 from scratchpad/ccr1109a2/ccr1109a2-vocab.scm.
;;; Library: analysis.

;;; ccr1109a2-vocab.scm -- COMPLETE NV DOMAINS AND THE PRINCIPAL UNITS U1(A) (CCR.pdf Section 1.8, Proposition
;;; 1.47).  DEFINITIONS ONLY; the laws are in theorem-library/ccr1109a2-nv.scm.  Agent CCR-1109-A2, wave
;;; 2026-11-09.  Destination: structure-library/ccr1109a2-vocab.scm.  Library: analysis (beside ccr2-vocab).
;;; Load window: after structure-library/ccr2-vocab (IS-NV-DOMAIN) and metric-completeness (IS-COMPLETE).
;;;
;;;   IS-COMPLETE-NV-DOMAIN(K, A)  A an NV domain inside K, complete as a subspace of the metric space of K
;;;                                (the convention of IS-COMPACT-NV-DOMAIN, ccr2-vocab)
;;;   NV-U1(K, A)                  U1(A) = {x in A : |x - 1| < 1}
;;; Binders c2*_.

(def-predicate 'IS-COMPLETE-NV-DOMAIN '(c2k_ c2a_)
  '(AND (IS-NV-DOMAIN c2k_ c2a_)
        (IS-COMPLETE (SUBSPACE-MS (NF-METRIC-SPACE c2k_) c2a_))))
(notation! 'IS-COMPLETE-NV-DOMAIN 'kind 'predicate 'arity 2
           'english "$2 is a complete non-archimedean valued domain inside the field $1")

(def-functoid 'NV-U1 '(c2k_ c2a_)
  '(SEP c2x_ c2a_ (< ((FNRM c2k_) ((ADD c2k_) c2x_ ((NEG c2k_) (ONE c2k_)))) 1)))
(notation! 'NV-U1 'kind 'functoid 'arity 2 'english "the principal units of $2")
