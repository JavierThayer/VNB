;;; nvs-metric.scm -- the metric induced by the norm of a real normed vector
;;; space, as VOCABULARY.
;;;
;;;   NVS-METRIC-SPACE(m) = [ VEC(m), (x,y) |-> ||x (-) y|| ]
;;;
;;; Mirrors NF-METRIC-SPACE (structure-library/normed-field-metric.scm) for a
;;; normed field and NAG-METRIC-SPACE (normed-ag-metric.scm) for a normed
;;; abelian group.
;;;
;;; HOISTED HERE 2026-09-20 (batch 12-A) from theorem-library/vector-taylor-proof.scm:28,
;;; where it was declared inside a proof file.  While it lived there, every
;;; theorem stated with it had to load BELOW vector-taylor-proof -- which kept
;;; the four metric laws of a normed vector space (nvs-ms-pts,
;;; nvs-metric-distance, nvs-metric-distance-q, nvs-dist-shift) out of their
;;; home, theorem-library/nvs-norm-laws.scm, and pinned the floor of
;;; theorem-library/rake-norm-metrics.scm.  A definition is not a proof; it
;;; belongs in structure-library.
;;;
;;; The laws are PROVEN in theorem-library/nvs-norm-laws.scm (the read-offs of
;;; the two slots, and the distance in both the strict `=' and the quasi-`=='
;;; form) and theorem-library/rake-norm-metrics.scm (nvs-metric-is-ms: it IS a
;;; metric space).  Nothing is asserted here.

(def-functoid 'NVS-METRIC-SPACE '(m)
  '(LIST (VEC m)
         (VNB-LAMBDA (LIST x y) (CARTESIAN (VEC m) (VEC m)) ((VNRM m) ((VADD m) x ((VNEG m) y))))))
