;;; frechet-metric.scm -- the METRIC of a seminormed space whose seminorm family is
;;; COUNTABLE (Thayer, "Analise Funcional e Teoria Espectral", Ch. 8 s.4, Prop. 8.24).
;;; Added 2026-10-10 (batch TVS-1).  Vocabulary only: the theorems are in
;;; theorem-library/frechet-metric.scm.
;;;
;;; THE BOOK'S CONSTRUCTION.  For a separating family (p_i), i in N, of seminorms on a
;;; vector space E (Def. 8.22 with Gamma enumerated; here IS-SEMINORM-FAMILY(fld, m, fam)
;;; of frechet-open-mapping.scm, p_i = fam(i), fld the scalar field), Prop. 8.24 (a) puts
;;;
;;;     d(xi, eta) = SUM_i 2^-i min(1, p_i(xi - eta)).
;;;
;;; HOW IT IS BUILT HERE.  The tree already has the construction one level up:
;;; C-METRIC-SPACE (structure-library/c-metric-space.scm) is a set carrying a countable
;;; separating family of PSEUDOMETRICS, and C-METRIC(s) is its canonical metric
;;;
;;;     D(a, b) = SUM_k 2^-(k+1) min(1, d_k(a, b)),
;;;
;;; already PROVEN to be a metric space (`c-metric-is-metric-space',
;;; theorem-library/c-metric-is-metric.scm).  A seminorm family gives such a family of
;;; pseudometrics, d_k(x, y) = p_k(x - y).  So the space is the composite
;;;
;;;     FR-C-SPACE(m, fam)      = [VEC m, k |-> ((x, y) |-> fam(k)(x - y))]
;;;     FR-METRIC-SPACE(m, fam) = C-METRIC(FR-C-SPACE(m, fam))
;;;     FR-METRIC(m, fam)       = DIST(FR-METRIC-SPACE(m, fam))
;;;
;;; and every metric fact about it is one citation of the C-METRIC development once
;;; `frm-c-space-is-c-metric-space' (IS-SEMINORM-FAMILY => IS-C-METRIC-SPACE of the
;;; family's space) is proven.  x - y is (VADD m)(x, (VNEG m)(y)), as fr-sub in
;;; frechet-open-mapping.scm writes it.
;;;
;;; THE SERIES AND THE WEIGHTS.  The distance is the sum of a real series named the way
;;; C-METRIC-W names it -- IOTA over SERIES-CONVERGES-TO, which `series-limit-iota'
;;; identifies with SERIES-LIMIT -- because that is the functoid the proven metric laws
;;; are stated with; a second spelling of the same sum would need its own laws.  The
;;; value theorem `frm-metric-value' states the book's formula with SERIES-LIMIT.  The
;;; weights are 2^-(k+1) for k in NN = {0, 1, 2, ...}, i.e. the book's 2^-i with the
;;; index starting at 1; the dyadic term is spelled exactly as in C-METRIC, so that
;;; `product-metric-default-summable' covers it.
;;;
;;; Binders of the constructed lambdas are `frk_', `fru_', `frv_': names no predicate
;;; body binds (CLAUDE.md: a term the driver builds must use binders nothing else binds).
;;;
;;; THE FIELD.  Since 2026-10-10 the seminorm vocabulary takes the scalar field as a
;;; parameter (IS-SEMINORM(fld, m, p), the user's decision on the TVS-1 finding).  The
;;; three functoids below do not: the metric is built from the seminorm values alone,
;;; as FR-CONV and FR-CAUCHY are, and the field enters only through the hypothesis
;;; IS-SEMINORM-FAMILY(fld, m, fam) of the theorems.
;;;
;;; Loads after frechet-open-mapping (IS-SEMINORM-FAMILY, FR-CONV, FR-CAUCHY) and
;;; c-metric-space (C-METRIC-SPACE, C-METRIC).

;;; The countable family of pseudometrics of a seminorm family, as a C-METRIC-SPACE
;;; tuple: carrier VEC m, k-th pseudometric (x, y) |-> fam(k)(x - y).
(def-functoid 'FR-C-SPACE '(m fam)
  '(LIST (VEC m)
         (VNB-LAMBDA frk_ NN
           (VNB-LAMBDA (LIST fru_ frv_) (CARTESIAN (VEC m) (VEC m))
             ((fam frk_) ((VADD m) fru_ ((VNEG m) frv_)))))))
(notation! 'FR-C-SPACE 'kind 'functoid 'arity 2
           'english "the pseudometric family of the seminorms $2 on $1")

;;; The metric space of Prop. 8.24 (a): the canonical metric of that family.
(def-functoid 'FR-METRIC-SPACE '(m fam)
  '(C-METRIC (FR-C-SPACE m fam)))
(notation! 'FR-METRIC-SPACE 'kind 'functoid 'arity 2
           'english "the metric space of the seminorms $2 on $1")

;;; Its distance function d.
(def-functoid 'FR-METRIC '(m fam)
  '(DIST (FR-METRIC-SPACE m fam)))
(notation! 'FR-METRIC 'kind 'functoid 'arity 2
           'english "the metric of the seminorms $2 on $1")

