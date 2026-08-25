;;; c-metric-space.scm -- C-METRIC-SPACE, a set carrying a COUNTABLE FAMILY OF
;;; PSEUDOMETRICS that separates points, and the CANONICAL METRIC it induces.
;;;
;;;     s = (X, d_*),   d_* : NN -> (X x X -> RR),
;;;     each d_k a pseudometric on X,
;;;     and the family SEPARATES:  (forall k. d_k(u,v) = 0)  =>  u = v.
;;;
;;;     C-METRIC(s) = (X, D),   D(a,b) = SUM_k 2^-(k+1) min(1, d_k(a,b)).
;;;
;;; WHY THIS IS A STRUCTURE AND NOT AN ARGUMENT LIST.  The tree already has the
;;; predicate IS-COUNTABLE-PSEUDOMETRIC-FAMILY(fam, ground)
;;; (structure-library/pseudometric.scm) -- a family and its carrier passed as two
;;; separate arguments, so that nothing names the PAIR and no accessor reads a
;;; component out of it.  A mathematical structure must be a `declare-structure':
;;; this is that declaration, and `c-pseudo-family-is-family' (below) is the one
;;; bridge lemma back to the argument-list form, so the gauge topology
;;; PSEUDO-GAUGE-TOP and the predicate IS-GAUGE-COUNTABLE apply to it unchanged.
;;;
;;; WHAT declare-structure CAN AND CANNOT SAY HERE.  The op clause
;;;     (op DISTS NN (FUN (CARTESIAN PTS PTS) RR))
;;; expresses the SEQUENCE OF DISTANCE FUNCTIONS exactly -- expand-accessors
;;; rewrites the compound range as well as the domain, giving the conjunct
;;;     DISTS(s) in FUN(NN, FUN(CARTESIAN(PTS s, PTS s), RR)),
;;; and the surface application dists(s)(k)(u,v) parses to (((DISTS s) k) u v),
;;; which is what substituting dst := ((DISTS s) k) into `is-pseudometric' gives.
;;; What it CANNOT say is "each d_k is a pseudometric": a (property PRED ACC ...)
;;; clause applies a named operation-property DIRECTLY to accessors and admits no
;;; quantifier over the index, so `(property is-pseudometric DISTS PTS)' would be
;;; the false claim that the SEQUENCE is a pseudometric.  The indexed form is a
;;; (law ...) clause, which is the intended escape hatch (MODULE's action axioms
;;; are of the same kind).  The separation condition is a second law: it is not a
;;; property of any one d_k but of the family.
;;;
;;; THE TRUNCATION IS min(1,.), NOT d/(1+d).  The tree's bounded transform is
;;; BDD-METRIC (structure-library/bounded-metric.scm), and it does not apply here:
;;; BDD-METRIC is a functoid on a metric-space STRUCTURE -- it reads PTS and DIST
;;; slots -- and every fact about it (bdd-metric-bounded, bdd-metric-is-metric-space)
;;; is guarded on IS-METRIC-SPACE, while the k-th entry of DISTS(s) is a bare
;;; FUNCTION and is only a PSEUDOmetric.  Using it would mean wrapping each d_k in
;;; a one-off structure and proving a pseudometric analogue of the whole bdd-fn-*
;;; family.  min(1,.) needs none of that: it is total on RR, the five laws are
;;; PROVEN (theorem-library/rr-min-basics.scm), and -- the operational point --
;;; it introduces no `recip', which `crs' declines on.  It is also the transform
;;; the user asked for.
;;;
;;; THE WEIGHT IS THE CANONICAL DYADIC ONE, 2^-(k+1), spelled with the SAME
;;; S-expression as PRODUCT-METRIC's default weight, so that the PROVEN
;;; `product-metric-default-summable' (theorem-library/dyadic-weights.scm) --
;;; SUMMABLE-WEIGHT of exactly that term -- discharges the summability guard by
;;; citation and no geometric series is re-derived.  Writing 2^-k instead would
;;; scale every distance by 2 and buy nothing.  `power' is not used with a
;;; negative exponent anywhere in the tree; the weight is written as a quotient.
;;;
;;; Loads after product-metric (SUMMABLE-WEIGHT), power-series
;;; (SERIES-CONVERGES-TO) and pseudometric (PSEUDOMETRIC-SPACE, the gauge
;;; vocabulary).

;;; -----------------------------------------------------------------------
;;; The structure.  Carrier PTS (shared with METRIC-SPACE / PSEUDOMETRIC-SPACE /
;;; TOP-SPACE at slot 1, as one-name-one-slot requires); DISTS at slot 2.

(declare-structure C-METRIC-SPACE
  (instance-var s)
  (carriers PTS)
  (op DISTS NN (FUN (CARTESIAN PTS PTS) RR))
  ;; each member of the family is a pseudometric on the carrier
  (law "forall([k_ in nn], is-pseudometric(dists(s)(k_), pts(s)))")
  ;; the family SEPARATES POINTS -- what upgrades the canonical pseudometric
  ;; to a metric, and the only hypothesis rung 4 spends
  (law "forall([u in pts(s), v in pts(s)],
          forall([k_ in nn], dists(s)(k_)(u, v) = 0) implies u = v)"))

(notation! 'IS-C-METRIC-SPACE 'noun "countably-metrised space" 'article "a")
(notation! 'DISTS 'kind 'functoid 'arity 1
           'english "the pseudometric family of $1")

;;; -----------------------------------------------------------------------
;;; The canonical metric.
;;;
;;; C-METRIC-W(s, w) is the weighted form -- every theorem about the
;;; construction is stated over a general SUMMABLE-WEIGHT w, exactly as
;;; PRODUCT-METRIC-W is, so that nothing in the argument depends on the
;;; particular weights and the canonical instance is one instantiation.
;;;
;;; The distance is named by IOTA over the series limit, the same device
;;; PRODUCT-METRIC-W uses; the description is licensed by convergence
;;; (c-metric-summable) plus limit uniqueness (rr-limit-unique, PROVEN in
;;; theorem-library/dominated-convergence.scm).

(def-functoid 'C-METRIC-W '(s w)
  '(LIST (PTS s)
         (VNB-LAMBDA (LIST u v) (CARTESIAN (PTS s) (PTS s))
           (IOTA L (SERIES-CONVERGES-TO
                     (VNB-LAMBDA k NN (* (w k) (min 1 (((DISTS s) k) u v))))
                     L)))))
(notation! 'C-METRIC-W 'kind 'functoid 'arity 2
           'english "the canonical metric of $1 with weights $2")

;;; The canonical instance: weights 2^-(k+1), so the diameter is at most 1.
(def-functoid 'C-METRIC '(s)
  '(C-METRIC-W s (VNB-LAMBDA n NN (/ 1 (power 2 (+ n 1))))))
(notation! 'C-METRIC 'kind 'functoid 'arity 1
           'english "the canonical metric space of $1")

;;; -----------------------------------------------------------------------
;;; The bridge to the argument-list vocabulary of pseudometric.scm: the k-th
;;; pseudometric, packaged as a PSEUDOMETRIC-SPACE on the common carrier.  With
;;; it, IS-COUNTABLE-PSEUDOMETRIC-FAMILY, PSEUDO-GAUGE-TOP and IS-GAUGE-COUNTABLE
;;; all apply to a C-METRIC-SPACE without restating them.

(def-functoid 'C-PSEUDO-FAMILY '(s)
  '(VNB-LAMBDA k NN (LIST (PTS s) ((DISTS s) k))))
(notation! 'C-PSEUDO-FAMILY 'kind 'functoid 'arity 1
           'english "the family of pseudometric spaces of $1")
