;;; product2-vocab.scm -- THE BINARY PRODUCT OF TWO METRIC SPACES (definitions only).
;;;
;;;   PRODUCT2-MS(s, t)   the metric space on CARTESIAN(PTS s, PTS t) with the MAX
;;;                       metric  d([a,b],[a',b']) = max(d_s(a,a'), d_t(b,b')).
;;;
;;; The max metric is the standard choice (it induces the product topology, and its
;;; triangle inequality is the coordinate triangle inequalities plus max <= sum).
;;; The tree had only the COUNTABLE product PRODUCT-METRIC(ms) of a sequence of
;;; spaces, over sequences (structure-library/product-metric.scm); a pair is not a
;;; sequence, so nothing there applies to CARTESIAN(A, B).  cc-coords-laws.scm
;;; records the gap for CARTESIAN(RR, RR).
;;;
;;; The distance is a lambda over pairs of PAIRS, read through NTH: a point of the
;;; product is any w in CARTESIAN(PTS s, PTS t), and cartesian-pair-eq writes it
;;; as [NTH 1 w, NTH 2 w].  MAX is the defined real maximum (number-systems.scm,
;;; rr-max-def), certified defined on real arguments (*pi-arith-total-heads*).
;;;
;;; Every law is PROVEN in theorem-library/product2-laws.scm; nothing is asserted
;;; here.  Library: analysis (it needs metric-space, MAX on RR, CARTESIAN; all are
;;; core or analysis).  Load slot: anywhere after structure-library/metric-subspace.
;;; Binders p2u_ / p2v_ are used by nothing else.

(def-functoid 'PRODUCT2-MS '(s t)
  '(LIST (CARTESIAN (PTS s) (PTS t))
         (VNB-LAMBDA (LIST p2u_ p2v_)
           (CARTESIAN (CARTESIAN (PTS s) (PTS t)) (CARTESIAN (PTS s) (PTS t)))
           (max ((DIST s) (NTH 1 p2u_) (NTH 1 p2v_))
                ((DIST t) (NTH 2 p2u_) (NTH 2 p2v_))))))

(notation! 'PRODUCT2-MS 'kind 'functoid 'arity 2
           'english "the product metric space of $1 and $2")
