;;; rake-rr-bounded-ms.scm -- the three facts about the constant RR-BOUNDED-MS
;;; (rake batch 5, integrator, 2026-09-18).
;;;
;;; RR-BOUNDED-MS was declared by a `def-functoid' with an EMPTY parameter list,
;;; which installed an unfold macete whose left-hand side was (RR-BOUNDED-MS ()),
;;; a term nothing mentions; the constant was therefore uninterpreted and the three
;;; supports about it said nothing about BDD-METRIC(RR-MS) (found by batch S).  It is
;;; now a `def-constant' with the defining quasi-equation `rr-bounded-ms-def'
;;; (structure-library/bounded-metric.scm), and each support is one rewrite along
;;; that equation plus one citation of the fact batch S proved at the intended term
;;; (theorem-library/rake-metric-constructions.scm).
;;;
;;; Window: [rake-metric-constructions + 1, end).  Statements copied literally from
;;; structure-library/bounded-metric.scm.

(define rbm-def '(== RR-BOUNDED-MS (BDD-METRIC RR-MS)))

(define (rbm-run! name stmt cited)
  (sp (make-wff stmt))
  (fact 'rr-bounded-ms-def)
  (subst rbm-def)
  (fact cited)
  (ass)
  (qed name)
  (topic! name 'constructions))

(rbm-run! 'rr-bounded-ms-is-metric-space
  '(IS-METRIC-SPACE RR-BOUNDED-MS)
  'bdd-rr-ms-is-metric-space)

(rbm-run! 'rr-bounded-ms-bounded
  '(FORALL x (IMPLIES (IN x RR)
     (FORALL y (IMPLIES (IN y RR)
       (< ((DIST RR-BOUNDED-MS) x y) 1)))))
  'bdd-rr-ms-bounded)

(rbm-run! 'rr-bounded-equivalent
  '(AND (IS-CONTINUOUS RR-MS RR-BOUNDED-MS (VNB-LAMBDA x RR x))
        (IS-CONTINUOUS RR-BOUNDED-MS RR-MS (VNB-LAMBDA x RR x)))
  'bdd-rr-equivalent)
