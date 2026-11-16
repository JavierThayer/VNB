;;; theorem-library/nvs-normed-ag-typing.scm -- THE NORMED GROUP OF A NORMED VECTOR SPACE
;;; (D8, 2026-11-15; the user's decision "Prove views").
;;;
;;;     normed-vector-space-as-normed-ag-is-normed-ag :
;;;       forall r. IS-NORMED-VECTOR-SPACE(r) => IS-NORMED-AG(NORMED-VECTOR-SPACE-AS-NORMED-AG r)
;;;
;;; was the `definitional' typing axiom of the view (structure-library/normed-vector-
;;; space.scm), unproven.  It is now a DEFERRED obligation of def-functor, proven here.
;;; The generic view driver (dk-view-close!, driver-kit.scm) reads every conjunct of
;;; IS-NORMED-AG off IS-NORMED-VECTOR-SPACE but one: the group norm's
;;;     ||-u|| = ||u||,
;;; which is not a law of a normed vector space but a consequence of two: (-1).u = -u
;;; (module-act-neg-one, at the module view) and homogeneity at -1, with |-1| = 1.
;;;
;;; Window: after span-bricks-proof (module-act-neg-one), rr-is-normed-field
;;; (rr-scalar-ring-one / -neg), view-typing-laws (the module view's typing); before
;;; rake-norm-metrics, the first citer.

(sp (make-wff '(FORALL r (IMPLIES (IS-NORMED-VECTOR-SPACE r) (IS-NORMED-AG (NORMED-VECTOR-SPACE-AS-NORMED-AG r))))))
(dk-peel!)
(let ((left (dk-view-close! 'NORMED-VECTOR-SPACE-AS-NORMED-AG)))
  (if (not (= (length left) 1))
      (error "nvs-normed-ag-typing: the generic driver left other than the norm of -u"
             (map (lambda (l) (expression->string (dk-goal-of l))) left)))
  (dk-focus! (car left)))
;; the leaf: vnrm(r)(vneg(r)(u)) = vnrm(r)(u)
(let* ((u  (cadr (cadr (cadr (dk-goal)))))
       (c  '((NEG (SCAL r)) (ONE (SCAL r))))
       (mv '(NORMED-VECTOR-SPACE-AS-MODULE r))
       (vu (list '(VNEG r) u)))
  ;; (-1).u = -u at the module view, read back to r's own accessors
  (fact 'normed-vector-space-as-module-is-module 'r)
  (dk-have! (list 'IN u (list 'VEC mv)) (lambda () (dk-vt--match!)))
  (dk-fact! 'module-act-neg-one mv u)
  (dk-have! (list '= (list '(ACT r) c u) vu) (lambda () (dk-vt--match!)))
  (subst (list '= vu (list '(ACT r) c u)))
  ;; the scalar is -1
  (dk-have! (list '== c '(- 1))
    (lambda ()
      (subst '(= (SCAL r) (NORMED-FIELD-AS-COMMUTATIVE-RING RR-NORMED-FIELD)))
      (mac 'rr-scalar-ring-one)
      (mac 'rr-scalar-ring-neg)
      (dk-have! '(IN 1 RR) (lambda () (arith)))
      (dk-lam-b!)
      (if (not (proof-done? *ps*)) (qrfl))))
  (subst (list '= c '(- 1)))
  ;; homogeneity at -1
  (dk-have! '(IN (- 1) (CARR (SCAL r)))
    (lambda () (subst '(= (SCAL r) (NORMED-FIELD-AS-COMMUTATIVE-RING RR-NORMED-FIELD)))
               (mac 'rr-scalar-ring-carr) (arith)))
  (subst (dk-apply! (dk-pick (lambda (h) (and (dk-head-is? h 'FORALL) (dk-contains? h 'ABS) (dk-contains? h '(ACT r))))
                             "homogeneity")
                    '(- 1) u))
  ;; |-1| = 1
  (dk-have! '(IN (- 1) RR) (lambda () (arith)))
  (dk-split! (dk-fact! 'rr-abs-def '(- 1)))
  (dk-have! '(NOT (<= 0 (- 1))) (lambda () (arith)))
  (detach! '(IMPLIES (NOT (<= 0 (- 1))) (= (ABS (- 1)) (- (- 1)))))
  (subst '(= (ABS (- 1)) (- (- 1))))
  (dk-have! (list 'IN (list '(VNRM r) u) 'RR) (lambda () (fact 'fun-apply-type-c '(VNRM r) '(VEC r) 'RR u) (ass)))
  (dk-ineq! (list 'IN (list '(VNRM r) u) 'RR)))
(qed 'normed-vector-space-as-normed-ag-is-normed-ag)
(view-typing-installed! 'NORMED-VECTOR-SPACE-AS-NORMED-AG)
