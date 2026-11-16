;;; theorem-library/cna-normed-ag-typing.scm -- THE NORMED GROUPS OF A COMPLEX NORMED
;;; ALGEBRA AND OF A UNITAL BANACH ALGEBRA (D8, 2026-11-15; the user's decision "Prove views").
;;;
;;;     cna-as-normed-ag-is-normed-ag  and  uba-as-normed-ag-is-normed-ag
;;;
;;; were `definitional' typing axioms of structure-library/ba-vocab.scm, unproven.  Both
;;; are DEFERRED obligations of def-functor, proven here.  For a complex normed algebra
;;; the generic view driver (dk-view-close!, driver-kit.scm) reads every conjunct of
;;; IS-NORMED-AG off the structure but ||-u|| = ||u||, which follows from (-1).u = -u
;;; (module-act-neg-one at the module view), homogeneity at -1 and |-1| = |1| = 1
;;; (cc-magnitude-neg, cc-magnitude-one).  A unital Banach algebra's normed group is then
;;; the generic driver's, through the complex normed algebra its first law names.
;;;
;;; Window: after ba-vocab (the views), ca-lft-cayley (cc-magnitude-one); before
;;; structure-library/functoriality, which cites both typings.

(sp (make-wff '(FORALL r (IMPLIES (IS-COMPLEX-NORMED-ALGEBRA r) (IS-NORMED-AG (CNA-AS-NORMED-AG r))))))
(dk-peel!)
(let ((left (dk-view-close! 'CNA-AS-NORMED-AG)))
  (if (not (= (length left) 1))
      (error "cna-normed-ag-typing: the generic driver left other than the norm of -u"
             (map (lambda (l) (expression->string (dk-goal-of l))) left)))
  (dk-focus! (car left)))
(let* ((u  (cadr (cadr (cadr (dk-goal)))))
       (c  '((NEG (SCAL r)) (ONE (SCAL r))))
       (mv '(CNA-AS-MODULE r))
       (vu (list '(VNEG r) u)))
  (fact 'cna-as-module-is-module 'r)
  (dk-have! (list 'IN u (list 'VEC mv)) (lambda () (dk-vt--match!)))
  (dk-fact! 'module-act-neg-one mv u)
  (dk-have! (list '= (list '(ACT r) c u) vu) (lambda () (dk-vt--match!)))
  (subst (list '= vu (list '(ACT r) c u)))
  (fact 'cc-is-normed-field)
  (dk-have! (list '== c '(- 1))
    (lambda ()
      (subst '(= (SCAL r) (NORMED-FIELD-AS-COMMUTATIVE-RING CC-NORMED-FIELD)))
      (mac 'normed-field-ring-view-one)
      (mac 'normed-field-ring-view-neg)
      (slot 'ONE)
      (slot 'NEG)
      (dk-have! '(IN 1 CC) (lambda () (arith)))
      (dk-lam-b!)
      (if (not (proof-done? *ps*)) (qrfl))))
  (subst (list '= c '(- 1)))
  (dk-have! '(IN (- 1) CC) (lambda () (arith)))
  (dk-have! '(IN (- 1) (CARR (SCAL r))) (lambda () (subst '(= (CARR (SCAL r)) CC)) (ass)))
  (subst (dk-apply! (dk-pick (lambda (h) (and (dk-head-is? h 'FORALL) (dk-contains? h 'MAGNITUDE) (dk-contains? h '(ACT r))))
                             "homogeneity")
                    '(- 1) u))
  (dk-have! '(IN 1 CC) (lambda () (arith)))
  (subst (dk-fact! 'cc-magnitude-neg 1))
  (subst (dk-fact! 'cc-magnitude-one))
  (dk-have! (list 'IN (list '(VNRM r) u) 'RR) (lambda () (fact 'fun-apply-type-c '(VNRM r) '(VEC r) 'RR u) (ass)))
  (dk-ineq! (list 'IN (list '(VNRM r) u) 'RR)))
(qed 'cna-as-normed-ag-is-normed-ag)
(view-typing-installed! 'CNA-AS-NORMED-AG)

;;; the unital Banach algebra's normed group: generic, through the typing above
(dk-view-typing! 'UBA-AS-NORMED-AG)
