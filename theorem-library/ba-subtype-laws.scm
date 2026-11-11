;;; ba-subtype-laws.scm -- the refinement step of COMPLEX-BANACH-ALGEBRA, proven.
;;; COMPLEX-BANACH-ALGEBRA refines COMPLEX-NORMED-ALGEBRA (same-shape-as, plus completeness).
;;; functoriality.scm climbs a refinement chain by citing X-is-PARENT; without this step the
;;; functoriality of UBA-AS-CBA and NUIBA-AS-CBA (target COMPLEX-BANACH-ALGEBRA) was not proved.
;;; Must load after structure-library/ba-vocab and before structure-library/functoriality.
(sp (make-wff '(FORALL s (IMPLIES (IS-COMPLEX-BANACH-ALGEBRA s) (IS-COMPLEX-NORMED-ALGEBRA s)))))
(dk-peel!)
(mac-h 'is-complex-banach-algebra-def '(IS-COMPLEX-BANACH-ALGEBRA s))
(dk-split-all!)
(ass)
(qed 'complex-banach-algebra-is-complex-normed-algebra)
