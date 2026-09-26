;;; hom-views.scm -- a view's action on arrows.
;;;
;;; A def-functor view V : NAME -> TARGET acts on arrows by the IDENTITY on the
;;; underlying map:  IS-HOM-NAME(a, b, f) => IS-HOM-TARGET(V(a), V(b), f).
;;; For 17 of the 19 views in the tree that theorem is ALREADY PROVEN, under the
;;; name V-functorial, by the generic driver of structure-library/functoriality.scm
;;; (loaded last): ring-additive-ag, ring-multiplicative-monoid,
;;; abelian-group-as-monoid, commutative-ring-additive-ag,
;;; commutative-ring-multiplicative-cm, field-additive-ag, field-as-integral-domain,
;;; field-as-euclidean-ring, normed-field-additive-ag,
;;; normed-field-as-commutative-ring, normed-field-as-integral-domain,
;;; module-vector-ag, normed-vector-space-as-module,
;;; normed-vector-space-as-normed-ag, normed-ag-as-abelian-group,
;;; complex-inner-product-space-as-module, measure-space-as-measurable-space
;;; (each `-functorial').  A second copy named hom-V would be a proven duplicate
;;; (proven-duplicate-audit), so none is stated here.
;;;
;;; The two that driver skips:
;;;
;;;   RINGOID-AS-RING -- its source's hom is an OVERRIDE (declare-hom!), which
;;;   functoriality.scm does not touch.  The override's body CONTAINS the ring
;;;   hom of the views as a conjunct, so the theorem is a projection, stated here
;;;   under the tree's naming: ringoid-as-ring-functorial.
;;;
;;;   FIELD-MULTIPLICATIVE-GROUP -- its target carrier is FIELD's DERIVED
;;;   NON-ZERO, so the arrow is not f but its restriction
;;;   VNB-LAMBDA x (NON-ZERO a) (f x); the typing lemma it was owed (a field hom
;;;   sends NON-ZERO(a) into NON-ZERO(b)) is now PROVEN, as hom-field-non-zero
;;;   (hom-laws.scm).  The functoriality theorem itself is not stated: it is a
;;;   page of view read-offs (CARR/OPR/IDEN/INV of the view), not one line --
;;;   batch 33 report.
;;;
;;; Window: after hom-laws.scm is not needed (it cites nothing of it); after
;;; ringoid.scm (IS-HOM-RINGOID) and interactive/proof-debt.  Batch 33 (2026-09-25).

(sp (make-wff '(FORALL a (FORALL b (FORALL f
      (IMPLIES (IS-HOM-RINGOID a b f)
        (IS-HOM-RING (RINGOID-AS-RING a) (RINGOID-AS-RING b) f)))))))
(dk-peel!)
(mac-h 'IS-HOM-RINGOID-def (dk-pick (dk-head? 'IS-HOM-RINGOID) "the ringoid hom"))
(dk-split-all!)
(ass)
(if (proof-done? *ps*) (qed 'ringoid-as-ring-functorial)
    (error "hom-views: failed to prove ringoid-as-ring-functorial"))
