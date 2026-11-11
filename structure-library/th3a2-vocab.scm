;;; th3a2-vocab.scm -- wave of 2026-11-09/10 (agent TH3-A2), wired 2026-11-10 from scratchpad/th3-1109/a2/th3a2-vocab.scm.
;;; Library: operator-algebras.

;;; ==========================================================================================
;;; TH3-A2 VOCABULARY (destination structure-library/; no proof in it).
;;; SUB-CIPS(v, kk): the subspace kk of the complex inner product space v, with the restricted
;;; operations, as a COMPLEX-INNER-PRODUCT-SPACE seven-tuple.  It is one when kk is a submodule
;;; (sub-cips-is-cips), and a Hilbert space when v is one and kk is closed (sub-cips-hilbert).
;;; The scalar slot is the CC ring view itself (as in CSIP-CIPS), so that every slot of the
;;; tuple reads off by `slot' without touching v's own accessors.
;;; The restriction of an operator t to kk is RESTRICT(t, kk) (metric-subspace-laws.scm).
;;; Binders tsbx_ tsby_ tsbc_ (used by no other file).
;;; ==========================================================================================
(def-functoid 'SUB-CIPS '(v kk)
  '(LIST (NORMED-FIELD-AS-COMMUTATIVE-RING CC-NORMED-FIELD) kk
         (VNB-LAMBDA (LIST tsbx_ tsby_) (CARTESIAN kk kk) ((VADD v) tsbx_ tsby_))
         (VZERO v)
         (VNB-LAMBDA tsbx_ kk ((VNEG v) tsbx_))
         (VNB-LAMBDA (LIST tsbc_ tsbx_) (CARTESIAN CC kk) ((ACT v) tsbc_ tsbx_))
         (VNB-LAMBDA (LIST tsbx_ tsby_) (CARTESIAN kk kk) ((IP v) tsbx_ tsby_))))
(notation! 'SUB-CIPS 'kind 'functoid 'arity 2 'english "the subspace $2 of $1 as an inner product space")
