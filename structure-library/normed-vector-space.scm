;;; normed-vector-space.scm -- NORMED-VECTOR-SPACE: a real normed vector space.
;;; Vocabulary only (no proofs).  Three decisions, as agreed:
;;;
;;;  (1) SCALARS ARE THE REALS.  The scalar ring is pinned to RR-NORMED-FIELD, so the
;;;      homogeneity law can use the real absolute value |r| = abs(r).  The
;;;      general "module over a normed field" case is left for later.
;;;
;;;  (2) HOMOGENEITY IS THE NEW LAW.  A NORMED-AG already supplies nonnegativity,
;;;      definiteness, inverse-invariance and the triangle inequality for an
;;;      additive-group norm; what a vector-space norm adds is
;;;          ||r . x|| = |r| * ||x||.
;;;
;;;  (3) ONE COMPLETE IFF (design A, like IS-MODULE), plus view-as edges down to
;;;      MODULE (forget the norm) and to NORMED-AG (the additive normed group).
;;;
;;; SHAPE (7 slots = MODULE's six + the norm at slot 7, the way NORMED-AG and
;;; NORMED-FIELD carry their norm in the last slot):
;;;   1 SCAL  substructure RING                   -- the scalars (pinned RR-NORMED-FIELD)
;;;   2 VEC   carrier                              -- the vectors
;;;   3 VADD  op (CARTESIAN VEC VEC) -> VEC        -- vector addition
;;;   4 VZERO constant in VEC                      -- zero vector
;;;   5 VNEG  op VEC -> VEC                         -- vector negation
;;;   6 ACT   op (CARTESIAN (CARR SCAL) VEC) -> VEC    -- scalar action r . x
;;;   7 VNRM  op VEC -> RR                          -- the norm
;;; Slots 1-6 mirror MODULE exactly (same accessors at the same indices), so the
;;; MODULE view-as is a clean forget-the-norm projection.  The norm accessor is
;;; VNRM (a V-prefixed vector op), NOT NRM: the global NRM accessor resolves to
;;; slot 5 (NORMED-AG loads last), so reusing it here would mis-extract.
;;;
;;; Sharing MODULE's accessors is not a reason to bypass declare-structure, and
;;; this file used to think it was: it hand-built its %make-structure-def and
;;; hand-wrote its IS-X axiom, "because slots 1-6 are MODULE's".  But we declare
;;; those six in MODULE's ORDER, so def-structure re-registers SCAL -> (NTH 1 s)
;;; ... ACT -> (NTH 6 s) -- byte-identical to what module.scm installed, and
;;; register-constant! / register-operator! / install-macete! are all idempotent
;;; overwrites.  Nothing collides.  Going through the funnel buys the four things
;;; the hand-written version had to remember (and the declaration the browser and
;;; describe-structure now show, which a hand-built structure-def cannot supply).
;;;
;;; Dependencies: module.scm (MODULE accessors SCAL..ACT, A/ADD/MUL/ONE),
;;; normed-ag.scm (NORMED-AG, for the view), numeric-instances.scm (RR-NORMED-FIELD),
;;; field/abs.

;;; The vector part and the four action laws are MODULE's, verbatim; the norm
;;; slot and the four norm laws are what this adds.  SCAL is pinned to RR-NORMED-FIELD
;;; by a law (decision (1)); the substructure slot separately types it a RING.
(declare-structure NORMED-VECTOR-SPACE
  (instance-var s)
  (substructure SCAL RING)                  ; the scalars -- pinned to RR-NORMED-FIELD below
  (carriers VEC)
  (op VADD (CARTESIAN VEC VEC) VEC)
  (constant VZERO VEC)
  (op VNEG VEC VEC)
  (op ACT (CARTESIAN (CARR SCAL) VEC) VEC)
  (op VNRM VEC RR)                          ; the norm, slot 7
  ;; (VEC, VADD, VZERO, VNEG) is an abelian group
  (property is-associative VADD VEC)
  (property is-commutative VADD VEC)
  (property is-identity VADD VZERO VEC)
  (property has-inverses VADD VZERO VNEG VEC)
  ;; SCALARS ARE THE REALS (decision (1)): the homogeneity law below needs the
  ;; real absolute value.
  (law "scal(s) = rr-normed-field")
  ;; the four action axioms -- MODULE's, with `s' for the structure
  (law "forall([r_ in carr(scal(s)), x_ in vec(s), y_ in vec(s)],
          act(s)(r_, vadd(s)(x_, y_)) = vadd(s)(act(s)(r_, x_), act(s)(r_, y_)))")
  (law "forall([r_ in carr(scal(s)), s_ in carr(scal(s)), x_ in vec(s)],
          act(s)(add(scal(s))(r_, s_), x_) = vadd(s)(act(s)(r_, x_), act(s)(s_, x_)))")
  (law "forall([r_ in carr(scal(s)), s_ in carr(scal(s)), x_ in vec(s)],
          act(s)(mul(scal(s))(r_, s_), x_) = act(s)(r_, act(s)(s_, x_)))")
  (law "forall([x_ in vec(s)], act(s)(one(scal(s)), x_) = x_)")
  ;; the norm laws on VNRM : VEC -> RR
  (law "forall([x_ in vec(s)], 0 <= vnrm(s)(x_))")                      ; nonnegative
  (law "forall([x_ in vec(s)], (vnrm(s)(x_) = 0) iff (x_ = vzero(s)))") ; definite
  (law "forall([r_ in carr(scal(s)), x_ in vec(s)],
          vnrm(s)(act(s)(r_, x_)) = abs(r_) * vnrm(s)(x_))")            ; homogeneous
  (law "forall([x_ in vec(s), y_ in vec(s)],
          vnrm(s)(vadd(s)(x_, y_)) <= vnrm(s)(x_) + vnrm(s)(y_))"))     ; triangle

;;; --- view-as edges (after the shape above is registered) ---
;;; forget the norm -> the underlying real vector space (a MODULE)
(def-functor 'NORMED-VECTOR-SPACE-AS-MODULE
  'NORMED-VECTOR-SPACE '(SCAL VEC VADD VZERO VNEG ACT)
  'MODULE              '(SCAL VEC VADD VZERO VNEG ACT))

;;; the additive normed group -> NORMED-AG (so FINSUM / triangle-sum machinery
;;; over the underlying group of a normed vector space applies)
(def-functor 'NORMED-VECTOR-SPACE-AS-NORMED-AG
  'NORMED-VECTOR-SPACE '(VEC VADD VZERO VNEG VNRM)
  'NORMED-AG           '(CARR   OPR  IDEN     INV  NRM))
