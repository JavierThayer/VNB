;;; normed-vector-space.scm -- NORMED-VECTOR-SPACE: a real normed vector space.
;;; Vocabulary only (no proofs).  Three decisions, as agreed:
;;;
;;;  (1) SCALARS ARE THE REALS.  The scalar ring is pinned to RR-RING, so the
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
;;;   1 SCAL  substructure RING                   -- the scalars (pinned RR-RING)
;;;   2 VEC   carrier                              -- the vectors
;;;   3 VADD  op (CARTESIAN VEC VEC) -> VEC        -- vector addition
;;;   4 VZERO constant in VEC                      -- zero vector
;;;   5 VNEG  op VEC -> VEC                         -- vector negation
;;;   6 ACT   op (CARTESIAN (A SCAL) VEC) -> VEC    -- scalar action r . x
;;;   7 VNRM  op VEC -> RR                          -- the norm
;;; Slots 1-6 mirror MODULE exactly (same accessors at the same indices), so the
;;; MODULE view-as is a clean forget-the-norm projection.  The norm accessor is
;;; VNRM (a V-prefixed vector op), NOT NRM: the global NRM accessor resolves to
;;; slot 5 (NORMED-AG loads last), so reusing it here would mis-extract.
;;;
;;; Dependencies: module.scm (MODULE accessors SCAL..ACT, A/ADD/MUL/ONE),
;;; normed-ag.scm (NORMED-AG, for the view), numeric-instances.scm (RR-RING),
;;; field/abs.

(fluid-let ((*current-provenance* 'definitional))

  ;; --- register the shape; only VNRM is a new accessor (1-6 are MODULE's) ---
  (hash-table-set! *structure-table* 'NORMED-VECTOR-SPACE
    (%make-structure-def 'NORMED-VECTOR-SPACE
      '((SCAL  substructure RING)
        (VEC   carrier)
        (VADD  op (CARTESIAN VEC VEC) VEC)
        (VZERO constant VEC)
        (VNEG  op VEC VEC)
        (ACT   op (CARTESIAN (CARR SCAL) VEC) VEC)
        (VNRM  op VEC RR))
      '()                                ; IS-NORMED-VECTOR-SPACE is hand-written
      (current-load-pathname)))

  (register-constant! 'VNRM 'accessor)
  (install-accessor-macete! 'VNRM 7)

  ;; --- the complete IS-NORMED-VECTOR-SPACE definition (design A) ---
  (theory-add-axiom! *current-theory* 'IS-NORMED-VECTOR-SPACE
    `(FORALL m
       (IFF (IS-NORMED-VECTOR-SPACE m)
         ,(conjuncts->and
            (list
              ;; shape; scalars are the reals
              '(= (LENGTH m) 7)
              '(= (SCAL m) RR-RING)
              '(IN (VEC m) SET)
              '(IN (VADD m) (FUN (CARTESIAN (VEC m) (VEC m)) (VEC m)))
              '(IN (VZERO m) (VEC m))
              '(IN (VNEG m) (FUN (VEC m) (VEC m)))
              '(IN (ACT m) (FUN (CARTESIAN (CARR (SCAL m)) (VEC m)) (VEC m)))
              '(IN (VNRM m) (FUN (VEC m) RR))
              ;; vector part (VEC, VADD, VZERO, VNEG) is an abelian group
              '(is-associative (VADD m) (VEC m))
              '(is-commutative (VADD m) (VEC m))
              '(is-identity (VADD m) (VZERO m) (VEC m))
              '(has-inverses (VADD m) (VZERO m) (VNEG m) (VEC m))
              ;; (1) action distributes over vector addition
              '(FORALL r_ (IMPLIES (IN r_ (CARR (SCAL m)))
                 (FORALL x_ (IMPLIES (IN x_ (VEC m))
                   (FORALL y_ (IMPLIES (IN y_ (VEC m))
                     (= ((ACT m) r_ ((VADD m) x_ y_))
                        ((VADD m) ((ACT m) r_ x_) ((ACT m) r_ y_)))))))))
              ;; (2) action distributes over ring addition
              '(FORALL r_ (IMPLIES (IN r_ (CARR (SCAL m)))
                 (FORALL s_ (IMPLIES (IN s_ (CARR (SCAL m)))
                   (FORALL x_ (IMPLIES (IN x_ (VEC m))
                     (= ((ACT m) ((ADD (SCAL m)) r_ s_) x_)
                        ((VADD m) ((ACT m) r_ x_) ((ACT m) s_ x_)))))))))
              ;; (3) action compatible with ring multiplication
              '(FORALL r_ (IMPLIES (IN r_ (CARR (SCAL m)))
                 (FORALL s_ (IMPLIES (IN s_ (CARR (SCAL m)))
                   (FORALL x_ (IMPLIES (IN x_ (VEC m))
                     (= ((ACT m) ((MUL (SCAL m)) r_ s_) x_)
                        ((ACT m) r_ ((ACT m) s_ x_)))))))))
              ;; (4) unital
              '(FORALL x_ (IMPLIES (IN x_ (VEC m))
                 (= ((ACT m) (ONE (SCAL m)) x_) x_)))
              ;; --- norm laws on VNRM : VEC -> RR ---
              ;; nonnegative
              '(FORALL x_ (IMPLIES (IN x_ (VEC m))
                 (<= 0 ((VNRM m) x_))))
              ;; definite:  ||x|| = 0  iff  x = 0
              '(FORALL x_ (IMPLIES (IN x_ (VEC m))
                 (IFF (= ((VNRM m) x_) 0) (= x_ (VZERO m)))))
              ;; homogeneous (the law beyond a group norm):  ||r.x|| = |r| ||x||
              '(FORALL r_ (IMPLIES (IN r_ (CARR (SCAL m)))
                 (FORALL x_ (IMPLIES (IN x_ (VEC m))
                   (= ((VNRM m) ((ACT m) r_ x_))
                      (* (abs r_) ((VNRM m) x_)))))))
              ;; subadditive (triangle):  ||x+y|| <= ||x|| + ||y||
              '(FORALL x_ (IMPLIES (IN x_ (VEC m))
                 (FORALL y_ (IMPLIES (IN y_ (VEC m))
                   (<= ((VNRM m) ((VADD m) x_ y_))
                       (+ ((VNRM m) x_) ((VNRM m) y_))))))))))))

  ;; --- NORMED-VECTOR-SPACE as the proper class ---
  (theory-add-axiom! *current-theory* 'NORMED-VECTOR-SPACE-class
    '(FORALL s (IFF (IN s NORMED-VECTOR-SPACE) (IS-NORMED-VECTOR-SPACE s)))))

;;; --- view-as edges (after the shape above is registered) ---
;;; forget the norm -> the underlying real vector space (a MODULE)
(def-view-as 'NORMED-VECTOR-SPACE-AS-MODULE
  'NORMED-VECTOR-SPACE '(SCAL VEC VADD VZERO VNEG ACT)
  'MODULE              '(SCAL VEC VADD VZERO VNEG ACT))

;;; the additive normed group -> NORMED-AG (so FINSUM / triangle-sum machinery
;;; over the underlying group of a normed vector space applies)
(def-view-as 'NORMED-VECTOR-SPACE-AS-NORMED-AG
  'NORMED-VECTOR-SPACE '(VEC VADD VZERO VNEG VNRM)
  'NORMED-AG           '(CARR   MUL  ID     INV  NRM))
