;;; sip-vocab.scm -- SEMI-INNER-PRODUCT SPACES (SIP-1, 2026-10-18).  Vocabulary only.
;;;
;;; THE DESIGN IS THE USER'S (2026-10-18, scratchpad/triage/SIP-1.md):
;;;   * REAL IS THE DEFAULT.  The notes (topological-vector-space.pdf, Ch. 1 s.3:
;;;     "In these notes we assume by default that all Hilbert spaces are real")
;;;     treat a complex space as a real one with an extra piece of structure.
;;;   * The degenerate case is a SEMI-INNER-PRODUCT SPACE: a real vector space with
;;;     a symmetric bilinear form whose diagonal is nonnegative, i.e. a POSITIVE
;;;     SEMIDEFINITE symmetric bilinear form.  (The phrase "semi-inner product" also
;;;     names Lumer's unrelated notion on normed spaces; it is not meant here.)
;;;     Definiteness is a refinement, PRE-HILBERT-SPACE, the notes' Definition 1.17.
;;;   * The quotient by the null vectors is a pre-Hilbert space.  The quotient is
;;;     the SETOID quotient of structure-library/setoid.scm, the precedent being
;;;     QUOTIENT(CAUCHY-SETOID(M)) in metric-completion.scm.
;;;
;;; THE SHAPE.  Slots 1-6 are MODULE's, name for name and index for index, exactly
;;; as normed-vector-space.scm and complex-inner-product.scm reuse them (one name,
;;; one slot: structures.scm, register-accessor-index!).  Slot 7 is the form, RIP
;;; (a fresh name: neither the constant registry nor the accessor index knew it),
;;; typed VEC x VEC -> RR.  It is not IP: IP is COMPLEX-INNER-PRODUCT-SPACE's slot 7
;;; and is typed into CC there.
;;;
;;;     1 SCAL   substructure RING     -- pinned to the reals, through the ring VIEW
;;;     2 VEC    carrier
;;;     3 VADD   op (VEC x VEC) -> VEC
;;;     4 VZERO  constant in VEC
;;;     5 VNEG   op VEC -> VEC
;;;     6 ACT    op (CARR SCAL x VEC) -> VEC
;;;     7 RIP    op (VEC x VEC) -> RR  -- the form
;;;
;;; THE SCALARS are pinned by `scal(s) = normed-field-as-commutative-ring(rr-normed-field)',
;;; never by the raw seven-tuple RR-NORMED-FIELD (complex-inner-product.scm, header,
;;; "THE SCALARS, AND A DEFECT NOT REPEATED HERE": IS-RING pins length 6).  The second
;;; law, `carr(scal(s)) = rr', is REDUNDANT (it follows from the first by unfolding the
;;; view and projecting the instance) and is stated for the same reason
;;; complex-inner-product.scm states its twin: a proof reaches the scalars in one
;;; projection.  It adds no assumption: IS-SEMI-INNER-PRODUCT-SPACE has exactly the
;;; models it would have without it.
;;;
;;; THE LAWS of the form are the minimal ones: symmetric, additive and homogeneous in
;;; the FIRST argument, nonnegative on the diagonal.  Linearity in the second argument
;;; is a consequence (symmetry) and is PROVED in theorem-library/sip-a.scm.
;;;
;;; THE MODULE VIEW is a `def-functor', pure slot selection, as for the two structures
;;; above: SIP-AS-MODULE forgets RIP.  Its typing axiom is the definitional
;;; `sip-as-module-is-module', and the view specializer transports every MODULE theorem
;;; present when this file loads (the frm-* group algebra of frechet-metric.scm among
;;; them) as a companion `<name>-sip-as-module' whose bill is its source's bill.
;;;
;;; Dependencies: module.scm (the accessors, MODULE), views.scm
;;; (NORMED-FIELD-AS-COMMUTATIVE-RING), numeric-instances.scm (RR-NORMED-FIELD),
;;; setoid.scm (SETOID, CLASS, QUOTIENT, DESCEND, DESCEND2), operation-properties.scm.
;;; LOAD WINDOW: after theorem-library/frechet-metric (so that the view specializer
;;; sees the frm-* module lemmas) -- in practice beside structure-library/lp-seminorm.
;;; Library: analysis (the same library as complex-inner-product.scm).

(declare-structure SEMI-INNER-PRODUCT-SPACE
  (instance-var s)
  (substructure SCAL RING)
  (carriers VEC)
  (op VADD (CARTESIAN VEC VEC) VEC)
  (constant VZERO VEC)
  (op VNEG VEC VEC)
  (op ACT (CARTESIAN (CARR SCAL) VEC) VEC)
  (op RIP (CARTESIAN VEC VEC) RR)
  (property is-associative VADD VEC)
  (property is-commutative VADD VEC)
  (property is-identity VADD VZERO VEC)
  (property has-inverses VADD VZERO VNEG VEC)
  (law "scal(s) = normed-field-as-commutative-ring(rr-normed-field)")
  (law "carr(scal(s)) = rr")
  (law "forall([r_ in carr(scal(s)), x_ in vec(s), y_ in vec(s)],
          act(s)(r_, vadd(s)(x_, y_)) = vadd(s)(act(s)(r_, x_), act(s)(r_, y_)))")
  (law "forall([r_ in carr(scal(s)), s_ in carr(scal(s)), x_ in vec(s)],
          act(s)(add(scal(s))(r_, s_), x_) = vadd(s)(act(s)(r_, x_), act(s)(s_, x_)))")
  (law "forall([r_ in carr(scal(s)), s_ in carr(scal(s)), x_ in vec(s)],
          act(s)(mul(scal(s))(r_, s_), x_) = act(s)(r_, act(s)(s_, x_)))")
  (law "forall([x_ in vec(s)], act(s)(one(scal(s)), x_) = x_)")
  ;; ----- the form: symmetric, linear in the first argument, positive semidefinite
  (law "forall([x_ in vec(s), y_ in vec(s)], rip(s)(x_, y_) = rip(s)(y_, x_))")
  (law "forall([x_ in vec(s), y_ in vec(s), z_ in vec(s)],
          rip(s)(vadd(s)(x_, y_), z_) = rip(s)(x_, z_) + rip(s)(y_, z_))")
  (law "forall([a_ in rr, x_ in vec(s), y_ in vec(s)],
          rip(s)(act(s)(a_, x_), y_) = a_ * rip(s)(x_, y_))")
  (law "forall([x_ in vec(s)], 0 <= rip(s)(x_, x_))"))

;;; The definite refinement: the notes' REAL PRE-HILBERT SPACE (Definition 1.17).
(declare-structure PRE-HILBERT-SPACE
  (instance-var s)
  (same-shape-as SEMI-INNER-PRODUCT-SPACE)
  (law "forall([x_ in vec(s)], rip(s)(x_, x_) = 0 implies x_ = vzero(s))"))

;;; THE VIEW: forget the form.
(def-functor 'SIP-AS-MODULE
  'SEMI-INNER-PRODUCT-SPACE '(SCAL VEC VADD VZERO VNEG ACT)
  'MODULE                   '(SCAL VEC VADD VZERO VNEG ACT))

;;; -----------------------------------------------------------------------
;;; THE NULL VECTORS AND THE QUOTIENT.
;;;
;;; SIP-NULL(v) = { x : <x,x> = 0 }, the null vectors -- a subspace (sip-a.scm).
;;; SIP-REL(v)  = { (x,y) : <x - y, x - y> = 0 } as an extensional SET of pairs,
;;;               in the shape SETOID's relation slot wants.
;;; SIP-SETOID(v) = [VEC(v), SIP-REL(v)], a SETOID instance.
;;; The quotient operations are the DESCENDs of the class-of-<op> maps (binary by
;;; DESCEND2, unary by DESCEND), the ringoid quotient's recipe (ringoid.scm); the
;;; scalar action descends one scalar at a time.  The quotient form is DESCEND2 of
;;; the form itself.  Binders sq*_ are used by nothing else in the tree.
(def-functoid 'SIP-NULL '(v)
  '(SEP sqn_ (VEC v) (= ((RIP v) sqn_ sqn_) 0)))

(def-functoid 'SIP-REL '(v)
  '(SEP sqp_ (CARTESIAN (VEC v) (VEC v))
     (= ((RIP v) ((VADD v) (NTH 1 sqp_) ((VNEG v) (NTH 2 sqp_)))
                 ((VADD v) (NTH 1 sqp_) ((VNEG v) (NTH 2 sqp_))))
        0)))

(def-functoid 'SIP-SETOID '(v)
  '(LIST (VEC v) (SIP-REL v)))

(def-functoid 'SIP-QVADD '(v)
  '(DESCEND2 (SIP-SETOID v)
     (VNB-LAMBDA (LIST sqa_ sqb_) (CARTESIAN (VEC v) (VEC v))
       (CLASS (SIP-SETOID v) ((VADD v) sqa_ sqb_)))))

(def-functoid 'SIP-QVNEG '(v)
  '(DESCEND (SIP-SETOID v)
     (VNB-LAMBDA sqa_ (VEC v) (CLASS (SIP-SETOID v) ((VNEG v) sqa_)))))

;;; the action of ONE scalar r on the quotient
(def-functoid 'SIP-QSCALE '(v r)
  '(DESCEND (SIP-SETOID v)
     (VNB-LAMBDA sqa_ (VEC v) (CLASS (SIP-SETOID v) ((ACT v) r sqa_)))))

(def-functoid 'SIP-QACT '(v)
  '(VNB-LAMBDA (LIST sqr_ sqc_) (CARTESIAN RR (QUOTIENT (SIP-SETOID v)))
     ((SIP-QSCALE v sqr_) sqc_)))

(def-functoid 'SIP-QRIP '(v)
  '(DESCEND2 (SIP-SETOID v)
     (VNB-LAMBDA (LIST sqa_ sqb_) (CARTESIAN (VEC v) (VEC v))
       ((RIP v) sqa_ sqb_))))

;;; THE QUOTIENT SPACE: [scalars, classes, +, [0], -, action, form].
(def-functoid 'SIP-QUOTIENT '(v)
  '(LIST (SCAL v) (QUOTIENT (SIP-SETOID v)) (SIP-QVADD v)
         (CLASS (SIP-SETOID v) (VZERO v)) (SIP-QVNEG v) (SIP-QACT v) (SIP-QRIP v)))

;;; -----------------------------------------------------------------------
;;; Notation.
(notation! 'IS-SEMI-INNER-PRODUCT-SPACE 'kind 'predicate 'arity 1
           'noun "semi-inner-product space" 'article "a")
(notation! 'IS-PRE-HILBERT-SPACE 'kind 'predicate 'arity 1
           'noun "pre-Hilbert space" 'article "a")
(notation! 'RIP 'kind 'accessor 'arity 1
           'english "the form of $1"
           'tex "\\langle\\cdot\\mid\\cdot\\rangle_{$1}")
(notation! 'SIP-NULL 'kind 'functoid 'arity 1
           'english "the null vectors of $1")
(notation! 'SIP-REL 'kind 'functoid 'arity 1
           'english "the null-difference relation of $1")
(notation! 'SIP-SETOID 'kind 'functoid 'arity 1
           'english "the setoid of $1 modulo its null vectors")
(notation! 'SIP-QUOTIENT 'kind 'functoid 'arity 1
           'english "the quotient of $1 by its null vectors")
