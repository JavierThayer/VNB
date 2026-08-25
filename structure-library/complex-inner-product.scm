;;; complex-inner-product.scm -- COMPLEX-INNER-PRODUCT-SPACE: a vector space over
;;; CC carrying a sesquilinear, conjugate-symmetric, positive-definite form IP.
;;; Vocabulary only (no proofs); the two inequalities it exists for are proved in
;;; theorem-library/inner-product-inequalities.scm.
;;;
;;; ====================================================================
;;; THE DESIGN QUESTION: how does this sit beside NORMED-VECTOR-SPACE?
;;; ====================================================================
;;;
;;; It does NOT refine it, and it CANNOT.  Three separate reasons, each decisive
;;; on its own, and together they fix the shape of this file completely.
;;;
;;; (1) A `(same-shape-as NORMED-VECTOR-SPACE)' refinement INHERITS the parent's
;;;     laws (def-substructure, structures.scm:729 -- the parent conjunct is
;;;     literal), and NORMED-VECTOR-SPACE's laws include `scal(s) =
;;;     normed-field-as-commutative-ring(rr-normed-field)'.  A refinement of it
;;;     therefore has REAL scalars, which
;;;     is the one thing a complex inner product space does not have.  The
;;;     pinning is deliberate there (its own header, decision (1): homogeneity
;;;     wants the real `abs'), and it is exactly what we cannot reuse.
;;;
;;; (2) A refinement may not declare a slot either ("(same-shape-as ...) inherits
;;;     the parent's shape, so it cannot declare slots", structures.scm:793), and
;;;     slot 7 here is a form VEC x VEC -> CC, not a norm VEC -> RR.  Different
;;;     shape, hence a different structure; the tree's word for the relation
;;;     between two shapes is `def-functor'.
;;;
;;; (3) But the shape is not free either: ONE NAME, ONE SLOT (structures.scm:127
;;;     ff., register-accessor-index!).  An accessor name that is claimed at a
;;;     second index becomes AMBIGUOUS library-wide and its reduction is
;;;     WITHDRAWN -- for everybody, including the eighteen existing files that
;;;     read VEC or VADD off a normed vector space.  So a complex inner product
;;;     space that is to be read with the vector-space accessors at all MUST put
;;;     them where MODULE and NORMED-VECTOR-SPACE put them:
;;;
;;;         1 SCAL   substructure RING     -- the scalars (pinned to CC below)
;;;         2 VEC    carrier               -- the vectors
;;;         3 VADD   op (VEC x VEC) -> VEC
;;;         4 VZERO  constant in VEC
;;;         5 VNEG   op VEC -> VEC
;;;         6 ACT    op (CARR SCAL x VEC) -> VEC
;;;         7 IP     op (VEC x VEC) -> CC   <-- the only new slot
;;;
;;;     Slots 1-6 are MODULE's, name for name and index for index, exactly as
;;;     normed-vector-space.scm reuses them; IP is a fresh name (checked: neither
;;;     the constant registry nor the accessor index knew `IP' before this file).
;;;     Re-declaring slots 1-6 is not a collision -- def-structure re-registers
;;;     SCAL -> (NTH 1 s) ... ACT -> (NTH 6 s) byte-identically and
;;;     register-constant! / install-macete! are idempotent overwrites.
;;;
;;; So the relation to the REAL normed vector space is not a subtype edge in
;;; either direction.  It is:
;;;
;;;   -- to MODULE, a VIEW: forget IP.  Pure slot selection, so `def-functor'
;;;      expresses it (COMPLEX-INNER-PRODUCT-SPACE-AS-MODULE, below), and every
;;;      MODULE theorem specializes across it.
;;;
;;;   -- to the normed world, a CONSTRUCTION, not a view.  The induced norm is
;;;      SQRT(<x,x>), which is COMPUTED from a slot rather than SELECTED from
;;;      one, and `def-functor' can only select ("target components must equal
;;;      target slot order", structures.scm:1140).  So IP-NORMED-AG below builds
;;;      the tuple by hand.  And the target is NORMED-AG, not
;;;      NORMED-VECTOR-SPACE: the latter pins its scalars to RR by law, so a
;;;      complex space is not one of those however its norm is obtained.  This
;;;      is the same edge normed-vector-space.scm itself draws to NORMED-AG.
;;;
;;; ====================================================================
;;; THE SCALARS, AND A DEFECT NOT REPEATED HERE
;;; ====================================================================
;;;
;;; The scalars are pinned by
;;;     scal(s) = normed-field-as-commutative-ring(cc-normed-field)
;;; and NOT by `scal(s) = cc-normed-field'.  The difference is the whole of a
;;; known inconsistency.  `(substructure SCAL RING)' becomes the conjunct
;;; (IS-RING (SCAL s)) (build-is-axiom, structures.scm:484), and IS-RING pins
;;; (= (LENGTH (SCAL s)) 6); CC-NORMED-FIELD is a SEVEN-tuple
;;; [CC binplus bintimes binneg 0 1 magnitude].  Pinning the raw instance would
;;; make IS-COMPLEX-INNER-PRODUCT-SPACE assert 6 = 7, i.e. make it unsatisfiable
;;; and every theorem about it vacuous.  numeric-instances.scm:243-249 describes
;;; this exact trap and fixed it for itself on 2026-05-30; NORMED-FIELD-AS-
;;; COMMUTATIVE-RING (views.scm:167) exists precisely to project slots 1..6 into
;;; a fresh 6-tuple, and that projection is what a scalar slot must hold.
;;;
;;; NORMED-VECTOR-SPACE DID pin the raw 7-tuple (`scal(s) = rr-normed-field'),
;;; so IS-NORMED-VECTOR-SPACE was unsatisfiable and its downstream theorems were
;;; vacuous.  REPAIRED 2026-08-23: it now pins
;;; `scal(s) = normed-field-as-commutative-ring(rr-normed-field)', the same
;;; shape as the line below, and this file's caution is now a shared convention
;;; rather than a lone one.  The measured cost was zero -- no bill moved, no
;;; proof in the library unfolds IS-NORMED-VECTOR-SPACE -- and the slot read-offs
;;; both structures need are PROVEN in
;;; theorem-library/normed-field-ring-view.scm.
;;;
;;; ====================================================================
;;; THE LAWS
;;; ====================================================================
;;;
;;; Slots 1-6 carry MODULE's four action laws VERBATIM (over carr(scal(s)), so
;;; that the MODULE view is a literal conjunct match) and the four abelian-group
;;; properties of (VEC, VADD, VZERO, VNEG).  What this structure ADDS is the form:
;;;
;;;   additive in the FIRST argument     <x+y, z> = <x,z> + <y,z>
;;;   homogeneous in the FIRST argument  <a.x, y> = a <x,y>
;;;   conjugate-symmetric                <y,x> = conj <x,y>
;;;   positive-definite                  <x,x> is REAL and >= 0,
;;;                                      and = 0 exactly at the zero vector
;;;
;;; That is the minimal presentation: additivity and conjugate-homogeneity in the
;;; SECOND argument are CONSEQUENCES (conjugate the first-argument laws), and are
;;; therefore not stated here but PROVED in
;;; theorem-library/complex-inner-product-laws.scm.
;;;
;;; ONE CONJUNCT IS DELIBERATELY REDUNDANT, and it is the realness of the
;;; diagonal.  Conjugate symmetry at y = x gives conj<x,x> = <x,x>, which SAYS
;;; <x,x> is real -- but the theory has no converse of cc-conjugate-fixes-rr
;;; (number-systems.scm:698 gives only "a in RR => conj a = a"), so nothing can
;;; get from that equation to a membership.  Without `ip(s)(x_,x_) in rr' the
;;; next law, `0 <= ip(s)(x_,x_)', would be an order comparison on a term the
;;; theory does not know is real, and `ineq' would refuse every use of it
;;; (ineq-atom-rr-ok? demands an IN _ RR certificate).  So it is stated.
;;;
;;; A SECOND REDUNDANT CONJUNCT, for the same species of reason:
;;; `carr(scal(s)) = cc'.  It follows from the pinning law by unfolding the view
;;; functoid and projecting the CC-NORMED-FIELD instance -- two definitional
;;; steps -- but as a LAW it is a literal conjunct of the IFF, so a proof reaches
;;; the scalars in one projection instead of a functoid unfold plus an NTH.
;;; Neither redundant conjunct adds an assumption: both are consequences of the
;;; others, so IS-COMPLEX-INNER-PRODUCT-SPACE has exactly the models it would
;;; have had without them.
;;;
;;; Dependencies: module.scm (the shared accessors and MODULE, for the view),
;;; views.scm (NORMED-FIELD-AS-COMMUTATIVE-RING), numeric-instances.scm
;;; (CC-NORMED-FIELD), normed-ag.scm (NORMED-AG, for the induced-norm
;;; construction), real-powers.scm (SQRT), number-systems.scm (CC, conjugate).
;;; Loads after normed-vector-space/linear-functional/dual-space, which is later
;;; than any of those.

(declare-structure COMPLEX-INNER-PRODUCT-SPACE
  (instance-var s)
  (substructure SCAL RING)                  ; the scalars -- pinned to CC below
  (carriers VEC)
  (op VADD (CARTESIAN VEC VEC) VEC)
  (constant VZERO VEC)
  (op VNEG VEC VEC)
  (op ACT (CARTESIAN (CARR SCAL) VEC) VEC)
  (op IP (CARTESIAN VEC VEC) CC)            ; the inner product, slot 7
  ;; (VEC, VADD, VZERO, VNEG) is an abelian group
  (property is-associative VADD VEC)
  (property is-commutative VADD VEC)
  (property is-identity VADD VZERO VEC)
  (property has-inverses VADD VZERO VNEG VEC)
  ;; THE SCALARS ARE THE COMPLEX NUMBERS -- through the ring VIEW of the normed
  ;; field, never the raw 7-tuple (see the header).
  (law "scal(s) = normed-field-as-commutative-ring(cc-normed-field)")
  ;; ... and, redundantly but usably, their carrier is CC.
  (law "carr(scal(s)) = cc")
  ;; the four action axioms -- MODULE's, verbatim, with `s' for the structure
  (law "forall([r_ in carr(scal(s)), x_ in vec(s), y_ in vec(s)],
          act(s)(r_, vadd(s)(x_, y_)) = vadd(s)(act(s)(r_, x_), act(s)(r_, y_)))")
  (law "forall([r_ in carr(scal(s)), s_ in carr(scal(s)), x_ in vec(s)],
          act(s)(add(scal(s))(r_, s_), x_) = vadd(s)(act(s)(r_, x_), act(s)(s_, x_)))")
  (law "forall([r_ in carr(scal(s)), s_ in carr(scal(s)), x_ in vec(s)],
          act(s)(mul(scal(s))(r_, s_), x_) = act(s)(r_, act(s)(s_, x_)))")
  (law "forall([x_ in vec(s)], act(s)(one(scal(s)), x_) = x_)")
  ;; ----- the sesquilinear form -----
  ;; additive in the first argument
  (law "forall([x_ in vec(s), y_ in vec(s), z_ in vec(s)],
          ip(s)(vadd(s)(x_, y_), z_) = ip(s)(x_, z_) + ip(s)(y_, z_))")
  ;; homogeneous in the first argument
  (law "forall([a_ in cc, x_ in vec(s), y_ in vec(s)],
          ip(s)(act(s)(a_, x_), y_) = a_ * ip(s)(x_, y_))")
  ;; conjugate-symmetric
  (law "forall([x_ in vec(s), y_ in vec(s)],
          ip(s)(y_, x_) = conjugate(ip(s)(x_, y_)))")
  ;; positive-definite: the diagonal is real, nonnegative, and vanishes only at 0
  (law "forall([x_ in vec(s)], ip(s)(x_, x_) in rr)")
  (law "forall([x_ in vec(s)], 0 <= ip(s)(x_, x_))")
  (law "forall([x_ in vec(s)], (ip(s)(x_, x_) = 0) iff (x_ = vzero(s)))"))

;;; -----------------------------------------------------------------------
;;; PROJECTED LAWS.  Each is a CONJUNCT of the IFF above, surfaced as a
;;; standalone citable theorem so a proof can `fact' it directly instead of
;;; peeling a nineteen-conjunct IFF.  Definitional -- a projection of the
;;; definition, not new content.  Exactly module.scm's "Projected module laws"
;;; idiom (module.scm:63 ff.).
;;;
;;; `cips-act-type' is the one that is a projection PLUS one step: the shape
;;; conjunct types ACT over carr(scal(s)), and the redundant carrier law rewrites
;;; that to CC.  Both steps are definitional, so the composite is.
(fluid-let ((*current-provenance* 'definitional))

  (theory-add-axiom! *current-theory* 'cips-scal-carrier
    '(FORALL v (IMPLIES (IS-COMPLEX-INNER-PRODUCT-SPACE v)
       (= (CARR (SCAL v)) CC))))

  (theory-add-axiom! *current-theory* 'cips-vzero-in
    '(FORALL v (IMPLIES (IS-COMPLEX-INNER-PRODUCT-SPACE v)
       (IN (VZERO v) (VEC v)))))

  ;; the zero vector is the identity of VADD -- the `is-identity VADD VZERO VEC'
  ;; property conjunct, unfolded (is-identity op unit crr says both sides;
  ;; the left one is what cips-ip-zero-right needs).
  (theory-add-axiom! *current-theory* 'cips-vadd-vzero
    '(FORALL v (IMPLIES (IS-COMPLEX-INNER-PRODUCT-SPACE v)
       (FORALL x_ (IMPLIES (IN x_ (VEC v))
         (= ((VADD v) (VZERO v) x_) x_))))))

  (theory-add-axiom! *current-theory* 'cips-vadd-type
    '(FORALL v (IMPLIES (IS-COMPLEX-INNER-PRODUCT-SPACE v)
       (FORALL x_ (IMPLIES (IN x_ (VEC v))
         (FORALL y_ (IMPLIES (IN y_ (VEC v))
           (IN ((VADD v) x_ y_) (VEC v)))))))))

  (theory-add-axiom! *current-theory* 'cips-act-type
    '(FORALL v (IMPLIES (IS-COMPLEX-INNER-PRODUCT-SPACE v)
       (FORALL a_ (IMPLIES (IN a_ CC)
         (FORALL x_ (IMPLIES (IN x_ (VEC v))
           (IN ((ACT v) a_ x_) (VEC v)))))))))

  (theory-add-axiom! *current-theory* 'cips-ip-type
    '(FORALL v (IMPLIES (IS-COMPLEX-INNER-PRODUCT-SPACE v)
       (FORALL x_ (IMPLIES (IN x_ (VEC v))
         (FORALL y_ (IMPLIES (IN y_ (VEC v))
           (IN ((IP v) x_ y_) CC))))))))

  ;; <x+y, z> = <x,z> + <y,z>
  (theory-add-axiom! *current-theory* 'cips-ip-add-left
    '(FORALL v (IMPLIES (IS-COMPLEX-INNER-PRODUCT-SPACE v)
       (FORALL x_ (IMPLIES (IN x_ (VEC v))
         (FORALL y_ (IMPLIES (IN y_ (VEC v))
           (FORALL z_ (IMPLIES (IN z_ (VEC v))
             (= ((IP v) ((VADD v) x_ y_) z_)
                (+ ((IP v) x_ z_) ((IP v) y_ z_))))))))))))

  ;; <a.x, y> = a <x,y>
  (theory-add-axiom! *current-theory* 'cips-ip-homog-left
    '(FORALL v (IMPLIES (IS-COMPLEX-INNER-PRODUCT-SPACE v)
       (FORALL a_ (IMPLIES (IN a_ CC)
         (FORALL x_ (IMPLIES (IN x_ (VEC v))
           (FORALL y_ (IMPLIES (IN y_ (VEC v))
             (= ((IP v) ((ACT v) a_ x_) y_)
                (* a_ ((IP v) x_ y_))))))))))))

  ;; <y,x> = conj <x,y>
  (theory-add-axiom! *current-theory* 'cips-ip-conj-sym
    '(FORALL v (IMPLIES (IS-COMPLEX-INNER-PRODUCT-SPACE v)
       (FORALL x_ (IMPLIES (IN x_ (VEC v))
         (FORALL y_ (IMPLIES (IN y_ (VEC v))
           (= ((IP v) y_ x_) (conjugate ((IP v) x_ y_))))))))))

  ;; <x,x> is a real
  (theory-add-axiom! *current-theory* 'cips-ip-self-real
    '(FORALL v (IMPLIES (IS-COMPLEX-INNER-PRODUCT-SPACE v)
       (FORALL x_ (IMPLIES (IN x_ (VEC v))
         (IN ((IP v) x_ x_) RR))))))

  ;; 0 <= <x,x>
  (theory-add-axiom! *current-theory* 'cips-ip-self-nonneg
    '(FORALL v (IMPLIES (IS-COMPLEX-INNER-PRODUCT-SPACE v)
       (FORALL x_ (IMPLIES (IN x_ (VEC v))
         (<= 0 ((IP v) x_ x_)))))))

  ;; the forward half of the definiteness law, in detachable form (an IFF in a
  ;; context cannot be `detach!'-ed; every use of definiteness in
  ;; theorem-library/inner-product-inequalities.scm wants exactly this half).
  (theory-add-axiom! *current-theory* 'cips-ip-zero-vector
    '(FORALL v (IMPLIES (IS-COMPLEX-INNER-PRODUCT-SPACE v)
       (FORALL x_ (IMPLIES (IN x_ (VEC v))
         (IMPLIES (= ((IP v) x_ x_) 0) (= x_ (VZERO v))))))))

  ;; <x,x> = 0 exactly at the zero vector
  (theory-add-axiom! *current-theory* 'cips-ip-definite
    '(FORALL v (IMPLIES (IS-COMPLEX-INNER-PRODUCT-SPACE v)
       (FORALL x_ (IMPLIES (IN x_ (VEC v))
         (IFF (= ((IP v) x_ x_) 0) (= x_ (VZERO v)))))))))

;;; -----------------------------------------------------------------------
;;; THE VIEW: forget the form.  Pure slot selection, so def-functor expresses it,
;;; and every MODULE theorem specializes across it.
(def-functor 'COMPLEX-INNER-PRODUCT-SPACE-AS-MODULE
  'COMPLEX-INNER-PRODUCT-SPACE '(SCAL VEC VADD VZERO VNEG ACT)
  'MODULE                      '(SCAL VEC VADD VZERO VNEG ACT))

;;; -----------------------------------------------------------------------
;;; THE INDUCED NORM -- a CONSTRUCTION, not a view (see the header).
;;;
;;; ||x|| = SQRT(<x,x>).  Well-defined: <x,x> is real and >= 0
;;; (cips-ip-self-real / -nonneg), which is exactly SQRT's precondition.
(def-functoid 'IP-NORM '(v x)
  '(SQRT ((IP v) x x)))

;;; The additive group of the vectors, carrying that norm.  NORMED-AG's shape is
;;; [CARR OPR IDEN INV NRM] (normed-ag.scm), so this is the vector part of v with
;;; the induced norm in slot 5.  The target is NORMED-AG and not
;;; NORMED-VECTOR-SPACE because the latter pins its scalars to RR by law.
(def-functoid 'IP-NORMED-AG '(v)
  '(LIST (VEC v) (VADD v) (VZERO v) (VNEG v)
         (VNB-LAMBDA x_ (VEC v) (IP-NORM v x_))))

(fluid-let ((*current-provenance* 'definitional))
  (support 'ip-normed-ag-carrier
    '(FORALL v (== (CARR (IP-NORMED-AG v)) (VEC v))))
  (support 'ip-normed-ag-norm-value
    '(FORALL v (FORALL x (IMPLIES (IN x (VEC v))
       (== ((NRM (IP-NORMED-AG v)) x) (IP-NORM v x)))))))

;;; The induced norm IS a group norm.  Nonnegativity and definiteness are
;;; sqrt-nonneg and cips-ip-definite; the triangle inequality is MINKOWSKI,
;;; PROVEN in theorem-library/inner-product-inequalities.scm as
;;; `cips-minkowski'.  Inverse-invariance is <-x,-x> = <x,x>.
(support 'ip-normed-ag-is-normed-ag
  '(FORALL v (IMPLIES (IS-COMPLEX-INNER-PRODUCT-SPACE v)
     (IS-NORMED-AG (IP-NORMED-AG v)))))
(warrant! 'ip-normed-ag-is-normed-ag 'reference
  "The norm induced by a complex inner product makes the additive group of
   vectors a normed abelian group.  ||x|| = SQRT(<x,x>) >= 0 (sqrt-nonneg);
   ||x|| = 0 iff <x,x> = 0 iff x = 0 (sqrt-sq and cips-ip-definite);
   ||-x|| = ||x|| since <-x,-x> = (-1)(conj -1)<x,x> = <x,x>; and the triangle
   inequality is `cips-minkowski', PROVEN in
   theorem-library/inner-product-inequalities.scm.  Only the packaging of the
   five slots into the NORMED-AG tuple is asserted here.  Standard: Rudin, Real
   and Complex Analysis, 4.1-4.2; Conway, A Course in Functional Analysis, I.1.")
(topic! 'ip-normed-ag-is-normed-ag 'analysis)
(gloss! 'ip-normed-ag-is-normed-ag
  "For every complex inner product space v, the additive group of its vectors,
   carrying the induced norm ||x|| = SQRT(<x,x>), is a normed abelian group.")

;;; -----------------------------------------------------------------------
;;; Notation -- read by wff->english / the proof reader (operators.scm).
(notation! 'IS-COMPLEX-INNER-PRODUCT-SPACE 'kind 'predicate 'arity 1
           'noun "complex inner product space" 'article "a")
(notation! 'IP 'kind 'accessor 'arity 1
           'english "the inner product of $1"
           'tex "\\langle\\cdot,\\cdot\\rangle_{$1}")
(notation! 'IP-NORM 'kind 'functoid 'arity 2
           'english "the induced norm of $2 in $1"
           'tex "\\lVert $2 \\rVert")
(notation! 'IP-NORMED-AG 'kind 'functoid 'arity 1
           'english "the additive group of $1 under the induced norm")
