;;; module.scm -- MODULE over a ring, with the scalar action ACT.
;;;
;;; A module is an abelian group (the vectors) together with an action of a ring
;;; (the scalars) satisfying the four module laws.  Following the "define
;;; concretely" discipline, IS-MODULE is ONE complete IFF (design A): shape +
;;; vector part is an abelian group + scalar part is a ring + action typed +
;;; the four action axioms.  No two-level shape/laws split.
;;;
;;; SHAPE (6 slots; the scalar ring rides as a SUBSTRUCTURE slot, so a module is
;;; a single tuple and "module over a ring" means the ring is component 1):
;;;   1 SCAL  substructure RING                 -- the scalars
;;;   2 VEC   carrier                            -- the vectors
;;;   3 VADD  op (CARTESIAN VEC VEC) -> VEC      -- vector addition
;;;   4 VZERO constant in VEC                    -- zero vector
;;;   5 VNEG  op VEC -> VEC                       -- vector negation
;;;   6 ACT   op (CARTESIAN (CARR SCAL) VEC) -> VEC  -- scalar action  r . x
;;; (VEC.VADD.VZERO.VNEG mirrors ABELIAN-GROUP's A.MUL.E.INV order, so a later
;;; MODULE -> ABELIAN-GROUP view-as on the vector part is a clean remap.)
;;;
;;; ACCESSOR NAMES.  Symbols case-fold to lowercase (the reader and MIT both
;;; fold).  We deliberately AVOID R / V as accessors -- they would fold to the
;;; ubiquitous r / v and collide with bound variables everywhere a module
;;; appears.  Hence SCAL (scalars) and VEC (vectors).  The destructuring surface
;;; `let [R, V, ...] be a module' maps the user's letters positionally onto
;;; these accessors, so you may still WRITE R, V at the surface.
;;;
;;; Vector space = a module whose SCAL is a field (a later subtype:
;;; IS-VECTOR-SPACE(m) <=> IS-MODULE(m) AND IS-FIELD-RING(SCAL m)).  IS-FIELD-RING,
;;; not IS-FIELD: the substructure slot above already pins length(SCAL m) = 6 and
;;; FIELD is an 8-slot shape, so the law had to be fieldhood stated OF A RING.
;;; Writing IS-FIELD there made IS-VECTOR-SPACE unsatisfiable (finite-dimensional.scm,
;;; repaired 2026-08-23).
;;;
;;; Dependencies: ring.scm (RING, IS-RING, A, ADD, MUL, ONE),
;;;               operation-properties.scm (is-associative/commutative/...).

(declare-structure MODULE
  (instance-var s)
  (substructure SCAL RING)                  ; the scalar ring
  (carriers VEC)
  (op VADD (CARTESIAN VEC VEC) VEC)
  (constant VZERO VEC)
  (op VNEG VEC VEC)
  (op ACT (CARTESIAN (CARR SCAL) VEC) VEC)
  ;; (VEC, VADD, VZERO, VNEG) is an abelian group
  (property is-associative VADD VEC)
  (property is-commutative VADD VEC)
  (property is-identity VADD VZERO VEC)
  (property has-inverses VADD VZERO VNEG VEC)
  ;; the four action axioms.  No named operation-property expresses these, which
  ;; is why IS-MODULE used to be written out longhand ("design A").
  ;; Bound scalars r_ s_ and vectors x_ y_ take trailing underscores to dodge
  ;; case-fold collisions with the accessors and the ring ops (CLAUDE.md).
  (law "forall([r_ in carr(scal(s)), x_ in vec(s), y_ in vec(s)],
          act(s)(r_, vadd(s)(x_, y_)) = vadd(s)(act(s)(r_, x_), act(s)(r_, y_)))")
  (law "forall([r_ in carr(scal(s)), s_ in carr(scal(s)), x_ in vec(s)],
          act(s)(add(scal(s))(r_, s_), x_) = vadd(s)(act(s)(r_, x_), act(s)(s_, x_)))")
  (law "forall([r_ in carr(scal(s)), s_ in carr(scal(s)), x_ in vec(s)],
          act(s)(mul(scal(s))(r_, s_), x_) = act(s)(r_, act(s)(s_, x_)))")
  (law "forall([x_ in vec(s)], act(s)(one(scal(s)), x_) = x_)"))

;;; -----------------------------------------------------------------------
;;; Projected module laws.  Each is a CONJUNCT of the IS-MODULE definition,
;;; surfaced as a standalone citable theorem so a proof can bc*/inst it
;;; directly instead of peeling the 15-conjunct IFF.  Definitional (a
;;; projection of the definition), not new mathematical content.

(fluid-let ((*current-provenance* 'definitional))

  ;; the scalar component is a ring
  (add-axiom! *library* 'module-scalar-ring
    '(FORALL m (IMPLIES (IS-MODULE m) (IS-RING (SCAL m)))))

  ;; ring zero lives in the scalar carrier (an action argument)
  (add-axiom! *library* 'module-scalar-zero-in
    '(FORALL m (IMPLIES (IS-MODULE m) (IN (ZERO (SCAL m)) (CARR (SCAL m))))))

  ;; the zero vector is a vector (the shape conjunct, surfaced for rfl's
  ;; definedness obligation on VZERO terms)
  (add-axiom! *library* 'module-vzero-in
    '(FORALL m (IMPLIES (IS-MODULE m) (IN (VZERO m) (VEC m)))))

  ;; action closure:  r . x  is a vector
  (add-axiom! *library* 'module-act-type
    '(FORALL m (IMPLIES (IS-MODULE m)
       (FORALL r_ (IMPLIES (IN r_ (CARR (SCAL m)))
         (FORALL x_ (IMPLIES (IN x_ (VEC m))
           (IN ((ACT m) r_ x_) (VEC m)))))))))

  ;; addition and negation close on the vectors -- the same read-off of the shape
  ;; conjuncts (IN (VADD m) (FUN (CARTESIAN (VEC m) (VEC m)) (VEC m))) and
  ;; (IN (VNEG m) (FUN (VEC m) (VEC m))) that module-act-type is of its own.
  ;; Surfaced because whole-module-is-submodule needs all three closures, and
  ;; IS-SUBMODULE states them in applied form.
  (add-axiom! *library* 'module-vadd-type
    '(FORALL m (IMPLIES (IS-MODULE m)
       (FORALL x_ (IMPLIES (IN x_ (VEC m))
         (FORALL y_ (IMPLIES (IN y_ (VEC m))
           (IN ((VADD m) x_ y_) (VEC m)))))))))

  (add-axiom! *library* 'module-vneg-type
    '(FORALL m (IMPLIES (IS-MODULE m)
       (FORALL x_ (IMPLIES (IN x_ (VEC m))
         (IN ((VNEG m) x_) (VEC m)))))))

  ;; (1) action distributes over vector addition
  (add-axiom! *library* 'module-act-distrib-vec
    '(FORALL m (IMPLIES (IS-MODULE m)
       (FORALL r_ (IMPLIES (IN r_ (CARR (SCAL m)))
         (FORALL x_ (IMPLIES (IN x_ (VEC m))
           (FORALL y_ (IMPLIES (IN y_ (VEC m))
             (= ((ACT m) r_ ((VADD m) x_ y_))
                ((VADD m) ((ACT m) r_ x_) ((ACT m) r_ y_))))))))))))

  ;; (2) action distributes over ring addition
  (add-axiom! *library* 'module-act-distrib-scalar
    '(FORALL m (IMPLIES (IS-MODULE m)
       (FORALL r_ (IMPLIES (IN r_ (CARR (SCAL m)))
         (FORALL s_ (IMPLIES (IN s_ (CARR (SCAL m)))
           (FORALL x_ (IMPLIES (IN x_ (VEC m))
             (= ((ACT m) ((ADD (SCAL m)) r_ s_) x_)
                ((VADD m) ((ACT m) r_ x_) ((ACT m) s_ x_))))))))))))

  ;; (3) action compatible with ring multiplication
  (add-axiom! *library* 'module-act-mul-compat
    '(FORALL m (IMPLIES (IS-MODULE m)
       (FORALL r_ (IMPLIES (IN r_ (CARR (SCAL m)))
         (FORALL s_ (IMPLIES (IN s_ (CARR (SCAL m)))
           (FORALL x_ (IMPLIES (IN x_ (VEC m))
             (= ((ACT m) ((MUL (SCAL m)) r_ s_) x_)
                ((ACT m) r_ ((ACT m) s_ x_))))))))))))

  ;; (4) unital
  (add-axiom! *library* 'module-act-unital
    '(FORALL m (IMPLIES (IS-MODULE m)
       (FORALL x_ (IMPLIES (IN x_ (VEC m))
         (= ((ACT m) (ONE (SCAL m)) x_) x_)))))))

;;; Notation -- read by wff->english / the proof reader (operators.scm).
(notation! 'IS-MODULE             'kind 'predicate 'arity 1 'noun "module" 'article "a")
