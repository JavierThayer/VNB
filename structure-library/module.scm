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
;;; IS-VECTOR-SPACE(m) <=> IS-MODULE(m) AND IS-FIELD(SCAL m)).
;;;
;;; Dependencies: ring.scm (RING, IS-RING, A, ADD, MUL, ONE),
;;;               operation-properties.scm (is-associative/commutative/...).

(fluid-let ((*current-provenance* 'definitional))

  ;; --- register the structure shape: accessors + structure-table + class ---
  (hash-table-set! *structure-table* 'MODULE
    (%make-structure-def 'MODULE
      '((SCAL  substructure RING)
        (VEC   carrier)
        (VADD  op (CARTESIAN VEC VEC) VEC)
        (VZERO constant VEC)
        (VNEG  op VEC VEC)
        (ACT   op (CARTESIAN (CARR SCAL) VEC) VEC))
      '()                                ; no property-clause laws: IS-MODULE is hand-written
      (current-load-pathname)))

  (for-each (lambda (p)
              (register-constant! (car p) 'accessor)
              (install-accessor-macete! (car p) (cdr p)))
            '((SCAL . 1) (VEC . 2) (VADD . 3) (VZERO . 4) (VNEG . 5) (ACT . 6)))

  ;; --- the complete IS-MODULE definition (design A) ---
  ;; bound vars r_ s_ (scalars) and x_ y_ (vectors) carry trailing underscores
  ;; to dodge case-fold collisions with the accessors / ring ops.
  (theory-add-axiom! *current-theory* 'IS-MODULE
    `(FORALL m
       (IFF (IS-MODULE m)
         ,(conjuncts->and
            (list
              ;; shape
              '(= (LENGTH m) 6)
              '(IS-RING (SCAL m))
              '(IN (VEC m) SET)
              '(IN (VADD m) (FUN (CARTESIAN (VEC m) (VEC m)) (VEC m)))
              '(IN (VZERO m) (VEC m))
              '(IN (VNEG m) (FUN (VEC m) (VEC m)))
              '(IN (ACT m) (FUN (CARTESIAN (CARR (SCAL m)) (VEC m)) (VEC m)))
              ;; vector part (VEC, VADD, VZERO, VNEG) is an abelian group
              '(is-associative (VADD m) (VEC m))
              '(is-commutative (VADD m) (VEC m))
              '(is-identity (VADD m) (VZERO m) (VEC m))
              '(has-inverses (VADD m) (VZERO m) (VNEG m) (VEC m))
              ;; (1) action distributes over vector addition:  r.(x+y) = r.x + r.y
              '(FORALL r_ (IMPLIES (IN r_ (CARR (SCAL m)))
                 (FORALL x_ (IMPLIES (IN x_ (VEC m))
                   (FORALL y_ (IMPLIES (IN y_ (VEC m))
                     (= ((ACT m) r_ ((VADD m) x_ y_))
                        ((VADD m) ((ACT m) r_ x_) ((ACT m) r_ y_)))))))))
              ;; (2) action distributes over ring addition:  (r+s).x = r.x + s.x
              '(FORALL r_ (IMPLIES (IN r_ (CARR (SCAL m)))
                 (FORALL s_ (IMPLIES (IN s_ (CARR (SCAL m)))
                   (FORALL x_ (IMPLIES (IN x_ (VEC m))
                     (= ((ACT m) ((ADD (SCAL m)) r_ s_) x_)
                        ((VADD m) ((ACT m) r_ x_) ((ACT m) s_ x_)))))))))
              ;; (3) action compatible with ring multiplication:  (r*s).x = r.(s.x)
              '(FORALL r_ (IMPLIES (IN r_ (CARR (SCAL m)))
                 (FORALL s_ (IMPLIES (IN s_ (CARR (SCAL m)))
                   (FORALL x_ (IMPLIES (IN x_ (VEC m))
                     (= ((ACT m) ((MUL (SCAL m)) r_ s_) x_)
                        ((ACT m) r_ ((ACT m) s_ x_)))))))))
              ;; (4) unital:  1.x = x
              '(FORALL x_ (IMPLIES (IN x_ (VEC m))
                 (= ((ACT m) (ONE (SCAL m)) x_) x_))))))))

  ;; --- MODULE as the proper class { m | IS-MODULE(m) } ---
  (theory-add-axiom! *current-theory* 'MODULE-class
    '(FORALL s (IFF (IN s MODULE) (IS-MODULE s)))))

;;; -----------------------------------------------------------------------
;;; Projected module laws.  Each is a CONJUNCT of the IS-MODULE definition,
;;; surfaced as a standalone citable theorem so a proof can bc*/inst it
;;; directly instead of peeling the 15-conjunct IFF.  Definitional (a
;;; projection of the definition), not new mathematical content.

(fluid-let ((*current-provenance* 'definitional))

  ;; the scalar component is a ring
  (theory-add-axiom! *current-theory* 'module-scalar-ring
    '(FORALL m (IMPLIES (IS-MODULE m) (IS-RING (SCAL m)))))

  ;; ring zero lives in the scalar carrier (an action argument)
  (theory-add-axiom! *current-theory* 'module-scalar-zero-in
    '(FORALL m (IMPLIES (IS-MODULE m) (IN (ZERO (SCAL m)) (CARR (SCAL m))))))

  ;; the zero vector is a vector (the shape conjunct, surfaced for rfl's
  ;; definedness obligation on VZERO terms)
  (theory-add-axiom! *current-theory* 'module-vzero-in
    '(FORALL m (IMPLIES (IS-MODULE m) (IN (VZERO m) (VEC m)))))

  ;; action closure:  r . x  is a vector
  (theory-add-axiom! *current-theory* 'module-act-type
    '(FORALL m (IMPLIES (IS-MODULE m)
       (FORALL r_ (IMPLIES (IN r_ (CARR (SCAL m)))
         (FORALL x_ (IMPLIES (IN x_ (VEC m))
           (IN ((ACT m) r_ x_) (VEC m)))))))))

  ;; addition and negation close on the vectors -- the same read-off of the shape
  ;; conjuncts (IN (VADD m) (FUN (CARTESIAN (VEC m) (VEC m)) (VEC m))) and
  ;; (IN (VNEG m) (FUN (VEC m) (VEC m))) that module-act-type is of its own.
  ;; Surfaced because whole-module-is-submodule needs all three closures, and
  ;; IS-SUBMODULE states them in applied form.
  (theory-add-axiom! *current-theory* 'module-vadd-type
    '(FORALL m (IMPLIES (IS-MODULE m)
       (FORALL x_ (IMPLIES (IN x_ (VEC m))
         (FORALL y_ (IMPLIES (IN y_ (VEC m))
           (IN ((VADD m) x_ y_) (VEC m)))))))))

  (theory-add-axiom! *current-theory* 'module-vneg-type
    '(FORALL m (IMPLIES (IS-MODULE m)
       (FORALL x_ (IMPLIES (IN x_ (VEC m))
         (IN ((VNEG m) x_) (VEC m)))))))

  ;; (1) action distributes over vector addition
  (theory-add-axiom! *current-theory* 'module-act-distrib-vec
    '(FORALL m (IMPLIES (IS-MODULE m)
       (FORALL r_ (IMPLIES (IN r_ (CARR (SCAL m)))
         (FORALL x_ (IMPLIES (IN x_ (VEC m))
           (FORALL y_ (IMPLIES (IN y_ (VEC m))
             (= ((ACT m) r_ ((VADD m) x_ y_))
                ((VADD m) ((ACT m) r_ x_) ((ACT m) r_ y_))))))))))))

  ;; (2) action distributes over ring addition
  (theory-add-axiom! *current-theory* 'module-act-distrib-scalar
    '(FORALL m (IMPLIES (IS-MODULE m)
       (FORALL r_ (IMPLIES (IN r_ (CARR (SCAL m)))
         (FORALL s_ (IMPLIES (IN s_ (CARR (SCAL m)))
           (FORALL x_ (IMPLIES (IN x_ (VEC m))
             (= ((ACT m) ((ADD (SCAL m)) r_ s_) x_)
                ((VADD m) ((ACT m) r_ x_) ((ACT m) s_ x_))))))))))))

  ;; (3) action compatible with ring multiplication
  (theory-add-axiom! *current-theory* 'module-act-mul-compat
    '(FORALL m (IMPLIES (IS-MODULE m)
       (FORALL r_ (IMPLIES (IN r_ (CARR (SCAL m)))
         (FORALL s_ (IMPLIES (IN s_ (CARR (SCAL m)))
           (FORALL x_ (IMPLIES (IN x_ (VEC m))
             (= ((ACT m) ((MUL (SCAL m)) r_ s_) x_)
                ((ACT m) r_ ((ACT m) s_ x_))))))))))))

  ;; (4) unital
  (theory-add-axiom! *current-theory* 'module-act-unital
    '(FORALL m (IMPLIES (IS-MODULE m)
       (FORALL x_ (IMPLIES (IN x_ (VEC m))
         (= ((ACT m) (ONE (SCAL m)) x_) x_)))))))

;;; Notation -- read by wff->english / the proof reader (operators.scm).
(notation! 'IS-MODULE             'kind 'predicate 'arity 1 'noun "module" 'article "a")
