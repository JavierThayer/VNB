;;; dual-space.scm -- THE DUAL of a real normed vector space, as an OBJECT.
;;;
;;; linear-functional.scm already has the PREDICATES -- IS-LINEAR-FUNCTIONAL,
;;; IS-BOUNDED-LINEAR-FUNCTIONAL -- and the functoid DUAL-NORM(m,f), and
;;; hahn-banach-*.scm / norm-as-sup-proof.scm reason with them one functional at
;;; a time.  What was missing is the SPACE: the normed vector space whose
;;; vectors ARE the bounded linear functionals on m and whose norm is DUAL-NORM.
;;; This file builds it and states that it is one.  Vocabulary only, no proofs.
;;;
;;;   DUAL-VEC(m)   { f in FUN(VEC m, RR) : IS-BOUNDED-LINEAR-FUNCTIONAL(m,f) }
;;;   DUAL(m)       the NORMED-VECTOR-SPACE 7-tuple over that carrier
;;;
;;; NOTHING IS RESTATED.  The carrier is carved out of FUN(VEC m, RR) by the
;;; EXISTING predicate; the norm slot is the EXISTING functoid DUAL-NORM.  The
;;; only new mathematics in the file is the single claim that the seven slots fit
;;; together into a normed vector space (dual-is-normed-vector-space).
;;;
;;; THE SHAPE IS FORCED, and it is worth saying why, because it is the same rule
;;; that forces the shape of complex-inner-product.scm next door.  An accessor
;;; name lives at exactly ONE slot index library-wide (register-accessor-index!,
;;; structures.scm:245; a second claim WITHDRAWS the reduction and makes the name
;;; ambiguous for everyone).  So a tuple that is to be read with VEC / VADD /
;;; VNRM must put them where NORMED-VECTOR-SPACE put them: SCAL 1, VEC 2, VADD 3,
;;; VZERO 4, VNEG 5, ACT 6, VNRM 7.  DUAL(m) is that tuple, with the pointwise
;;; operations in slots 3-6.
;;;
;;; THE FUNCTOID TRAP (CLAUDE.md, "Where a definition lives").  DUAL-VEC is a
;;; `def-functoid', so it installs a rewrite MACETE and no theorem: `mac' unfolds
;;; it in a GOAL, and `mac-h' CANNOT unfold it in an ASSUMPTION -- it warns
;;; "unknown theorem/macete" and the driver sails on with the hypothesis intact.
;;; Every proof about the dual reads a functional OUT of the context ("let f be a
;;; vector of DUAL(m)"), so the membership law has to be stated separately:
;;; `dual-vec-membership' below is that law, and it is stamped `definitional' --
;;; the functoid unfold composed with the SEP separation schema, both trusted
;;; base, i.e. exactly the IFF `def-predicate' would have generated had DUAL-VEC
;;; been a predicate.  Same treatment, same reasoning, as span-membership
;;; (mod-seq.scm) and principal-ideal-membership (ideal.scm).  The three slot
;;; readouts below are stamped the same way and for the same reason: each is the
;;; DUAL functoid unfold composed with an NTH projection.
;;;
;;; A DEFECT IT INHERITED, and no longer does (repaired 2026-08-23).  Until that
;;; date IS-NORMED-VECTOR-SPACE WAS UNSATISFIABLE, so
;;; `dual-is-normed-vector-space' below -- and every other theorem in the tree
;;; stated over that predicate -- was VACUOUSLY true.  normed-vector-space.scm
;;; declared `(substructure SCAL RING)', whose IS-RING conjunct pins
;;; length(SCAL s) = 6, and then pinned `scal(s) = rr-normed-field', where
;;; RR-NORMED-FIELD is the SEVEN-tuple [RR binplus bintimes binneg 0 1 abs]
;;; (numeric-instances.scm:250).  Six equals seven.  The one-line repair recorded
;;; here -- pin the scalars through the view that exists for exactly this
;;; purpose,
;;;     (law "scal(s) = normed-field-as-commutative-ring(rr-normed-field)")
;;; -- HAS NOW BEEN MADE, in normed-vector-space.scm, whose header carries the
;;; full account.  What it cost, measured rather than estimated: ZERO bills
;;; moved, every one byte-identical, because no proof in the library unfolds
;;; IS-NORMED-VECTOR-SPACE.  The blast radius this note warned about was real
;;; but empty.
;;;
;;; ONE CONSEQUENCE FOR THIS FILE, and it is not discharged.  A satisfiable
;;; predicate is not an INHABITED one: nothing in the tree exhibits a normed
;;; vector space, so `dual-is-normed-vector-space' asserts that DUAL(m) is one
;;; whenever m is, and no m is known to be.  That is an ordinary unproved
;;; hypothesis now, not a contradiction -- which is the whole difference the
;;; repair makes.
;;;
;;; Dependencies: normed-vector-space.scm (the 7-slot shape and its accessors),
;;; linear-functional.scm (IS-BOUNDED-LINEAR-FUNCTIONAL, DUAL-NORM),
;;; numeric-instances.scm is NOT needed -- RR-NORMED-FIELD is named, not unfolded.

;;; ====================================================================
;;; the carrier: the bounded linear functionals on m
;;; ====================================================================

(def-functoid 'DUAL-VEC '(m)
  '(SEP f_ (FUN (VEC m) RR) (IS-BOUNDED-LINEAR-FUNCTIONAL m f_)))

;;; The membership law -- see THE FUNCTOID TRAP above.  `definitional': the
;;; DUAL-VEC unfold composed with SEP separation, nothing else.
(fluid-let ((*current-provenance* 'definitional))
  (support 'dual-vec-membership
    '(FORALL m (FORALL f
       (IFF (IN f (DUAL-VEC m))
            (AND (IN f (FUN (VEC m) RR))
                 (IS-BOUNDED-LINEAR-FUNCTIONAL m f)))))))

;;; ====================================================================
;;; the dual space itself
;;; ====================================================================

;;; DUAL(m) = [ RR-NORMED-FIELD,          scalars (the reals, as m's are)
;;;             DUAL-VEC(m),              vectors: the bounded functionals
;;;             (f,g) |-> (x |-> f x + g x),      pointwise sum
;;;             x |-> 0,                          the zero functional
;;;             f |-> (x |-> -(f x)),             pointwise negation
;;;             (r,f) |-> (x |-> r * f x),        pointwise scaling
;;;             f |-> DUAL-NORM(m,f) ]            the operator norm
;;;
;;; Every operation is POINTWISE, so each one is a VNB-LAMBDA whose body is
;;; itself a VNB-LAMBDA on VEC(m): a vector of DUAL(m) is a function, and the
;;; operations of a function space act on values.
(def-functoid 'DUAL '(m)
  '(LIST RR-NORMED-FIELD
         (DUAL-VEC m)
         (VNB-LAMBDA (LIST f_ g_) (CARTESIAN (DUAL-VEC m) (DUAL-VEC m))
           (VNB-LAMBDA x_ (VEC m) (+ (f_ x_) (g_ x_))))
         (VNB-LAMBDA x_ (VEC m) 0)
         (VNB-LAMBDA f_ (DUAL-VEC m)
           (VNB-LAMBDA x_ (VEC m) (- (f_ x_))))
         (VNB-LAMBDA (LIST r_ f_) (CARTESIAN RR (DUAL-VEC m))
           (VNB-LAMBDA x_ (VEC m) (* r_ (f_ x_))))
         (VNB-LAMBDA f_ (DUAL-VEC m) (DUAL-NORM m f_))))

;;; ====================================================================
;;; slot readouts -- the DUAL unfold composed with an NTH projection.
;;; `definitional' for the same reason dual-vec-membership is.
;;; ====================================================================

(fluid-let ((*current-provenance* 'definitional))
  (support 'dual-scal
    '(FORALL m (== (SCAL (DUAL m)) RR-NORMED-FIELD)))
  (support 'dual-carrier
    '(FORALL m (== (VEC (DUAL m)) (DUAL-VEC m))))
  ;; the norm slot APPLIED -- the form a proof wants, so that citing it does not
  ;; also owe a beta-reduction (and, with it, the `lam-b' typing obligation).
  (support 'dual-norm-value
    '(FORALL m (FORALL f (IMPLIES (IN f (DUAL-VEC m))
       (== ((VNRM (DUAL m)) f) (DUAL-NORM m f)))))))

;;; ====================================================================
;;; ... and it is a normed vector space
;;; ====================================================================

;;; The one piece of mathematics in the file.  See the DEFECT note in the header
;;; before leaning on it: while IS-NORMED-VECTOR-SPACE stays unsatisfiable this
;;; is a vacuous truth, and the warrant below is what it will be worth once the
;;; scalar slot of normed-vector-space.scm is pinned through the view.
(support 'dual-is-normed-vector-space
  '(FORALL m (IMPLIES (IS-NORMED-VECTOR-SPACE m)
     (IS-NORMED-VECTOR-SPACE (DUAL m)))))
(warrant! 'dual-is-normed-vector-space 'reference
  "The dual of a normed vector space is a normed vector space.  The bounded
   linear functionals are closed under pointwise sum, negation and real scaling
   (each operation preserves additivity, homogeneity and boundedness, the bound
   constants adding resp. scaling), so DUAL-VEC(m) with those operations is a
   real vector space with the zero functional as its zero.  The operator norm is
   a norm on it: DUAL-NORM(m,f) >= 0 by definition; DUAL-NORM(m,f) = 0 forces
   |f(x)| <= 0 for every x, hence f = 0; DUAL-NORM(m, r.f) = |r| DUAL-NORM(m,f)
   since c bounds |f| iff |r|c bounds |r f|; and DUAL-NORM(m, f+g) <=
   DUAL-NORM(m,f) + DUAL-NORM(m,g) because the sum of the two bounds is a bound
   for the sum and DUAL-NORM is the LEAST bound.  Standard: Rudin, Functional
   Analysis, 4.1; Conway, A Course in Functional Analysis, III.1.")
(topic! 'dual-is-normed-vector-space 'analysis)
(gloss! 'dual-is-normed-vector-space
  "For every normed vector space m, the tuple DUAL(m) -- the bounded linear
   functionals on m, with pointwise addition, negation and real scaling, and the
   operator norm DUAL-NORM -- is itself a normed vector space.")

;;; -----------------------------------------------------------------------
;;; Notation -- read by wff->english / the proof reader (operators.scm).
(notation! 'DUAL 'kind 'functoid 'arity 1
           'english "the dual space of $1"
           'tex "{$1}^{*}")
(notation! 'DUAL-VEC 'kind 'functoid 'arity 1
           'english "the bounded linear functionals on $1")
