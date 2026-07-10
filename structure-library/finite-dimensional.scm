;;; finite-dimensional.scm -- finite-dimensional vector spaces, Zorn-free.
;;;
;;; Following the user's plan (no linear algebra needed for the definition):
;;;   * a MODULE is NOETHERIAN if it satisfies the ascending chain condition
;;;     (ACC) on submodules -- every nondecreasing chain of submodules is
;;;     eventually constant;
;;;   * a VECTOR SPACE is a module whose scalars form a field;
;;;   * a vector space is FINITE-DIMENSIONAL iff it is noetherian.
;;;
;;; No basis, no dimension count -- just the chain condition.  This is exactly
;;; what makes Hahn-Banach for finite-dimensional real normed spaces Zorn-free:
;;; one extends a bounded linear functional one dimension higher at a time, and
;;; ACC bounds the iteration.  (Zorn is kept for the general case, later.)
;;;
;;; Builds on module.scm (MODULE/IS-MODULE/SCAL/VEC/VADD/VZERO/VNEG/ACT) and
;;; field.scm (IS-FIELD).  POWER is the kernel powerset former; SUBSET the
;;; kernel subset predicate.  Bound vars carry trailing underscores to dodge
;;; case-fold collisions with the module accessors (per module.scm convention).

;;; A vector space is a module over a field.
(def-predicate 'IS-VECTOR-SPACE '(m)
  '(AND (IS-MODULE m) (IS-FIELD (SCAL m))))

;;; S is a submodule of m: a subset of the vectors that contains the zero vector
;;; and is closed under vector addition, negation, and the scalar action.
(def-predicate 'IS-SUBMODULE '(m s)
  '(AND (SUBSET s (VEC m))
   (AND (IN (VZERO m) s)
   (AND (FORALL x_ (IMPLIES (IN x_ s)
          (FORALL y_ (IMPLIES (IN y_ s) (IN ((VADD m) x_ y_) s)))))
   (AND (FORALL x_ (IMPLIES (IN x_ s) (IN ((VNEG m) x_) s)))
        (FORALL r_ (IMPLIES (IN r_ (CARR (SCAL m)))
          (FORALL x_ (IMPLIES (IN x_ s) (IN ((ACT m) r_ x_) s))))))))))

;;; The four closure conjuncts of IS-SUBMODULE, surfaced as standalone citable
;;; theorems so a proof `fact's each directly instead of unfolding IS-SUBMODULE
;;; (which mac-h would DELETE, taking the hypothesis every other `fact' guarded
;;; on IS-SUBMODULE needs).  Definitional: each is a projection of the IFF above,
;;; exactly as module.scm surfaces module-vadd-type / module-act-type from
;;; IS-MODULE.  (submodule-subset, the fifth, is already a proven theorem in
;;; submodule-fg-proof.scm.)
(fluid-let ((*current-provenance* 'definitional))
  (theory-add-axiom! *current-theory* 'submodule-vzero-in
    '(FORALL m (FORALL s (IMPLIES (IS-SUBMODULE m s) (IN (VZERO m) s)))))
  (theory-add-axiom! *current-theory* 'submodule-vadd-closed
    '(FORALL m (FORALL s (IMPLIES (IS-SUBMODULE m s)
       (FORALL x_ (IMPLIES (IN x_ s)
         (FORALL y_ (IMPLIES (IN y_ s) (IN ((VADD m) x_ y_) s)))))))))
  (theory-add-axiom! *current-theory* 'submodule-vneg-closed
    '(FORALL m (FORALL s (IMPLIES (IS-SUBMODULE m s)
       (FORALL x_ (IMPLIES (IN x_ s) (IN ((VNEG m) x_) s)))))))
  (theory-add-axiom! *current-theory* 'submodule-act-closed
    '(FORALL m (FORALL s (IMPLIES (IS-SUBMODULE m s)
       (FORALL r_ (IMPLIES (IN r_ (CARR (SCAL m)))
         (FORALL x_ (IMPLIES (IN x_ s) (IN ((ACT m) r_ x_) s))))))))))

;;; m is NOETHERIAN: it is a module, and every nondecreasing chain of submodules
;;; f : NN -> POWER(VEC m) is eventually constant (the ascending chain condition).
(def-predicate 'IS-NOETHERIAN '(m)
  '(AND (IS-MODULE m)
     (FORALL f_ (IMPLIES (IN f_ (FUN NN (POWER (VEC m))))
       (IMPLIES (AND (FORALL n_ (IMPLIES (IN n_ NN) (IS-SUBMODULE m (f_ n_))))
                     (FORALL n_ (IMPLIES (IN n_ NN) (SUBSET (f_ n_) (f_ (succ n_))))))
         (FORSOME k_ (AND (IN k_ NN)
            (FORALL n_ (IMPLIES (AND (IN n_ NN) (<= k_ n_))
              (= (f_ n_) (f_ k_)))))))))))

;;; A finite-dimensional vector space is a noetherian vector space.
(def-predicate 'IS-FINITE-DIMENSIONAL '(m)
  '(AND (IS-VECTOR-SPACE m) (IS-NOETHERIAN m)))

;;; A subspace of a (real) vector space is exactly a submodule.
(def-predicate 'IS-SUBSPACE '(m s)
  '(IS-SUBMODULE m s))

;;; SPAN-ADD-ONE(m, s, v) = s + RR.v = { x + r.v : x in s, r in RR }: the
;;; subspace spanned by s together with one more vector v -- the "one dimension
;;; higher" domain of the Hahn-Banach extension step.
(def-functoid 'SPAN-ADD-ONE '(m s v)
  '(SEP y_ (VEC m)
     (FORSOME x_ (AND (IN x_ s)
       (FORSOME r_ (AND (IN r_ RR)
         (= y_ ((VADD m) x_ ((ACT m) r_ v)))))))))
