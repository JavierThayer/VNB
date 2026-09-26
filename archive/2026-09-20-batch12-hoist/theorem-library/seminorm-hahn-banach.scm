;;; seminorm-hahn-banach.scm -- seminorms on a K-vector space and the
;;; HAHN-BANACH extension theorem dominated by a seminorm (statement only).
;;; Seed for functional analysis, K = RR or CC (mainly CC).  Added 2026-07-22.
;;;
;;; MODELLING.  A "K-vector space" is a MODULE m whose scalars are a NORMED
;;; FIELD K (so K carries an absolute value FNRM = |.|).  Scalars live in
;;; CARR(SCAL m); scalar ops are (ADD/MUL (SCAL m)).  Functionals here are
;;; K-VALUED (f : VEC(m) -> CARR(SCAL m)) -- the existing linear-functional.scm
;;; is RR-valued only, so these are new.
;;;
;;; ====================================================================
;;; THE SCALAR SLOT -- and the inconsistency that lived in it (repaired
;;; 2026-08-24).  Fourth appearance of one defect; see normed-vector-space.scm
;;; and finite-dimensional.scm for the first three.
;;; ====================================================================
;;;
;;; IS-SEMINORM used to say, of one m, BOTH
;;;
;;;     (IS-MODULE m)                 -> MODULE declares (substructure SCAL RING),
;;;                                      so the IFF carries (IS-RING (SCAL m)) and
;;;                                      IS-RING pins length(scal(m)) = 6
;;;     (IS-NORMED-FIELD (SCAL m))    -> NORMED-FIELD is a SEVEN-slot shape
;;;                                      [CARR ADD MUL NEG ZERO ONE FNRM], so it
;;;                                      pins the SAME term to 7
;;;
;;; Six against seven: IS-SEMINORM(m, p) |- falsity, the predicate was EMPTY, and
;;; every theorem carrying it was VACUOUSLY true.  IS-SEMINORM-FAMILY and (through
;;; it) IS-FRECHET-STRUCTURE carried the same pair, and the four supports
;;; hahn-banach-seminorm, closed-graph-theorem, open-mapping-theorem and
;;; open-mapping-bounded-inverse were vacuous on it.  The derivation is
;;; scratchpad/sn-falsity-probe.scm; the standing check is test-suite-negative.scm
;;; section 2f.
;;;
;;; THE REPAIR: NAME THE FIELD.  A normed field reaches the ring world only
;;; through NORMED-FIELD-AS-COMMUTATIVE-RING (views.scm:167), which projects
;;; slots 1..6 into a fresh 6-tuple -- and that projection is what a scalar SLOT
;;; must hold.  So the field is named by its own binder and the slot is pinned to
;;; its ring view:
;;;
;;;     FORSOME fld.  IS-NORMED-FIELD(fld)
;;;                   and scal(m) = normed-field-as-commutative-ring(fld)
;;;                   and  ... p(act(m)(lam, x)) = (fnrm(fld))(lam) * p(x)
;;;
;;; 6 = 6, and the homogeneity law reaches the norm through `fld'.
;;;
;;; WHY NOT THE IS-FIELD-RING SHAPE, which is how finite-dimensional.scm's
;;; sibling defect was repaired?  Because THIS law reads FNRM -- the one slot the
;;; ring view DROPS.  `carr', `add', `mul', `one' survive the projection and
;;; IS-K-LINEAR-ON / IS-K-LINEAR read their scalars through them unchanged; the
;;; NORM does not survive it and there is no six-slot predicate that can speak
;;; about it.  Naming the field is the only way to reach it.
;;;
;;; The three objections field.scm:101 records against the existential, and where
;;; each stands here:
;;;   * "every unfolding proof must skolemize the FORSOME" -- measured: NO proof
;;;     in the tree unfolds any of these predicates or cites any of the four
;;;     supports.  The cost is zero today and is paid by whoever proves them.
;;;   * "the satisfiability audit does not descend into a FORSOME, so the pin
;;;     stops being watched" -- true, and it is why section 2f of
;;;     test-suite-negative.scm exists: the refusal is checked directly, with an
;;;     anti-vacuity control beside it.
;;;   * "it demands an instance of the bigger shape to exhibit anything" -- does
;;;     not apply: RR-NORMED-FIELD and CC-NORMED-FIELD are both declared
;;;     (numeric-instances.scm), where the tree has no 8-tuple FIELD but QQ-FIELD.
;;;
;;; Loads after module / normed-field / finite-dimensional (IS-SUBMODULE,
;;; EXTENDS-ON) and order-zorn (zorn-lemma).
;;; ====================================================================

;;; ---- vocabulary --------------------------------------------------------

;;; IS-SEMINORM(m, p): p : VEC(m) -> RR is nonnegative, subadditive and
;;; absolutely homogeneous (p(lambda.x) = |lambda| p(x)).  Unlike a norm, p may
;;; vanish off zero.
(def-predicate 'IS-SEMINORM '(m p)
  (conjuncts->and
    (list
      '(IS-MODULE m)
      '(IN p (FUN (VEC m) RR))
      (forall-guarded 'x '(IN x (VEC m)) '(<= 0 (p x)))
      (forall-guarded 'x '(IN x (VEC m))
        (forall-guarded 'y '(IN y (VEC m))
          '(<= (p ((VADD m) x y)) (+ (p x) (p y)))))
      ;; absolute homogeneity, and with it the statement that the scalars ARE a
      ;; normed field.  The field is NAMED (see THE SCALAR SLOT in the header):
      ;; scal(m) holds its six-slot RING VIEW -- which is what IS-MODULE's
      ;; (substructure SCAL RING) pins -- and the law reaches the absolute value
      ;; through `fld', the norm being the one slot the view drops.
      (forsome-guarded '(fld)
        (list '(IS-NORMED-FIELD fld)
              '(= (SCAL m) (NORMED-FIELD-AS-COMMUTATIVE-RING fld)))
        (forall-guarded 'lam '(IN lam (CARR (SCAL m)))
          (forall-guarded 'x '(IN x (VEC m))
            '(= (p ((ACT m) lam x)) (* ((FNRM fld) lam) (p x)))))))))
(notation! 'IS-SEMINORM 'kind 'predicate 'arity 2
           'english "$2 is a seminorm on $1")

;;; IS-K-LINEAR-ON(m, s, f): f : s -> CARR(SCAL m) is K-linear on the submodule s.
(def-predicate 'IS-K-LINEAR-ON '(m s f)
  (conjuncts->and
    (list
      '(IS-MODULE m)
      '(IS-SUBMODULE m s)
      '(IN f (FUN s (CARR (SCAL m))))
      (forall-guarded 'x '(IN x s)
        (forall-guarded 'y '(IN y s)
          '(= (f ((VADD m) x y)) ((ADD (SCAL m)) (f x) (f y)))))
      (forall-guarded 'lam '(IN lam (CARR (SCAL m)))
        (forall-guarded 'x '(IN x s)
          '(= (f ((ACT m) lam x)) ((MUL (SCAL m)) lam (f x))))))))
(notation! 'IS-K-LINEAR-ON 'kind 'predicate 'arity 3
           'english "$3 is a K-linear functional on the submodule $2 of $1")

;;; IS-K-LINEAR(m, f): f : VEC(m) -> CARR(SCAL m) is K-linear on the whole space.
(def-predicate 'IS-K-LINEAR '(m f)
  (conjuncts->and
    (list
      '(IS-MODULE m)
      '(IN f (FUN (VEC m) (CARR (SCAL m))))
      (forall-guarded 'x '(IN x (VEC m))
        (forall-guarded 'y '(IN y (VEC m))
          '(= (f ((VADD m) x y)) ((ADD (SCAL m)) (f x) (f y)))))
      (forall-guarded 'lam '(IN lam (CARR (SCAL m)))
        (forall-guarded 'x '(IN x (VEC m))
          '(= (f ((ACT m) lam x)) ((MUL (SCAL m)) lam (f x))))))))
(notation! 'IS-K-LINEAR 'kind 'predicate 'arity 2
           'english "$2 is a K-linear functional on $1")

;;; ---- Hahn-Banach dominated by a seminorm --------------------------------

;;; A K-linear functional on a subspace, dominated by a seminorm p (|f| <= p on
;;; the subspace), extends to a K-linear functional on the whole space still
;;; dominated by p.  (Complex/real Hahn-Banach; Bohnenblust-Sobczyk for CC.)
;;; The scalar field is named by a UNIVERSAL binder here, not an existential:
;;; the domination hypothesis and the conclusion both read its norm, so `fld'
;;; has to scope over the whole implication.  Its two guards are the same pair
;;; IS-SEMINORM's existential carries -- IS-NORMED-FIELD(fld), and scal(m) is
;;; fld's six-slot ring view -- so the statement pins length(scal(m)) to 6 only,
;;; agreeing with IS-MODULE.
(support 'hahn-banach-seminorm
  (forall-guarded '(m p s f fld)
    (list
      '(IS-MODULE m)
      '(IS-NORMED-FIELD fld)
      '(= (SCAL m) (NORMED-FIELD-AS-COMMUTATIVE-RING fld))
      '(IS-SEMINORM m p)
      '(IS-SUBMODULE m s)
      '(IS-K-LINEAR-ON m s f)
      '(FORALL x (IMPLIES (IN x s) (<= ((FNRM fld) (f x)) (p x)))))
    (forsome-guarded 'ff '(IS-K-LINEAR m ff)
      (conjuncts->and
        (list
          '(EXTENDS-ON s ff f)
          '(FORALL x (IMPLIES (IN x (VEC m))
             (<= ((FNRM fld) (ff x)) (p x)))))))))
(warrant! 'hahn-banach-seminorm 'reference
  '(yosida "Hahn-Banach Extension Theorem, Ch. IV.1" 119))
(gloss! 'hahn-banach-seminorm
  "Hahn-Banach, seminorm-dominated form, over K = RR or CC.  Let m be a K-vector
   space -- a module whose scalars are the normed field fld, SCAL(m) holding fld's
   six-slot ring view -- p a seminorm on m, s a subspace, and f a K-linear
   functional on s with |f(x)| <= p(x) for x in s, |.| = FNRM(fld).
   Then f extends to a K-linear functional ff on all of m with |ff(x)| <= p(x)
   everywhere.  The proof is the classic transfinite/Zorn extension (one dimension
   at a time, dominated bound preserved); over CC it is the Bohnenblust-Sobczyk
   reduction to the real part.  Sources: Yosida IV.1; the user's notes (exercise).")
(topic! 'hahn-banach-seminorm 'analysis)
;; Intended proof leans on Zorn (maximal dominated extension).
(rests-on 'hahn-banach-seminorm '(zorn-lemma))
