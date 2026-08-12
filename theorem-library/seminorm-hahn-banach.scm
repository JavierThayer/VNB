;;; seminorm-hahn-banach.scm -- seminorms on a K-vector space and the
;;; HAHN-BANACH extension theorem dominated by a seminorm (statement only).
;;; Seed for functional analysis, K = RR or CC (mainly CC).  Added 2026-07-22.
;;;
;;; MODELLING.  A "K-vector space" is a MODULE m whose scalar ring SCAL(m) is a
;;; NORMED FIELD K (so K carries an absolute value FNRM = |.|).  For K = CC use
;;; SCAL(m) = a CC normed field; for K = RR, RR-NORMED-FIELD.  Scalars live in
;;; CARR(SCAL m); scalar ops are (ADD/MUL (SCAL m)); |lambda| = (FNRM (SCAL m)).
;;; Functionals here are K-VALUED (f : VEC(m) -> CARR(SCAL m)) -- the existing
;;; linear-functional.scm is RR-valued only, so these are new.
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
      '(IS-NORMED-FIELD (SCAL m))
      '(IN p (FUN (VEC m) RR))
      (forall-guarded 'x '(IN x (VEC m)) '(<= 0 (p x)))
      (forall-guarded 'x '(IN x (VEC m))
        (forall-guarded 'y '(IN y (VEC m))
          '(<= (p ((VADD m) x y)) (+ (p x) (p y)))))
      (forall-guarded 'lam '(IN lam (CARR (SCAL m)))
        (forall-guarded 'x '(IN x (VEC m))
          '(= (p ((ACT m) lam x)) (* ((FNRM (SCAL m)) lam) (p x))))))))
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
(support 'hahn-banach-seminorm
  (forall-guarded '(m p s f)
    (list
      '(IS-MODULE m)
      '(IS-NORMED-FIELD (SCAL m))
      '(IS-SEMINORM m p)
      '(IS-SUBMODULE m s)
      '(IS-K-LINEAR-ON m s f)
      '(FORALL x (IMPLIES (IN x s) (<= ((FNRM (SCAL m)) (f x)) (p x)))))
    (forsome-guarded 'ff '(IS-K-LINEAR m ff)
      (conjuncts->and
        (list
          '(EXTENDS-ON s ff f)
          '(FORALL x (IMPLIES (IN x (VEC m))
             (<= ((FNRM (SCAL m)) (ff x)) (p x)))))))))
(warrant! 'hahn-banach-seminorm 'reference
  '(yosida "Hahn-Banach Extension Theorem, Ch. IV.1" 119))
(gloss! 'hahn-banach-seminorm
  "Hahn-Banach, seminorm-dominated form, over K = RR or CC.  Let m be a K-vector
   space (a module whose scalar field SCAL(m) is a normed field), p a seminorm on
   m, s a subspace, and f a K-linear functional on s with |f(x)| <= p(x) for x in s.
   Then f extends to a K-linear functional ff on all of m with |ff(x)| <= p(x)
   everywhere.  The proof is the classic transfinite/Zorn extension (one dimension
   at a time, dominated bound preserved); over CC it is the Bohnenblust-Sobczyk
   reduction to the real part.  Sources: Yosida IV.1; the user's notes (exercise).")
(topic! 'hahn-banach-seminorm 'analysis)
;; Intended proof leans on Zorn (maximal dominated extension).
(rests-on 'hahn-banach-seminorm '(zorn-lemma))
