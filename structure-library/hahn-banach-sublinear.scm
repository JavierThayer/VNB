;;; structure-library/hahn-banach-sublinear.scm -- the vocabulary of the
;;; Hahn-Banach theorem for a SUBLINEAR functional (RM-3A, 2026-10-10).
;;; DEFINITIONS ONLY; every law is PROVEN in theorem-library/hahn-banach-sublinear.scm
;;; (prefix hbs-).
;;;
;;; A REAL VECTOR SPACE is a MODULE m whose scalar slot is the ring view of the real
;;; normed field: SCAL(m) = NORMED-FIELD-AS-COMMUTATIVE-RING(RR-NORMED-FIELD), the
;;; pin the seminorm vocabulary (seminorm-hahn-banach.scm) and IS-NORMED-VECTOR-SPACE
;;; use.  The theorems carry the pin as a hypothesis; it is not folded into a
;;; predicate here.
;;;
;;; IS-SUBLINEAR(m, p): p : VEC(m) -> RR is subadditive and POSITIVELY homogeneous,
;;;   p(x + y) <= p(x) + p(y),   p(t.x) = t p(x) for every real t >= 0.
;;; The homogeneity law is read with the action of m at a real scalar, so it is
;;; meaningful when the scalars of m are the reals (the pin above); the predicate
;;; itself says nothing about m.  With t = 0 it gives p(vzero) = 0 once 0.x = vzero.
;;;
;;; BINDERS end in an underscore and begin with `hs'; no predicate body and no
;;; kernel-minted eigenvariable uses them.
;;;
;;; Dependencies: module.scm (VEC, VADD, ACT).  Library: analysis (with the theorem
;;; file); it states nothing outside core and algebra.

(def-predicate 'IS-SUBLINEAR '(m p)
  (conjuncts->and
    (list
      '(IN p (FUN (VEC m) RR))
      '(FORALL hsx_ (IMPLIES (IN hsx_ (VEC m))
         (FORALL hsy_ (IMPLIES (IN hsy_ (VEC m))
           (<= (p ((VADD m) hsx_ hsy_)) (+ (p hsx_) (p hsy_)))))))
      '(FORALL hst_ (IMPLIES (IN hst_ RR) (IMPLIES (<= 0 hst_)
         (FORALL hsx_ (IMPLIES (IN hsx_ (VEC m))
           (= (p ((ACT m) hst_ hsx_)) (* hst_ (p hsx_)))))))))))

(notation! 'IS-SUBLINEAR 'kind 'predicate 'arity 2
           'english "$2 is a sublinear functional on $1")
