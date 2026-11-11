;;; ba-cx-vocab.scm -- wave of 2026-11-09/10 (agent BA-1), wired 2026-11-10 from scratchpad/ba1-1109/ba-cx-vocab.scm.
;;; Library: operator-algebras.

;;; ba-cx-vocab.scm -- C(X): the complex continuous functions on a topological space, with the
;;; sup norm, as a 10-tuple of the UNITAL-INVOLUTIVE-BANACH-ALGEBRA shape (ba-vocab.scm), for
;;; F. J. Thayer, "Banach Algebras and Applications", 1.15, 1.23, 1.31, 1.37.
;;; DEFINITIONS ONLY.  The C(X) part of BA-MAP-REPORT.md s.3.2 (M(X) is a later bundle).
;;; Agent BA-1, wave 2026-11-09 (STEP 0).  Destination: structure-library/ba-cx-vocab.scm.
;;; Library: operator-algebras.  Load window: after ba-vocab.scm (the slot layout and VMUL, VONE,
;;; VSTAR), structure-library/top-space (METRIC-TOP, IS-HOM-TOP-SPACE), structure-library/complex
;;; (CC-MS), structure-library/extended-reals-pos (ESUP).
;;;
;;;   CCONT(t)          {f in FUN(PTS t, CC) : f continuous from t to METRIC-TOP(CC-MS)}
;;;   SUP-NORM-T(t, f)  ESUP of {|f(x)| : x in PTS t}  (the pattern of CC-SUP-NORM; ESUP of an
;;;                     empty set is 0, of an unbounded one POS-INF: the theorem that it is the
;;;                     norm of CCONT-ALGEBRA(t) assumes t compact and nonempty)
;;;   CCONT-ALGEBRA(t)  [CC ring view, CCONT(t), pointwise +, 0, -, scalar multiple, SUP-NORM-T,
;;;                     pointwise product, the constant 1, pointwise conjugation]
;;; The intended theorem (agent BA-SW): t a compact Hausdorff TOP-SPACE with PTS(t) nonempty
;;; implies IS-COMMUTATIVE-C-STAR-ALGEBRA(CCONT-ALGEBRA(t)).
;;; For a compact subset K of CC, C(K) is CCONT-ALGEBRA(SUBSPACE-TOP(METRIC-TOP(CC-MS), K)).
;;;
;;; Binders kx*_ (kxf_ kxg_ kxp_ kxc_ kxt_), used by no other file.

(def-functoid 'CCONT '(kxt_)
  '(SEP kxf_ (FUN (PTS kxt_) CC) (IS-HOM-TOP-SPACE kxt_ (METRIC-TOP CC-MS) kxf_)))

(def-functoid 'SUP-NORM-T '(kxt_ kxf_)
  '(ESUP (IMAGE (VNB-LAMBDA kxp_ (PTS kxt_) (magnitude (kxf_ kxp_))) (PTS kxt_))))

(def-functoid 'CCONT-VADD '(kxt_)
  '(VNB-LAMBDA (LIST kxf_ kxg_) (CARTESIAN (CCONT kxt_) (CCONT kxt_))
     (VNB-LAMBDA kxp_ (PTS kxt_) (+ (kxf_ kxp_) (kxg_ kxp_)))))
(def-functoid 'CCONT-VZERO '(kxt_)
  '(VNB-LAMBDA kxp_ (PTS kxt_) 0))
(def-functoid 'CCONT-VNEG '(kxt_)
  '(VNB-LAMBDA kxf_ (CCONT kxt_) (VNB-LAMBDA kxp_ (PTS kxt_) (- (kxf_ kxp_)))))
(def-functoid 'CCONT-ACT '(kxt_)
  '(VNB-LAMBDA (LIST kxc_ kxf_) (CARTESIAN CC (CCONT kxt_))
     (VNB-LAMBDA kxp_ (PTS kxt_) (* kxc_ (kxf_ kxp_)))))
(def-functoid 'CCONT-VNRM '(kxt_)
  '(VNB-LAMBDA kxf_ (CCONT kxt_) (SUP-NORM-T kxt_ kxf_)))
(def-functoid 'CCONT-VMUL '(kxt_)
  '(VNB-LAMBDA (LIST kxf_ kxg_) (CARTESIAN (CCONT kxt_) (CCONT kxt_))
     (VNB-LAMBDA kxp_ (PTS kxt_) (* (kxf_ kxp_) (kxg_ kxp_)))))
(def-functoid 'CCONT-VONE '(kxt_)
  '(VNB-LAMBDA kxp_ (PTS kxt_) 1))
(def-functoid 'CCONT-VSTAR '(kxt_)
  '(VNB-LAMBDA kxf_ (CCONT kxt_) (VNB-LAMBDA kxp_ (PTS kxt_) (conjugate (kxf_ kxp_)))))

(def-functoid 'CCONT-ALGEBRA '(kxt_)
  '(LIST (NORMED-FIELD-AS-COMMUTATIVE-RING CC-NORMED-FIELD) (CCONT kxt_) (CCONT-VADD kxt_)
         (CCONT-VZERO kxt_) (CCONT-VNEG kxt_) (CCONT-ACT kxt_) (CCONT-VNRM kxt_) (CCONT-VMUL kxt_)
         (CCONT-VONE kxt_) (CCONT-VSTAR kxt_)))

(notation! 'CCONT 'kind 'functoid 'arity 1 'english "the continuous complex functions on $1" 'tex "C({$1})")
(notation! 'SUP-NORM-T 'kind 'functoid 'arity 2 'english "the supremum norm of $2 on $1"
           'tex "\\lVert $2 \\rVert_{\\infty}")
(notation! 'CCONT-ALGEBRA 'kind 'functoid 'arity 1 'english "the C*-algebra of continuous complex functions on $1")
(notation! 'CCONT-VADD 'kind 'functoid 'arity 1 'english "pointwise addition on C($1)")
(notation! 'CCONT-VZERO 'kind 'functoid 'arity 1 'english "the zero function on $1")
(notation! 'CCONT-VNEG 'kind 'functoid 'arity 1 'english "pointwise negation on C($1)")
(notation! 'CCONT-ACT 'kind 'functoid 'arity 1 'english "pointwise scalar multiplication on C($1)")
(notation! 'CCONT-VNRM 'kind 'functoid 'arity 1 'english "the supremum norm on C($1)")
(notation! 'CCONT-VMUL 'kind 'functoid 'arity 1 'english "pointwise multiplication on C($1)")
(notation! 'CCONT-VONE 'kind 'functoid 'arity 1 'english "the constant function 1 on $1")
(notation! 'CCONT-VSTAR 'kind 'functoid 'arity 1 'english "pointwise conjugation on C($1)")
