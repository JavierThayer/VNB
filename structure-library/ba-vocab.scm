;;; ba-vocab.scm -- wave of 2026-11-09/10 (agent BA-1), wired 2026-11-10 from scratchpad/ba1-1109/ba-vocab.scm.
;;; Library: operator-algebras.

;;; ba-vocab.scm -- BANACH ALGEBRAS: the structures, the views, and the element-level vocabulary
;;; of F. J. Thayer, "Banach Algebras and Applications" (docs/BanachAlgebras.pdf), chapter 1.
;;; DEFINITIONS ONLY: no proof, no support, no axiom other than what declare-structure,
;;; def-functor and def-by-nn-recursion install by their own mechanism.
;;; Agent BA-1, wave 2026-11-09 (STEP 0).  Destination: structure-library/ba-vocab.scm.
;;; Library: operator-algebras (BA-MAP-REPORT.md s.3.9).
;;; Load window: after structure-library/normed-ag-metric (NAG-METRIC-SPACE),
;;; structure-library/metric-completeness (IS-COMPLETE), views.scm / numeric-instances
;;; (NORMED-FIELD-AS-COMMUTATIVE-RING, CC-NORMED-FIELD), structure-library/top-product
;;; (TPRODUCT-TOP) and structure-library/top-continuity (SUBSPACE-TOP), structure-library/
;;; extended-reals-pos (ESUP, EINF), ordinals (def-by-nn-recursion), complex (CC-MS),
;;; top-space (METRIC-TOP, IS-HOM-TOP-SPACE).  All of these load before load.scm position
;;; ~1700; the file can sit anywhere after structure-library/seminorm-hahn-banach.
;;;
;;; THE USER'S DECISIONS (2026-11-09): D1 complex scalars only; D2 a Banach algebra is unital
;;; by definition with ||1|| = 1, the non-unital structures exist for 1.1, 1.18, 1.19 only.
;;;
;;; ====================================================================
;;; THE SLOT LAYOUT (ONE NAME, ONE SLOT; BA-MAP-REPORT.md s.3.1)
;;; ====================================================================
;;;   1 SCAL  substructure RING, pinned to NORMED-FIELD-AS-COMMUTATIVE-RING(CC-NORMED-FIELD)
;;;   2 VEC   carrier        3 VADD   4 VZERO   5 VNEG   6 ACT      (MODULE's indices)
;;;   7 VNRM  op VEC -> RR   (NORMED-VECTOR-SPACE's index)
;;;   8 VMUL  op VEC x VEC -> VEC            (new name)
;;;   9 VONE  constant in VEC                (unital structures)    (new name)
;;;  10 VSTAR op VEC -> VEC                  (unital involutive)    (new name)
;;;   9 ISTAR op VEC -> VEC                  (non-unital involutive; only 1.18 / 1.19)
;;; The scalars are pinned through the RING VIEW of the normed field, never the raw 7-tuple
;;; (complex-inner-product.scm, "THE SCALARS, AND A DEFECT NOT REPEATED HERE"), and the
;;; carrier law carr(scal(s)) = cc is stated redundantly, as there, so that a proof reaches CC
;;; in one projection.
;;;
;;; A structure with more slots cannot be `same-shape-as' one with fewer, so a unital algebra
;;; states the non-unital laws as ONE law on the tuple of its first eight slots, as
;;; sip-complex-vocab.scm does for COMPLEX-SEMI-INNER-PRODUCT-SPACE; the views UBA-AS-CBA and
;;; UIBA-AS-UBA are exactly those tuples.
;;;
;;; THE HOMOMORPHISMS.  The generated IS-HOM-X of a structure with a norm op preserves the
;;; norm (an isometry, categories.scm); a homomorphism of these notes need not.  The
;;; algebraic arrows are the predicates IS-ALG-HOM and IS-STAR-HOM below.  The generated
;;; IS-HOM-UNITAL-C-STAR-ALGEBRA (isometric) is the arrow of 1.23's "isometric isomorphism".
;;;
;;; Binders: ba*_ (bax_, bay_, baz_, bau_, ...), used by no other file.

;;; --------------------------------------------------------------------------------------------
;;; COMPLEX-NORMED-ALGEBRA: an associative complex algebra with a submultiplicative norm.
(declare-structure COMPLEX-NORMED-ALGEBRA
  (instance-var s)
  (substructure SCAL RING)
  (carriers VEC)
  (op VADD (CARTESIAN VEC VEC) VEC)
  (constant VZERO VEC)
  (op VNEG VEC VEC)
  (op ACT (CARTESIAN (CARR SCAL) VEC) VEC)
  (op VNRM VEC RR)
  (op VMUL (CARTESIAN VEC VEC) VEC)
  ;; (VEC, VADD, VZERO, VNEG) is an abelian group
  (property is-associative VADD VEC)
  (property is-commutative VADD VEC)
  (property is-identity VADD VZERO VEC)
  (property has-inverses VADD VZERO VNEG VEC)
  ;; the scalars are the complex numbers, through the ring view; and their carrier is CC
  (law "scal(s) = normed-field-as-commutative-ring(cc-normed-field)")
  (law "carr(scal(s)) = cc")
  ;; the four action axioms (MODULE's, verbatim)
  (law "forall([r_ in carr(scal(s)), x_ in vec(s), y_ in vec(s)],
          act(s)(r_, vadd(s)(x_, y_)) = vadd(s)(act(s)(r_, x_), act(s)(r_, y_)))")
  (law "forall([r_ in carr(scal(s)), s_ in carr(scal(s)), x_ in vec(s)],
          act(s)(add(scal(s))(r_, s_), x_) = vadd(s)(act(s)(r_, x_), act(s)(s_, x_)))")
  (law "forall([r_ in carr(scal(s)), s_ in carr(scal(s)), x_ in vec(s)],
          act(s)(mul(scal(s))(r_, s_), x_) = act(s)(r_, act(s)(s_, x_)))")
  (law "forall([x_ in vec(s)], act(s)(one(scal(s)), x_) = x_)")
  ;; the norm: nonnegative, definite, homogeneous (complex modulus), subadditive
  (law "forall([x_ in vec(s)], 0 <= vnrm(s)(x_))")
  (law "forall([x_ in vec(s)], (vnrm(s)(x_) = 0) iff (x_ = vzero(s)))")
  (law "forall([r_ in carr(scal(s)), x_ in vec(s)],
          vnrm(s)(act(s)(r_, x_)) = magnitude(r_) * vnrm(s)(x_))")
  (law "forall([x_ in vec(s), y_ in vec(s)],
          vnrm(s)(vadd(s)(x_, y_)) <= vnrm(s)(x_) + vnrm(s)(y_))")
  ;; the product: associative, bilinear over CC, submultiplicative
  (property is-associative VMUL VEC)
  (law "forall([x_ in vec(s), y_ in vec(s), z_ in vec(s)],
          vmul(s)(x_, vadd(s)(y_, z_)) = vadd(s)(vmul(s)(x_, y_), vmul(s)(x_, z_)))")
  (law "forall([x_ in vec(s), y_ in vec(s), z_ in vec(s)],
          vmul(s)(vadd(s)(x_, y_), z_) = vadd(s)(vmul(s)(x_, z_), vmul(s)(y_, z_)))")
  (law "forall([r_ in carr(scal(s)), x_ in vec(s), y_ in vec(s)],
          vmul(s)(act(s)(r_, x_), y_) = act(s)(r_, vmul(s)(x_, y_)))")
  (law "forall([r_ in carr(scal(s)), x_ in vec(s), y_ in vec(s)],
          vmul(s)(x_, act(s)(r_, y_)) = act(s)(r_, vmul(s)(x_, y_)))")
  (law "forall([x_ in vec(s), y_ in vec(s)],
          vnrm(s)(vmul(s)(x_, y_)) <= vnrm(s)(x_) * vnrm(s)(y_))"))

;;; the views: forget the product (a MODULE), forget the scalars (a NORMED-AG: the
;;; complete-group series theorems, NAG-METRIC-SPACE and absolute-summable-implies-summable
;;; apply through it)
(def-functor 'CNA-AS-MODULE
  'COMPLEX-NORMED-ALGEBRA '(SCAL VEC VADD VZERO VNEG ACT)
  'MODULE                 '(SCAL VEC VADD VZERO VNEG ACT))

;;; DEFERRED typing (D8, 2026-11-15): ||-x|| = ||x|| is a consequence, not a law --
;;; theorem-library/nvs-normed-ag-typing.scm.
(def-functor 'CNA-AS-NORMED-AG
  'COMPLEX-NORMED-ALGEBRA '(VEC VADD VZERO VNEG VNRM)
  'NORMED-AG              '(CARR OPR IDEN INV NRM)
  'deferred)

;;; the metric space of a normed algebra: d(x, y) = ||x - y||
(def-functoid 'CNA-METRIC-SPACE '(baa_)
  '(NAG-METRIC-SPACE (CNA-AS-NORMED-AG baa_)))

;;; COMPLEX-BANACH-ALGEBRA: a complete complex normed algebra (not necessarily unital).
(declare-structure COMPLEX-BANACH-ALGEBRA
  (instance-var s)
  (same-shape-as COMPLEX-NORMED-ALGEBRA)
  (law "is-complete(nag-metric-space(cna-as-normed-ag(s)))"))

;;; --------------------------------------------------------------------------------------------
;;; UNITAL-BANACH-ALGEBRA: a complex Banach algebra with unit 1 and ||1|| = 1 (decision D2).
;;; THE BANACH ALGEBRA of the notes.
(declare-structure UNITAL-BANACH-ALGEBRA
  (instance-var s)
  (substructure SCAL RING)
  (carriers VEC)
  (op VADD (CARTESIAN VEC VEC) VEC)
  (constant VZERO VEC)
  (op VNEG VEC VEC)
  (op ACT (CARTESIAN (CARR SCAL) VEC) VEC)
  (op VNRM VEC RR)
  (op VMUL (CARTESIAN VEC VEC) VEC)
  (constant VONE VEC)
  (law "is-complex-banach-algebra([scal(s), vec(s), vadd(s), vzero(s), vneg(s), act(s), vnrm(s), vmul(s)])")
  (law "carr(scal(s)) = cc")
  (law "forall([x_ in vec(s)], vmul(s)(vone(s), x_) = x_)")
  (law "forall([x_ in vec(s)], vmul(s)(x_, vone(s)) = x_)")
  (law "vnrm(s)(vone(s)) = 1"))

(def-functor 'UBA-AS-CBA
  'UNITAL-BANACH-ALGEBRA  '(SCAL VEC VADD VZERO VNEG ACT VNRM VMUL)
  'COMPLEX-BANACH-ALGEBRA '(SCAL VEC VADD VZERO VNEG ACT VNRM VMUL))

;;; the ring of a unital algebra (CARR := VEC, ADD := VADD, MUL := VMUL, NEG := VNEG,
;;; ZERO := VZERO, ONE := VONE): "is a field" and IS-RING-ISO are read through it
(def-functor 'UBA-AS-RING
  'UNITAL-BANACH-ALGEBRA '(VEC VADD VMUL VNEG VZERO VONE)
  'RING                  '(CARR ADD MUL NEG ZERO ONE))

(def-functor 'UBA-AS-MODULE
  'UNITAL-BANACH-ALGEBRA '(SCAL VEC VADD VZERO VNEG ACT)
  'MODULE                '(SCAL VEC VADD VZERO VNEG ACT))

;;; DEFERRED typing (D8): generic, through CNA-AS-NORMED-AG's, once that is proven
;;; (theorem-library/nvs-normed-ag-typing.scm).
(def-functor 'UBA-AS-NORMED-AG
  'UNITAL-BANACH-ALGEBRA '(VEC VADD VZERO VNEG VNRM)
  'NORMED-AG             '(CARR OPR IDEN INV NRM)
  'deferred)

;;; the metric space of a unital algebra (the same as CNA-METRIC-SPACE(UBA-AS-CBA(a)))
(def-functoid 'BA-METRIC-SPACE '(baa_)
  '(NAG-METRIC-SPACE (UBA-AS-NORMED-AG baa_)))

(declare-structure COMMUTATIVE-BANACH-ALGEBRA
  (instance-var s)
  (same-shape-as UNITAL-BANACH-ALGEBRA)
  ;; (a `property' clause is silently DROPPED in a same-shape-as refinement: stated as a law)
  (law "forall([x_ in vec(s), y_ in vec(s)], vmul(s)(x_, y_) = vmul(s)(y_, x_))"))

;;; --------------------------------------------------------------------------------------------
;;; Involutive algebras (Definition 1.17): the involution is conjugate linear, involutive,
;;; reverses products and is ISOMETRIC (the notes include the isometry in the definition).
(declare-structure UNITAL-INVOLUTIVE-BANACH-ALGEBRA
  (instance-var s)
  (substructure SCAL RING)
  (carriers VEC)
  (op VADD (CARTESIAN VEC VEC) VEC)
  (constant VZERO VEC)
  (op VNEG VEC VEC)
  (op ACT (CARTESIAN (CARR SCAL) VEC) VEC)
  (op VNRM VEC RR)
  (op VMUL (CARTESIAN VEC VEC) VEC)
  (constant VONE VEC)
  (op VSTAR VEC VEC)
  (law "is-unital-banach-algebra([scal(s), vec(s), vadd(s), vzero(s), vneg(s), act(s), vnrm(s), vmul(s), vone(s)])")
  (law "carr(scal(s)) = cc")
  (law "forall([x_ in vec(s), y_ in vec(s)], vstar(s)(vadd(s)(x_, y_)) = vadd(s)(vstar(s)(x_), vstar(s)(y_)))")
  (law "forall([r_ in cc, x_ in vec(s)], vstar(s)(act(s)(r_, x_)) = act(s)(conjugate(r_), vstar(s)(x_)))")
  (law "forall([x_ in vec(s)], vstar(s)(vstar(s)(x_)) = x_)")
  (law "forall([x_ in vec(s), y_ in vec(s)], vstar(s)(vmul(s)(x_, y_)) = vmul(s)(vstar(s)(y_), vstar(s)(x_)))")
  (law "forall([x_ in vec(s)], vnrm(s)(vstar(s)(x_)) = vnrm(s)(x_))"))

(def-functor 'UIBA-AS-UBA
  'UNITAL-INVOLUTIVE-BANACH-ALGEBRA '(SCAL VEC VADD VZERO VNEG ACT VNRM VMUL VONE)
  'UNITAL-BANACH-ALGEBRA            '(SCAL VEC VADD VZERO VNEG ACT VNRM VMUL VONE))

;;; C*-algebras with unit: ||x* x|| = ||x||^2
(declare-structure UNITAL-C-STAR-ALGEBRA
  (instance-var s)
  (same-shape-as UNITAL-INVOLUTIVE-BANACH-ALGEBRA)
  (law "forall([x_ in vec(s)], vnrm(s)(vmul(s)(vstar(s)(x_), x_)) = vnrm(s)(x_) * vnrm(s)(x_))"))

(declare-structure COMMUTATIVE-C-STAR-ALGEBRA
  (instance-var s)
  (same-shape-as UNITAL-C-STAR-ALGEBRA)
  ;; (a `property' clause is silently DROPPED in a same-shape-as refinement: stated as a law)
  (law "forall([x_ in vec(s), y_ in vec(s)], vmul(s)(x_, y_) = vmul(s)(y_, x_))"))

;;; the non-unital involutive corner (1.18, 1.19): ISTAR at slot 9
(declare-structure NU-INVOLUTIVE-BANACH-ALGEBRA
  (instance-var s)
  (substructure SCAL RING)
  (carriers VEC)
  (op VADD (CARTESIAN VEC VEC) VEC)
  (constant VZERO VEC)
  (op VNEG VEC VEC)
  (op ACT (CARTESIAN (CARR SCAL) VEC) VEC)
  (op VNRM VEC RR)
  (op VMUL (CARTESIAN VEC VEC) VEC)
  (op ISTAR VEC VEC)
  (law "is-complex-banach-algebra([scal(s), vec(s), vadd(s), vzero(s), vneg(s), act(s), vnrm(s), vmul(s)])")
  (law "carr(scal(s)) = cc")
  (law "forall([x_ in vec(s), y_ in vec(s)], istar(s)(vadd(s)(x_, y_)) = vadd(s)(istar(s)(x_), istar(s)(y_)))")
  (law "forall([r_ in cc, x_ in vec(s)], istar(s)(act(s)(r_, x_)) = act(s)(conjugate(r_), istar(s)(x_)))")
  (law "forall([x_ in vec(s)], istar(s)(istar(s)(x_)) = x_)")
  (law "forall([x_ in vec(s), y_ in vec(s)], istar(s)(vmul(s)(x_, y_)) = vmul(s)(istar(s)(y_), istar(s)(x_)))")
  (law "forall([x_ in vec(s)], vnrm(s)(istar(s)(x_)) = vnrm(s)(x_))"))

(declare-structure NU-C-STAR-ALGEBRA
  (instance-var s)
  (same-shape-as NU-INVOLUTIVE-BANACH-ALGEBRA)
  (law "forall([x_ in vec(s)], vnrm(s)(vmul(s)(istar(s)(x_), x_)) = vnrm(s)(x_) * vnrm(s)(x_))"))

(def-functor 'NUIBA-AS-CBA
  'NU-INVOLUTIVE-BANACH-ALGEBRA '(SCAL VEC VADD VZERO VNEG ACT VNRM VMUL)
  'COMPLEX-BANACH-ALGEBRA       '(SCAL VEC VADD VZERO VNEG ACT VNRM VMUL))

;;; a unital involutive algebra, forgetting its unit, as a non-unital one
(def-functor 'UIBA-AS-NUIBA
  'UNITAL-INVOLUTIVE-BANACH-ALGEBRA '(SCAL VEC VADD VZERO VNEG ACT VNRM VMUL VSTAR)
  'NU-INVOLUTIVE-BANACH-ALGEBRA     '(SCAL VEC VADD VZERO VNEG ACT VNRM VMUL ISTAR))

;;; --------------------------------------------------------------------------------------------
;;; ELEMENTS.  Every functoid below reads the accessors of its first argument, so it applies
;;; to any of the unital structures (they share slots 1-9).

;;; x is invertible: a two-sided inverse exists.  INVERSE-EL is its IOTA (unique by the
;;; notes' argument v = v(au) = (va)u = u).
(def-predicate 'IS-INVERTIBLE-EL '(baa_ bax_)
  '(AND (IN bax_ (VEC baa_))
        (FORSOME bau_ (AND (IN bau_ (VEC baa_))
                           (AND (= ((VMUL baa_) bau_ bax_) (VONE baa_))
                                (= ((VMUL baa_) bax_ bau_) (VONE baa_)))))))

(def-functoid 'INVERSE-EL '(baa_ bax_)
  '(IOTA bau_ (AND (IN bau_ (VEC baa_))
                   (AND (= ((VMUL baa_) bau_ bax_) (VONE baa_))
                        (= ((VMUL baa_) bax_ bau_) (VONE baa_))))))

;;; the set of invertible elements
(def-functoid 'INVERTIBLES '(baa_)
  '(SEP bav_ (VEC baa_) (IS-INVERTIBLE-EL baa_ bav_)))

;;; powers: x^0 = 1, x^(n+1) = x x^n
(def-by-nn-recursion 'EL-POW '(bpa_ bpx_)
  '(VONE bpa_)
  '(bpn_ bpv_)
  '((VMUL bpa_) bpx_ bpv_))

;;; z 1 - x, the element whose invertibility defines the spectrum
(def-functoid 'SHIFT-EL '(baa_ baz_ bax_)
  '((VADD baa_) ((ACT baa_) baz_ (VONE baa_)) ((VNEG baa_) bax_)))

;;; the spectrum sigma(x) = {z in C : z 1 - x is not invertible}
(def-functoid 'SPECTRUM '(baa_ bax_)
  '(SEP baz_ CC (NOT (IS-INVERTIBLE-EL baa_ (SHIFT-EL baa_ baz_ bax_)))))

;;; the resolvent z |-> (z 1 - x)^(-1) on C \ sigma(x)  (Proposition 1.6's F)
(def-functoid 'RESOLVENT '(baa_ bax_)
  '(VNB-LAMBDA brz_ (DIFFERENCE CC (SPECTRUM baa_ bax_))
     (INVERSE-EL baa_ (SHIFT-EL baa_ brz_ bax_))))

;;; the spectral radius, DEFINED as inf_(n >= 1) ||x^n||^(1/n); Lemma 1.7 is then the theorem
;;; that ||x^n||^(1/n) converges to it (no IOTA of a limit).  EINF of a set of nonnegative
;;; reals (extended-reals-pos.scm), which is finite here (bounded by ||x||).
(def-functoid 'SPECTRAL-RADIUS '(baa_ bax_)
  '(EINF (SEP bsw_ RR (FORSOME bsn_ (AND (IN bsn_ NN) (AND (<= 1 bsn_)
           (= bsw_ (RPOW-STAR ((VNRM baa_) (EL-POW baa_ bax_ bsn_)) (RECIP-STAR bsn_)))))))))

;;; --------------------------------------------------------------------------------------------
;;; Involutive elements (slot 10, VSTAR)
(def-predicate 'IS-SELF-ADJOINT-EL '(baa_ bax_)
  '(AND (IN bax_ (VEC baa_)) (= ((VSTAR baa_) bax_) bax_)))
(def-predicate 'IS-NORMAL-EL '(baa_ bax_)
  '(AND (IN bax_ (VEC baa_))
        (= ((VMUL baa_) ((VSTAR baa_) bax_) bax_) ((VMUL baa_) bax_ ((VSTAR baa_) bax_)))))
(def-predicate 'IS-UNITARY-EL '(baa_ bax_)
  '(AND (IN bax_ (VEC baa_))
        (AND (= ((VMUL baa_) ((VSTAR baa_) bax_) bax_) (VONE baa_))
             (= ((VMUL baa_) bax_ ((VSTAR baa_) bax_)) (VONE baa_)))))
(def-predicate 'IS-PROJECTION-EL '(baa_ bax_)
  '(AND (IN bax_ (VEC baa_))
        (AND (= ((VSTAR baa_) bax_) bax_) (= ((VMUL baa_) bax_ bax_) bax_))))
;;; A_sa and A_sa^2 = {x^2 : x in A_sa}
(def-functoid 'SA-PART '(baa_)
  '(SEP bav_ (VEC baa_) (= ((VSTAR baa_) bav_) bav_)))
(def-functoid 'SA-SQUARES '(baa_)
  '(SEP bav_ (VEC baa_) (FORSOME baw_ (AND (IN baw_ (SA-PART baa_)) (= bav_ ((VMUL baa_) baw_ baw_))))))

;;; --------------------------------------------------------------------------------------------
;;; IDEALS of a (possibly non-commutative) algebra: a linear subspace closed under
;;; multiplication by the algebra on the left (left ideal), on the right, or both.
(def-predicate 'IS-ALG-SUBSPACE '(baa_ bai_)
  '(AND (SUBSET bai_ (VEC baa_))
   (AND (IN (VZERO baa_) bai_)
   (AND (FORALL bax_ (IMPLIES (IN bax_ bai_) (FORALL bay_ (IMPLIES (IN bay_ bai_)
          (IN ((VADD baa_) bax_ bay_) bai_)))))
        (FORALL baz_ (IMPLIES (IN baz_ CC) (FORALL bax_ (IMPLIES (IN bax_ bai_)
          (IN ((ACT baa_) baz_ bax_) bai_)))))))))
(def-predicate 'IS-LEFT-IDEAL '(baa_ bai_)
  '(AND (IS-ALG-SUBSPACE baa_ bai_)
        (FORALL bay_ (IMPLIES (IN bay_ (VEC baa_)) (FORALL bax_ (IMPLIES (IN bax_ bai_)
          (IN ((VMUL baa_) bay_ bax_) bai_)))))))
(def-predicate 'IS-RIGHT-IDEAL '(baa_ bai_)
  '(AND (IS-ALG-SUBSPACE baa_ bai_)
        (FORALL bay_ (IMPLIES (IN bay_ (VEC baa_)) (FORALL bax_ (IMPLIES (IN bax_ bai_)
          (IN ((VMUL baa_) bax_ bay_) bai_)))))))
(def-predicate 'IS-TWO-SIDED-IDEAL '(baa_ bai_)
  '(AND (IS-LEFT-IDEAL baa_ bai_) (IS-RIGHT-IDEAL baa_ bai_)))
;;; maximal among the PROPER ideals of the same kind (Corollary 1.5's reading)
(def-predicate 'IS-MAXIMAL-LEFT-IDEAL '(baa_ bai_)
  '(AND (IS-LEFT-IDEAL baa_ bai_)
   (AND (NOT (= bai_ (VEC baa_)))
        (FORALL baj_ (IMPLIES (IS-LEFT-IDEAL baa_ baj_)
          (IMPLIES (SUBSET bai_ baj_) (IMPLIES (NOT (= baj_ (VEC baa_))) (= baj_ bai_))))))))
(def-predicate 'IS-MAXIMAL-RIGHT-IDEAL '(baa_ bai_)
  '(AND (IS-RIGHT-IDEAL baa_ bai_)
   (AND (NOT (= bai_ (VEC baa_)))
        (FORALL baj_ (IMPLIES (IS-RIGHT-IDEAL baa_ baj_)
          (IMPLIES (SUBSET bai_ baj_) (IMPLIES (NOT (= baj_ (VEC baa_))) (= baj_ bai_))))))))
(def-predicate 'IS-MAXIMAL-IDEAL '(baa_ bai_)
  '(AND (IS-TWO-SIDED-IDEAL baa_ bai_)
   (AND (NOT (= bai_ (VEC baa_)))
        (FORALL baj_ (IMPLIES (IS-TWO-SIDED-IDEAL baa_ baj_)
          (IMPLIES (SUBSET bai_ baj_) (IMPLIES (NOT (= baj_ (VEC baa_))) (= baj_ bai_))))))))

;;; --------------------------------------------------------------------------------------------
;;; UNITIZATION (Proposition 1.1): C x A with (l, x) + (r, y) = (l + r, x + y),
;;; (l, x)(r, y) = (l r, l y + r x + x y), ||(l, x)|| = |l| + ||x||, unit (1, 0).
;;; UNITIZATION-NA(a) is the 8-tuple (a normed algebra), UNITIZATION(a) the 9-tuple with the
;;; unit, UNITIZATION-STAR(a) the 10-tuple with (l, x)* = (conj l, x*) for a NU-INVOLUTIVE a.
;;; Binders bup_ buq_ buc_.
(def-functoid 'UNIT-VEC '(baa_) '(CARTESIAN CC (VEC baa_)))
(def-functoid 'UNIT-VADD '(baa_)
  '(VNB-LAMBDA (LIST bup_ buq_) (CARTESIAN (UNIT-VEC baa_) (UNIT-VEC baa_))
     (LIST (+ (NTH 1 bup_) (NTH 1 buq_)) ((VADD baa_) (NTH 2 bup_) (NTH 2 buq_)))))
(def-functoid 'UNIT-VNEG '(baa_)
  '(VNB-LAMBDA bup_ (UNIT-VEC baa_) (LIST (- (NTH 1 bup_)) ((VNEG baa_) (NTH 2 bup_)))))
(def-functoid 'UNIT-ACT '(baa_)
  '(VNB-LAMBDA (LIST buc_ bup_) (CARTESIAN CC (UNIT-VEC baa_))
     (LIST (* buc_ (NTH 1 bup_)) ((ACT baa_) buc_ (NTH 2 bup_)))))
(def-functoid 'UNIT-VNRM '(baa_)
  '(VNB-LAMBDA bup_ (UNIT-VEC baa_) (+ (magnitude (NTH 1 bup_)) ((VNRM baa_) (NTH 2 bup_)))))
(def-functoid 'UNIT-VMUL '(baa_)
  '(VNB-LAMBDA (LIST bup_ buq_) (CARTESIAN (UNIT-VEC baa_) (UNIT-VEC baa_))
     (LIST (* (NTH 1 bup_) (NTH 1 buq_))
           ((VADD baa_) ((VADD baa_) ((ACT baa_) (NTH 1 bup_) (NTH 2 buq_))
                                     ((ACT baa_) (NTH 1 buq_) (NTH 2 bup_)))
                        ((VMUL baa_) (NTH 2 bup_) (NTH 2 buq_))))))
(def-functoid 'UNIT-ISTAR '(baa_)
  '(VNB-LAMBDA bup_ (UNIT-VEC baa_) (LIST (conjugate (NTH 1 bup_)) ((ISTAR baa_) (NTH 2 bup_)))))
(def-functoid 'UNITIZATION-NA '(baa_)
  '(LIST (NORMED-FIELD-AS-COMMUTATIVE-RING CC-NORMED-FIELD) (UNIT-VEC baa_) (UNIT-VADD baa_)
         (LIST 0 (VZERO baa_)) (UNIT-VNEG baa_) (UNIT-ACT baa_) (UNIT-VNRM baa_) (UNIT-VMUL baa_)))
(def-functoid 'UNITIZATION '(baa_)
  '(LIST (NORMED-FIELD-AS-COMMUTATIVE-RING CC-NORMED-FIELD) (UNIT-VEC baa_) (UNIT-VADD baa_)
         (LIST 0 (VZERO baa_)) (UNIT-VNEG baa_) (UNIT-ACT baa_) (UNIT-VNRM baa_) (UNIT-VMUL baa_)
         (LIST 1 (VZERO baa_))))
(def-functoid 'UNITIZATION-STAR '(baa_)
  '(LIST (NORMED-FIELD-AS-COMMUTATIVE-RING CC-NORMED-FIELD) (UNIT-VEC baa_) (UNIT-VADD baa_)
         (LIST 0 (VZERO baa_)) (UNIT-VNEG baa_) (UNIT-ACT baa_) (UNIT-VNRM baa_) (UNIT-VMUL baa_)
         (LIST 1 (VZERO baa_)) (UNIT-ISTAR baa_)))

;;; --------------------------------------------------------------------------------------------
;;; HOMOMORPHISMS (the algebraic arrows; see the header).  a, b unital algebras.
(def-predicate 'IS-ALG-HOM '(baa_ bab_ baf_)
  '(AND (IN baf_ (FUN (VEC baa_) (VEC bab_)))
   (AND (FORALL bax_ (IMPLIES (IN bax_ (VEC baa_)) (FORALL bay_ (IMPLIES (IN bay_ (VEC baa_))
          (= (baf_ ((VADD baa_) bax_ bay_)) ((VADD bab_) (baf_ bax_) (baf_ bay_)))))))
   (AND (FORALL baz_ (IMPLIES (IN baz_ CC) (FORALL bax_ (IMPLIES (IN bax_ (VEC baa_))
          (= (baf_ ((ACT baa_) baz_ bax_)) ((ACT bab_) baz_ (baf_ bax_)))))))
   (AND (FORALL bax_ (IMPLIES (IN bax_ (VEC baa_)) (FORALL bay_ (IMPLIES (IN bay_ (VEC baa_))
          (= (baf_ ((VMUL baa_) bax_ bay_)) ((VMUL bab_) (baf_ bax_) (baf_ bay_)))))))
        (= (baf_ (VONE baa_)) (VONE bab_)))))))
(def-predicate 'IS-STAR-HOM '(baa_ bab_ baf_)
  '(AND (IS-ALG-HOM baa_ bab_ baf_)
        (FORALL bax_ (IMPLIES (IN bax_ (VEC baa_))
          (= (baf_ ((VSTAR baa_) bax_)) ((VSTAR bab_) (baf_ bax_)))))))

;;; --------------------------------------------------------------------------------------------
;;; FUNCTIONALS, CHARACTERS, THE GELFAND SPACE AND TRANSFORM
;;; bounded CC-linear functionals on a normed algebra (the complex dual A*), and the dual norm
(def-predicate 'IS-CC-LINEAR-ON '(baa_ baf_)
  '(AND (IN baf_ (FUN (VEC baa_) CC))
   (AND (FORALL bax_ (IMPLIES (IN bax_ (VEC baa_)) (FORALL bay_ (IMPLIES (IN bay_ (VEC baa_))
          (= (baf_ ((VADD baa_) bax_ bay_)) (+ (baf_ bax_) (baf_ bay_)))))))
        (FORALL baz_ (IMPLIES (IN baz_ CC) (FORALL bax_ (IMPLIES (IN bax_ (VEC baa_))
          (= (baf_ ((ACT baa_) baz_ bax_)) (* baz_ (baf_ bax_))))))))))
(def-functoid 'CDUAL-VEC '(baa_)
  '(SEP baf_ (FUN (VEC baa_) CC)
     (AND (IS-CC-LINEAR-ON baa_ baf_)
          (FORSOME bam_ (AND (IN bam_ RR) (FORALL bax_ (IMPLIES (IN bax_ (VEC baa_))
            (<= (magnitude (baf_ bax_)) (* bam_ ((VNRM baa_) bax_))))))))))
(def-functoid 'CDUAL-NORM '(baa_ baf_)
  '(ESUP (IMAGE (VNB-LAMBDA bdx_ (SEP bdy_ (VEC baa_) (<= ((VNRM baa_) bdy_) 1)) (magnitude (baf_ bdx_)))
                (SEP bdy_ (VEC baa_) (<= ((VNRM baa_) bdy_) 1)))))

;;; the characters: unit-preserving multiplicative linear functionals A -> C (Remark 1.13: they
;;; are automatically bounded, of norm 1; that is a theorem, not part of the definition)
(def-functoid 'CHARACTERS '(baa_)
  '(SEP bac_ (FUN (VEC baa_) CC)
     (AND (IS-CC-LINEAR-ON baa_ bac_)
     (AND (FORALL bax_ (IMPLIES (IN bax_ (VEC baa_)) (FORALL bay_ (IMPLIES (IN bay_ (VEC baa_))
            (= (bac_ ((VMUL baa_) bax_ bay_)) (* (bac_ bax_) (bac_ bay_)))))))
          (= (bac_ (VONE baa_)) 1)))))

;;; A-hat: the characters with the topology of pointwise convergence, i.e. the subspace of the
;;; product of copies of C indexed by A (the tree's weak* construction, DUAL-WEAK-STAR-TOP,
;;; with CC for RR; compact by `tychonoff', no complex Banach-Alaoglu)
(def-functoid 'GELFAND-SPACE '(baa_)
  '(SUBSPACE-TOP (TPRODUCT-TOP (VEC baa_) (VNB-LAMBDA bgx_ (VEC baa_) (METRIC-TOP CC-MS)))
                 (CHARACTERS baa_)))

;;; G(x) = (chi |-> chi(x)), a function on the characters
(def-functoid 'GELFAND-TRANSFORM '(baa_)
  '(VNB-LAMBDA bgx_ (VEC baa_) (VNB-LAMBDA bgc_ (CHARACTERS baa_) (bgc_ bgx_))))

;;; the dual map of Gelfand spaces, omega |-> omega o phi (Proposition 1.26)
(def-functoid 'GELFAND-DUAL-MAP '(baa_ bab_ baf_)
  '(VNB-LAMBDA bgw_ (CHARACTERS bab_) (VNB-LAMBDA bgx_ (VEC baa_) (bgw_ (baf_ bgx_)))))

;;; --------------------------------------------------------------------------------------------
;;; Notation
(notation! 'IS-COMPLEX-NORMED-ALGEBRA 'kind 'predicate 'arity 1 'noun "complex normed algebra" 'article "a")
(notation! 'IS-COMPLEX-BANACH-ALGEBRA 'kind 'predicate 'arity 1 'noun "complex Banach algebra" 'article "a")
(notation! 'IS-UNITAL-BANACH-ALGEBRA 'kind 'predicate 'arity 1 'noun "Banach algebra with unit" 'article "a")
(notation! 'IS-COMMUTATIVE-BANACH-ALGEBRA 'kind 'predicate 'arity 1
           'noun "commutative Banach algebra with unit" 'article "a")
(notation! 'IS-UNITAL-INVOLUTIVE-BANACH-ALGEBRA 'kind 'predicate 'arity 1
           'noun "involutive Banach algebra with unit" 'article "an")
(notation! 'IS-UNITAL-C-STAR-ALGEBRA 'kind 'predicate 'arity 1 'noun "C*-algebra with unit" 'article "a")
(notation! 'IS-COMMUTATIVE-C-STAR-ALGEBRA 'kind 'predicate 'arity 1
           'noun "commutative C*-algebra with unit" 'article "a")
(notation! 'IS-NU-INVOLUTIVE-BANACH-ALGEBRA 'kind 'predicate 'arity 1
           'noun "involutive Banach algebra" 'article "an")
(notation! 'IS-NU-C-STAR-ALGEBRA 'kind 'predicate 'arity 1 'noun "C*-algebra" 'article "a")
(notation! 'VMUL 'kind 'accessor 'arity 1 'english "the product of $1" 'tex "\\cdot_{$1}")
(notation! 'VONE 'kind 'accessor 'arity 1 'english "the unit of $1" 'tex "1_{$1}")
(notation! 'VSTAR 'kind 'accessor 'arity 1 'english "the involution of $1" 'tex "{}^{*_{$1}}")
(notation! 'ISTAR 'kind 'accessor 'arity 1 'english "the involution of $1" 'tex "{}^{*_{$1}}")
(notation! 'CNA-METRIC-SPACE 'kind 'functoid 'arity 1 'english "the metric space of the normed algebra $1")
(notation! 'BA-METRIC-SPACE 'kind 'functoid 'arity 1 'english "the metric space of the Banach algebra $1")
(notation! 'IS-INVERTIBLE-EL 'kind 'predicate 'arity 2 'english "$2 is invertible in $1")
(notation! 'INVERSE-EL 'kind 'functoid 'arity 2 'english "the inverse of $2 in $1" 'tex "{$2}^{-1}")
(notation! 'INVERTIBLES 'kind 'functoid 'arity 1 'english "the invertible elements of $1")
(notation! 'EL-POW 'kind 'functoid 'arity 3 'english "the $3-th power of $2 in $1" 'tex "{$2}^{$3}")
(notation! 'SHIFT-EL 'kind 'functoid 'arity 3 'english "$2 1 - $3 in $1")
(notation! 'SPECTRUM 'kind 'functoid 'arity 2 'english "the spectrum of $2 in $1" 'tex "\\sigma({$2})")
(notation! 'RESOLVENT 'kind 'functoid 'arity 2 'english "the resolvent of $2 in $1")
(notation! 'SPECTRAL-RADIUS 'kind 'functoid 'arity 2 'english "the spectral radius of $2 in $1" 'tex "\\rho({$2})")
(notation! 'IS-SELF-ADJOINT-EL 'kind 'predicate 'arity 2 'english "$2 is self-adjoint in $1")
(notation! 'IS-NORMAL-EL 'kind 'predicate 'arity 2 'english "$2 is normal in $1")
(notation! 'IS-UNITARY-EL 'kind 'predicate 'arity 2 'english "$2 is unitary in $1")
(notation! 'IS-PROJECTION-EL 'kind 'predicate 'arity 2 'english "$2 is a projection in $1")
(notation! 'SA-PART 'kind 'functoid 'arity 1 'english "the self-adjoint elements of $1")
(notation! 'SA-SQUARES 'kind 'functoid 'arity 1 'english "the squares of self-adjoint elements of $1")
(notation! 'IS-ALG-SUBSPACE 'kind 'predicate 'arity 2 'english "$2 is a linear subspace of $1")
(notation! 'IS-LEFT-IDEAL 'kind 'predicate 'arity 2 'english "$2 is a left ideal of $1")
(notation! 'IS-RIGHT-IDEAL 'kind 'predicate 'arity 2 'english "$2 is a right ideal of $1")
(notation! 'IS-TWO-SIDED-IDEAL 'kind 'predicate 'arity 2 'english "$2 is a two-sided ideal of $1")
(notation! 'IS-MAXIMAL-LEFT-IDEAL 'kind 'predicate 'arity 2 'english "$2 is a maximal proper left ideal of $1")
(notation! 'IS-MAXIMAL-RIGHT-IDEAL 'kind 'predicate 'arity 2 'english "$2 is a maximal proper right ideal of $1")
(notation! 'IS-MAXIMAL-IDEAL 'kind 'predicate 'arity 2 'english "$2 is a maximal proper ideal of $1")
(notation! 'UNITIZATION-NA 'kind 'functoid 'arity 1 'english "the unitization of $1 as a normed algebra")
(notation! 'UNITIZATION 'kind 'functoid 'arity 1 'english "the unitization of $1")
(notation! 'UNITIZATION-STAR 'kind 'functoid 'arity 1 'english "the involutive unitization of $1")
(notation! 'IS-ALG-HOM 'kind 'predicate 'arity 3 'english "$3 is a unital algebra homomorphism from $1 to $2")
(notation! 'IS-STAR-HOM 'kind 'predicate 'arity 3 'english "$3 is a unital *-homomorphism from $1 to $2")
(notation! 'IS-CC-LINEAR-ON 'kind 'predicate 'arity 2 'english "$2 is a complex-linear functional on $1")
(notation! 'CDUAL-VEC 'kind 'functoid 'arity 1 'english "the bounded complex-linear functionals on $1")
(notation! 'CDUAL-NORM 'kind 'functoid 'arity 2 'english "the norm of the functional $2 on $1")
(notation! 'CHARACTERS 'kind 'functoid 'arity 1 'english "the characters of $1")
(notation! 'GELFAND-SPACE 'kind 'functoid 'arity 1 'english "the Gelfand space of $1" 'tex "\\widehat{$1}")
(notation! 'GELFAND-TRANSFORM 'kind 'functoid 'arity 1 'english "the Gelfand transform of $1")
(notation! 'GELFAND-DUAL-MAP 'kind 'functoid 'arity 3 'english "the dual map of $3 on the Gelfand spaces")
