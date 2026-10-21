;;; sip-complex-vocab.scm -- THE COMPLEX STRUCTURE J on a semi-inner-product space (SIP-1,
;;; 2026-10-18).  Vocabulary only.
;;;
;;; THE DESIGN IS THE USER'S (2026-10-18, scratchpad/triage/SIP-1.md): a complex space is a
;;; REAL space with an extra piece of structure, a real-linear J with J^2 = -I that is
;;; antisymmetric and isometric (the notes, topological-vector-space.pdf, Ch. 1 s.3.1,
;;; Proposition 1.24: any two of the three properties give the third -- on a pre-Hilbert
;;; space; see below for the semidefinite case).  The structure is a `declare-structure'
;;; with a J slot, never a bare predicate.
;;;
;;; THE SHAPE: the seven slots of SEMI-INNER-PRODUCT-SPACE at their indices (one name, one
;;; slot) and JOP at slot 8, an operation VEC -> VEC.  The laws:
;;;   * the first seven slots form a semi-inner-product space -- stated as ONE law,
;;;     IS-SEMI-INNER-PRODUCT-SPACE of the literal seven-list, which is exactly the view
;;;     CSIP-AS-SIP below, so the view's typing axiom is that law read off;
;;;   * JOP is real-linear, J^2 = -I, and J is antisymmetric.
;;; Isometry is NOT a law: it follows from the other two in the semidefinite case
;;; (Proposition 1.24 (2), proved in theorem-library/sip-b.scm).  The two laws chosen are the
;;; two that cannot be derived there: antisymmetry and isometry give J^2 = -I only up to a
;;; null vector, since <J^2 x + x, y> = 0 for every y says J^2 x + x is null, not zero.  The
;;; notes' proof of (3) from (1) and (2) uses definiteness (Definition 1.17 (3)).
;;;
;;; COMPLEX-PRE-HILBERT-SPACE is the definite refinement.
;;;
;;; THE COMPLEX OPERATIONS, the notes' (37) and (38):
;;;   CACT(v)(a + ib, x) = a.x + b.Jx               complex scalar multiplication
;;;   CRIP(v)(x, y)      = <x,y> - i <Jx, y>        the complex form
;;; and CSIP-CIPS(v) is the seven-tuple that is a COMPLEX-INNER-PRODUCT-SPACE when v is a
;;; complex pre-Hilbert space (theorem-library/sip-b.scm).  That structure
;;; (complex-inner-product.scm) is NOT changed; it is connected by bridge theorems.
;;;
;;; THE QUOTIENT: J respects the null-difference relation (it is isometric and linear), so
;;; it descends; CSIP-QUOTIENT(v) is SIP-QUOTIENT of the underlying real space with the
;;; descended J in slot 8.
;;;
;;; LOAD WINDOW: after theorem-library/sip-a (the view specializer transports every
;;; SEMI-INNER-PRODUCT-SPACE theorem present when this file loads to a companion
;;; `<name>-csip-as-sip'), and after structure-library/complex-inner-product.
;;; Library: analysis.

;;; ---- the three properties of an operator on a semi-inner-product space ------------------
(def-predicate 'IS-REAL-LINEAR-OP '(v jo)
  '(AND (IN jo (FUN (VEC v) (VEC v)))
   (AND (FORALL x_ (IMPLIES (IN x_ (VEC v)) (FORALL y_ (IMPLIES (IN y_ (VEC v))
          (= (jo ((VADD v) x_ y_)) ((VADD v) (jo x_) (jo y_)))))))
        (FORALL a_ (IMPLIES (IN a_ RR) (FORALL x_ (IMPLIES (IN x_ (VEC v))
          (= (jo ((ACT v) a_ x_)) ((ACT v) a_ (jo x_))))))))))

;;; (32): <A x, y> = -<x, A y>
(def-predicate 'IS-ANTISYMMETRIC-OP '(v jo)
  '(FORALL x_ (IMPLIES (IN x_ (VEC v)) (FORALL y_ (IMPLIES (IN y_ (VEC v))
     (= ((RIP v) (jo x_) y_) (- ((RIP v) x_ (jo y_)))))))))

(def-predicate 'IS-ISOMETRIC-OP '(v jo)
  '(FORALL x_ (IMPLIES (IN x_ (VEC v)) (FORALL y_ (IMPLIES (IN y_ (VEC v))
     (= ((RIP v) (jo x_) (jo y_)) ((RIP v) x_ y_)))))))

;;; J^2 = -I
(def-predicate 'IS-SQUARE-MINUS-ID '(v jo)
  '(FORALL x_ (IMPLIES (IN x_ (VEC v)) (= (jo (jo x_)) ((VNEG v) x_)))))

;;; ---- the structure ----------------------------------------------------------------------
(declare-structure COMPLEX-SEMI-INNER-PRODUCT-SPACE
  (instance-var s)
  (substructure SCAL RING)
  (carriers VEC)
  (op VADD (CARTESIAN VEC VEC) VEC)
  (constant VZERO VEC)
  (op VNEG VEC VEC)
  (op ACT (CARTESIAN (CARR SCAL) VEC) VEC)
  (op RIP (CARTESIAN VEC VEC) RR)
  (op JOP VEC VEC)
  (law "is-semi-inner-product-space([scal(s), vec(s), vadd(s), vzero(s), vneg(s), act(s), rip(s)])")
  (law "is-real-linear-op(s, jop(s))")
  (law "is-square-minus-id(s, jop(s))")
  (law "is-antisymmetric-op(s, jop(s))"))

(declare-structure COMPLEX-PRE-HILBERT-SPACE
  (instance-var s)
  (same-shape-as COMPLEX-SEMI-INNER-PRODUCT-SPACE)
  (law "forall([x_ in vec(s)], rip(s)(x_, x_) = 0 implies x_ = vzero(s))"))

;;; THE VIEW: forget J.
(def-functor 'CSIP-AS-SIP
  'COMPLEX-SEMI-INNER-PRODUCT-SPACE '(SCAL VEC VADD VZERO VNEG ACT RIP)
  'SEMI-INNER-PRODUCT-SPACE         '(SCAL VEC VADD VZERO VNEG ACT RIP))

;;; ---- (37) and (38) -----------------------------------------------------------------------
(def-functoid 'CACT '(v)
  '(VNB-LAMBDA (LIST cxz_ cxx_) (CARTESIAN CC (VEC v))
     ((VADD v) ((ACT v) (real-part cxz_) cxx_) ((ACT v) (imag-part cxz_) ((JOP v) cxx_)))))

(def-functoid 'CRIP '(v)
  '(VNB-LAMBDA (LIST cxx_ cxy_) (CARTESIAN (VEC v) (VEC v))
     (- ((RIP v) cxx_ cxy_) (* +i ((RIP v) ((JOP v) cxx_) cxy_)))))

;;; the complex space, as a COMPLEX-INNER-PRODUCT-SPACE tuple
(def-functoid 'CSIP-CIPS '(v)
  '(LIST (NORMED-FIELD-AS-COMMUTATIVE-RING CC-NORMED-FIELD) (VEC v) (VADD v) (VZERO v) (VNEG v)
         (CACT v) (CRIP v)))

;;; ---- sesquilinear forms (the notes, after Definition 1.21: conditions (1) and (2)) ---------
;;; on a complex semi-inner-product space, with respect to the complex scalar multiplication
;;; CACT: additive and homogeneous in the first argument, conjugate symmetric.
(def-predicate 'IS-SESQUILINEAR-FORM '(v sqf)
  '(AND (IN sqf (FUN (CARTESIAN (VEC v) (VEC v)) CC))
   (AND (FORALL x_ (IMPLIES (IN x_ (VEC v)) (FORALL y_ (IMPLIES (IN y_ (VEC v)) (FORALL z_ (IMPLIES (IN z_ (VEC v))
          (= (sqf ((VADD v) x_ y_) z_) (+ (sqf x_ z_) (sqf y_ z_)))))))))
   (AND (FORALL a_ (IMPLIES (IN a_ CC) (FORALL x_ (IMPLIES (IN x_ (VEC v)) (FORALL y_ (IMPLIES (IN y_ (VEC v))
          (= (sqf ((CACT v) a_ x_) y_) (* a_ (sqf x_ y_)))))))))
        (FORALL x_ (IMPLIES (IN x_ (VEC v)) (FORALL y_ (IMPLIES (IN y_ (VEC v))
          (= (sqf y_ x_) (conjugate (sqf x_ y_)))))))))))

;;; ---- the quotient ------------------------------------------------------------------------
(def-functoid 'CSIP-QJ '(v)
  '(DESCEND (SIP-SETOID (CSIP-AS-SIP v))
     (VNB-LAMBDA sqa_ (VEC v) (CLASS (SIP-SETOID (CSIP-AS-SIP v)) ((JOP v) sqa_)))))

(def-functoid 'CSIP-QUOTIENT '(v)
  '(LIST (SCAL v) (QUOTIENT (SIP-SETOID (CSIP-AS-SIP v))) (SIP-QVADD (CSIP-AS-SIP v))
         (CLASS (SIP-SETOID (CSIP-AS-SIP v)) (VZERO v)) (SIP-QVNEG (CSIP-AS-SIP v))
         (SIP-QACT (CSIP-AS-SIP v)) (SIP-QRIP (CSIP-AS-SIP v)) (CSIP-QJ v)))
;;; (the first seven entries are SIP-QUOTIENT of the underlying real space with the view's
;;; accessors read off -- the form in which the view specializer states the quotient's laws)

;;; ---- the other bridge, (29)-(30): a complex inner product space as a real one with J ------
;;; <x, y> = Re <x, y>_C (29), J x = i x (30), real scalars acting by restriction.
(def-functoid 'CIPS-RACT '(w)
  '(VNB-LAMBDA (LIST cxr_ cxx_) (CARTESIAN RR (VEC w)) ((ACT w) cxr_ cxx_)))
(def-functoid 'CIPS-RIP '(w)
  '(VNB-LAMBDA (LIST cxx_ cxy_) (CARTESIAN (VEC w) (VEC w)) (real-part ((IP w) cxx_ cxy_))))
(def-functoid 'CIPS-J '(w)
  '(VNB-LAMBDA cxx_ (VEC w) ((ACT w) +i cxx_)))
;;; the underlying real space, and the real space with J
(def-functoid 'CIPS-RSIP '(w)
  '(LIST (NORMED-FIELD-AS-COMMUTATIVE-RING RR-NORMED-FIELD) (VEC w) (VADD w) (VZERO w) (VNEG w)
         (CIPS-RACT w) (CIPS-RIP w)))
(def-functoid 'CIPS-REAL '(w)
  '(LIST (NORMED-FIELD-AS-COMMUTATIVE-RING RR-NORMED-FIELD) (VEC w) (VADD w) (VZERO w) (VNEG w)
         (CIPS-RACT w) (CIPS-RIP w) (CIPS-J w)))

;;; ---- THE COMPLEXIFICATION of a semi-inner-product space v: pairs (x1, x2) of vectors,
;;; componentwise operations, <(x1,x2), (y1,y2)> = <x1,y1> + <x2,y2>, J(x1, x2) = (-x2, x1).
;;; COMPLEXIFY(v) is a COMPLEX-SEMI-INNER-PRODUCT-SPACE (theorem-library/sip-b.scm); complex L^2
;;; is COMPLEXIFY of real L^2 (sip-l2-vocab.scm).  Binders cp_ cq_ cr_ are used by nothing else.
(def-functoid 'CX-VADD '(v)
  '(VNB-LAMBDA (LIST cp_ cq_) (CARTESIAN (CARTESIAN (VEC v) (VEC v)) (CARTESIAN (VEC v) (VEC v)))
     (LIST ((VADD v) (NTH 1 cp_) (NTH 1 cq_)) ((VADD v) (NTH 2 cp_) (NTH 2 cq_)))))
(def-functoid 'CX-VNEG '(v)
  '(VNB-LAMBDA cp_ (CARTESIAN (VEC v) (VEC v)) (LIST ((VNEG v) (NTH 1 cp_)) ((VNEG v) (NTH 2 cp_)))))
(def-functoid 'CX-ACT '(v)
  '(VNB-LAMBDA (LIST cr_ cp_) (CARTESIAN (CARR (SCAL v)) (CARTESIAN (VEC v) (VEC v)))
     (LIST ((ACT v) cr_ (NTH 1 cp_)) ((ACT v) cr_ (NTH 2 cp_)))))
(def-functoid 'CX-RIP '(v)
  '(VNB-LAMBDA (LIST cp_ cq_) (CARTESIAN (CARTESIAN (VEC v) (VEC v)) (CARTESIAN (VEC v) (VEC v)))
     (+ ((RIP v) (NTH 1 cp_) (NTH 1 cq_)) ((RIP v) (NTH 2 cp_) (NTH 2 cq_)))))
(def-functoid 'CX-J '(v)
  '(VNB-LAMBDA cp_ (CARTESIAN (VEC v) (VEC v)) (LIST ((VNEG v) (NTH 2 cp_)) (NTH 1 cp_))))
;;; the underlying real space of the complexification, and the complexification itself
(def-functoid 'CX-SIP '(v)
  '(LIST (SCAL v) (CARTESIAN (VEC v) (VEC v)) (CX-VADD v) (LIST (VZERO v) (VZERO v)) (CX-VNEG v)
         (CX-ACT v) (CX-RIP v)))
(def-functoid 'COMPLEXIFY '(v)
  '(LIST (SCAL v) (CARTESIAN (VEC v) (VEC v)) (CX-VADD v) (LIST (VZERO v) (VZERO v)) (CX-VNEG v)
         (CX-ACT v) (CX-RIP v) (CX-J v)))

;;; ---- notation ----------------------------------------------------------------------------
(notation! 'IS-REAL-LINEAR-OP 'kind 'predicate 'arity 2 'english "$2 is a real-linear operator on $1")
(notation! 'IS-ANTISYMMETRIC-OP 'kind 'predicate 'arity 2 'english "$2 is antisymmetric on $1")
(notation! 'IS-ISOMETRIC-OP 'kind 'predicate 'arity 2 'english "$2 is isometric on $1")
(notation! 'IS-SQUARE-MINUS-ID 'kind 'predicate 'arity 2 'english "$2 squares to minus the identity on $1")
(notation! 'IS-COMPLEX-SEMI-INNER-PRODUCT-SPACE 'kind 'predicate 'arity 1
           'noun "complex semi-inner-product space" 'article "a")
(notation! 'IS-COMPLEX-PRE-HILBERT-SPACE 'kind 'predicate 'arity 1
           'noun "complex pre-Hilbert space" 'article "a")
(notation! 'JOP 'kind 'accessor 'arity 1 'english "the complex structure of $1" 'tex "J_{$1}")
(notation! 'IS-SESQUILINEAR-FORM 'kind 'predicate 'arity 2 'english "$2 is a sesquilinear form on $1")
(notation! 'CACT 'kind 'functoid 'arity 1 'english "the complex scalar multiplication of $1")
(notation! 'CRIP 'kind 'functoid 'arity 1 'english "the complex form of $1")
(notation! 'CSIP-CIPS 'kind 'functoid 'arity 1 'english "$1 as a complex inner product space")
(notation! 'CSIP-QUOTIENT 'kind 'functoid 'arity 1 'english "the quotient of $1 by its null vectors")
(notation! 'COMPLEXIFY 'kind 'functoid 'arity 1 'english "the complexification of $1")
(notation! 'CX-SIP 'kind 'functoid 'arity 1 'english "the real space underlying the complexification of $1")
(notation! 'CIPS-RIP 'kind 'functoid 'arity 1 'english "the real part of the inner product of $1")
(notation! 'CIPS-J 'kind 'functoid 'arity 1 'english "multiplication by i on $1")
(notation! 'CIPS-RSIP 'kind 'functoid 'arity 1 'english "the underlying real semi-inner-product space of $1")
(notation! 'CIPS-REAL 'kind 'functoid 'arity 1 'english "$1 as a real space with complex structure")
