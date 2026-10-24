;;; la-z3-vocab.scm -- quotient modules, the ring as a module over itself, the cyclic
;;; groups Z/(a), finite direct sums of modules and module isomorphisms (LA-Z3,
;;; 2026-10-24).  No proof in this file.
;;;
;;; THE SOURCE.  The user's linear-algebra notes, section "Structure of Finitely Generated
;;; Abelian Groups": Lemma 3.49 ("the quotient E/F is isomorphic to the group Z/(a_1) +
;;; ... + Z/(a_k) + Z + ... + Z"), Proposition 3.50, Corollaries 3.51 and 3.52.  An abelian
;;; group is a ZZ-module (SCAL = ZZ-RING), as in structure-library/la-z2-vocab.scm.
;;;
;;; THE DEFINITIONS (the vocabulary the user adopted on 2026-10-24).
;;;   QMOD-REL(md, sm), QMOD-SETOID(md, sm) -- x ~ y iff x + (-y) lies in sm, as an
;;;       extensional set of pairs, and the SETOID [VEC md, ~] of structure-library/setoid.
;;;   QUOTIENT-MODULE(md, sm) -- E/F: the classes of that setoid with the operations that
;;;       DESCEND from the operations of md (the recipe of SIP-QUOTIENT, sip-vocab.scm):
;;;       [scalars, classes, +, [0], -, action].  QMOD-SCALE(md, sm, r) is the action of
;;;       ONE scalar r on the classes.
;;;   RING-AS-MODULE(R) -- the ring R as a module over itself: [R, CARR R, ADD R, ZERO R,
;;;       NEG R, MUL R].
;;;   ZZ-MOD(a) -- Z/(a): the quotient of RING-AS-MODULE(ZZ-RING) by the ideal aZ
;;;       (PRINCIPAL-IDEAL(ZZ-RING, a), structure-library/ideal), a ZZ-module.
;;;       Z/(0) is a copy of Z, so the notes' Z^(n-k) is a sum of copies of Z/(0).
;;;   DIRECT-SUM(S, n, F) -- the direct sum of the modules F(1), ..., F(n) over the scalar
;;;       ring S: the functions f on [1, n] with f(i) in VEC(F(i)), with the operations
;;;       taken componentwise.  F is a function on [1, n] whose values are modules.
;;;   IS-ISO-MODULE(A, B, f) -- f is a module isomorphism: IS-HOM-MODULE(A, B, f) and f a
;;;       bijection of VEC A onto VEC B.
;;;
;;; Binders: qmp_ qma_ qmb_ qmr_ qmc_ (quotient), dsv_ dsk_ dsj_ dsf_ dsg_ dsi_ dqr_
;;; (direct sum): names no predicate body, statement or driver uses elsewhere.
;;; Needs: structure-library/setoid (SETOID, CLASS, QUOTIENT, DESCEND, DESCEND2), module
;;; (MODULE), ideal (PRINCIPAL-IDEAL), numeric-instances (ZZ-RING), bijection
;;; (BIJECTION), and IS-HOM-MODULE (the generated arrows of MODULE).
;;; Destination structure-library/; LOAD WINDOW after setoid, module, ideal,
;;; bijection and numeric-instances; before theorem-library/la-z3-quotient.
;;; Library: linear-algebra.  No axiom, support or stamp.

(def-functoid 'QMOD-REL '(md sm)
  '(SEP qmp_ (CARTESIAN (VEC md) (VEC md))
     (IN ((VADD md) (NTH 1 qmp_) ((VNEG md) (NTH 2 qmp_))) sm)))

(def-functoid 'QMOD-SETOID '(md sm)
  '(LIST (VEC md) (QMOD-REL md sm)))

(def-functoid 'QMOD-VADD '(md sm)
  '(DESCEND2 (QMOD-SETOID md sm)
     (VNB-LAMBDA (LIST qma_ qmb_) (CARTESIAN (VEC md) (VEC md))
       (CLASS (QMOD-SETOID md sm) ((VADD md) qma_ qmb_)))))

(def-functoid 'QMOD-VNEG '(md sm)
  '(DESCEND (QMOD-SETOID md sm)
     (VNB-LAMBDA qma_ (VEC md) (CLASS (QMOD-SETOID md sm) ((VNEG md) qma_)))))

;;; the action of ONE scalar r on the classes
(def-functoid 'QMOD-SCALE '(md sm r)
  '(DESCEND (QMOD-SETOID md sm)
     (VNB-LAMBDA qma_ (VEC md) (CLASS (QMOD-SETOID md sm) ((ACT md) r qma_)))))

(def-functoid 'QMOD-ACT '(md sm)
  '(VNB-LAMBDA (LIST qmr_ qmc_) (CARTESIAN (CARR (SCAL md)) (QUOTIENT (QMOD-SETOID md sm)))
     ((QMOD-SCALE md sm qmr_) qmc_)))

;;; E/F: [scalars, classes, +, [0], -, action]
(def-functoid 'QUOTIENT-MODULE '(md sm)
  '(LIST (SCAL md) (QUOTIENT (QMOD-SETOID md sm)) (QMOD-VADD md sm)
         (CLASS (QMOD-SETOID md sm) (VZERO md)) (QMOD-VNEG md sm) (QMOD-ACT md sm)))

(def-functoid 'RING-AS-MODULE '(R)
  '(LIST R (CARR R) (ADD R) (ZERO R) (NEG R) (MUL R)))

(def-functoid 'ZZ-MOD '(a)
  '(QUOTIENT-MODULE (RING-AS-MODULE ZZ-RING) (PRINCIPAL-IDEAL ZZ-RING a)))

(def-functoid 'DSUM-VEC '(n F)
  '(SEP dsv_ (FUN (INTERVAL 1 n) (BIG-UNION dsk_ (INTERVAL 1 n) (VEC (F dsk_))))
     (FORALL dsj_ (IMPLIES (IN dsj_ (INTERVAL 1 n)) (IN (dsv_ dsj_) (VEC (F dsj_)))))))

(def-functoid 'DSUM-VADD '(n F)
  '(VNB-LAMBDA (LIST dsf_ dsg_) (CARTESIAN (DSUM-VEC n F) (DSUM-VEC n F))
     (VNB-LAMBDA dsi_ (INTERVAL 1 n) ((VADD (F dsi_)) (dsf_ dsi_) (dsg_ dsi_)))))

(def-functoid 'DSUM-VZERO '(n F)
  '(VNB-LAMBDA dsi_ (INTERVAL 1 n) (VZERO (F dsi_))))

(def-functoid 'DSUM-VNEG '(n F)
  '(VNB-LAMBDA dsf_ (DSUM-VEC n F)
     (VNB-LAMBDA dsi_ (INTERVAL 1 n) ((VNEG (F dsi_)) (dsf_ dsi_)))))

(def-functoid 'DSUM-ACT '(S n F)
  '(VNB-LAMBDA (LIST dqr_ dsf_) (CARTESIAN (CARR S) (DSUM-VEC n F))
     (VNB-LAMBDA dsi_ (INTERVAL 1 n) ((ACT (F dsi_)) dqr_ (dsf_ dsi_)))))

(def-functoid 'DIRECT-SUM '(S n F)
  '(LIST S (DSUM-VEC n F) (DSUM-VADD n F) (DSUM-VZERO n F) (DSUM-VNEG n F) (DSUM-ACT S n F)))

(def-predicate 'IS-ISO-MODULE '(A B f)
  '(AND (IS-HOM-MODULE A B f) (IN f (BIJECTION (VEC A) (VEC B)))))

(notation! 'QMOD-REL 'kind 'functoid 'arity 2
           'english "the congruence modulo $2 on $1")
(notation! 'QMOD-SETOID 'kind 'functoid 'arity 2
           'english "the vectors of $1 under the congruence modulo $2")
(notation! 'QUOTIENT-MODULE 'kind 'functoid 'arity 2
           'english "the quotient module $1/$2")
(notation! 'RING-AS-MODULE 'kind 'functoid 'arity 1
           'english "$1 as a module over itself")
(notation! 'ZZ-MOD 'kind 'functoid 'arity 1
           'english "Z/($1)")
(notation! 'DIRECT-SUM 'kind 'functoid 'arity 3
           'english "the direct sum of the $2 modules $3 over $1")
(notation! 'IS-ISO-MODULE 'kind 'predicate 'arity 3
           'english "$3 is an isomorphism of the module $1 onto the module $2")
