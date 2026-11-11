;;; ba-ops-vocab.scm -- wave of 2026-11-09/10 (agent BA-BH), wired 2026-11-10 from scratchpad/babh-1109/ba-ops-vocab.scm.
;;; Library: operator-algebras.

;;; ba-ops-vocab.scm -- OPERATORS ON A COMPLEX HILBERT SPACE: bounded operators, the operator
;;; norm, the adjoint, the algebra B(H) as a 10-tuple in the slot layout of ba-vocab.scm, the
;;; range / kernel / support of an operator, the projection E_K as a term, partial isometries,
;;; and the Hilbert direct sum H (+) K.
;;; F. J. Thayer, "Banach Algebras and Applications" (docs/BanachAlgebras.pdf), ch. 1 s.7 and
;;; ch. 2 s.1.  DEFINITIONS ONLY: no proof, no support, no axiom.
;;; Agent BA-BH, wave 2026-11-09.  Destination: structure-library/ba-ops-vocab.scm.
;;; Library: operator-algebras (BA-MAP-REPORT.md s.3.9).
;;; Load window: after structure-library/ba-vocab (the 10-slot layout, IS-PROJECTION-EL ...)
;;; and structure-library/hilbert-space (IS-HILBERT-SPACE, IP-METRIC-SPACE, PERP,
;;; IS-ORTHOGONAL-PROJECTION); both load well before position 1700.
;;;
;;; A Hilbert space is the tree's IS-HILBERT-SPACE on COMPLEX-INNER-PRODUCT-SPACE
;;; (BA-MAP-REPORT.md s.4, decided).  Its inner product is linear in the FIRST argument (the
;;; notes' convention), and ||x|| is IP-NORM(v, x) = SQRT(<x, x>).
;;;
;;; THE OPERATOR NORM is the textbook  ||T|| = sup { ||Tx|| / ||x|| : x /= 0 }, with 0 put
;;; in the set so that it is inhabited when H = {0} (then ||T|| = 0).  It is a SUP over RR
;;; (rr-sup-*), not an IOTA: the spec theorem `opnorm-spec' says it is the least nonnegative
;;; bound, which is DUAL-NORM's IOTA body (linear-functional.scm) for operators.
;;;
;;; THE ADJOINT is defined POINTWISE: T*(y) is the IOTA of the z with <Tx | y> = <x | z> for
;;; every x.  The z exists by `riesz-representation' applied to x |-> <Tx | y> and is unique
;;; by `riesz-representation-unique'.
;;;
;;; THE ALGEBRA B(H).  BH-ALGEBRA(v) is the 10-tuple
;;;   [CC ring view, BOUNDED-OPS(v,v), +, 0, -, scalar action, OPNORM, composition, identity,
;;;    adjoint]
;;; in exactly ba-vocab.scm's slots (SCAL VEC VADD VZERO VNEG ACT VNRM VMUL VONE VSTAR); the
;;; product is composition, S.T = S o T (x |-> S(T x)).  Each operation of the tuple is a
;;; VNB-LAMBDA over BOUNDED-OPS(v, v) whose body is a NAMED operator construction (BOP-SUM,
;;; BOP-SCALE, ...), so that a beta at typed operators yields a term that `mac' opens and the
;;; pointwise value lemmas read.
;;;
;;; Names: the generated arrow names and gal-ch-vocab.scm's OP-ZERO / OP-NEG are taken, so the
;;; constructions are BOP-* ("bounded operator").  Binders: bo*_ (box_ boy_ boz_ boa_ bom_ boc_
;;; bok_ bop_ bos_ bot_) and bh*_ for HSUM, used by no other file.  Parameters are bov_ bow_
;;; bos_ bot_ boc_ bok_ (functoid parameters), never single letters.

;;; --------------------------------------------------------------------------------------------
;;; LINEAR AND BOUNDED OPERATORS v -> w (v, w complex inner product spaces)
(def-predicate 'IS-LINEAR-OP '(bov_ bow_ bot_)
  '(AND (IN bot_ (FUN (VEC bov_) (VEC bow_)))
   (AND (FORALL box_ (IMPLIES (IN box_ (VEC bov_)) (FORALL boy_ (IMPLIES (IN boy_ (VEC bov_))
          (= (bot_ ((VADD bov_) box_ boy_)) ((VADD bow_) (bot_ box_) (bot_ boy_)))))))
        (FORALL boc_ (IMPLIES (IN boc_ CC) (FORALL box_ (IMPLIES (IN box_ (VEC bov_))
          (= (bot_ ((ACT bov_) boc_ box_)) ((ACT bow_) boc_ (bot_ box_))))))))))

(def-predicate 'IS-BOUNDED-OP '(bov_ bow_ bot_)
  '(AND (IS-LINEAR-OP bov_ bow_ bot_)
        (FORSOME bom_ (AND (IN bom_ RR) (AND (<= 0 bom_)
          (FORALL box_ (IMPLIES (IN box_ (VEC bov_))
            (<= (IP-NORM bow_ (bot_ box_)) (* bom_ (IP-NORM bov_ box_))))))))))

;;; L(v, w): the bounded linear operators
(def-functoid 'BOUNDED-OPS '(bov_ bow_)
  '(SEP bot_ (FUN (VEC bov_) (VEC bow_)) (IS-BOUNDED-OP bov_ bow_ bot_)))

;;; ||T|| = sup ({0} u { ||Tx|| / ||x|| : x in H, ||x|| /= 0 })
(def-functoid 'OPNORM '(bov_ bow_ bot_)
  '(SUP (SEP boa_ RR
          (OR (= boa_ 0)
              (FORSOME box_ (AND (IN box_ (VEC bov_))
                            (AND (NOT (= (IP-NORM bov_ box_) 0))
                                 (= boa_ (* (IP-NORM bow_ (bot_ box_)) (recip (IP-NORM bov_ box_)))))))))))

;;; --------------------------------------------------------------------------------------------
;;; THE OPERATOR CONSTRUCTIONS (pointwise)
(def-functoid 'BOP-SUM '(bov_ bow_ bos_ bot_)
  '(VNB-LAMBDA box_ (VEC bov_) ((VADD bow_) (bos_ box_) (bot_ box_))))
(def-functoid 'BOP-ZERO '(bov_ bow_)
  '(VNB-LAMBDA box_ (VEC bov_) (VZERO bow_)))
(def-functoid 'BOP-NEG '(bov_ bow_ bot_)
  '(VNB-LAMBDA box_ (VEC bov_) ((VNEG bow_) (bot_ box_))))
(def-functoid 'BOP-SCALE '(bov_ bow_ boc_ bot_)
  '(VNB-LAMBDA box_ (VEC bov_) ((ACT bow_) boc_ (bot_ box_))))
;;; S o T with T defined on VEC(v)
(def-functoid 'BOP-COMP '(bov_ bos_ bot_)
  '(VNB-LAMBDA box_ (VEC bov_) (bos_ (bot_ box_))))
(def-functoid 'BOP-ID '(bov_)
  '(VNB-LAMBDA box_ (VEC bov_) box_))

;;; the adjoint T* : w -> v of T : v -> w, <T x | y> = <x | T* y>
(def-functoid 'OP-ADJOINT '(bov_ bow_ bot_)
  '(VNB-LAMBDA boy_ (VEC bow_)
     (IOTA boz_ (AND (IN boz_ (VEC bov_))
                     (FORALL box_ (IMPLIES (IN box_ (VEC bov_))
                       (= ((IP bow_) (bot_ box_) boy_) ((IP bov_) box_ boz_))))))))

;;; --------------------------------------------------------------------------------------------
;;; B(H) AS A UNITAL C*-ALGEBRA (ba-vocab.scm's slots 1-10)
(def-functoid 'BH-VADD '(bov_)
  '(VNB-LAMBDA (LIST bos_ bot_) (CARTESIAN (BOUNDED-OPS bov_ bov_) (BOUNDED-OPS bov_ bov_))
     (BOP-SUM bov_ bov_ bos_ bot_)))
(def-functoid 'BH-VNEG '(bov_)
  '(VNB-LAMBDA bot_ (BOUNDED-OPS bov_ bov_) (BOP-NEG bov_ bov_ bot_)))
(def-functoid 'BH-ACT '(bov_)
  '(VNB-LAMBDA (LIST boc_ bot_) (CARTESIAN CC (BOUNDED-OPS bov_ bov_))
     (BOP-SCALE bov_ bov_ boc_ bot_)))
(def-functoid 'BH-VNRM '(bov_)
  '(VNB-LAMBDA bot_ (BOUNDED-OPS bov_ bov_) (OPNORM bov_ bov_ bot_)))
(def-functoid 'BH-VMUL '(bov_)
  '(VNB-LAMBDA (LIST bos_ bot_) (CARTESIAN (BOUNDED-OPS bov_ bov_) (BOUNDED-OPS bov_ bov_))
     (BOP-COMP bov_ bos_ bot_)))
(def-functoid 'BH-VSTAR '(bov_)
  '(VNB-LAMBDA bot_ (BOUNDED-OPS bov_ bov_) (OP-ADJOINT bov_ bov_ bot_)))

(def-functoid 'BH-ALGEBRA '(bov_)
  '(LIST (NORMED-FIELD-AS-COMMUTATIVE-RING CC-NORMED-FIELD) (BOUNDED-OPS bov_ bov_)
         (BH-VADD bov_) (BOP-ZERO bov_ bov_) (BH-VNEG bov_) (BH-ACT bov_) (BH-VNRM bov_)
         (BH-VMUL bov_) (BOP-ID bov_) (BH-VSTAR bov_)))

;;; --------------------------------------------------------------------------------------------
;;; RANGE, KERNEL, SUPPORT; PROJECTIONS; PARTIAL ISOMETRIES
(def-functoid 'OP-RANGE '(bov_ bow_ bot_)
  '(SEP boy_ (VEC bow_) (FORSOME box_ (AND (IN box_ (VEC bov_)) (= boy_ (bot_ box_))))))
(def-functoid 'OP-KERNEL '(bov_ bow_ bot_)
  '(SEP box_ (VEC bov_) (= (bot_ box_) (VZERO bow_))))
;;; the support of U (Remark 2.3): the orthogonal complement of its kernel
(def-functoid 'OP-SUPPORT '(bov_ bow_ bot_)
  '(PERP bov_ (OP-KERNEL bov_ bow_ bot_)))

;;; E_K, the orthogonal projection onto K as a term (Definition 1.54); unique by
;;; orthogonal-projection-unique, so the IOTA denotes when K is a closed subspace
(def-functoid 'PROJ-OP '(bov_ bok_)
  '(IOTA bop_ (IS-ORTHOGONAL-PROJECTION bov_ bok_ bop_)))

;;; a projection (Definition 1.56): a self-adjoint idempotent bounded operator on H
(def-predicate 'IS-PROJECTION-OP '(bov_ bot_)
  '(AND (IN bot_ (BOUNDED-OPS bov_ bov_))
   (AND (= (OP-ADJOINT bov_ bov_ bot_) bot_)
        (= (BOP-COMP bov_ bot_ bot_) bot_))))

;;; U is an isometry on ks: ||U x|| = ||x|| for x in ks
(def-predicate 'IS-ISOMETRIC-ON '(bov_ bow_ bot_ bok_)
  '(FORALL box_ (IMPLIES (IN box_ bok_) (= (IP-NORM bow_ (bot_ box_)) (IP-NORM bov_ box_)))))

;;; Definition 2.2: U in L(H) is isometric on some closed subspace K and 0 on K-perp
(def-predicate 'IS-PARTIAL-ISOMETRY '(bov_ bot_)
  '(AND (IN bot_ (BOUNDED-OPS bov_ bov_))
        (FORSOME bok_ (AND (IS-SUBMODULE bov_ bok_)
                      (AND (IS-CLOSED (IP-METRIC-SPACE bov_) bok_)
                      (AND (IS-ISOMETRIC-ON bov_ bov_ bot_ bok_)
                           (FORALL box_ (IMPLIES (IN box_ (PERP bov_ bok_))
                             (= (bot_ box_) (VZERO bov_))))))))))

;;; --------------------------------------------------------------------------------------------
;;; THE HILBERT DIRECT SUM H (+) K: pairs, componentwise operations, <(a,b) | (c,d)> =
;;; <a | c> + <b | d>.  A 7-tuple in COMPLEX-INNER-PRODUCT-SPACE's layout.  Binders bh*_.
(def-functoid 'HSUM-VEC '(bov_ bow_) '(CARTESIAN (VEC bov_) (VEC bow_)))
(def-functoid 'HSUM-VADD '(bov_ bow_)
  '(VNB-LAMBDA (LIST bhp_ bhq_) (CARTESIAN (CARTESIAN (VEC bov_) (VEC bow_)) (CARTESIAN (VEC bov_) (VEC bow_)))
     (LIST ((VADD bov_) (NTH 1 bhp_) (NTH 1 bhq_)) ((VADD bow_) (NTH 2 bhp_) (NTH 2 bhq_)))))
(def-functoid 'HSUM-VNEG '(bov_ bow_)
  '(VNB-LAMBDA bhp_ (CARTESIAN (VEC bov_) (VEC bow_))
     (LIST ((VNEG bov_) (NTH 1 bhp_)) ((VNEG bow_) (NTH 2 bhp_)))))
(def-functoid 'HSUM-ACT '(bov_ bow_)
  '(VNB-LAMBDA (LIST bhc_ bhp_) (CARTESIAN CC (CARTESIAN (VEC bov_) (VEC bow_)))
     (LIST ((ACT bov_) bhc_ (NTH 1 bhp_)) ((ACT bow_) bhc_ (NTH 2 bhp_)))))
(def-functoid 'HSUM-IP '(bov_ bow_)
  '(VNB-LAMBDA (LIST bhp_ bhq_) (CARTESIAN (CARTESIAN (VEC bov_) (VEC bow_)) (CARTESIAN (VEC bov_) (VEC bow_)))
     (+ ((IP bov_) (NTH 1 bhp_) (NTH 1 bhq_)) ((IP bow_) (NTH 2 bhp_) (NTH 2 bhq_)))))
(def-functoid 'HSUM '(bov_ bow_)
  '(LIST (NORMED-FIELD-AS-COMMUTATIVE-RING CC-NORMED-FIELD) (CARTESIAN (VEC bov_) (VEC bow_))
         (HSUM-VADD bov_ bow_) (LIST (VZERO bov_) (VZERO bow_)) (HSUM-VNEG bov_ bow_)
         (HSUM-ACT bov_ bow_) (HSUM-IP bov_ bow_)))

;;; --------------------------------------------------------------------------------------------
;;; Notation
(notation! 'IS-LINEAR-OP 'kind 'predicate 'arity 3 'english "$3 is a linear operator from $1 to $2")
(notation! 'IS-BOUNDED-OP 'kind 'predicate 'arity 3 'english "$3 is a bounded linear operator from $1 to $2")
(notation! 'BOUNDED-OPS 'kind 'functoid 'arity 2 'english "the bounded operators from $1 to $2" 'tex "L({$1}, {$2})")
(notation! 'OPNORM 'kind 'functoid 'arity 3 'english "the operator norm of $3" 'tex "\\lVert {$3} \\rVert")
(notation! 'BOP-SUM 'kind 'functoid 'arity 4 'english "$3 + $4" 'tex "{$3} + {$4}")
(notation! 'BOP-ZERO 'kind 'functoid 'arity 2 'english "the zero operator from $1 to $2" 'tex "0")
(notation! 'BOP-NEG 'kind 'functoid 'arity 3 'english "- $3" 'tex "-{$3}")
(notation! 'BOP-SCALE 'kind 'functoid 'arity 4 'english "$3 $4" 'tex "{$3}\\,{$4}")
(notation! 'BOP-COMP 'kind 'functoid 'arity 3 'english "$2 $3" 'tex "{$2}{$3}")
(notation! 'BOP-ID 'kind 'functoid 'arity 1 'english "the identity operator of $1" 'tex "1")
(notation! 'OP-ADJOINT 'kind 'functoid 'arity 3 'english "the adjoint of $3" 'tex "{$3}^{*}")
(notation! 'BH-ALGEBRA 'kind 'functoid 'arity 1 'english "the algebra of bounded operators on $1" 'tex "L({$1})")
(notation! 'OP-RANGE 'kind 'functoid 'arity 3 'english "the range of $3" 'tex "\\mathrm{ran}\\,{$3}")
(notation! 'OP-KERNEL 'kind 'functoid 'arity 3 'english "the kernel of $3" 'tex "\\ker {$3}")
(notation! 'OP-SUPPORT 'kind 'functoid 'arity 3 'english "the support of $3" 'tex "\\mathrm{supp}\\,{$3}")
(notation! 'PROJ-OP 'kind 'functoid 'arity 2 'english "the orthogonal projection onto $2" 'tex "E_{$2}")
(notation! 'IS-PROJECTION-OP 'kind 'predicate 'arity 2 'english "$2 is a projection on $1")
(notation! 'IS-ISOMETRIC-ON 'kind 'predicate 'arity 4 'english "$3 is isometric on $4")
(notation! 'IS-PARTIAL-ISOMETRY 'kind 'predicate 'arity 2 'english "$2 is a partial isometry in $1")
(notation! 'HSUM 'kind 'functoid 'arity 2 'english "the Hilbert direct sum of $1 and $2" 'tex "{$1} \\oplus {$2}")
