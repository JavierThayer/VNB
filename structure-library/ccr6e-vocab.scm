;;; ccr6e-vocab.scm -- wave of 2026-11-09/10 (agent CCR-1109-D3), wired 2026-11-10 from scratchpad/ccr1109d3/ccr6e-vocab.scm.
;;; Library: complex-analysis.

;;; ccr6e-vocab.scm -- BICHARACTERS ON A VECTOR SPACE E OVER A NORMED FIELD K (CCR.pdf chapter 6: Definition 6.1
;;; for E, the polar (62) and Definition 6.13 for E, the bilinear maps of section 6.4).  DEFINITIONS ONLY; the laws
;;; are in theorem-library/ccr6-e.scm.  Agent CCR-1109-D3, 2026-11-09.  Destination: structure-library/ccr6e-vocab.scm.
;;; Library: complex-analysis (beside ccr5-vocab).  Load window: after ccr4-vocab (IS-ADD-CHARACTER), ccr5-vocab,
;;; module (IS-MODULE, VEC, VADD, ACT), ccr-ch3b-vocab (IS-NORM-ON, CCR-1109-B2; unwired) and ca-lft-vocab (UNIT-CIRCLE).
;;;
;;; The conventions are those of IS-NORM-ON (CCR-1109-B2): a vector space over K is a module E whose scalar ring
;;; is the ring view of K, SCAL(E) = NORMED-FIELD-AS-COMMUTATIVE-RING(K).
;;;
;;;   IS-K-VECTOR-SPACE(K, E)            E is a module with SCAL(E) = the ring view of K
;;;   IS-E-CHARACTER(K, E, chi)          chi : E -> T additive, and continuous along every line: a |-> chi(a x)
;;;                                      is a character of K+ for every x
;;;   IS-E-BICHARACTER(K, E, w)          w : E x E -> T additive in each argument, continuous along lines in
;;;                                      each argument                                              (Def 6.1)
;;;   IS-E-BILINEAR-BICHARACTER(K, E, w) and w(a x, y) = w(x, a y)                                  (Def 6.1, (56))
;;;   E-POLAR(E, w, V)                   {eta in E : w(eta, xi) = 1 for all xi in V}                (62)
;;;   NORM-BALL(E, nu, r)                {x in E : nu(x) <= r}
;;;   IS-E-UNIPOLAR(K, E, nu, w)         nu a norm on E, w a bilinear bicharacter, and the unit ball of nu is
;;;                                      self-polar                                                 (Def 6.13)
;;;   IS-K-BILINEAR-FORM(K, E, lam)      lam : E x E -> K additive and K-homogeneous in each argument (section 6.4)
;;;
;;; CONTINUITY.  Definition 6.1 asks for continuity in each argument for the topology of the norm of E.  It is
;;; stated here along LINES: for each x the map a |-> chi(a x) is a (continuous) character of K.  On a
;;; finite-dimensional E this is continuity for the max norm of any basis (a character of a finite sum is the
;;; product of the characters of the terms), which is continuity for every norm by Proposition 3.8 (equivalence of
;;; norms; not in the tree, CCR-1109-B2 4.2).  It needs no topology on E, and it is exactly what the proofs of 6.24
;;; and 6.32 use (b |-> w(b u, v) is a character of K).
;;; Binders c6v*_: names no other definition uses.

(def-predicate 'IS-K-VECTOR-SPACE '(c6vk_ c6vm_)
  '(AND (IS-MODULE c6vm_) (= (SCAL c6vm_) (NORMED-FIELD-AS-COMMUTATIVE-RING c6vk_))))
(notation! 'IS-K-VECTOR-SPACE 'kind 'predicate 'arity 2 'english "$2 is a vector space over $1")

(def-predicate 'IS-E-CHARACTER '(c6vk_ c6vm_ c6vc_)
  '(AND (IN c6vc_ (FUN (VEC c6vm_) UNIT-CIRCLE))
   (AND (FORALL c6vx_ (IMPLIES (IN c6vx_ (VEC c6vm_)) (FORALL c6vy_ (IMPLIES (IN c6vy_ (VEC c6vm_))
          (= (c6vc_ ((VADD c6vm_) c6vx_ c6vy_)) (* (c6vc_ c6vx_) (c6vc_ c6vy_)))))))
        (FORALL c6vx_ (IMPLIES (IN c6vx_ (VEC c6vm_))
          (IS-ADD-CHARACTER c6vk_ (VNB-LAMBDA c6va_ (CARR c6vk_) (c6vc_ ((ACT c6vm_) c6va_ c6vx_)))))))))
(notation! 'IS-E-CHARACTER 'kind 'predicate 'arity 3 'english "$3 is a character of the additive group of the vector space $2 over $1")

(def-predicate 'IS-E-BICHARACTER '(c6vk_ c6vm_ c6vw_)
  '(AND (IN c6vw_ (FUN (CARTESIAN (VEC c6vm_) (VEC c6vm_)) UNIT-CIRCLE))
   (AND (FORALL c6vx_ (IMPLIES (IN c6vx_ (VEC c6vm_)) (FORALL c6vy_ (IMPLIES (IN c6vy_ (VEC c6vm_))
          (FORALL c6vz_ (IMPLIES (IN c6vz_ (VEC c6vm_))
            (AND (= (c6vw_ ((VADD c6vm_) c6vx_ c6vy_) c6vz_) (* (c6vw_ c6vx_ c6vz_) (c6vw_ c6vy_ c6vz_)))
                 (= (c6vw_ c6vz_ ((VADD c6vm_) c6vx_ c6vy_)) (* (c6vw_ c6vz_ c6vx_) (c6vw_ c6vz_ c6vy_))))))))))
        (FORALL c6vx_ (IMPLIES (IN c6vx_ (VEC c6vm_)) (FORALL c6vy_ (IMPLIES (IN c6vy_ (VEC c6vm_))
          (AND (IS-ADD-CHARACTER c6vk_ (VNB-LAMBDA c6va_ (CARR c6vk_) (c6vw_ ((ACT c6vm_) c6va_ c6vx_) c6vy_)))
               (IS-ADD-CHARACTER c6vk_ (VNB-LAMBDA c6va_ (CARR c6vk_) (c6vw_ c6vy_ ((ACT c6vm_) c6va_ c6vx_))))))))))))
(notation! 'IS-E-BICHARACTER 'kind 'predicate 'arity 3 'english "$3 is a bicharacter on the vector space $2 over $1")

(def-predicate 'IS-E-BILINEAR-BICHARACTER '(c6vk_ c6vm_ c6vw_)
  '(AND (IS-E-BICHARACTER c6vk_ c6vm_ c6vw_)
        (FORALL c6va_ (IMPLIES (IN c6va_ (CARR c6vk_)) (FORALL c6vx_ (IMPLIES (IN c6vx_ (VEC c6vm_)) (FORALL c6vy_ (IMPLIES (IN c6vy_ (VEC c6vm_))
          (= (c6vw_ ((ACT c6vm_) c6va_ c6vx_) c6vy_) (c6vw_ c6vx_ ((ACT c6vm_) c6va_ c6vy_)))))))))))
(notation! 'IS-E-BILINEAR-BICHARACTER 'kind 'predicate 'arity 3 'english "$3 is a bilinear bicharacter on the vector space $2 over $1")

(def-functoid 'E-POLAR '(c6vm_ c6vw_ c6vv_)
  '(SEP c6vh_ (VEC c6vm_) (FORALL c6vx_ (IMPLIES (IN c6vx_ c6vv_) (= (c6vw_ c6vh_ c6vx_) 1)))))
(notation! 'E-POLAR 'kind 'functoid 'arity 3 'english "the polar of $3 in $1 with respect to $2")

(def-functoid 'NORM-BALL '(c6vm_ c6vn_ c6vr_)
  '(SEP c6vx_ (VEC c6vm_) (<= (c6vn_ c6vx_) c6vr_)))
(notation! 'NORM-BALL 'kind 'functoid 'arity 3 'english "the closed ball of radius $3 about 0 in $1 for the norm $2")

(def-predicate 'IS-E-UNIPOLAR '(c6vk_ c6vm_ c6vn_ c6vw_)
  '(AND (IS-NORM-ON c6vk_ c6vm_ c6vn_)
   (AND (IS-E-BILINEAR-BICHARACTER c6vk_ c6vm_ c6vw_)
        (= (E-POLAR c6vm_ c6vw_ (NORM-BALL c6vm_ c6vn_ 1)) (NORM-BALL c6vm_ c6vn_ 1)))))
(notation! 'IS-E-UNIPOLAR 'kind 'predicate 'arity 4 'english "$4 is a unipolar bicharacter on $2 over $1 for the norm $3")

(def-predicate 'IS-K-BILINEAR-FORM '(c6vk_ c6vm_ c6vl_)
  '(AND (IN c6vl_ (FUN (CARTESIAN (VEC c6vm_) (VEC c6vm_)) (CARR c6vk_)))
   (AND (FORALL c6vx_ (IMPLIES (IN c6vx_ (VEC c6vm_)) (FORALL c6vy_ (IMPLIES (IN c6vy_ (VEC c6vm_))
          (FORALL c6vz_ (IMPLIES (IN c6vz_ (VEC c6vm_))
            (AND (= (c6vl_ ((VADD c6vm_) c6vx_ c6vy_) c6vz_) ((ADD c6vk_) (c6vl_ c6vx_ c6vz_) (c6vl_ c6vy_ c6vz_)))
                 (= (c6vl_ c6vz_ ((VADD c6vm_) c6vx_ c6vy_)) ((ADD c6vk_) (c6vl_ c6vz_ c6vx_) (c6vl_ c6vz_ c6vy_))))))))))
        (FORALL c6va_ (IMPLIES (IN c6va_ (CARR c6vk_)) (FORALL c6vx_ (IMPLIES (IN c6vx_ (VEC c6vm_)) (FORALL c6vy_ (IMPLIES (IN c6vy_ (VEC c6vm_))
          (AND (= (c6vl_ ((ACT c6vm_) c6va_ c6vx_) c6vy_) ((MUL c6vk_) c6va_ (c6vl_ c6vx_ c6vy_)))
               (= (c6vl_ c6vx_ ((ACT c6vm_) c6va_ c6vy_)) ((MUL c6vk_) c6va_ (c6vl_ c6vx_ c6vy_)))))))))))))
(notation! 'IS-K-BILINEAR-FORM 'kind 'predicate 'arity 3 'english "$3 is a $1-bilinear form on $2")
