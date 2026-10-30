;;; ccr4-vocab.scm -- ADDITIVE CHARACTERS OF A NORMED FIELD AND THE DUALITY MAP (CCR.pdf chapter 5, Definitions
;;; 5.1 and 5.11; chapter 6, Definition 6.1 for E = K).  DEFINITIONS ONLY; the laws are in
;;; theorem-library/ccr4-chars.scm.  Agent CCR-B4, 2026-10-26.  Destination: structure-library/ccr4-vocab.scm.
;;; Library: analysis.  Load window: after normed-field-metric, metric-continuity, ca-lft-vocab (UNIT-CIRCLE).
;;;
;;;   IS-ADD-CHARACTER(K, chi)      chi : K -> T a continuous homomorphism of the additive group (Def 5.1;
;;;                                 T = UNIT-CIRCLE inside CC, CC with its metric CC-MS)
;;;   IS-NONTRIVIAL-CHARACTER(K, chi)  a character with chi(x) /= 1 for some x
;;;   DUALITY-MAP(K, chi, a)        Psi_chi(a) = x |-> chi(a x)                         (Def 5.11, (54))
;;;   IS-BICHARACTER(K, w)          w : K x K -> T, a character in each argument        (Def 6.1, E = K)
;;;   IS-BILINEAR-BICHARACTER(K, w) and w(a x, y) = w(x, a y)                           (Def 6.1, (56))
;;;   BICHAR-OF(K, chi, a)          (x, y) |-> chi(a x y)                                 (Lemma 6.3, (57))
;;; Binders ch*_.

(def-predicate 'IS-ADD-CHARACTER '(chk_ chc_)
  '(AND (IN chc_ (FUN (CARR chk_) UNIT-CIRCLE))
   (AND (FORALL chx_ (IMPLIES (IN chx_ (CARR chk_)) (FORALL chy_ (IMPLIES (IN chy_ (CARR chk_))
          (= (chc_ ((ADD chk_) chx_ chy_)) (* (chc_ chx_) (chc_ chy_)))))))
        (IS-CONTINUOUS (NF-METRIC-SPACE chk_) CC-MS chc_))))
(notation! 'IS-ADD-CHARACTER 'kind 'predicate 'arity 2 'english "$2 is a character of the additive group of $1")

(def-predicate 'IS-NONTRIVIAL-CHARACTER '(chk_ chc_)
  '(AND (IS-ADD-CHARACTER chk_ chc_)
        (FORSOME chx_ (AND (IN chx_ (CARR chk_)) (NOT (= (chc_ chx_) 1))))))
(notation! 'IS-NONTRIVIAL-CHARACTER 'kind 'predicate 'arity 2 'english "$2 is a non-trivial character of the additive group of $1")

(def-functoid 'DUALITY-MAP '(chk_ chc_ cha_)
  '(VNB-LAMBDA chx_ (CARR chk_) (chc_ ((MUL chk_) cha_ chx_))))
(notation! 'DUALITY-MAP 'kind 'functoid 'arity 3 'english "the character x |-> $2($3 x) of $1")

(def-predicate 'IS-BICHARACTER '(chk_ chw_)
  '(AND (IN chw_ (FUN (CARTESIAN (CARR chk_) (CARR chk_)) UNIT-CIRCLE))
   (AND (FORALL chy_ (IMPLIES (IN chy_ (CARR chk_))
          (IS-ADD-CHARACTER chk_ (VNB-LAMBDA chx_ (CARR chk_) (chw_ chx_ chy_)))))
        (FORALL chy_ (IMPLIES (IN chy_ (CARR chk_))
          (IS-ADD-CHARACTER chk_ (VNB-LAMBDA chx_ (CARR chk_) (chw_ chy_ chx_))))))))
(notation! 'IS-BICHARACTER 'kind 'predicate 'arity 2 'english "$2 is a bicharacter on $1")

(def-predicate 'IS-BILINEAR-BICHARACTER '(chk_ chw_)
  '(AND (IS-BICHARACTER chk_ chw_)
        (FORALL cha_ (IMPLIES (IN cha_ (CARR chk_)) (FORALL chx_ (IMPLIES (IN chx_ (CARR chk_)) (FORALL chy_ (IMPLIES (IN chy_ (CARR chk_))
          (= (chw_ ((MUL chk_) cha_ chx_) chy_) (chw_ chx_ ((MUL chk_) cha_ chy_)))))))))))
(notation! 'IS-BILINEAR-BICHARACTER 'kind 'predicate 'arity 2 'english "$2 is a bilinear bicharacter on $1")

;;; BICHAR-OF(K, chi, a): (x, y) |-> chi(a x y), the bicharacter (57) of Lemma 6.3
(def-functoid 'BICHAR-OF '(chk_ chc_ cha_)
  '(VNB-LAMBDA (LIST chu_ chv_) (CARTESIAN (CARR chk_) (CARR chk_)) (chc_ ((MUL chk_) cha_ ((MUL chk_) chu_ chv_)))))
(notation! 'BICHAR-OF 'kind 'functoid 'arity 3 'english "the bicharacter (x, y) |-> $2($3 x y) of $1")
