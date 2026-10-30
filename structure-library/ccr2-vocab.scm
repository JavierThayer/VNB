;;; ccr2-vocab.scm -- NON-ARCHIMEDEAN VALUED FIELDS AND THEIR DOMAINS (CCR.pdf chapters 1-2 and 4:
;;; Definitions 1.8, 1.12, 1.14, 2.5, 4.3).  DEFINITIONS ONLY; the laws are in theorem-library/ccr2-nv.scm.
;;; Agent CCR-B2, wave MAP-1026, 2026-10-26.  Destination: structure-library/ccr2-vocab.scm.  Library:
;;; analysis.  Load window: after structure-library/normed-field (IS-NORMED-FIELD, FNRM), metric-subspace
;;; (SUBSPACE-MS), compactness (IS-COMPACT).
;;;
;;; THE MODEL.  The tree's normed field (IS-NORMED-FIELD: a field with an absolute value FNRM) is the
;;; paper's valued field; a NON-ARCHIMEDEAN one adds the ultrametric inequality (Definition 1.8 (iii)).
;;; The paper's NV DOMAIN A ("an integral domain equipped with a non-archimedean valuation such that |x| <= 1
;;; for all x in A", the convention after Remark 1.13) is taken INSIDE an NV field K: a subring of K on which
;;; the absolute value is at most 1.  Remark 1.16 is the reason this loses nothing: every NV domain extends
;;; its valuation to its field of fractions.  Taking A inside K avoids constructing F(A) (a quotient ring);
;;; "K is the field of fractions of A" is the property IS-FRACTIONS-OF(K, A).  Ideals of A are subsets of A
;;; (IS-NV-IDEAL), so no ring structure on A is built.
;;;
;;;   IS-NV-FIELD(K)            a normed field with |x + y| <= max(|x|, |y|)
;;;   NV-INTEGERS(K)            Z(K) = {x in K : |x| <= 1}                      (Definition 1.12)
;;;   IS-NV-DOMAIN(K, A)        A a subring of K with |x| <= 1 on A
;;;   IS-FRACTIONS-OF(K, A)     every x in K has x b = a for some a, b in A, b /= 0  (K = F(A), Def. 1.14)
;;;   IS-COMPACT-NV-DOMAIN(K, A) A compact as a subspace of the metric space of K
;;;   NV-UNITS(K, A)            U(A), the invertible elements of A
;;;   NV-MAXIMAL(K, A)          M(A) = {x in A : |x| < 1}                     (Definition 2.5)
;;;   IS-NV-IDEAL(K, A, I)      an ideal of A
;;;   NV-PRINCIPAL(K, A, x)     the principal ideal (x) = {m x : m in A}
;;;   NV-IDEAL2(K, A, x, y)     the ideal (x, y) = {m x + n y : m, n in A}
;;;   IS-NV-PID(K, A)           every ideal of A is principal
;;;   NV-BALL(K, A, r)          B(r) = {x in A : |x| <= r}                   (Proposition 2.12)
;;; Binders cw*_.

(def-predicate 'IS-NV-FIELD '(cwk_)
  '(AND (IS-NORMED-FIELD cwk_)
        (FORALL cwx_ (IMPLIES (IN cwx_ (CARR cwk_)) (FORALL cwy_ (IMPLIES (IN cwy_ (CARR cwk_))
          (<= ((FNRM cwk_) ((ADD cwk_) cwx_ cwy_)) (MAX ((FNRM cwk_) cwx_) ((FNRM cwk_) cwy_)))))))))
(notation! 'IS-NV-FIELD 'kind 'predicate 'arity 1 'english "$1 is a non-archimedean valued field")

(def-functoid 'NV-INTEGERS '(cwk_)
  '(SEP cwx_ (CARR cwk_) (<= ((FNRM cwk_) cwx_) 1)))
(notation! 'NV-INTEGERS 'kind 'functoid 'arity 1 'english "the ring of integral elements of $1")

(def-predicate 'IS-NV-DOMAIN '(cwk_ cwa_)
  '(AND (IS-NV-FIELD cwk_)
   (AND (FORALL cwx_ (IMPLIES (IN cwx_ cwa_) (IN cwx_ (CARR cwk_))))
   (AND (IN (ZERO cwk_) cwa_)
   (AND (IN (ONE cwk_) cwa_)
   (AND (FORALL cwx_ (IMPLIES (IN cwx_ cwa_) (FORALL cwy_ (IMPLIES (IN cwy_ cwa_) (IN ((ADD cwk_) cwx_ cwy_) cwa_)))))
   (AND (FORALL cwx_ (IMPLIES (IN cwx_ cwa_) (FORALL cwy_ (IMPLIES (IN cwy_ cwa_) (IN ((MUL cwk_) cwx_ cwy_) cwa_)))))
   (AND (FORALL cwx_ (IMPLIES (IN cwx_ cwa_) (IN ((NEG cwk_) cwx_) cwa_)))
        (FORALL cwx_ (IMPLIES (IN cwx_ cwa_) (<= ((FNRM cwk_) cwx_) 1)))))))))))
(notation! 'IS-NV-DOMAIN 'kind 'predicate 'arity 2
           'english "$2 is a non-archimedean valued domain inside the field $1")

(def-predicate 'IS-FRACTIONS-OF '(cwk_ cwa_)
  '(FORALL cwx_ (IMPLIES (IN cwx_ (CARR cwk_))
     (FORSOME cwu_ (AND (IN cwu_ cwa_) (FORSOME cwv_ (AND (IN cwv_ cwa_)
       (AND (NOT (= cwv_ (ZERO cwk_))) (= ((MUL cwk_) cwx_ cwv_) cwu_)))))))))
(notation! 'IS-FRACTIONS-OF 'kind 'predicate 'arity 2 'english "$1 is the field of fractions of $2")

(def-predicate 'IS-COMPACT-NV-DOMAIN '(cwk_ cwa_)
  '(AND (IS-NV-DOMAIN cwk_ cwa_)
        (IS-COMPACT (SUBSPACE-MS (NF-METRIC-SPACE cwk_) cwa_))))
(notation! 'IS-COMPACT-NV-DOMAIN 'kind 'predicate 'arity 2
           'english "$2 is a compact non-archimedean valued domain inside the field $1")

(def-functoid 'NV-UNITS '(cwk_ cwa_)
  '(SEP cwx_ cwa_ (FORSOME cwy_ (AND (IN cwy_ cwa_) (= ((MUL cwk_) cwx_ cwy_) (ONE cwk_))))))
(notation! 'NV-UNITS 'kind 'functoid 'arity 2 'english "the group of units of $2")

(def-functoid 'NV-MAXIMAL '(cwk_ cwa_)
  '(SEP cwx_ cwa_ (< ((FNRM cwk_) cwx_) 1)))
(notation! 'NV-MAXIMAL 'kind 'functoid 'arity 2 'english "the elements of $2 of absolute value less than one")

(def-predicate 'IS-NV-IDEAL '(cwk_ cwa_ cwi_)
  '(AND (FORALL cwx_ (IMPLIES (IN cwx_ cwi_) (IN cwx_ cwa_)))
   (AND (IN (ZERO cwk_) cwi_)
   (AND (FORALL cwx_ (IMPLIES (IN cwx_ cwi_) (FORALL cwy_ (IMPLIES (IN cwy_ cwi_) (IN ((ADD cwk_) cwx_ cwy_) cwi_)))))
   (AND (FORALL cwx_ (IMPLIES (IN cwx_ cwi_) (IN ((NEG cwk_) cwx_) cwi_)))
        (FORALL cwr_ (IMPLIES (IN cwr_ cwa_) (FORALL cwx_ (IMPLIES (IN cwx_ cwi_) (IN ((MUL cwk_) cwr_ cwx_) cwi_))))))))))
(notation! 'IS-NV-IDEAL 'kind 'predicate 'arity 3 'english "$3 is an ideal of $2")

(def-functoid 'NV-PRINCIPAL '(cwk_ cwa_ cwg_)
  '(SEP cwx_ cwa_ (FORSOME cwm_ (AND (IN cwm_ cwa_) (= cwx_ ((MUL cwk_) cwm_ cwg_))))))
(notation! 'NV-PRINCIPAL 'kind 'functoid 'arity 3 'english "the principal ideal of $2 generated by $3")

(def-functoid 'NV-IDEAL2 '(cwk_ cwa_ cwg_ cwh_)
  '(SEP cwx_ cwa_ (FORSOME cwm_ (AND (IN cwm_ cwa_) (FORSOME cwn_ (AND (IN cwn_ cwa_)
     (= cwx_ ((ADD cwk_) ((MUL cwk_) cwm_ cwg_) ((MUL cwk_) cwn_ cwh_)))))))))
(notation! 'NV-IDEAL2 'kind 'functoid 'arity 4 'english "the ideal of $2 generated by $3 and $4")

(def-predicate 'IS-NV-PID '(cwk_ cwa_)
  '(AND (IS-NV-DOMAIN cwk_ cwa_)
        (FORALL cwi_ (IMPLIES (IS-NV-IDEAL cwk_ cwa_ cwi_)
          (FORSOME cwg_ (AND (IN cwg_ cwa_) (= cwi_ (NV-PRINCIPAL cwk_ cwa_ cwg_))))))))
(notation! 'IS-NV-PID 'kind 'predicate 'arity 2 'english "$2 is a principal ideal domain")

(def-functoid 'NV-BALL '(cwk_ cwa_ cwr_)
  '(SEP cwx_ cwa_ (<= ((FNRM cwk_) cwx_) cwr_)))
(notation! 'NV-BALL 'kind 'functoid 'arity 3 'english "the elements of $2 of absolute value at most $3")
