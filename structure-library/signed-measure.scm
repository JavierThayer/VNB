;;; signed-measure.scm -- WAVE 2 (2026-10-27..30), wired 2026-10-30 from scratchpad/mf/mf-vocab.scm.
;;; Library: measure.

;;; mf-vocab.scm -- signed measures (construction-of-measures.pdf ch. 3, sec. 4): DEFINITIONS ONLY.
;;; Agent M-F, 2026-10-29 (NEW DEFINITIONS, the user's to confirm).
;;; DESTINATION: structure-library/signed-measure.scm.  Library: measure.
;;; Load window: after structure-library/measure.scm (IS-MEASURE, IS-SIGMA-ALGEBRA), extended-reals
;;; (RR-STAR, POS-INF, NEG-INF), extended-reals-pos (ESUP, RR-POS-STAR, eplus), power-series.scm
;;; (SERIES-PARTIAL-SUM).
;;;
;;; THE EXTENDED LINE.  [-inf, +inf] is RR-STAR.  Three operations on it:
;;;   EXT-NEG(x)       -x, with -(+inf) = -inf and -(-inf) = +inf.
;;;   EXT-ADD(x, y)    x + y wherever the sum is defined: +inf when either term is +inf, else -inf when
;;;                    either is -inf, else the real sum.  At the one undefined pair (+inf, -inf) the
;;;                    value is +inf, a CONVENTION: no statement below applies EXT-ADD to that pair.
;;;   EXT-SUB(x, y)    EXT-ADD(x, EXT-NEG(y)): the difference nu+(A) - nu-(A) of Prop 3.12, used only
;;;                    where at least one of the two is finite (the notes' "well-defined").
;;;
;;; SERIES.  Def 3.11 asks that sum_i nu(A_i) CONVERGE to nu(U A_i), conditionally, in the extended
;;; line.  EXT-PARTIAL-SUM(x, n) is the n-th partial sum x(0) + ... + x(n-1) on [-inf, +inf]: +inf
;;; when some term below n is +inf, else -inf when some term below n is -inf, else the real partial
;;; sum SERIES-PARTIAL-SUM.  EXT-SERIES-CONVERGES-TO(x, l) says the partial sums tend to l in
;;; [-inf, +inf]: for a real l they are eventually real and within every eps of l; for l = +inf they
;;; are eventually above every real; for l = -inf eventually below every real.
;;;
;;; IS-SIGNED-MEASURE(omega, ca, nu)   Def 3.11: nu : ca -> [-inf, +inf], nu(empty) = 0, at most one
;;;   of +inf, -inf in the range, and for every pairwise disjoint sequence in ca the series of the
;;;   values converges to the value of the union.  (The notes leave nu(empty) = 0 implicit; it is the
;;;   standard first clause, and countable additivity at the empty sequence forces it.)
;;; POS-VARIATION(ca, nu)   (57): nu+(A) = sup{ nu(E) : E in ca, E subset A }.  The supremum is taken
;;;   in [0, +inf] over the values that lie there; since nu(empty) = 0 is among the values, it is the
;;;   notes' supremum.
;;; SIGNED-NEG(ca, nu)      the signed measure -nu : A |-> -nu(A).
;;; NEG-VARIATION(ca, nu)   (58)/(59): nu-(A) = -inf{ nu(E) : E subset A } = sup{ -nu(E) } = (-nu)+(A).
;;;   Defined by the last form of (59).
;;; TOTAL-VARIATION(ca, nu) Def 3.14: |nu| = nu+ + nu-.
;;; TOTAL-VARIATION-NORM(omega, ca, nu)   Def 3.14: ||nu|| = |nu|(X).

(def-functoid 'EXT-NEG '(enx_)
  '(IF (= enx_ POS-INF) NEG-INF (IF (= enx_ NEG-INF) POS-INF (- enx_))))
(notation! 'EXT-NEG 'kind 'functoid 'arity 1 'english "the negative of $1 in the extended reals")

(def-functoid 'EXT-ADD '(eax_ eay_)
  '(IF (OR (= eax_ POS-INF) (= eay_ POS-INF)) POS-INF
       (IF (OR (= eax_ NEG-INF) (= eay_ NEG-INF)) NEG-INF (+ eax_ eay_))))
(notation! 'EXT-ADD 'kind 'functoid 'arity 2 'english "the extended sum of $1 and $2")

(def-functoid 'EXT-SUB '(esx_ esy_)
  '(EXT-ADD esx_ (EXT-NEG esy_)))
(notation! 'EXT-SUB 'kind 'functoid 'arity 2 'english "the extended difference of $1 and $2")

(def-functoid 'EXT-PARTIAL-SUM '(x n)
  '(IF (FORSOME epk_ (AND (IN epk_ NN) (AND (< epk_ n) (= (x epk_) POS-INF)))) POS-INF
       (IF (FORSOME epk_ (AND (IN epk_ NN) (AND (< epk_ n) (= (x epk_) NEG-INF)))) NEG-INF
           (SERIES-PARTIAL-SUM x n))))
(notation! 'EXT-PARTIAL-SUM 'kind 'functoid 'arity 2
           'english "the $2-th partial sum of the extended series $1")

(def-predicate 'EXT-SERIES-CONVERGES-TO '(x l)
  (conjuncts->and
    (list
      '(IN l RR-STAR)
      '(IMPLIES (IN l RR)
         (FORALL ece_ (IMPLIES (POS-RR ece_)
           (FORSOME ecm_ (AND (IN ecm_ NN)
             (FORALL ecn_ (IMPLIES (IN ecn_ NN) (IMPLIES (<= ecm_ ecn_)
               (AND (IN (EXT-PARTIAL-SUM x ecn_) RR)
                    (< (abs (- (EXT-PARTIAL-SUM x ecn_) l)) ece_))))))))))
      '(IMPLIES (= l POS-INF)
         (FORALL ecb_ (IMPLIES (IN ecb_ RR)
           (FORSOME ecm_ (AND (IN ecm_ NN)
             (FORALL ecn_ (IMPLIES (IN ecn_ NN) (IMPLIES (<= ecm_ ecn_)
               (< ecb_ (EXT-PARTIAL-SUM x ecn_))))))))))
      '(IMPLIES (= l NEG-INF)
         (FORALL ecb_ (IMPLIES (IN ecb_ RR)
           (FORSOME ecm_ (AND (IN ecm_ NN)
             (FORALL ecn_ (IMPLIES (IN ecn_ NN) (IMPLIES (<= ecm_ ecn_)
               (< (EXT-PARTIAL-SUM x ecn_) ecb_))))))))))))
(notation! 'EXT-SERIES-CONVERGES-TO 'kind 'predicate 'arity 2
           'english "the extended series $1 converges to $2")

(def-predicate 'IS-SIGNED-MEASURE '(omega ca nu)
  (conjuncts->and
    (list
      '(IS-SIGMA-ALGEBRA omega ca)
      '(IN nu (FUN ca RR-STAR))
      '(= (nu EMPTY-SET) 0)
      '(NOT (AND (FORSOME sma_ (AND (IN sma_ ca) (= (nu sma_) POS-INF)))
                 (FORSOME smb_ (AND (IN smb_ ca) (= (nu smb_) NEG-INF)))))
      (forall-guarded '(smf_)
                      (list '(IN smf_ (FUN NN ca))
                            (forall-guarded '(smi_ smj_)
                                            '((IN smi_ NN) (IN smj_ NN) (NOT (= smi_ smj_)))
                              '(= (INTERSECTION (smf_ smi_) (smf_ smj_)) EMPTY-SET)))
        '(EXT-SERIES-CONVERGES-TO (VNB-LAMBDA smn_ NN (nu (smf_ smn_)))
                                  (nu (BIG-UNION smn_ NN (smf_ smn_))))))))
(notation! 'IS-SIGNED-MEASURE 'kind 'predicate 'arity 3
           'english "$3 is a countably additive signed measure on the sigma-algebra $2 of subsets of $1")

(def-functoid 'POS-VARIATION '(ca nu)
  '(VNB-LAMBDA pva_ ca
     (ESUP (SEP pvv_ RR-POS-STAR
             (FORSOME pve_ (AND (IN pve_ ca) (AND (SUBSET pve_ pva_) (= (nu pve_) pvv_))))))))
(notation! 'POS-VARIATION 'kind 'functoid 'arity 2 'english "the positive variation of $2")

(def-functoid 'SIGNED-NEG '(ca nu)
  '(VNB-LAMBDA sna_ ca (EXT-NEG (nu sna_))))
(notation! 'SIGNED-NEG 'kind 'functoid 'arity 2 'english "the negative of the signed measure $2")

(def-functoid 'NEG-VARIATION '(ca nu)
  '(POS-VARIATION ca (SIGNED-NEG ca nu)))
(notation! 'NEG-VARIATION 'kind 'functoid 'arity 2 'english "the negative variation of $2")

(def-functoid 'TOTAL-VARIATION '(ca nu)
  '(VNB-LAMBDA tva_ ca (eplus ((POS-VARIATION ca nu) tva_) ((NEG-VARIATION ca nu) tva_))))
(notation! 'TOTAL-VARIATION 'kind 'functoid 'arity 2 'english "the total variation of $2")

(def-functoid 'TOTAL-VARIATION-NORM '(omega ca nu)
  '((TOTAL-VARIATION ca nu) omega))
(notation! 'TOTAL-VARIATION-NORM 'kind 'functoid 'arity 3 'english "the total variation norm of $3")
