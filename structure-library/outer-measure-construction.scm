;;; outer-measure-construction.scm -- METHOD I OUTER MEASURES; null sets,
;;; complete and sigma-finite measures.  Vocabulary only: no proof, no support.
;;; Agent MEASURE-2, 2026-10-08 (scratchpad/triage/MEASURE-2.md).  The proofs are
;;; theorem-library/outer-measure-construction.scm.
;;;
;;; SOURCES.  Thayer, Construction of Measures: Def. 4.6 (pre-measure, p. 32),
;;; Prop. 4.7 / Def. 4.8 (the method I outer measure, Eq. (78), pp. 32-33),
;;; Def. 3.1 (null sets, complete measures, p. 21), Def. 3.6 (sigma-finite, p. 22).
;;;
;;; WHAT AND WHY.
;;;
;;;   * IS-PREMEASURE(omega, cls, pm) -- Def. 4.6: cls a family of subsets of
;;;     omega containing the empty set, pm : cls -> [0, +inf] with pm(empty) = 0.
;;;     The notes leave the ambient set X implicit (C subset of P(X)); it is a
;;;     parameter here, in the argument order of measure.scm.
;;;
;;;   * COVER-SUMS(omega, cls, pm, es) -- the SET of the numbers of which Eq. (78)
;;;     takes the infimum: the sums ESUM_n pm(A_n) over the sequences A in
;;;     FUN(NN, cls) whose union covers es.  It is a SEP over RR-POS-STAR, so it
;;;     is a set of extended reals and EINF applies to it directly.  "A sequence"
;;;     is a function on NN, repetitions allowed, as everywhere in the measure
;;;     files (sigma-algebra.scm, COUNTABLE); ESUM is the unordered sum of
;;;     extended-sum.scm.
;;;
;;;   * METHOD-I-OUTER(omega, cls, pm) -- Def. 4.8: the function on POWER(omega)
;;;     whose value at es is EINF(COVER-SUMS(omega, cls, pm, es)).  The notes'
;;;     convention "if there are no covering sequences, mu*(E) = +inf" is not a
;;;     clause: it is the value EINF gives the empty set (the lower bounds of the
;;;     empty set are all of [0, +inf], whose supremum is POS-INF).
;;;
;;;   * IS-NULL-SET(omega, ca, mu, ns) -- Def. 3.1: ns lies inside some member of
;;;     ca of measure 0.  The definition does not ask that mu be a measure; every
;;;     statement that uses it carries IS-MEASURE as its own hypothesis.
;;;
;;;   * IS-COMPLETE-MEASURE(omega, ca, mu) -- Def. 3.1, last sentence: a measure
;;;     whose null sets all belong to ca.
;;;
;;;   * IS-SIGMA-FINITE(omega, ca, mu) -- Def. 3.6: omega is the union of a
;;;     sequence of members of ca of finite measure ("finite" is membership in
;;;     RR, the form measure-laws.scm uses).  IS-MEASURE is not a conjunct, as
;;;     the brief decided; statements carry it beside.
;;;
;;; NOT DEFINED: the completion of a measure as an object (Def. 3.3, Prop. 3.3).
;;; Prop. 4.12 is stated as the membership it amounts to (every measurable set is
;;; A u N with A in ca and N null), which needs no new object.
;;;
;;; Binder names carry a `cv' / `nl' / `sf' prefix: a set, IOTA or lambda built by
;;; a driver must use binders nothing else binds (CLAUDE.md), and `es', `ns' avoid
;;; the case-fold of E / N (`nn' is NN).
;;; ====================================================================

(def-predicate 'IS-PREMEASURE '(omega cls pm)
  (conjuncts->and
    (list
      '(IN omega SET)
      '(SUBSET cls (POWER omega))
      '(IN EMPTY-SET cls)
      '(IN pm (FUN cls RR-POS-STAR))
      '(= (pm EMPTY-SET) 0))))

(notation! 'IS-PREMEASURE 'kind 'predicate 'arity 3
           'english "$3 is a pre-measure on the family $2 of subsets of $1")

(def-functoid 'COVER-SUMS '(omega cls pm es)
  '(SEP cvv_ RR-POS-STAR
     (FORSOME cvs_
       (AND (IN cvs_ (FUN NN cls))
            (AND (SUBSET es (BIG-UNION cvn_ NN (cvs_ cvn_)))
                 (= cvv_ (ESUM (VNB-LAMBDA cvk_ NN (pm (cvs_ cvk_))))))))))

(notation! 'COVER-SUMS 'kind 'functoid 'arity 4
           'english "the set of sums of $3 over the sequences in $2 covering $4")

(def-functoid 'METHOD-I-OUTER '(omega cls pm)
  '(VNB-LAMBDA cve_ (POWER omega) (EINF (COVER-SUMS omega cls pm cve_))))

(notation! 'METHOD-I-OUTER 'kind 'functoid 'arity 3
           'english "the method I outer measure on $1 of the pre-measure $3 on $2")

(def-predicate 'IS-NULL-SET '(omega ca mu ns)
  '(FORSOME nla_ (AND (IN nla_ ca) (AND (SUBSET ns nla_) (= (mu nla_) 0)))))

(notation! 'IS-NULL-SET 'kind 'predicate 'arity 4
           'english "$4 is a null set of the measure $3 on $2")

(def-predicate 'IS-COMPLETE-MEASURE '(omega ca mu)
  (conjuncts->and
    (list
      '(IS-MEASURE omega ca mu)
      '(FORALL nls_ (IMPLIES (IS-NULL-SET omega ca mu nls_) (IN nls_ ca))))))

(notation! 'IS-COMPLETE-MEASURE 'kind 'predicate 'arity 3
           'english "$3 is a complete measure on the sigma-algebra $2 of subsets of $1")

(def-predicate 'IS-SIGMA-FINITE '(omega ca mu)
  '(FORSOME sff_
     (AND (IN sff_ (FUN NN ca))
          (AND (FORALL sfn_ (IMPLIES (IN sfn_ NN) (IN (mu (sff_ sfn_)) RR)))
               (= (BIG-UNION sfk_ NN (sff_ sfk_)) omega)))))

(notation! 'IS-SIGMA-FINITE 'kind 'predicate 'arity 3
           'english "$3 is sigma-finite on the sigma-algebra $2 of subsets of $1")

;;; =====================================================================
;;; LEBESGUE OUTER MEASURE ON THE LINE, as an instance (the brief's item 6).
;;;
;;;   * CLOSED-INTERVALS -- the covering family C of the notes' construction of
;;;     Lebesgue measure: the empty set and the closed intervals CCINT(a, b),
;;;     a <= b real.  A SEP over POWER(RR), so it is a set.
;;;   * INTERVAL-LENGTH(s) -- the length of a set of reals read off the set,
;;;     without the sup and inf of RR: the supremum in [0, +inf] of the
;;;     differences y - x, x <= y in s (and of 0, so that the empty set has length
;;;     0).  This is the diameter of s; on CCINT(a, b), a <= b, it is b - a
;;;     (interval-length-ccint).  It is total on all sets of reals, which makes the
;;;     pre-measure (VNB-LAMBDA s CLOSED-INTERVALS (INTERVAL-LENGTH s)) a function
;;;     on C with no well-definedness obligation (the representation of an
;;;     interval by its endpoints is never used to define it).
;;; The pre-measure and the outer measure are written out in the statements --
;;; METHOD-I-OUTER(RR, CLOSED-INTERVALS, VNB-LAMBDA s CLOSED-INTERVALS
;;; (INTERVAL-LENGTH s)) -- rather than named: a function-valued constant does not
;;; unfold in applied position (cc-coords-laws.scm), and a functoid cannot be
;;; parameterless.
;;; =====================================================================

(def-constant 'CLOSED-INTERVALS
  (list 'closed-intervals-def
        '(== CLOSED-INTERVALS
             (SEP oci_ (POWER RR)
               (OR (= oci_ EMPTY-SET)
                   (FORSOME oca_ (AND (IN oca_ RR)
                     (FORSOME ocb_ (AND (IN ocb_ RR) (AND (<= oca_ ocb_) (= oci_ (CCINT oca_ ocb_))))))))))))

(notation! 'CLOSED-INTERVALS 'english "the family of the empty set and the closed intervals of the real line")

(def-functoid 'INTERVAL-LENGTH '(s)
  '(ESUP (SEP odv_ RR-POS-STAR
           (OR (= odv_ 0)
               (FORSOME odx_ (AND (IN odx_ s)
                 (FORSOME ody_ (AND (IN ody_ s) (AND (<= odx_ ody_) (= odv_ (- ody_ odx_)))))))))))

(notation! 'INTERVAL-LENGTH 'kind 'functoid 'arity 1
           'english "the length (diameter) of the set of reals $1")
