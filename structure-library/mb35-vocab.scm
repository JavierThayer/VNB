;;; mb35-vocab.scm -- vocabulary for construction of measures, chapter 5 section 2 (M-B35, 2026-10-26).
;;; Destination: structure-library/.  Library: measure.
;;;
;;;   IS-REGULAR-MEASURE(s, mu)  Definition 5.48: mu is a finite measure on the Borel sets of s and every Borel
;;;                              set E has mu(E) = sup{ mu(K) : K subset E, K compact }  (K compact: the
;;;                              subspace on K is a compact metric space)
;;;
;;; NBGSEP (2026-10-28): the compact rgk_ is bounded explicitly by rgk_ in POWER(PTS s), so the
;;; separation is predicative (NBG).  rgk_ subset rge_, a Borel set, already gives it: the meaning
;;; is unchanged.
;;; Load window: after the measure vocabulary (IS-MEASURE, BOREL-SETS), ESUP and IS-COMPACT.
(def-predicate 'IS-REGULAR-MEASURE '(s mu)
  '(AND (IS-MEASURE (PTS s) (BOREL-SETS s) mu)
        (AND (IN (mu (PTS s)) RR)
             (FORALL rge_ (IMPLIES (IN rge_ (BOREL-SETS s))
               (= (mu rge_) (ESUP (SEP rgv_ RR-POS-STAR (FORSOME rgk_ (AND (IN rgk_ (POWER (PTS s)))
                  (AND (SUBSET rgk_ rge_)
                  (AND (IS-COMPACT (SUBSPACE-MS s rgk_)) (= rgv_ (mu rgk_))))))))))))))
(notation! 'IS-REGULAR-MEASURE 'kind 'predicate 'arity 2 'english "$2 is a regular measure on $1")
