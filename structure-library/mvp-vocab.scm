;;; mvp-vocab.scm -- WAVE 2 (2026-10-27..30), wired 2026-10-30 from scratchpad/calint2/mvp-vocab.scm.
;;; Library: complex-analysis.

;;; mvp-vocab.scm -- complex-analysis Definition 3.54 (CAL-INT-2, 2026-10-28).  Destination: structure-library/.
;;; HAS-MEAN-VALUE-PROPERTY(u, f): f is a continuous complex function on the open set u, and
;;;   f(c) = 1/(2 pi) int_0^{2 pi} f(c + r e^{it}) dt     (the notes' (92))
;;; for every c and r > 0 with the CLOSED disc CLOSURE(B(c, r)) inside u.
;;; Library: complex-analysis.  Load window: after path-integral (CC-INT) and baire-category (CLOSURE).
(def-predicate 'HAS-MEAN-VALUE-PROPERTY '(mvu_ mvf_)
  (conjuncts->and
    (list '(IS-OPEN (NF-METRIC-SPACE CC-NORMED-FIELD) mvu_)
          '(IN mvf_ (FUN mvu_ CC))
          '(FORALL rgy_ (IMPLIES (IN rgy_ mvu_)
             (IS-CONTINUOUS-AT (SUBSPACE-MS (NF-METRIC-SPACE CC-NORMED-FIELD) mvu_) (NF-METRIC-SPACE CC-NORMED-FIELD) mvf_ rgy_)))
          '(FORALL mvc_ (IMPLIES (IN mvc_ CC) (FORALL mvr_ (IMPLIES (IN mvr_ RR) (IMPLIES (< 0 mvr_)
             (IMPLIES (SUBSET (CLOSURE CC-MS (BALL CC-MS mvc_ mvr_)) mvu_)
               (= (mvf_ mvc_)
                  (* (recip (* 2 PI))
                     (CC-INT (VNB-LAMBDA mvt_ (CCINT 0 (* 2 PI)) (mvf_ (+ mvc_ (* mvr_ (CC-EXP (* +i mvt_)))))) 0 (* 2 PI)))))))))))))
(notation! 'HAS-MEAN-VALUE-PROPERTY 'kind 'predicate 'arity 2
           'english "$2 has the mean value property on $1")
