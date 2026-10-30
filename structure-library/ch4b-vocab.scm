;;; ch4b-vocab.scm -- WAVE 2 (2026-10-27..30), wired 2026-10-30 from scratchpad/ch4b/ch4b-vocab.scm.
;;; Library: complex-analysis.

;;; ch4b-vocab.scm -- complex-analysis 4.2-4.3 (meromorphic functions, residues): vocabulary (CH4-B, 2026-10-29).
;;; Destination: structure-library/.  Library: complex-analysis.  Load window: after ch4a-vocab (none of its
;;; heads is used here), diff-on (HOLOMORPHIC-ON), metric balls, path-integral (LINE-INT, CIRCLE-PATH, TRACE).
;;; B(a, r) is BALL(CC-MS, a, r); the punctured ball is DIFFERENCE(B(a, r), SINGLETON(a)).
;;;
;;; IS-MEROMORPHIC-AT(f, a)   f is meromorphic at a (Def 4.9): on some punctured ball about a,
;;;                           f(z) = (1/(z - a))^N g(z) with N in NN and g holomorphic on the ball.  N = 0 covers
;;;                           "analytic at a" and "removable singularity"; N >= 1 with g(a) /= 0 is a pole.
;;; IS-POLE(f, a, N)          f has a pole of order N at a (Def 4.7, in the form (112) gives right after it):
;;;                           N >= 1 and f(z) = (1/(z - a))^N g(z) on a punctured ball, g holomorphic, g(a) /= 0.
;;;                           The equivalence with the Laurent-series form of Def 4.7 is a theorem (ch4b files).
;;; IS-REMOVABLE-SINGULARITY(f, a)   f agrees on a punctured ball about a with a function holomorphic on the ball.
;;; IS-ESSENTIAL-SINGULARITY(f, a)   neither a removable singularity nor a pole.
;;; MEROMORPHIC-ON(U, f)      Def 4.9, second form: U open, and for some A subset U, f is holomorphic on U \ A and
;;;                           has a removable singularity or a pole at each point of A.
;;; RESIDUE(f, a)             Def 4.14, read as the circle integral that equals c_-1 (Prop 4.2): THE complex x with
;;;                           x = 1/(2 pi i) int_{|w - a| = rho} f(w) dw for every rho in some interval (0, r).
(def-predicate 'IS-MEROMORPHIC-AT '(mrf_ mra_)
  '(AND (IN mra_ CC)
        (FORSOME mrn_ (AND (IN mrn_ NN)
          (FORSOME mrr_ (AND (IN mrr_ RR) (AND (< 0 mrr_)
            (FORSOME mrg_ (AND (HOLOMORPHIC-ON (BALL CC-MS mra_ mrr_) mrg_)
              (FORALL mrz_ (IMPLIES (IN mrz_ (DIFFERENCE (BALL CC-MS mra_ mrr_) (SINGLETON mra_)))
                (= (mrf_ mrz_) (* (power (recip (- mrz_ mra_)) mrn_) (mrg_ mrz_))))))))))))))
(notation! 'IS-MEROMORPHIC-AT 'kind 'predicate 'arity 2 'english "$1 is meromorphic at $2")
(def-predicate 'IS-POLE '(mrf_ mra_ mrn_)
  '(AND (IN mra_ CC) (AND (IN mrn_ NN) (AND (<= 1 mrn_)
          (FORSOME mrr_ (AND (IN mrr_ RR) (AND (< 0 mrr_)
            (FORSOME mrg_ (AND (HOLOMORPHIC-ON (BALL CC-MS mra_ mrr_) mrg_) (AND (NOT (= (mrg_ mra_) 0))
              (FORALL mrz_ (IMPLIES (IN mrz_ (DIFFERENCE (BALL CC-MS mra_ mrr_) (SINGLETON mra_)))
                (= (mrf_ mrz_) (* (power (recip (- mrz_ mra_)) mrn_) (mrg_ mrz_)))))))))))))))
(notation! 'IS-POLE 'kind 'predicate 'arity 3 'english "$1 has a pole of order $3 at $2")
(def-predicate 'IS-REMOVABLE-SINGULARITY '(mrf_ mra_)
  '(AND (IN mra_ CC)
          (FORSOME mrr_ (AND (IN mrr_ RR) (AND (< 0 mrr_)
            (FORSOME mrg_ (AND (HOLOMORPHIC-ON (BALL CC-MS mra_ mrr_) mrg_)
              (FORALL mrz_ (IMPLIES (IN mrz_ (DIFFERENCE (BALL CC-MS mra_ mrr_) (SINGLETON mra_)))
                (= (mrf_ mrz_) (mrg_ mrz_)))))))))))
(notation! 'IS-REMOVABLE-SINGULARITY 'kind 'predicate 'arity 2 'english "$1 has a removable singularity at $2")
(def-predicate 'IS-ESSENTIAL-SINGULARITY '(mrf_ mra_)
  '(AND (IN mra_ CC) (AND (NOT (IS-REMOVABLE-SINGULARITY mrf_ mra_)) (NOT (FORSOME mrn_ (IS-POLE mrf_ mra_ mrn_))))))
(notation! 'IS-ESSENTIAL-SINGULARITY 'kind 'predicate 'arity 2 'english "$1 has an essential singularity at $2")
(def-predicate 'MEROMORPHIC-ON '(mru_ mrf_)
  '(AND (IS-OPEN (NF-METRIC-SPACE CC-NORMED-FIELD) mru_)
        (FORSOME mrs_ (AND (SUBSET mrs_ mru_) (AND (HOLOMORPHIC-ON (DIFFERENCE mru_ mrs_) mrf_)
          (FORALL mrx_ (IMPLIES (IN mrx_ mrs_)
            (OR (IS-REMOVABLE-SINGULARITY mrf_ mrx_) (FORSOME mrn_ (IS-POLE mrf_ mrx_ mrn_))))))))))
(notation! 'MEROMORPHIC-ON 'kind 'predicate 'arity 2 'english "$2 is meromorphic on $1")
(def-functoid 'RESIDUE '(mrf_ mra_)
  '(IOTA mrx_ (AND (IN mrx_ CC)
     (FORSOME mrr_ (AND (IN mrr_ RR) (AND (< 0 mrr_)
       (FORALL mrp_ (IMPLIES (IN mrp_ RR) (IMPLIES (< 0 mrp_) (IMPLIES (< mrp_ mrr_)
         (= mrx_ (* (recip (* (* 2 PI) +i))
                    (LINE-INT (VNB-LAMBDA mrw_ (TRACE (CIRCLE-PATH mra_ mrp_) 0 (* 2 PI)) (mrf_ mrw_))
                              (CIRCLE-PATH mra_ mrp_) (CIRCLE-DERIV mra_ mrp_) 0 (* 2 PI))))))))))))))
(notation! 'RESIDUE 'kind 'functoid 'arity 2 'english "the residue of $1 at $2")
