;;; mb35-souslin-vocab.scm -- vocabulary for construction of measures, chapter 5 section 1.3-1.4: sieves and
;;; Souslin sets (M-B35 / B5, 2026-10-26).  Destination: structure-library/.  Library: measure.
;;;
;;;   NSTAR                     N*, the finite sequences of naturals: the functions ORD-SEGMENT(n) -> NN
;;;   IS-SIEVE(s, sv)           Definition 5.4: sv : N* -> subsets of X with, along every z in N^N
;;;                             (= FUN(NN, NN)), the diameter property diam S_{z|n} -> 0, monotonicity
;;;                             S_{z|n+1} subset S_{z|n}, and the intersection property (some point in every
;;;                             S_{z|n}); z|n is RESTRICT(z, ORD-SEGMENT(n))
;;;   SOUSLIN-SET(s, sv)        the Souslin operation: the union over z in N^N of the intersections of the S_{z|n}
;;;   IS-SOUSLIN(s, e)          Definition 5.7: e is the Souslin set of some sieve
;;;   IS-BAIRE-CONTINUOUS(s, f) f : N^N -> X is continuous for the product topology of N^N: at every z, for every
;;;                             eps > 0 some n has d(f(z), f(w)) <= eps whenever w|n = z|n (the cylinders
;;;                             {w : w|n = z|n} are a neighbourhood base of z)
;;;
;;; Load window: after mb4-vocab (DIAM), the RESTRICT and ORD-SEGMENT vocabulary.
(def-constant 'NSTAR
  (list 'nstar-def '(== NSTAR (BIG-UNION nsk_ NN (FUN (ORD-SEGMENT nsk_) NN)))))
(notation! 'NSTAR 'kind 'constant 'arity 0 'english "the finite sequences of naturals")
(def-predicate 'IS-SIEVE '(s sv)
  '(AND (IN sv (FUN NSTAR (POWER (PTS s))))
        (FORALL svz_ (IMPLIES (IN svz_ (FUN NN NN))
          (AND (FORALL sve_ (IMPLIES (POS-RR sve_) (FORSOME svb_ (AND (IN svb_ NN)
                 (FORALL svn_ (IMPLIES (IN svn_ NN) (IMPLIES (<= svb_ svn_)
                   (<= (DIAM s (sv (RESTRICT svz_ (ORD-SEGMENT svn_)))) sve_))))))))
               (AND (FORALL svn_ (IMPLIES (IN svn_ NN)
                      (SUBSET (sv (RESTRICT svz_ (ORD-SEGMENT (succ svn_)))) (sv (RESTRICT svz_ (ORD-SEGMENT svn_))))))
                    (FORSOME svp_ (AND (IN svp_ SET)
                      (FORALL svn_ (IMPLIES (IN svn_ NN) (IN svp_ (sv (RESTRICT svz_ (ORD-SEGMENT svn_))))))))))))))
;;; W1 (2026-11-04): svp_ is bounded by SET (it is a member of a class), so that IS-SIEVE is
;;; predicative where a comprehension condition names IS-SOUSLIN.  The former definiens is the
;;; proven `is-sieve-classes' (theorem-library/mb35-souslin.scm).
(notation! 'IS-SIEVE 'kind 'predicate 'arity 2 'english "$2 is a sieve of subsets of $1")
(def-functoid 'SOUSLIN-SET '(s sv)
  '(SEP sxp_ (PTS s) (FORSOME sxz_ (AND (IN sxz_ (FUN NN NN))
     (FORALL sxn_ (IMPLIES (IN sxn_ NN) (IN sxp_ (sv (RESTRICT sxz_ (ORD-SEGMENT sxn_))))))))))
(notation! 'SOUSLIN-SET 'kind 'functoid 'arity 2 'english "the Souslin set of the sieve $2 in $1")
(def-predicate 'IS-SOUSLIN '(s e)
  '(FORSOME ssv_ (AND (IS-SIEVE s ssv_) (= (SOUSLIN-SET s ssv_) e))))
(notation! 'IS-SOUSLIN 'kind 'predicate 'arity 2 'english "$2 is a Souslin subset of $1")
(def-predicate 'IS-BAIRE-CONTINUOUS '(s f)
  '(AND (IN f (FUN (FUN NN NN) (PTS s)))
        (FORALL bcz_ (IMPLIES (IN bcz_ (FUN NN NN)) (FORALL bce_ (IMPLIES (POS-RR bce_)
          (FORSOME bcn_ (AND (IN bcn_ NN) (FORALL bcw_ (IMPLIES (IN bcw_ (FUN NN NN))
            (IMPLIES (= (RESTRICT bcw_ (ORD-SEGMENT bcn_)) (RESTRICT bcz_ (ORD-SEGMENT bcn_)))
              (<= ((DIST s) (f bcz_) (f bcw_)) bce_))))))))))))
(notation! 'IS-BAIRE-CONTINUOUS 'kind 'predicate 'arity 2 'english "$2 is a continuous map from N^N to $1")
