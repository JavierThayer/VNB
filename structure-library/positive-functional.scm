;;; structure-library/positive-functional.scm -- continuous real functions on a
;;; metric space, positive linear functionals on them, clopen sets.  DEFINITIONS
;;; ONLY (Riesz-Markov, stage 2, RM-2, 2026-10-10); the laws are PROVEN in
;;; theorem-library/riesz-markov-cantor.scm (prefix rmc-).
;;;
;;; Source: the user's notes-63 (2026-10-10), form (b).  The vocabulary is stated
;;; for ANY metric space s: stage 3 (RM-3) uses it on the compact space X itself.
;;;
;;;   CONT-FNS(s)       the set of the continuous functions PTS s -> RR (continuity
;;;                     into RR-MS, structure-library/metric-continuity.scm).  The
;;;                     pointwise sum and the scalar multiple are written as lambdas,
;;;                       (VNB-LAMBDA sx_ (PTS s) (+ (f sx_) (g sx_)))
;;;                       (VNB-LAMBDA sx_ (PTS s) (* c (f sx_))),
;;;                     literally the terms of rintegral-add / rintegral-scale
;;;                     (theorem-library/real-integral.scm, omega = PTS s), so that a
;;;                     law of the functional and a law of the integral speak of the
;;;                     same function.  Closure of CONT-FNS under both is a theorem
;;;                     (rmc-cont-fns-add, rmc-cont-fns-scale); no vector-space
;;;                     structure is declared.
;;;   IS-POSITIVE-FUNCTIONAL(s, lam)
;;;                     lam : CONT-FNS(s) -> RR is additive, real-homogeneous, and
;;;                     lam(g) >= 0 whenever g >= 0 at every point.
;;;   CLOPEN-SETS(s)    the subsets of PTS s that are both open and closed (a SEP
;;;                     over POWER(PTS s), hence a set).  On a compact space they
;;;                     form the algebra of sets on which a positive functional
;;;                     defines a content: u |-> lam(INDICATOR(PTS s, u))
;;;                     (theorem-library/riesz-markov-cantor.scm writes that content
;;;                     out; INDICATOR is measure vocabulary and this file is analysis).
;;;
;;; BINDERS end in an underscore and start with the definition's letters (cf, pf);
;;; `sx_' is the binder of real-integral.scm's pointwise lambdas, kept on purpose.
;;;
;;; Dependencies: metric-continuity (IS-CONTINUOUS), metric-open-sets (IS-OPEN,
;;; IS-CLOSED), numeric-instances (RR-MS).  Library: analysis.

(def-functoid 'CONT-FNS '(s)
  '(SEP cfh_ (FUN (PTS s) RR) (IS-CONTINUOUS s RR-MS cfh_)))

(def-predicate 'IS-POSITIVE-FUNCTIONAL '(s lam)
  (conjuncts->and
    (list
      '(IN lam (FUN (CONT-FNS s) RR))
      '(FORALL pff_ (IMPLIES (IN pff_ (CONT-FNS s))
         (FORALL pfg_ (IMPLIES (IN pfg_ (CONT-FNS s))
           (= (lam (VNB-LAMBDA sx_ (PTS s) (+ (pff_ sx_) (pfg_ sx_))))
              (+ (lam pff_) (lam pfg_)))))))
      '(FORALL pfc_ (IMPLIES (IN pfc_ RR)
         (FORALL pff_ (IMPLIES (IN pff_ (CONT-FNS s))
           (= (lam (VNB-LAMBDA sx_ (PTS s) (* pfc_ (pff_ sx_))))
              (* pfc_ (lam pff_)))))))
      '(FORALL pff_ (IMPLIES (IN pff_ (CONT-FNS s))
         (IMPLIES (FORALL pfx_ (IMPLIES (IN pfx_ (PTS s)) (<= 0 (pff_ pfx_))))
                  (<= 0 (lam pff_))))))))

(def-functoid 'CLOPEN-SETS '(s)
  '(SEP cou_ (POWER (PTS s)) (AND (IS-OPEN s cou_) (IS-CLOSED s cou_))))

(notation! 'CONT-FNS 'kind 'functoid 'arity 1
           'english "the set of continuous real functions on $1")
(notation! 'IS-POSITIVE-FUNCTIONAL 'kind 'predicate 'arity 2
           'english "$2 is a positive linear functional on the continuous real functions on $1")
(notation! 'CLOPEN-SETS 'kind 'functoid 'arity 1
           'english "the family of the subsets of $1 that are open and closed")
