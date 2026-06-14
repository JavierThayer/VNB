;;; summable-cauchy.scm -- the telescoping bridge: a metric-space sequence whose
;;; consecutive distances are bounded by a SUMMABLE real series is Cauchy (and,
;;; in a complete space, converges).  This is the second leg of the completeness
;;; argument sketched in metric-completeness.scm (cauchy-rapid-subsequence is the
;;; first): rapidly-Cauchy subsequence + summation + diagonalization.
;;;
;;; The hypothesis "the consecutive-distance bound is summable" is stated with
;;; SERIES-CONVERGES (power-series.scm) on the real bound sequence rad, which is
;;; why this file loads after power-series.  Bound var is `rad', NOT `a' (case-
;;; folds to the carrier accessor A).
;;;
;;; Library-build phase: warranted well-known, no proof attempted
;;; [[feedback-pss-over-proof-slog]] [[project-metric-completion]].
;;;
;;; Dependencies: metric-completeness.scm (IS-CAUCHY-SEQ, CONVERGES, IS-COMPLETE,
;;; IS-METRIC-SPACE, X, D), power-series.scm (SERIES-CONVERGES), numeric-
;;; instances.scm (RR, RR-MS).

;;; -----------------------------------------------------------------------
;;; summable-bound-implies-cauchy: in ANY metric space, if d(f_k, f_{k+1}) <=
;;; rad(k) for all k and the real series sum_k rad(k) converges, then f is
;;; Cauchy.  (No completeness needed -- pure telescoping.)
(support 'summable-bound-implies-cauchy
  '(FORALL s (FORALL f (FORALL rad
     (IMPLIES (AND (IS-METRIC-SPACE s)
              (AND (IN f (FUN NN (X s)))
              (AND (IN rad (FUN NN RR))
              (AND (SERIES-CONVERGES rad)
                   (FORALL k (IMPLIES (IN k NN)
                     (<= ((D s) (f k) (f (succ k))) (rad k))))))))
       (IS-CAUCHY-SEQ s f))))))
(warrant! 'summable-bound-implies-cauchy 'well-known
  "Telescoping.  For m <= n the triangle inequality gives
   d(f m, f n) <= sum_{k=m}^{n-1} d(f k, f(succ k)) <= sum_{k=m}^{n-1} rad(k)
   = P(n) - P(m), where P is the partial-sum sequence of rad.  SERIES-CONVERGES
   says P converges in RR, hence P is Cauchy: for eps>0 there is N with
   P(n)-P(m) < eps whenever n > m >= N.  So d(f m, f n) < eps there, i.e. f is
   Cauchy.  Needs no completeness of s.")

;;; -----------------------------------------------------------------------
;;; summable-bound-converges: the complete-space payoff -- same hypothesis,
;;; plus completeness, gives convergence.  (summable-bound-implies-cauchy +
;;; complete-cauchy-converges.)
(support 'summable-bound-converges
  '(FORALL s (FORALL f (FORALL rad
     (IMPLIES (AND (IS-COMPLETE s)
              (AND (IN f (FUN NN (X s)))
              (AND (IN rad (FUN NN RR))
              (AND (SERIES-CONVERGES rad)
                   (FORALL k (IMPLIES (IN k NN)
                     (<= ((D s) (f k) (f (succ k))) (rad k))))))))
       (CONVERGES s f))))))
(warrant! 'summable-bound-converges 'well-known
  "summable-bound-implies-cauchy makes f Cauchy (IS-COMPLETE carries IS-METRIC-
   SPACE), and complete-cauchy-converges then gives a limit in s.")
