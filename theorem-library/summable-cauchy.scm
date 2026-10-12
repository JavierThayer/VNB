;;; summable-cauchy.scm -- the telescoping bridge: a metric-space sequence whose
;;; consecutive distances are bounded by a SUMMABLE real series is Cauchy (and,
;;; in a complete space, converges).  This is the second leg of the completeness
;;; argument sketched in metric-completeness.scm (cauchy-rapid-subsequence is the
;;; first): rapidly-Cauchy subsequence + summation + diagonalization.
;;;
;;; The hypothesis "the consecutive-distance bound is summable" is stated with
;;; SERIES-CONVERGES (power-series.scm) on the real bound sequence rad, which is
;;; why this file loads after power-series.  Bound var is `rad', NOT `a' (case-
;;; folds to the carrier accessor, `A' when this was written, `CARR' now).
;;;
;;; Library-build phase: warranted well-known, no proof attempted
;;; [[feedback-pss-over-proof-slog]] [[project-metric-completion]].
;;;
;;; Dependencies: metric-completeness.scm (IS-CAUCHY-SEQ, CONVERGES, IS-COMPLETE,
;;; IS-METRIC-SPACE, PTS, DIST), power-series.scm (SERIES-CONVERGES), numeric-
;;; instances.scm (RR, RR-MS).

;;; -----------------------------------------------------------------------
;;; summable-bound-implies-cauchy: in ANY metric space, if d(f_k, f_{k+1}) <=
;;; rad(k) for all k and the real series sum_k rad(k) converges, then f is
;;; Cauchy.  (No completeness needed -- pure telescoping.)
;;; summable-bound-implies-cauchy RETIRED 2026-09-18 (rake batch 5c): proven in theorem-library/rake-series2.scm

;;; -----------------------------------------------------------------------
;;; summable-bound-converges: the complete-space payoff -- same hypothesis,
;;; plus completeness, gives convergence.  (summable-bound-implies-cauchy +
;;; complete-cauchy-converges.)
;;; summable-bound-converges RAKE-ASM-B2 2026-10-12: PROVEN in theorem-library/rake-asm-b2.scm under this name; the assumption is retired.
