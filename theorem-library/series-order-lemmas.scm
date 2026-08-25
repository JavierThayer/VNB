;;; series-order-lemmas.scm -- order facts about real partial sums and limits.
;;;
;;; These are the infinite-sum half of the inequality suite -- needed regardless
;;; of the linear-arithmetic oracle (which is finite/linear).  Its keystone was
;;; monotone-convergence on RR, which comparison-test (power-series.scm) cites
;;; by name; that one is now PROVEN and lives in
;;; theorem-library/monotone-convergence-proof.scm (see the note below), and so
;;; are the two partial-sum ORDER facts this file used to assert -- they moved
;;; to theorem-library/comparison-test-proof.scm with comparison-test itself.
;;; NOTHING REMAINS.  The last entry, the Cauchy criterion, was proven and
;;; moved on 2026-08-22 (see the end of this file); every note below records
;;; where a retired support went and why it could not stay.  The file installs
;;; nothing and is kept for that record.
;;;
;;; Real sequence vars are f, g (NOT `a' -> the carrier accessor, `A' when this
;;; was written, `CARR' now); index n_ / m (NOT `n'
;;; alone where it could fold with N); a bound is bnd; eps as usual.  Loads after
;;; power-series (SERIES-PARTIAL-SUM / SERIES-CONVERGES) and order-lemmas.
;;;
;;; Library-build phase: warranted well-known [[feedback-library-axioms-fine]].
;;; Dependencies: power-series.scm (SERIES-PARTIAL-SUM, SERIES-CONVERGES),
;;; metric-completeness.scm (CONVERGES), numeric-instances.scm (RR-MS),
;;; order-predicates.scm (POS-RR, <), number-systems.scm (RR, <=, abs).

;;; -----------------------------------------------------------------------
;; monotone-convergence-rr MOVED 2026-08-20 to
;; theorem-library/monotone-convergence-proof.scm, where it is PROVEN -- along
;; with the monotone lift `nn-monotone-step-implies-le' it needs -- billing
;; `modulo {nn-zero-le, nn-le-succ-cases}' [trust: well-known], i.e. resting on
;; nothing but the two NN-order supports of structure-library/order-lemmas.scm.
;; It was a `well-known' support here, and the warrant's eps-N sketch is exactly
;; the route the proof takes (sup of the range, then rr-sup-approx).  The proof
;; loads LATE -- after theorem-library/rr-sup-approx, which did not exist when
;; this file was written -- and nothing in the tree cites the name in between.

;;; -----------------------------------------------------------------------
;;; Partial-sum monotonicity.
;;
;; series-partial-sum-monotone-nonneg and series-partial-sum-le-termwise MOVED
;; 2026-08-20 to theorem-library/comparison-test-proof.scm, where both are
;; PROVEN `modulo 0' -- along with comparison-test itself (power-series.scm),
;; which named all three as the ingredients it was waiting on.  Both were
;; `well-known' supports here and both warrants named the SUM-AG recurrence as
;; the route; that recurrence is now on the surface as `series-partial-sum-succ'
;; (SERIES-PARTIAL-SUM(f,succ k) == SERIES-PARTIAL-SUM(f,k) + f(k)), after which
;; each is one `ineq' -- the first with no induction at all, the second with one.
;; The proofs load LATE, after theorem-library/monotone-convergence-proof, which
;; did not exist when this file was written; nothing in the tree cites either
;; name in between.

;;; -----------------------------------------------------------------------
;;; Series triangle inequality: |sum| <= sum of |.|.
;;;
;;; RETIRED as a support 2026-08-21 and PROVEN, at the end of
;;; theorem-library/comparison-test-proof.scm.  It cannot live here: the proof
;;; needs `rr-abs-triangle-c' (rr-abs-basics, load.scm:583), the partial-sum
;;; recurrence and `abs-seq-in-fun' (comparison-test-proof, load.scm:1392), all
;;; of which load after this file.  Nothing cited it in between -- checked --
;;; so the move costs no bill.
;;;
;;; The statement changed in ONE respect: `k' is quantified FIRST, ahead of `f'.
;;; `ni' tests the goal's SHAPE, literally (FORALL n (IMPLIES (IN n NN) body)),
;;; so the induction variable has to be outermost or the induction cannot be
;;; started at all (CLAUDE.md's induction lane).  A citation therefore takes its
;;; arguments as (fact 'series-partial-sum-abs-le k f), not the other way round.

;;; -----------------------------------------------------------------------
;;; Cauchy criterion for real series: convergence => tails vanish.
;;;
;;; RETIRED as a support 2026-08-22 and PROVEN, in
;;; theorem-library/series-cauchy-proof.scm, `modulo 0'.  It was the LAST live
;;; entry of this file, which is now history only and installs nothing.
;;;
;;; It cannot live here.  The proof unfolds SERIES-CONVERGES to a named limit
;;; and then needs `rr-pos-halvable' (rr-halving, load.scm:624), `rr-abs-bound'
;;; / `rr-le-abs' / `rr-neg-abs-le' (rr-abs-basics, load.scm:583), `rr-ms-dist'
;;; (load.scm:886) and `series-partial-sum-in-rr' /
;;; `series-partial-sum-seq-apply' (comparison-test-proof, load.scm:1392) --
;;; every one of them BELOW this file.  The proof therefore sits immediately
;;; after comparison-test-proof and immediately BEFORE
;;; theorem-library/dominated-convergence, which is the only file in the tree
;;; that cites the name (`series-tail-small'); nothing between this file and
;;; that one cites it, so the move costs no bill.
;;;
;;; The statement was carried over BYTE-IDENTICAL -- checked, not assumed:
;;; installing the proof under the old name reports "re-installing the same
;;; statement", which is the warning install-theorem! prints when the two agree,
;;; rather than the "already installed with a DIFFERENT statement" one.
