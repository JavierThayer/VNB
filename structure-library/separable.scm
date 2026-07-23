;;; separable.scm -- separability of a metric space (a dense sequence) and the
;;; bridge  compact => separable.  Vocabulary + STATEMENT; proof deferred (see
;;; the effort note).  Added 2026-07-22 for the Ascoli-Arzelà arc.
;;;
;;; A metric space is SEPARABLE iff it has a countable dense subset; for a metric
;;; space this is equivalent to having a DENSE SEQUENCE dseq : NN -> PTS(s)
;;; (every ball meets its range).  We take the dense-sequence form: it is exactly
;;; what Ascoli's diagonal argument consumes, and it sidesteps a standalone
;;; IS-COUNTABLE (which the base does not have).
;;;
;;; EFFORT NOTE (why WARRANTED, not proved).  compact => totally bounded
;;; (compact-iff-tb-complete) => for each n a finite (1/(n+1))-net F_n; the union
;;; U_n F_n is a countable dense set.  A machine proof needs (a) a choice
;;; function n |-> F_n selecting a net per scale and (b) an ENUMERATION of the
;;; countable union of finite sets as one NN-sequence.  The base has no
;;; countable-union / NN x NN pairing machinery, so (b) is a moderate build, NOT
;;; the minor effort the go/no-go gate asked for -- stated as a usable support,
;;; with the enumeration machinery flagged as the obstacle.
;;;
;;; Loads after compactness (IS-COMPACT, compact-iff-tb-complete) and metric-
;;; topology (TOTALLY-BOUNDED / IS-R-NET), before the Ascoli statement that
;;; rests on it.  Binder dseq (NOT e -- avoids the numeric constant %e / e).
;;; ====================================================================

(define (sep-all  v cond body) `(FORALL  ,v (IMPLIES ,cond ,body)))
(define (sep-some v cond body) `(FORSOME ,v (AND     ,cond ,body)))

;;; IS-SEPARABLE(s): s is a metric space carrying a dense sequence
;;; dseq : NN -> PTS(s) -- every point is approximated to arbitrary precision by
;;; some dseq(n).
(def-predicate 'IS-SEPARABLE '(s)
  (conjuncts->and
    (list
      '(IS-METRIC-SPACE s)
      (sep-some 'dseq '(IN dseq (FUN NN (PTS s)))
        (sep-all 'x '(IN x (PTS s))
          (sep-all 'eps '(POS-RR eps)
            (sep-some 'n '(IN n NN)
              '(< ((DIST s) x (dseq n)) eps))))))))

;;; compact-metric-is-separable: a compact metric space is separable.  (IS-COMPACT
;;; already carries IS-METRIC-SPACE.)  The bridge Ascoli-Arzelà needs.
(support 'compact-metric-is-separable
  '(FORALL s (IMPLIES (IS-COMPACT s) (IS-SEPARABLE s))))
(warrant! 'compact-metric-is-separable 'reference
  '(thayer-calc "compact metric => separable (union of finite 1/n-nets)"))
(gloss! 'compact-metric-is-separable
  "A compact metric space is separable: it has a dense sequence.  Proof route:
   compact => totally bounded (compact-iff-tb-complete), so for each n in NN there
   is a FINITE (1/(n+1))-net F_n (TOTALLY-BOUNDED at r = 1/(n+1)); the union
   D = U_n F_n is countable, and it is dense because for any point x and tolerance
   eps, choosing n with 1/(n+1) < eps puts some center of F_n within eps of x.
   Enumerating D as a single NN-sequence is the countable-union-of-finite-sets step
   the base cannot yet mechanize (no NN x NN pairing / countable-union machinery),
   which is why this is asserted rather than proved.")
(category! 'compact-metric-is-separable 'topology)

;; The proven/asserted engine this rests on: compact => totally bounded.  (The
;; countable-union enumeration is the content that is NOT yet a separate support.)
(rests-on 'compact-metric-is-separable '(compact-iff-tb-complete))
