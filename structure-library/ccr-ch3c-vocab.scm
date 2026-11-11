;;; ccr-ch3c-vocab.scm -- wave of 2026-11-09/10 (agent CCR-1109-B3), wired 2026-11-10 from scratchpad/ccr1109b3/ccr-ch3c-vocab.scm.
;;; Library: analysis.

;;; ccr-ch3c-vocab.scm -- CCR.pdf chapter 3, third pass: the definitions the limit argument of Lemma 3.4
;;; needs.  DEFINITIONS ONLY; the laws are in theorem-library/ccr-ch3c-*.scm.  Agent CCR-1109-B3, wave
;;; 2026-11-09.  Destination: structure-library/ccr-ch3c-vocab.scm.  Library: analysis (FNRM, as
;;; ccr-ch3-vocab).
;;;
;;; THE MODEL is that of ccr-ch3-vocab: K a normed field, matrices MAT(m, n, CARR K).  The max norm enters
;;; only through bounds, so ||A - B||_max <= e is given as a predicate on the pair, entrywise; no matrix
;;; subtraction is needed:
;;;
;;;   IS-MAT-CLOSE(K, m, n, A, B, e)   A and B are m-by-n matrices over K with |a_ij - b_ij| <= e for every
;;;                                    entry, i.e. ||A - B||_max <= e.
;;;
;;; Load window: after structure-library/ccr-ch3-vocab (beside it).  Binders cdv*_.  No axiom, support or
;;; stamp.

(def-predicate 'IS-MAT-CLOSE '(K m n A B e)
  '(AND (IN A (MAT m n (CARR K)))
   (AND (IN B (MAT m n (CARR K)))
        (FORALL cdvi_ (IMPLIES (IN cdvi_ (INTERVAL 1 m))
          (FORALL cdvj_ (IMPLIES (IN cdvj_ (INTERVAL 1 n))
            (<= ((FNRM K) ((ADD K) (ENTRY A cdvi_ cdvj_) ((NEG K) (ENTRY B cdvi_ cdvj_)))) e))))))))
(notation! 'IS-MAT-CLOSE 'kind 'predicate 'arity 6
           'english "$4 and $5 are $2-by-$3 matrices over $1 with max norm of the difference at most $6")
