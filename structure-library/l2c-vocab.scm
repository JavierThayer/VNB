;;; l2c-vocab.scm -- wave of 2026-11-09/10 (agent TH3-L2), wired 2026-11-10 from scratchpad/th3-1109/l2/l2c-vocab.scm.
;;; Library: measure.

;;; l2c-vocab.scm -- COMPLEX L^2 AS A HILBERT SPACE (TH3-L2, 2026-11-09).  Vocabulary only.
;;;
;;; THE DESIGN (the user's, 2026-10-18, scratchpad/triage/SIP-1.md): a complex space is a REAL
;;; semi-inner-product space with a complex structure J; the spaces of integrable functions are
;;; SETOIDS with equality almost everywhere as the relation.
;;;
;;; CL2-HILBERT(omega, cA, mu) is the complexification of the real Hilbert space L^2 modulo
;;; null functions:  CSIP-CIPS(COMPLEXIFY(SIP-QUOTIENT(L2-SPACE(omega, cA, mu)))).
;;; Its vectors are PAIRS [CLASS u, CLASS v] of a.e.-classes of real square-integrable
;;; functions, read as u + i v; J is multiplication by i, J[u, v] = [-v, u]; the complex form is
;;;     <[u1, u2], [v1, v2]> = (int u1 v1 + int u2 v2) + i (int u2 v1 - int u1 v2)
;;;                          = int (u1 + i u2) conj(v1 + i v2).
;;; WHY THIS ORDER (complexify AFTER the quotient): completeness is then two citations,
;;; l2-quotient-is-real-hilbert (theorem-library/l2-hilbert.scm) and complexify-hilbert
;;; (theorem-library/sip-d1.scm).  The other order, CSIP-QUOTIENT(CL2-SPACE) (classes of
;;; pairs, sip-c.scm's cl2-quotient-is-cips), has no completeness theorem and would need either
;;; a second Riesz-Fischer argument or an isometric isomorphism onto this space.
;;;
;;; LOAD WINDOW: after theorem-library/l2-hilbert (and so after sip-d1, sip-l2-vocab).
;;; Library: measure (L2-SPACE is measure vocabulary).

(def-functoid 'CL2-HILBERT '(omega cA mu)
  '(CSIP-CIPS (COMPLEXIFY (SIP-QUOTIENT (L2-SPACE omega cA mu)))))

(notation! 'CL2-HILBERT 'kind 'functoid 'arity 3
           'english "the complex Hilbert space L^2 of $3 on $1" 'tex "L^2_{\\mathbb{C}}({$1}, {$3})")
