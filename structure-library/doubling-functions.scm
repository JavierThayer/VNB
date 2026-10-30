;;; doubling-functions.scm -- WAVE 2 (2026-10-27..30), wired 2026-10-30 from scratchpad/mf/mf-mivocab.scm.
;;; Library: measure.

;;; mf-mivocab.scm -- bounded equivalence of gauge functions (construction-of-measures.pdf ch. 4, Def 4.43):
;;; DEFINITIONS ONLY.  Agent M-F (target M-I), 2026-10-29 (NEW DEFINITION, the user's to confirm).
;;; DESTINATION: structure-library/doubling-functions.scm.  Library: measure.
;;; Load window: after structure-library/hausdorff-vocab.scm (NNREAL, IS-DOUBLING).
;;;
;;; IS-BOUNDEDLY-EQUIVALENT(phi, psi)   Def 4.43 with r0 = +inf: phi, psi : [0, +inf) -> [0, +inf) and there are
;;;   positive constants c, C with c phi(r) <= psi(r) <= C phi(r) for every real r > 0.

(def-predicate 'IS-BOUNDEDLY-EQUIVALENT '(phi psi)
  '(AND (IN phi (FUN NNREAL NNREAL))
     (AND (IN psi (FUN NNREAL NNREAL))
       (FORSOME bel_ (FORSOME beu_
         (AND (POS-RR bel_) (AND (POS-RR beu_)
           (FORALL ber_ (IMPLIES (IN ber_ RR) (IMPLIES (< 0 ber_)
             (AND (<= (* bel_ (phi ber_)) (psi ber_)) (<= (psi ber_) (* beu_ (phi ber_))))))))))))))
(notation! 'IS-BOUNDEDLY-EQUIVALENT 'kind 'predicate 'arity 2
           'english "$1 and $2 are boundedly equivalent on [0, +oo)")
