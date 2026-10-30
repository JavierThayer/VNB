;;; ca-line-vocab.scm -- WAVE 2 (2026-10-27..30), wired 2026-10-30 from scratchpad/ch3e/ch3f-line.scm (vocab), scratchpad/ch3e/ch3f-refl.scm (vocab).
;;; Library: complex-analysis.
;;; Proof-free: the definitions (with their notation! lines) moved here from the proof file(s) named above.

(def-functoid 'CC-LINE '(clnp_ clnd_)
  '(SEP clnz_ CC (= (imag-part (* (- clnz_ clnp_) (conjugate clnd_))) 0)))
(notation! 'CC-LINE 'kind 'functoid 'arity 2 'english "the straight line through $1 in the direction $2")

;;; ---- from ch3e/ch3f-refl.scm
(def-functoid 'CONJ-SET '(cjsa_) '(SEP cjsz_ CC (IN (conjugate cjsz_) cjsa_)))
(notation! 'CONJ-SET 'kind 'functoid 'arity 1 'english "the set of complex conjugates of the elements of $1")
