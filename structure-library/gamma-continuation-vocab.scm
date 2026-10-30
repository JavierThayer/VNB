;;; gamma-continuation-vocab.scm -- WAVE 2 (2026-10-27..30), wired 2026-10-30 from scratchpad/ch3g/ch3g-gamma.scm (vocab).
;;; Library: complex-analysis.
;;; Proof-free: the definitions (with their notation! lines) moved here from the proof file(s) named above.

(def-by-nn-recursion 'POCH '(pcz_)
  1
  '(pcn_ pcv_)
  '(* pcv_ (+ pcz_ pcn_)))
(notation! 'POCH 'kind 'functoid 'arity 2 'english "the rising factorial of $1 of length $2")
(def-functoid 'GAMMA-EXT '(gez_)
  '(* (GAMMA-FUNCTION (+ gez_ (CHOICE (SEP gek_ NN (< 0 (+ (real-part gez_) gek_))))))
      (recip (POCH gez_ (CHOICE (SEP gek_ NN (< 0 (+ (real-part gez_) gek_))))))))
(notation! 'GAMMA-EXT 'kind 'functoid 'arity 1
           'english "the analytic continuation of the Gamma function at $1")
