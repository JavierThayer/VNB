;;; ba-bh2-vocab.scm -- wave of 2026-11-09/10 (agent BA-BH2), wired 2026-11-10 from scratchpad/babh2-1109/ba-bh2-vocab.scm.
;;; Library: operator-algebras.

;;; ba-bh2-vocab.scm -- THE NORMED GROUP AND THE METRIC SPACE OF THE BOUNDED OPERATORS v -> w.
;;; DEFINITIONS ONLY: no proof, no support, no axiom.
;;; Agent BA-BH2, wave 2026-11-09.  Destination: structure-library/ba-bh2-vocab.scm.
;;; Library: operator-algebras (with ba-ops-vocab.scm).
;;; Load window: after structure-library/ba-ops-vocab (BOUNDED-OPS, BOP-SUM, BOP-ZERO, BOP-NEG,
;;; OPNORM) and structure-library/normed-ag (NAG-METRIC-SPACE).
;;;
;;; BOP-NORMED-AG(v, w) is the 5-tuple [L(v, w), +, 0, -, ||.||] in NORMED-AG's slots
;;; constructions of ba-ops-vocab.scm, with ba-ops-vocab's binders (bos_ bot_), so that at
;;; w = v each unfolds to exactly the term BH-VADD(v), BH-VNEG(v), BH-VNRM(v) unfolds to.
(def-functoid 'BOP-VADD '(bov_ bow_)
  '(VNB-LAMBDA (LIST bos_ bot_) (CARTESIAN (BOUNDED-OPS bov_ bow_) (BOUNDED-OPS bov_ bow_))
     (BOP-SUM bov_ bow_ bos_ bot_)))
(def-functoid 'BOP-VINV '(bov_ bow_)
  '(VNB-LAMBDA bot_ (BOUNDED-OPS bov_ bow_) (BOP-NEG bov_ bow_ bot_)))
(def-functoid 'BOP-VNRM '(bov_ bow_)
  '(VNB-LAMBDA bot_ (BOUNDED-OPS bov_ bow_) (OPNORM bov_ bow_ bot_)))
(def-functoid 'BOP-NORMED-AG '(bov_ bow_)
  '(LIST (BOUNDED-OPS bov_ bow_) (BOP-VADD bov_ bow_) (BOP-ZERO bov_ bow_) (BOP-VINV bov_ bow_)
         (BOP-VNRM bov_ bow_)))

(notation! 'BOP-NORMED-AG 'kind 'functoid 'arity 2
           'english "the normed group of bounded operators from $1 to $2")
