;;; ba-quotient-vocab.scm -- wave of 2026-11-09/10 (agent BA-1C), wired 2026-11-10 from scratchpad/ba1c-1109/ba-quotient-vocab.scm.
;;; Library: operator-algebras.

;;; ba-quotient-vocab.scm -- BANACH ALGEBRAS: the quotient norm (Thayer, 1.11).
;;; QUOT-NORM(a, i, x) = inf { ||x - y|| : y in i }, the norm of the coset x + i in A/i.
;;; Read as an EINF over RR-POS-STAR, as SPECTRAL-RADIUS is (ba-vocab).
;;; Agent BA-1C, wave 2026-11-09.  Destination: structure-library/ba-quotient-vocab.scm.
;;; Library: operator-algebras.  No proof in this file.  Binders: bqq*_, used by no other file.
;;; LOAD WINDOW: after structure-library/ba-vocab.

(def-functoid 'QUOT-NORM '(bqqa_ bqqi_ bqqx_)
  '(EINF (SEP bqqw_ RR (FORSOME bqqy_ (AND (IN bqqy_ bqqi_)
           (= bqqw_ ((VNRM bqqa_) ((VADD bqqa_) bqqx_ ((VNEG bqqa_) bqqy_)))))))))
(notation! 'QUOT-NORM 'kind 'functoid 'arity 3 'english "the norm of the coset of $3 modulo $2 in $1")
