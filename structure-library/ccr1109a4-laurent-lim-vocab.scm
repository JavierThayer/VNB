;;; ccr1109a4-laurent-lim-vocab.scm -- wave of 2026-11-09/10 (agent CCR-1109-A4), wired 2026-11-10 from scratchpad/ccr1109a4/ccr1109a4-laurent-lim-vocab.scm.
;;; Library: analysis.

;;; ccr1109a4-laurent-lim-vocab.scm -- the limit of a coefficientwise-stabilising sequence of formal Laurent series.
;;; DEFINITIONS ONLY.  Agent CCR-1109-A4, 2026-11-09.  Destination: structure-library/ccr1109a4-laurent-lim-vocab.scm.
;;; Library: algebra (it names only LAURENT-SET's carrier and NN).  Load window: after ccr1109a3-laurent-vocab.
;;;
;;; LAURENT-LIMC(K, s, j) is the EVENTUAL VALUE of the coefficients s_n(j): the unique c in CARR(K) with
;;; s_n(j) = c for all n past some M (an IOTA; it denotes when the coefficients at j settle, which a Cauchy
;;; sequence of K((x)) guarantees).  LAURENT-LIM(K, s) is the series j |-> LAURENT-LIMC(K, s, j).
;;; Binders ll*_.

(def-functoid 'LAURENT-LIMC '(llk_ lls_ llj_)
  '(IOTA llc_ (AND (IN llc_ (CARR llk_))
     (FORSOME llm_ (AND (IN llm_ NN) (FORALL lln_ (IMPLIES (IN lln_ NN) (IMPLIES (<= llm_ lln_) (= ((lls_ lln_) llj_) llc_)))))))))
(notation! 'LAURENT-LIMC 'kind 'functoid 'arity 3 'english "the eventual value of the coefficients at $3 of the sequence $2")

(def-functoid 'LAURENT-LIM '(llk_ lls_) '(VNB-LAMBDA llj_ ZZ (LAURENT-LIMC llk_ lls_ llj_)))
(notation! 'LAURENT-LIM 'kind 'functoid 'arity 2 'english "the coefficientwise limit of the sequence $2 of Laurent series")

;;; The polynomials x^0 .. x^(m-1) with coefficients in K, as Laurent series: the functions ZZ -> CARR(K) that
;;; vanish below 0 and from m on.  For a FINITE K these form a finite set (theorem-library ccr1109a4: induction on
;;; m, each P_(m+1) inside the image of P_m x CARR(K) under LAURENT-EXT); they are the finite nets that make
;;; K[[x]] totally bounded.  LAURENT-EXT(K, m) sends (p, c) to p + c x^m.
(def-functoid 'LAURENT-POLYS '(llk_ llm_)
  '(SEP llg_ (FUN ZZ (CARR llk_))
     (AND (FORALL llj_ (IMPLIES (IN llj_ ZZ) (IMPLIES (< llj_ 0) (= (llg_ llj_) (ZERO llk_)))))
          (FORALL llj_ (IMPLIES (IN llj_ ZZ) (IMPLIES (<= llm_ llj_) (= (llg_ llj_) (ZERO llk_))))))))
(notation! 'LAURENT-POLYS 'kind 'functoid 'arity 2 'english "the polynomials over $1 of degree below $2")

(def-functoid 'LAURENT-EXT '(llk_ llm_)
  '(VNB-LAMBDA llw_ (CARTESIAN (LAURENT-POLYS llk_ llm_) (CARR llk_))
     (LAURENT-ADD llk_ (NTH 1 llw_) (LAURENT-MONO llk_ (NTH 2 llw_) llm_))))
(notation! 'LAURENT-EXT 'kind 'functoid 'arity 2 'english "the map (p, c) |-> p + c x^$2 on the polynomials of degree below $2")
