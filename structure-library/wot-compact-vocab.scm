;;; wot-compact-vocab.scm -- agent BA-1117-TRACE (round 2), 2026-11-17.
;;; THE UNIT BALL OF L(H): the bounded operators of operator norm at most 1 (BanachAlgebras.pdf
;;; Proposition 5.10).  DEFINITIONS ONLY: no proof, no support, no axiom.
;;; Destination: structure-library/wot-compact-vocab.scm.  Library: operator-algebras.
;;; Load window: after structure-library/ba-ops-vocab (BOUNDED-OPS, OPNORM).
(def-functoid 'OP-UNIT-BALL '(wuv_)
  '(SEP wub_ (BOUNDED-OPS wuv_ wuv_) (<= (OPNORM wuv_ wuv_ wub_) 1)))
(notation! 'OP-UNIT-BALL 'kind 'functoid 'arity 1
  'english "the unit ball of L($1): the bounded operators of norm at most 1")
