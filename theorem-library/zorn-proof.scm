;;; zorn-proof.scm -- proving ZORN'S LEMMA from the well-ordering principle, via
;;; the GREEDY-KEPT-CHAIN construction (avoids the cardinality/Hartogs comparison
;;; lemma the base lacks).  Multi-session build; this file grows as lemmas land.
;;; Started 2026-07-22.
;;;
;;; CONSTRUCTION.  Given a well-ordering phi : ORD-SEGMENT(CARD grd) -> grd of the
;;; ground set, walk the elements in phi-order and KEEP each one that dominates
;;; every element kept so far.  The kept set is a chain; its upper bound (hypo)
;;; is maximal.  Cumulative kept set by transfinite recursion:
;;;   ZKEPT(0)       = {}
;;;   ZKEPT(succ a)  = ZKEPT(a)  U  {phi(a)  if phi(a) dominates all of ZKEPT(a)}
;;;   ZKEPT(lim)     = U_{b<lim} ZKEPT(b)
;;; GREEDY-CHAIN = ZKEPT(CARD grd).
;;; ====================================================================

;;; KEEP-SET(phi, grd, porel, kset, alpha): the conditionally-added element --
;;; {phi(alpha)} if phi(alpha) is in grd and dominates every z in kset, else {}.
;;; (A SEP over grd, so no singleton constructor is needed.)
(def-functoid 'KEEP-SET '(phi grd porel kset alpha)
  '(SEP y grd
     (AND (= y (phi alpha))
          (FORALL z (IMPLIES (IN z kset) (IN (LIST z y) porel))))))

;;; ZKEPT(phi, grd, porel, alpha): the cumulative kept set at stage alpha.
(def-by-ord-recursion 'ZKEPT '(phi grd porel)
  'EMPTY-SET                                        ; ZKEPT(...,0) = {}
  '(alpha val)                                      ; val = ZKEPT(...,alpha)
  '(UNION val (KEEP-SET phi grd porel val alpha))   ; successor step
  '(lam)
  '(BIG-UNION beta (ORD-SEGMENT lam) (ZKEPT phi grd porel beta)))   ; limit step

;;; GREEDY-CHAIN(phi, grd, porel): the full kept chain, ZKEPT at CARD(grd).
(def-functoid 'GREEDY-CHAIN '(phi grd porel)
  '(ZKEPT phi grd porel (CARD grd)))
