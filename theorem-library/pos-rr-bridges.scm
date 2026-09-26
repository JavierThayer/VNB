;;; pos-rr-bridges.scm -- the two projections of POS-RR, and one more
;;; positivity fact, PROVEN modulo 0.
;;;
;;;     rr-pos-rr-in-rr:          POS-RR(t)  =>  t in RR
;;;     rr-lt-of-pos-rr:          POS-RR(t)  =>  0 < t
;;;     rr-one-plus-nonneg-pos:   d in RR,  0 <= d  =>  0 < 1 + d
;;;
;;; WHY.  POS-RR is `(AND (IN r RR) (AND (<= 0 r) (NOT (= 0 r))))'
;;; (structure-library/order-predicates.scm) and `<' is the same pair of
;;; conjuncts, so both projections are one unfold each.  The other direction,
;;; 0 < x => POS-RR(x), is `rr-pos-rr-of-lt' (theorem-library/pos-rr-of-lt),
;;; and its header measured that until it was written NO theorem in the
;;; library CONCLUDED a POS-RR.  These two are the mirror gap: every driver
;;; that received a POS-RR(d) -- from rr-pos-halvable, rr-min-pos, rr-pos-shrink,
;;; a continuity delta -- and needed `d in RR' or `0 < d' unfolded it with
;;; `mac-h', which REPLACES the assumption, and so had to order the unfold after
;;; every `inst+' that still wanted POS-RR(d) intact (cont-agree-off-pt.scm,
;;; continuous-one-sided-sign.scm and rr-le-all-pos.scm each carry a comment
;;; about exactly that).  A CITATION lands the projection and leaves the
;;; hypothesis alone.  `dk-halve!' (driver-kit.scm) is built on these two.
;;;
;;; LOAD SLOT: right after theorem-library/rr-order-basics (load.scm:684).  The
;;; file cites nothing from it -- the floor is driver-kit (dk-peel!,
;;; dk-split-all!, ineq!) plus the primitive number-systems axioms and the
;;; order-predicates definitions -- but the order-basics shelf is where a reader
;;; looks for a fact of this size, and every file that will cite these
;;; (rr-order-bundle and the other rr-pos-halvable consumers) loads well below.

;;; ====================================================================
;;; rr-pos-rr-in-rr:  POS-RR(t)  =>  t in RR
;;; ====================================================================
(sp (make-wff '(FORALL t (IMPLIES (POS-RR t) (IN t RR)))))
(dk-peel!)
(mac-h 'pos-rr '(POS-RR t))
(dk-split-all!)
(ass)
(qed 'rr-pos-rr-in-rr)
(topic! 'rr-pos-rr-in-rr 'inequalities)
(alias! 'rr-pos-rr-in-rr "a POS-RR is a real")

;;; ====================================================================
;;; rr-lt-of-pos-rr:  POS-RR(t)  =>  0 < t
;;; ====================================================================
(sp (make-wff '(FORALL t (IMPLIES (POS-RR t) (< 0 t)))))
(dk-peel!)
(mac-h 'pos-rr '(POS-RR t))
(dk-split-all!)
(mac '<)
(dk-conj-close!)
(qed 'rr-lt-of-pos-rr)
(topic! 'rr-lt-of-pos-rr 'inequalities)
(alias! 'rr-lt-of-pos-rr "a POS-RR is strictly positive")

;;; ====================================================================
;;; rr-one-plus-nonneg-pos:  d in RR, 0 <= d  =>  0 < 1 + d
;;; ====================================================================
;;; Linear in the one atom d, which the peeled typing certifies; `ineq!'
;;; selects the usable order premise itself.
(sp (make-wff '(FORALL d (IMPLIES (IN d RR) (IMPLIES (<= 0 d) (< 0 (+ 1 d)))))))
(dk-peel!)
(ineq!)
(qed 'rr-one-plus-nonneg-pos)
(topic! 'rr-one-plus-nonneg-pos 'inequalities)
