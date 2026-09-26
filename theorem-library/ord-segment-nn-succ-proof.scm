;;; ord-segment-nn-succ-proof.scm -- the NN-flavoured ORD-SEGMENT successor
;;; characterisation, proven from three ordinal primitives.
;;;
;;;     forall n, k.  n in NN  =>
;;;         ( k in ORD-SEGMENT(succ n)  iff  k in ORD-SEGMENT(n) or k = n )
;;;
;;; The support of the same name lives in theorem-library/ord-segment-nn-succ.scm
;;; (a PSS-promoted stub; its archived script predates the E->IDEN rename).
;;; This file is named `-proof' only because that stub holds the name.
;;;
;;; PLAN (all three citations are `primitive', structure-library/ordinals.scm):
;;;   nn-subset-ord    n in NN => n in ORD          -- the guard ord-segment-succ wants
;;;   ord-succ-nn      n in NN => succ_ORD n = succ n  -- rewrite the goal's succ n
;;;   ord-segment-succ alpha in ORD => forall x. x in OS(succ_ORD alpha) iff ...
;;; instantiated at alpha := n, x := k, and the goal is that instance.  The
;;; archived script went through the `informal' support succ-nn-ord instead;
;;; ord-succ-nn is the same equation the other way round, so it is not needed.
;;;
;;; WINDOW.  lo = any theorem-library slot after driver-kit / proof-debt (the
;;; three primitives load with structure-library/ordinals).  hi = theorem-
;;; library/pigeonhole-segments, the earliest `mac' of ord-segment-nn-succ
;;; (founder-warrants only re-warrants it).
;;;
;;; Helper prefix: osn- (none needed).

(sp (make-wff '(FORALL n (FORALL k (IMPLIES (IN n NN)
       (IFF (IN k (ORD-SEGMENT (succ n)))
            (OR (IN k (ORD-SEGMENT n)) (= k n))))))))
(dk-peel-to! 'IFF)                     ; lands (IN n NN); goal is the IFF.  One `di'
                                       ; peels only the two FORALLs: the guard sits
                                       ; under FORALL k, so it is not read as a guard
(fact 'nn-subset-ord 'n)               ; (IN n ORD)
(fact 'ord-succ-nn 'n)                 ; (= (succ_ORD n) (succ n))
(subst '(= (succ n) (succ_ORD n)))     ; goal now reads ORD-SEGMENT(succ_ORD n)
(fact 'ord-segment-succ 'n 'k)         ; the IFF at alpha := n, x := k
(ass)
(qed 'ord-segment-nn-succ)
(topic! 'ord-segment-nn-succ 'plumbing)
