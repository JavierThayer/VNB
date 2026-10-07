;;; nn-cancel.scm -- CANCELLATION ON NN, proven in the core (2026-10-07).
;;;
;;;   nn-add-cancel   a, b, c in NN,  a + c = b + c  =>  a = b
;;;   nn-mul-cancel   a, b, c in NN,  c /= 0,  a*c = b*c  =>  a = b
;;;
;;; Both were proven before: nn-add-cancel in cancellation.scm by restriction from
;;; ZZ (zz-add-cancel, the additive group of ZZ-RING), nn-mul-cancel in
;;; nn-integral.scm through ZZ as an integral domain (zz-mul-cancel-zero).  Those
;;; routes made two NN facts cited from core files (nn-pairing, nn-mod3-proof) rest
;;; on the algebra book, the last two violations of the library gate.  NN inherits
;;; its arithmetic from RR (number-systems.scm), so the facts are one citation each
;;; over RR: linear arithmetic for the sum, rr-cancel-mul-right for the product.
;;; Statements UNCHANGED from the two sites.  Loads after rr-order-basics and before
;;; nn-integral (whose nn-2-cancel cites nn-mul-cancel) and nn-mod3-proof.

(sp (make-wff '(FORALL a (IMPLIES (IN a NN)
                 (FORALL b (IMPLIES (IN b NN)
                   (FORALL c (IMPLIES (IN c NN)
                     (IMPLIES (= (+ a c) (+ b c)) (= a b))))))))))
(dk-peel!)
(let loop () (when (dk-head-is? (dk-goal) 'IMPLIES) (di) (loop)))
(fact 'nn-in-rr 'a)
(fact 'nn-in-rr 'b)
(fact 'nn-in-rr 'c)
(dk-ineq! '(IN a RR) '(IN b RR) '(IN c RR) '(= (+ a c) (+ b c)))
(qed 'nn-add-cancel)
(topic! 'nn-add-cancel 'inequalities)

(sp (make-wff '(FORALL a (IMPLIES (IN a NN)
                 (FORALL b (IMPLIES (IN b NN)
                   (FORALL c (IMPLIES (IN c NN)
                     (IMPLIES (NOT (= c 0))
                       (IMPLIES (= (* a c) (* b c)) (= a b)))))))))))
(dk-peel!)
(let loop () (when (dk-head-is? (dk-goal) 'IMPLIES) (di) (loop)))
(fact 'nn-in-rr 'a)
(fact 'nn-in-rr 'b)
(fact 'nn-in-rr 'c)
(fact 'rr-cancel-mul-right 'a 'b 'c)      ; u, v, c in RR; c /= 0; u*c = v*c  =>  u = v
(ass)
(qed 'nn-mul-cancel)
(topic! 'nn-mul-cancel 'inequalities)
