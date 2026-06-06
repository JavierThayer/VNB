;;; scratch-ordself.scm -- ord-segment-self:  n in NN => n not in ORD-SEGMENT(n).
;;; Probe: does `mac` work on the biconditional axioms ord-segment-membership
;;; and ord-lt-iff?  Needed for caseA's  n not in ORD-SEGMENT(k)  step.
(load "load.scm")

(sp (make-wff '(FORALL n (IMPLIES (IN n NN) (NOT (IN n (ORD-SEGMENT n)))))))
(define nv (eigen-name 'n *fresh-counter*))
(di)                       ; intro n, assume n in NN
(display "--- after di ---\n") (show)

;;; n in ORD  (ord-segment-membership side condition)
(ta 'nn-subset-ord)
(inst '(FORALL n (IMPLIES (IN n NN) (IN n ORD))) nv)
(cut `(IN ,nv ORD))
(define use-ord (last-node))
  (bc `(IMPLIES (IN ,nv NN) (IN ,nv ORD)))
  (ass)
(refocus! use-ord)
(display "--- n in ORD established ---\n") (show)

(mac 'ord-segment-membership)   ; (IN n os(n)) -> (<_ORD n n) ?
(display "--- after mac ord-segment-membership ---\n") (show)
(mac 'ord-lt-iff)               ; (<_ORD n n) -> (AND (<=_ORD n n) (NOT (= n n))) ?
(display "--- after mac ord-lt-iff ---\n") (show)
(di)                            ; assume the AND, goal FALSITY
(ai `(AND (<=_ORD ,nv ,nv) (NOT (= ,nv ,nv))))
(cut `(= ,nv ,nv))
(define use-eq (last-node))
  (rfl)
(refocus! use-eq)
(ai `(NOT (= ,nv ,nv)))         ; not-elim: (= n n) in context -> closes FALSITY
(display "--- FINAL ---\n") (show)
