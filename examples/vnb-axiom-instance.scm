;;; vnb-axiom-instance.scm
;;;
;;; Title:    Instantiating a VNB axiom
;;; Goal:     "a in b implies a in SET"
;;;
;;; Demonstrates: pulling a named axiom into context (ta), specialising it
;;; to particular terms (inst), then closing the goal by backchaining (bc).

(sp (make-wff-from-string "a in b implies a in SET"))
(di)
(ta 'membership-implies-sethood)
(inst "forall([a, b], a in b implies a in set)" 'a)
(inst "forall([b], a in b implies a in set)" 'b)
(bc "a in b implies a in set")
(ass)
