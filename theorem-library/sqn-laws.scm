;;; sqn-laws.scm -- the two SQN facts that structure-library/sqn.scm used to STAMP
;;; `definitional', proven here from the definition (the user, 2026-11-13: "Why is
;;; this a definition and not an axiom?" -- neither: each is a consequence).
;;;
;;; The definition of SQN is the def-functoid SQN(a) := FUN(NN, a) (sqn.scm).
;;; * sqn-membership is its unfold under IN.  It must exist as a THEOREM, because
;;;   `mac-h' cannot unfold a functoid in an assumption by the functoid's own name
;;;   (CLAUDE.md, "Where a definition lives"); 25 call sites fire it by name.
;;; * sqn-sethood follows from the primitive `fun-set-iff' (library.scm) at NN and
;;;   `nn-is-set' (number-systems.scm).
;;; Both bill modulo 0, as the stamps did, so no citer's bill changes; the stamps had
;;; made the two facts invisible to the ledger.

(sp (make-wff '(FORALL a (FORALL f_ (IFF (IN f_ (SQN a)) (IN f_ (FUN NN a)))))))
(di)
(mac 'SQN)
(prop)
(qed 'sqn-membership)

(sp (make-wff '(FORALL a (IMPLIES (IN a SET) (IN (SQN a) SET)))))
(di)
(mac 'SQN)
(let ((sqnl-a (caddr (cadr (dk-goal)))))      ; goal (IN (FUN NN a') SET): read a' off it
  (fact 'fun-set-iff 'NN sqnl-a))
(fact 'nn-is-set)
(prop)
(qed 'sqn-sethood)
