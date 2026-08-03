;;; interval-widen.scm -- an interval membership survives widening the top end.
;;;
;;;     i in INTERVAL(a,b),  b <= c   =>   i in INTERVAL(a,c)
;;;
;;; Three read-offs and one transitivity.  It exists because of the beta guard:
;;; a driver that reduces a summand lambda of domain [1,succ n] at an index w
;;; introduced from [1,n] -- span-bricks2-proof's peel and snoc both do -- has
;;; to carry w across the two intervals first, and did not, so the reduction was
;;; off-domain.  Four sites want the step, so it is a lemma and not four copies.
;;;
;;; Proven, not asserted: interval-elt-in-nn / interval-lo / interval-hi are the
;;; forward read-offs of interval-membership, interval-mem-intro its converse,
;;; and nn-le-trans the transitivity, all in order-lemmas.scm.

(define (iw-goal) (wff-formula (sequent-node-assertion (proof-state-focus *ps*))))
(define (iw-di*)                          ; di is greedy; peel to a fixed point
  (let lp () (let* ((g (iw-goal)) (h (and (pair? g) (car g))))
               (when (memq h '(FORALL IMPLIES)) (di) (lp)))))

(sp (make-wff
  '(FORALL a (FORALL b (FORALL c (FORALL i
     (IMPLIES (IN i (INTERVAL a b))
       (IMPLIES (<= b c)
         (IN i (INTERVAL a c))))))))))
(iw-di*)
(fact 'interval-elt-in-nn 'a 'b 'i)       ; i in NN
(fact 'interval-lo 'a 'b 'i)              ; a <= i
(fact 'interval-hi 'a 'b 'i)              ; i <= b
(fact 'nn-le-trans 'i 'b 'c)              ; i <= b <= c
(fact 'interval-mem-intro 'a 'c 'i)
(ass)
(qed 'interval-widen)
(category! 'interval-widen 'inequalities)
