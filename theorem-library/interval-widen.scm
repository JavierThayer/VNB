;;; interval-widen.scm -- an interval membership survives widening the top end.
;;;
;;;     i in INTERVAL(a,b),  b <= c   =>   i in INTERVAL(a,c)
;;;
;;; Three read-offs and one transitivity.  It exists because of the beta guard:
;;; a driver that reduces a summand lambda of domain [1,succ n] at an index w
;;; introduced from [1,n] -- span-bricks2-proof's peel and snoc both do -- has
;;; to carry w across the two intervals first, and did not, so the reduction was
;;; off-domain.  Two sites want the step, so it is a lemma and not two copies.
;;;
;;; GUARDED ON BOTH b AND c, 2026-08-03, and the guards are not decoration.
;;; Transitivity of <= on NN is `nn-le-trans-guarded', which rightly demands
;;; that every term it chains through be a natural -- and NOTHING else in this
;;; statement types b or c: `i <= b' says nothing about b, `b <= c' nothing
;;; about c.  The first version leaned on the UNGUARDED nn-le-trans and so
;;; chained through two untyped terms, which is exactly the defect that
;;; migration was retiring.  Written in the morning, caught the same afternoon
;;; by the migration that removed the crutch.  Both call sites pass b := n and
;;; c := succ n, with both typings already in context.
;;;
;;; Proven, not asserted: interval-elt-in-nn / interval-lo / interval-hi are the
;;; forward read-offs of INTERVAL's definition (theorem-library/interval-basics),
;;; interval-mem-intro its converse (order-lemmas), and nn-le-trans-guarded the
;;; transitivity (theorem-library/nn-order-basics).

(define (iw-goal) (wff-formula (sequent-node-assertion (proof-state-focus *ps*))))
(define (iw-di*)                          ; di is greedy; peel to a fixed point
  (let lp () (let* ((g (iw-goal)) (h (and (pair? g) (car g))))
               (when (memq h '(FORALL IMPLIES)) (di) (lp)))))

(sp (make-wff
  '(FORALL b (IMPLIES (IN b NN)
     (FORALL c (IMPLIES (IN c NN)
       (FORALL a (FORALL i
         (IMPLIES (IN i (INTERVAL a b))
           (IMPLIES (<= b c)
             (IN i (INTERVAL a c))))))))))))
(iw-di*)
(fact 'interval-elt-in-nn 'a 'b 'i)       ; i in NN
(fact 'interval-lo 'a 'b 'i)              ; a <= i
(fact 'interval-hi 'a 'b 'i)              ; i <= b
(fact 'nn-le-trans-guarded 'i 'b 'c)      ; i <= b <= c
(fact 'interval-mem-intro 'a 'c 'i)
(ass)
(qed 'interval-widen)
(topic! 'interval-widen 'inequalities)
