;;; mean-value.scm -- the Mean Value Theorem arc (calculus.pdf Ch 2.4-2.5):
;;; interior-extremum => derivative 0 (Prop 2.10), Rolle's lemma (2.12), and
;;; later the MVT itself.  Built on the Extreme Value Theorem (extreme-value.scm)
;;; and IS-DIFF-AT (differentiation.scm).
;;;
;;; All asserted as witness-manufacturing blocks: Rolle's theta comes from EVT's
;;; argmax via Prop 2.10, so a downstream consumer bc*'s rolle and never guesses
;;; theta -- [[automatable-assembly]].

;;; ===================================================================
;;; Prop 2.10 (interior form): at an interior maximum/minimum of f on [a,b],
;;; if f is differentiable there, its derivative is 0.
;;; ===================================================================

;;; Caratheodory view: f(x)-f(theta) = phi(x)(x-theta), phi continuous at theta,
;;; phi(theta)=L.  At an interior max, f(x)-f(theta) <= 0 on [a,b]; for x>theta
;;; (x-theta>0) phi(x)<=0, for x<theta phi(x)>=0; continuity at theta forces
;;; phi(theta)=L=0.
(add-to-pss 'interior-max-deriv-zero
  '(FORALL f (FORALL a (FORALL b (FORALL theta (FORALL L
     (IMPLIES (AND (IN f (FUN RR RR)) (AND (IN a RR) (AND (IN b RR)
              (AND (IN theta RR) (AND (< a theta) (< theta b))))))
     (IMPLIES (FORALL x (IMPLIES (IN x (CCINT a b)) (<= (f x) (f theta))))
     (IMPLIES (IS-DIFF-AT f theta L)
       (= L 0))))))))))
(warrant! 'interior-max-deriv-zero 'reference
  "calculus.pdf Prop 2.10 (interior max).  Caratheodory factor phi: phi(x)<=0
   for x>theta and phi(x)>=0 for x<theta (since f(x)-f(theta)<=0); continuity at
   theta forces phi(theta)=L=0.")
(category! 'interior-max-deriv-zero 'analysis)

(add-to-pss 'interior-min-deriv-zero
  '(FORALL f (FORALL a (FORALL b (FORALL theta (FORALL L
     (IMPLIES (AND (IN f (FUN RR RR)) (AND (IN a RR) (AND (IN b RR)
              (AND (IN theta RR) (AND (< a theta) (< theta b))))))
     (IMPLIES (FORALL x (IMPLIES (IN x (CCINT a b)) (<= (f theta) (f x))))
     (IMPLIES (IS-DIFF-AT f theta L)
       (= L 0))))))))))
(warrant! 'interior-min-deriv-zero 'reference
  "calculus.pdf Prop 2.10 (interior min): apply interior-max-deriv-zero to -f.")
(category! 'interior-min-deriv-zero 'analysis)

;;; ===================================================================
;;; Rolle's lemma (2.12): h continuous on [a,b], differentiable on (a,b), with
;;; h(a)=h(b), has an interior critical point.
;;; ===================================================================
(add-to-pss 'rolle
  '(FORALL h (FORALL a (FORALL b
     (IMPLIES (AND (IN h (FUN RR RR)) (AND (IN a RR) (AND (IN b RR) (< a b))))
     (IMPLIES (FORALL x (IMPLIES (IN x (CCINT a b))
                 (IS-CONTINUOUS-AT RR-MS RR-MS h x)))
     (IMPLIES (FORALL x (IMPLIES (AND (< a x) (< x b))
                 (FORSOME L (IS-DIFF-AT h x L))))
     (IMPLIES (= (h a) (h b))
       (FORSOME theta (AND (< a theta) (AND (< theta b)
                      (IS-DIFF-AT h theta 0))))))))))))
(warrant! 'rolle 'reference
  "calculus.pdf Lemma 2.12.  EVT gives a max and a min of h on [a,b].  If the
   max is interior, interior-max-deriv-zero gives h'=0 there; likewise an
   interior min via interior-min-deriv-zero.  If BOTH are endpoints then, since
   h(a)=h(b), max=min so h is constant on [a,b] and h'=0 at any interior point.
   The witness theta is EVT's argmax/argmin, not a guess.")
(category! 'rolle 'analysis)
