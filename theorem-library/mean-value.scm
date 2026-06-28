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

;;; ===================================================================
;;; Generalized MVT (Thm 2.11) -> MVT (Thm 2.13) -> corollaries (2.14, 2.15).
;;; Witnesses (theta) flow from rolle by bc*, so the arc stays assemblable.
;;; Stated with product forms (L*(b-a) = f(b)-f(a)) to avoid division.
;;; ===================================================================

;;; Thm 2.11: generalized MVT.  Rolle on h(x)=f(x)(g(b)-g(a))-g(x)(f(b)-f(a)).
(add-to-pss 'generalized-mvt
  '(FORALL f (FORALL g (FORALL a (FORALL b
     (IMPLIES (AND (IN f (FUN RR RR)) (AND (IN g (FUN RR RR))
              (AND (IN a RR) (AND (IN b RR) (< a b)))))
     (IMPLIES (FORALL x (IMPLIES (IN x (CCINT a b))
                 (AND (IS-CONTINUOUS-AT RR-MS RR-MS f x)
                      (IS-CONTINUOUS-AT RR-MS RR-MS g x))))
     (IMPLIES (FORALL x (IMPLIES (AND (< a x) (< x b))
                 (AND (FORSOME L (IS-DIFF-AT f x L))
                      (FORSOME M (IS-DIFF-AT g x M)))))
       (FORSOME theta (AND (< a theta) (AND (< theta b)
         (FORSOME L (FORSOME M (AND (IS-DIFF-AT f theta L)
                                (AND (IS-DIFF-AT g theta M)
           (= (* L (- (g b) (g a))) (* M (- (f b) (f a)))))))))))))))))))
(warrant! 'generalized-mvt 'reference
  "calculus.pdf Thm 2.11.  Apply rolle to h(x)=f(x)(g(b)-g(a))-g(x)(f(b)-f(a));
   h(a)=h(b)=f(a)g(b)-g(a)f(b), and h'(theta)=0 is the stated identity.")
(category! 'generalized-mvt 'analysis)

;;; Thm 2.13: MVT.  generalized-mvt at g = identity (g(b)-g(a)=b-a, g'=1).
(add-to-pss 'mvt
  '(FORALL f (FORALL a (FORALL b
     (IMPLIES (AND (IN f (FUN RR RR)) (AND (IN a RR) (AND (IN b RR) (< a b))))
     (IMPLIES (FORALL x (IMPLIES (IN x (CCINT a b)) (IS-CONTINUOUS-AT RR-MS RR-MS f x)))
     (IMPLIES (FORALL x (IMPLIES (AND (< a x) (< x b)) (FORSOME L (IS-DIFF-AT f x L))))
       (FORSOME theta (AND (< a theta) (AND (< theta b)
         (FORSOME L (AND (IS-DIFF-AT f theta L)
           (= (* L (- b a)) (- (f b) (f a)))))))))))))))
(warrant! 'mvt 'reference
  "calculus.pdf Thm 2.13: generalized-mvt with g = identity, so f'(theta)(b-a) =
   f(b)-f(a).")
(category! 'mvt 'analysis)

;;; Cor 2.15: derivative identically 0 on (a,b) => f constant on [a,b].
(add-to-pss 'deriv-zero-implies-constant
  '(FORALL f (FORALL a (FORALL b
     (IMPLIES (AND (IN f (FUN RR RR)) (AND (IN a RR) (AND (IN b RR) (< a b))))
     (IMPLIES (FORALL x (IMPLIES (IN x (CCINT a b)) (IS-CONTINUOUS-AT RR-MS RR-MS f x)))
     (IMPLIES (FORALL x (IMPLIES (AND (< a x) (< x b)) (IS-DIFF-AT f x 0)))
       (FORALL u (FORALL v (IMPLIES (AND (IN u (CCINT a b)) (IN v (CCINT a b)))
         (= (f u) (f v))))))))))))
(warrant! 'deriv-zero-implies-constant 'reference
  "calculus.pdf Cor 2.15: MVT on any subinterval [u,v] gives f(v)-f(u) =
   f'(theta)(v-u) = 0, so f is constant.")
(category! 'deriv-zero-implies-constant 'analysis)

;;; Cor 2.14: f' <= M on (a,b) => f(b)-f(a) <= M(b-a)  (and the >= m form).
(add-to-pss 'mvt-upper-bound
  '(FORALL f (FORALL a (FORALL b (FORALL M
     (IMPLIES (AND (IN f (FUN RR RR)) (AND (IN a RR) (AND (IN b RR) (AND (IN M RR) (< a b)))))
     (IMPLIES (FORALL x (IMPLIES (IN x (CCINT a b)) (IS-CONTINUOUS-AT RR-MS RR-MS f x)))
     (IMPLIES (FORALL x (IMPLIES (AND (< a x) (< x b))
                 (FORSOME L (AND (IS-DIFF-AT f x L) (<= L M)))))
       (<= (- (f b) (f a)) (* M (- b a)))))))))))
(warrant! 'mvt-upper-bound 'reference
  "calculus.pdf Cor 2.14: MVT gives theta with f(b)-f(a)=f'(theta)(b-a)<=M(b-a).")
(category! 'mvt-upper-bound 'analysis)

(add-to-pss 'mvt-lower-bound
  '(FORALL f (FORALL a (FORALL b (FORALL m
     (IMPLIES (AND (IN f (FUN RR RR)) (AND (IN a RR) (AND (IN b RR) (AND (IN m RR) (< a b)))))
     (IMPLIES (FORALL x (IMPLIES (IN x (CCINT a b)) (IS-CONTINUOUS-AT RR-MS RR-MS f x)))
     (IMPLIES (FORALL x (IMPLIES (AND (< a x) (< x b))
                 (FORSOME L (AND (IS-DIFF-AT f x L) (<= m L)))))
       (<= (* m (- b a)) (- (f b) (f a)))))))))))
(warrant! 'mvt-lower-bound 'reference
  "calculus.pdf Cor 2.14 (lower): MVT gives f(b)-f(a)=f'(theta)(b-a)>=m(b-a).")
(category! 'mvt-lower-bound 'analysis)
