;;; continuity-algebra.scm -- pointwise continuity is an algebra on RR.
;;;
;;; The supporting machinery for differentiation (theorem-library/
;;; differentiation.scm): the constant and identity maps are continuous at every
;;; point, and IS-CONTINUOUS-AT(RR-MS,RR-MS,-,a) is closed under pointwise sum
;;; and product.  These are the standard eps-delta facts (constant: any delta;
;;; identity: delta=eps; sum: eps/2 split + triangle; product: bound one factor
;;; near a, then |gh - g(a)h(a)| <= |g||h-h(a)| + |h(a)||g-g(a)|).  Asserted as
;;; warranted supports (well-known) -- the eps-delta drudgery is exactly the
;;; "boring minutiae" the PSS is meant to absorb; the INTERESTING content is the
;;; differentiation rules proved on top of these (where the algebraic phi does
;;; the work).  Reusable well beyond differentiation.

;;; Constant map x|->c is continuous at every a.  (Antecedents curried, not
;;; AND'd, so a backchain spawns them as separate subgoals -- closes cleanly
;;; with inline bc* handlers; see differentiation.scm.)
(support 'const-continuous-at
  '(FORALL c (IMPLIES (IN c RR) (FORALL a (IMPLIES (IN a RR)
     (IS-CONTINUOUS-AT RR-MS RR-MS (VNB-LAMBDA x RR c) a))))))
(warrant! 'const-continuous-at 'well-known
  "Constant map: for any eps>0 any delta>0 works, since d(c,c)=0<=eps.")
(topic! 'const-continuous-at 'analysis)

;;; Identity map x|->x is continuous at every a.
(support 'identity-continuous-at
  '(FORALL a (IMPLIES (IN a RR)
     (IS-CONTINUOUS-AT RR-MS RR-MS (VNB-LAMBDA x RR x) a))))
(warrant! 'identity-continuous-at 'well-known
  "Identity map: delta=eps works, since d(x,a)=|x-a|<=eps whenever |x-a|<=eps.")
(topic! 'identity-continuous-at 'analysis)

;;; Pointwise sum of two maps continuous at a is continuous at a.
(support 'sum-continuous-at
  '(FORALL g (FORALL h (FORALL a (IMPLIES
     (IS-CONTINUOUS-AT RR-MS RR-MS g a)
     (IMPLIES (IS-CONTINUOUS-AT RR-MS RR-MS h a)
     (IS-CONTINUOUS-AT RR-MS RR-MS (VNB-LAMBDA x RR (+ (g x) (h x))) a)))))))
(warrant! 'sum-continuous-at 'well-known
  "Sum of continuous: given eps, take delta = min of the eps/2-deltas for g and
   h; the triangle inequality gives |(g+h)(x)-(g+h)(a)| <= eps.")
(topic! 'sum-continuous-at 'analysis)

;;; Pointwise product of two maps continuous at a is continuous at a.
(support 'product-continuous-at
  '(FORALL g (FORALL h (FORALL a (IMPLIES
     (IS-CONTINUOUS-AT RR-MS RR-MS g a)
     (IMPLIES (IS-CONTINUOUS-AT RR-MS RR-MS h a)
     (IS-CONTINUOUS-AT RR-MS RR-MS (VNB-LAMBDA x RR (* (g x) (h x))) a)))))))
(warrant! 'product-continuous-at 'well-known
  "Product of continuous: g is bounded near a (continuity), and
   |gh(x)-gh(a)| <= |g(x)||h(x)-h(a)| + |h(a)||g(x)-g(a)|; choose deltas making
   each summand < eps/2.")
(topic! 'product-continuous-at 'analysis)

;;; Composition of continuous: f continuous at a and g continuous at f(a) give
;;; g o f = COMPOSE(g,f) continuous at a.  (The block the Caratheodory chain
;;; rule needs: phi_g o f is continuous at a.)
(support 'compose-continuous-at
  '(FORALL g (FORALL f (FORALL a (IMPLIES
     (IS-CONTINUOUS-AT RR-MS RR-MS f a)
     (IMPLIES (IS-CONTINUOUS-AT RR-MS RR-MS g (f a))
     (IS-CONTINUOUS-AT RR-MS RR-MS (COMPOSE g f) a)))))))
(warrant! 'compose-continuous-at 'well-known
  "Composition of continuous: given eps, the g-at-f(a) delta feeds the f-at-a
   delta; (g o f)(x) = g(f(x)) stays within eps of g(f(a)).")
(topic! 'compose-continuous-at 'topology)

;;; Difference of two maps continuous at a is continuous at a (sum with -h).
(support 'sub-continuous-at
  '(FORALL g (FORALL h (FORALL a (IMPLIES
     (IS-CONTINUOUS-AT RR-MS RR-MS g a)
     (IMPLIES (IS-CONTINUOUS-AT RR-MS RR-MS h a)
     (IS-CONTINUOUS-AT RR-MS RR-MS (VNB-LAMBDA x RR (- (g x) (h x))) a)))))))
(warrant! 'sub-continuous-at 'well-known
  "Difference of continuous is continuous: (g-h)(x) = g(x) + (-1)*h(x); the eps/2
   split for sum-continuous-at, negation being an isometry of RR.")
(topic! 'sub-continuous-at 'analysis)

;;; Continuity is a property of the point-values: if f agrees with a map g that
;;; is continuous at a, at every point, then f is continuous at a.  (The transfer
;;; that lets a proof establish continuity of the tidy algebraic representative
;;; and carry it back to the function actually in hand -- e.g. diff-implies-
;;; continuous, where f equals f(a)+phi(x)(x-a) pointwise.)
(support 'cont-transfer-ptwise-eq
  '(FORALL f (FORALL g (FORALL a (IMPLIES
     (IN f (FUN RR RR))
     (IMPLIES (IS-CONTINUOUS-AT RR-MS RR-MS g a)
     (IMPLIES (FORALL x (IMPLIES (IN x RR) (= (f x) (g x))))
              (IS-CONTINUOUS-AT RR-MS RR-MS f a))))))))
(warrant! 'cont-transfer-ptwise-eq 'well-known
  "f = g pointwise and g continuous at a => f continuous at a: continuity reads
   only the values, and d(f(x),f(a)) = d(g(x),g(a)) at every x, so the same delta
   works.")
(topic! 'cont-transfer-ptwise-eq 'analysis)

;;; Two maps continuous at a that agree at every OTHER point agree at a as well.
;;; (a is a limit point of RR, so the value at a is forced by the punctured
;;; values; the crux of uniqueness of the Caratheodory factor, hence of DERIV.)
(support 'cont-agree-off-pt
  '(FORALL fa (FORALL fb (FORALL pt (IMPLIES (IN pt RR) (IMPLIES (IS-CONTINUOUS-AT RR-MS RR-MS fa pt) (IMPLIES (IS-CONTINUOUS-AT RR-MS RR-MS fb pt) (IMPLIES (FORALL x (IMPLIES (IN x RR) (IMPLIES (NOT (= x pt)) (= (fa x) (fb x))))) (= (fa pt) (fb pt))))))))))
(warrant! 'cont-agree-off-pt 'well-known
  "fa, fb continuous at pt and fa(x)=fb(x) for all x/=pt => fa(pt)=fb(pt).  pt is
   a limit point of RR (no isolated points), so both values are the common limit
   of the punctured values; take x -> pt.")
(topic! 'cont-agree-off-pt 'analysis)
