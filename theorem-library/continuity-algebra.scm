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
     (IS-CONTINUOUS-AT RR-MS RR-MS (VNB-LAMBDA x c) a))))))
(warrant! 'const-continuous-at 'well-known
  "Constant map: for any eps>0 any delta>0 works, since d(c,c)=0<=eps.")
(category! 'const-continuous-at 'analysis)

;;; Identity map x|->x is continuous at every a.
(support 'identity-continuous-at
  '(FORALL a (IMPLIES (IN a RR)
     (IS-CONTINUOUS-AT RR-MS RR-MS (VNB-LAMBDA x x) a))))
(warrant! 'identity-continuous-at 'well-known
  "Identity map: delta=eps works, since d(x,a)=|x-a|<=eps whenever |x-a|<=eps.")
(category! 'identity-continuous-at 'analysis)

;;; Pointwise sum of two maps continuous at a is continuous at a.
(support 'sum-continuous-at
  '(FORALL g (FORALL h (FORALL a (IMPLIES
     (IS-CONTINUOUS-AT RR-MS RR-MS g a)
     (IMPLIES (IS-CONTINUOUS-AT RR-MS RR-MS h a)
     (IS-CONTINUOUS-AT RR-MS RR-MS (VNB-LAMBDA x (+ (g x) (h x))) a)))))))
(warrant! 'sum-continuous-at 'well-known
  "Sum of continuous: given eps, take delta = min of the eps/2-deltas for g and
   h; the triangle inequality gives |(g+h)(x)-(g+h)(a)| <= eps.")
(category! 'sum-continuous-at 'analysis)

;;; Pointwise product of two maps continuous at a is continuous at a.
(support 'product-continuous-at
  '(FORALL g (FORALL h (FORALL a (IMPLIES
     (IS-CONTINUOUS-AT RR-MS RR-MS g a)
     (IMPLIES (IS-CONTINUOUS-AT RR-MS RR-MS h a)
     (IS-CONTINUOUS-AT RR-MS RR-MS (VNB-LAMBDA x (* (g x) (h x))) a)))))))
(warrant! 'product-continuous-at 'well-known
  "Product of continuous: g is bounded near a (continuity), and
   |gh(x)-gh(a)| <= |g(x)||h(x)-h(a)| + |h(a)||g(x)-g(a)|; choose deltas making
   each summand < eps/2.")
(category! 'product-continuous-at 'analysis)
