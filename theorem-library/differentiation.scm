;;; differentiation.scm -- Chapter 2 (Differentiation) of calculus.pdf, founded
;;; on the CARATHEODORY / o(h) ALGEBRAIC definition (user's choice 2026-06-27).
;;;
;;; f is differentiable at a with derivative L iff there is a function phi,
;;; continuous at a, with phi(a) = L and
;;;        f(x) - f(a) = phi(x) * (x - a)      for all x.
;;; This is equivalent to calculus.pdf Def 2.1 (the limit of the difference
;;; quotient): for x /= a the identity forces phi(x) = (f(x)-f(a))/(x-a), and
;;; continuity of phi at a is exactly existence of that limit, with the value
;;; phi(a) = f'(a).  But it is purely EQUATIONAL, so the differentiation rules
;;; become ring identities the macetes fire on directly (no eps-delta on the
;;; quotient): see the rule statements below and the notes' own Prop 2.4/2.5/2.6
;;; proofs, which already run through exactly this phi.
;;;
;;; Real functions f : RR -> RR; values use the +/-/*/abs surface (the same the
;;; RR-MS metric uses); point continuity is IS-CONTINUOUS-AT(RR-MS,RR-MS,phi,a)
;;; (structure-library/metric-continuity.scm).  The supporting "continuity
;;; algebra" lives in theorem-library/continuity-algebra.scm.
;;;
;;; STATUS: deriv-const and deriv-identity are MACHINE-PROVEN from the algebraic
;;; definition (the witness phi is a constant, continuity by const-continuous-at,
;;; the factorization closes by crs) -- proof-of-concept that the foundation
;;; fires.  derivative-unique, diff-implies-continuous (Prop 2.4), deriv-sum
;;; (2.5), deriv-product (2.6) remain warranted supports: they additionally need
;;; (a) skolemizing the IS-DIFF-AT hypotheses to extract the factor phi, (b) for
;;; sum/product the RR-closure of f(x)+g(x) / f(x)*g(x) under fun-apply-type
;;; (the known [[numeric-closure-gap]]), and (c) a "continuity respects pointwise
;;; equality" lemma for Prop 2.4 -- the next increment.

;;; ===================================================================
;;; The Caratheodory derivative
;;; ===================================================================

;;; IS-DIFF-AT(f, a, L): f is differentiable at a with derivative L.
(def-predicate 'IS-DIFF-AT '(f a L)
  '(AND (IN f (FUN RR RR))
   (AND (IN a RR)
   (AND (IN L RR)
        (FORSOME phi
          (AND (IN phi (FUN RR RR))
          (AND (IS-CONTINUOUS-AT RR-MS RR-MS phi a)
          (AND (= (phi a) L)
               (FORALL x (IMPLIES (IN x RR)
                 (= (- (f x) (f a)) (* (phi x) (- x a)))))))))))))

;;; DERIV(f, a) = the unique L with IS-DIFF-AT(f,a,L) (well-defined by
;;; derivative-unique below); equals phi(a).  Written f'(a) in the notes.
(def-functoid 'DERIV '(f a)
  '(IOTA L (IS-DIFF-AT f a L)))

;;; ===================================================================
;;; First results (calculus.pdf Chapter 2.1) -- warranted, proofs next increment
;;; ===================================================================

;;; Uniqueness of the derivative: makes DERIV's IOTA well-defined.  From the two
;;; factorizations phi(x)(x-a) = psi(x)(x-a): for x/=a, phi(x)=psi(x); both are
;;; continuous at a, so phi(a)=psi(a), i.e. L=M.
(support 'derivative-unique
  '(FORALL f (FORALL a (FORALL L (FORALL M
     (IMPLIES (AND (IS-DIFF-AT f a L) (IS-DIFF-AT f a M))
              (= L M)))))))
(warrant! 'derivative-unique 'well-known
  "If f(x)-f(a)=phi(x)(x-a)=psi(x)(x-a) with phi,psi continuous at a, then
   phi and psi agree off a (cancel x-a/=0), hence at a by continuity, so the
   two derivative values phi(a)=L and psi(a)=M coincide.")
(category! 'derivative-unique 'analysis)

;;; Prop 2.4: differentiable at a => continuous at a.
(support 'diff-implies-continuous
  '(FORALL f (FORALL a (FORALL L
     (IMPLIES (IS-DIFF-AT f a L)
              (IS-CONTINUOUS-AT RR-MS RR-MS f a))))))
(warrant! 'diff-implies-continuous 'reference
  "calculus.pdf Prop 2.4.  f(x) = f(a) + phi(x)(x-a) with phi continuous at a;
   as x -> a, phi(x) -> phi(a) (bounded) and (x-a) -> 0, so f(x) -> f(a).")
(category! 'diff-implies-continuous 'analysis)

;;; Derivative of a constant function is 0  (PROVEN).  Witness phi = const 0:
;;; c-c = 0 = 0*(x-a), and phi = const 0 is continuous at a with phi(a)=0.
(sp '(FORALL c (FORALL a
       (IMPLIES (AND (IN c RR) (IN a RR))
                (IS-DIFF-AT (VNB-LAMBDA x c) a 0)))))
(grind) (mac 'IS-DIFF-AT) (fact 'rr-zero-in)
(di) (lam-t) (grind) (ass)                       ; lambda(x,c) : RR -> RR
(di) (ass)                                       ; a in RR
(di) (ass)                                       ; 0 in RR
(ew '(VNB-LAMBDA x 0))                             ; phi := const 0
(di) (lam-t) (grind) (ass)                       ; lambda(x,0) : RR -> RR
(di) (bc* 'const-continuous-at () (ass) (ass))    ; phi continuous at a
(di) (lam-b) (rfl)                               ; phi(a) = 0
(grind) (lam-b) (crs)                            ; c-c = 0*(x-a)
(qed 'deriv-const)

;;; Derivative of the identity function is 1  (PROVEN).  Witness phi = const 1:
;;; x-a = 1*(x-a), and phi = const 1 is continuous at a with phi(a)=1.
(sp '(FORALL a
       (IMPLIES (IN a RR)
                (IS-DIFF-AT (VNB-LAMBDA x x) a 1))))
(grind) (mac 'IS-DIFF-AT) (fact 'rr-one-in)
(di) (lam-t) (grind) (ass)                       ; lambda(x,x) : RR -> RR
(di) (ass)                                       ; a in RR
(di) (ass)                                       ; 1 in RR
(ew '(VNB-LAMBDA x 1))                             ; phi := const 1
(di) (lam-t) (grind) (ass)                       ; lambda(x,1) : RR -> RR
(di) (bc* 'const-continuous-at () (ass) (ass))    ; phi continuous at a
(di) (lam-b) (rfl)                               ; phi(a) = 1
(grind) (lam-b) (crs)                            ; x-a = 1*(x-a)
(qed 'deriv-identity)

;;; Prop 2.5: sum rule.  phi_{f+g} = phi_f + phi_g.
(support 'deriv-sum
  '(FORALL f (FORALL g (FORALL a (FORALL L (FORALL M
     (IMPLIES (AND (IS-DIFF-AT f a L) (IS-DIFF-AT g a M))
              (IS-DIFF-AT (VNB-LAMBDA x (+ (f x) (g x))) a (+ L M)))))))))
(warrant! 'deriv-sum 'reference
  "calculus.pdf Prop 2.5.  (f+g)(x)-(f+g)(a) = (phi_f(x)+phi_g(x))(x-a); the
   witness phi_f+phi_g is continuous at a (sum of continuous), value L+M.")
(category! 'deriv-sum 'analysis)

;;; Prop 2.6: product rule.  phi_{fg}(x) = phi_f(x) g(x) + f(a) phi_g(x).
(support 'deriv-product
  '(FORALL f (FORALL g (FORALL a (FORALL L (FORALL M
     (IMPLIES (AND (IS-DIFF-AT f a L) (IS-DIFF-AT g a M))
              (IS-DIFF-AT (VNB-LAMBDA x (* (f x) (g x))) a
                          (+ (* L (g a)) (* (f a) M))))))))))
(warrant! 'deriv-product 'reference
  "calculus.pdf Prop 2.6.  (fg)(x)-(fg)(a) = [phi_f(x)g(x) + f(a)phi_g(x)](x-a)
   by adding and subtracting f(a)g(x); the bracket is continuous at a with
   value L*g(a)+f(a)*M.")
(category! 'deriv-product 'analysis)

;;; Prop 2.8: the CHAIN RULE.  COMPOSE(g,f)(x) = g(f(x)); (g o f)'(a)=g'(f(a))f'(a).
;;; Caratheodory form (limit-free, no o/O algebra): with f(x)-f(a)=phi_f(x)(x-a)
;;; and g(y)-g(f(a))=phi_g(y)(y-f(a)),
;;;   (gof)(x)-(gof)(a) = phi_g(f(x)) * (f(x)-f(a)) = [phi_g(f(x))*phi_f(x)]*(x-a),
;;; so the Caratheodory factor of g o f is (phi_g o f)*phi_f -- continuous at a
;;; (compose-continuous-at + product-continuous-at; f cont at a by diff=>cont),
;;; value phi_g(f(a))*phi_f(a) = M*L.
(support 'deriv-chain
  '(FORALL f (FORALL g (FORALL a (FORALL L (FORALL M
     (IMPLIES (IS-DIFF-AT f a L)
     (IMPLIES (IS-DIFF-AT g (f a) M)
       (IS-DIFF-AT (COMPOSE g f) a (* M L))))))))))
(warrant! 'deriv-chain 'reference
  "calculus.pdf Prop 2.8 (chain rule), Caratheodory form: the factor of g o f is
   (phi_g o f)*phi_f, continuous at a with value g'(f(a))*f'(a) = M*L.")
(category! 'deriv-chain 'analysis)
