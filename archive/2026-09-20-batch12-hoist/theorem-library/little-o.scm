;;; little-o.scm -- calculus.pdf Section 2.2, the calculus of o/O notation, in a
;;; LIMIT-FREE form consistent with the Caratheodory derivative (so we need no
;;; function-limit primitive).
;;;
;;; The notes define o(f) via  lim_{h->a} g/f -> 0.  For the increment f = (x-a)
;;; -- the only case differentiation/Taylor use -- this is equivalent to the
;;; epsilon-form:  g is o(x-a) at a  iff  g(x) = eps(x)*(x-a) for some eps that
;;; is continuous at a with eps(a) = 0.  (eps(x) = g(x)/(x-a) off a; continuity
;;; at a with value 0 is exactly g/(x-a) -> 0.)  This is the same shape as the
;;; Caratheodory factor, so it threads cleanly into IS-DIFF-AT.
;;;
;;; Real functions g : RR -> RR; +/-/* on values; IS-CONTINUOUS-AT(RR-MS,...).
;;;
;;; The existential eps in LITTLE-O-AT is never *guessed* downstream: a proof
;;; introduces an o-fact only by bc*-ing one of the manufacturing lemmas below
;;; (the eq-12 bridge, o-sum, o-scalar).  Those asserted lemmas are the blocks;
;;; the chain rule / Taylor assemble from them by search.  [[automatable-assembly]]

;;; ===================================================================
;;; LITTLE-O-AT(g, a):  g is o(x - a) at a.
;;; ===================================================================
(def-predicate 'LITTLE-O-AT '(g a)
  '(AND (IN g (FUN RR RR))
   (AND (IN a RR)
        (FORSOME eps
          (AND (IN eps (FUN RR RR))
          (AND (IS-CONTINUOUS-AT RR-MS RR-MS eps a)
          (AND (= (eps a) 0)
               (FORALL x (IMPLIES (IN x RR)
                 (= (g x) (* (eps x) (- x a))))))))))))

;;; ===================================================================
;;; The eq-(12) bridge: differentiability <=> the increment is L*h + o(h).
;;; f'(a)=L  iff  x |-> f(x)-f(a)-L*(x-a)  is o(x-a) at a.
;;; (=>) take eps = phi - L (phi the Caratheodory factor): increment(x) =
;;;      (phi(x)-L)(x-a), eps continuous at a, eps(a)=0.
;;; (<=) take phi = eps + L: f(x)-f(a) = phi(x)(x-a), phi continuous, phi(a)=L.
;;; This is the block that lets the chain rule run on o-algebra.
;;; ===================================================================
;;; diff-iff-little-o RETIRED 2026-09-18 (rake batch 5): proven modulo 0 in theorem-library/rake-series.scm

;;; ===================================================================
;;; o-algebra blocks (curried antecedents for inline bc* handlers).
;;; ===================================================================

;;; Sum: o(x-a) + o(x-a) = o(x-a).  Witness eps_{g+h} = eps_g + eps_h.
;;; little-o-sum RETIRED 2026-09-18 (rake batch 5): proven modulo 0 in theorem-library/rake-series.scm

;;; Scalar: c * o(x-a) = o(x-a).  Witness eps_{c g} = c * eps_g.
;;; little-o-scalar RETIRED 2026-09-18 (rake batch 5): proven modulo 0 in theorem-library/rake-series.scm

;;; -----------------------------------------------------------------------
;;; Notation -- the ENGLISH of these predicates, declared beside their
;;; definitions and read by wff->english / the proof reader (operators.scm).
;;; A def-predicate's reading cannot be derived the way a structure's noun can
;;; (noun vs adjective: IS-COMPLETE wants "s is complete", not "s is a complete"),
;;; so it is written here, once, next to what it means.
(notation! 'LITTLE-O-AT 'kind 'predicate 'arity 2
           'english "$1 is little-o at $2")
