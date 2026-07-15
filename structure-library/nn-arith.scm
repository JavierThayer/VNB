;;; nn-arith.scm -- the recursion equations for + and * on NN.
;;;
;;; THE GAP.  number-systems.scm (:43-87) axiomatizes NN with `succ' (a kernel
;;; term-former), closure, and the COMMUTATIVE-MONOID-ish laws of + and * --
;;; comm, assoc, distrib, a+0 = a, 1*a = a.  It never connects the two: there is
;;; no equation anywhere in the tree relating `+' to `succ'.  Not `succ n = n+1',
;;; not `a + succ b = succ(a+b)', nothing.  So NN's arithmetic is Peano's only in
;;; name: `+' is an abstract commutative operation that happens to fix 0.
;;;
;;; It bites the moment you do induction.  (ni) builds its step goal by
;;; substituting the SYMBOLIC term (succ n) (primitive-inferences.scm:1020), and
;;; then nothing can move: `crs' treats (succ n) as an opaque generator (it is
;;; not a ring head), `arith' only evaluates GROUND numerals, and no lemma
;;; rewrites it.  Every induction over NN arithmetic in this library has so far
;;; dodged this by never needing to cross the succ/+ boundary.
;;;
;;; The two equations below are that connection.  They are the standard
;;; primitive-recursive definition of + and * -- Peano's, in the form every
;;; textbook gives -- and with them the rest is THEOREM, not assertion:
;;; succ n = n + 1, additive cancellation, 2*k /= 2*j+1, parity, even-square-
;;; implies-even (see theorem-library/nn-parity-proof.scm).  They are asserted
;;; here only because number-systems.scm introduces NN by axiom rather than
;;; constructing it; the kernel's ~92 primitive axioms do not grow, so they are
;;; warranted supports.
;;;
;;; NOT asserted, because they are derivable and are proved in nn-parity-proof:
;;;   succ injective on NN  -- ord-succ-injective + ord-succ-nn (ordinals.scm)
;;;   a * 0 = 0             -- distributivity + additive cancellation
;;;
;;; Loads after number-systems (NN, +, *, succ) and proof-debt (support/warrant!).

;;; a + succ(b) = succ(a + b)
(support 'nn-add-succ
  '(FORALL a
     (IMPLIES (IN a NN)
       (FORALL b
         (IMPLIES (IN b NN)
           (= (+ a (succ b)) (succ (+ a b))))))))

(warrant! 'nn-add-succ 'reference
  "The recursion equation defining + on NN: a + succ(b) = succ(a + b).  Peano.
   ASSERTED because number-systems.scm axiomatizes NN's + by its algebraic laws
   (comm/assoc/distrib/zero) and never relates it to succ, leaving the two
   symbols unconnected.  Retire it by constructing + as the recursion it is.")

;;; a * succ(b) = a*b + a
(support 'nn-mul-succ
  '(FORALL a
     (IMPLIES (IN a NN)
       (FORALL b
         (IMPLIES (IN b NN)
           (= (* a (succ b)) (+ (* a b) a)))))))

(warrant! 'nn-mul-succ 'reference
  "The recursion equation defining * on NN: a * succ(b) = a*b + a.  Peano.
   Same gap as nn-add-succ: number-systems.scm gives * its algebraic laws and
   never relates it to succ.")
