;;; poly-degree.scm -- DEG, LEADCOEF and MONOMIAL for the monoid algebra's
;;; polynomial specialisation A[NN].
;;;
;;; This file is DEFINITIONS ONLY.  Everything about them that is a claim is
;;; proved in theorem-library/poly-degree-laws.scm; nothing here is asserted.
;;;
;;; ==================================================================
;;; THE CONVENTION, and why this one
;;; ==================================================================
;;;
;;; A polynomial over A is a finitely-supported coefficient sequence
;;; NN -> CARR(A) (structure-library/polynomial.scm).  Two readings of "its
;;; degree" are available and they differ by one:
;;;
;;;   (i)  the LEAST STRICT BOUND -- the least n with p(k) = 0 for every
;;;        k >= n.  That is the LENGTH of the coefficient list, i.e. one more
;;;        than the degree for a nonzero p, and 0 for p = 0.
;;;   (ii) the LARGEST EXPONENT carrying a nonzero coefficient.
;;;
;;; THIS FILE DEFINES (ii), spelled as a minimisation so that it is reachable
;;; by `minimize!' exactly as (i) would be:
;;;
;;;     DEG(A, p)  =  the least n in NN such that p(k) = ZERO(A)
;;;                   for every k in NN with n < k.
;;;
;;; `n < k' rather than `n <= k' is the whole difference.  A non-strict bound
;;; is an n that is >= every element of the support, so the LEAST non-strict
;;; bound IS the largest support element -- the degree in the textbook sense --
;;; while the least STRICT bound is that plus one.  Both are equally easy to
;;; reach (the existence witness in each case is the eventually-zero index of
;;; poly-tail-zero-fwd), so the naming decides it: a symbol called DEG that
;;; returns one more than the degree is a trap of exactly the kind this tree
;;; keeps paying for.
;;;
;;; CONSEQUENCES OF (ii), stated once so that no later law has to rediscover
;;; them:
;;;
;;;   * DEG(A, 0) = 0, and DEG(A, c) = 0 for a nonzero constant c.  NN has no
;;;     -infinity, so the zero polynomial and the nonzero constants share a
;;;     degree.  There is no way around this short of moving the codomain to
;;;     NN u {-inf}, which would need an order and an addition on that set and
;;;     buys one boundary case.
;;;   * Hence `deg(fg) = deg f + deg g' is FALSE as stated for f = 0, and every
;;;     multiplicative law has to carry a nonzero hypothesis.  The additive law
;;;     `deg(f+g) <= max(deg f, deg g)' is unaffected and holds for all f, g.
;;;   * LEADCOEF(A, 0) = 0.  `leadcoef-nonzero' is therefore guarded on p
;;;     having SOME nonzero coefficient, which is the honest hypothesis.
;;;
;;; DEFINEDNESS.  DEG is an IOTA, so DEG(A, p) is DEFINED exactly when the
;;; description succeeds: when a least bound in the above sense exists and is
;;; unique.  For p in CARR(POLY(A)) both hold (deg-well-defined,
;;; theorem-library/poly-degree-laws.scm) -- existence from poly-tail-zero-fwd
;;; plus `minimize!', uniqueness from nn-le-antisym.  For a p that is NOT
;;; finitely supported the description is empty and DEG(A, p) is undefined;
;;; `=' being partial in VNB, that is the correct outcome and needs no guard in
;;; the definition itself.
;;;
;;; Needs: polynomial.scm (POLY / SUPP / FINSUPP), order-predicates (`<'),
;;; order-lemmas (NN order vocabulary).  Loaded late (after
;;; theorem-library/nn-least-element) because its companion proof file uses
;;; `minimize!', which resolves nn-least-element at call time.
;;; ==================================================================

;;; ---- DEG-BOUND: "no coefficient past index n" ------------------------
;;; A PREDICATE, not a functoid, and deliberately: `def-predicate' installs the
;;; defining IFF as a THEOREM, so `mac-h' can unfold it in an ASSUMPTION --
;;; which is where it is always met ("let n bound the support of p").  A
;;; `def-functoid' would install only the rewrite macete and `mac-h' would warn
;;; `unknown theorem/macete' and no-op (CLAUDE.md, and poly-membership.scm's
;;; header at length).
;;;
;;; The evaluation index is `k_' with a trailing underscore, never `k' or `n':
;;; the reader case-folds, and `n' is a parameter of this very predicate.
(def-predicate 'DEG-BOUND '(A p n)
  '(FORALL k_ (IMPLIES (IN k_ NN) (IMPLIES (< n k_) (= (p k_) (ZERO A))))))
(notation! 'DEG-BOUND 'arity 3 'english "$3 bounds the support of $2")
(gloss! 'DEG-BOUND
  "DEG-BOUND(A,p,n) -- every coefficient of p past index n vanishes:
   p(k) = ZERO(A) for every k in NN with n < k.  Note the bound is NON-STRICT
   in the sense that p(n) itself is unconstrained; n is allowed to be the
   degree, not required to exceed it.  DEG(A,p) is the least n with this
   property.")
(topic! 'DEG-BOUND 'algebra)

;;; ---- DEG: the least such bound ---------------------------------------
;;; Written as the definite description of the least element rather than as a
;;; MIN over a SEP set: the tree has no MIN-of-a-set constructor, and building
;;; one would owe the sethood and non-emptiness obligations at every use.  The
;;; IOTA owes them once, in deg-well-defined, and `iota-d' is the rule that
;;; collects them.
(def-functoid 'DEG '(A p)
  '(IOTA n_ (AND (IN n_ NN)
             (AND (DEG-BOUND A p n_)
                  (FORALL j_ (IMPLIES (IN j_ NN)
                               (IMPLIES (DEG-BOUND A p j_) (<= n_ j_))))))))
(notation! 'DEG 'arity 2 'english "the degree of $2")
(gloss! 'DEG
  "DEG(A,p) -- the degree of the polynomial p over A: the least n in NN with
   p(k) = ZERO(A) for every k > n, equivalently the largest exponent carrying a
   nonzero coefficient.  DEG(A,0) = 0, and so does DEG of any constant: NN has
   no -infinity.  Defined (as an IOTA) exactly when p has finite support; see
   deg-well-defined.")
(topic! 'DEG 'algebra)

;;; ---- LEADCOEF: the coefficient at the degree --------------------------
(def-functoid 'LEADCOEF '(A p) '(p (DEG A p)))
(notation! 'LEADCOEF 'arity 2 'english "the leading coefficient of $2")
(gloss! 'LEADCOEF
  "LEADCOEF(A,p) = p(DEG(A,p)) -- the leading coefficient of p.  It is nonzero
   exactly when p is (leadcoef-nonzero); LEADCOEF(A,0) = ZERO(A), which is what
   the DEG(A,0) = 0 convention forces.")
(topic! 'LEADCOEF 'algebra)

;;; ---- MONOMIAL: c.x^n --------------------------------------------------
;;; The coefficient sequence that is c at index n and zero elsewhere.  Its
;;; domain is declared NN, which is CARR(NN-ADD-MONOID) after `slot CARR'
;;; (the nn-add-monoid@carr instance macete) -- the spelling `poly-membership'
;;; consumes, via SQN(CARR A) = FUN(NN, CARR A).
;;;
;;; The evaluation point is x_, never n or c: both are parameters here, and the
;;; case fold would capture them inside the lambda exactly as it would have
;;; captured M in MONALG-ADD (polynomial.scm:52).
(def-functoid 'MONOMIAL '(A c n)
  '(VNB-LAMBDA x_ NN (IF (= x_ n) c (ZERO A))))
(notation! 'MONOMIAL 'arity 3 'english "the monomial $2 x^$3 over $1")
(gloss! 'MONOMIAL
  "MONOMIAL(A,c,n) -- the polynomial c.x^n over A: the coefficient sequence
   whose value is c at index n and ZERO(A) everywhere else.  Its support is
   {n} when c /= 0 and empty otherwise; its degree is n when c /= 0.")
(topic! 'MONOMIAL 'algebra)
