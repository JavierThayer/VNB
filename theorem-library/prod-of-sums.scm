;;; theorem-library/prod-of-sums.scm
;;;
;;; The expansion of a finite PRODUCT OF SUMS over a commutative ring:
;;;
;;;   prod_{k in X} (a(k) + b(k))
;;;       = sum_{S subseteq X} (prod_{k in S} a(k)) * (prod_{k in X\S} b(k))
;;;
;;; -- the multilinear / "FOIL over an index set" identity.  Sum on the right
;;; ranges over POWER(X), the powerset (2^|X| terms); each term is a(k) over a
;;; subset S times b(k) over its complement X\S.  Commutativity makes the
;;; product unordered (no enumeration needed) and the regrouping valid.
;;;
;;; This file is the whole dependency tower, stated as warranted Proof Support
;;; Set entries (library-build phase: assert with a warrant, defer the formal
;;; induction).  Three layers:
;;;
;;;   (1) set-minus  -- DIFFERENCE was used in the codebase (field.scm,
;;;                     numeric-instances.scm) but never characterized; its
;;;                     membership / sethood axioms are filled in here.
;;;   (2) powerset   -- POWER(X) finiteness, subset-finiteness, and the
;;;                     insert-split that drives the induction on |X|.
;;;   (3) product    -- the finite-product recurrence (FINSUM's long-promised
;;;                     finsum-insert, finsum.scm:75) and PROD-RING's
;;;                     empty / singleton / insert / closure laws.
;;;
;;; capped by  prod-of-sums-expansion.
;;;
;;; Singletons / one-point extensions are PAIR(x,x) / UNION(X,PAIR(k,k)) to
;;; mesh with card-insert and finite-set-induction (cardinality.scm).
;;;
;;; Dependencies: finprod.scm (FINPROD/PROD-RING), views.scm (COMMUTATIVE-RING-
;;; MULTIPLICATIVE-CM, COMMUTATIVE-RING-ADDITIVE-AG), injection.scm (IMAGE),
;;; cardinality.scm (CARD), monoid.scm (COMM-MONOID), theory.scm (POWER,
;;; DIFFERENCE, UNION, INTERSECTION, PAIR, EMPTY-SET).

;;; =======================================================================
;;; Layer 1 -- set difference X \ B
;;; =======================================================================

;;; x in (U \ B)  iff  x in U and x not in B.
;;; U, NOT X: the reader case-folds X to x, collapsing (IN x X) to (IN x x).
(support 'difference-membership
  '(FORALL U (FORALL B (FORALL x
      (IFF (IN x (DIFFERENCE U B))
           (AND (IN x U) (NOT (IN x B))))))))

(warrant! 'difference-membership 'well-known
  "Defining property of set difference.  DIFFERENCE was already in use
   (field.scm: NON-ZERO = A \\ {ZERO}; numeric-instances.scm) with no
   characterizing axiom; this records the standard one.")

;;; X \ B is a set whenever X is -- it is a subclass of X (separation).
(support 'difference-set
  '(FORALL X (IMPLIES (IN X SET)
      (FORALL B (IN (DIFFERENCE X B) SET)))))

(warrant! 'difference-set 'well-known
  "X \\ B is a subclass of the set X, hence a set by separation
   (cf. set-equality-not-class: a subclass of a set is a set).")

;;; =======================================================================
;;; Layer 2 -- powerset finiteness and the insert-split
;;; =======================================================================

;;; A subset of a finite set is finite.
(support 'card-subset-nn
  '(FORALL X (IMPLIES (AND (IN X SET) (IN (CARD X) NN))
      (FORALL S (IMPLIES (AND (IN S SET)
                              (FORALL z (IMPLIES (IN z S) (IN z X))))
                 (IN (CARD S) NN))))))

(warrant! 'card-subset-nn 'well-known
  "A subset of a finite set is finite (its cardinality is bounded by the
   superset's).  Standard; the RHS terms PROD-RING(R,a,S) and
   PROD-RING(R,b,X\\S) need S and X\\S finite to be well-defined.")

;;; The powerset of a finite set is finite: |POWER(X)| = 2^|X| in NN.
(support 'card-power-nn
  '(FORALL X (IMPLIES (AND (IN X SET) (IN (CARD X) NN))
      (IN (CARD (POWER X)) NN))))

(warrant! 'card-power-nn 'well-known
  "A finite set has 2^|X| subsets -- finitely many.  This is what makes the
   sum over POWER(X) on the right of the expansion a genuine FINSUM.  (The
   exact count |POWER(X)| = 2^|X| is deliberately NOT stated: the 2-arg
   `power' head is overloaded -- power-exp reads (power 2 n) as the function
   space FUN(n,2), not the number -- so the exact-value support would be
   ambiguous.  Finiteness is all the induction needs.)")

;;; Insert-split, cover half.  For k not in X, every subset of X u {k} either
;;; avoids k (a subset of X) or is S u {k} for a unique subset S of X.  So
;;; POWER(PTS u {k}) is the union of POWER(X) and the image of POWER(X) under
;;; S |-> S u {k}.  This is the set-level heart of the induction on |X|.
(support 'power-insert-cover
  '(FORALL X (IMPLIES (IN X SET)
      (FORALL k (IMPLIES (AND (IN k SET) (NOT (IN k X)))
        (= (POWER (UNION X (PAIR k k)))
           (UNION (POWER X)
                  (IMAGE (VNB-LAMBDA S (UNION S (PAIR k k))) (POWER X)))))))))

(warrant! 'power-insert-cover 'well-known
  "A subset of X u {k} contains k or not; dropping k gives a subset of X, and
   the two cases are the two halves of the union.  Standard bijection
   underlying the binomial recursion; here as a set equation.")

;;; Insert-split, disjointness half.  k not in X, so a subset of X cannot equal
;;; one that contains k -- the two halves are disjoint, and card-union-disjoint
;;; + the injectivity of S |-> S u {k} split the FINSUM cleanly.
(support 'power-insert-disjoint
  '(FORALL X (IMPLIES (IN X SET)
      (FORALL k (IMPLIES (AND (IN k SET) (NOT (IN k X)))
        (= (INTERSECTION (POWER X)
                         (IMAGE (VNB-LAMBDA S (UNION S (PAIR k k))) (POWER X)))
           EMPTY-SET))))))

(warrant! 'power-insert-disjoint 'well-known
  "Every member of POWER(X) omits k (k not in X); every member of the image
   contains k.  Hence the two halves of power-insert-cover are disjoint.")

;;; =======================================================================
;;; Layer 3 -- the finite-product recurrence and PROD-RING's laws
;;; =======================================================================

;;; finsum-insert: the long-promised insertion recurrence for FINSUM over a
;;; finite set (finsum.scm:75 refers to it as `finsum-insert' but it was never
;;; installed; the insert-last-is-bijection groundwork is in scratch-fs3.scm).
;;; Adding one fresh point k to the index folds in one more factor f(k):
;;;
;;;   FINSUM(m, f, X u {k}) = (MUL m)(FINSUM(m, f, X), f(k))    (k not in X)
;;;
;;; Stated over a commutative monoid (the generality the unordered product
;;; needs); it is the multiplicative twin of the additive sum's recursion and
;;; the workhorse of every induction on |X| below.
(support 'finsum-insert
  '(FORALL m (IMPLIES (IS-COMM-MONOID m)
      (FORALL X (IMPLIES (AND (IN X SET) (IN (CARD X) NN))
      (FORALL k (IMPLIES (AND (IN k SET) (NOT (IN k X)))
      (FORALL f (IMPLIES (IN f (FUN (UNION X (PAIR k k)) (CARR m)))
        (= (FINSUM m f (UNION X (PAIR k k)))
           ((MUL m) (FINSUM m f X) (f k))))))))))))

(warrant! 'finsum-insert 'well-known
  "Enumerate X then append k last (INSERT-LAST, finsum.scm): a bijection
   ORD-SEGMENT(|X|+1) -> X u {k} placing k at index |X|, so SUM-AG peels f(k)
   as the final fold step (sum-ag-succ) on top of FINSUM over X.  Independence
   of the chosen enumeration is finsum-comm-monoid-well-defined.  Uses no
   inverses, hence holds over a bare commutative monoid.  (Candidate to
   discharge into a `proof' once insert-last-is-bijection is finished --
   groundwork in scratch-fs3.scm.)")

;;; PROD-RING over the empty set is the multiplicative identity ONE(R).
;;; (FINSUM over EMPTY-SET is E of the structure = ONE under the mult view.)
(support 'prod-ring-empty
  '(FORALL R (IMPLIES (IS-COMMUTATIVE-RING R)
      (FORALL f (= (PROD-RING R f EMPTY-SET) (ONE R))))))

(warrant! 'prod-ring-empty 'informal
  "PROD-RING(R,f,S) = FINSUM(R^x,f,S) with R^x the multiplicative comm-monoid
   of R, whose identity ID maps to ONE(R); finsum-empty gives the empty fold =
   ID(R^x) = ONE(R).  The empty product is 1.")

;;; PROD-RING over a singleton {x} is f(x).
(support 'prod-ring-singleton
  '(FORALL R (IMPLIES (IS-COMMUTATIVE-RING R)
      (FORALL x (IMPLIES (IN x SET)
      (FORALL f (IMPLIES (IN f (FUN (PAIR x x) (CARR R)))
        (= (PROD-RING R f (PAIR x x)) (f x)))))))))

(warrant! 'prod-ring-singleton 'informal
  "FINSUM over a one-point set is the single value (finsum-singleton through
   the multiplicative view); the one-factor product is that factor.")

;;; PROD-RING insertion recurrence: adding a fresh index k multiplies in f(k).
;;; This is finsum-insert at m = R's multiplicative comm-monoid (MUL of the
;;; view reduces to (MUL R)); the workhorse for induction on |X|.
(support 'prod-ring-insert
  '(FORALL R (IMPLIES (IS-COMMUTATIVE-RING R)
      (FORALL X (IMPLIES (AND (IN X SET) (IN (CARD X) NN))
      (FORALL k (IMPLIES (AND (IN k SET) (NOT (IN k X)))
      (FORALL f (IMPLIES (IN f (FUN (UNION X (PAIR k k)) (CARR R)))
        (= (PROD-RING R f (UNION X (PAIR k k)))
           ((MUL R) (PROD-RING R f X) (f k))))))))))))

(warrant! 'prod-ring-insert 'informal
  "finsum-insert specialized to R's multiplicative commutative monoid
   (COMMUTATIVE-RING-MULTIPLICATIVE-CM R), whose MUL is (MUL R) and whose
   FINSUM is PROD-RING.  prod_{X u {k}} = (prod_X) * f(k).")

;;; PROD-RING stays in the carrier.
(support 'prod-ring-type
  '(FORALL R (IMPLIES (IS-COMMUTATIVE-RING R)
      (FORALL X (IMPLIES (AND (IN X SET) (IN (CARD X) NN))
      (FORALL f (IMPLIES (IN f (FUN X (CARR R)))
        (IN (PROD-RING R f X) (CARR R)))))))))

(warrant! 'prod-ring-type 'informal
  "finsum-comm-monoid-type through the multiplicative view: the product folds
   with (MUL R), which closes on CARR(R), seeded at ONE(R) in CARR(R).")

;;; =======================================================================
;;; Capstone -- the product-of-sums expansion
;;; =======================================================================

;;;   prod_{k in X} (a(k) + b(k))
;;;       = sum_{S in POWER(X)} (prod_{k in S} a(k)) * (prod_{k in X\S} b(k))
;;;
;;; LHS: PROD-RING of the pointwise sum a+b over X.
;;; RHS: FINSUM over POWER(X), in R's additive abelian group
;;;      (COMMUTATIVE-RING-ADDITIVE-AG R), of the ring product of the two
;;;      partial products PROD-RING(R,a,S) and PROD-RING(R,b,X\S).
(support 'prod-of-sums-expansion
  '(FORALL R (IMPLIES (IS-COMMUTATIVE-RING R)
      (FORALL X (IMPLIES (AND (IN X SET) (IN (CARD X) NN))
      (FORALL a (IMPLIES (IN a (FUN X (CARR R)))
      (FORALL b (IMPLIES (IN b (FUN X (CARR R)))
        (= (PROD-RING R (VNB-LAMBDA k ((ADD R) (a k) (b k))) X)
           (FINSUM (COMMUTATIVE-RING-ADDITIVE-AG R)
                   (VNB-LAMBDA S ((MUL R) (PROD-RING R a S)
                                          (PROD-RING R b (DIFFERENCE X S))))
                   (POWER X))))))))))))

(warrant! 'prod-of-sums-expansion 'well-known
  "Expand each binomial factor and collect: choosing a(k) or b(k) at each k in
   X corresponds to a subset S (the k's where a was chosen), contributing
   prod_S a * prod_{X\\S} b; summing over all 2^|X| choices gives the result
   (commutativity makes the regrouping valid).  Formal route: induction on |X|
   via finite-set-induction.  Base |X|=0: prod-ring-empty gives 1, and POWER
   (EMPTY-SET)={EMPTY-SET} contributes ONE*ONE=1.  Step X u {k0}: prod-ring-
   insert factors out (a(k0)+b(k0)), ring-left-dist splits it, and power-
   insert-cover / power-insert-disjoint reindex POWER(PTS u {k0}) into the
   subsets containing vs avoiding k0 -- matching the two distributed sums.")
